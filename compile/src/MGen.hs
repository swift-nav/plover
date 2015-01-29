{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
module MGen where
import Name

import Data.String
import Data.List
import Data.Maybe (fromJust)
import qualified Data.Map.Strict as M

import Control.Applicative ((<$>))
import Control.Monad (foldM)
import Control.Monad.Trans.Either
import Control.Monad.Trans.Class
import Control.Monad.Free
import Data.Foldable (Foldable)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence)

import Debug.Trace (trace)

type Variable = String

data Line = LStore Loc RHS | LAction RHS
  deriving (Show, Eq, Ord)

infix 4 :=, :==, :<
pattern l :=  r = LStore l r
pattern l :== b = LStore l (RHSMat b)
pattern l :< b = LStore l (RHSBlock b)

data RHS = RHSMat MExprU
         | RHSExpr ExprU
         | RHSCall Variable [(Variable, RHS)]
         | RHSVoid
         | RHSBlock [Line]
  deriving (Show, Eq, Ord)


type View2 a = Expr -> Expr -> a
data Dim' a = Dim a a
  deriving (Show, Eq, Ord)
type Dim = Dim' Name
type DimU = Dim' ExprU
rows (Dim r _) = r
cols (Dim _ c) = c

data Mat = Mat BaseType DimU (View2 ExprU)
  deriving (Show, Eq, Ord)

data MExpr' e
  = MRef Variable
  | MLit Mat
  | MMul e e
  | MSum e e
  deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)
type MExpr = MExpr' Name
type MExprU = Free MExpr' Name

data Expr' a
  = ERef Variable
  | ELit Int
  | ESum a a
  | EMul a a
  | ESummation a (Expr -> Expr)
 deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)

--data Expr' a = Expr ExprTag [a]
--  deriving (Show, Eq, Ord)
type Expr = Expr' Name
type ExprU = Free Expr' Name

data Loc 
  = LName Variable
  | LIndex Loc Expr
  deriving (Show, Eq, Ord)

data BaseType = Int | Float | Void
  deriving (Show, Eq, Ord)
type TypeContext = M.Map Variable Name
type Context = (Blocks, TypeContext)

-- TODO change to match Expr' format
data TypeTag
  = TMatrix Dim   -- basetype, expr, expr
  | TExpr         -- basetype
  | TBlock        -- return type, arg types
  | TLit BaseType -- None
  deriving (Show, Eq, Ord)
-- TODO change to match Expr' format
data Type' a = Type TypeTag [a]
  deriving (Show, Eq, Ord)
type Type = Type' Name

data UValue = UType Type | UExpr Expr | UVar
  deriving (Show, Eq, Ord)
data UError = UError [Name] String
  deriving (Show, Eq, Ord)

-- Operations that unify and may fail
type InnerM = EitherT UError (EnvMonad UValue)
-- Operations that run InnerM actions, handle errors
-- TODO aggregate errors?
type OuterM = EnvMonad UValue
-- Operations that simply use store/get
type M = EnvMonad UValue

data Block = Block [Line] Context
  deriving (Show, Eq, Ord)
type Blocks = M.Map Variable Block

-- Updates a context and the monad environment given a line.
-- Unification errors for the given line are passed over,
-- so context may be erroneous as well, but parsing can still continue.
parseLine :: Context -> Line -> OuterM Context
parseLine c@(blocks, context) ((LName var) :< lines) = do
  return (M.insert var (Block lines c) blocks, context)
parseLine c@(blocks, context) ((LName var) := val) = do
  -- Type the RHS, check context for LHS, bind RHS to LHS, return type ref
  okay <- runEitherT $ do
    rhs <- typeExpr c val
    lhs <- lift $ case M.lookup var context of
      Nothing -> store UVar
      Just n -> return n
    unifyBind lhs rhs
    return lhs
  -- Check result, update context if valid
  case okay of
    Left err -> trace ("parseLine. " ++ show err) $ return c
    Right typeName -> return (blocks, M.insert var typeName context)
-- TODO is this ok?
parseLine c (LAction _) = return c

parseLines :: Context -> [Line] -> OuterM Context
parseLines = foldM parseLine

-- TODO should return Either Error Name
typeExpr :: Context -> RHS -> InnerM Name
typeExpr c@(blocks, context) (RHSCall name bindings) = do
  let (vars, args) = unzip bindings
  argTypes <- mapM (typeExpr c) args
  let block = fromJust (M.lookup name blocks)
  applyBlock block (zip vars argTypes)
-- TODO ????????
typeExpr c@(blocks, context) (RHSExpr (Pure name)) =
  return name
typeExpr c@(blocks, context) (RHSExpr (Free tag)) =
  case tag of
    ERef var -> lift $
      case M.lookup var context of
        Nothing -> store UVar
        Just t -> return t
    ELit i -> lift $ store $ UType (Type (TLit Int) [])
    ESum e1 e2 -> do
      t1 <- typeExpr c (RHSExpr e1)
      t2 <- typeExpr c (RHSExpr e2)
      unifyBind t1 t2
      return t1
    EMul e1 e2 -> do
      t1 <- typeExpr c (RHSExpr e1)
      t2 <- typeExpr c (RHSExpr e2)
      unifyBind t1 t2
      return t1
    ESummation _ fn -> lift $ store $ UType (Type (TLit Float) [])

typeExpr c@(blocks, context) RHSVoid =
  lift $ store $ UType (Type (TLit Void) [])
-- TODO check result from unifications
typeExpr c@(blocks, context) (RHSMat (Free tag)) =
  case tag of
    MRef var -> lift $
      case M.lookup var context of
        Nothing -> store UVar
        Just t -> return t
    MLit mat -> do
      mvar <- lift $ store UVar
      matVar <- storeMat c mat
      unifyDim mvar matVar
      return mvar
    MMul e1 e2 -> do
      t1 <- typeExpr c (RHSMat e1)
      t2 <- typeExpr c (RHSMat e2)
      unifyInner t1 t2
      return t1
    MSum e1 e2 -> do
      t1 <- typeExpr c (RHSMat e1)
      t2 <- typeExpr c (RHSMat e2)
      unifyDim t1 t2
      return t1

-- TODO remove
typeExpr _ b = error $ "typeExpr. " ++ (show b)

matrixVar :: M Name
matrixVar = do
  typeVar <- store UVar
  rowsVar <- store UVar
  colsVar <- store UVar
  store $ UType (Type (TMatrix $ Dim rowsVar colsVar) [typeVar])

matchMatrix :: Name -> InnerM Type
matchMatrix name = do
  val <- lift $ get name
  case val of
    UVar -> do
      mvar <- lift $ matrixVar
      unifyBind name mvar
      matchMatrix name
    UType t@(Type (TMatrix _) _) ->
      right t
    _ -> left $ UError [name] "not a matrix"

-- Return rows or columns variable
matrixProperty :: (Dim -> Name) -> Name -> InnerM Name
matrixProperty fn name = do
  Type (TMatrix dim) _ <- matchMatrix name
  return (fn dim)

storeMat :: Context -> Mat -> InnerM Name
storeMat c (Mat tp (Dim rows cols) _) = do
  typeVar <- lift $ store $ UType (Type (TLit tp) [])
  rowsVar <- typeExpr c (RHSExpr rows)
  colsVar <- typeExpr c (RHSExpr cols)
  lift $ store $ UType (Type (TMatrix $ Dim rowsVar colsVar) [typeVar])

unifyDim :: Name -> Name -> InnerM ()
unifyDim n1 n2  = do
  unifyRows n1 n2
  unifyCols n1 n2
  unifyBaseType n1 n2

unifyBaseType :: Name -> Name -> InnerM ()
unifyBaseType n1 n2 = do
  Type _ bt1 <- matchMatrix n1
  Type _ bt2 <- matchMatrix n2
  assert (bt1 == bt2) [n1, n2] "unifyBaseType."

assert :: Bool -> [Name] -> String -> InnerM ()
assert True _ _ = return ()
assert False names str = left $ UError names ("assert failure: " ++ str)

unifyRows :: Name -> Name -> InnerM ()
unifyRows n1 n2 = do
  r1 <- matrixProperty rows n1
  r2 <- matrixProperty rows n2
  unifyBind r1 r2
unifyCols :: Name -> Name -> InnerM ()
unifyCols n1 n2 = do
  c1 <- matrixProperty cols n1
  c2 <- matrixProperty cols n2
  unifyBind c1 c2
unifyInner :: Name -> Name -> InnerM ()
unifyInner n1 n2 = do
  c1 <- matrixProperty cols n1
  r2 <- matrixProperty rows n2
  unifyBind c1 r2

chk = runEnv . parseLines emptyContext

unifyBind :: Name -> Name -> InnerM ()
unifyBind n1 n2 = do
  bindings <- unify n1 n2
  mapM_ (uncurry update) bindings
 where
  update n1 n2 = lift $ do
    v2 <- get n2
    -- TODO remove trace
    trace (show (n1, v2)) $ put n1 v2

unify :: Name -> Name -> InnerM [Pair]
unify n1 n2 = do
  v1 <- lift $ get n1
  v2 <- lift $ get n2
  unifyOne n1 v1 n2 v2

type Pair = (Name, Name)
unifyOne :: Name -> UValue -> Name -> UValue -> InnerM [Pair]
unifyOne n1 UVar n2 t = right $ [(n1, n2)]
unifyOne n1 t n2 UVar = unifyOne n2 UVar n1 t
unifyOne n1 (UType (Type t1 ns1)) n2 (UType (Type t2 ns2)) = do
  assert (t1 == t2) [n1, n2] $
    "unifyOne. type tags don't match: " ++ (show t1 ++ show t2)
  bs <- unifyMany [n1, n2] ns1 ns2
  return $ (n1, n2) : bs

unifyOne n1 (UExpr e1) n2 (UExpr e2) = do
  assert (tagEq e1 e2) [n1, n2] $
    "unifyOne. expr types don't match: " ++ show e1 ++ ", " ++ show e2
  bs <- unifyMany [n1, n2] (children e1) (children e2)
  return $ (n1, n2) : bs

unifyOne n1 v1 n2 v2 = left $ UError [n1, n2] $
  "unifyOne. value types don't match: " ++ show v1 ++ ", " ++ show v2

unifyMany :: [Name] -> [Name] -> [Name] -> InnerM [Pair]
unifyMany from ns1 ns2 = do
  assert (length ns1 == length ns2) from $
    "unifyMany. type arg list lengths don't match: "
      ++ show ns1 ++ ", " ++ show ns2
  concat <$> mapM (uncurry unify) (zip ns1 ns2)

tagEq :: (Functor f, Eq (f ())) => f a -> f a -> Bool
tagEq t1 t2 = fmap (const ()) t1 == fmap (const ()) t2

children :: (T.Traversable t) => t a -> [a]
children t = fst $ T.mapAccumR step [] t
 where
  step list child = (child : list, ())

extend :: TypeContext -> [(Variable, Name)] -> TypeContext
extend context bindings = foldr (uncurry M.insert) context bindings
-- Returns type of block result
-- TODO support empty block?
applyBlock :: Block -> [(Variable, Name)] -> InnerM Name
applyBlock (Block lines (blocks, context)) bindings = do
  let bs' = extend context bindings
  let (body, ret) = (init lines, last lines)
  c2 <- lift $ parseLines (blocks, bs') body
  case ret of
    LAction rhs -> typeExpr c2 rhs
    _ -> typeExpr c2 RHSVoid

-- TESTS
emptyContext :: Context
emptyContext = (M.fromList [], M.fromList [])
b1 = [LAction RHSVoid]

p1 = [ "v" :< b1 ]
p2 = [ "x" := 2
     , "y" := 3
     , LAction "x"
     ]

-- It Works !
p3 = [ "x" := 2
     , "y" := RHSExpr ("u" * "x")
     , LAction "y"
     ]
p4 = [ "x" :== 2
     , "y" :== "x" * "u"
     ]


e1, e2 :: ExprU

(e1, e2) = evalEnv $ do 
  n1 <- store 2
  n2 <- store 3
  return (Pure n1 * 4, Pure n2 * 3)


-- STUFF --
instance Show (a -> b) where
  show f = "<fn>"
-- TODO is this desirable?
instance Eq (a -> b) where
  a == b = False
instance Ord (a -> b) where
  compare a b = GT -- ???

instance IsString MExprU where
  fromString = Free . MRef
--instance IsString Expr where
--  fromString str = Expr (ERef str) []
instance IsString Loc where
  fromString = LName
--
instance IsString RHS where
  fromString = RHSExpr . fromString
instance IsString ExprU where
  fromString = Free . ERef
instance Num RHS where
  x * y = undefined
  x + y = undefined
  fromInteger = RHSExpr . fromInteger
  abs = undefined
  signum = undefined
  negate = undefined
instance Num ExprU where
  x * y = Free (EMul x y)
  x + y = Free (ESum x y)
  fromInteger x = Free (ELit $ fromInteger x)
  abs = undefined
  signum = undefined
  negate = undefined
instance Num MExprU where
  x * y = Free (MMul x y)
  x + y = Free (MSum x y)
  fromInteger x = Free $ MLit $ Mat Float (Dim 1 1) (\_ _ -> fromInteger x)
  abs = undefined
  signum = undefined
  negate = undefined

--block1 =
-- [ "tau" := Call "norm" ["rx_st" - ("meas" :~ "sat_pos")] / "GPS_C"
-- , "weTau" := "tau" * "E_DOT"
-- , "xk_new" := Call "approx_rotation" ["weTau"] * ("meas" :~ "sat_pos")
-- , "los" := "xk_new" - "rx_state"
-- , "pred" := Call "norm" ["los"]
-- , "omp" := ("meas" :~ "pseudo") - "pred"
-- , "G" := 
--]
--the_goal =
-- [ All "j" (Call "block1" ["meas" :! "j", "pred" :! "j", "omp" :! "j", "G" :! "j"])
-- ,
-- ]

-- TODO
-- add functions
-- read block, build type context
-- unify
--  store unification context
