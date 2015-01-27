{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
module MGen where
import Prelude hiding ((**))
import Name
import qualified Data.Map.Strict as M
import Data.List
import Data.Maybe (fromJust)
import Control.Applicative ((<$>))
import Data.String
import Control.Monad (foldM)
import Debug.Trace (trace)

import Control.Monad.Free

data False
deriving instance Show False
deriving instance Eq False
deriving instance Ord False

data Line = LStore Loc RHS | LAction RHS
  deriving (Show, Eq, Ord)
infix 4 :=, :==
pattern l :=  r = LStore l r
pattern l :== b = LStore l (RHSBlock b)
data RHS = RHSMat MExpr | RHSExpr ExprU
         | RHSCall Variable [(Variable, RHS)]
         | RHSVoid
         | RHSBlock [Line]
  deriving (Show, Eq, Ord)

type Variable = String

data Mat = Mat Expr Expr (View2 Expr)
  deriving (Show, Eq, Ord)

data MExpr
  = MRef Variable
  | MLit Mat
  | MMul MExpr MExpr
  | MSum MExpr MExpr
  deriving (Show, Eq, Ord)

type View1 a = Expr -> a
type View2 a = Expr -> Expr -> a
data Expr' a = Expr ExprTag [a]
  deriving (Show, Eq, Ord)
type Expr = Expr' Name
type ExprU = Free Expr' Name

data ExprTag
  = ERef Variable
  | ELit Int
  | ESum
  | EMul
  | ESummation (Expr -> Expr)
  deriving (Show, Eq, Ord)

data Loc 
  = LName Variable
  | LIndex Loc Expr
  deriving (Show, Eq, Ord)

data BaseType = Int | Float | Void
  deriving (Show, Eq, Ord)
type TypeContext = M.Map Variable Name
type Context = (Blocks, TypeContext)

data Type a = Type TypeTag [a]
  deriving (Show, Eq, Ord)
data TypeTag
  = TMatrix -- basetype, expr, expr
  | TExpr -- basetype
  | TBlock -- return type, arg types
  | TLit BaseType
  deriving (Show, Eq, Ord)

data UValue = UType (Type Name) | UExpr Expr | UVar
  deriving (Show, Eq, Ord)

type M a = EnvMonad UValue a
data Block = Block [Line] Context
  deriving (Show, Eq, Ord)
type Blocks = M.Map Variable Block

parseLine :: Context -> Line -> M Context
parseLine c@(blocks, context) ((LName var) :== lines) = do
  return (M.insert var (Block lines c) blocks, context)
parseLine c@(blocks, context) ((LName var) := val) = do
  rhs <- typeExpr c val
  lhs <- case M.lookup var context of
    Nothing -> store UVar
    Just n -> return n
  okay <- unifyBind lhs rhs
  if okay then return () else error "EIT"
  return $ (blocks, M.insert var lhs context)
-- TODO is this ok?
parseLine c (LAction _) = return c

parseLines :: Context -> [Line] -> M Context
parseLines = foldM parseLine

typeExpr :: Context -> RHS -> M Name
typeExpr c@(blocks, context) (RHSCall name bindings) = do
  let (vars, args) = unzip bindings
  argTypes <- mapM (typeExpr c) args
  let block = fromJust (M.lookup name blocks)
  applyBlock block (zip vars argTypes)
typeExpr c@(blocks, context) (RHSExpr (Free (Expr tag ns))) =
  case tag of
    ERef var ->
      case M.lookup var context of
        Nothing -> store UVar
        Just t -> return t
    ELit i -> store $ UType (Type (TLit Int) [])
    ESum -> do
      let [e1, e2] = ns
      t1 <- typeExpr c (RHSExpr e1)
      t2 <- typeExpr c (RHSExpr e2)
      unifyBind t1 t2
      return t1
    EMul -> do
      let [e1, e2] = ns
      t1 <- typeExpr c (RHSExpr e1)
      t2 <- typeExpr c (RHSExpr e2)
      unifyBind t1 t2
      return t1
    ESummation fn -> store $ UType (Type (TLit Float) [])
typeExpr c@(blocks, context) RHSVoid =
  store $ UType (Type (TLit Void) [])
typeExpr _ b = error (show b)
--typeExpr c@(blocks, context) (RHSMat m) = _

-- TESTS
emptyContext :: Context
emptyContext = (M.fromList [], M.fromList [])
b1 = [LAction RHSVoid]

p1 = [ "v" :== b1 ]
p2 = [ "x" := 2
     , "y" := 3
     , LAction "x"
     ]
p3 = [ "x" := 2
     , "y" := RHSExpr ("u" * "x")
     , LAction "y"
     ]

chk = runEnv . parseLines emptyContext

unifyBind :: Name -> Name -> M Bool
unifyBind n1 n2 = do
  mbs <- unify n1 n2
  case mbs of
    Nothing -> return False
    Just bs -> mapM (uncurry update) bs >> return True
 where
  update n1 n2 = do
    v2 <- get n2
    trace (show (n1, v2)) $ put n1 v2

unify :: Name -> Name -> M (Maybe [Pair])
unify n1 n2 = do
  v1 <- get n1
  v2 <- get n2
  let mpairs = unifyOne n1 v1 n2 v2
  case mpairs of
    Nothing -> return Nothing
    Just (need, assert) -> do
      mbls <- mapM (uncurry unify) need
      return $ do
        bindingLists <- sequence mbls
        return $ assert ++ concat bindingLists

type Flip = Bool
type Pair = (Name, Name)
unifyOne :: Name -> UValue -> Name -> UValue -> Maybe ([Pair], [Pair])
unifyOne n1 UVar n2 t = Just ([], [(n1, n2)])
unifyOne n1 t n2 UVar = unifyOne n2 UVar n1 t
unifyOne n1 (UType (Type t1 ns1)) n2 (UType (Type t2 ns2)) =
  if t1 == t2 && length ns1 == length ns2
  then return (zip ns1 ns2, [(n1, n2)])
  else Nothing
unifyOne n1 (UExpr (Expr t1 ns1)) n2 (UExpr (Expr t2 ns2)) =
  if t1 == t2 && length ns1 == length ns2
  then return (zip ns1 ns2, [(n1, n2)])
  else Nothing
unifyOne _ _ _ _ = Nothing

extend :: TypeContext -> [(Variable, Name)] -> TypeContext
extend context bindings = foldr (uncurry M.insert) context bindings
-- Returns type of block result
-- TODO support empty block?
applyBlock :: Block -> [(Variable, Name)] -> M Name
applyBlock (Block lines (blocks, context)) bindings = do
  let bs' = extend context bindings
  let (body, ret) = (init lines, last lines)
  c2 <- parseLines (blocks, bs') body
  case ret of
    LAction rhs -> typeExpr c2 rhs
    _ -> typeExpr c2 RHSVoid



-- STUFF --
instance Show (a -> b) where
  show f = "<fn>"
-- TODO is this desirable?
instance Eq (a -> b) where
  a == b = False
instance Ord (a -> b) where
  compare a b = GT -- ???

--instance IsString MExpr where
--  fromString = MRef
--instance IsString Expr where
--  fromString str = Expr (ERef str) []
instance IsString Loc where
  fromString = LName
--
instance IsString RHS where
  fromString = RHSExpr . fromString
instance IsString ExprU where
  fromString x = Free (Expr (ERef x) [])
instance Num RHS where
  x * y = undefined
  x + y = undefined
  fromInteger = RHSExpr . fromInteger
  abs = undefined
  signum = undefined
  negate = undefined
instance Num ExprU where
  x * y = Free (Expr EMul [x, y])
  x + y = Free (Expr ESum [x, y])
  fromInteger x = Free (Expr (ELit $ fromInteger x) [])
  abs = undefined
  signum = undefined
  negate = undefined
--instance Num MExpr where
--  x * y = MMul x y
--  x + y = MSum x y
--  fromInteger x = MLit $ Mat 1 1 (\_ _ -> fromInteger x)
--  abs = undefined
--  signum = undefined
--  negate = undefined

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
