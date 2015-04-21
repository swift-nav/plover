{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
module Plover.Reduce
  ( compile, reduceArith, typeCheck
  , fmt
  ) where

import Data.List (intercalate, nub)
import Data.Monoid hiding (Sum)
import qualified Data.Foldable as F (Foldable, fold)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence, mapM, traverse)
import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Monad.State
import Data.String
import Data.Maybe (fromJust)
import Data.Function (on)

import Debug.Trace (trace, traceStack)

import qualified Smash.Simplify as S
import Plover.Types
import Plover.Generics
import Plover.Print
import Plover.Macros (seqList, generatePrinter, newline)

-- Hacky CExpr printer
fmt :: String -> String
fmt x = go "" (tokenize x)
 where
   fix :: Char -> String
   fix '(' = " ( "
   fix ')' = " ) "
   fix c = [c]

   tokenize :: String -> [String]
   tokenize = words . concatMap fix

   go :: String -> [String] -> String
   --go ind ("(" : "Free" : str) = "\n" ++ ind ++ "(" ++ "Free" ++ " " ++ go (ind) str
   go ind ("(" : head : str) = "\n" ++ ind ++ "(" ++ head ++ " " ++ go ("  " ++ ind) str
   go ind (")" : str) = ")" ++ go (drop 2 ind) str
   go ind (word : str) = word ++ go ind str
   go _ [] = ""


-- Searches syntax tree for simple arithmetic expressions, simplifies them
reduceArith = mvisit toExpr step
  where
    scale 1 x = x
    scale x (IntLit 1) = IntLit x
    scale x y = (IntLit x) * y

    step = S.simplify scale

    toExpr :: CExpr -> Maybe (S.Expr CExpr Int)
    toExpr (a :+ b) = do
      a' <- toExpr a
      b' <- toExpr b
      return $ S.Sum [a', b']
    toExpr (a :* b) = do
      a' <- toExpr a
      b' <- toExpr b
      return $ S.Mul [a', b']
    toExpr (IntLit i) = return $ S.Prim i
    toExpr (Negate x) = do
      x' <- toExpr x
      return $ S.Mul [S.Prim (-1), x']
    toExpr e@(Ref v) = return $ S.Atom e
    --toExpr e@(a :! b) = return $ S.Atom e
    toExpr x = Nothing

-- Attempts to simplify numeric expressions.
-- Called by type checker
numericEquiv :: CExpr -> CExpr -> Bool
numericEquiv = (==) `on` reduceArith

-- Type Checking
--isDefined :: Variable -> M Bool
--isDefined var = do
--  (_, env) <- get
--  case lookup var env of
--    Nothing -> return False
--    Just _ -> return True

withBindings :: [(Variable, Type)] -> M a -> M a
withBindings bindings m = do
  env0 <- getVarTypes
  mapM_ (uncurry extend) bindings
  a <- m
  setVarTypes env0
  return a

local = withBindings []

vectorTypeEq :: Type -> Type -> String -> M ()
vectorTypeEq Void Void _ = return ()
vectorTypeEq NumType NumType _ = return ()
vectorTypeEq IntType IntType _ = return ()
vectorTypeEq (VecType as t1) (VecType bs t2) err = do
  assert (and $ zipWith numericEquiv as bs) err
  unifyGen t1 t2
vectorTypeEq _ _ err = left err

-- Unify, for type variables
type Bindings = [(Variable, CExpr)]

walk :: Bindings -> CExpr -> CExpr
walk bs (Ref v) =
  case lookup v bs of
    Nothing -> Ref v
    Just (Ref v') | v' == v -> Ref v
    Just (Ref v') -> walk bs (Ref v')
    Just val -> val
walk bs e = e

-- Whether to treat R's as variables to be bound or as function arguments
data UnifyMethod = Extend | Universal

unifyExpr :: UnifyMethod -> Bindings -> CExpr -> CExpr -> M Bindings
unifyExpr u bs = unifyExpr' u bs `on` walk bs

unifyExpr' :: UnifyMethod -> Bindings -> CExpr -> CExpr -> M Bindings
unifyExpr' Extend bs (Ref v) x = return $ (v, x) : bs
unifyExpr' _ bs x y = do
  assert (x `numericEquiv` y) $ "unifyExpr failure:\n" ++ sep x y
  return bs

onM f g x y = do
  x' <- g x
  y' <- g y
  f x' y'

unifyType u bs = unifyT u bs `onM` normalizeType

unifyT :: UnifyMethod -> Bindings -> Type -> Type -> M Bindings
unifyT u bs (VecType d1 t1) (VecType d2 t2) = do
  bs' <- unifyMany u bs (map Dimension d1) (map Dimension d2)
  unifyType u bs' t1 t2
unifyT u bs (FnType (FnT _ params1 out1)) (FnType (FnT _ params2 out2)) = do
  bs' <- unifyType u bs out1 out2
  unifyMany u bs' (map snd params1) (map snd params2)
unifyT u bs (Dimension d1) (Dimension d2) = do
  unifyExpr u bs d1 d2
unifyT _ bs Void Void = return bs
unifyT _ bs StringType StringType = return bs
unifyT _ bs IntType IntType = return bs
unifyT _ bs IntType NumType = left "unifyT. can't store float as int"
unifyT _ bs NumType IntType = return bs
unifyT _ bs NumType NumType = return bs
unifyT _ bs NumType (VecType [] NumType) = return bs
unifyT _ bs (VecType [] NumType) NumType = return bs
unifyT u bs t1@(TypedefType _) t2@(TypedefType _) = do
  t1' <- normalizeType t1
  t2' <- normalizeType t2
  unifyType u bs t1' t2'
unifyT u bs (StructType _ (ST _ fields1)) (StructType _ (ST _ fields2)) = do
  let (nfs1, ts1) = unzip fields1
      (nfs2, ts2) = unzip fields2
  assert (nfs1 == nfs2) $ "unification failure: field names don't match: " ++ sep fields1 fields2
  unifyMany u bs ts1 ts2
unifyT u bs (PtrType t1) (PtrType t2) = unifyType u bs t1 t2
unifyT _ bs e1 e2 = left $ "unification failure:\n" ++ sep e1 e2

unifyMany :: UnifyMethod -> Bindings -> [Type] -> [Type] -> M Bindings
unifyMany u bs ts1 ts2 = do
  assert (length ts1 == length ts2) $ "unifyMany failure:\n" ++ sep ts1 ts2
  foldM (uncurry . unifyType u) bs $ zip ts1 ts2


-- Used by typeCheck whenever types should be equal
unifyGen :: Type -> Type -> M ()
unifyGen t1 t2 = unifyType Universal [] t1 t2 >> return ()

-- takes fn, args, returns fn applied to correct implict arguments
getImplicits :: CExpr -> [CExpr] -> M [CExpr]
getImplicits fn args = do
  FnType (FnT implicits params out) <- local $ typeCheck fn
  argTypes <- mapM (local . typeCheck) args
  bindings <- unifyMany Extend [] (map snd params) argTypes
  let
    resolve var =
      case lookup var bindings of
        Nothing -> left $ "unresolved implicit argument: "
          ++ show var ++ " function:\n" ++ show fn
        Just x -> return x
  mapM (resolve . fst) implicits

numeric NumType = True
numeric IntType = True
numeric _ = False

numerics x y = numeric x && numeric y

joinNum IntType IntType = IntType
joinNum IntType NumType = NumType
joinNum NumType IntType = NumType
joinNum NumType NumType = NumType

typeCheck :: CExpr -> M Type
typeCheck x = normalizeType =<< typeCheck' x

-- Typecheck --
typeCheck' :: CExpr -> M Type
typeCheck' e@(var := b) = do
  t <- typeCheck' b
  extend var t
  return Void
typeCheck' e@(a :<= b) = do
  tl <- typeCheck' a
  tr <- typeCheck' b
  unifyGen tl tr
  return Void
typeCheck' (Declare t var) = do
  extend var t
  return Void
typeCheck' (Ptr a) = do
  t <-typeCheck' a
  case t of
    VecType d b -> return $ VecType (1 : d) b
    _ -> return $ VecType [1] t
typeCheck' (a :> b) = do
  typeCheck' a
  typeCheck' b
typeCheck' e@(a :# b) = do
  ta <- typeCheck' a
  tb <- typeCheck' b
  case (ta, tb) of
    (VecType (a0 : as) t1, VecType (b0 : bs) t2) -> do
      assert (as == bs) $ "expr concat mismatch: " ++ show e ++ " !! " ++ sep as bs
      unifyGen t1 t2
      return $ VecType ((a0 + b0) : as) t1
    _ -> error $ "typeCheck' :#. " ++ sep ta tb ++ "\n" ++ sep a b
typeCheck' e@(Offset a b) = do
  typeA <- typeCheck' a
  typeB <- typeCheck' b
  case (typeA, typeB) of
    -- TODO check lengths
    -- These are for pointer offsets
    (VecType (_ : _) _, IntType) -> return typeA
    (IntType, VecType (_ : _) _) -> return typeB
    _ -> left $ "typeCheck'. Offset. should have VecType, IntType. have: " ++ sep typeA typeB ++ "\n" ++ sep a b
typeCheck' e@(a :+ b) = do
  typeA <- typeCheck' a
  typeB <- typeCheck' b
  case (typeA, typeB) of
    --(VecType (_ : _) _, IntType) -> return typeA
    --(IntType, VecType (_ : _) _) -> return typeB
    (IntType, IntType) -> return IntType
    (NumType, IntType) -> return NumType
    (IntType, NumType) -> return NumType
    _ -> do
      vectorTypeEq typeA typeB $ "vector sum mismatch:\n" ++
        sep typeA typeB ++ "\n" ++ sep a b
      return typeA
typeCheck' e@(a :/ b) = do
  typeA <- typeCheck' a
  typeB <- typeCheck' b
  assert (numeric typeB) $ "denominator must be a number: " ++ show e
  return typeA
typeCheck' e@(a :* b) = do
  typeA <- typeCheck' a
  typeB <- typeCheck' b
  case (typeA, typeB) of
    (x, y) | numerics x y -> return $ joinNum x y
    (VecType [a0, a1] n1, VecType [b0, b1] n2) | numeric n1 && numeric n2 && n1 == n2 -> do
      assert (a1 `numericEquiv` b0) $ "matrix product mismatch: " ++ show e
      return $ VecType [a0, b1] n1
    (VecType [a0] n1, VecType [b0] n2) | numeric n1 && numeric n2 && n1 == n2 -> do
      assert (a0 `numericEquiv` b0) $ "vector product mismatch: " ++ show e
      return $ VecType [a0] n1
    (VecType [a0, a1] n1, VecType [b0] n2) | numeric n1 && numeric n2 && n1 == n2 -> do
      assert (a1 `numericEquiv` b0) $ "matrix/vector product mismatch:\n" ++
        sep (reduceArith a1) (reduceArith b0) ++ "\n" ++ sep a b
      return $ VecType [a0] n1
    (VecType [a1] n1, VecType [b0, b1] n2) | numeric n1 && numeric n2 && n1 == n2 -> do
      assert (a1 `numericEquiv` b0) $ "vector/matrix product mismatch: " ++ show e
      return $ VecType [b1] n1
    _ -> error ("improper product:\n" ++ sep typeA typeB ++ "\n" ++ sep a b)
typeCheck' (Vec var bound body) = do
  t <- withBindings [(var, IntType)] (typeCheck' body)
  case t of
    VecType bs bt ->
      return $ VecType (bound : bs) bt
    Void -> return Void
    _ -> return $ VecType [bound] t
typeCheck' (Ref var) = varType var
-- TODO get rid of this Expr?
typeCheck' (Return e) = typeCheck' e
typeCheck' VoidExpr = return Void
typeCheck' (IntLit _) = return IntType
typeCheck' (NumLit _) = return NumType
typeCheck' (StrLit _) = return stringType
typeCheck' (a :! b) = do
  itype <- typeCheck' b
  case itype of
    IntType -> return ()
    t -> error $ sep t b
  ta <- typeCheck' a
  case ta of
    VecType [_] t -> return t
    VecType (_ : as) t ->
      return $ VecType as t
    _ -> error $ "LOOK: " ++ sep a b
typeCheck' (Sigma body) = do
  VecType (_ : as) t <- typeCheck' body
  return $ VecType as t
typeCheck' (Negate x) = typeCheck' x
typeCheck' (Unary "transpose" m) = do
  VecType [rs, cs] t <- typeCheck' m
  return $ VecType [cs, rs] t
typeCheck' e@(Unary "inverse" m) = do
  -- TODO replace with case
  VecType [rs, cs] t <- typeCheck' m
  assert (rs `numericEquiv` cs) $ "typeCheck'. inverse applied to non-square matrix: " ++ show e
  return $ VecType [cs, rs] t
typeCheck' e@(FunctionDef var t@(FnT implicits params out) body) = do
  extend var (FnType t)
  tbody <- withBindings (implicits ++ params) $ typeCheck' body
  -- unifyGen tbody out
  return Void
typeCheck' e@(Extern var t) = do
  extend var t
  return Void
typeCheck' e@(App f args) = do
  FnType (FnT implicits params out) <- typeCheck' f
  argTypes <- mapM typeCheck' args
  bindings <- unifyMany Extend [] (map snd params) argTypes
  let out' = foldl (\term (var, val) -> fmap (subst var val) term) out bindings
  return $ out'
typeCheck' (AppImpl f _ args) = typeCheck' (App f args)
typeCheck' (StructDecl name tp) = do
  extendTypedef name (StructType name tp)
  let fields = map fst $ st_fields tp
  assert (length (nub fields) == length fields) $
    "typeCheck'. struct declaration fields are not unique: " ++ show tp
  return Void
typeCheck' (s :. f) = do
  t <- typeCheck s
  case t of
    StructType _ (ST _ fieldTypes) -> do
      case lookup f fieldTypes of
        Just t -> return t
        Nothing -> left $ "typeCheck'. field is not a member of struct:\n"
          ++ sep f fieldTypes
    _ -> error $ "typeCheck'. not a struct: " ++ sep s t
--TODO
--typeCheck' (s :-> f) = do
--  PtrType (StructType (ST fieldTypes)) <- typeCheck' s
--  case lookup f fieldTypes of
--    Just t -> return t
--    Nothing -> left $ "typeCheck'. field is not a member of struct:\n"
--      ++ sep f fieldTypes
typeCheck' x = error ("typeCheck': " ++ ppExpr Lax x)

-- Compilation Utils --
-- TODO capture
subst :: Variable -> CExpr -> CExpr -> CExpr
subst var val v = visit fix v
  where
    fix (Ref v) | v == var = val
    fix v = v

compileMMMul :: CExpr -> (CExpr, CExpr) -> CExpr -> (CExpr, CExpr) -> M CExpr
compileMMMul x (r1, c1) y (r2, c2) = do
  i <- freshName
  inner <- freshName
  j <- freshName
  x' <- flattenTerm x
  y' <- flattenTerm y
  xb <- body x' (Ref i) (Ref inner)
  yb <- body y' (Ref inner) (Ref j)
  return $
    Vec i r1 $ Vec j c2 $ Sigma $
      Vec inner c1 (xb * yb)
  where
    body vec v1 v2 = return ((vec :! v1) :! v2)

flattenTerm :: CExpr -> M CExpr
flattenTerm e | not (compoundVal e) = return e
flattenTerm e = do
  n <- freshName
  return $ (n := e :> Ref n)

compileMVMul :: CExpr -> (CExpr, CExpr) -> CExpr -> CExpr -> M CExpr
compileMVMul x (r1, c1) y rows = do
  i <- freshName
  inner <- freshName
  return $
    Vec i rows $ Sigma $
      Vec inner c1 (((x :! (Ref i)) :! (Ref inner)) * (y :! (Ref inner)))

compileFunctionArgs f args = do
  (cont, fn, rargs) <- foldM step (id, f, []) args
  implicits <- getImplicits f args
  return $ cont (AppImpl fn implicits (reverse rargs))
  where
    --step :: (CExpr -> CExpr, CExpr, [CExpr]) -> CExpr -> M (...)
    step (cont, fn, args) arg =
      if compoundVal arg
      then do
        n <- freshName
        return (\e -> (n := arg) :> e, fn, (Ref n) : args)
      else return (cont, fn, arg : args)

compoundVal (Ref _) = False
compoundVal (IntLit _) = False
compoundVal (StrLit _) = False
compoundVal (a :! b) = compoundVal a || compoundVal b
compoundVal (a :+ b) = compoundVal a || compoundVal b
compoundVal (a :* b) = compoundVal a || compoundVal b
compoundVal (a :/ b) = compoundVal a || compoundVal b
compoundVal (a :> b) = compoundVal b
compoundVal _ = True


simpleVal (Unary _ _)  = False
simpleVal (a :! b) = simpleVal a && simpleVal b
simpleVal (a :+ b) = simpleVal a && simpleVal b
simpleVal (a :* b) = simpleVal a && simpleVal b
simpleVal _ = True

-- Term Reduction --
compile :: CExpr -> M CExpr
-- Iterate compileStep to convergence
compile expr = do
  -- _ <- typeCheck expr
  head <$> (scanM step expr)
  where
    sep = "\n------------\n"
    debugFlag = False

    step expr =
     let
        printStep =
          if debugFlag
          then
            case flatten expr of
              Right e' -> trace (sep ++ ppLine Lax "" e' ++ sep)
              Left _ -> id
          else id
     in printStep $ local $ compileStep Top expr

-- TODO remove dependence on context?
data RWContext = Top | LHS | RHS
  deriving (Show)

pushExpr :: CExpr -> M ()
pushExpr e =
  modify $ \s -> s { term_stack = e : term_stack s }

popExpr :: M ()
popExpr = modify $ \s -> s { term_stack = tail $ term_stack s }

compileStep :: RWContext -> CExpr -> M CExpr
compileStep c expr = do
  pushExpr expr
  expr' <- compileStep' c expr
  popExpr
  return expr'

-- TODO is this confluent? how could we prove it?
compileStep' :: RWContext -> CExpr -> M CExpr

-- Initialization -> Declaration; Assignment
-- var := b  -->  (Decl type var); (a :<= b)
compileStep' _ e@(var := b) = do
  t <- local $ typeCheck b
  extend var t
  -- TODO remove/add cleaner instrumentation option
  let debugFlag = False
  let notGenVar ('v' : 'a' : 'r' : _) = False
      notGenVar _ = True
  post <- case t of
            VecType _ _ | debugFlag && notGenVar var ->
              do
                let pname = "printf" :$ StrLit (var ++ "\n")
                p <- generatePrinter var t
                return [pname, p, newline ""]
            _ -> return []

  return $ seqList $
    [ Declare t var
    , (Ref var) :<= b
    ] ++ post

-- Keep type environment "current" while compiling
compileStep' _ e@(Declare t var) = do
  extend var t
  return $ e
compileStep' Top e@(Extern var t) = do
  extend var t
  return e
compileStep' Top e@(StructDecl name tp) = do
  extendTypedef name (StructType name tp)
  return e

compileStep' Top e@(FunctionDef var t@(FnT implicits params _) body) = do
  body' <- withBindings (implicits ++ params) $ compileStep Top body
  extend var $ FnType t
  return $ (FunctionDef var t body')

compileStep' _ e@(Unary "transpose" m) = do
  VecType [rows, cols] _ <- local $ typeCheck m
  i <- freshName
  j <- freshName
  return $ Vec i cols $ Vec j rows $ ((m :! (Ref j)) :! (Ref i))

compileStep' _ e@(Unary "inverse" m) = do
  VecType [dim, _] t <- local $ typeCheck m
  inv <- freshName
  return $ seqList [
    Declare (VecType [dim, dim] t) inv,
    App "inverse" [m, Ref inv],
    Ref inv]

-- Arithmetic: +, *, /  --
compileStep' ctxt e@(x :+ y) = do
  tx <- local $ typeCheck x
  ty <- local $ typeCheck y
  case (tx, ty) of
    -- pointwise add
    (VecType (len1 : _) t1, VecType (len2 : _) t2) | numerics t1 t2 -> do
      i <- freshName
      return $ Vec i len1 (x :! (Ref i) + y :! (Ref i))
    (_, _) | compoundVal x -> do
      a <- freshName
      return $ (a := x) :> (Ref a :+ y)
    (_, _) | compoundVal y -> do
      b <- freshName
      return $ (b := y) :> (x :+ Ref b)
    (NumType, NumType) | NumLit a <- x, NumLit b <- y ->
      return $ NumLit (a + b)
    (t1, t2) | numerics t1 t2 -> do
      x' <- compileStep ctxt x
      y' <- compileStep ctxt y
      return $ x' + y'
    -- TODO this handles adding ptr to int; does it allow anything else?
    _ -> return e

compileStep' _ ((a :> b) :* c) = return $ a :> (b :* c)
compileStep' _ (c :* (a :> b)) = return $ a :> (c :* b)

compileStep' ctxt e@(x :* y) = do
  tx <- local $ typeCheck x
  ty <- local $ typeCheck y
  case (tx, ty) of
    -- Matrix product
    -- m × n  -->  Vec i (Vec j (∑ (Vec k (m i k * n k j))))
    (VecType [r1, c1] _, VecType [r2, c2] _) ->
      compileMMMul x (r1, c1) y (r2, c2)
    -- matrix/vector vector/matrix products
    (VecType [r1, c1] _, VecType [r2] _) ->
      compileMVMul x (r1, c1) y r2
    (VecType (len1 : _) _, VecType (len2 : _) _) -> do
      assert (len1 == len2) $ "product length mismatch: " ++ show e
      i <- freshName
      return $ Vec i len1 (x :! (Ref i) :* y :! (Ref i))
    (n, v@(VecType (len : _) _)) | numeric n -> scale x y len
    (v@(VecType (len : _) _), n) | numeric n -> scale y x len
    (_, _) | compoundVal x -> do
      a <- freshName
      return $ (a := x) :> (Ref a :* y)
    (_, _) | compoundVal y -> do
      b <- freshName
      return $ (b := y) :> (x :* Ref b)
    -- (NumType, NumType) | IntLit a <- x, IntLit b <- y -> return $ IntLit (a * b)
    (t1, t2) | numerics t1 t2 -> do
      x' <- compileStep ctxt x
      y' <- compileStep ctxt y
      return $ x' * y'
  where
    scale s vec len = do
      i <- freshName
      return $ Vec i len (s :* vec :! (Ref i))

compileStep' ctxt e@(x :/ y) = do
  tx <- local $ typeCheck x
  ty <- local $ typeCheck y
  case (tx, ty) of
    -- pointwise div
    (VecType (len : _) _, NumType) -> do
      i <- freshName
      return $ Vec i len ((x :! (Ref i)) :/ y)
    (n1, n2) | numerics n1 n2, compoundVal x -> do
      a <- freshName
      return $ (a := x) :> (Ref a :/ y)
    (n1, n2) | numerics n1 n2, compoundVal y -> do
      b <- freshName
      return $ (b := y) :> (x :/ Ref b)
    (n1, n2) | numerics n1 n2 -> do
      x' <- compileStep ctxt x
      y' <- compileStep ctxt y
      return $ x' / y'
    p -> error ("compileStep': " ++ show p ++ "\n" ++ show x ++ "\n" ++ show y)

-- Juxtaposition
-- a :<= u # v  -->  (a :<= u); (a + size u :<= v)
compileStep' _ (a :<= u :# v) = do
  VecType (offset : _) _ <- local $ typeCheck u
  -- TODO (a + offset) will always be wrapped by an index operation?
  return $ (a :<= u) :> ((Offset a offset) :<= v)

compileStep' _ (a :<= (Ptr x)) = do
  n <- freshName
  return (a :<= Vec n 1 x)

-- Sequence assignment
-- a :<= (u; v)  --> u; (a :<= v)
compileStep' _ (a :<= (u :> v)) = do
  return $
    u :>
    a :<= v

-- Summation
-- a :<= ∑ (Vec i y_i)  -->  (a :<= 0); (Vec i (a :<= a + y_i))
compileStep' _ (a :<= (Sigma vec)) = do
  i <- freshName
  VecType (len : _) _ <- local $ typeCheck vec
  let body = a :<= a + (vec :! (Ref i))
  return $
    (a :<= 0.0) :>
    (Vec i len $ body)

-- Vector assignment
-- a :<= Vec i b_i  -->  Vec (a + i :<= b_i)
compileStep' ctxt (a :<= (Vec var r body)) = do
  let lhs = a :! (Ref var)
  rhs <- withBindings [(var, IntType)] $ compileStep RHS body
  return $ Vec var r (lhs :<= rhs)
  --return $ Vec var r (lhs :<= body)

-- Lift compound values before (a :<= Vector) wraps vector body in a loop
compileStep' _ (a :<= (b :* c)) | compoundVal b = do
  n <- freshName
  return $ (n := b) :> (a :<= Ref n :* c)
compileStep' _ (a :<= (b :* c)) | compoundVal c = do
  n <- freshName
  return $ (n := c) :> (a :<= b :* Ref n)

-- Vector assignment, reduction on RHS
compileStep' ctxt (a :<= b) = do
  bt <- local $ typeCheck b
  case bt of
    -- Avoid repeatedly calling inverse
    -- TODO generalize?
    VecType (len : _) _ | simpleVal b -> do
      i <- freshName
      let lhs = (a :! (Ref i))
      return $ Vec i len (lhs :<= b :! (Ref i))
    _ -> do
      a' <- compileStep LHS a
      b' <- compileStep RHS b
      return $ a' :<= b'

compileStep' ctxt e@(Negate x) = do
  tx <- local $ typeCheck x
  case tx of
    n | numeric n, compoundVal x -> do
      a <- freshName
      return $ (a := x) :> (Negate (Ref a))
    n | numeric n -> do
      x' <- compileStep ctxt x
      return $ Negate x'
    VecType (len : _) _ -> do
      i <- freshName
      return $ Vec i len (- (x :! (Ref i)))

-- Reduces function args and lifts compound ones
compileStep' _ e@(App f args) = do
  compileFunctionArgs f args

-- Reduction of an index operation
compileStep' _ ((Vec var b body) :! ind) =
  return $ subst var ind body
compileStep' RHS e@((a :+ b) :! ind) =
  return $ (a :! ind) + (b :! ind)
compileStep' ctxt@RHS (e@(a :* b) :! ind) = do
  ta <- local $ typeCheck a
  tb <- local $ typeCheck b
  case (ta, tb) of
    (VecType [len1] _, VecType [len2] _) -> return $ (a :! ind) * (b :! ind)
    (t1, t2) | numerics t1 t2 -> return $ (a :! ind) * (b :! ind)
    _ -> do
      e' <- compileStep ctxt e
      return $ e' :! ind
compileStep' ctrxt ((a :> b) :! c) = return $ a :> (b :! c)
-- Pointer literal elimination
compileStep' _ e@((Ptr x) :! (IntLit 0)) = return x
compileStep' ctxt (a :! b) = do
  a' <- compileStep ctxt a
  b' <- compileStep ctxt b
  return (a' :! b')


-- Single iteration loop unrolling
compileStep' _ e@(Vec var (IntLit 1) body) = do
  t <- local $ typeCheck e
  case t of
    Void -> return $ subst var (IntLit 0) body
    _ -> return e

-- Reduction within a Vec
-- Vec i x  -->  Vec i x
compileStep' ctxt (Vec var r body) = do
  body' <- withBindings [(var, IntType)] $ compileStep ctxt body
  --body' <- withBindings [] $ compileStep ctxt body
  return $ Vec var r body'

-- Sequencing
-- a :> b  -->  a :> b
compileStep' ctxt (a :> b) = do
  a' <- compileStep ctxt a
  b' <- compileStep ctxt b
  return (a' :> b')

-- id
-- x  -->  x
compileStep' _ x = return x

