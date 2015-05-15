-- TODO
-- need uniform way of rewriting
--   C[ a :> b ] --> a :> C[ b ]
--   and simplifying under a constructor
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Plover.Reduce
  ( compile, reduceArith, typeCheck
  -- TODO
  , defs
  , refs
  , seqExpr
  , hoist
  ) where

import Data.List (nub)
import qualified Data.Traversable as T (traverse)
import Control.Monad.Free (Free(..))
import Control.Applicative ((<$>))
import Control.Monad.State
import Data.Function (on)

import Debug.Trace (trace)

import qualified Language.Plover.Simplify as S
import Language.Plover.Types
import Language.Plover.Generics
import Language.Plover.Print
import Language.Plover.Macros (seqList, generatePrinter, newline)
import Language.Plover.Optimization

-- Searches syntax tree for simple arithmetic expressions, simplifies them
reduceArith :: CExpr -> CExpr
reduceArith t = mvisit msimplify reduceArith t
  where
    scale :: Int -> CExpr -> CExpr
    scale 1 x = x
    scale x (IntLit 1) = IntLit x
    scale x y = (IntLit x) * y

    simplify :: S.Expr CExpr Int -> CExpr
    simplify = S.simplify scale

    atom :: CExpr -> Maybe (S.Expr CExpr Int)
    atom = return . S.Atom

    msimplify :: CExpr -> Maybe CExpr
    msimplify e = do
      e' <- toExpr e
      let e'' = simplify e'
      if e == e'' then Nothing else return e''

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
    toExpr e@(Ref _) = atom e
    toExpr e@(_ :! _) = atom e
    --toExpr e@(a :! b) = return $ S.Atom e
    toExpr _ = Nothing

-- Attempts to simplify numeric expressions.
-- Called by type checker
numericEquiv :: CExpr -> CExpr -> Bool
numericEquiv = (==) `on` reduceArith

withBindings :: [(Variable, Type)] -> M a -> M a
withBindings bindings m = do
  env0 <- getVarTypes
  mapM_ (uncurry extend) bindings
  a <- m
  setVarTypes env0
  return a

local :: M a -> M a
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
walk _ e = e

-- Whether to treat R's as variables to be bound or as function arguments
data UnifyMethod = Extend | Universal

unifyExpr :: UnifyMethod -> Bindings -> CExpr -> CExpr -> M Bindings
unifyExpr u bs = unifyExpr' u bs `on` walk bs

unifyExpr' :: UnifyMethod -> Bindings -> CExpr -> CExpr -> M Bindings
unifyExpr' Extend bs (Ref v) x = return $ (v, x) : bs
unifyExpr' _ bs x y = do
  assert (x `numericEquiv` y) $ "unifyExpr failure:\n" ++ sep x y
  return bs

onM :: (a -> a -> M b) -> (c -> M a) -> c -> c -> M b
onM f g x y = do
  x' <- g x
  y' <- g y
  f x' y'

unifyType :: UnifyMethod -> Bindings -> Type -> Type -> M Bindings
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
unifyT _ bs BoolType BoolType = return bs
unifyT _ bs IntType IntType = return bs
unifyT _ _  IntType NumType = left "unifyT. can't store float as int"
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
unifyT _ _ e1 e2 = left $ "unification failure:\n" ++ sep e1 e2

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
  FnType (FnT implicits params _) <- local $ typeCheck fn
  argTypes <- mapM (local . typeCheck) args
  bindings <- unifyMany Extend [] (map snd params) argTypes
  let
    resolve var =
      case lookup var bindings of
        Nothing -> left $ "unresolved implicit argument: "
          ++ show var ++ " function:\n" ++ show fn
        Just x -> return x
  mapM (resolve . fst) implicits

numeric :: Type -> Bool
numeric NumType = True
numeric IntType = True
numeric _ = False

numerics :: Type -> Type -> Bool
numerics x y = numeric x && numeric y

joinNum :: Type -> Type -> Type
joinNum IntType IntType = IntType
joinNum IntType NumType = NumType
joinNum NumType IntType = NumType
joinNum NumType NumType = NumType
joinNum t1 t2 = error $ "joinNum: can't join non numeric types: " ++ sep t1 t2

-- Returns type of (a :! b) given appropriate type parameters for a
vecTail :: [CExpr] -> Type -> Error -> M Type
vecTail [] _ msg = left msg
vecTail [_] t _ = return t
vecTail (_ : ds) t _ = return $ VecType ds t

typeCheck :: CExpr -> M Type
typeCheck x = normalizeType =<< typeCheck' x

-- Typecheck --
typeCheck' :: CExpr -> M Type
typeCheck' (var := b) = do
  t <- typeCheck' b
  extend var t
  return Void
typeCheck' (a :<= b) = do
  tl <- typeCheck' a
  tr <- typeCheck' b
  unifyGen tl tr
  return Void
typeCheck' (If cond t f) = do
  tt <- local $ typeCheck' t
  tf <- local $ typeCheck' f
  assert (tt == tf) $ "If branch expressions must have the same type, have: " ++ sep tt tf
  ctype <- typeCheck' cond
  case ctype of
    BoolType -> return tt
    _ -> left $ "If condition is not a BoolType, got: " ++ show ctype
typeCheck' (Extension t) =
  typeCheck t
typeCheck' (Declare t var) = do
  extend var t
  return Void
typeCheck' (Ptr a) = do
  t <-typeCheck' a
  case t of
    VecType d b -> return $ VecType (1 : d) b
    _ -> return $ VecType [1] t
typeCheck' (a :> b) = do
  _ <- typeCheck' a
  typeCheck' b
typeCheck' e@(a :# b) = do
  ta <- typeCheck' a
  tb <- typeCheck' b
  case (ta, tb) of
    (VecType (a0 : as) t1, VecType (b0 : bs) t2) -> do
      assert (as == bs) $ "expr concat mismatch: " ++ show e ++ " !! " ++ sep as bs
      unifyGen t1 t2
      return $ VecType ((a0 + b0) : as) t1
    _ -> left $ "typeCheck' :#. " ++ sep ta tb ++ "\n" ++ sep a b

typeCheck' (a :+ b) = do
  typeA <- typeCheck' a
  typeB <- typeCheck' b
  case (typeA, typeB) of
    (IntType, IntType) -> return IntType
    (NumType, IntType) -> return NumType
    (IntType, NumType) -> return NumType
    (VecType (_ : _) _, IntType) -> return typeA
    (IntType, VecType (_ : _) _) -> return typeB
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
    (VecType [a0, a1] n1, VecType [b0, b1] n2) | numerics n1 n2 && n1 == n2 -> do
      assert (a1 `numericEquiv` b0) $ "matrix product mismatch: " ++ show e
      return $ VecType [a0, b1] n1
    (VecType [a0] n1, VecType [b0] n2) | numerics n1 n2 && n1 == n2 -> do
      assert (a0 `numericEquiv` b0) $ "vector product mismatch: " ++ show e
      return $ VecType [a0] n1
    (VecType [a0, a1] n1, VecType [b0] n2) | numerics n1 n2 && n1 == n2 -> do
      assert (a1 `numericEquiv` b0) $ "matrix/vector product mismatch:\n" ++
        sep (reduceArith a1) (reduceArith b0) ++ "\n" ++ sep a b
      return $ VecType [a0] n1
    (VecType [a1] n1, VecType [b0, b1] n2) | numerics n1 n2 && n1 == n2 -> do
      assert (a1 `numericEquiv` b0) $ "vector/matrix product mismatch: " ++ show e
      return $ VecType [b1] n1
    (n1, VecType d n2) | numerics n1 n2 -> return $ VecType d (joinNum n1 n2)
    (VecType d n2, n1) | numerics n1 n2-> return $ VecType d (joinNum n1 n2)
    _ -> left ("improper product:\n" ++ sep typeA typeB ++ "\n" ++ sep a b)
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
typeCheck' (Assert c) = do
  btype <- typeCheck' c
  case btype of
    BoolType -> return Void
    t -> left $ "Assert condition must be BoolType, got: " ++ sep t btype
typeCheck' (Equal a b) = do
  atype <- typeCheck' a
  btype <- typeCheck' b
  if atype == btype
    then return BoolType
    else left $ "Equality test between values with different types: " ++ sep atype btype
typeCheck' VoidExpr = return Void
typeCheck' (IntLit _) = return IntType
typeCheck' (NumLit _) = return NumType
typeCheck' (StrLit _) = return stringType
typeCheck' (BoolLit _) = return BoolType
typeCheck' (a :! b) = do
  itype <- typeCheck' b
  case itype of
    IntType -> return ()
    t -> left $ "typeCheck. index not an integer: " ++ sep t b
  VecType ds t <- typeCheck' a
  vecTail ds t $ "LOOK: " ++ sep a b
typeCheck' e@(FlatIndex vec ind dim) = do
  itype <- typeCheck' ind
  case itype of
    IntType -> return ()
    t -> left $ "typeCheck. index not an integer: " ++ sep t ind
  VecType (d : ds) t <- typeCheck' vec
  assert (product ds `numericEquiv` product dim) $ ("internal typeCheck error. malformed FlatIndex: "
    ++ sep d dim ++ "\n" ++ show e)
  vecTail (d : ds) t "this can't happen"
typeCheck' e@(Sigma body) = do
  VecType ds t <- typeCheck' body
  vecTail ds t $ "Attempted to sum scalar type: " ++ show e
typeCheck' (Negate x) = typeCheck' x
typeCheck' (Unary "transpose" m) = do
  VecType [rs, cs] t <- typeCheck' m
  return $ VecType [cs, rs] t
typeCheck' e@(Unary "inverse" m) = do
  -- TODO replace with case
  VecType [rs, cs] t <- typeCheck' m
  assert (rs `numericEquiv` cs) $ "typeCheck'. inverse applied to non-square matrix: " ++ show e
  return $ VecType [cs, rs] t
typeCheck' (FunctionDef var t@(FnT implicits params _) body) = do
  extend var (FnType t)
  _ <- withBindings (implicits ++ params) $ typeCheck' body
  -- TODO: actually typecheck output
  -- unifyGen tbody out
  return Void
typeCheck' (Extern var t) = do
  extend var t
  return Void
typeCheck' (App f args) = do
  FnType (FnT _ params out) <- typeCheck' f
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
        Just t' -> return t'
        Nothing -> left $ "typeCheck'. field is not a member of struct:\n"
          ++ sep f fieldTypes
    _ -> error $ "typeCheck'. not a struct: " ++ sep s t
typeCheck' (s :-> f) = do
  t0 <- typeCheck s
  case t0 of
    PtrType t1 -> do
      t2 <- normalizeType t1
      case t2 of
        StructType _ (ST _ fieldTypes) -> do
          case lookup f fieldTypes of
            Just t3 -> return t3
            Nothing -> left $ "typeCheck'. field is not a member of struct:\n"
              ++ sep f fieldTypes
        _ -> left $ "typeCheck'. not a pointer to a struct: " ++ sep s t2
    _ -> left $ "typeCheck'. not a pointer to a struct: " ++ sep s t0
typeCheck' x = error ("typeCheck': " ++ ppExpr Lax x)

-- Compilation Utils --
-- TODO capture
subst :: Variable -> CExpr -> CExpr -> CExpr
subst var val v = visit f v
  where
    f (Ref v') | v' == var = val
    f v' = v'

compileMMMul :: CExpr -> (CExpr, CExpr) -> CExpr -> (CExpr, CExpr) -> M CExpr
compileMMMul x (r1, c1) y (_, c2) = do
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
compileMVMul x (_, c1) y rows = do
  i <- freshName
  inner <- freshName
  return $
    Vec i rows $ Sigma $
      Vec inner c1 (((x :! (Ref i)) :! (Ref inner)) * (y :! (Ref inner)))

compileFunctionArgs :: CExpr -> [CExpr] -> M CExpr
compileFunctionArgs f args = do
  (cont, fn, rargs) <- foldM step (id, f, []) args
  implicits <- getImplicits f args
  return $ cont (AppImpl fn implicits (reverse rargs))
  where
    --step :: (CExpr -> CExpr, CExpr, [CExpr]) -> CExpr -> M (...)
    step (cont, fn, args') arg =
      if compoundVal arg
      then do
        n <- freshName
        let declArg = \e -> (n := arg) :> e
        return (cont . declArg, fn, (Ref n) : args')
      else return (cont, fn, arg : args')

compoundVal :: CExpr -> Bool
compoundVal (Ref _) = False
compoundVal (IntLit _) = False
compoundVal (StrLit _) = False
compoundVal (BoolLit _) = False
compoundVal (a :=: b) = compoundVal a || compoundVal b
compoundVal (a :! b)  = compoundVal a || compoundVal b
compoundVal (a :+ b)  = compoundVal a || compoundVal b
compoundVal (a :* b)  = compoundVal a || compoundVal b
compoundVal (a :/ b)  = compoundVal a || compoundVal b
compoundVal (_ :> b)  = compoundVal b
compoundVal _ = True

simpleVal :: CExpr -> Bool
simpleVal (Unary _ _)  = False
simpleVal (a :! b) = simpleVal a && simpleVal b
simpleVal (a :+ b) = simpleVal a && simpleVal b
simpleVal (a :* b) = simpleVal a && simpleVal b
simpleVal _ = True

-- Term Reduction --
compile :: CExpr -> M CExpr
-- Iterate compileStep to convergence
compile expr = do
  t <- local $ typeCheck expr
  assert (t == Void) $ "compile expects a Void-type statement, got: " ++ show t
  head <$> (scanM step expr)
  where
    sepLine = "\n------------\n"
    debugFlag = False

    step expr' =
     let
        printStep =
          if debugFlag
          then
            case flatten expr' of
              Right e' -> trace (sepLine ++ ppLine Lax "" e' ++ sepLine)
              Left _ -> id
          else id
     in printStep $ local $ compileStep Top expr'

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
compileStep' _ (var := b) = do
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
compileStep' _ e@(Extension t) = do
  _ <- typeCheck t
  return e
compileStep' _ (Declare t var) = do
  extend var t
  let t' = fmap reduceArith t
  return $ Declare t' var
compileStep' Top e@(Extern var t) = do
  extend var t
  return e
compileStep' Top e@(StructDecl name tp) = do
  extendTypedef name (StructType name tp)
  return e

compileStep' Top (FunctionDef var t@(FnT implicits params _) body) = do
  body' <- withBindings (implicits ++ params) $ compileStep Top body
  extend var $ FnType t
  return $ (FunctionDef var t body')

compileStep' _ (Unary "transpose" m) = do
  VecType [rows, cols] _ <- local $ typeCheck m
  i <- freshName
  j <- freshName
  return $ Vec i cols $ Vec j rows $ ((m :! (Ref j)) :! (Ref i))

compileStep' _ (Unary "inverse" m) = do
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
    (VecType (len1 : _) t1, VecType (_ : _) t2) | numerics t1 t2 -> do
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
    _ -> recurse ctxt e

compileStep' _ ((a :> b) :+ c) = return $ a :> (b :+ c)
compileStep' _ (c :+ (a :> b)) = return $ a :> (c :+ b)
compileStep' _ ((a :> b) :* c) = return $ a :> (b :* c)
compileStep' _ (c :* (a :> b)) = return $ a :> (c :* b)

compileStep' _ (Assert c) = return $ App "assert" [c]

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
    -- TODO should only apply to [len1], [len2] ?
    (VecType (len1 : _) _, VecType (len2 : _) _) -> do
      assert (len1 == len2) $ "product length mismatch: " ++ show e
      i <- freshName
      return $ Vec i len1 (x :! (Ref i) :* y :! (Ref i))
    (n, (VecType (len : _) _)) | numeric n -> scale x y len
    ((VecType (len : _) _), n) | numeric n -> scale y x len
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
    (t1, t2) -> left $ "don't know how to multiply types: " ++ sep t1 t2
  where
    scale s vec len = do
      i <- freshName
      return $ Vec i len (s :* vec :! (Ref i))

compileStep' ctxt (x :/ y) = do
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
  return $ (a :<= u) :> ((a :+ offset) :<= v)

compileStep' _ (a :<= (Ptr x)) = do
  n <- freshName
  return (a :<= Vec n 1 x)

-- Sequence assignment
-- a :<= (u; v)  --> u; (a :<= v)
compileStep' _ (a :<= (u :> v)) = do
  return $
    u :>
    a :<= v
compileStep' _ ((u :> v) :<= a) = do
  return $
    u :>
    v :<= a

-- Summation
-- a :<= ∑ (Vec i y_i)  -->  (a :<= 0); (Vec i (a :<= a + y_i))
compileStep' _ (a :<= (Sigma vec)) = do
  i <- freshName
  VecType (len : _) _ <- local $ typeCheck vec
  let body = a :<= a + (vec :! (Ref i))
  return $
    (a :<= 0) :>
    (Vec i len $ body)

-- Vector assignment
-- a :<= Vec i b_i  -->  Vec (a + i :<= b_i)
compileStep' _ (a :<= (Vec var r body)) = do
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
compileStep' ctxt e@(a :<= b) = do
  bt <- local $ typeCheck b
  case bt of
    -- Avoid repeatedly calling inverse
    -- TODO generalize?
    VecType (len : _) _ | simpleVal b -> do
      i <- freshName
      let lhs = (a :! (Ref i))
      return $ Vec i len (lhs :<= b :! (Ref i))
    _ -> do
      -- TODO call reduceArith?
      recurse ctxt e

compileStep' ctxt (Negate x) = do
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
    t -> left $ "don't know how to negate non numeric type: " ++ show t

-- Reduces function args and lifts compound ones
compileStep' _ (App f args) = do
  compileFunctionArgs f args

-- Reduction of an index operation
compileStep' _ (FlatIndex (Vec var _ body) ind _) =
  return $ subst var ind body

compileStep' RHS e@(FlatIndex (a :+ b) ind _) = do
  ta <- local $ typeCheck a
  tb <- local $ typeCheck b
  case (ta, tb) of
    (VecType _ _, VecType _ _) ->
      return $ (a :! ind) + (b :! ind)
    _ -> recurse RHS e

compileStep' ctxt@RHS e@(FlatIndex (a :* b) ind _) = do
  ta <- local $ typeCheck a
  tb <- local $ typeCheck b
  case (ta, tb) of
    (VecType [_] _, VecType [_] _) -> return $ (a :! ind) * (b :! ind)
    (t1, t2) | numerics t1 t2 -> return $ (a :! ind) * (b :! ind)
    _ -> do
      recurse ctxt e
compileStep' _ (FlatIndex (a :> b) c _) = return $ a :> (b :! c)
compileStep' _ (FlatIndex a (b :> c) _) = return $ b :> (a :! c)

compileStep' _ (e :! i) = do
  VecType (_ : ds) _ <- local $ typeCheck e
  return $ FlatIndex e i (ds)

-- Dim terms are not totally reduced
compileStep' ctxt (FlatIndex v ind dim) = do
  v'    <- compileStep ctxt v
  ind'  <- compileStep ctxt ind
  dim' <- mapM (compileStep ctxt) dim
  return $ FlatIndex v' ind' dim'

-- Pointer literal elimination
compileStep' _ (FlatIndex (Ptr x) (IntLit 0) _) = return x

-- Single iteration loop unrolling
compileStep' _ e@(Vec var (IntLit 1) body) = do
  t <- local $ typeCheck e
  case t of
    Void -> return $ subst var (IntLit 0) body
    _ -> return e

-- Finite unrolling
--compileStep' _ e@(Vec var (IntLit n) body) = do
--  t <- local $ typeCheck e
--  case t of
--    Void -> return $ seqList (map (\i -> subst var (IntLit i) body) [0..(n-1)])
--    _ -> return e

-- Reduction within a Vec
-- Vec i x  -->  Vec i x
compileStep' ctxt (Vec var r body) = do
  body' <- withBindings [(var, IntType)] $ compileStep ctxt body
  --body' <- withBindings [] $ compileStep ctxt body
  return $ Vec var (reduceArith r) body'

-- Sequencing
-- a :> b  -->  a :> b
--compileStep' ctxt (a :> b) = do
--  a' <- compileStep ctxt a
--  b' <- compileStep ctxt b
--  return (a' :> b')

-- Control flow
-- If -> If
compileStep' _ (If (a :> c) t f) = return $ a :> (If c t f)
compileStep' _ (If c t f) | compoundVal c = do
  n <- freshName
  return (n := c :> If (Ref n) t f)

-- If -> If
--compileStep' ctxt (If c t f) = do
--  c' <- local $ compileStep ctxt c
--  t' <- local $ compileStep ctxt t
--  f' <- local $ compileStep ctxt f
--  return (If c' t' f')

-- Vector comparison
compileStep' _ e@(x :=: y) = do
  tx <- local $ typeCheck x
  ty <- local $ typeCheck y
  case (tx, ty) of
    -- pointwise comparison
    (VecType (_ : _) _, VecType (_ : _) _) -> do
      left "Vector comparison not implemented"
    _ -> return e

-- generic recursion step
-- C[ x ] --> C[ rewrite x ]
compileStep' c x = recurse c x


recurse :: RWContext -> CExpr -> M CExpr
recurse ctxt (Free x) = fmap Free $ T.traverse (compileStep ctxt) x
recurse _ x = return x
