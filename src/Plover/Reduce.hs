{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
module Plover.Reduce
  ( compile, reduceArith, typeCheck
  ) where

import Data.List (intercalate)
import Data.Monoid hiding (Sum)
import qualified Data.Foldable as F (Foldable, fold)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence, mapM, traverse)
import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Monad.Trans.Either
import Control.Monad.State
import Data.String
import Data.Maybe (fromJust)
import Data.Function (on)

import Debug.Trace (trace)

import qualified Smash.Simplify as S
import Plover.Types
import Plover.Generics
import Plover.Print
import Plover.Macros (seqList, generatePrinter, newline)

-- Searches syntax tree for simple arithmetic expressions, simplifies them
reduceArith = mvisit toExpr step
  where
    scale 1 x = x
    scale x (Lit 1) = Lit x
    scale x y = (Lit x) * y

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
    toExpr (Lit i) = return $ S.Prim i
    toExpr (Neg x) = do
      x' <- toExpr x
      return $ S.Mul [S.Prim (-1), x']
    toExpr e@(R v) = return $ S.Atom e
    --toExpr e@(a :! b) = return $ S.Atom e
    toExpr x = Nothing

-- Attempts to simplify numeric expressions.
-- Called by type checker
numericEquiv :: CExpr -> CExpr -> Bool
numericEquiv = (==) `on` reduceArith

-- Type Checking
isDefined :: Variable -> M Bool
isDefined var = do
  (_, env) <- get
  case lookup var env of
    Nothing -> return False
    Just _ -> return True

varType :: Variable -> M Type
varType var = do
  (_, env) <- get
  case lookup var env of
    Nothing -> left $ "undefined var: " ++ var ++ "\n" ++ unlines (map show env)
    Just t -> return t

assert :: Bool -> Error -> M ()
assert cond msg = if cond then return () else left msg

withBindings :: [(Variable, Type)] -> M a -> M a
withBindings bindings m = do
  (_, env0) <- get
  mapM_ (uncurry extend) bindings
  a <- m
  modify $ \(c, _) -> (c, env0)
  return a

vectorTypeEq :: Type -> Type -> Bool
vectorTypeEq Void Void = True
vectorTypeEq (ExprType as) (ExprType bs) = and $ zipWith numericEquiv as bs

-- Unify, for type variables
type Bindings = [(Variable, CExpr)]

walk :: Bindings -> CExpr -> CExpr
walk bs (R v) =
  case lookup v bs of
    Nothing -> R v
    Just (R v') | v' == v -> R v
    Just (R v') -> walk bs (R v')
    Just val -> val
walk bs e = e

-- Whether to treat R's as variables to be bound or as function arguments
data UnifyMethod = Extend | Universal

unifyExpr :: UnifyMethod -> Bindings -> CExpr -> CExpr -> M Bindings
unifyExpr u bs = unifyExpr' u bs `on` walk bs

unifyExpr' :: UnifyMethod -> Bindings -> CExpr -> CExpr -> M Bindings
unifyExpr' Extend bs (R v) x = return $ (v, x) : bs
unifyExpr' _ bs x y = do
  assert (x `numericEquiv` y) $ "unifyExpr failure:\n" ++ sep x y
  return bs

unifyT :: UnifyMethod -> Bindings -> Type -> Type -> M Bindings
unifyT u bs (ExprType d1) (ExprType d2) =
  unifyMany u bs (map Dimension d1) (map Dimension d2)
unifyT u bs (FnType (FnT _ params1 out1)) (FnType (FnT _ params2 out2)) = do
  bs' <- unifyT u bs out1 out2
  unifyMany u bs' (map snd params1) (map snd params2)
unifyT u bs (Dimension d1) (Dimension d2) = do
  unifyExpr u bs d1 d2
unifyT _ bs Void Void = return bs
unifyT _ bs StringType StringType = return bs
unifyT _ bs IntType IntType = return bs
unifyT _ bs e1 e2 = left $ "unification failure:\n" ++ sep e1 e2

unifyMany :: UnifyMethod -> Bindings -> [Type] -> [Type] -> M Bindings
unifyMany u bs ts1 ts2 = do
  assert (length ts1 == length ts2) $ "unifyMany failure:\n" ++ sep ts1 ts2
  foldM (uncurry . unifyT u) bs $ zip ts1 ts2

-- takes fn, args, returns fn applied to correct implict arguments
getImplicits :: CExpr -> [CExpr] -> M [CExpr]
getImplicits fn args = do
  FnType (FnT implicits params out) <- typeCheck fn
  argTypes <- mapM typeCheck args
  bindings <- unifyMany Extend [] (map snd params) argTypes
  let 
    resolve var =
      case lookup var bindings of
        Nothing -> left $ "unresolved implicit argument: "
          ++ show var ++ " function:\n" ++ show fn
        Just x -> return x
  mapM (resolve . fst) implicits

-- Typecheck --
typeCheck :: CExpr -> M Type
typeCheck e@(var := b) = do
  t <- typeCheck b
  extend var t
  return Void
typeCheck e@(a :< b) = do
  tl <- typeCheck a
  tr <- typeCheck b
  unifyT Universal [] tl tr
  return Void
typeCheck (Declare t var) = do
  extend var t
  return Void
typeCheck (a :> b) = do
  typeCheck a
  typeCheck b
typeCheck e@(a :# b) = do
  ta <- typeCheck a
  tb <- typeCheck b
  case (ta, tb) of
    (ExprType (a0 : as), ExprType (b0 : bs)) -> do
      assert (as == bs) $ "expr concat mismatch: " ++ show e ++ " !! " ++ sep as bs
      return $ ExprType ((a0 + b0) : as)
    _ -> error $ "typeCheck :#. " ++ sep ta tb ++ "\n" ++ sep a b
typeCheck e@(a :+ b) = do
  typeA <- typeCheck a
  typeB <- typeCheck b
  case (typeA, typeB) of
    -- TODO check lengths
    -- These are for pointer offsets
    (ExprType (_ : _), ExprType []) -> return typeA
    (ExprType [], ExprType (_ : _)) -> return typeB
    _ -> do
      assert (vectorTypeEq typeA typeB) $ "vector sum mismatch:\n" ++ sep typeA typeB ++ "\n" ++ sep a b
      return typeA
typeCheck e@(a :/ b) = do
  typeA <- typeCheck a
  typeB <- typeCheck b
  assert (typeB == numType) $ "denominator must be a number: " ++ show e
  return typeA
typeCheck e@(a :* b) = do
  typeA <- typeCheck a
  typeB <- typeCheck b
  case (typeA, typeB) of
    (ExprType [], _) -> return typeB
    (_, ExprType []) -> return typeA
    (ExprType [a0, a1], ExprType [b0, b1]) -> do
      assert (a1 `numericEquiv` b0) $ "matrix product mismatch: " ++ show e
      return $ ExprType [a0, b1]
    (ExprType [a0], ExprType [b0]) -> do
      assert (a0 `numericEquiv` b0) $ "vector product mismatch: " ++ show e
      return $ ExprType [a0]
    (ExprType [a0, a1], ExprType [b0]) -> do
      assert (a1 `numericEquiv` b0) $ "matrix/vector product mismatch:\n" ++
        sep (reduceArith a1) (reduceArith b0) ++ "\n" ++ sep a b
      return $ ExprType [a0]
    (ExprType [a1], ExprType [b0, b1]) -> do
      assert (a1 `numericEquiv` b0) $ "vector/matrix product mismatch: " ++ show e
      return $ ExprType [b1]
    _ -> error ("product:\n" ++ sep typeA typeB ++ "\n" ++ sep a b)
typeCheck (Lam var bound body) = do
  mt <- withBindings [(var, numType)] (typeCheck body)
  case mt of
    ExprType btype -> 
      return $ ExprType (bound : btype)
    Void -> return Void
typeCheck (R var) = varType var
typeCheck (Free (IntLit _)) = return numType
typeCheck (a :! b) = do
  ExprType [] <- typeCheck b
  ta <- typeCheck a
  case ta of
    ExprType (_ : as) ->
      return $ ExprType as
    _ -> error $ "LOOK: " ++ sep a b
typeCheck (Free (Sigma body)) = do
  ExprType (_ : as) <- typeCheck body
  return $ ExprType as
typeCheck (Neg x) = typeCheck x
typeCheck (Free (Unary "transpose" m)) = do
  ExprType [rs, cs] <- typeCheck m
  return $ ExprType [cs, rs]
typeCheck e@(Free (Unary "inverse" m)) = do
  ExprType [rs, cs] <- typeCheck m
  assert (rs `numericEquiv` cs) $ "typeCheck. inverse applied to non-square matrix: " ++ show e
  return $ ExprType [cs, rs]
typeCheck e@(FnDef var t@(FnT implicits params _) body) = do
  extend var (FnType t)
  withBindings (implicits ++ params) $ typeCheck body
  return Void
typeCheck e@(Free (Extern var t)) = do
  extend var t
  return Void
typeCheck e@(Free (App f args)) = do
  FnType (FnT implicits params out) <- typeCheck f
  argTypes <- mapM typeCheck args
  bindings <- unifyMany Extend [] (map snd params) argTypes
  let out' = foldl (\term (var, val) -> fmap (subst var val) term) out bindings
  return $ out'
typeCheck (Free (AppImpl f _ args)) = typeCheck (Free (App f args))
typeCheck (Str _) = return stringType
typeCheck (Ret _) = return Void
typeCheck x = error ("typeCheck: " ++ ppExpr Lax x)


-- Compilation Utils --
-- TODO capture
subst :: Variable -> CExpr -> CExpr -> CExpr
subst var val v = visit fix v
  where
    fix (R v) | v == var = val
    fix v = v

compileMMMul :: CExpr -> (CExpr, CExpr) -> CExpr -> (CExpr, CExpr) -> M CExpr
compileMMMul x (r1, c1) y (r2, c2) = do
  i <- freshName
  inner <- freshName
  j <- freshName
  x' <- flattenTerm x
  y' <- flattenTerm y
  xb <- body x' (R i) (R inner)
  yb <- body y' (R inner) (R j)
  return $
    Lam i r1 $ Lam j c2 $ Free $ Sigma $ 
      Lam inner c1 (xb * yb)
  where
    body vec v1 v2 = return ((vec :! v1) :! v2)

flattenTerm :: CExpr -> M CExpr
flattenTerm e | not (compoundVal e) = return e
flattenTerm e = do
  n <- freshName
  return $ (n := e :> R n)

compileMVMul :: CExpr -> (CExpr, CExpr) -> CExpr -> CExpr -> M CExpr
compileMVMul x (r1, c1) y rows = do
  i <- freshName
  inner <- freshName
  return $
    Lam i rows $ Free $ Sigma $
      Lam inner c1 (((x :! (R i)) :! (R inner)) * (y :! (R inner)))

compileFunctionArgs f args = do
  (cont, fn, rargs) <- foldM step (id, f, []) args
  implicits <- getImplicits f args
  return $ cont (Free $ AppImpl fn implicits (reverse rargs))
  where
    --step :: (CExpr -> CExpr, CExpr, [CExpr]) -> CExpr -> M (...)
    step (cont, fn, args) arg =
      if compoundVal arg
      then do
        n <- freshName
        return (\e -> (n := arg) :> e, fn, (R n) : args)
      else return (cont, fn, arg : args)

compoundVal (R _) = False
compoundVal (Free (IntLit _)) = False
compoundVal (Free (StrLit _)) = False
compoundVal (a :! b) = compoundVal a || compoundVal b
compoundVal (a :+ b) = compoundVal a || compoundVal b
compoundVal (a :* b) = compoundVal a || compoundVal b
compoundVal (a :/ b) = compoundVal a || compoundVal b
compoundVal (a :> b) = compoundVal b
compoundVal _ = True


simpleVal (Free (Unary _ _))  = False
simpleVal (a :! b) = simpleVal a && simpleVal b
simpleVal (a :+ b) = simpleVal a && simpleVal b
simpleVal (a :* b) = simpleVal a && simpleVal b
simpleVal _ = True

-- Term Reduction --
compile :: CExpr -> M CExpr
-- Iterate compileStep to convergence
compile expr = do
  _ <- typeCheck expr
  head <$> scanM step expr
  --if debugFlag
  --then do
  --  scanM step expr
  --else do
  --  _ <- typeCheck expr
  --  expr' <- fixM step expr
  --  return [expr']
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
     in printStep $ compileStep Top expr

-- TODO remove dependence on context?
data Context = Top | LHS | RHS
  deriving (Show)

-- TODO is this confluent? how could we prove it?
compileStep :: Context -> CExpr -> M CExpr

-- Initialization -> Declaration; Assignment
-- var := b  -->  (Decl type var); (a :< b)
compileStep _ e@(var := b) = do
  t <- typeCheck b
  _ <- typeCheck e
  -- TODO remove/add cleaner instrumentation option
  let debugFlag = False
  let notGenVar ('v' : 'a' : 'r' : _) = False
      notGenVar _ = True
  post <- case t of
            ExprType _ | debugFlag && notGenVar var ->
              do 
                let pname = "printf" :$ Str (var ++ "\n")
                p <- generatePrinter var t
                return [pname, p, newline ""]
            _ -> return []

  return $ seqList $
    [ Declare t var
    , (R var) :< b
    ] ++ post

-- Keep type environment "current" while compiling
compileStep _ e@(Declare t var) = do
  extend var t
  return e
compileStep Top e@(Free (Extern var t)) = do
  extend var t
  return e

compileStep Top e@(FnDef var t@(FnT implicits params _) body) = do
  body' <- withBindings (implicits ++ params) $ compileStep Top body
  return $ (FnDef var t body')

compileStep _ e@(Free (Unary "transpose" m)) = do
  ExprType [rows, cols] <- typeCheck m
  i <- freshName
  j <- freshName
  return $ Lam i cols $ Lam j rows $ ((m :! (R j)) :! (R i))

compileStep _ e@(Free (Unary "inverse" m)) = do
  ExprType [dim, _] <- typeCheck m
  inv <- freshName
  return $ seqList [
    Declare (ExprType [dim, dim]) inv,
    Free $ App "inverse" [m, R inv],
    R inv]

-- Arithmetic: +, *, /  --
compileStep ctxt e@(x :+ y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    -- pointwise add
    (ExprType (len1 : _), ExprType (len2 : _)) -> do
      i <- freshName
      return $ Lam i len1 (x :! (R i) + y :! (R i))
    (_, _) | compoundVal x -> do
      a <- freshName
      return $ (a := x) :> (R a :+ y)
    (_, _) | compoundVal y -> do
      b <- freshName
      return $ (b := y) :> (x :+ R b)
    (ExprType [], ExprType []) | Lit a <- x, Lit b <- y -> return $ Lit (a + b)
    (ExprType [], ExprType []) -> do
      x' <- compileStep ctxt x
      y' <- compileStep ctxt y
      return $ x' + y'
    -- TODO this handles adding ptr to int; does it allow anything else?
    _ -> return e

compileStep _ ((a :> b) :* c) = return $ a :> (b :* c)
compileStep _ (c :* (a :> b)) = return $ a :> (c :* b)

compileStep ctxt e@(x :* y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    -- Matrix product
    -- m × n  -->  Vec i (Vec j (∑ (Vec k (m i k * n k j))))
    (ExprType [r1, c1], ExprType [r2, c2]) ->
      compileMMMul x (r1, c1) y (r2, c2)
    -- matrix/vector vector/matrix products
    (ExprType [r1, c1], ExprType [r2]) ->
      compileMVMul x (r1, c1) y r2
    -- TODO
    --(ExprType [c1], ExprType [r2, c2]) ->
    --  compileMMMul x (r1, c1) y (r2, c2)
    -- pointwise multiply
    (ExprType (len1 : _), ExprType (len2 : _)) -> do
      assert (len1 == len2) $ "product length mismatch: " ++ show e
      i <- freshName
      return $ Lam i len1 (x :! (R i) :* y :! (R i))
    (ExprType [], v@(ExprType (len : _))) -> scale x y len
    (v@(ExprType (len : _)), ExprType []) -> scale y x len
    (_, _) | compoundVal x -> do
      a <- freshName
      return $ (a := x) :> (R a :* y)
    (_, _) | compoundVal y -> do
      b <- freshName
      return $ (b := y) :> (x :* R b)
    (ExprType [], ExprType []) | Lit a <- x, Lit b <- y -> return $ Lit (a * b)
    (ExprType [], ExprType []) -> do
      x' <- compileStep ctxt x
      y' <- compileStep ctxt y
      return $ x' * y'
  where
    scale s vec len = do
      i <- freshName
      return $ Lam i len (s :* vec :! (R i))

compileStep ctxt e@(x :/ y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    -- pointwise div
    (ExprType (len : _), ExprType []) -> do
      i <- freshName
      return $ Lam i len ((x :! (R i)) :/ y)
    (ExprType [], ExprType []) | compoundVal x -> do
      a <- freshName
      return $ (a := x) :> (R a :/ y)
    (ExprType [], ExprType []) | compoundVal y -> do
      b <- freshName
      return $ (b := y) :> (x :/ R b)
    (ExprType [], ExprType []) -> do
      x' <- compileStep ctxt x
      y' <- compileStep ctxt y
      return $ x' / y'
    p -> error ("compileStep: " ++ show p ++ "\n" ++ show x ++ "\n" ++ show y)

-- Juxtaposition
-- a :< u # v  -->  (a :< u); (a + size u :< v)
compileStep _ (a :< u :# v) = do
  ExprType (offset : _) <- typeCheck u
  -- TODO (a + offset) will always be wrapped by an index operation?
  return $ (a :< u) :> ((a + offset) :< v)

-- Sequence assignment
-- a :< (u; v)  --> u; (a :< v)
compileStep _ (a :< (u :> v)) = do
  return $
    u :>
    a :< v

-- Summation
-- a :< ∑ (Vec i y_i)  -->  (a :< 0); (Vec i (a :< a + y_i))
compileStep _ (a :< (Sig vec)) = do
  i <- freshName
  ExprType (len : _) <- typeCheck vec
  let body = a :< a + (vec :! (R i))
  return $
    (a :< 0) :>
    (Lam i len $ body)

-- Vector assignment
-- a :< Vec i b_i  -->  Vec (a + i :< b_i)
compileStep ctxt (a :< (Lam var r body)) = do
  let lhs = a :! (R var)
  rhs <- withBindings [(var, numType)] $ compileStep RHS body
  return $ Lam var r (lhs :< rhs)
  --return $ Lam var r (lhs :< body)

-- Lift compound values before (a :< Vector) wraps vector body in a loop
compileStep _ (a :< (b :* c)) | compoundVal b = do
  n <- freshName
  return $ (n := b) :> (a :< R n :* c)
compileStep _ (a :< (b :* c)) | compoundVal c = do
  n <- freshName
  return $ (n := c) :> (a :< b :* R n)

-- Vector assignment, reduction on RHS
compileStep ctxt (a :< b) = do
  bt <- typeCheck b
  case bt of
    -- Avoid repeatedly calling inverse
    -- TODO generalize?
    ExprType (len : _) | simpleVal b -> do
      i <- freshName
      let lhs = (a :! (R i))
      return $ Lam i len (lhs :< b :! (R i))
    _ -> do
      a' <- compileStep LHS a
      b' <- compileStep RHS b
      return $ a' :< b'

compileStep ctxt e@(Neg x) = do
  tx <- typeCheck x
  case tx of
    ExprType [] | compoundVal x -> do
      a <- freshName
      return $ (a := x) :> (Neg (R a))
    ExprType [] -> do
      x' <- compileStep ctxt x
      return $ Neg x'
    ExprType (len : _) -> do
      i <- freshName
      return $ Lam i len (- (x :! (R i)))

-- Reduces function args and lifts compound ones
compileStep _ e@(Free (App f args)) = do
  compileFunctionArgs f args

-- Reduction of an application
compileStep _ ((Lam var b body) :! ind) =
  return $ subst var ind body
compileStep RHS ((a :+ b) :! ind) = return $ (a :! ind) + (b :! ind)
compileStep ctxt@RHS (e@(a :* b) :! ind) = do
  ta <- typeCheck a
  tb <- typeCheck b
  case (ta, tb) of
    (ExprType [len1], ExprType [len2]) -> return $ (a :! ind) * (b :! ind)
    (ExprType [], ExprType []) -> return $ (a :! ind) * (b :! ind)
    _ -> do
      e' <- compileStep ctxt e
      return $ e' :! ind
compileStep ctrxt ((a :> b) :! c) = return $ a :> (b :! c)
compileStep ctxt (a :! b) = do
  a' <- compileStep ctxt a
  b' <- compileStep ctxt b
  return (a' :! b')

-- Single-iteration loop unrolling
compileStep _ e@(Lam var (Lit 1) body) = do
  t <- typeCheck e
  case t of
    Void -> return $ subst var (Lit 0) body
    _ -> return e

-- Reduction within a Vec
-- Vec i x  -->  Vec i x
compileStep ctxt (Lam var r body) = do
  body' <- withBindings [(var, numType)] $ compileStep ctxt body
  return $ Lam var r body'

-- Sequencing
-- a :> b  -->  a :> b
compileStep ctxt (a :> b) = do
  a' <- compileStep ctxt a
  b' <- compileStep ctxt b
  return (a' :> b')

-- id
-- x  -->  x
compileStep _ x = return x

