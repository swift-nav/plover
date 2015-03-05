-- TODO
--   high:
--   - functions
--     - parameter lists
--     - externs
--   - check all rule interactions
--   - BinOp Expr case
--   - delete old compiler
--
--   medium:
--   - binding: names for context, indices for vectors?
--   - do initial typecheck to check for Void
--   - rewrite compileStep using visit?
--
--   low:
--   - throw error if value re-assigned?
--   - loop hoisting
--   - low level optimization?
--     *       a + -(b)  -->  a - b
--     * float x; x = y  -->  float x = y;
--     * use Functor instance to simplify
--
--  - compile notes
--    * require initially tree-like program with single-assignment
--    * do initial typecheck 
--    * iterate compiler transform
--      * inserts decls
--      * vectorizes assignments
--      * flattens arithmetic when needed
--
--  - what is a type?
--    * currently, a dimension list or Void
--    - will need to add annotations of some kind (for matrix types)
--      * could use property model
--      * may need to add more complex type environment

{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs, DataKinds, TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Smash.Parse.Types3 where

import Data.List (intercalate)
import Data.Monoid hiding (Sum)
import qualified Data.Foldable as F (Foldable, fold)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence, mapM, traverse)
import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Monad.Trans.Either
import Control.Monad.State
import Data.String

import Debug.Trace (trace)

type Variable = String

data Void
deriving instance Show Void
deriving instance Eq Void
deriving instance Ord Void

data Expr a
  = Abs Variable a a
  | Ref Variable
  | App a a
  | Concat a a
  | Sigma a

  -- TODO is including Type ok?
  | Decl Type Variable
  | Init a a
  | Assign a a
  | Seq a a

  | IntLit Int

  -- TODO generalize this? like (BinOp OpType a a), OpType = String?
  | Sum a a
  | Mul a a
  | Div a a
  | Negate a

  -- Only needed for output
  | Deref a
 deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

data Line
  -- All instances of CExpr should be arithmetic only
  = Each Variable CExpr Line
  | Block [Line]
  | Store CExpr CExpr
  | LineDecl Type Variable
  deriving (Show, Eq, Ord)

type CExpr = Free Expr Void

-- Type Utilities --
data Type = ExprType [CExpr] | Void
  deriving (Show, Eq, Ord)

typeAppend :: Type -> Type -> Type
typeAppend (ExprType l1) (ExprType l2) = ExprType (l1 ++ l2)

typeSize :: Type -> CExpr
typeSize (ExprType l) = product l

numType :: Type
numType = ExprType []
-- --

-- Typechecking/Compilation Monad --
type MState = (Int, [(Variable, Type)])
initialState :: MState
initialState = (0, [])
type Error = String
type SM = State MState
type M = EitherT Error SM

varType :: Variable -> M Type
varType var = do
  (_, env) <- get
  case lookup var env of
    -- TODO infer types?
    Nothing -> left $ "undefined var: " ++ var ++ "\n" ++ show env
    --Nothing -> return numType
    Just t -> return t

extend :: Variable -> Type -> M ()
extend var t = modify $ \(c, env) -> (c, (var, t) : env)

assert :: Bool -> Error -> M ()
assert cond msg = if cond then return () else left msg

freshName :: M Variable
freshName = do
  (c, env) <- get
  put (c+1, env)
  return ("var" ++ show c)

withBinding :: Variable -> Type -> M a -> M a
withBinding var t m = do
  (_, env0) <- get
  extend var t
  a <- m
  modify $ \(c, _) -> (c, env0)
  return a
-- --

-- Typecheck --
typeCheck :: CExpr -> M Type
typeCheck ((R var) := b) = do
  t <- typeCheck b
  extend var t
  return Void
typeCheck (a := b) = return Void
typeCheck (a :< b) = return Void
typeCheck (Declare _ _) = return Void
typeCheck (a :> b) = do
  typeCheck a
  typeCheck b
typeCheck e@(a :# b) = do
  ExprType (a0 : as) <- typeCheck a
  ExprType (b0 : bs) <- typeCheck b
  assert (as == bs) $ "expr concat mismatch: " ++ show e ++ " !! " ++ sep as bs
  return $ ExprType ((a0 + b0) : as)
typeCheck e@(a :+ b) = do
  typeA <- typeCheck a
  typeB <- typeCheck b
  case (typeA, typeB) of
    _ | typeA == typeB -> return typeA
    -- TODO check lengths
    (ExprType (_ : _), ExprType []) -> return typeA
    (ExprType [], ExprType (_ : _)) -> return typeB
  --assert (typeA == typeB) $ "sum mismatch: " ++ show e
  --return typeA
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
      assert (a1 == b0) $ "matrix product mismatch: " ++ show e
      return $ ExprType [a0, b1]
    (ExprType [a0], ExprType [b0]) -> do
      assert (a0 == b0) $ "vector product mismatch: " ++ show e
      return $ ExprType [a0]
    _ -> error ("product:\n" ++ sep typeA typeB ++ "\n" ++ sep a b)
typeCheck (Lam var bound body) = do
  -- withBinding discards any inner bindings
  mt <- withBinding var numType (typeCheck body)
  case mt of
    ExprType btype -> 
      return $ ExprType (bound : btype)
    Void -> return Void
typeCheck (R var) = varType var
typeCheck (Free (IntLit _)) = return numType
typeCheck (a :! b) = do
  ExprType [] <- typeCheck b
  ExprType (_ : as) <- typeCheck a
  return $ ExprType as
typeCheck (Free (Sigma body)) = do
  ExprType (_ : as) <- typeCheck body
  return $ ExprType as
typeCheck (Neg x) = typeCheck x
typeCheck x = error ("typeCheck: " ++ ppExpr Lax x)

-- Compilation Utilities --
-- Generic fold
iterMon :: (Monoid m, Functor f) => (f m -> m) -> Free f m -> m
iterMon _ (Pure m) = m
iterMon fn (Free f) = fn $ fmap (iterMon fn) f

-- Generic map
visit :: (Functor f) => (Free f a -> Free f a) -> Free f a -> Free f a
---- iterM passes in an unwrapped expr (:: Expr CExpr),
---- so we fmap subst and then rewrap it with Free
visit f = f . iterM (Free . fmap (visit f))

fromFix :: (Functor f) => Free f Void -> Free f a
fromFix = fmap undefined

-- TODO capture
subst :: Variable -> CExpr -> CExpr -> CExpr
subst var val v = visit fix v
  where
    fix (R v) | v == var = val
    fix v = v

compileMMul :: CExpr -> [CExpr] -> CExpr -> [CExpr] -> M CExpr
compileMMul x [r1, c1] y [r2, c2] = do
  i <- freshName
  inner <- freshName
  j <- freshName
  xb <- body x (R i) (R inner)
  yb <- body y (R inner) (R j)
  return $
    Lam i r1 $ Lam j c2 $ Free $ Sigma $ 
      Lam inner c1 (xb * yb)
  where
    body vec v1 v2 = return ((vec :! v1) :! v2)

-- TODO remove
infix 7 !!!
(!!!) x y = return $ x :! y

-- TODO remove basicVal
basicVal (R _) = True
basicVal (Free (IntLit _)) = True
basicVal (a :! v) = basicVal a
basicVal _ = False

compoundVal (R _) = False
compoundVal (Free (IntLit _)) = False
compoundVal (a :! b) = compoundVal a || compoundVal b
compoundVal (a :+ b) = compoundVal a || compoundVal b
compoundVal (a :* b) = compoundVal a || compoundVal b
compoundVal (a :/ b) = compoundVal a || compoundVal b
compoundVal _ = True

flatOp op x y = do
  a <- freshName
  b <- freshName
  return $ (R a := x :> R b := y :> (R a) `op` (R b))

-- Compile --
-- TODO is this confluent? how could we prove it?
-- it is sensitive to order of rewrite rules:
--   some rules shadow others
compile :: CExpr -> SM CExpr
-- Iterate compileStep to convergence
compile expr = fixM step expr
  where
    sep = "\n------------\n"
    -- TODO doesn't quite work
    debugFlag = False
    printStep = 
      if debugFlag
      then trace (sep ++ ppLine Lax "" (flatten expr) ++ sep)
      else id

    step expr = printStep $ do
      mval <- runEitherT (compileStep expr)
      case mval of
        Left err -> trace ((err ++ "\n" ++ show expr)) $ return expr
        Right expr' -> return expr'


-- Each case has a symbolic explanation
compileStep :: CExpr -> M CExpr

-- Initialization -> Declaration; Assignment
-- var := b  -->  (Decl type var); (a :< b)
compileStep e@((R var) := b) = do
  t <- typeCheck b
  _ <- typeCheck e
  return $
    (Declare t var) :> ((R var) :< b)

-- Keep type environment "current" while compiling
compileStep e@(Declare t var) = do
  extend var t
  return e

-- Juxtaposition
-- a :< u # v  -->  (a :< u); (a + size u :< v)
-- TODO check this interaction with [ ]
compileStep (a :< u :# v) = do
  offset <- typeSize <$> typeCheck u
  --return $ (a :< u) :> ((DR $ a + offset) :< v)
  return $ (a :< u) :> ((a + offset) :< v)

-- Sequence assignment
-- a :< (u; v)  --> u; (a :< v)
compileStep (a :< (u :> v)) = do
  return $
    u :>
    a :< v


-- Arithmetic: +, *, /  --
-- TODO combine these
compileStep e@(x :+ y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    -- pointwise add
    (ExprType (len1 : _), ExprType (len2 : _)) -> do
      assert (len1 == len2) $ "length mismatch: " ++ show e
      i <- freshName
      return $ Lam i len1 (x :! (R i) + y :! (R i))
    -- numberic add
    (ExprType [], ExprType []) | compoundVal x -> do
      a <- freshName
      return $ (R a := x) :> (R a :+ y)
    (ExprType [], ExprType []) | compoundVal y -> do
      b <- freshName
      return $ (R b := y) :> (x :+ R b)
    (ExprType [], ExprType []) -> do
      x' <- compileStep x
      y' <- compileStep y
      return $ x' + y'
    -- TODO this handles adding ptr to int; does it allow anything else?
    --_ -> return e
    _ -> error $ "compileStep. +. " ++ show e
    --(ExprType [], ExprType []) -> return e
compileStep e@(x :* y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    -- Matrix product
    -- m × n  -->  Vec i (Vec j (∑ (Vec k (m i k * n k j))))
    (ExprType [r1, c1], ExprType [r2, c2]) ->
      compileMMul x [r1, c1] y [r2, c2]
    -- pointwise multiply
    (ExprType (len1 : _), ExprType (len2 : _)) -> do
      assert (len1 == len2) $ "length mismatch: " ++ show e
      i <- freshName
      return $ Lam i len1 (x :! (R i) :* y :! (R i))
    (ExprType [], v@(ExprType (len : _))) -> scale x y len
    (v@(ExprType (len : _)), ExprType []) -> scale y x len
    (ExprType [], ExprType []) | compoundVal x -> do
      a <- freshName
      return $ (R a := x) :> (R a :* y)
    (ExprType [], ExprType []) | compoundVal y -> do
      b <- freshName
      return $ (R b := y) :> (x :* R b)
    (ExprType [], ExprType []) -> do
      x' <- compileStep x
      y' <- compileStep y
      return $ x' * y'
  where
    scale s vec len = do
      i <- freshName
      return $ Lam i len (s :* vec :! (R i))

compileStep e@(x :/ y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    -- pointwise div
    (ExprType (len : _), ExprType []) -> do
      i <- freshName
      return $ Lam i len ((x :! (R i)) :/ y)
    (ExprType [], ExprType []) | compoundVal x -> do
      a <- freshName
      return $ (R a := x) :> (R a :/ y)
    (ExprType [], ExprType []) | compoundVal y -> do
      b <- freshName
      return $ (R b := y) :> (x :/ R b)
    (ExprType [], ExprType []) -> do
      x' <- compileStep x
      y' <- compileStep y
      return $ x' / y'
    p -> error ("compileStep: " ++ show p ++ "\n" ++ show x ++ "\n" ++ show y)

-- Summation
-- a :< ∑ (Vec i y_i)  -->  (a :< 0); (Vec i (a :< a + y_i))
compileStep (a :< (Sig vec)) = do
  i <- freshName
  ExprType (len : _) <- typeCheck vec
  let body = a :< a + (vec :! (R i))
  return $
    (a :< 0) :>
    (Lam i len $ body)

-- Vector assignment
-- a :< Vec i b_i  -->  Vec (a + i :< b_i)
compileStep (a :< (Lam var r body)) = do
  lhs <- withBinding var numType $ a !!! R var
  rhs <- withBinding var numType $ compileStep body
  return $ Lam var r (lhs :< rhs)

-- Vector assignment, reduction on RHS
compileStep (a :< b) = do
  bt <- typeCheck b
  case bt of
    ExprType (len : _) -> do
      i <- freshName
      --lhs <- withBinding i numType $ a !!! (R i)
      let lhs = (a :! (R i))
      return $ Lam i len (lhs :< b :! (R i))
    _ -> do
      b' <- compileStep b
      return $ a :< b'

compileStep e@(Neg x) = do
  tx <- typeCheck x
  case tx of
    ExprType [] -> return e
    ExprType (len : _) -> do
      i <- freshName
      return $ Lam i len (- (x :! (R i)))

-- Reduction of an application
compileStep ((Lam var b body) :! ind) =
  return $ subst var ind body
compileStep ((a :+ b) :! ind) = return $ (a :! ind) + (b :! ind)
compileStep (e@(a :* b) :! ind) = do
  ta <- typeCheck a
  tb <- typeCheck b
  case (ta, tb) of
    (ExprType [len1], ExprType [len2]) -> return $ (a :! ind) * (b :! ind)
    (ExprType [], ExprType []) -> return $ (a :! ind) * (b :! ind)
    _ -> do
      e' <- compileStep e
      return $ e' :! ind
compileStep (a :! b) = do
  a' <- compileStep a
  b' <- compileStep b
  return (a' :! b')

-- Reduction within a Vec
-- Vec i x  -->  Vec i x
compileStep (Lam var r body) = do
  body' <- withBinding var numType $ compileStep body
  return $ Lam var r body'

-- Sequencing
-- a :< b  -->  a :< b
compileStep (a :> b) = do
  a' <- compileStep a
  b' <- compileStep b
  return (a' :> b')

-- id
-- x  -->  x
compileStep x = return x


-- Printing output --
flatten :: CExpr -> Line
flatten (Declare t var) = LineDecl t var
flatten (Lam var bound body) = Each var bound (flatten body)
flatten (R a :< val) = Store (R a) val
flatten (n :< val) = Store (n) val
flatten (a :> b) = mergeBlocks (flatten a) (flatten b)
flatten (n := val) = Store n val
flatten x = error $ "flatten: " ++ show x

mergeBlocks :: Line -> Line -> Line
mergeBlocks (Block ls1) (Block ls2) = Block (ls1 ++ ls2)
mergeBlocks (Block ls) x = Block (ls ++ [x])
mergeBlocks x (Block ls) = Block (x : ls)
mergeBlocks x y = Block [x, y]

indent off = "  " ++ off

ppMain :: Line -> String
ppMain line = wrapMain (ppLine Strict "  " line)
  where
    wrapMain body =
      "int main() {\n" ++ body ++ "}\n"

data StrictGen = Strict | Lax
ppLine strict off (Block ls) = concat $ map (ppLine strict off) ls
ppLine strict off (Each var expr body) = 
  let vs = ppVar var in
  off ++ "for (int " ++ vs ++ "; " ++
  vs ++ " < " ++ ppExpr strict expr ++ "; " ++
  vs ++ "++) {\n"
    ++ ppLine strict (indent off) body
  ++ off ++ "}\n"
ppLine strict off (Store x e) =
  off ++ ppExpr strict (x) ++ " = " ++
  ppExpr strict e ++ lineEnd
ppLine strict off (LineDecl t var) = 
  let (pre, post) = ppType strict t in
  off ++ pre ++ " " ++ ppVar var ++ post ++ lineEnd

ppLine Strict _ x = error ("ppLine. incomplete reduction: " ++ show x)
ppLine Lax off x = off ++ show x ++ "\n"

lineEnd = ";\n"

ppVar = id
ppType :: StrictGen -> Type -> (String, String)
ppType _ (Void) = ("void", "")
-- TODO general base type
ppType strict t = printArrayType t
  where
    printVecType (ExprType []) = ("float", "")
    printVecType (ExprType es) = ("float", "[" ++ intercalate " * " (map (ppExpr strict) es) ++ "]")
    printArrayType (ExprType es) = ("float", concatMap printOne es)
    printOne e = "[" ++ ppExpr strict e ++ "]"
wrapp s = "(" ++ s ++ ")"
ppExpr strict e =
  let pe = ppExpr strict in
  case e of
    (a :+ b) -> wrapp $ pe a ++ " + " ++ pe b
    (a :* b) -> wrapp $ pe a ++ " * " ++ pe b
    (a :/ b) -> wrapp $ pe a ++ " / " ++ pe b
    (R v) -> ppVar v
    (Free (IntLit i)) -> show i
    (a :! b) -> pe a ++ "[" ++ pe b ++ "]"
    (DR x) -> "(*(" ++ pe x ++ "))"
    (Free (Negate x)) -> "-(" ++ pe x ++ ")"
    (a :< b) -> error "ppExpr.  :<"
    e -> case strict of
           Strict -> error $ "ppExpr. " ++ show e
           Lax -> show e
-- --

-- Testing --
seqList :: [CExpr] -> CExpr
seqList es = foldr1 (:>) es

runM m = runState (runEitherT m) initialState
runS m = runState m initialState
compileMain :: CExpr -> String
compileMain = ppMain . flatten . fst . runS . compile
main = putStrLn . compileMain
writeMain expr =
  let p = compileMain expr in
  do putStrLn p
     writeFile "p3_out.c" p

-- Syntax
infix  4 :=, :<
infixl 1 :>
infix  6 :+, :*, :#
infix 7 :!
pattern a :< b = Free (Assign a b)
pattern a := b = Free (Init a b)
pattern a :# b = Free (Concat a b)
pattern a :+ b = Free (Sum a b)
pattern a :* b = Free (Mul a b)
pattern a :/ b = Free (Div a b)
pattern Lam a b c = Free (Abs a b c)
pattern R a = Free (Ref a)
pattern DR a = Free (Deref a)
pattern Sig x = Free (Sigma x)
pattern Neg x = Free (Negate x)
pattern Declare t x = Free (Decl t x)
pattern a :! b = Free (App a b)
pattern a :> b = Free (Seq a b)

-- Stuff --
fixM :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixM f x = do
  x' <- f x
  if x == x' then return x else fixM f x'

sep :: (Show a, Show b) => a -> b -> String
sep s1 s2 = show s1 ++ ", " ++ show s2

instance IsString (Free Expr a) where
  fromString = Free . Ref
instance Num (Free Expr a) where
  x * y = Free (Mul x y)
  x + y = Free (Sum x y)
  fromInteger x = Free (IntLit $ fromInteger x)
  abs = undefined
  signum = undefined
  negate = Free . Negate
instance Fractional (Free Expr a) where
  x / y = Free (Div x y)
