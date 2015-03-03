-- TODO
--   - flatten arithmetic
--     * check for multiline operations, only flatten them
--   - gcc it
--   - check :# arithmetic
--   - functions
--     - parameter lists
--     - externs
--   - clean up vec body operation?
--   - throw error if value re-assigned?
--   - loop hoisting
--   - binding: names for context, indices for vectors?
--   - low level optimization?
--     *       a + -(b)  -->  a - b
--     * float x; x = y  -->  float x = y;
--     * use Functor instance to simplify
--
-- ISSUES
--  - compute size of imperatively defined thing
--    * require initially tree-like program with single-assignment
--    * step through to get sizes -> context + declarations
--    * iterate compiler transform
--    * return decls + final tree
--      * could allow decls in initial syntax
--
--  - what is a type (size)
--    * dimension list
--    - will need to add annotations of some kind (for matrix types)
--      * could use property model
--      * may need to add more complex type environment
--

{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs, DataKinds, TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Smash.Parse.Types3 where

import Data.Foldable (Foldable)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence, mapM, traverse)
import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Monad.Trans.Either
import Control.Monad.State
import Data.String

import Debug.Trace (trace)

type Tag = String
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
 deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)

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
type M = EitherT Error (State MState)

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

-- Typecheck, Compile --
typeCheck :: CExpr -> M Type
--typeCheck e@(a :< b) =
--  error $ "typeCheck. found update-assignment: " ++ show e ++
--          "\nuse := to declare instead"
typeCheck ((R var) := b) = do -- trace ("LOOK: " ++ show var) $ do
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
  assert (typeA == typeB) $ "sum mismatch: " ++ show e
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
    (ExprType [a0], ExprType [b0]) -> do
      assert (a0 == b0) $ "vector product mismatch: " ++ show e
      return $ ExprType [a0]
    (ExprType [a0, a1], ExprType [b0, b1]) -> do
      assert (a1 == b0) $ "matrix product mismatch: " ++ show e
      return $ ExprType [a0, b1]
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
typeCheck x = error ("typeCheck: " ++ ppExpr x)

size :: CExpr -> M CExpr
size x = typeSize <$> typeCheck x

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
    body vec v1 v2 = do
      vec' <- (vecBody vec v1)
      vec'' <- (vecBody vec' v2)
      return vec''

-- TODO cleanup remove case check
vecBody :: CExpr -> CExpr -> M CExpr
vecBody (Lam i r body) index = return $ subst i index body
vecBody (R v) index = return $ (R v) :! index
vecBody v@(_ :! _) index = return $ v :! index
vecBody v index = do
  v' <- compile v
  case v' of
    Lam _ _ _ -> vecBody v' index
    R _ -> vecBody v' index
    _ :! _ -> vecBody v' index
    _ -> error $ "vecBody: " ++ show v'

-- TODO HARD is this confluent? how could we prove it?
compile :: CExpr -> M CExpr
compile expr = do
  -- Populate type environment
  _ <- typeCheck expr
  -- Iterate compileStep to convergence
  fixM compileStep expr


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

-- Vector assignment
-- a :< Vec i b_i  -->  Vec (a + i :< b_i)
compileStep (a :< (Lam var r body)) = do
  --offset <- withBinding var numType $ size body
  --lhs <- compileStep (a + R var * offset)
  lhs <- withBinding var numType $ compileStep (a :! (R var))
  rhs <- withBinding var numType $ compileStep body
  return $ Lam var r (lhs :< rhs)

-- Arithmetic: +, *, /  --
compileStep e@(x :+ y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    -- pointwise add
    (ExprType (len1 : _), ExprType (len2 : _)) -> do
      assert (len1 == len2) $ "length mismatch: " ++ show e
      i <- freshName
      xb <- vecBody x (R i)
      yb <- vecBody y (R i)
      return $ Lam i len1 (xb + yb)
    -- numberic add
    (ExprType [], ExprType []) -> return e
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
      xb <- vecBody x (R i)
      yb <- vecBody y (R i)
      return $ Lam i len1 (xb * yb)
    _ -> return e
compileStep e@(x :/ y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    -- pointwise div
    (ExprType (len : _), ExprType []) -> do
      i <- freshName
      xb <- vecBody x (R i)
      return $ Lam i len (xb / y)
    (ExprType [], ExprType []) -> return e
    p -> error ("compileStep: " ++ show p ++ "\n" ++ show x ++ "\n" ++ show y)

compileStep e@(Neg x) = do
  tx <- typeCheck x
  case tx of
    ExprType [] -> return e
    ExprType (len : _) -> do
      i <- freshName
      xb <- vecBody x (R i)
      return $ Lam i len (- xb)

-- Juxtaposition
-- a :< u # v  -->  (a :< u); (a + size u :< v)
compileStep (a :< u :# v) = do
  fst <- compileStep $ a :< u
  offset <- size u
  -- TODO FIX check this
  snd <- compileStep $ (DR $ a + offset) :< v
  return $ fst :> snd

-- Summation
-- a :< ∑ (Vec i y_i)  -->  (a :< 0); (Vec i (a :< a + y_i))
compileStep (a :< Free (Sigma vec)) = do
  i <- freshName
  ExprType (len : _) <- typeCheck vec
  vb <- vecBody vec (R i)
  let body = (a :< a + vb)
  return $
    (a :< 0) :>
    (Lam i len $ body)

-- Sequence assignment
-- a :< (u; v)  --> u; (a :< v)
compileStep (a :< (u :> v)) = do
  return $
    u :>
    a :< v

-- Reduction on the right
-- a :< x  -->  a :< x
compileStep (a :< x) = do
  x' <- compileStep x
  return $ a :< x'

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

-- TODO capture
subst :: Variable -> CExpr -> CExpr -> CExpr
subst var val (R v) | v == var = val
-- iterM passes in an unwrapped expr (:: Expr CExpr),
-- so we fmap subst and then rewrap it with Free
subst var val expr = iterM (Free . fmap (subst var val)) expr

fromFix :: Functor f => Free f Void -> Free f a
fromFix = fmap (const undefined)

-- Printing output --
flatten :: CExpr -> Line
flatten (Declare t var) = LineDecl t var
flatten (Lam var bound body) = Each var bound (flatten body)
flatten (n :< val) = Store n val
flatten (a :> b) = mergeBlocks (flatten a) (flatten b)
flatten x = error $ "flatten: " ++ show x

mergeBlocks :: Line -> Line -> Line
mergeBlocks (Block ls1) (Block ls2) = Block (ls1 ++ ls2)
mergeBlocks (Block ls) x = Block (ls ++ [x])
mergeBlocks x (Block ls) = Block (x : ls)
mergeBlocks x y = Block [x, y]

indent off = "  " ++ off

ppLine off (Block ls) = concat $ map (ppLine off) ls
ppLine off (Each var expr body) = 
  let vs = ppVar var in
  off ++ "for (int " ++ vs ++ "; " ++
  vs ++ " < " ++ ppExpr expr ++ "; " ++
  vs ++ "++) {\n"
    ++ ppLine (indent off) body
  ++ off ++ "}\n"
ppLine off (Store x e) = off ++ ppExpr (x) ++ " = " ++ ppExpr e ++ lineEnd
ppLine off (LineDecl t var) = 
  let (pre, post) = ppType t in
  off ++ pre ++ " " ++ ppVar var ++ post ++ lineEnd
ppLine off x = off ++ show x ++ "\n"

lineEnd = ";\n"

ppVar = id
ppType (Void) = ("void", "")
-- TODO general base type
ppType (ExprType es) = ("float", concatMap printOne es)
  where
    printOne e = "[" ++ ppExpr e ++ "]"
wrapp s = "(" ++ s ++ ")"
ppExpr (a :+ b) = wrapp $ ppExpr a ++ " + " ++ ppExpr b
ppExpr (a :* b) = wrapp $ ppExpr a ++ " * " ++ ppExpr b
ppExpr (a :/ b) = wrapp $ ppExpr a ++ " / " ++ ppExpr b
ppExpr (R v) = ppVar v
ppExpr (Free (IntLit i)) = show i
ppExpr (a :! b) = ppExpr a ++ "[" ++ ppExpr b ++ "]"
ppExpr (DR x) = "*(" ++ ppExpr x ++ ")"
ppExpr (Free (Negate x)) = "-(" ++ ppExpr x ++ ")"
--ppExpr (a :< b) = ppLine "" (Store a b)
ppExpr (a :< b) = error "ppExpr.  :<"
ppExpr e = show e
-- --


-- Testing --
seqList :: [CExpr] -> CExpr
seqList es = foldr1 (:>) es

runM m = runState (runEitherT m) initialState
main p1 = 
  let (mexpr, _) = runM m in
  case mexpr of
    Left err -> putStrLn err
    Right expr -> putStrLn . ppLine "" $ (flatten expr)

 where
   m = compile p1
-- --

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
  --abs = undefined
  --signum = undefined
  negate = Free . Negate
instance Fractional (Free Expr a) where
  x / y = Free (Div x y)
