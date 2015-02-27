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
import Control.Monad
import Control.Monad.Free
import Control.Monad.Trans.Either
import Control.Monad.State
import qualified Data.Map.Strict as M
import Data.String
import Debug.Trace (trace)

import qualified Language.C.Syntax as C

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

  | Assign a a
  | Seq a a

  -- | Number a
  | IntLit Int
  | Sum a a
  | Mul a a
  | Negate a

  -- Only needed for output
  | Deref a
 deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)

data Line
  -- All instances of CExpr should be arithmetic only
  = Each Variable CExpr Line
  | Block [Line]
  | Store CExpr CExpr
  | Decl Type Variable
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
    Nothing -> left $ "undefined var: " ++ var
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
typeCheck ((R var) := b) = do
  t <- typeCheck b
  extend var t
  return Void
typeCheck (a :> b) = do
  typeCheck a
  typeCheck b
typeCheck e@(a :# b) = do
  ExprType (a0 : as) <- typeCheck a
  ExprType (b0 : bs) <- typeCheck b
  assert (as == bs) $ "expr concat mismatch: " ++ show e
  return $ ExprType ((a0 + b0) : as)
typeCheck e@(a :+ b) = do
  typeA <- typeCheck a
  typeB <- typeCheck b
  assert (typeA == typeB) $ "sum mismatch: " ++ show e
  return typeA
typeCheck e@(a :* b) = do
  typeA <- typeCheck a
  typeB <- typeCheck b
  case (typeA, typeB) of
    (ExprType [], ExprType []) -> return typeA
    (ExprType [a0, a1], ExprType [b0, b1]) -> do
      assert (a1 == b0) $ "matrix product mismatch: " ++ show e
      return $ ExprType [a0, b1]
    _ -> error ("product:\n" ++ sep typeA typeB ++ "\n" ++ sep a b)
typeCheck (Lam var bound body) = do
  ExprType btype <- withBinding var numType (typeCheck body)
  return $ ExprType (bound : btype)
typeCheck (R var) = varType var
typeCheck (Free (IntLit _)) = return numType
typeCheck (a :! b) = do
  ExprType [] <- typeCheck b
  ExprType (_ : as) <- typeCheck a
  return $ ExprType as
typeCheck (Free (Sigma body)) = typeCheck body
typeCheck x = error ("typeCheck: " ++ show x)

size :: CExpr -> M CExpr
size x = typeSize <$> typeCheck x

compileMMul :: CExpr -> [CExpr] -> CExpr -> [CExpr] -> M CExpr

compileMMul x [r1, c1] y [r2, c2] = do
  i <- freshName
  inner <- freshName
  j <- freshName
  return $
    Lam i r1 $ Lam j c2 $ Free $ Sigma $ 
      Lam inner c1 (body x (R i) (R inner) * body y (R inner) (R j))
 where
   body (Lam i r (Lam j c body)) v1 v2 = 
     subst j v2 (subst i v1 body)
   body (R x) v1 v2 = ((R x) :! v1) :! v2

compile :: CExpr -> M CExpr
compile expr = do
  _ <- typeCheck expr
  fixM compileStep expr

compileStep :: CExpr -> M CExpr
compileStep (a := (Lam var r body)) = do
  offset <- withBinding var numType $ size body
  lhs <- compileStep (a + R var * offset)
  rhs <- compileStep body
  return $ Lam var r (lhs := rhs)

compileStep (a := u :# v) = do
  fst <- compileStep $ a := u
  offset <- size u
  snd <- compileStep $ (a + offset) := v
  return $ fst :> snd

compileStep (a := Free (Sigma (Lam var r body))) = do
  body' <- compileStep (a := (DR a) + body)
  return $
    (a := 0) :>
    (Lam var r $ body')

compileStep e@(x :* y) = do
  tx <- typeCheck x
  ty <- typeCheck y
  case (tx, ty) of
    (ExprType [r1, c1], ExprType [r2, c2]) ->
      compileMMul x [r1, c1] y [r2, c2]
    _ -> return e

--compileStep (a := (Lam i1 r1 (Lam j1 c1 body1))
--               :* (Lam i2 r2 (Lam j2 c2 body2))) = do

compileStep (a := (u :> v)) = do
  return $
    u :>
    a := v
compileStep (a := x) = do
  x' <- compileStep x
  return $ a := x'

compileStep (Lam var r body) = do
  body' <- withBinding var numType $ compileStep body
  return $ Lam var r body'

compileStep (a :> b) = do
  a' <- compileStep a
  b' <- compileStep b
  return (a' :> b')

compileStep x = return x

subst :: Variable -> CExpr -> CExpr -> CExpr
subst var val (R v) | v == var = val
-- iterM passes in an unwrapped expr (:: Expr CExpr),
-- so we fmap subst and then rewrap it with Free
subst var val expr = iterM (Free . fmap (subst var val)) expr


fromFix :: Functor f => Free f Void -> Free f a
fromFix = fmap (const undefined)

-- Printing output --
flatten :: CExpr -> Line
flatten (Lam var bound body) = Each var bound (flatten body)
flatten (n := val) = Store n val
flatten (a :> b) = mergeBlocks (flatten a) (flatten b)
flatten x = error $ "flatten: " ++ show x
mergeBlocks (Block ls1) (Block ls2) = Block (ls1 ++ ls2)
mergeBlocks (Block ls) x = Block (ls ++ [x])
mergeBlocks x (Block ls) = Block (x : ls)
mergeBlocks x y = Block [x, y]
mergeBlocks x y = error $ "mergeBlocks: " ++ sep x y

indent off = "  " ++ off

ppLine off (Block ls) = concat $ map (ppLine off) ls
ppLine off (Each var expr body) = 
  off ++ "for (" ++ ppVar var ++ "; " ++ ppExpr expr ++ ") {\n"
  ++ ppLine (indent off) body
  ++ off ++ "}\n"
ppLine off (Store x e) = off ++ ppExpr (Free $ Deref x) ++ " = " ++ ppExpr e ++ ";\n"
ppLine off x = off ++ show x ++ "\n"

ppVar = id
ppExpr (a :+ b) = ppExpr a ++ " + " ++ ppExpr b
ppExpr (a :* b) = ppExpr a ++ " * " ++ ppExpr b
ppExpr (R v) = ppVar v
ppExpr (Free (IntLit i)) = show i
ppExpr (a :! b) = ppExpr a ++ "[" ++ ppExpr b ++ "]"
ppExpr (DR x) = "*(" ++ ppExpr x ++ ")"
ppExpr e = show e

-- --

-- Testing --

main = 
  let (mexpr, _) = runState (runEitherT m) initialState in
  case mexpr of
    Left err -> putStrLn err
    Right expr -> putStrLn . ppLine "" $ (flatten expr)

 where
   p1 :: CExpr
   p1 =
        ("x" := Lam "i" 1 (Lam "j" 2 ("temp" := "i" + "j" :> "temp")))
     :> ("y" := Lam "i" 2 (Lam "j" 3 ("i" + "j")))
     :> ("z" := "x" * "y")
   m :: M CExpr
   m = compile p1

st0 = subst "x" (R "y") (R "x")
st1 = subst "x" (R "y") (R "x" + R "z")

-- --

-- Syntax
infix  4 :=
infixl 1 :>
infix  6 :+, :*, :#, :!
pattern a := b = Free (Assign a b)
pattern a :# b = Free (Concat a b)
pattern a :+ b = Free (Sum a b)
pattern a :* b = Free (Mul a b)
pattern Lam a b c = Free (Abs a b c)
pattern R a = Free (Ref a)
pattern DR a = Free (Deref a)
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
-- --
