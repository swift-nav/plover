-- ISSUES
--  - Flatten vs. No Flatten
--    * just retypecheck?
--  - compute size of imperatively defined thing
--    * require initially tree-like program with single-assignment
--    * step through to get sizes -> context + declarations
--    * iterate compiler transform
--    * return decls + final tree
--      * could allow decls in initial syntax
--
--  - what is a type (size)
--    * dimension list + coarse size
--      * would be enough for matrix multiply, loop definitions, compile
--
--  - do I need type checking
--    - should I annotate terms directly with types?
--      * no? just keep context with (name -> type) (or size?)
--  - choose a monad
--    * context monad? EitherT (State name counter + context)
--  - why do I need explicit lambdas
--    - how to handle names
--      * could just use debruijn?
--      * could use \i -> e as long as (size e) and (type e) don't depend on i?
--
--  - how to insert declarations
--    * OK

{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs, DataKinds, TypeOperators #-}
module Smash.Parse.Types3 where
import Data.Foldable (Foldable)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence)
import Control.Applicative ((<$>))
import Control.Monad
import Control.Monad.Free
import Control.Monad.Trans.Either
import Control.Monad.State
import qualified Data.Map.Strict as M
import Data.String

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
 deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)

type FExpr a = Free Expr a
type CExpr = Free Expr Void

--TODO delete
--data Nat = O | S Nat
-- deriving (Show, Eq, Ord)
--data E m where
--  ELit :: Int -> E O
--  ERef :: Variable -> E m
--  ESum :: E m -> E m -> E m
--  EMul :: E m -> E m -> E m
--  ELam :: E O -> (E O -> E n) -> E (S n)
--
--instance Show (E m) where
--  show (ELit i) = show i
--  show (ERef v) = "&" ++ v
--  show (EMul a b) = show a ++ " * " ++ show b
--
--e0 = ELit 0
--e1 = ELam (ELit 2) (\i -> ELam (ELit 3) (\j -> ESum i j))
--
--size :: E m -> E O
--size (ELam bound body) = EMul bound (size (body e0))
--size (ELit _) = ELit 1
--size (ESum a b) = size a  -- assert = size b
--size x = error (show x)

data Type = ExprType [CExpr] | Void
  deriving (Show, Eq, Ord)
typeAppend :: Type -> Type -> Type
typeAppend (ExprType l1) (ExprType l2) = ExprType (l1 ++ l2)

typeSize :: Type -> CExpr
typeSize (ExprType l) = product l

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

numType :: Type
numType = ExprType []

sep :: (Show a, Show b) => a -> b -> String
sep s1 s2 = show s1 ++ ", " ++ show s2

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
typeCheck x = error (show x)

pp :: CExpr -> IO ()
pp = putStrLn . ppExpr ""

ppExpr :: String -> CExpr -> String
ppExpr pre expr =
  let pe = ppExpr pre in
  case expr of
    a :> b -> unlines [pre ++ pe a, pre ++ pe b]
    a := b -> undefined


main = 
  let (mexpr, _) = runState (runEitherT m) initialState in
  case mexpr of
    Left err -> putStrLn err
    Right expr -> print expr

 where
   p1 :: CExpr
   p1 =
        ("x" := Lam "i" 1 (Lam "j" 2 ("temp" := "i" + "j" :> "temp")))
     :> ("y" := Lam "i" 2 (Lam "j" 3 ("i" + "j")))
     :> ("z" := "x" * "y")
   m :: M CExpr
   m = compile p1


fixpoint :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixpoint f x = do
  x' <- f x
  if x == x' then return x else fixpoint f x'

compile :: CExpr -> M CExpr
compile expr = do
  _ <- typeCheck expr
  fixpoint compileStep expr

size :: CExpr -> M CExpr
size x = typeSize <$> typeCheck x

compileStep :: CExpr -> M CExpr
compileStep (a := (Lam var r body)) = do
  offset <- withBinding var numType $ size body
  lhs <- compileStep (a + R var * offset)
  rhs <- compileStep body
  compileStep $ Lam var r (lhs := rhs)

compileStep (a := u :# v) = do
  fst <- compileStep $ a := u
  offset <- size u
  snd <- compileStep $ (a + offset) := v
  return $ fst :> snd

compileStep (a := Free (Sigma (Lam var r body))) = do
  body' <- compileStep (a := a + body)
  return $
    (a := 0) :>
    (Lam var r $ body')

compileStep (a := (Lam i1 r1 (Lam j1 c1 body1))
               :* (Lam i2 r2 (Lam j2 c2 body2))) = do
  var <- freshName
  return $
    Lam i1 r1 $ Lam j2 c2 $ Free $ Sigma $ 
      Lam (var) c1 ((sub body1 j1 (R var)) * (sub body2 i2 (R var)))

compileStep (a :> b) = do
  a' <- compileStep a
  b' <- compileStep b
  return (a' :> b')

compileStep x = return x

sub :: CExpr -> Variable -> CExpr -> CExpr
-- TODO!!
sub e var val = e

--size :: FExpr a -> FExpr a
--size = undefined


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
pattern a :! b = Free (App a b)
pattern a :> b = Free (Seq a b)

instance IsString (FExpr a) where
  fromString = Free . Ref
instance Num (FExpr a) where
  x * y = Free (Mul x y)
  x + y = Free (Sum x y)
  fromInteger x = Free (IntLit $ fromInteger x)
  --abs = undefined
  --signum = undefined
  negate = Free . Negate
