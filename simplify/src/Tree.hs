{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Tree
  (Expr, nameTreeM, nameTree)
where
import Data.Foldable
import Data.Traversable hiding (mapM, sequence)
import qualified Data.Traversable as T (mapM, sequence)
import Control.Monad.Free
import Data.String
import Name

type Expr f = Free f Name

-- Populates Env with a Name for each node
nameTreeM :: Traversable f => Free f Name -> EnvMonad (f Name) Name
nameTreeM = iterM (\f -> T.sequence f >>= store)
nameTree :: Traversable e => Expr e -> Env (e Name)
nameTree = snd . runEnv . nameTreeM

-- Named attaches a label to some other functor
data Labeled label f x = Node label (f x)
 deriving (Eq, Show)
type Named = Labeled Name
type NamedTree f = Free (Named f) Name
label (Free (Node l _)) = l

-- Returns tree labeled with Names
-- The Env it creates is the same as nameTreeM
labelTreeM :: Traversable f => Free f (NamedTree f) -> EnvMonad (f Name) (NamedTree f)
labelTreeM =
  let
    step :: Traversable f => f (EnvMonad (f Name) (NamedTree f)) -> (EnvMonad (f Name) (NamedTree f))
    step f = do
      -- layer :: f (NamedTree f)
      layer <- T.sequence f
      let nameLayer = fmap label layer
      name <- store nameLayer
      return $ Free (Node name layer)
  in
    iterM step

-- Examples
data TestE a = Sum a a | Mul a a | L Int | Var String
 deriving (Eq, Show, Functor, Foldable, Traversable)

type TestExpr a = Free TestE a

instance Num (TestExpr a) where
  a + b = Free (Sum a b)
  a * b = Free (Mul a b)
  fromInteger = Free . L . fromIntegral
  abs = undefined
  signum = undefined
  negate = undefined
instance IsString (TestExpr a) where
  fromString = Free . Var

t1, t2, t3 :: TestExpr a
t1 = 0 * 1
t2 = (1 + 2) * (3 + 4)
t3 = ("x" + "y") ^ 3

test :: (NamedTree TestE, Env (TestE Name))
test = runEnv $ do
  t4 <- labelTreeM t3
  t5 <- labelTreeM $ Pure t4 * Pure t4
  return t5
