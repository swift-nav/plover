module Simplify where

import Language.Plover.Simplify

-- Test expressions
data TE = TE :+ TE | TE :* TE | Lit Int | Var String
 deriving (Show, Eq, Ord)
instance Num TE where
  (+) = (:+)
  (*) = (:*)
  fromInteger = Lit . fromIntegral
  abs = undefined
  signum = undefined
  negate = undefined

chkte :: TE -> TE
chkte = (simplify scale . teconvert)
 where
  scale n e | e == fromInteger 1 = Lit n
  scale 1 e = e
  scale i e = Lit i * e

teconvert :: TE -> Expr TE Int
teconvert (a :+ b) = Sum [teconvert a, teconvert b]
teconvert (a :* b) = Mul [teconvert a, teconvert b]
teconvert (Lit 0) = Zero
teconvert (Lit 1) = One
teconvert (Lit x) = Prim x
teconvert v@(Var _) = Atom v

t1 :: TE
t1 = (Var "x" + Var "y") ^ (4 :: Int)

-- TODO: Hook in tests

