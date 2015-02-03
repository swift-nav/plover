{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module Smash.Simplify
  (simplify, Expr(..))
where
import qualified Data.Map.Strict as M
import Control.Monad (foldM)

-- TODO add rebuild to atom 
data Expr e num
  = Sum [(Expr e num)]
  | Mul [(Expr e num)]
  | Atom e
  | Prim num
  | Zero
  | One
 deriving (Show, Eq, Ord)

data Term e n
  = Term n (M.Map e Int)
  | Z
  deriving (Show, Eq)
term1 :: Num n => Term atom n
term1 = Term 1 M.empty

-- Main simplification function
reduce :: (Ord e, Num num) => Term e num -> Expr e num
       -> [Term e num]
reduce Z _ = return Z
reduce term x = step x
 where
  -- Distribute
  step (Sum as) = concatMap (reduce term) as
  -- Sequence
  step (Mul as) = foldM reduce term as
  -- Increment
  step (Atom e) =
    let Term coefficient map = term in
    return $ Term coefficient (M.insertWith (+) e 1 map)
  -- Numeric simplify
  step (Prim n) =
    let Term coefficient map = term in
    return $ Term (n * coefficient) map
  step Zero = return $ Z
  step One = return $ term

foldTerm :: (Num num) => [Term e num] -> [(num, [(e, Int)])]
foldTerm = map fix
 where
  fix Z = (0, [])
  fix (Term coefficient map) = (coefficient, M.toList map)

rebuildTerm :: Num expr => [(expr, Int)] -> expr
rebuildTerm [] = 1
rebuildTerm (e : es) = foldl (\acc pair -> acc * fix pair) (fix e) es
 where
  fix = uncurry (^)

sum' :: (Num a) => [a] -> a
sum' [] = 0
sum' xs = foldr1 (+) xs

rebuild :: (Num expr, Num num) => (num -> expr -> expr) -> Polynomial expr num -> expr
rebuild scale poly = sum' $ map (\(term, coef) -> scale coef (rebuildTerm term)) (M.toList poly)

type Polynomial expr num = M.Map [(expr, Int)] num
poly0 :: Polynomial expr num
poly0 = M.empty

addTerm :: (Ord expr, Num num)
        => Term expr num -> Polynomial expr num -> Polynomial expr num
addTerm Z p = p
addTerm (Term coefficient map) p =
  M.insertWith (+) (M.toList map) coefficient p

(.>) = flip (.)

simplify :: (Ord expr, Num expr, Num num) => (expr -> Expr expr num) -> (num -> expr -> expr) -> expr -> expr
simplify makeExpr scale = makeExpr .> reduce term1 .> foldr addTerm poly0 .> rebuild scale

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

chkte = simplify teconvert scale 
 where
  scale n e | e == fromIntegral 1 = Lit n
  scale 1 e = e
  scale i e = Lit i * e
teconvert (a :+ b) = Sum [teconvert a, teconvert b]
teconvert (a :* b) = Mul [teconvert a, teconvert b]
teconvert (Lit 0) = Zero
teconvert (Lit 1) = One
teconvert l@(Lit x) = Prim x
teconvert v@(Var s) = Atom v

t1 :: TE
t1 = (Var "x" + Var "y") ^ 4
