{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
module Main where

import Data.List

un = undefined
mapTup f g (a, b) = (f a, g b)
mapSnd f (a, b) = (a, f b)

type Name = String

data Expr a = ELit a
            | EVar Name
            | ESum (Expr a) (Expr a)
            | EMul (Expr a) (Expr a)
  deriving (Show, Eq)

instance Num a => Num (Expr a) where
  x + y = ESum x y
  x * y = EMul x y
  fromInteger x = ELit (fromIntegral x)
  abs = un
  signum = un
  negate = un

type Rows = Int
type Cols = Int
type Row  = Int
type Col  = Int
type Index = Int

type Scalar = Double
type S = Scalar
type Element a = ((Row, Col), a)


data Mat a
  = Zero
  | One
  | Scalar a

  | Linear [(Index, Element a)]
  | Dense Rows Cols [Element a]
  | Block [Rows] [Cols] [Element (Mat a)]
  | FnMat (Fn a)

  | Mul (Mat a) (Mat a)
  | Sum (Mat a) (Mat a)
  | Var Rows Cols Name
  deriving (Show, Eq)

data Fn a = Fn (Expr Int) (Expr Int) (Expr a -> Expr a -> Expr a)
instance Show a => Show (Fn a) where
  show (Fn r c _) = "Fn " ++ (show r) ++ " " ++ (show c)

instance Eq (Fn a) where
  _ == _ = False

instance Num a => Num (Mat a) where
  x + y = Sum x y
  x * y = Mul x y
  fromInteger x = Scalar (fromInteger x)
  abs = un
  signum = un
  negate = un
          

toDense :: Int -> Int -> (Row -> Col -> a) -> Mat a
toDense rows cols fn = Dense rows cols elems
 where
  elems = [((i, j), fn i j) | i <- [0..rows-1], j <- [0..cols-1]]

matchBlocks :: [Rows] -> [Cols] -> [Rows] -> [Cols] -> Bool
matchBlocks r1 c1 r2 c2 =
 and (zipWith (==) c1 r2)

colEq c (_, c') = c == c'
rowEq r (r', _) = r == r'

joinWith f g h xs ys = [(h x, h y) | x <- xs, Just y <- [find (\y -> g y == f x) ys]]

--dotElems :: Num a => [Element (Mat a)] -> [Element (Mat a)] -> Mat a
dotElems row col =
  sum $ map (uncurry (*)) $ joinWith (snd . fst) (fst . fst) snd row col

mulDense :: Num a => Mat a -> Mat a -> Mat a
mulDense (Dense rows _ es1) (Dense _ cols es2) =
  let entry i j =
        let ri = filter (rowEq i . fst) es1
            cj = filter (colEq j . fst) es2
        in
          dotElems ri cj
  in
    toDense rows cols entry

mulFn (Fn (ELit r1) (ELit c1) f1)
      (Fn (ELit r2) (ELit c2) f2) =
  if c1 == c2
  then Fn (ELit r1) (ELit c2) (\r c -> sum [f1 r i * f2 i c | i <- [0..c1-1]])
  else error "dims don't match"


fn2dense (Fn (ELit rows) (ELit cols) f1) = toDense rows cols f1

mulBlock b1@(Block r1 c1 bs1) b2@(Block r2 c2 bs2) =
 if matchBlocks r1 c1 r2 c2
 then 
   let Dense _ _ es =
         (mulDense (Dense (length r1) (length c1) bs1)
                   (Dense (length r2) (length c2) bs2))
   in
    Block r1 c2 es

 else  un

mul Zero _ = Zero
mul _ Zero = Zero
mul One x = simpl x
mul x One = simpl x
mul d1@(Dense _ _ _) d2@(Dense _ _ _) = simpl $ mulDense d1 d2
mul b1@(Block _ _ _) b2@(Block _ _ _) = simpl $ mulBlock b1 b2
mul x y = Mul x y

plus Zero x = x
plus x Zero = x
plus x y = Sum (simpl x) (simpl y)

simpl :: Mat Scalar -> Mat Scalar
simpl (Scalar 0) = Zero
simpl (Scalar 1) = One
simpl (Mul x y) = mul x y
simpl (Sum x y) = plus x y
simpl (Block rs cs es) = Block rs cs (map (mapSnd simpl) es)
simpl x = x

simplify x =
  let x' = simpl x in
  if x' == x then x else simplify x'

constDense r c x = toDense r c (\_ _ -> x)
m22 :: Mat Scalar
m22 = constDense 2 2 1
m44 = let Dense _ _ bs = constDense 2 2 m22
      in Block [2,2] [2,2] bs
mb :: Mat Scalar
mb = Block [1,1] [1,1] [((0,0), One)
                       ,((0,1), One)
                       ,((1,0), Zero)
                       ,((1,1), One)
                       ]
mb2 = mulBlock mb mb

data Loc = Index Loc (Expr Int) | Ref Name
data Program = Loop Name (Expr Int) (Expr Int) Program
             | Assign Loc (Expr Scalar)

compile :: Mat a -> Mat a -> Program
compile (FnMat (Fn rows cols fn)) = un
