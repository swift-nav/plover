module Main3 where

import Data.List
import Control.Monad.State 
import Control.Applicative

un = undefined
mapTup f g (a, b) = (f a, g b)
mapSnd f (a, b) = (a, f b)

instance Show (a -> b) where
 show _ = "[fn]"
instance Eq (a -> b) where
 _ == _ = False

type Name = String

data Expr = EInt Int
          | EDub Double
          | ERef Loc
          | ESum Expr Expr
          | EMul Expr Expr
  deriving (Show, Eq)

instance Num Expr where
  x * y = EMul x y
  x + y = ESum x y
  fromInteger x = EInt (fromInteger x)
  abs = un
  signum = un
  negate = un

type Row  = Expr
type Col  = Expr
type Rows = Expr
type Cols = Expr

data Loc = Index Loc Expr | Ref Name
  deriving (Show, Eq)
-- Used for block matrix compilation
-- each submatrix is compiled using a view into
-- the total matrix
data LocView
  -- Base loc, view fn
  = View Loc (Expr -> Expr -> Loc)

loc2expr :: LocView -> Expr
loc2expr (View l _) = ERef l


type Element a = ((Row, Col), a)

data Mat a
  = Var Rows Cols Name
  | One  -- must occur inside Block
  | Zero -- must occur inside Block
  | Scalar a

  | Sum (Mat a) (Mat a)
  | Mul (Mat a) (Mat a)

  | Block [Int] [Int] (Row -> Col -> Mat a)
  | Sparse Rows Cols [Element a]
  deriving (Show, Eq)

instance Num a => Num (Mat a) where
  x + y = Sum x y
  x * y = Mul x y
  fromInteger x = Scalar (fromInteger x)
  abs = un
  signum = un
  negate = un

mdim :: Mat a -> Maybe (Rows, Cols)
mdim (Block rlist clist _) =
  Just (EInt $ sum rlist, EInt $ sum clist)
mdim (Sparse rs cs _) = Just (rs, cs)
mdim (Var rs cs _) = Just (rs, cs)
mdim (Scalar _) = Just (EInt 1, EInt 1)
mdim _ = Nothing

data Program
  = Call String [Expr]
  | Loop Name Expr Expr Program
  | Assign Loc Expr
  | PBlock [Program]
  deriving (Show, Eq)

type CMonad = State Int
state0 = 0

fresh :: CMonad Int
fresh = do
  n <- get
  put (n+1)
  return n
--freshLoc :: CMonad LocView
--freshLoc = do
--  n <- fresh
--  let ref = (Ref ("l" ++ show n))
--  return $ Unit ref

freshMat :: Rows -> Cols -> CMonad LocView
freshMat rs cs = do
  n <- fresh
  let ref = Ref ("m" ++ show n)
  return $ View ref $ \i j -> Index ref (i * rs + j)


range n = [0..n-1]

compile :: LocView -> Rows -> Cols -> Mat Expr
        -> CMonad Program
compile (View v0 vfn) rs cs (Block rlist clist fn) =
  let 
    width = cs
    view i j =
       View v0 $ \k l ->
         let k' = EInt (sum . take i $ rlist) + k
             l' = EInt (sum . take j $ clist) + l
         in
         vfn k' l'
  in
    PBlock <$> sequence
      [let ei = EInt i
           ej = EInt j
       in compile (view i j)
               (EInt $ rlist !! i)
               (EInt $ clist !! j) 
               (fn ei ej)

               | i <- range (length rlist)
               , j <- range (length clist)
      ]
compile (View _ vfn) 1 1 (Scalar s) =
  return $ Assign (vfn 0 0) s
compile (View _ vfn) rs cs Zero =
  error "zero" -- some loop
compile (View _ vfn) rs cs One  =
  error "one" -- some loop
compile 

compileMul :: Expr -> Expr -> Expr
           -> LocView -> LocView -> LocView
           -> Program
compileMul rows inner cols
           (View _ fn) (View _ m1) (View _ m2) =
  let i = "i"
      j = "j"
      m = "m"
      [i', j', m'] = map (ERef . Ref) [i,j,m]
  in
  Loop i 0 rows $
    Loop j 0 cols $
      Loop m 0 inner $ 
        Assign (fn i' j') (mul i' m' j')
 where
  mul i m j =
    ERef (m1 i m) * ERef (m2 m j)

wrap s = "(" ++ s ++ ")"

ppE :: Expr -> String
ppE (EInt i) = show i
ppE (EDub i) = show i
ppE (ERef loc) =
 case loc of
   Ref name -> name
   Index loc' expr -> ppE (ERef loc') ++ "[" ++ ppE expr ++ "]"
ppE (ESum e1 e2) = wrap (ppE e1 ++ " + " ++ ppE e2) 
ppE (EMul e1 e2) = wrap (ppE e1 ++ " * " ++ ppE e2) 

ppLoc = ppE . ERef

pp' :: Program -> [String]
pp' (PBlock ps) = concatMap pp' ps
pp' (Call fn args) = [fn ++ "(" ++ intercalate "," (map ppE args) ++ ");"]
pp' (Loop name start end body) =
  [ "for(u8 " ++ name ++ "="++ ppE start ++ "; " ++ name ++ "< " ++ ppE end ++ "; " ++ name ++ "++) {\n"]
  ++ pp' body
  ++ ["\n}"]
pp' (Assign loc val) =
  [ppLoc loc ++ " = " ++ ppE val]

pp = putStrLn . unlines . pp'

runc m = 
  let p = flip evalState state0 $ do
        let Just (rs, cs) = mdim m
        l <- freshMat rs cs
        compile l rs cs m
  in pp p

-- Simplification --
mulBlock d1@(Block rlist1 clist1 f1) d2@(Block rlist2 clist2 f2) =
  if clist1 == rlist2
  then Block rlist1 clist2 $ \r c ->
    sum [f1 r (EInt i) * f2 (EInt i) c | i <- range (length clist1)]
  else error $ "mismatch: " ++ show d1 ++ " " ++ show d2


m1 :: Mat Expr
m1 = Block [1,1] [1,1] (\i j -> Scalar $ i * ERef (Ref "x"))
m2 = Block [2,2,2] [2,2,2] (\i j -> m1)
m3 = Var 2 2 "M3"
