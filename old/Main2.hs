module Main2 where
import Data.List
import Control.Monad.State 

un = undefined
mapTup f g (a, b) = (f a, g b)
mapSnd f (a, b) = (a, f b)

type Name = String

type Rows  = Int
type Cols  = Int
type Row   = Int
type Col   = Int
type Index = Int

type S = Double
type Element a = ((Row, Col), a)

instance Show (a -> b) where
 show _ = "[fn]"
instance Eq (a -> b) where
 _ == _ = False

data Mat a
  = Var Expr Expr Name
  | One
  | Zero
  | Scalar a

  | Sum (Mat a) (Mat a)
  | Mul (Mat a) (Mat a)

  | Block [Rows] [Cols] (Row -> Col -> Mat a)
  | Sparse Rows Cols [Element a]
  -- | Gen Name Name (Row -> Col -> a)
  deriving (Show, Eq)

instance Num a => Num (Mat a) where
  x + y = Sum x y
  x * y = Mul x y
  fromInteger x = Scalar (fromInteger x)
  abs = un
  signum = un
  negate = un

s = Scalar

range n = [0..n-1]

mulBlock d1@(Block r1 c1 f1) d2@(Block r2 c2 f2) =
  if c1 == c2
  then Block r1 c2 (\r c -> sum [f1 r i * f2 i c | i <- range c1])
  else error $ "mismatch: " ++ show d1 ++ " " ++ show d2

eval (Block rows cols f) = 
  Sparse rows cols [((i, j), f i j) | i <- range rows, j <- range cols]
eval' (Sparse rs cs elems) =
  Sparse rs cs (map (mapSnd eval) elems)

data Expr = EInt Int
          | EDub Double
          | EVar Name
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

data Loc = Index Loc Expr | Ref Name
  deriving (Show, Eq)
loc2expr :: Location -> Expr
loc2expr (Space l _) = ERef l
loc2expr (Unit l)  = ERef l
data Location = Unit Loc
              | Space Loc (Expr -> Expr -> Loc)
data Program = Call String [Expr]
             | Loop Name Expr Expr Program
             | Assign Loc Expr
             | PBlock [Program]
  deriving (Show, Eq)

wrap s = "(" ++ s ++ ")"

ppE :: Expr -> String
ppE (EInt i) = show i
ppE (EDub i) = show i
ppE (EVar n) = n
ppE (ERef loc) =
 case loc of
   Ref name -> name
   Index loc' expr -> ppE (ERef loc') ++ "[" ++ ppE expr ++ "]"
ppE (ESum e1 e2) = wrap (ppE e1 ++ " + " ++ ppE e2) 
ppE (EMul e1 e2) = wrap (ppE e1 ++ " * " ++ ppE e2) 

pp' :: Program -> [String]
pp' (Call fn args) = [fn ++ "(" ++ intercalate "," (map ppE args) ++ ");"]
pp' (Loop name start end body) =
  [ "for(u8 " ++ name ++ "="++ ppE start ++ "; " ++ name ++ "< " ++ ppE end ++ "; " ++ name ++ "++) {\n"]
  ++ pp' body
  ++ ["\n}"]

pp = putStrLn . unlines . pp'

memcpy :: Location -> Name -> Expr -> Program
memcpy l n size = Call "memcpy" [loc2expr l, EVar n, size]

type CMonad = State Int
state0 = 0

fresh :: CMonad Int
fresh = do
  n <- get
  put (n+1)
  return n
freshLoc :: CMonad Location
freshLoc = do
  n <- fresh
  let ref = (Ref ("l" ++ show n))
  return $ Unit ref

freshMat :: CMonad Location
freshMat = do
  n <- fresh
  let ref = Ref ("m" ++ show n)
  return $ Space ref $ \i j -> Index (Index ref i) j

compileMul :: Expr -> Expr -> Expr
           -> Location -> Location -> Location
           -> Program
compileMul rows inner cols (Space _ fn) (Space _ m1) (Space _ m2) =
  let i = "i"
      j = "j"
      m = "m"
      [i', j', m'] = map EVar [i,j,m]
  in
  Loop i 0 rows $
    Loop j 0 cols $
      Loop m 0 inner $ 
        Assign (fn i' j') (mul i' m' j')
 where
  mul i m j =
    ERef (m1 i m) * ERef (m2 m j)

compile :: Show a => Location -> Mat a -> CMonad (Program, Expr, Expr)
compile loc (Var r c name) =
  let size_double = EInt 8
      p = memcpy loc name (r * c * size_double)
  in return (p, r, c)
 where 
compile loc (Mul x y) = do
  xl <- freshMat
  yl <- freshMat
  (x', r1, c1) <- compile xl x
  (y', r2, c2) <- compile yl y
  if c1 /= r2 then error ("dim mismatch: " ++ show x ++ " " ++ show y) else return ()
  let mul = compileMul r1 c1 c2 loc xl yl
      p = PBlock [x', y', mul]
  return $ (p, r1, c2)



runc m = 
  let (p, r, c) = flip evalState state0 $ do
        l <- freshMat
        compile l m
  in pp p


m1 = Block 2 2 (\i j -> s $ i + j)
m2 = Block 2 2 (\i j -> m1)
m3 = Var 2 2 "M3"
