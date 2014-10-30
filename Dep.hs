{-# LANGUAGE OverloadedStrings, PatternSynonyms #-}
--UndecidableInstances, FlexibleInstances #-}

module Dep where
import Names
import Simplify

import qualified Data.Map.Strict as M
import Data.List
import Control.Applicative
import Data.String
import Text.PrettyPrint -- TODO remove?
un = undefined

-- Goal: reduce expression tree to linear sequence
-- 1: do for atoms
-- 2: vectors?
-- 3: matrices
-- TODO make matrix type
-- figure out isSum
--   - does it simplify matrix products?
-- should simplify handle rebuilding the term?
--

data Type
  = TInt
  deriving (Show, Eq)
data Atom
  = R Name
  | I Int
  deriving (Show, Eq, Ord)
data Loc
  = LName Name
  | LIndex Loc Atom
  deriving (Show, Eq, Ord)
infixl 6 :+, :*
data E
  = ELit Atom
  | E :+ E
  | E :* E
  | E :! E
  deriving (Show, Eq, Ord)
infixl 6 ::+, ::*
data Op
  = Atom ::+ Atom
  | Atom ::* Atom
  deriving (Show, Eq)
infix 4 :=
data Line
  = Decl Type Name
  | Loc := Op
  | Loc :< Atom
  | Loc :** Name
  deriving (Show, Eq)

data Vec
  = Vec Atom (Atom -> E)
  | VProd Atom Vec Vec
  | VScale E Vec
compileV :: Vec -> NameMonad (Name, [Line])
compileV (Vec len f) = do
  name <- freshName
  case len of
    R n -> un
    I num  -> do
      lines <- concat <$> mapM (compileEntry name) [0..num-1]
      return (name, lines)
 where
   compileEntry name i = do
      (at, lines) <- simplCompile (f (I i))
      let line = bindName at name i
      return (lines ++ [line])
   bindName :: Atom -> Name -> Int -> Line
   bindName atom name i = 
     (LIndex (fn name) (I i)) :< atom
compileV (VProd len (Vec _ f1) (Vec _ f2)) =
  let v' = Vec len (\i -> f1 i :* f2 i)
  in
    compileV v'
--compileV (VProd len v1 v2) = do
--  (n1, ls1) <- compileV v1
--  (n2, ls2) <- compileV v2
--  (n, ls') <- compileV (Vec len (\i -> (fn n1 :! ELit i) :* (fn n2 :! ELit i)))
--  return (n, ls1 ++ ls2 ++ ls')

simpl = toE . simplify eExpr
simplCompile :: E -> NameMonad (Atom, [Line])
simplCompile = compile . simpl
binOp :: E -> Maybe (E, E)
binOp (e1 :+ e2) = Just (e1, e2)
binOp (e1 :* e2) = Just (e1, e2)
binOp (e1 :! e2) = Just (e1, e2)
binOp _ = Nothing
compile :: E -> NameMonad (Atom, [Line])
compile (ELit b@(I n)) = return (b, [])
compile (ELit b@(R n)) = return (b, [])
compile e | Just (e1, e2) <- binOp e = do
  (n1, ls1) <- compile e1
  (n2, ls2) <- compile e2
  (n, lines) <- doOp e n1 n2
  return (fn n, ls1 ++ ls2 ++ lines)
doOp (_ :+ _) n1 n2 = do
  n <- freshName
  return (n, [fn n := n1 ::+ n2])
doOp (_ :* _) n1 n2 = do
  n <- freshName
  return (n, [fn n := n1 ::* n2])
doOp (_ :! _) n1 n2 = do
  np <- freshName
  n <- freshName
  let ls = [ fn np := n1 ::+ n2
           , fn n :** np ]
  return (n, ls)
--compile (e1 :+ e2) = do
--  (n1, ls1) <- compile e1
--  (n2, ls2) <- compile e2
--  n <- freshName
--  return $ (fn n, ls1 ++ ls2 ++ [fn n := n1 ::+ n2])
--compile (e1 :* e2) = do
--  (n1, ls1) <- compile e1
--  (n2, ls2) <- compile e2
--  n <- freshName
--  return $ (fn n, ls1 ++ ls2 ++ [fn n := n1 ::* n2])

-- TESTS --
e1, e2, e3 :: E
e1 = fn "x" :+ fn "y"
e2 = e1 :* e1
e3 = e2 :* e2
e4 = (e2 :! e2)
v1, v2, v3 :: Vec
v1 = Vec (I 2) (\_ -> 1)
v2 = Vec (I 2) ((* (fn "x")) . ELit)
v3 = VProd (I 2) v1 v2

toE :: Poly E Int -> E
toE poly =
  let toProd (ts, coef) =
        let n' = ELit (I coef) in
        case ts of
          [] -> n'
          _  -> 
            foldl1 (:*) $
              (if coef == 1
              then []
              else [n'])
                ++ (concatMap (\(n, exp) -> replicate exp (id n)) ts)
  in
  case map toProd $ M.toList poly of
    []  -> 0
    ps  -> foldr1 (:+) ps
pp = mapM_ print . runName
chk = pp . (snd <$>) . compile . simpl
chkv = pp . (snd <$>) . compileV


fullSimpl :: E -> E
fullSimpl (e1 :! e2) = fullSimpl e1 :! fullSimpl e2
fullSimpl (e1 :+ e2) = simpl $ fullSimpl e1 :+ fullSimpl e2
fullSimpl (e1 :* e2) = simpl $ fullSimpl e1 :* fullSimpl e2
fullSimpl e = simpl e

-- STUFF --
eExpr :: Expr E E Int
eExpr = Expr
  { isSum = isSum
  , isMul = isMul
  , isAtom = isAtom
  , isPrim = isPrim
  , zero = 0
  , one = 1
  }
  where
   isSum (e1 :+ e2) = Just [e1, e2]
   isSum _ = Nothing
   isMul (e1 :* e2) = Just [e1, e2]
   isMul _ = Nothing
   isAtom e@(ELit (R n)) = Just e
   isAtom e@(_ :! _) = Just e
   isAtom _ = Nothing
   isPrim (ELit (I n)) = Just n
   isPrim _ = Nothing

   isNode (e1 :! e2) =
     Just ([e1, e2], \[e1, e2] -> e1 :! e2)

instance Num E where
  x * y = x :* y
  x + y = x :+ y
  fromInteger x = ELit . I $ (fromInteger x)
  abs = un
  signum = un
  negate = un
class Named a where
  fn :: Name -> a
instance Named Loc where
  fn = LName
instance Named Atom where
  fn = R
instance Named E where
  fn = ELit . fn
