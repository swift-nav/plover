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
instance Show (a -> b) where
  show f = "<fn>"
instance Eq (a -> b) where
  a == b = False
instance Ord (a -> b) where
  compare a b = GT -- ???

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
data ELoc 
  = ELName Name
  | ELIndex ELoc E
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
  | ESum E (E -> E)
  deriving (Show, Eq, Ord)
infixl 6 ::+, ::*
data Op
  = Atom ::+ Atom
  | Atom ::* Atom
  deriving (Show, Eq)
infix 4 :=
data RHS
  = ROp Op
  | RAtom Atom
  | RLoc Loc
  deriving (Show, Eq)
data Line
  = Decl Type Name
  | Loc := RHS
  -- | Loc :< Atom
  | Loc :** Name
  | Each Name Atom Atom [Line]
  deriving (Show, Eq)
isLit :: E -> Maybe Int
isLit (ELit (I n)) = Just n
isLit _ = Nothing
    

type LocView = (E -> ELoc)
type ValView = (E -> E)
-- Abstract vector
data Vec = Vec E ValView
  deriving (Show)
-- Abstract vector expression
data VExpr
  = VLit Vec
  | VBlock E (E -> VExpr)
  | VPlus VExpr VExpr
  | VProd VExpr VExpr
  | VDot VExpr VExpr
  | VSum VExpr
  -- | VSum E (E -> VExpr)
  deriving (Show)

--TODO
--data GenExpr
--  = GV VExpr
--  | GE Expr
--  | VDot VExpr VExpr
--  deriving (Show)

vlen :: VExpr -> E
vlen (VLit (Vec at _)) = at
vlen (VBlock len es) = ESum len (\i -> vlen (es i))
  --sum (map vlen es)
vlen (VProd v1 _) = vlen v1
vlen (VPlus v1 _) = vlen v1
vlen (VDot _ _) = 1
vlen (VSum _) = 1
-- Semi-concrete vector
type ViewPair = (LocView, ValView)
data MemVec = MemVec E [(LocView, ValView)]
  deriving Show

-- Simplify VExpr
--dotVec :: Vec -> Vec -> E
--dotVec (Vec len f1) (Vec _ f2) =
--  ESum len (\i -> f1 i :* f2 i)
-- Utils
vBinOp (VProd v1 v2) = Just (VProd, (:*), v1, v2)
vBinOp (VPlus v1 v2) = Just (VPlus, (:+), v1, v2)
vBinOp _ = Nothing
-- Main fn
simplV :: VExpr -> VExpr
simplV (VBlock l1 vs1) =
  VBlock l1 (simplV . vs1)
simplV v | Just (op, op', v1, v2) <- vBinOp v =
  let
    step (VLit v1@(Vec len vf1)) (VLit v2@(Vec _ vf2)) =
      VLit $ Vec len (\i -> vf1 i `op'` vf2 i)
    step (VBlock l1 vs1) (VBlock l2 vs2) =
      simplV $ VBlock l1 $ \b -> (vs1 b `op` vs2 b)
    step v1 v2 = v
    v1' = simplV v1
    v2' = simplV v2
  in step v1' v2'
simplV v0@(VDot v1 v2) = simplV $ VSum $ VProd v1 v2
--  let v1' = simplV v1
--      v2' = simplV v2
--  in step v1' v2'
--  where
--    step (VLit v1@(Vec _ _)) (VLit v2@(Vec _ _)) =
--      VLit $ Vec 1 $ \_ -> dotVec v1 v2
--    step (VBlock l1 vs1) (VBlock l2 vs2) =
--      -- TODO partial static length check
--      --if map vlen vs1 /= map vlen vs2
--      --then error $ "simplV. lens don't match: " ++ show v0 else 
--      VSum $ VLit $ Vec 
--      VBlock 1 $ \_ -> VSum l1 (\i -> VDot (vs1 i) (vs2 i))
--    step v1 v2 = error $ unlines ["simplV. ", show v1, show v2]
simplV (VSum (VLit (Vec len vfn))) =
  VLit $ Vec 1 (\_ -> ESum len vfn)
simplV v = v

-- Concretize VExpr to list of (LocView, Vec)
idView name i = ELIndex (fn name) i
concretize :: Name -> VExpr -> NameMonad [(LocView, Vec)]
concretize name (VLit v) = do
  return [(idView name, v)]
-- TODO general length block vector needs for loop
concretize name v0@(VBlock blocks vfn) = do
  case isLit blocks of
    Just num ->
      let vs = map (vfn . fromIntegral) [0..num-1]
          offsets = scanl (+) 0 (map vlen vs)
          len = last offsets
          offset o pairs =
            map (\(lv, vv) -> (lv . (+ o), vv)) pairs
      in do cvs <- mapM (concretize name) vs
            return $ concat $ zipWith offset offsets cvs
    Nothing -> error $ "concretize. general len block vector unsupported: " ++ show v0
concretize name v | Just (op, op', v1, v2) <- vBinOp v = do
  n1 <- freshName
  n2 <- freshName
  name <- freshName
  cv1 <- concretize n1 v1
  cv2 <- concretize n2 v2
  return $ [(idView name , Vec (vlen v1) $ \i -> (fn n1 :! i `op'` fn n2 :! i))]
--TODO
concretize name (VDot v1 v2) = un
concretize name (VSum v1) = do
  n1 <- freshName
  name <- freshName
  cv1 <- concretize n1 v1
  return $ [(idView name , Vec 1 $ \_ -> ESum (vlen v1) (\i -> fn n1 :! i))]

-- Compile to explicit loops
compileELoc :: ELoc -> NameMonad (Loc, [Line])
compileELoc (ELName n) = return (LName n, [])
compileELoc (ELIndex el ind) = do
  (ind, indLines) <- simplCompile ind
  (l, lLines) <- compileELoc el
  return (LIndex l ind, indLines ++ lLines)
compileCV :: (LocView, Vec) -> NameMonad [Line]
compileCV (loc, Vec len val) = do
  (loopBound, lbLines) <- compile len
  index  <- freshName
  blockLines <- compileEntry loc val (fn index)
  let loop = Each index (I 0) loopBound (blockLines)
  return $ (lbLines ++ [loop])
 where
   compileEntry loc val ind = do
     (lhs, lhsLines) <- compileELoc (loc ind)
     (val, valLines) <- simplCompile (val ind)
     let line = lhs := RAtom val
     return (lhsLines ++ valLines ++ [line])
compileV :: VExpr -> NameMonad (Name, [Line])
compileV vexpr = do
  name <- freshName
  cvs <- concretize name vexpr
  lines <- concat <$> mapM compileCV cvs
  return (name, lines)

{-
toMemVec :: Vec -> MemVec
toMemVec (Vec len vfn) = MemVec len [(id, vfn)]
compileV0 :: VExpr -> MemVec
compileV0 (VLit v) = toMemVec $ v
compileV0 (VBlock len vfn) =
  case isLit len of
    Just num ->
      let 
        vs = map (vfn . fromIntegral) [0..num-1]
        offsets = scanl (+) 0 (map vlen vs)
        len = last offsets
        vs' = map compileV0 vs
        offset o (MemVec _ pairs) =
          map (\(lv, vv) -> ((+ o) . lv, vv))
              pairs
      in
      MemVec len (concat $ zipWith offset offsets vs')
    Nothing ->
      error $ "compileV0. block vector is not constant length"
compileV0 v = error $ "compileV0: " ++ show v

compileEntry lfn vfn name i = do
   (val, valLines) <- simplCompile (vfn i)
   (ind, indLines) <- simplCompile (lfn i)
   let line = bindName val name ind
   return (indLines ++ valLines ++ [line])
 where
  bindName :: Atom -> Name -> Atom -> Line
  bindName val name ind = 
    (LIndex (fn name) ind) := RAtom val

compileVecLoop :: LocView -> ValView -> E -> NameMonad (Name, [Line])
compileVecLoop len loc val = do
  (loopBound, lbLines) <- compile len
  output <- freshName
  index  <- freshName
  blockLines <- compileEntry l1 v1 output (fn index)
  let loop = Each index (I 0) loopBound (blockLines)
  return $ (output, lbLines ++ [loop])
compileMem :: MemVec -> NameMonad (Name, [Line])
compileMem (MemVec len pairs) = do
  pairs <- mapM compileVecLoop 
  case isLit len of
    -- TODO Just n -> 
    _ -> do
      compileVecLoop len l1 v1

compileV :: VExpr -> NameMonad (Name, [Line])
compileV = compileMem . compileV0
-}

--compileMem (MemVec len [(l1, v1)]) = do
--  name <- freshName
--  lines <- concat <$> mapM (compileEntry l1 v1 name) [fromIntegral 0]
--  return (name, lines)
--compileV0 (VBlock _ [v1, v2]) = --TODO
--  let
--    Vec len1 f1 = simplV v1
--    Vec len2 f2 = simplV v2
--    view1 = id
--    view2 = (+ len1)
--  in
--    MSeq [len1, len2]
--         [ MVec len1 view1 f1
--         , MVec len2 view2 f2
--         ]

--compileV :: Vec -> NameMonad (Name, [Line])
--compileV (Vec len f) = do
--  name <- freshName
--  case len of
--    R n -> un -- for loop
--    I num  -> do
--      lines <- concat <$> mapM (compileEntry name) [0..num-1]
--      return (name, lines)
-- where

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
compile (ESum len vfn) =
  case isLit len of
    --Just n ->
    --  error "compile. ESum. should be reduced already"
    _ -> do
      (loopBound, lbLines) <- compile len
      output <- freshName
      index  <- freshName
      (exprName, exprLines) <- compile (vfn (fn index))
      let loop = Each index (I 0) loopBound (exprLines ++ [update])
          update = fn output := ROp (fn output ::+ exprName)
      return (fn output, lbLines ++ [loop])

compile e | Just (e1, e2) <- binOp e = do
  (n1, ls1) <- compile e1
  (n2, ls2) <- compile e2
  (n, lines) <- doOp e n1 n2
  return (fn n, ls1 ++ ls2 ++ lines)
doOp (_ :+ _) n1 n2 = do
  n <- freshName
  return (n, [fn n := ROp (n1 ::+ n2)])
doOp (_ :* _) n1 n2 = do
  n <- freshName
  return (n, [fn n := ROp (n1 ::* n2)])
-- TODO remove?
doOp (_ :! _) n1 n2 = do
  np <- freshName
  n <- freshName
  let ls = [ fn np := ROp (n1 ::+ n2)
           , fn n :** np ]
  return (n, ls)

-- TESTS --
e1, e2, e3 :: E
e1 = fn "x" :+ fn "y"
e2 = e1 :* e1
e3 = e2 :* e2
e4 = (e2 :! e2)
e5 l = ESum l (\i -> i :* i)
v1, v2, v3 :: VExpr
v1 = VLit $ Vec 2 (\_ -> 2)
v2 = VLit $ Vec 2 ((* (fn "x")))
v3 = VProd v1 v2
v3' = VDot v1 v2
v4 = VBlock 2 (\_ -> v1)
v5 = VDot v4 v4

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
chk = pp . (snd <$>) . compile . fullSimpl
chkv = pp . (snd <$>) . compileV . simplV

fullSimpl :: E -> E
fullSimpl (e1 :! e2) = fullSimpl e1 :! fullSimpl e2
fullSimpl (e1 :+ e2) = simpl $ fullSimpl e1 :+ fullSimpl e2
fullSimpl (e1 :* e2) = simpl $ fullSimpl e1 :* fullSimpl e2
fullSimpl s@(ESum len f) =
  case isLit len of 
    Just n ->
      fullSimpl $ sum (map (f . fromIntegral) [0..n-1])
    Nothing -> s
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
   isAtom e@(ESum _ _) = Just e
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
instance Named ELoc where
  fn = ELName
instance Named Loc where
  fn = LName
instance Named Atom where
  fn = R
instance Named E where
  fn = ELit . fn
