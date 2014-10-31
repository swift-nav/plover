{-# LANGUAGE OverloadedStrings, PatternSynonyms #-}
module Vec where
import Prelude hiding ((**))
import Names
import qualified Simplify
import qualified Data.Map.Strict as M
import Data.List
import Control.Applicative
import Data.String

-- Goal: algebraically simplify expression tree and reduce to linear sequence
-- 1: do for atoms - works
-- 2: vectors - works
-- 3: matrices
-- TODO make matrix type
-- should Simplify handle rebuilding the term?

-- Expressions
infixl 6 :+, :*
data E
  = ELit Atom
  | E :+ E
  | E :* E
  | E :! E
  | ESum E (E -> E)
  deriving (Show, Eq, Ord)
pattern LitNum n = ELit (I n)
isLit :: E -> Maybe Int
isLit (LitNum n) = Just n
isLit _ = Nothing

-- Vectors
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

-- Programs
-- Immediate Value
data Atom
  = R Name
  | I Int
  deriving (Show, Eq, Ord)
-- General location
data ELoc 
  = ELName Name
  | ELIndex ELoc E
  deriving (Show, Eq, Ord)
-- Immediate location
data Loc
  = LName Name
  | LIndex Loc Atom
  deriving (Show, Eq, Ord)
infixl 6 ::+, ::*
-- Immediate operation
data Op
  = Atom ::+ Atom
  | Atom ::* Atom
  deriving (Show, Eq)
data RHS
  = ROp Op
  | RAtom Atom
  | RLoc Loc
  | RDeref Name
  deriving (Show, Eq)
infix 4 :=
-- Syntax
data Line
  = Loc := RHS
  | Each Name Atom Atom [Line]
  | Decl Loc
  deriving (Show, Eq)

-- Expression Simplification/Compilation --
-- Simplification --
toE :: Simplify.Poly E Int -> E
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
simpl = toE . Simplify.simplify eExpr
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
-- END / Simplification --
-- Expression Compilation --
simplCompile :: E -> NameMonad (Atom, [Line])
simplCompile = compile . fullSimpl
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
           , fn n := RDeref np ]
  return (n, ls)
-- END / Expression Compilation --
-- END / Expression Simplification/Compilation --

-- Vector Simplification/Compilation --
-- Simplification --
vlen :: VExpr -> E
vlen (VLit (Vec at _)) = at
vlen (VBlock len es) = ESum len (\i -> vlen (es i))
vlen (VProd v1 _) = vlen v1
vlen (VPlus v1 _) = vlen v1
vlen (VDot _ _) = 1
vlen (VSum _) = 1
vBinOp (VProd v1 v2) = Just (VProd, (:*), v1, v2)
vBinOp (VPlus v1 v2) = Just (VPlus, (:+), v1, v2)
vBinOp _ = Nothing
injectExpr :: Either E VExpr -> VExpr
injectExpr (Right v) = v
injectExpr (Left e) = VLit $ Vec 1 (\_ -> e)
simplV :: VExpr -> Either E VExpr
simplV (VBlock l1 vs1) =
  Right $ VBlock l1 (injectExpr . simplV . vs1)
simplV v | Just (op, op', v1, v2) <- vBinOp v =
  let
    step (VLit v1@(Vec len vf1)) (VLit v2@(Vec _ vf2)) =
      Right $ VLit $ Vec len (\i -> (vf1 i) `op'` (vf2 i))
    step (VBlock l1 vs1) (VBlock l2 vs2) =
      simplV $ VBlock l1 $ \b -> (vs1 b `op` vs2 b)
    step v1 v2 = Right v
    v1' = injectExpr $ simplV v1
    v2' = injectExpr $ simplV v2
  in step v1' v2'
simplV v0@(VDot v1 v2) = simplV $ VSum $ injectExpr . simplV $ VProd v1 v2
simplV (VSum (VLit (Vec len vfn))) =
  Left $ ESum len (fullSimpl . vfn)
  --VLit $ Vec 1 (\_ -> ESum len vfn)
simplV (VSum v) = Right $ VSum (injectExpr $ simplV v)
simplV v = Right v
-- END / Simplification --
-- Assign names, LocViews --
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
  cv1 <- concretize n1 v1
  cv2 <- concretize n2 v2
  return $ cv1 ++ cv2 ++ [(idView name , Vec (vlen v1) $ \i -> ((fn n1 :! i) `op'` (fn n2 :! i)))]
concretize name v@(VDot _ _) = error $ "concretize. VDot should be reduced by now: " ++ show v
concretize name (VSum v1) = do
  n1 <- freshName
  cv1 <- concretize n1 v1
  return $ cv1 ++ [(idView name , Vec 1 $ \_ -> fullSimpl $ ESum (fullSimpl $ vlen v1) (\i -> fn n1 :! i))]
-- END / Assign names, LocViews --
-- Compile to explicit loops --
compileELoc :: ELoc -> NameMonad (Loc, [Line])
compileELoc (ELName n) = return (LName n, [])
compileELoc (ELIndex el ind) = do
  (ind, indLines) <- simplCompile ind
  (l, lLines) <- compileELoc el
  return (LIndex l ind, indLines ++ lLines)
compileCV :: (LocView, Vec) -> NameMonad [Line]
compileCV (loc, Vec len val) = do
  (loopBound, lbLines) <- simplCompile len
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
compileV :: VExpr -> NameMonad (Atom, [Line])
compileV vexpr = do
  name <- freshName
  cvs <- concretize name vexpr
  lines <- concat <$> mapM compileCV cvs
  return (fn name, lines)
-- END / Compile to explicit loops --
-- END / Vector Simplification/Compilation --

-- TODO (len, lenLines) <- simplCompile (vlen vexpr) let decl = Decl (LIndex (fn name) len)
-- ^ generate decls

-- Pretty Print Programs --
ppName :: Name -> String
ppName = id
ppLoc :: Loc -> String
ppLoc (LName name) = ppName name
ppLoc (LIndex loc at) = ppLoc loc ++ "[" ++ ppAtom at ++ "]"
ppAtom (R name) = ppName name
ppAtom (I int) = show int
ppOp (a1 ::+ a2) = ppAtom a1 ++ " + " ++ ppAtom a2
ppOp (a1 ::* a2) = ppAtom a1 ++ " * " ++ ppAtom a2
ppRHS :: RHS -> String
ppRHS (ROp op) = ppOp op
ppRHS (RAtom at) = ppAtom at
ppRHS (RLoc loc) = ppLoc loc
ppRHS (RDeref name) = "*("++ppName name++")"
ppLine :: String -> Line -> String
ppLine offset line =
  case line of
    Decl loc ->
      offset ++ ppLoc loc ++ ";\n"
    loc := rhs ->
      offset ++ ppLoc loc ++ " = " ++ ppRHS rhs ++ ";\n"
    Each name lower upper block ->
      offset ++ "for(" ++
         ppName name ++ " = " ++ ppAtom lower ++ "; " ++ 
         ppName name ++ " < " ++ ppAtom upper ++ "; " ++
         ppName name ++ "++) {\n" ++
         concat (map (ppLine ("  " ++ offset)) block) ++
      offset ++ "}\n"
-- END / Pretty Print Programs --

-- TESTS --
pp = putStr . concat . map (ppLine "")
chk  = pp . runName . (snd <$>) . compile . fullSimpl
chkv = pp . runName . (snd <$>) . either compile compileV . simplV
e1, e2, e3 :: E
e1 = fn "x" :+ fn "y"
e2 = e1 :* e1
e3 = e2 :* e2
e4 = (e2 :! e2)
e5 l = ESum l (\i -> i :* i)
v1, v2, v3 :: VExpr
v1 = VLit $ Vec 2 (\_ -> 2)
v1' = VLit $ Vec (fn "len") (\_ -> 2)
v1'' = VLit $ Vec (fn "len") (id)
v2 = VLit $ Vec 2 ((* (fn "x")))
v3 = VProd v1 v2
v3' = VDot v1 v2
v4 = VBlock 2 (\_ -> v1)
v4' = VBlock 2 (\_ -> v1')
v5 = VDot v4 v4
v5' = VDot v4' v4'
v6 = VDot v1 v1
vx1 = VLit $ Vec 1 (\_ -> 0)
vy1 = VLit $ Vec 1 (\_ -> fn "y")
xy = VBlock 2 $ (\(ELit (I n)) -> if n == 0 then vx1 else vy1)
yx = VBlock 2 $ (\(ELit (I n)) -> if n == 0 then vy1 else vx1)
xyd2 = VDot xy v1
xydyx = VDot xy yx

infixr 3 #
x # y = VBlock 2 (\(LitNum n) -> if n == 0 then x else y)
infix 2 **
x ** y = VDot x y
n $$ v = VLit $ Vec n (\_ -> v)
v_1 = 1 $$ 1
v_0 = 1 $$ 0
i :: E -> VExpr
i len = VLit $ Vec len (id)

-- END / TESTS --

-- STUFF --
un = undefined
instance Show (a -> b) where
  show f = "<fn>"
instance Eq (a -> b) where
  a == b = False
instance Ord (a -> b) where
  compare a b = GT -- ???
eExpr :: Simplify.Expr E E Int
eExpr = Simplify.Expr
  { Simplify.isSum = isSum
  , Simplify.isMul = isMul
  , Simplify.isAtom = isAtom
  , Simplify.isPrim = isPrim
  , Simplify.zero = 0
  , Simplify.one = 1
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
instance Num VExpr where
  x * y = VProd x y
  x + y = VPlus x y
  fromInteger x = 1 $$ (fromInteger x)
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
instance IsString E where
  fromString = fn
-- END / STUFF --
