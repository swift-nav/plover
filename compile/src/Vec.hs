{-# LANGUAGE OverloadedStrings #-}
module Vec where
import Prelude hiding ((**))
import Names
import qualified Simplify
import qualified Simplify2 as S
import qualified Data.Map.Strict as M
import Data.List
import Control.Applicative
import Data.String
import Debug.Trace (trace)

-- Reorganization:
--   - clean up, document data types
--   - simplifier
--     - better interface
--     - rebuild term

-- Expressions
infixl 6 :+, :*
data E
  = ELit Atom
  | E :+ E
  | E :* E
  | E :! E
  | ESum E (E -> E)
  deriving (Show, Eq, Ord)
isLit :: E -> Maybe Int
isLit (ELit (I n)) = Just n
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

-- Matrices
type MatLocView = E -> E -> ELoc
type MatView = E -> E -> E
data Mat = Mat E E MatView
  deriving (Show, Eq)
data MExpr
  = MLit Mat
  | MRef Name E E
  | MMul MExpr MExpr
  | MSum MExpr MExpr
  deriving (Show, Eq)

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
infix 4 :==
-- Syntax
data Line
  = Loc := RHS  -- Simple assignment
  | Loc :== RHS -- With type decl
  | Each Name Atom Atom [Line]
  | Decl Name
  deriving (Show, Eq)
-- Type Environment
data BaseType = Int | Float
  deriving (Show, Eq)
data Type = Single BaseType | Array BaseType | Void
  deriving (Show, Eq)
type TypeList = [(Name, Type)]
-- Functions
-- Name, Args, Return argument name
data Signature = Signature Name TypeList (Name, Type)
  deriving (Show, Eq)
data FnExpr = FnExpr Signature MExpr
  deriving (Show, Eq)
data Fn = Fn Signature [Line]
  deriving (Show, Eq)

simplFn :: FnExpr -> FnExpr
simplFn (FnExpr sig mexpr) = FnExpr sig (simplifyM mexpr)
compileFn :: FnExpr -> NameMonad Fn
compileFn (FnExpr sig@(Signature name args (ret, retType)) mexpr) = do
  lines <- compileM ret mexpr
  return $ Fn sig lines


--compileM :: MExpr -> NameMonad (Atom, [Line])
--compileM mexpr = do
--  name <- freshName
--  cms <- concretizeM name mexpr
--  lines <- concat <$> mapM compileCM cms
--  return (fn name, lines)
--
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
--simpl = toE . Simplify.simplify eExpr
simpl = S.simplify expr2expr eScale
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
compile e = do
  n <- freshName
  lines <- compile' n e
  return (R n, lines)

compile' :: Name -> E -> NameMonad [Line]
compile' n e = do
  case e of
    ESum _ _ -> do
      let decl = fn n :== RAtom (I 0)
      lines <- compileSum n e
      return $ decl : lines
    _ -> do
      (lines, rhs) <- compileExpr e
      return $ lines ++ [fn n :== rhs]

compileExpr :: E -> NameMonad ([Line], RHS)
compileExpr (ELit b@(I n)) = return ([], RAtom b)
compileExpr (ELit b@(R n)) = return ([], RAtom b)
compileExpr e | Just (e1, e2) <- binOp e = do
  n1 <- freshName
  n2 <- freshName
  ls1 <- compile' n1 e1
  ls2 <- compile' n2 e2
  (lines, rhs) <- doOp e (fn n1) (fn n2)
  return (ls1 ++ ls2 ++ lines, rhs)
compileSum :: Name -> E -> NameMonad [Line]
compileSum output (ESum len vfn) =
  case isLit len of
    --Just n ->
    --  error "compile. ESum. should be reduced already"
    _ -> do
      (loopBound, lbLines) <- compile len
      let initLine = fn output := RAtom (I 0)
      index  <- freshName
      (exprName, exprLines) <- compile (vfn (fn index))
      let loop = Each index (I 0) loopBound (exprLines ++ [update])
          update = fn output := ROp (fn output ::+ exprName)
      return $ [initLine] ++ lbLines ++ [loop]
doOp (_ :+ _) n1 n2 = do
  return ([], ROp (n1 ::+ n2))
doOp (_ :* _) n1 n2 = do
  return ([], ROp (n1 ::* n2))
-- TODO remove?
doOp (_ :! _) n1 n2 = do
  np <- freshName
  let ls = [fn np := ROp (n1 ::+ n2)]
  return (ls, RDeref np)
-- END / Expression Compilation --
-- END / Expression Simplification/Compilation --

-- Vector Simplification/Compilation --
-- TODO add length checking
-- TODO generate decls: -- (len, lenLines) <- simplCompile (vlen vexpr) let decl = Decl (LIndex (fn name) len)
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
-- requires change of concretize type :(
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

-- Matrices --
matView :: E -> Name -> E -> E -> ELoc
matView width name i j = ELIndex (fn name) (i * width + j)
simplifyM = simplM . expandRefM
expandRefM :: MExpr -> MExpr
expandRefM (MRef name rows cols) = MLit (Mat rows cols (\i j -> fn name :! (i * cols) + j))
expandRefM (MMul m1 m2) = MMul (expandRefM m1) (expandRefM m2)
expandRefM (MSum m1 m2) = MSum (expandRefM m1) (expandRefM m2)
expandRefM m@(MLit _) = m
simplM :: MExpr -> MExpr
simplM (MMul (MLit (Mat rs1 cs1 mfn1)) (MLit (Mat rs2 cs2 mfn2))) =
  simplM $ MLit $ Mat rs1 cs2 $ \i k -> ESum cs1 (\j -> mfn1 i j * mfn2 j k)
simplM (MSum (MLit (Mat rs1 cs1 mfn1)) (MLit (Mat _ _ mfn2))) =
  simplM $ MLit $ Mat rs1 cs1 $ \i j -> mfn1 i j + mfn2 i j
simplM (MLit (Mat rs cs mfn)) = MLit $ Mat (fullSimpl rs) (fullSimpl cs) (\i j -> fullSimpl (mfn i j))
simplM m = m
idMView width name r c = ELIndex (fn name) (r * width + c)
concretizeM :: Name -> MExpr -> NameMonad [(MatLocView, Mat)]
concretizeM name (MLit m@(Mat _ cs _)) = return [(idMView cs name, m)]
compileCM :: (MatLocView, Mat) -> NameMonad [Line]
compileCM (loc, Mat rs cs val) = do
  (rLoopBound, rlLines) <- simplCompile rs
  (cLoopBound, clLines) <- simplCompile cs
  rIndex <- freshName
  cIndex <- freshName
  blockLines <- compileEntry loc val (fn rIndex) (fn cIndex)
  let loop = Each rIndex (I 0) rLoopBound
               [Each cIndex (I 0) cLoopBound
                 blockLines]
  return $ rlLines ++ clLines ++ [loop]
 where
   compileEntry loc val i j = do
     (lhs, lhsLines) <- compileELoc (loc i j)
     (val, valLines) <- simplCompile (val i j)
     return $ lhsLines ++ valLines ++ [lhs := RAtom val]
compileM :: Name -> MExpr -> NameMonad [Line]
compileM name mexpr = do
  cms <- concretizeM name mexpr
  lines <- concat <$> mapM compileCM cms
  return lines

compileM' expr = do
  n <- freshName
  lines <- compileM n expr
  return (n, lines)

seqPair :: Monad m => m a -> (a -> m b) -> m (a, b)
seqPair m f = do
  a <- m
  b <- f a
  return (a, b)

-- END / Matrices? --

-- Pretty Print Programs --
-- TODO use standard C syntax library?
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
    Decl name ->
      offset ++ ppName name ++ ";\n"
    loc := rhs ->
      offset ++ ppLoc loc ++ " = " ++ ppRHS rhs ++ ";\n"
    loc :== rhs ->
      offset ++ "float " ++ ppLoc loc ++ " = " ++ ppRHS rhs ++ ";\n"
    Each name lower upper block ->
      offset ++ "for(" ++
         "int " ++ ppName name ++ " = " ++ ppAtom lower ++ "; " ++ 
         ppName name ++ " < " ++ ppAtom upper ++ "; " ++
         ppName name ++ "++) {\n" ++
         concat (map (ppLine ("  " ++ offset)) block) ++
      offset ++ "}\n"

ppBaseType :: BaseType -> String
ppBaseType Int = "int"
ppBaseType Float = "float"
ppType :: Type -> String
ppType (Single bt) = ppBaseType bt
ppType (Array bt) = ppBaseType bt ++ "*"
ppType Void = "void"
ppArg :: (Name, Type) -> String
ppArg (name, t) = ppType t ++ " " ++ ppName name
ppSig :: Signature -> String -> String
ppSig (Signature name args ret) body = str ++ " {\n" ++ body ++ "}\n"
 where
   str = "void " ++ name ++ "("
         ++ intercalate ", " (map ppArg (ret : args))
         ++ ")"
ppFn :: Fn -> String
ppFn (Fn sig lines) = ppSig sig (concat (map (ppLine "  ") lines))
-- END / Pretty Print Programs --

-- Notation --
infixr 3 #
x # y = VBlock 2 (\(ELit (I n)) -> if n == 0 then x else y)
infix 2 **
x ** y = VDot x y
n $$ v = VLit $ Vec n (\_ -> v)
v_1 = 1 $$ 1
v_0 = 1 $$ 0
i :: E -> VExpr
i len = VLit $ Vec len (id)
-- END / Notation --

-- Test expressions --
pp = putStr . concat . map (ppLine "")
chk  = pp . snd . runName . compile . fullSimpl
chkv = pp . snd . runName . either compile compileV . simplV
chkm = pp . snd . runName . compileM' . simplifyM
chkf = putStr . ppFn . runName . compileFn . simplFn
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

m1  = MLit $ Mat 1 1 (\_ _ -> 1)
mp2 = MLit $ Mat 2 2 (\i j -> i + j)
mpn n = MLit $ Mat n n (\i j -> i + j)
mpn' n = MLit $ Mat n n (\i j -> "x" :! (i * "c" + j))

fn1 = FnExpr (Signature
                "multiply"
                [("x", Array Float), ("y", Array Float),
                 ("k", Single Int), ("m", Single Int), ("n", Single Int)]
                ("z", Array Float))
             (MRef "x" "k" "m" * MRef "y" "m" "n")
-- END / Test expressions --

-- STUFF --
instance Show (a -> b) where
  show f = "<fn>"
-- TODO is this desirable?
instance Eq (a -> b) where
  a == b = False
instance Ord (a -> b) where
  compare a b = GT -- ???
expr2expr :: E -> S.Expr E Int
expr2expr (a :+ b) = S.Sum [expr2expr a, expr2expr b]
expr2expr (a :* b) = S.Mul [expr2expr a, expr2expr b]
expr2expr (ELit (I 0)) = S.Zero
expr2expr (ELit (I 1)) = S.One
expr2expr l@(ELit (I n)) = S.Prim n l
expr2expr e@(ELit (R n)) = S.Atom e
expr2expr e@(_ :! _) = S.Atom e
expr2expr e@(ESum _ _) = S.Atom e
eScale :: Int -> E -> E
eScale n e | e == fromIntegral 1 = fromIntegral n
eScale 0 e = 0
eScale 1 e = e
eScale n e = fromIntegral n * e

-- TODO remove references to Simplify in favor of new library
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
instance Num E where
  x * y = x :* y
  x + y = x :+ y
  fromInteger x = ELit . I $ (fromInteger x)
  abs = undefined
  signum = undefined
  negate = undefined
instance Num VExpr where
  x * y = VProd x y
  x + y = VPlus x y
  fromInteger x = 1 $$ (fromInteger x)
  abs = undefined
  signum = undefined
  negate = undefined
instance Num MExpr where
  x * y = MMul x y
  x + y = MSum x y
  fromInteger x = MLit $ Mat 1 1 (\_ _ -> fromInteger x)
  abs = undefined
  signum = undefined
  negate = undefined
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
