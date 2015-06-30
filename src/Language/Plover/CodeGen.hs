{-# LANGUAGE QuasiQuotes #-}

-- Remember: CODE GEN DON'T CARE.  This should be as simple as
-- possible while generating code which isn't too terrible.  It should
-- not do any simplifications that the reducer could do.

module Language.Plover.CodeGen where

import Language.C.Quote.C
import qualified Language.C.Syntax as C
import Language.C.Pretty
import Text.PrettyPrint.Mainland

import Data.Either
import Data.Tag
import Control.Monad.State
import qualified Data.Map as M

import Language.Plover.Types hiding (freshName)

import Data.Loc (SrcLoc(SrcLoc), Loc(NoLoc))

import Debug.Trace
strace :: Show a => a -> a
strace x = trace ("@@@ " ++ show x) x


data CodeGenState = CodeGenState
                    { bindings :: M.Map String String
                    , usedNames :: [String]
                    }
                    deriving Show

type CM a = State CodeGenState a

runCM :: CM a -> a
runCM m = evalState m (CodeGenState M.empty [])

newScope :: CM a -> CM a
newScope m = do bs <- bindings <$> get
                un <- usedNames <$> get
                v <- m
                modify $ \state -> state { bindings = bs, usedNames = un }
                return v

-- | Creates a new scope, but any names used cannot be used after the
-- scope.  Sometimes we don't want to insert { blocks }, for instance
-- with Let.
newBlocklessScope :: CM a -> CM a
newBlocklessScope m = do bs <- bindings <$> get
                         v <- m
                         modify $ \state -> state { bindings = bs }
                         return v

-- | Creates a valid C identifier from a string.  The def argument is
-- the default string to use if there is nothing to salvage.
getOkIdentifier :: String -> String -> String
getOkIdentifier def [] = def
getOkIdentifier def (v:vs) | v `elem` okStart = v : takeWhile (`elem` okRest) vs
                           | otherwise = getOkIdentifier def []
  where okStart = ['A'..'Z'] ++ ['a'..'z'] ++ "_"
        okRest = okStart ++ ['0'..'9']

-- | Gets a C identifier for a given Plover identifier
lookupName :: String -> String -> CM String
lookupName def v = do bs <- bindings <$> get
                      case M.lookup v bs of
                       Just v' -> return v'
                       Nothing -> newName def v

-- | Gets a unique name (and store it in the used variable list).  The
-- argument is the base for the name, and must be a valid C
-- identifier.
freshName :: String -> CM String
freshName v = freshName' 1 v
  where freshName' :: Int -> String -> CM String
        freshName' i v = do bs <- usedNames <$> get
                            let v' = if i == 1
                                     then v
                                     else v ++ show i
                            if v' `elem` bs
                              then freshName' (i + 1) v
                              else do modify $ \state -> state { usedNames = v' : bs }
                                      return v'

-- | Gets a new C identifier for a given Plover identifier (i.e., it
-- should shadow a previous binding)
newName :: String -> String -> CM String
newName def v = do v' <- freshName (getOkIdentifier def v)
                   modify $ \state -> state { bindings = M.insert v v' (bindings state) }
                   return v'

compileTopLevel :: [DefBinding] -> CM [C.Definition]
compileTopLevel defbs = do let defbs' = filter (not . extern) defbs
                           forM_ defbs' $ \defb ->
                             lookupName (error "Invalid top-level name") (binding defb)
                           d1 <- fmap concat $ forM defbs' $ \defb -> newScope $ case definition defb of
                             FunctionDef mexp ft -> compileFunctionDecl (binding defb) ft
                             _ -> return []
                           d2 <- fmap concat $ forM defbs' $ \defb -> newScope $ case definition defb of
                             FunctionDef (Just body) ft -> compileFunction (binding defb) ft body
                             _ -> return []
                           return (includes ++ d1 ++ d2)
  where includes = [cunit|$esc:("#include <stdbool.h>") |]

compileFunctionDecl :: String -> FunctionType -> CM [C.Definition]
compileFunctionDecl name ft = do
  args'' <- compileParams args'
  return $ case args'' of
    [] -> [ [cedecl| $ty:(compileType retty) $id:(name)(void); |] ]
    _ ->  [ [cedecl| $ty:(compileType retty) $id:(name)($params:(args'')); |] ]
  where (FnT args retty, _) = getEffectiveFunType ft
        nonVoid ty = case ty of
                      Void -> False
                      _ -> True
        args' = [(v, ty) | (v, _, _, ty) <- args, nonVoid ty]

compileFunction :: String -> FunctionType -> CExpr -> CM [C.Definition]
compileFunction name ft exp = do
  args'' <- compileParams args'
  blks <- case retty of
    Void -> noValue $ compileStat exp
    _ -> do (expbl, expex) <- withValue $ compileStat exp
            return (expbl ++ [ [citem| return $expex; |] ])
  return $ case args'' of
    [] -> [ [cedecl| $ty:(compileType retty) $id:(name)(void) { $items:blks } |] ]
    _ ->  [ [cedecl| $ty:(compileType retty) $id:(name)($params:(args'')) { $items:blks } |] ]
  where (FnT args retty, _) = getEffectiveFunType ft
        nonVoid ty = case ty of
                      Void -> False
                      _ -> True
        args' = [(v, ty) | (v, _, _, ty) <- args, nonVoid ty]
  

compileParams :: [(Variable, Type)] -> CM [C.Param]
compileParams = mapM compileParam

compileParam :: (Variable, Type) -> CM C.Param
compileParam (v, ty) = do v' <- lookupName "arg" v
                          return [cparam| $ty:(compileType ty) $id:(v') |]

compileType :: Type -> C.Type
compileType = compileType' . normalizeTypes

compileType' :: Type -> C.Type
compileType' (VecType _ ty) = [cty|$ty:(compileType ty)*|] -- make sure type is normalized
compileType' Void = [cty|void|]
compileType' (IntType IDefault) = compileType (IntType actualDefaultIntType)
compileType' (IntType U8) = [cty|typename u8|]
compileType' (IntType S8) = [cty|typename s8|]
compileType' (IntType U16) = [cty|typename u16|]
compileType' (IntType S16) = [cty|typename s16|]
compileType' (IntType U32) = [cty|typename u32|]
compileType' (IntType S32) = [cty|typename s32|]
compileType' (IntType U64) = [cty|typename u64|]
compileType' (IntType S64) = [cty|typename s64|]
compileType' (FloatType FDefault) = compileType (FloatType actualDefaultFloatType)
compileType' (FloatType Float) = [cty|float|]
compileType' (FloatType Double) = [cty|double|]
compileType' StringType = [cty|char*|]
compileType' BoolType = [cty|typename bool|]
compileType' (PtrType ty) = [cty|$ty:(compileType ty)*|]
compileType' (TypedefType v) = [cty|typename $id:v*|]
compileType' (StructType v _) = [cty|typename $id:v*|]
compileType' (TypeHole _) = error "No type holes allowed."

-- When initializing a variable, need things like the length of the
-- array rather than just a pointer
compileInitType :: Type -> CM ([C.BlockItem], C.Type)
compileInitType ty = compileInitType' (normalizeTypes ty)

compileInitType' :: Type -> CM ([C.BlockItem], C.Type)
compileInitType' (VecType idxs base) = do (sizebl, sizeex) <- withValue $ compileStat (foldr1 (*) idxs)
                                          (basebl, basety) <- compileInitType base
                                          return (sizebl ++ basebl,
                                                  [cty|$ty:basety[$sizeex] |])
--compileInitType' -- structs are weird
compileInitType' t = return ([], compileType t)

data Compiled = Compiled { noValue :: CM [C.BlockItem]
                         , withDest :: CmLoc -> CM [C.BlockItem]
                         , withValue :: CM ([C.BlockItem], C.Exp)
                         , asLoc :: CM ([C.BlockItem], CmLoc)
                         }

-- withValue :: Compiled -> CM ([C.BlockItem], C.Exp)
-- withValue com = do (prep, loc) <- asLoc com
--                    (bl, exp) <- asRValue loc
--                    return (prep ++ bl, exp)

data CmLoc = CmLoc { apIndex :: C.Exp -> CM ([C.BlockItem], CmLoc)
                     -- ^ apply an index to a vector location
                   , store :: C.Exp -> CM [C.BlockItem]
                     -- ^ store an expression if this is a simple (i.e, non-vector) location
                   , asRValue :: Compiled
                     -- ^ get the compiled simple (i.e., non-vector) expression
                   , asArgument :: CM ([C.BlockItem], [C.BlockItem], C.Exp, [C.BlockItem])
                     -- ^ get a representation of the location (of any
                     -- type) which can be passed as an argument to a
                     -- function.  The first is setup for a location,
                     -- the second is setup for an In variable, the
                     -- third is the expression to pass, and the
                     -- fourth is for an Out variable.
                   , locType :: Type
                     -- ^ gets the type of this location. Every type
                     -- should know its location, and this helps for
                     -- generating store code
                   }


-- | makes a simple-valued location
expLoc :: Type -> C.Exp -> CmLoc
expLoc ty exp = CmLoc { apIndex = error "Cannot apIndex expLoc"
                      , store = \v -> return $ [ [citem| $exp = $v; |] ]
                      , asRValue = compPureExpr ty $ return ([], exp)
                      , asArgument = return ([], [], exp, [])
                      , locType = ty
                      }

-- | takes a C identifier and makes a simple-valued location
refLoc :: Type -> String -> CmLoc
refLoc ty v = expLoc ty [cexp| $id:v |]

-- | generates a fresh location using freshName
freshLoc :: String -> Type -> CM ([C.BlockItem], CmLoc)
freshLoc v ty = do v' <- freshName v
                   makeLoc v' ty

-- | generates a stack location using the C identifier
makeLoc :: String -> Type -> CM ([C.BlockItem], CmLoc)
makeLoc v ty = case normalizeTypes ty of
  VecType idxs bty -> do (vbl, vty) <- compileInitType ty
                         return $ (vbl ++ [ [citem| $ty:vty $id:v; |] ],
                                   mkVecLoc bty [cexp| $id:v|] idxs)
  _ -> do (vbl, vty) <- compileInitType ty
          return $ (vbl ++ [ [citem| $ty:vty $id:v; |] ],
                    refLoc ty v)

-- | Type is normalized type of vector.  Creates a vector based on
-- using C indexing of the expression, assuming the expression is
-- stored linearly in memory.
mkVecLoc :: Type -> C.Exp -> [CExpr] -> CmLoc
mkVecLoc baseTy vec bnds = mkVecLoc' [] bnds
  where mkVecLoc' :: [(C.Exp, CExpr)] -> [CExpr] -> CmLoc
        mkVecLoc' acc [] = CmLoc {
          apIndex = error "All indices already applied."
          , store = \exp -> do (blks, idxc) <- collapseIdx idx idxs bnds []
                               return $ blks ++ [ [citem| $vec[$idxc] = $exp; |] ]
          , asRValue = compImpureExpr baseTy $
                       do (blks, idxc) <- collapseIdx idx idxs bnds []
                          return (blks, [cexp| $vec[$idxc] |])
          , asArgument = do (blks, idxc) <- collapseIdx idx idxs bnds []
                            return (blks, [], [cexp| $vec[$idxc] |], [])
          , locType = baseTy
          }
          where (idx:idxs, bnds) = unzip acc
        mkVecLoc' acc (bnd:bnds) = CmLoc {
          apIndex = \idx -> return ([], mkVecLoc' (acc ++ [(idx, bnd)]) bnds)
          , store = error "Cannot do simple store into vector"
          , asRValue = compPureExpr (VecType (bnd:bnds) baseTy) $ return ([], vec) -- TODO ?
          , asArgument = case acc of
              [] -> return ([], [], vec, [])
              _ -> do (blks, exp) <- withValue $ compPureExpr (VecType (bnd:bnds) baseTy) $ return ([], vec)
                      return (blks, [], exp, [])
          , locType = VecType (bnd:bnds) baseTy
        }
        collapseIdx :: C.Exp -> [C.Exp] -> [CExpr] -> [C.BlockItem] -> CM ([C.BlockItem], C.Exp)
        collapseIdx accidx [] _ blks = return (blks, accidx)
        collapseIdx accidx (idx:idxs) (bnd:bnds) blks = do (bndbl, bndex) <- withValue $ compileStat bnd
                                                           collapseIdx [cexp| $bndex * $accidx + $idx |]
                                                             idxs bnds (blks ++ bndbl)

deferLoc :: Type -> CmLoc -> Int -> (CmLoc -> CM ([C.BlockItem], CmLoc))
            -> CM ([C.BlockItem], CmLoc)
deferLoc ty loc 0 f = f loc
deferLoc ty loc n f = return ([], dloc)
  where dloc = CmLoc
               { apIndex = \idx -> do (bl', loc') <- apIndex loc idx
                                      (bl'', loc'') <- deferLoc ty' loc' (n - 1) f
                                      return (bl' ++ bl'', loc'')
               , store = error $ "Cannot store into deferLoc"
               , asRValue = comp
               , asArgument = do (locbl, loc) <- freshLoc "arg" ty
                                 (locbl', locex) <- withValue $ asRValue loc 
                                 st <- storeLoc loc dloc
                                 str <- storeLoc dloc loc
                                 return (locbl ++ locbl', st, locex, str)
               , locType = ty
               }
        comp = Compiled
               { withDest = \dest -> storeLoc dest dloc
               , withValue = defaultWithValue ty comp
               , noValue = defaultNoValue ty comp
               , asLoc = return ([], dloc)
               }

        VecType (bnd:bnds) bty = normalizeTypes ty
        ty' = VecType bnds bty

-- | uses withValue, executing exp as a statement.
defaultNoValue :: Type -> Compiled -> CM [C.BlockItem]
defaultNoValue ty comp = do (bbl, exp) <- withValue comp
                            return $ bbl ++ [ [citem| $exp; |] ]

-- | uses withValue
defaultWithDest :: Type -> Compiled -> (CmLoc -> CM [C.BlockItem])
defaultWithDest ty comp loc = do (bbl, exp) <- withValue comp
                                 sbl <- storeExp loc exp
                                 return (bbl ++ sbl)


-- | uses withDest
defaultWithValue :: Type -> Compiled -> CM ([C.BlockItem], C.Exp)
defaultWithValue ty comp = do (locbl, loc) <- freshLoc "tmp" ty
                              spbl <- withDest comp loc
                              (vbl, vex) <- withValue $ asRValue loc
                              return (locbl ++ spbl ++ vbl, vex)

-- | uses withDest
defaultAsLoc :: Type -> Compiled -> CM ([C.BlockItem], CmLoc)
defaultAsLoc ty comp = do (locbl, loc) <- freshLoc "loc" ty
                          spbl <- withDest comp loc
                          return (locbl ++ spbl, loc)

-- | uses withValue
defaultAsLocFromWithValue :: Type -> Compiled -> CM ([C.BlockItem], CmLoc)
defaultAsLocFromWithValue ty comp = do (bl, exp) <- withValue comp
                                       return (bl, expLoc ty exp)

-- | uses asRValue and apIndex.  Just spills the thing into a new
-- location.
defaultAsArgument :: CmLoc -> CM ([C.BlockItem], [C.BlockItem], C.Exp, [C.BlockItem])
defaultAsArgument loc = do (flocbl, floc) <- freshLoc "loc" (locType loc)
                           spbl <- storeLoc floc loc
                           (bef, prep, exp, aft) <- asArgument floc
                           return (flocbl ++ bef, spbl ++ prep, exp, aft)

bindBl :: CM ([C.BlockItem], a) -> (a -> CM ([C.BlockItem], b)) -> CM ([C.BlockItem], b)
bindBl ma f = do (bl, a) <- ma
                 (bl', b) <- f a
                 return (bl ++ bl', b)

storeExp :: CmLoc -> C.Exp -> CM [C.BlockItem]
storeExp dst exp = case normalizeTypes (locType dst) of
  VecType idxs bty -> storeLoc dst (mkVecLoc bty exp idxs)
  _ -> store dst exp

storeLoc :: CmLoc -> CmLoc -> CM [C.BlockItem]
storeLoc dst src = case normalizeTypes (locType dst) of
  VecType (idx:idxs) bty -> makeFor idx $ \i -> do
    (dstbl, dst') <- apIndex dst i
    (srcbl, src') <- apIndex src i
    substore <- storeLoc dst' src'
    return $ dstbl ++ srcbl ++ substore
  _ -> withDest (asRValue src) dst

makeFor :: CExpr -> (C.Exp -> CM ([C.BlockItem])) -> CM [C.BlockItem]
makeFor idx mbody = newScope $ do
  let itty = compileType $ getType idx
  i <- freshName "idx"
  (boundBl, boundEx) <- withValue $ compileStat idx
  body <- mbody [cexp| $id:i |]
  return $ boundBl ++ [ [citem| for ($ty:itty $id:i = 0; $id:i < $boundEx; $id:i++) { $items:body } |] ]

-- | an expression with no side effects does not need to be computed
-- if no result is needed.
compPureExpr :: Type -> CM ([C.BlockItem], C.Exp) -> Compiled
compPureExpr ty mexpr = comp
  where comp = Compiled
               { noValue = do (bl, expr) <- mexpr
                              return bl
               , withDest = defaultWithDest ty comp
               , withValue = mexpr
               , asLoc = do (bl, expr) <- mexpr
                            return $ (bl, expLoc ty expr)
               }

compImpureExpr :: Type -> CM ([C.BlockItem], C.Exp) -> Compiled
compImpureExpr ty mexpr = comp
  where comp = Compiled
               { noValue = defaultNoValue ty comp
               , withDest = defaultWithDest ty comp
               , withValue = do (bl, expr) <- mexpr
                                return (bl, expr)
               , asLoc = defaultAsLoc ty comp }

compLoc :: Type -> CM ([C.BlockItem], CmLoc) -> Compiled
compLoc ty mloc = comp
  where comp = Compiled
               { noValue = do (bbl, loc) <- mloc
                              bbl' <- noValue $ asRValue loc
                              return $ bbl ++ bbl'
               , withDest = \dest -> do (bbl, loc) <- mloc
                                        bbl' <- storeLoc dest loc
                                        return $ bbl ++ bbl'
               , withValue = do (bbl, loc) <- mloc
                                (bbl', exp) <- withValue $ asRValue loc
                                return (bbl ++ bbl', exp)
               , asLoc = mloc
               }

testCompileExpr :: CExpr -> String
testCompileExpr exp = let (blks, v) = evalState (withValue $ compileStat exp) (CodeGenState M.empty [])
                          item = if null blks
                                 then [citem| { return $v; } |]
                                 else [citem| { $items:blks return $v; } |]
                      in show $ ppr item


compileStat :: CExpr -> Compiled

compileStat v@(Vec _ i range exp) = comp
  where comp = Compiled
               { noValue = return []
               , withDest = \dest -> newScope $ do
                    let ty@(VecType bnds bty) = normalizeTypes (getType v)
                        itty = compileType $ getType (head bnds)
                    vidx <- newName "i" i
                    (boundBl, boundEx) <- withValue $ compileStat (head bnds)
                    (srcbl, src) <- asLoc $ compileStat exp
                    let cvidx = [cexp|$id:vidx|]
                    (ccvidxbl, ccvidx) <- rngExp cvidx
                    (destbl, dest') <- apIndex dest cvidx
                    stbl <- storeLoc dest' src
                    return $ destbl ++ boundBl
                      ++ mkFor itty vidx boundEx (ccvidxbl ++ srcbl ++ stbl)
               , withValue = defaultWithValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
        rngExp idx = case range of
          Range (IntLit _ _ 0) end (IntLit _ _ 1) -> return ([], idx)
          Range start end (IntLit _ _ 1) -> do (stblk, stex) <- withValue $ compileStat start
                                               return (stblk, [cexp| $stex + $idx |])
          Range (IntLit _ _ 0) end step -> do (stepblk, stepex) <- withValue $ compileStat step
                                              return (stepblk, [cexp| $stepex * $idx |])
          Range start end step -> do (stblk, stex) <- withValue $ compileStat start
                                     (stepblk, stepex) <- withValue $ compileStat step
                                     return (stblk ++ stepblk, [cexp| $stex + $idx * $stepex |])

        mkFor vidxty vidx bnd bodybl =
          [ [citem| for ($ty:vidxty $id:vidx = 0; $id:vidx < $bnd; $id:vidx++) { $items:bodybl } |] ]

compileStat exp@(RangeVal _ range) = comp
  where comp = Compiled
               { noValue = defaultNoValue ty comp
               , withDest = \dest -> do (bll, loc) <- asLoc comp
                                        st <- storeLoc dest loc
                                        return $ bll ++ st
               , withValue = defaultWithValue ty comp
               , asLoc = return ([], loc)
               }
        ty@(VecType _ bty) = normalizeTypes $ getType exp
        
        loc = CmLoc
              { apIndex = \idx -> do (bl, exp) <- rngExp idx
                                     return (bl, expLoc bty exp)
              , store = error "Cannot store into rangeval"
              , asRValue = error "cannot asRValue rangeval"
              , asArgument = do (bl, ex) <- withValue comp
                                return (bl, [], ex, [])
              , locType = ty
              }

        rngExp idx = case range of
          Range (IntLit _ _ 0) end (IntLit _ _ 1) -> return ([], idx)
          Range start end (IntLit _ _ 1) -> do (stblk, stex) <- withValue $ compileStat start
                                               return (stblk, [cexp| $stex + $idx |])
          Range (IntLit _ _ 0) end step -> do (stepblk, stepex) <- withValue $ compileStat step
                                              return (stepblk, [cexp| $stepex * $idx |])
          Range start end step -> do (stblk, stex) <- withValue $ compileStat start
                                     (stepblk, stepex) <- withValue $ compileStat step
                                     return (stblk ++ stepblk, [cexp| $stex + $idx * $stepex |])


compileStat (If _ a b c) = comp
  where comp = Compiled
               { noValue = do (abl, aexp) <- withValue $ compileStat a
                              bbl <- noValue $ compileStat b
                              cbl <- noValue $ compileStat c
                              return (abl ++ mkIf aexp bbl cbl)
               , withDest = \loc -> do (abl, aexp) <- withValue $ compileStat a
                                       bbl <- withDest (compileStat b) loc
                                       cbl <- withDest (compileStat c) loc
                                       return (abl ++ mkIf aexp bbl cbl)
               , withValue = defaultWithValue (getType b) comp
               , asLoc = defaultAsLoc (getType b) comp
               }
        mkIf aexp bbl cbl = [ [citem| if ($aexp) { $items:bbl } else { $items:cbl } |] ]

compileStat (VoidExpr _) = Compiled { noValue = return []
                                    , withDest = \v -> error "Cannot store VoidExpr"
                                    , withValue = return $ ([], error "Cannot get VoidExpr")
                                    , asLoc = return $ ([], error "Cannot get VoidExpr") }
compileStat x@(IntLit _ _ v) = compPureExpr (getType x) $ return ([], [cexp| $int:v |]) -- TODO consider type
compileStat x@(FloatLit _ _ v) = compPureExpr (getType x) $ return ([], [cexp| $double:(toRational v) |]) -- TODO consider type
compileStat (StrLit _ s) = compPureExpr StringType $ return ([], [cexp| $string:s |])
compileStat (BoolLit _ b) = compPureExpr BoolType $ return ([], [cexp| $id:lit |])
  where lit :: String
        lit = if b then "true" else "false"

compileStat v@(VecLit pos ty xs) = comp
  where comp = Compiled
               { noValue = defaultNoValue vty comp
               , withDest = \dest -> fmap concat $ forM (zip [0..] xs) $ \(i,x) -> do
                    (dstbl, xdst) <- apIndex dest [cexp| $int:i |]
                    xbl <- withDest (compileStat x) xdst
                    return $ dstbl ++ xbl
               , withValue = defaultWithValue vty comp
               , asLoc = defaultAsLoc vty comp
               }
        vty = normalizeTypes $ getType v

compileStat (Let _ v val x) = comp
  where comp = Compiled
               { withDest = \dest -> makeLet $ \bbl -> do
                  xbl <- withDest (compileStat x) dest
                  return $ bbl ++ xbl
               , noValue = makeLet $ \bbl -> do
                    xbl <- noValue $ compileStat x
                    return $ bbl ++ xbl
               , withValue = makeLet $ \bbl -> do
                    (xbl, xex) <- withValue (compileStat x)
                    return $ (bbl ++ xbl, xex)
               , asLoc = defaultAsLoc xty comp
               }
        xty = normalizeTypes $ getType x
        makeLet f = newBlocklessScope $ do
          v' <- newName "let" v
          (locbl, loc) <- makeLoc v' (getType val)
          valbl <- case val of
            Uninitialized {} -> return []
            _ -> withDest (compileStat val) loc -- TODO this is wrongly inside the new scope 
          f (locbl ++ valbl)

-- -- skipping Uninitialized

compileStat (Seq _ a b) = comp
  where comp = Compiled
               { noValue = do abl <- noValue $ compileStat a
                              bbl <- noValue $ compileStat b
                              return (abl ++ bbl)
               , withDest = \loc -> do abl <- noValue $ compileStat a
                                       bbl <- withDest (compileStat b) loc
                                       return (abl ++ bbl)
               , withValue = do abl <- noValue $ compileStat a
                                (bbl, bexp) <- withValue $ compileStat b
                                return (abl ++ bbl, bexp)
               , asLoc = do abl <- noValue $ compileStat a
                            (bbl, bloc) <- asLoc $ compileStat b
                            return (abl ++ bbl, bloc)
               }

compileStat (ConcreteApp pos (Get _ (Ref (FnType ft) f)) args) = comp
  where comp = Compiled
               { withValue = do (bbl, fexp, bbl') <- theCall f dargs
                                case bbl' of
                                 [] -> return (bbl, fexp)
                                 _ -> do (locbl, loc) <- freshLoc "ret" retty
                                         st <- storeExp loc fexp
                                         (locbl', ex) <- withValue $ asRValue loc
                                         return (bbl ++ locbl ++ st ++ bbl' ++ locbl', ex)
               , withDest = \dest -> do (bbl, fexp, bbl') <- theCall f dargs
                                        stbl <- storeExp dest fexp
                                        return (bbl ++ stbl ++ bbl')
               , noValue = do (bbl, fexp, bbl') <- theCall f dargs
                              return (bbl ++ [[citem| $fexp; |]] ++ bbl')
               , asLoc = do (bbl, fexp, bbl') <- theCall f dargs
                            case bbl' of
                              [] -> return (bbl, expLoc retty fexp)
                              _ -> do (locbl, loc) <- freshLoc "ret" retty
                                      st <- storeExp loc fexp
                                      return (bbl ++ locbl ++ st ++ bbl', loc)
               }

        (FnT params retty, _) = getEffectiveFunType ft
        dirs = map (\(_,_,dir,_) -> dir) params
        dargs = zip dirs args

        -- | Returns what to do before the call, the argument, and what to do after the call
        theCall :: String -> [(ArgDir, CExpr)] -> CM ([C.BlockItem], C.Exp, [C.BlockItem])
        theCall f args = do
          args' <- forM args $ \(dir, a) ->
            case voidType a of
             True -> do c' <- noValue $ compileStat a
                        return $ Left c'
             False -> do (abl, aloc) <- asLoc $ compileStat a
                         (argbl, prep, arg, argbl') <- asArgument aloc
                         return $ case dir of
                           ArgIn -> Right (abl ++ argbl ++ prep, arg, [])
                           ArgOut -> Right (abl ++ argbl, arg, argbl')
                           ArgInOut -> Right (abl ++ argbl ++ prep, arg, argbl')
          let bbl = concat $ flip map args' $ \x -> case x of
                                                     Left bl -> bl
                                                     Right (bl, _, _) -> bl
              args'' = map (\(_,x,_) -> x) $ rights args'
              bbl' = concat $ flip map args' $ \x -> case x of
                                                      Left _ -> []
                                                      Right (_, _, bl) -> bl
              fexp = [cexp| $id:(f)($args:(args'')) |]
          return (bbl, fexp, bbl')
        voidType :: CExpr -> Bool
        voidType exp = case normalizeTypes $ getType exp of
          Void -> True
          _ -> False

compileStat (Hole {}) = error "No holes allowed"

compileStat (Get pos (Index a [])) = compileStat a
compileStat v@(Get pos loc) = compLoc (getType v) (compileLoc loc)

compileStat v@(Addr pos loc) = comp
  where comp = Compiled
               { withValue = do (bloc, loc) <- compileLoc loc
                                (bl, exp) <- withValue $ asRValue loc
                                return (bloc ++ bl, [cexp| & $exp |])
               , noValue = defaultNoValue (getType v) comp
               , withDest = defaultWithDest (getType v) comp
               , asLoc = do (bl, ex) <- withValue $ comp
                            return (bl, expLoc (getType v) ex)
               }

compileStat (Set pos loc v) = comp
  where comp = Compiled
               { noValue = do (bloc, loc) <- compileLoc loc
                              stbl <- withDest (compileStat v) loc
                              return $ bloc ++ stbl
               , withDest = \dst -> do bl <- noValue comp -- Shouldn't happen, but just in case...
                                       return bl
               , withValue = do bl <- noValue comp
                                return (bl, error "Cannot get Set as value.")
               , asLoc = error "Set is not a location"
               }

compileStat (AssertType pos a ty) = compileStat a

-- -- unary
-- -- binary

compileStat v@(Binary _ op a b)
  | op `elem` [Add, Sub] = compileVectorized aty bty (asLoc $ compileStat a) (asLoc $ compileStat b)
  where aty = normalizeTypes $ getType a
        bty = normalizeTypes $ getType b

        opExp a b = case op of
                     Add -> [cexp| $a + $b |]
                     Sub -> [cexp| $a - $b |]

        compileVectorized (VecType [] aty) bty ma mb = compileVectorized aty bty ma mb
        compileVectorized aty (VecType [] bty) ma mb = compileVectorized aty bty ma mb
        compileVectorized ta@(VecType (abnd:abnds) aty) tb@(VecType (_:bbnds) bty) ma mb = comp
          where comp = Compiled
                       { withDest = \dest -> storeLoc dest loc
                       , withValue = defaultWithValue (locType loc) comp
                       , noValue = defaultNoValue (locType loc) comp
                       , asLoc = return ([], loc) }
                loc = CmLoc
                      { apIndex = \idx -> do (abl, aloc) <- ma
                                             (bbl, bloc) <- mb
                                             (bl, loc) <- asLoc $ compileVectorized
                                                          (VecType abnds aty) (VecType bbnds bty)
                                                          (apIndex aloc idx) (apIndex bloc idx)
                                             return (abl ++ bbl ++ bl, loc)
                      , asArgument = defaultAsArgument loc
                      , locType = getVectorizedType ta tb
                      , asRValue = error "Cannot get vectorized binary operation as rvalue"
                      , store = error "Cannot store into vectorized binary operation"
                      }
        compileVectorized ta@(VecType (abnd:abnds) aty) tb ma mb = comp
          where comp = Compiled
                       { withDest = \dest -> storeLoc dest loc
                       , withValue = defaultWithValue (locType loc) comp
                       , noValue = defaultNoValue (locType loc) comp
                       , asLoc = return ([], loc)
                       }
                loc = CmLoc
                      { apIndex = \idx -> do (abl, aloc) <- ma
                                             (bbl, bloc) <- mb
                                             (bl, loc) <- asLoc $ compileVectorized
                                                          (VecType abnds aty) tb
                                                          (apIndex aloc idx) (return ([], bloc))
                                             return (abl ++ bbl ++ bl, loc)
                      , asArgument = defaultAsArgument loc
                      , locType = getVectorizedType ta tb
                      , asRValue = error "Cannot get vectorized binary operation as rvalue"
                      , store = error "Cannot store into vectorized binary operation"

                      }
        compileVectorized ta tb@(VecType (bbnd:bbnds) bty) ma mb = comp
          where comp = Compiled
                       { withDest = \dest -> storeLoc dest loc
                       , withValue = defaultWithValue (locType loc) comp
                       , noValue = defaultNoValue (locType loc) comp
                       , asLoc = return ([], loc)
                       }
                loc = CmLoc
                      { apIndex = \idx -> do (abl, aloc) <- ma
                                             (bbl, bloc) <- mb
                                             (bl, loc) <- asLoc $ compileVectorized
                                                          ta (VecType bbnds bty)
                                                          (return ([], aloc)) (apIndex bloc idx)
                                             return (abl ++ bbl ++ bl, loc)
                      , asArgument = defaultAsArgument loc
                      , locType = getVectorizedType ta tb
                      , asRValue = error "Cannot get vectorized binary operation as rvalue"
                      , store = error "Cannot store into vectorized binary operation"
                      }
        compileVectorized ta tb ma mb = compPureExpr (getVectorizedType ta tb) $ do
          (abl, aloc) <- ma
          (abl', aex) <- withValue $ asRValue aloc
          (bbl, bloc) <- mb
          (bbl', bex) <- withValue $ asRValue bloc
          return (abl ++ abl' ++ bbl ++ bbl', opExp aex bex )

compileStat v@(Binary _ Mul a b) = case (aty, bty) of
  (VecType [ia, ib] aty', VecType [_, ic] bty') ->
    let comp = Compiled
               { withDest = \dest -> do (abl, aloc) <- asLoc $ compileStat a
                                        (bbl, bloc) <- asLoc $ compileStat b
                                        forbl1 <- makeFor ia $ \i -> do
                                          (abl', aloc') <- apIndex aloc i
                                          (dbl, dest') <- apIndex dest i
                                          forbl2 <- makeFor ic $ \k -> do
                                            sumname <- freshName "sum"
                                            let sumty = compileType rty
                                            forbl3 <- makeFor ib $ \j -> do
                                              (abl'', aex) <- apIndex aloc' j
                                                              `bindBl` (withValue . asRValue)
                                              (bbl', bex) <- (apIndex bloc j
                                                              `bindBl` flip apIndex k)
                                                             `bindBl` (withValue . asRValue)
                                              return (abl'' ++ bbl' ++
                                                      [[citem| $id:sumname += $aex * $bex; |]])
                                            (dbl', dest'') <- apIndex dest' k
                                            st <- storeExp dest'' [cexp| $id:sumname |]
                                            return $ dbl' ++ [[citem| $ty:sumty $id:sumname = 0; |]] ++ forbl3 ++ st
                                          return $ abl' ++ forbl2
                                        return (abl ++ bbl ++ forbl1)
               , withValue = defaultWithValue (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
    in comp
  (VecType [ia] aty', VecType [_, ib] bty') -> error "vec mat not impl"
  (VecType [ia, ib] aty', VecType [_] bty') -> error "mat vec not impl"
  (VecType [ia] aty', VecType [_] bty') ->
    let comp = Compiled
               { withValue = do (abl, aloc) <- asLoc $ compileStat a
                                (bbl, bloc) <- asLoc $ compileStat b
                                sumname <- freshName "sum"
                                let sumty = compileType rty
                                forbl <- makeFor ia $ \i -> do
                                  (abl', aex) <- apIndex aloc i `bindBl` (withValue . asRValue)
                                  (bbl', bex) <- apIndex bloc i `bindBl` (withValue . asRValue)
                                  return (abl' ++ bbl' ++
                                          [[citem| $id:sumname += $aex * $bex; |]])
                                return (abl ++ bbl ++
                                        [[citem| $ty:sumty $id:sumname = 0; |]]
                                        ++ forbl, [cexp| $id:sumname |])
               , asLoc = defaultAsLocFromWithValue (getType v) comp
               , withDest = defaultWithDest (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               }
    in comp
  (VecType {}, VecType {}) -> error "compileStat: cannot multiply arbitrary vectors"
  _ -> let comp = Compiled
                  { noValue = return []
                  , withValue =  do
                       (abl, aex) <- withValue $ compileStat a
                       (bbl, bex) <- withValue $ compileStat b
                       return (abl ++ bbl, [cexp| $aex * $bex |])
                  , asLoc = defaultAsLocFromWithValue (getType v) comp
                  , withDest = defaultWithDest (getType v) comp
                  }
       in comp
  where aty = normalizeTypes $ getType a
        bty = normalizeTypes $ getType b

        rty = case normalizeTypes $ getType v of
          VecType _ ty -> ty
          ty -> ty

compileStat v = error $ "compileStat not implemented: " ++ show v

compileLoc :: Location CExpr -> CM ([C.BlockItem], CmLoc)
compileLoc (Ref ty v) =  case normalizeTypes ty of
  VecType idxs bty -> do v <- lookupName "v" v
                         return $ ([], mkVecLoc bty [cexp| $id:v |] idxs)
  _ -> do v' <- lookupName "v" v
          return $ ([], refLoc ty v')

compileLoc loc@(Index a idxs) = do (abl, aloc) <- asLoc $ compileStat a
                                   cidxs' <- mapM mkIndex idxs
                                   let idxbl = concat $ map fst cidxs'
                                       ty = normalizeTypes $ getLocType loc
                                   (abl', aloc') <- mkLoc ty aloc (map snd cidxs')
                                   return (abl ++ idxbl ++ abl', aloc')
  where mkIndex :: CExpr -> CM ([C.BlockItem], Either (Int, CmLoc) C.Exp) -- TODO tuple
        mkIndex idx = case normalizeTypes (getType idx) of
          VecType ibnds ibty -> do
            (idxbl, idxloc) <- asLoc $ compileStat idx
            return $ (idxbl, Left (length ibnds, idxloc))
          ty -> do
            (idxbl, idxex) <- withValue $ compileStat idx
            return $ (idxbl, Right idxex)

        mkLoc :: Type -> CmLoc -> [Either (Int, CmLoc) C.Exp] -> CM ([C.BlockItem], CmLoc)
        mkLoc _ aloc [] = return ([], aloc)
        mkLoc ty aloc ((Right exp):idxs) = do (bl', aloc') <- apIndex aloc exp
                                              (bl'', aloc'') <- mkLoc ty aloc' idxs
                                              return (bl' ++ bl'', aloc'')
        mkLoc ty aloc ((Left (n, iloc)):idxs) = deferLoc ty iloc n $ \iloc' -> do
          (ilocbl, ilocex) <- withValue $ asRValue iloc'
          (abl', aloc') <- apIndex aloc ilocex -- TODO tuples
          (bl'', aloc'') <- mkLoc (strip n ty) aloc' idxs
          return (ilocbl ++ abl' ++ bl'', aloc'')

        strip :: Int -> Type -> Type
        strip 0 ty = ty
        strip n (VecType (bnd:bnds) bty) = strip (n - 1) (VecType bnds bty)
