{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE PatternSynonyms #-}

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
import Control.Applicative ((<$>), (<*>))
import qualified Data.Map as M

import Language.Plover.Types hiding (freshName)

import Data.Loc (SrcLoc(SrcLoc), Loc(NoLoc))

--import qualified Language.Plover.CodeGenMonad

import Debug.Trace
strace :: Show a => a -> a
strace x = trace ("@@@ " ++ show x) x


data CodeGenState = CodeGenState
                    { bindings :: M.Map String String
                    , usedNames :: [String]
                    , genCode :: [C.BlockItem]
                    }
                    deriving Show


type CM a = State CodeGenState a

-- | Returns the output header file and the output source file.
doCompile :: [DefBinding] -> (String, String)
doCompile defs = runCM $ do (header, code) <- compileTopLevel defs
                            return (show $ ppr header, show $ ppr code)

runCM :: CM a -> a
runCM m = evalState m (CodeGenState M.empty [] [])

writeCode :: [C.BlockItem] -> CM ()
writeCode code = modify $ \state -> state { genCode = genCode state ++ code }

withCode :: CM a -> CM ([C.BlockItem], a)
withCode m = do code <- genCode <$> get
                modify $ \state -> state { genCode = [] }
                x <- m
                code' <- genCode <$> get
                modify $ \state -> state { genCode = code }
                return (code', x)

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

compileTopLevel :: [DefBinding] -> CM ([C.Definition], [C.Definition])
compileTopLevel defbs = do let defbs' = filter (not . extern) defbs
                           forM_ defbs' $ \defb ->
                             lookupName (error "Invalid top-level name") (binding defb)
                           decls <- fmap concat $ forM (filter (not . static) defbs') $ \defb ->
                                    newScope $ case definition defb of
                                                 FunctionDef mexp ft -> compileFunctionDecl (binding defb) ft
                                                 _ -> return []
                           declstatic <- fmap concat $ forM (filter static defbs') $ \defb ->
                                         newScope $ case definition defb of
                                                      FunctionDef mexp ft -> compileFunctionDecl (binding defb) ft
                                                      _ -> return []
                           ddef <- fmap concat $ forM defbs' $ \defb -> newScope $ case definition defb of
                             FunctionDef (Just body) ft -> compileFunction (binding defb) ft body
                             _ -> return []
                           return (ext_includes ++ decls, int_includes ++ declstatic ++ ddef)
  where ext_includes = [cunit| $esc:("#include \"common.h\"") |]
        int_includes = [cunit| $esc:("#include <math.h>")
                               $esc:("#include <stdio.h>")
                               $esc:("#include \"linear_algebra.h\"") |]

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
        args' = [(v, dir, ty) | (v, _, dir, ty) <- args, nonVoid ty]

compileFunction :: String -> FunctionType -> CExpr -> CM [C.Definition]
compileFunction name ft exp = do
  args'' <- compileParams args'
  (blks,_) <- withCode $ case mret of
    Just (v, retty') -> do v' <- lookupName "arg" v
                           let dest = case normalizeTypes retty' of
                                       VecType st bnds retty'' -> mkVecLoc retty'' [cexp| $id:(v') |] bnds
                                       retty'' -> refLoc retty'' v'
                           withDest (compileStat exp) dest
    Nothing ->  case retty of
                  Void -> noValue $ compileStat exp
                  _ -> do expex <- asExp $ compileStat exp
                          writeCode [citems| return $expex; |]
  return $ case args'' of
    [] -> [ [cedecl| $ty:(compileType retty) $id:(name)(void) { $items:blks } |] ]
    _ ->  [ [cedecl| $ty:(compileType retty) $id:(name)($params:(args'')) { $items:blks } |] ]
  where (FnT args retty, mret) = getEffectiveFunType ft
        nonVoid ty = case ty of
                      Void -> False
                      _ -> True
        args' = [(v, dir, ty) | (v, _, dir, ty) <- args, nonVoid ty]


compileParams :: [(Variable, ArgDir, Type)] -> CM [C.Param]
compileParams = mapM compileParam

compileParam :: (Variable, ArgDir, Type) -> CM C.Param
compileParam (v, dir, ty) = do v' <- lookupName "arg" v
                               case dir of -- TODO figure out how to document directions.
                                ArgIn -> return [cparam| const $ty:(compileType ty) $id:(v') |]
                                ArgOut -> return [cparam| $ty:(compileType ty) $id:(v') |]
                                ArgInOut -> return [cparam| $ty:(compileType ty) $id:(v') |]

compileType :: Type -> C.Type
compileType = compileType' . normalizeTypes

compileType' :: Type -> C.Type
compileType' (VecType _ _ ty) = [cty|$ty:(compileType ty)*|] -- make sure type is normalized
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
compileType' (TypedefType v) = [cty|typename $id:v|]
compileType' (StructType v _) = [cty|typename $id:v|]
compileType' (TypeHole _) = error "No type holes allowed."

-- When initializing a variable, need things like the length of the
-- array rather than just a pointer
compileInitType :: Type -> CM C.Type
compileInitType ty = compileInitType' (normalizeTypes ty)

compileInitType' :: Type -> CM C.Type
compileInitType' (VecType _ idxs base) = do sizeex <- asExp $ compileStat (foldr1 (*) idxs)
                                            basety <- compileInitType base
                                            return [cty|$ty:basety[$sizeex] |]
compileInitType' t = return $ compileType t

data Compiled = Compiled { noValue :: CM ()
                         , withDest :: CmLoc -> CM ()
                         , asExp :: CM C.Exp
                         , asLoc :: CM CmLoc
                         }

-- withValue :: Compiled -> CM ([C.BlockItem], C.Exp)
-- withValue com = do (prep, loc) <- asLoc com
--                    (bl, exp) <- asRValue loc
--                    return (prep ++ bl, exp)

data CmLoc = CmLoc { apIndex :: C.Exp -> CM CmLoc
                     -- ^ apply an index to a vector location
                   , store :: C.Exp -> CM ()
                     -- ^ store an expression if this is a simple (i.e, non-vector) location
                   , asRValue :: Compiled
                     -- ^ get the compiled simple (i.e., non-vector) expression
                   , asArgument :: CM ([C.BlockItem], C.Exp, [C.BlockItem])
                     -- ^ get a representation of the location (of any
                     -- type) which can be passed as an argument to a
                     -- function.  The first is setup for an In
                     -- variable, the second is the expression to
                     -- pass, and the third is for an Out variable.
                   , locType :: Type
                     -- ^ gets the type of this location. Every type
                     -- should know its location, and this helps for
                     -- generating store code
                   }


-- | makes a location based on an expression
expLoc :: Type -> CM C.Exp -> CmLoc
expLoc ty mexp =
    CmLoc
    { apIndex = \idx -> case normalizeTypes ty of
                          VecType _ bnds baseTy -> do exp <- mexp
                                                      apIndex (mkVecLoc baseTy exp bnds) idx
                          _ -> error "Cannot apIndex simple expLoc"
    , store = \v -> do exp <- mexp
                       case normalizeTypes ty of
                         VecType _ bnds baseTy -> error "Cannot simple store into vector expLoc"
                         _ -> writeCode [citems| $exp = $v; |]
    , asRValue = compPureExpr ty mexp -- not correct for vector, but shouldn't be used anyway
    , asArgument = do exp <- mexp
                      return ([], exp, [])
    , locType = ty
    }

-- | takes a C identifier and makes a simple-valued location
refLoc :: Type -> String -> CmLoc
refLoc ty v = expLoc ty (return [cexp| $id:v |])

-- | generates a fresh location using freshName
freshLoc :: String -> Type -> CM CmLoc
freshLoc v ty = do v' <- freshName v
                   makeLoc v' ty

-- | generates a stack location using the C identifier
makeLoc :: String -> Type -> CM CmLoc
makeLoc v ty = case normalizeTypes ty of
  VecType _ idxs bty -> do vty <- compileInitType ty
                           writeCode [citems| $ty:vty $id:v; |]
                           return $ mkVecLoc bty [cexp| $id:v |] idxs
  _ -> do vty <- compileInitType ty
          writeCode [citems| $ty:vty $id:v; |]
          return $ refLoc ty v

-- | Type is normalized type of vector.  Creates a vector based on
-- using C indexing of the expression, assuming the expression is
-- stored linearly in memory.
mkVecLoc :: Type -> C.Exp -> [CExpr] -> CmLoc
mkVecLoc baseTy vec bnds = mkVecLoc' [] bnds
  where mkVecLoc' :: [(C.Exp, CExpr)] -> [CExpr] -> CmLoc
        mkVecLoc' acc [] = CmLoc {
          apIndex = error "All indices already applied."
          , store = \exp -> do idxc <- collapseIdx idx idxs bnds
                               writeCode [citems| $vec[$idxc] = $exp; |]
          , asRValue = compImpureExpr baseTy $
                       do idxc <- collapseIdx idx idxs bnds
                          return [cexp| $vec[$idxc] |]
          , asArgument = do idxc <- collapseIdx idx idxs bnds
                            return ([], [cexp| $vec[$idxc] |], [])
          , locType = baseTy
          }
          where (idx:idxs, _:bnds) = unzip acc
        mkVecLoc' acc (bnd:bnds) = CmLoc {
          apIndex = \idx -> return $ mkVecLoc' (acc ++ [(idx, bnd)]) bnds
          , store = error "Cannot do simple store into vector"
          , asRValue = error "Cannot get vector as rvalue" -- compPureExpr (VecType (bnd:bnds) baseTy) $ return ([], vec) -- TODO ?
          , asArgument = case acc of
              [] -> return ([], vec, [])
              _ -> do let (idx:idxs, bnds') = unzip (acc ++ zip (repeat [cexp|0|]) (bnd:bnds))
                      idxc <- collapseIdx idx idxs bnds'
                      return ([], [cexp| $vec + $idxc |], [])
          , locType = VecType DenseMatrix (bnd:bnds) baseTy
        }

        collapseIdx :: C.Exp -> [C.Exp] -> [CExpr] -> CM C.Exp
        collapseIdx accidx [] _ = return accidx
        collapseIdx accidx (idx:idxs) (bnd:bnds) = do bndex <- asExp $ compileStat bnd
                                                      collapseIdx [cexp| $bndex * $accidx + $idx |]
                                                                  idxs bnds

-- | Creates a location which lets indices be applied on a given
-- location a fixed number of times before handing the location to a
-- function. TODO choose a better name
deferLoc :: Type -> CmLoc -> Int -> (CmLoc -> CM CmLoc)
            -> CM CmLoc
deferLoc ty loc 0 f = f loc
deferLoc ty loc n f = return dloc
  where dloc = CmLoc
               { apIndex = \idx -> do loc' <- apIndex loc idx
                                      dloc' <- deferLoc ty' loc' (n - 1) f
                                      return dloc'
               , store = error $ "Cannot simple store into deferLoc"
               , asRValue = error "Cannot get deferLoc asRValue" -- comp
               , asArgument = defaultAsArgument dloc
               , locType = ty
               }
        -- comp = Compiled
        --        { withDest = \dest -> storeLoc dest dloc
        --        , withValue = defaultWithValue ty comp
        --        , noValue = defaultNoValue ty comp
        --        , asLoc = return ([], dloc)
        --        }

        VecType _ (bnd:bnds) bty = normalizeTypes ty
        ty' = VecType DenseMatrix bnds bty

-- | Lifts a location of x to a location of type (VecType
-- [a_1,\dots,a_n] x) by ignoring indexes.
liftLoc :: Type -> CmLoc -> [CExpr] -> CmLoc
liftLoc ty loc [] = loc
liftLoc ty loc (bnd:bnds) = lloc
    where lloc = CmLoc
                 { apIndex = \idx -> return $ liftLoc ty loc bnds
                 , store = error "Cannot store into liftLoc"
                 , asRValue = error "Cannot get liftLoc asRValue"
                 , asArgument = defaultAsArgument lloc
                 , locType = VecType DenseMatrix (bnd:bnds) ty
                 }

-- | Creates a loc which is inside another loc at an offset.
offsetLoc :: Type -> CmLoc -> C.Exp -> CmLoc
offsetLoc ty loc offset = oloc
    where oloc = CmLoc
                 { apIndex = \idx -> apIndex loc [cexp| $offset + $idx |]
                 , store = error "Cannot store into offsetLoc"
                 , asRValue = error "Cannot get offsetLoc asRValue"
                 , asArgument = defaultAsArgument oloc
                 , locType = ty
                 }

-- | uses asExp, executing exp as a statement.
defaultNoValue :: Type -> Compiled -> CM ()
defaultNoValue ty comp = do exp <- asExp comp
                            writeCode [citems| $exp; |]

-- | uses asExp
defaultWithDest :: Type -> Compiled -> (CmLoc -> CM ())
defaultWithDest ty comp loc = do exp <- asExp comp
                                 storeExp loc exp


-- | uses withDest
defaultAsExp :: Type -> Compiled -> CM C.Exp
defaultAsExp ty comp = do loc <- freshLoc "tmp" ty
                          withDest comp loc
                          (bl,vex,_) <- asArgument loc
                          writeCode bl
                          return vex

-- | uses withDest
defaultAsLoc :: Type -> Compiled -> CM CmLoc
defaultAsLoc ty comp = do loc <- freshLoc "loc" ty
                          withDest comp loc
                          return loc

-- | uses asExp
defaultAsLocFromAsExp :: Type -> Compiled -> CM CmLoc
defaultAsLocFromAsExp ty comp = do exp <- asExp comp
                                   return $ expLoc ty (return exp)

-- | uses asRValue and apIndex.  Just spills the thing into a new
-- location.
defaultAsArgument :: CmLoc -> CM ([C.BlockItem], C.Exp, [C.BlockItem])
defaultAsArgument loc = do floc <- freshLoc "arg" (locType loc)
                           (stbef,_) <- withCode $ storeLoc floc loc
                           (staft,_) <- withCode $ storeLoc loc floc
                           (bef, exp, aft) <- asArgument floc
                           return (stbef ++ bef, exp, aft ++ staft)

defaultAsArgumentNoOut :: CmLoc -> CM ([C.BlockItem], C.Exp, [C.BlockItem])
defaultAsArgumentNoOut loc = do floc <- freshLoc "arg" (locType loc)
                                (stbef,_) <- withCode $ storeLoc floc loc
                                (bef, exp, _) <- asArgument floc
                                return (stbef ++ bef, exp, [])

spillLoc :: CmLoc -> CM CmLoc
spillLoc loc = do (bef, exp, _) <- asArgument loc
                  writeCode bef
                  return $ expLoc (locType loc) (return exp)

storeExp :: CmLoc -> C.Exp -> CM ()
storeExp dst exp = case normalizeTypes (locType dst) of
  VecType _ idxs bty -> storeLoc dst (mkVecLoc bty exp idxs)
  _ -> store dst exp

storeLoc :: CmLoc -> CmLoc -> CM ()
storeLoc dst src = case normalizeTypes (locType dst) of
  VecType _ (idx:idxs) bty -> makeFor idx $ \i -> do
    dst' <- apIndex dst i
    src' <- apIndex src i
    storeLoc dst' src'
  _ -> withDest (asRValue src) dst -- or (asExp $ asRValue src) >>= store dst

makeFor :: CExpr -> (C.Exp -> CM ()) -> CM ()
makeFor idx mbody = do boundEx <- asExp $ compileStat idx
                       (body, i) <- withCode $ newScope $ do
                                      i <- freshName "idx"
                                      mbody [cexp| $id:i |]
                                      return i
                       writeCode [citems| for ($ty:itty $id:i = 0; $id:i < $boundEx; $id:i++) { $items:body } |]
    where itty = compileType $ getType idx

-- | an expression with no side effects does not need to be computed
-- if no result is needed.
compPureExpr :: Type -> CM C.Exp -> Compiled
compPureExpr ty mexpr = comp
  where comp = Compiled
               { noValue = void mexpr
               , withDest = defaultWithDest ty comp
               , asExp = mexpr
               , asLoc = do expr <- mexpr
                            return $ expLoc ty (return expr)
               }

-- | an expression with side effects does need to be computed even if
-- no result is needed.
compImpureExpr :: Type -> CM C.Exp -> Compiled
compImpureExpr ty mexpr = comp
  where comp = Compiled
               { noValue = defaultNoValue ty comp
               , withDest = defaultWithDest ty comp
               , asExp = mexpr
               , asLoc = defaultAsLoc ty comp
               }

defaultAsRValue :: Type -> CM CmLoc -> Compiled
defaultAsRValue ty mloc = comp
  where comp = Compiled
               { noValue = mloc >>= noValue . asRValue
               , withDest = \dest -> mloc >>= storeLoc dest
               , asExp = mloc >>= asExp . asRValue
               , asLoc = mloc
               }

-- testCompileExpr :: CExpr -> String
-- testCompileExpr exp = let (blks, v) = evalState (withCode $ withValue $ compileStat exp) (CodeGenState M.empty [] [])
--                           item = if null blks
--                                  then [citem| { return $v; } |]
--                                  else [citem| { $items:blks return $v; } |]
--                       in show $ ppr item


compileStat :: CExpr -> Compiled

compileStat e@(Vec pos v range@(Range cstart cend cstep) exp) = comp
  where comp = Compiled -- TODO consider compiling range object as loc and indexing it
               { noValue = return ()
               , withDest = \dest -> do start <- asExp $ compileStat cstart
                                        len <- asExp $ compileStat $ rangeLength pos range
                                        step <- asExp $ compileStat cstep
                                        (body,(i,j)) <- withCode $ newScope $ do
                                                      i <- newName "i" v
                                                      j <- freshName "idx"
                                                      dest' <- apIndex dest [cexp| $id:j |]
                                                      withDest (compileStat exp) dest'
                                                      return (i,j)
                                        writeCode [citems| for($ty:itty $id:i = $start, $id:j=0; $id:j < $len; $id:i += $step, $id:j++) { $items:body } |]
               , asExp = defaultAsExp ty comp
               , asLoc = defaultAsLoc ty comp
               }
        ty = normalizeTypes $ getType e
        itty = compileType $ getType $ rangeLength pos range

compileStat (For pos v range@(Range cstart cend cstep) exp) = comp
  where comp = Compiled
               { noValue = do start <- asExp $ compileStat cstart
                              len <- asExp $ compileStat $ rangeLength pos range
                              step <- asExp $ compileStat cstep
                              (body, (i, j)) <- withCode $ newScope $ do
                                            i <- newName "i" v
                                            j <- freshName "idx"
                                            noValue $ compileStat exp
                                            return (i, j)
                              writeCode [citems| for($ty:itty $id:i = $start, $id:j = 0; $id:j < $len; $id:i += $step, $id:j++) { $items:body } |]
               , asExp = error "Cannot get For as expression"
               , withDest = error "Cannot use For as dest"
               , asLoc = error "Cannot use For as location"
               }
        itty = compileType $ getType $ rangeLength pos range

compileStat exp@(RangeVal _ range) = comp
  where comp = Compiled
               { noValue = defaultNoValue ty comp
               , withDest = \dest -> do loc <- asLoc comp
                                        storeLoc dest loc
               , asExp = defaultAsExp ty comp
               , asLoc = return loc
               }
        ty@(VecType _ _ bty) = normalizeTypes $ getType exp

        loc = CmLoc
              { apIndex = \idx -> do exp <- rngExp idx
                                     return $ expLoc bty (return exp)
              , store = error "Cannot store into rangeval"
              , asRValue = error "cannot asRValue rangeval"
              , asArgument = do ex <- asExp comp
                                return ([], ex, [])
              , locType = ty
              }

        rngExp idx = case range of
          Range (IntLit _ _ 0) end (IntLit _ _ 1) -> return idx
          Range start end (IntLit _ _ 1) -> do stex <- asExp $ compileStat start
                                               return [cexp| $stex + $idx |]
          Range (IntLit _ _ 0) end step -> do stepex <- asExp $ compileStat step
                                              return [cexp| $stepex * $idx |]
          Range start end step -> do stex <- asExp $ compileStat start
                                     stepex <- asExp $ compileStat step
                                     return [cexp| $stex + $idx * $stepex |]


compileStat (If _ a b c) = comp
  where comp = Compiled
               { noValue = do aexp <- asExp $ compileStat a
                              (bbl,_) <- withCode $ newScope $ noValue $ compileStat b
                              (cbl,_) <- withCode $ newScope $ noValue $ compileStat c
                              mkIf aexp bbl cbl
               , withDest = \loc -> do aexp <- asExp $ compileStat a
                                       (bbl,_) <- withCode $ newScope $ withDest (compileStat b) loc
                                       (cbl,_) <- withCode $ newScope $ withDest (compileStat c) loc
                                       mkIf aexp bbl cbl
               , asExp = defaultAsExp (getType b) comp
               , asLoc = defaultAsLoc (getType b) comp
               }
        mkIf aexp bbl cbl = writeCode [citems| if ($aexp) { $items:bbl } else { $items:cbl } |]

compileStat (VoidExpr _) = Compiled { noValue = return ()
                                    , withDest = \v -> error "Cannot store VoidExpr"
                                    , asExp = return $ error "Cannot get VoidExpr"
                                    , asLoc = return $ error "Cannot get VoidExpr"
                                    }
compileStat x@(IntLit _ _ v) = compPureExpr (getType x) $ return [cexp| $int:v |] -- TODO consider type
compileStat x@(FloatLit _ _ v) = compPureExpr (getType x) $ return [cexp| $double:(toRational v) |] -- TODO consider type
compileStat (StrLit _ s) = compPureExpr StringType $ return [cexp| $string:s |]
compileStat (BoolLit _ b) = compPureExpr BoolType $ return [cexp| $id:lit |]
  where lit :: String
        lit = if b then "true" else "false"

compileStat v@(VecLit pos ty xs) = comp
  where comp = Compiled
               { noValue = defaultNoValue vty comp
               , withDest = \dest -> forM_ (zip [0..] xs) $ \(i,x) -> do
                    xdst <- apIndex dest [cexp| $int:i |]
                    withDest (compileStat x) xdst
               , asExp = defaultAsExp vty comp
               , asLoc = defaultAsLoc vty comp
               }
        vty = normalizeTypes $ getType v

compileStat (Let _ v val x) = comp
  where comp = Compiled
               { withDest = \dest -> makeLet $ withDest (compileStat x) dest
               , noValue = makeLet $ noValue $ compileStat x
               , asExp = makeLet $ asExp $ compileStat x
               , asLoc = defaultAsLoc xty comp
               }
        xty = normalizeTypes $ getType x
        makeLet m =
            mdo vloc <- makeLoc v' (getType val)
                case val of
                  Uninitialized {} -> return()
                  _ -> withDest (compileStat val) vloc
                (v',x) <- newBlocklessScope $ do
                            v' <- newName "let" v
                            x <- m
                            return (v',x)
                return x

-- -- skipping Uninitialized

compileStat (Seq _ a b) = comp
  where comp = Compiled
               { noValue = do noValue $ compileStat a
                              noValue $ compileStat b
               , withDest = \loc -> do noValue $ compileStat a
                                       withDest (compileStat b) loc
               , asExp = do noValue $ compileStat a
                            asExp $ compileStat b
               , asLoc = do noValue $ compileStat a
                            asLoc $ compileStat b
               }

compileStat (ConcreteApp pos (Get _ (Ref (FnType ft) f)) args) = comp
  where (FnT params retty, mret) = getEffectiveFunType ft
        dirs = map (\(_,_,dir,_) -> dir) params

        -- Compiled forms for the arguments
        margs' :: CM [([C.BlockItem],C.Exp,[C.BlockItem])]
        margs' = forM args $ \a -> (asLoc $ compileStat a) >>= asArgument
        -- if the result is complex, the compiled arguments along with the destination
        margs'' dest = do args' <- margs'
                          (b,e,a) <- asArgument $ dest
                          return $ args' ++ [(b,e,a)] -- TODO tuple dest

        comp = case mret of
                Just (_, retty') -> Compiled
                                    { withDest = \dest -> do args' <- margs'' dest
                                                             let dargs = zip (dirs ++ [ArgOut]) args'
                                                                 (bbl, fexp, bbl') = theCall f dargs
                                                             writeCode bbl
                                                             writeCode [citems| $fexp; |]
                                                             writeCode bbl'
                                    , asExp = defaultAsExp retty' comp
                                    , noValue = defaultNoValue retty' comp
                                    , asLoc = defaultAsLoc retty' comp
                                    }
                Nothing -> Compiled
                           { asExp = do dargs <- (zip dirs) <$> margs'
                                        let (bbl, fexp, bbl') = theCall f dargs
                                        writeCode bbl
                                        case bbl' of
                                          [] -> return fexp
                                          _ -> do loc <- freshLoc "ret" retty
                                                  storeExp loc fexp
                                                  writeCode bbl'
                                                  (reta, retex, _) <- asArgument loc
                                                  writeCode reta
                                                  return retex
                           , withDest = \dest -> do dargs <- (zip dirs) <$> margs'
                                                    let (bbl, fexp, bbl') = theCall f dargs
                                                    writeCode bbl
                                                    stbl <- storeExp dest fexp
                                                    writeCode bbl'
                           , noValue = do dargs <- (zip dirs) <$> margs'
                                          let (bbl, fexp, bbl') = theCall f dargs
                                          writeCode bbl
                                          writeCode [citems| $fexp; |]
                                          writeCode bbl'
                           , asLoc = defaultAsLocFromAsExp retty comp
                           }

        -- | Returns what to do before the call, the argument, and what to do after the call
        theCall :: String -> [(ArgDir, ([C.BlockItem], C.Exp, [C.BlockItem]))] -> ([C.BlockItem], C.Exp, [C.BlockItem])
        theCall f args = (before, [cexp| $id:f($args:(exps)) |], after)
            where before = concat $ flip map args $ \(dir, (bef, argex, aft)) -> case dir of
                                                                                   ArgIn -> bef
                                                                                   ArgOut -> []
                                                                                   ArgInOut -> bef
                  exps = map (\(dir, (bef, argex, aft)) -> argex) args
                  after = concat $ flip map args $ \(dir, (bef, argex, aft)) -> case dir of
                                                                                  ArgIn -> []
                                                                                  ArgOut -> aft
                                                                                  ArgInOut -> aft

compileStat (Hole {}) = error "No holes allowed"

compileStat (Get pos (Index a [])) = compileStat a
compileStat v@(Get pos loc) = defaultAsRValue (getType v) (compileLoc loc)

compileStat v@(Addr pos loc) = comp
  where comp = Compiled
               { asExp = do (bef, exp, _) <- compileLoc loc >>= asArgument
                            writeCode bef
                            return [cexp| & $exp |]
               , noValue = defaultNoValue (getType v) comp
               , withDest = defaultWithDest (getType v) comp
               , asLoc = do ex <- asExp $ comp
                            return $ expLoc (getType v) (return ex)
               }

compileStat (Set pos loc v) = comp
  where comp = Compiled
               { noValue = do loc <- compileLoc loc
                              withDest (compileStat v) loc
               , withDest = \dst -> noValue comp -- Shouldn't happen, but just in case...
               , asExp = do noValue comp
                            return $ error "Cannot get Set as value."
               , asLoc = error "Set is not a location"
               }

compileStat (AssertType pos a ty) = compileStat a

-- -- unary

compileStat v@(Unary _ op a)
  | op `elem` [Neg] = compileVectorized' aty (asLoc $ compileStat a)
  where aty = normalizeTypes $ getType a

        opExp :: C.Exp -> C.Exp
        opExp a = case op of
                   Neg -> [cexp| -$a |]

        compileVectorized' aty ma = comp
            where comp = Compiled
                         { withDest = \dest -> mloc' >>= flip withDest dest
                         , asExp = mloc' >>= asExp
                         , noValue = mloc' >>= noValue
                         , asLoc = mloc' >>= asLoc
                         }
                  mloc' = compileVectorized aty <$> ma

        compileVectorized :: Type -> CmLoc -> Compiled
        compileVectorized (VecType _ [] aty) aloc = compileVectorized aty aloc
        compileVectorized ta@(VecType _ (abnd:abnds) aty) aloc = comp
          where comp = Compiled
                       { withDest = \dest -> storeLoc dest loc
                       , asExp = defaultAsExp (locType loc) comp
                       , noValue = defaultNoValue (locType loc) comp
                       , asLoc = return loc }
                loc = CmLoc
                      { apIndex = \idx -> do aloc' <- apIndex aloc idx
                                             asLoc $ compileVectorized
                                                       (VecType DenseMatrix abnds aty)
                                                       aloc'
                      , asArgument = defaultAsArgumentNoOut loc
                      , locType = getVectorizedType ta ta
                      , asRValue = error "Cannot get vectorized unary operation as rvalue"
                      , store = error "Cannot store into vectorized unary operation"
                      }
        compileVectorized ta aloc = compPureExpr (getVectorizedType ta ta) $ opExp <$> (asExp $ asRValue aloc)

compileStat v@(Unary _ Inverse a) = comp
  where comp = Compiled
               { withDest = \dest -> do aloc <- asLoc $ compileStat a
                                        (bl, aex, _) <- asArgument aloc
                                        (_, dex, daf) <- asArgument dest
                                        nex <- asExp $ compileStat n
                                        writeCode bl
                                        writeCode [citems|matrix_inverse($nex,$aex,$dex);|]
                                        writeCode daf
               , asExp = defaultAsExp (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
        VecType _ [n,_] bty = normalizeTypes $ getType a

compileStat v@(Unary _ Transpose a) = comp
  where comp = Compiled
               { withDest = \dest -> do aloc <- asLoc $ compileStat a
                                        case normalizeTypes $ getType a of
                                          VecType _ [_] _ -> do -- then dest is 1 x n and a is a 1-d vector
                                            dest' <- apIndex dest [cexp| 0 |]
                                            makeFor i2 $ \i -> do aloc' <- apIndex aloc i
                                                                  dest'' <- apIndex dest' i
                                                                  storeLoc dest'' aloc'
                                          _ -> makeFor i2 $ \i -> -- then both are (at least) two-dimensional
                                               do aloc' <- apIndex aloc i -- we reverse indices since better to do row-normal (?)
                                                  makeFor i1 $ \j ->
                                                      do aloc'' <- apIndex aloc' j
                                                         dest'' <- apIndex dest i >>= flip apIndex j
                                                         storeLoc dest'' aloc''
               , asExp = defaultAsExp (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = return loc
               }
        loc = CmLoc -- Defer application of the indices so we may swap them.
              { apIndex = \idx1 -> do aloc <- asLoc $ compileStat a
                                      return $ loc' aloc idx1
              , asArgument = defaultAsArgumentNoOut loc
              , locType = VecType DenseMatrix (i1:i2:idxs) aty'
              , asRValue = error "Cannot get transpose as rvalue"
              , store = error "Cannot store (yet) into transpose"
              }
        loc' aloc idx1 = CmLoc
                         { apIndex = \idx2 -> case normalizeTypes $ getType a of
                                                VecType _ [_] _ -> apIndex aloc idx2
                                                _ -> apIndex aloc idx2 >>= flip apIndex idx1
                         , asArgument = defaultAsArgumentNoOut loc
                         , locType = VecType DenseMatrix (i2:idxs) aty'
                         , asRValue = error "Cannot get transpose as rvalue"
                         , store = error "Cannot store (yet) into transpose"
                         }
        VecType _ (i1:i2:idxs) aty' = normalizeTypes $ getType v -- N.B. this will have i1=1 if v is a 1-d vector.

-- -- binary

compileStat v@(Binary _ op a b)
  | op `elem` [Add, Sub, Div] = compileVectorized' aty bty (asLoc (compileStat a)) (asLoc (compileStat b))
  where aty = normalizeTypes $ getType a
        bty = normalizeTypes $ getType b

        opExp a b = case op of
                     Add -> [cexp| $a + $b |]
                     Sub -> [cexp| $a - $b |]
                     Div -> [cexp| $a / $b |]

        compileVectorized' aty bty ma mb = comp
            where comp = Compiled
                         { withDest = \dest -> mloc' >>= flip withDest dest
                         , asExp = mloc' >>= asExp
                         , noValue = mloc' >>= noValue
                         , asLoc = mloc' >>= asLoc
                         }
                  mloc' = compileVectorized aty bty <$> ma <*> mb

        compileVectorized (VecType _ [] aty) bty aloc bloc = compileVectorized aty bty aloc bloc
        compileVectorized aty (VecType _ [] bty) aloc bloc = compileVectorized aty bty aloc bloc
        compileVectorized ta@(VecType _ (abnd:abnds) aty) tb@(VecType _ (_:bbnds) bty) aloc bloc = comp
          where comp = Compiled
                       { withDest = \dest -> storeLoc dest loc
                       , asExp = defaultAsExp (locType loc) comp
                       , noValue = defaultNoValue (locType loc) comp
                       , asLoc = return loc }
                loc = CmLoc
                      { apIndex = \idx -> do aloc' <- apIndex aloc idx
                                             bloc' <- apIndex bloc idx
                                             asLoc $ compileVectorized
                                                    (VecType DenseMatrix abnds aty) (VecType DenseMatrix bbnds bty)
                                                    aloc' bloc'
                      , asArgument = defaultAsArgumentNoOut loc
                      , locType = getVectorizedType ta tb
                      , asRValue = error "Cannot get vectorized binary operation as rvalue"
                      , store = error "Cannot store into vectorized binary operation"
                      }
        compileVectorized ta@(VecType _ (abnd:abnds) aty) tb aloc bloc = comp -- then tb is lower dimensional
          where comp = Compiled
                       { withDest = \dest -> storeLoc dest loc
                       , asExp = defaultAsExp (locType loc) comp
                       , noValue = defaultNoValue (locType loc) comp
                       , asLoc = return loc
                       }
                loc = CmLoc
                      { apIndex = \idx -> do aloc' <- apIndex aloc idx
                                             asLoc $ compileVectorized
                                                       (VecType DenseMatrix abnds aty) tb
                                                       aloc' bloc
                      , asArgument = defaultAsArgumentNoOut loc
                      , locType = getVectorizedType ta tb
                      , asRValue = error "Cannot get vectorized binary operation as rvalue"
                      , store = error "Cannot store into vectorized binary operation"

                      }
        compileVectorized ta tb@(VecType _ (bbnd:bbnds) bty) aloc bloc = comp -- then ta is lower dimensional
          where comp = Compiled
                       { withDest = \dest -> storeLoc dest loc
                       , asExp = defaultAsExp (locType loc) comp
                       , noValue = defaultNoValue (locType loc) comp
                       , asLoc = return loc
                       }
                loc = CmLoc
                      { apIndex = \idx -> do bloc' <- apIndex bloc idx
                                             asLoc $ compileVectorized
                                                       ta (VecType DenseMatrix bbnds bty)
                                                       aloc bloc'
                      , asArgument = defaultAsArgumentNoOut loc
                      , locType = getVectorizedType ta tb
                      , asRValue = error "Cannot get vectorized binary operation as rvalue"
                      , store = error "Cannot store into vectorized binary operation"
                      }
        compileVectorized ta tb aloc bloc = compPureExpr (getVectorizedType ta tb)
                                            $ opExp <$> (asExp $ asRValue aloc) <*> (asExp $ asRValue bloc)

compileStat v@(Binary _ Mul a b) = case (aty, bty) of
  (VecType _ [ia, ib] aty', VecType _ [_, ic] bty') ->
    let comp = Compiled
               { withDest = \dest -> do aloc <- asLoc $ compileStat a
                                        bloc <- asLoc $ compileStat b
                                        makeFor ia $ \i -> do
                                          aloc' <- apIndex aloc i
                                          dest' <- apIndex dest i
                                          makeFor ic $ \k -> do
                                            sumname <- freshName "sum"
                                            writeCode [citems| $ty:sumty $id:sumname = 0; |]
                                            makeFor ib $ \j -> do
                                              aex <- apIndex aloc' j >>= asExp . asRValue
                                              bex <- apIndex bloc j >>= flip apIndex k >>= asExp . asRValue
                                              writeCode [citems| $id:sumname += $aex * $bex; |]
                                            dest'' <- apIndex dest' k
                                            store dest'' [cexp| $id:sumname |]
               , asExp = defaultAsExp (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
    in comp
  (VecType _ [ia] aty', VecType _ [_, ib] bty') -> -- left vector is (ia x 1) matrix, so right is (1 x ib) row vector (outer product)
    let comp = Compiled
               { withDest = \dest -> do aloc <- asLoc $ compileStat a
                                        bloc <- (asLoc $ compileStat b) >>= flip apIndex [cexp| 0 |]
                                        makeFor ia $ \i -> do
                                          aex <- apIndex aloc i >>= asExp . asRValue
                                          dest' <- apIndex dest i
                                          makeFor ib $ \j -> do
                                            bex <- apIndex bloc j >>= asExp . asRValue
                                            dest'' <- apIndex dest' j
                                            store dest'' [cexp| $aex * $bex |]
               , asExp = defaultAsExp (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
    in comp
  (VecType _ [ia, ib] aty', VecType _ [_] bty') ->
    let comp = Compiled
               { withDest = \dest -> do aloc <- asLoc $ compileStat a
                                        bloc <- asLoc $ compileStat b
                                        makeFor ia $ \i -> do
                                          aloc' <- apIndex aloc i
                                          sumname <- freshName "sum"
                                          writeCode [citems| $ty:sumty $id:sumname = 0; |]
                                          makeFor ib $ \j -> do
                                            aex <- apIndex aloc' j >>= asExp . asRValue
                                            bex <- apIndex bloc j >>= asExp . asRValue
                                            writeCode [citems| $id:sumname += $aex * $bex; |]
                                          dest' <- apIndex dest i
                                          store dest' [cexp| $id:sumname |]
               , asExp = defaultAsExp (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
    in comp
  (VecType _ [ia] aty', VecType _ [_] bty') -> -- dot product
    let comp = Compiled
               { asExp = do aloc <- asLoc $ compileStat a
                            bloc <- asLoc $ compileStat b
                            sumname <- freshName "sum"
                            writeCode [citems| $ty:sumty $id:sumname = 0; |]
                            makeFor ia $ \i -> do
                              aex <- apIndex aloc i >>= asExp . asRValue
                              bex <- apIndex bloc i >>= asExp . asRValue
                              writeCode [citems| $id:sumname += $aex * $bex; |]
                            return [cexp| $id:sumname |]
               , asLoc = defaultAsLocFromAsExp (getType v) comp
               , withDest = defaultWithDest (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               }
    in comp
  (VecType {}, VecType {}) -> error "compileStat: cannot multiply arbitrary vectors"
  _ -> let comp = Compiled
                  { noValue = return ()
                  , asExp =  do
                       aex <- asExp $ compileStat a
                       bex <- asExp $ compileStat b
                       return [cexp| $aex * $bex |]
                  , asLoc = defaultAsLocFromAsExp (getType v) comp
                  , withDest = defaultWithDest (getType v) comp
                  }
       in comp
  where aty = normalizeTypes $ getType a
        bty = normalizeTypes $ getType b

        rty = case normalizeTypes $ getType v of
          VecType _ _ ty -> ty
          ty -> ty

        sumty = compileType rty

compileStat v@(Binary pos Concat v1 v2) = comp
  where comp = Compiled
               { withDest = \dest -> do
                    v1loc <- asLoc $ compileStat v1
                    v2loc <- asLoc $ compileStat v2
                    let VecType _ (_:dbnds) dbty = normalizeTypes $ locType dest
                    storeLoc (offsetLoc (VecType DenseMatrix (bnd1:dbnds) dbty) dest [cexp| 0 |]) v1loc
                    bnd1ex <- asExp $ compileStat bnd1
                    storeLoc (offsetLoc (VecType DenseMatrix (bnd2:dbnds) dbty) dest bnd1ex) v2loc
               , asLoc = defaultAsLoc (getType v) comp
               , asExp = defaultAsExp (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               }
        (VecType _ (bnd1:bnds1) bty1) = normalizeTypes $ getType v1
        (VecType _ (bnd2:bnds2) bty2) = normalizeTypes $ getType v2

compileStat v@(Binary pos op v1 v2) | op `elem` comparisonOps = comp
  where comp = Compiled
                  { noValue = return ()
                  , asExp = opExp <$> (asExp $ compileStat v1) <*> (asExp $ compileStat v2)
                  , asLoc = defaultAsLocFromAsExp (getType v) comp
                  , withDest = defaultWithDest (getType v) comp
                  }
        opExp a b = case op of
                      EqOp ->  [cexp| $a == $b |]
                      LTOp ->  [cexp| $a <  $b |]
                      LTEOp -> [cexp| $a <= $b |]
        comparisonOps = [EqOp, LTOp, LTEOp]
compileStat v = error $ "compileStat not implemented: " ++ show v

compileLoc :: Location CExpr -> CM CmLoc
compileLoc (Ref ty v) = case normalizeTypes ty of
  VecType _ idxs bty -> do v <- lookupName "v" v
                           return $ mkVecLoc bty [cexp| $id:v |] idxs
  _ -> do v' <- lookupName "v" v
          return $ refLoc ty v'

compileLoc loc@(Index a idxs) = do aloc <- asLoc $ compileStat a
                                   cidxs' <- mapM mkIndex idxs
                                   let ty = normalizeTypes $ getLocType loc
                                   mkLoc ty cidxs' aloc
  where mkIndex :: CExpr -> CM (Either (Int, CmLoc) C.Exp) -- TODO tuple
        mkIndex idx = case normalizeTypes (getType idx) of
          VecType _ ibnds ibty -> do
            idxloc <- asLoc $ compileStat idx
            return $ Left (length ibnds, idxloc)
          ty -> do
            idxex <- asExp $ compileStat idx
            return $ Right idxex

        mkLoc :: Type -> [Either (Int, CmLoc) C.Exp] -> CmLoc -> CM CmLoc
        mkLoc _ [] aloc = return aloc
        mkLoc ty ((Right exp):idxs) aloc = apIndex aloc exp >>= mkLoc ty idxs
        mkLoc ty ((Left (n, iloc)):idxs) aloc = deferLoc ty iloc n $ \iloc' -> do -- TODO tuples
          ilocex <- asExp $ asRValue iloc'
          apIndex aloc ilocex >>= mkLoc (strip n ty) idxs

        strip :: Int -> Type -> Type
        strip 0 ty = ty
        strip n (VecType _ (bnd:bnds) bty) = strip (n - 1) (VecType DenseMatrix bnds bty)

compileLoc l@(Field a field) = do sex <- asExp $ compileStat a
                                  let sex' = access sex (getType a) field
                                  case getLocType l of
                                   ty@(VecType _ bnds bty) -> return $ mkVecLoc bty sex' bnds
                                   ty -> return $ expLoc ty (return sex')
  where access ex (StructType {}) field  = [cexp| $ex.$id:field |]
        access ex (PtrType aty) field = [cexp| $(access' ex aty)->field |]
        access' ex (PtrType aty) = [cexp| *$(access' ex aty) |]
        access' ex aty = ex

compileLoc l@(Deref a) = do
  sex <- asExp $ compileStat a
  case normalizeTypes (getLocType l) of
    VecType _ idxs bty -> do
      return $ mkVecLoc bty [cexp| *$sex|] idxs
    ty -> return $ expLoc ty (return [cexp| *$sex|])
