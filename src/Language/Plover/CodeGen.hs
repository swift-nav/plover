{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecursiveDo #-}

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
        args' = [(v, dir, ty) | (v, _, dir, ty) <- args, nonVoid ty]

compileFunction :: String -> FunctionType -> CExpr -> CM [C.Definition]
compileFunction name ft exp = do
  args'' <- compileParams args'
  blks <- case mret of
    Just (v, retty') -> do v' <- lookupName "arg" v
                           let dest = case normalizeTypes retty' of
                                       VecType bnds retty'' -> mkVecLoc retty'' [cexp| $id:(v') |] bnds
                                       retty'' -> refLoc retty'' v'
                           withDest (compileStat exp) dest
    Nothing ->  case retty of
      Void -> noValue $ compileStat exp
      _ -> do (expbl, expex) <- withValue $ compileStat exp
              return (expbl ++ [ [citem| return $expex; |] ])
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
compileType' (TypedefType v) = [cty|typename $id:v|]
compileType' (StructType v _) = [cty|typename $id:v|]
compileType' (TypeHole _) = error "No type holes allowed."

-- When initializing a variable, need things like the length of the
-- array rather than just a pointer
compileInitType :: Type -> CM ([C.BlockItem], C.Type)
compileInitType ty = compileInitType' (normalizeTypes ty)

compileInitType' :: Type -> CM ([C.BlockItem], C.Type)
compileInitType' (VecType idxs base) = do sizeex <- asExp $ compileStat (foldr1 (*) idxs)
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
                          VecType bnds baseTy -> do exp <- mexp
                                                    apIndex (mkVecLoc baseTy exp bnds) idx
                          _ -> error "Cannot apIndex simple expLoc"
    , store = \v -> do exp <- mexp
                       case normalizeTypes ty of
                         VecType bnds baseTy -> error "Cannot simple store into vector expLoc"
                         _ -> writeCode [citems| $exp = $v; |]
    , asRValue = compPureExpr ty exp -- not correct for vector, but shouldn't be used anyway
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
  VecType idxs bty -> do vty <- compileInitType ty
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
          where (idx:idxs, bnds) = unzip acc
        mkVecLoc' acc (bnd:bnds) = CmLoc {
          apIndex = \idx -> return $ mkVecLoc' (acc ++ [(idx, bnd)]) bnds
          , store = error "Cannot do simple store into vector"
          , asRValue = error "Cannot get vector as rvalue" -- compPureExpr (VecType (bnd:bnds) baseTy) $ return ([], vec) -- TODO ?
          , asArgument = case acc of
              [] -> return ([], [], vec, [])
              _ -> do let (idx:idxs, bnds') = unzip (acc ++ zip (repeat [cexp|0|]) (bnd:bnds))
                      idxc <- collapseIdx idx idxs bnds'
                      return ([], [cexp| $vec + $idxc |], [])
          , locType = VecType (bnd:bnds) baseTy
        }

        collapseIdx :: C.Exp -> [C.Exp] -> [CExpr] -> CM C.Exp
        collapseIdx accidx [] _ = return accidx
        collapseIdx accidx (idx:idxs) (bnd:bnds) = do bndex <- asExp $ compileStat bnd
                                                      collapseIdx [cexp| $bndex * $accidx + $idx |]
                                                                  idxs bnds

-- | Creates a location which lets indices be applied on a given
-- location a fixed number of times before handing the location to a
-- function.
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

        VecType (bnd:bnds) bty = normalizeTypes ty
        ty' = VecType bnds bty

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
defaultasExp ty comp = do loc <- freshLoc "tmp" ty
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
                                   return (expLoc ty exp)

-- | uses asRValue and apIndex.  Just spills the thing into a new
-- location.
defaultAsArgument :: CmLoc -> CM ([C.BlockItem], C.Exp, [C.BlockItem])
defaultAsArgument loc = do floc <- freshLoc "arg" (locType loc)
                           (stbef,_) = withCode $ storeLoc floc loc
                           (staft,_) = withCode $ storeLoc loc floc
                           (bef, exp, aft) <- asArgument floc
                           return (stbef ++ bef, exp, aft ++ staft)

storeExp :: CmLoc -> C.Exp -> CM ()
storeExp dst exp = case normalizeTypes (locType dst) of
  VecType idxs bty -> storeLoc dst (mkVecLoc bty exp idxs)
  _ -> store dst exp

storeLoc :: CmLoc -> CmLoc -> CM ()
storeLoc dst src = case normalizeTypes (locType dst) of
  VecType (idx:idxs) bty -> makeFor idx $ \i -> do
    dst' <- apIndex dst i
    src' <- apIndex src i
    storeLoc dst' src'
  _ -> withDest (asRValue src) dst -- or (asExp $ asRValue src) >>= store dst

makeFor :: CExpr -> (C.Exp -> CM ()) -> CM ()
makeFor idx mbody = do boundEx <- asExp $ compileStat idx
                       (body,_) <- withCode $ newScope $ do
                                     let itty = compileType $ getType idx
                                     i <- freshName "idx"
                                     mbody [cexp| $id:i |]
                       writeCode [citems| for ($ty:itty $id:i = 0; $id:i < $boundEx; $id:i++) { $items:body } |]

-- | an expression with no side effects does not need to be computed
-- if no result is needed.
compPureExpr :: Type -> CM C.Exp -> Compiled
compPureExpr ty mexpr = comp
  where comp = Compiled
               { noValue = void mexpr
               , withDest = defaultWithDest ty comp
               , asExp = mexpr
               , asLoc = do expr <- mexpr
                            return $ expLoc ty expr
               }

-- | an expression with side effects does need to be computed even if
-- no result is needed.
compImpureExpr :: Type -> CM C.Exp -> Compiled
compImpureExpr ty mexpr = comp
  where comp = Compiled
               { noValue = defaultNoValue ty comp
               , withDest = defaultWithDest ty comp
               , withValue = mexpr
               , asLoc = defaultAsLoc ty comp
               }

defaultAsRValue :: Type -> CM CmLoc -> Compiled
defaultAsRValue ty mloc = comp
  where comp = Compiled
               { noValue = mloc >>= noValue . asRValue
               , withDest = \dest -> mloc >>= storeLoc dest
               , withValue = mloc >>= withValue . asRValue
               , asLoc = mloc
               }

-- testCompileExpr :: CExpr -> String
-- testCompileExpr exp = let (blks, v) = evalState (withCode $ withValue $ compileStat exp) (CodeGenState M.empty [] [])
--                           item = if null blks
--                                  then [citem| { return $v; } |]
--                                  else [citem| { $items:blks return $v; } |]
--                       in show $ ppr item


compileStat :: CExpr -> Compiled

compileStat e@(Vec _ v range@(Range cstart cend cstep) exp) = comp
  where comp = Compiled -- TODO consider compiling range object as loc and indexing it
               { noValue = return ()
               , withDest = \dest -> do start <- asExp $ compileStat cstart
                                        end <- asExp $ compileStat cend
                                        step <- asExp $ compileStat cstep
                                        (body,(i,j)) <- withCode $ do
                                                      i <- newName "i" v
                                                      j <- freshName "idx"
                                                      dest' <- apIndex dest [cexp| $id:j |]
                                                      withDest (compileStat exp) dest'
                                                      return (i,j)
                                        writeCode [citems| for($ty:itty $id:i = $start, $id:j=0; $id:i < $end; $id:i += $step, $id:j++) { $items:body } |]
               , asExp = defaultAsExp (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }

compileStat (For pos i range@(Range cstart cend cstep) exp) = comp
  where comp = Compiled
               { noValue = do start <- asExp $ compileStat cstart
                              end <- asExp $ compileStat cend
                              step <- asExp $ compileStat cstep
                              (body,i) <- withCode $ do
                                            i <- newName "i" v
                                            noValue $ compileStat exp
                                            return i
                              writeCode [citems| for($ty:itty $id:i = $start; $id:i < $end; $id:i += $step) { $items:body } |]
               , asExp = error "Cannot get For as expression"
               , withDest = error "Cannot use For as dest"
               , asLoc = error "Cannot use For as location"
               }

compileStat exp@(RangeVal _ range) = comp
  where comp = Compiled
               { noValue = defaultNoValue ty comp
               , withDest = \dest -> do loc <- asLoc comp
                                        storeLoc dest loc
               , asExp = defaultAsExp ty comp
               , asLoc = return loc
               }
        ty@(VecType _ bty) = normalizeTypes $ getType exp
        
        loc = CmLoc
              { apIndex = \idx -> do exp <- rngExp idx
                                     return $ expLoc bty exp
              , store = error "Cannot store into rangeval"
              , asRValue = error "cannot asRValue rangeval"
              , asArgument = do ex <- asExp comp
                                return ([], ex, [])
              , locType = ty
              }

        rngExp idx = case range of
          Range (IntLit _ _ 0) end (IntLit _ _ 1) -> return idx
          Range start end (IntLit _ _ 1) -> do stex <- withValue $ compileStat start
                                               return [cexp| $stex + $idx |]
          Range (IntLit _ _ 0) end step -> do stepex <- withValue $ compileStat step
                                              return [cexp| $stepex * $idx |]
          Range start end step -> do stex <- withValue $ compileStat start
                                     stepex <- withValue $ compileStat step
                                     return [cexp| $stex + $idx * $stepex |]


compileStat (If _ a b c) = comp
  where comp = Compiled
               { noValue = do aexp <- withValue $ compileStat a
                              (bbl,_) <- withCode $ newScope $ noValue $ compileStat b
                              (cbl,_) <- withCode $ newScope $ noValue $ compileStat c
                              mkIf aexp bbl cbl
               , withDest = \loc -> do aexp <- withValue $ compileStat a
                                       (bbl,_) <- withCode $ newScope $ withDest (compileStat b) loc
                                       (cbl,_) <- withCode $ newScope $ withDest (compileStat c) loc
                                       mkIf aexp bbl cbl
               , asExp = defaultAsExp (getType b) comp
               , asLoc = defaultAsLoc (getType b) comp
               }
        mkIf aexp bbl cbl = writeCode [citems| if ($aexp) { $items:bbl } else { $items:cbl } |]

compileStat (VoidExpr _) = Compiled { noValue = return ()
                                    , withDest = \v -> error "Cannot store VoidExpr"
                                    , withValue = return $ error "Cannot get VoidExpr"
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
               , withDest = \dest -> fmap concat $ forM (zip [0..] xs) $ \(i,x) -> do
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
                v' <- newBlocklessScope $ do
                       v' <- newName "let" v
                       m
                return ()

-- -- skipping Uninitialized

compileStat (Seq _ a b) = comp
  where comp = Compiled
               { noValue = do noValue $ compileStat a
                              noValue $ compileStat b
               , withDest = \loc -> do noValue $ compileStat a
                                       withDest (compileStat b) loc
               , withValue = do noValue $ compileStat a
                                withValue $ compileStat b
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
                                    , asExp = asExp retty' comp
                                    , noValue = defaultNoValue retty' comp
                                    , asLoc = defaultAsLoc retty' comp
                                    }
                Nothing -> Compiled
                           { asExp = do dargs <- (zip dirs) <$> margs'
                                        let (bbl, fexp, bbl') = theCall f dargs
                                        writeCode bl
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
                           , asLoc = defaultAsLoc retty comp
                           }

        -- | Returns what to do before the call, the argument, and what to do after the call
        theCall :: String -> [(ArgDir, ([C.BlockItem], CmLoc, [C.BlockItem]))] -> ([C.BlockItem], C.Exp, [C.BlockItem])
        theCall f args = (before, [cexp| $id:f($args:(exps)) |], after)
            where before = forM args $ \(dir, (bef, argex, aft)) -> case dir of
                                                                      ArgIn -> bef
                                                                      ArgOut -> []
                                                                      ArgInOut -> bef
                  exps = map (\(dir, (bef, argex, aft)) -> argex) args
                  after = forM args $ \(dir, (bef, argex, aft)) -> case dir of
                                                                     ArgIn -> []
                                                                     ArgOut -> aft
                                                                     ArgInOut -> aft

compileStat (Hole {}) = error "No holes allowed"

compileStat (Get pos (Index a [])) = compileStat a
compileStat v@(Get pos loc) = defaultAsRValue (getType v) (compileLoc loc)

-- compileStat v@(Addr pos loc) = comp
--   where comp = Compiled
--                { withValue = do (bloc, loc) <- compileLoc loc
--                                 (bl, exp) <- withValue $ asRValue loc
--                                 return (bloc ++ bl, [cexp| & $exp |])
--                , noValue = defaultNoValue (getType v) comp
--                , withDest = defaultWithDest (getType v) comp
--                , asLoc = do (bl, ex) <- withValue $ comp
--                             return (bl, expLoc (getType v) ex)
--                }

-- compileStat (Set pos loc v) = comp
--   where comp = Compiled
--                { noValue = do (bloc, loc) <- compileLoc loc
--                               stbl <- withDest (compileStat v) loc
--                               return $ bloc ++ stbl
--                , withDest = \dst -> do bl <- noValue comp -- Shouldn't happen, but just in case...
--                                        return bl
--                , withValue = do bl <- noValue comp
--                                 return (bl, error "Cannot get Set as value.")
--                , asLoc = error "Set is not a location"
--                }

compileStat (AssertType pos a ty) = compileStat a

-- -- unary

compileStat v@(Unary _ op a)
  | op `elem` [Neg] = compileVectorized aty (asLoc $ compileStat a)
  where aty = normalizeTypes $ getType a

        opExp a = case op of
                   Neg -> [cexp| -$a |]

        compileVectorized (VecType [] aty) ma = compileVectorized aty ma
        compileVectorized ta@(VecType (abnd:abnds) aty) ma = comp
          where comp = Compiled
                       { withDest = \dest -> storeLoc dest loc
                       , asExp = defaultAsExp (locType loc) comp
                       , noValue = defaultNoValue (locType loc) comp
                       , asLoc = return loc }
                loc = CmLoc
                      { apIndex = \idx -> do aloc <- ma
                                             asLoc $ compileVectorized
                                                       (VecType abnds aty)
                                                       (apIndex aloc idx)
                      , asArgument = defaultAsArgument loc
                      , locType = getVectorizedType ta ta
                      , asRValue = error "Cannot get vectorized unary operation as rvalue"
                      , store = error "Cannot store into vectorized unary operation"
                      }
        compileVectorized ta ma = compPureExpr (getVectorizedType ta ta) $ opExp <$> ma

compileStat v@(Unary _ Inverse a) = comp
  where comp = Compiled
               { withDest = \dest -> do aloc <- asLoc $ compileStat a
                                        (bl, aex, _) <- asArgument aloc
                                        (_, dex, daf) <- asArgument dest
                                        nex <- withValue $ compileStat n
                                        writeCode bl
                                        writeCode [citems|inverse($nex,$aex,$dex);|]
                                        writeCode daf
               , withValue = defaultWithValue (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
        VecType [n,_] bty = normalizeTypes $ getType a

compileStat v@(Unary _ Transpose a) = comp
  where comp = Compiled
               { withDest = \dest -> do aloc <- asLoc $ compileStat a
                                        makeFor i2 $ \i -> do
                                          aloc' <- apIndex aloc i
                                          makeFor i1 $ \j -> do
                                            aloc'' <- apIndex aloc' j
                                            dest' <- apIndex dest i
                                            dest'' <- apIndex dest' j
                                            storeLoc dest'' aloc''
               , withValue = defaultWithValue (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
        loc = CmLoc
              { apIndex = \idx1 -> do aloc <- asLoc $ compileStat a
                                      return $ loc' aloc idx1
              , asArgument = defaultAsArgument loc
              , locType = VecType (i1:i2:idxs) aty'
              , asRValue = error "Cannot get transpose as rvalue"
              , store = error "Cannot store (yet) into transpose"
              }
        loc' aloc idx1 = CmLoc
                         { apIndex = \idx2 -> apIndex aloc idx2 >>= flip apIndex idx1
                         , asArgument = defaultAsArgument loc
                         , locType = VecType (i2:idxs) aty'
                         , asValue = error "Cannot get transpose as rvalue"
                         , store = error "Cannot store (yet) into transpose"
                         }
        VecType (i1:i2:idxs) aty' = normalizeTypes $ getType v

-- -- binary

compileStat v@(Binary _ op a b)
  | op `elem` [Add, Sub, Div] = compileVectorized aty bty (asLoc $ compileStat a) (asLoc $ compileStat b)
  where aty = normalizeTypes $ getType a
        bty = normalizeTypes $ getType b

        opExp a b = case op of
                     Add -> [cexp| $a + $b |]
                     Sub -> [cexp| $a - $b |]
                     Div -> [cexp| $a / $b |]

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
                                              return (abl'' ++ bbl',
                                                      [[citem| $id:sumname += $aex * $bex; |]])
                                            (dbl', dest'') <- apIndex dest' k
                                            st <- storeExp dest'' [cexp| $id:sumname |]
                                            return $ (dbl', [citems| $ty:sumty $id:sumname = 0; |] ++ forbl3 ++ st)
                                          return $ (abl' ++ dbl, forbl2)
                                        return (abl ++ bbl ++ forbl1)
               , withValue = defaultWithValue (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
    in comp
  (VecType [ia] aty', VecType [_, ib] bty') ->
    let comp = Compiled
               { withDest = \dest -> do (abl, aloc) <- asLoc $ compileStat a
                                        (bbl, bloc) <- asLoc $ compileStat b
                                        forbl1 <- makeFor ia $ \i -> do
                                          sumname <- freshName "sum"
                                          let sumty = compileType rty
                                          forbl2 <- makeFor ib $ \j -> do
                                            (abl', aex) <- apIndex aloc j
                                                           `bindBl` (withValue . asRValue)
                                            (bbl', bex) <- (apIndex bloc j
                                                            `bindBl` flip apIndex i)
                                                           `bindBl` (withValue . asRValue)
                                            return (abl' ++ bbl',
                                                    [citems| $id:sumname += $aex * $bex; |])
                                          (dbl, dest') <- apIndex dest i
                                          st <- storeExp dest' [cexp| $id:sumname |]
                                          return $ (dbl, [citems| $ty:sumty $id:sumname = 0; |] ++ forbl2 ++ st)
                                        return $ abl ++ bbl ++ forbl1
               , withValue = defaultWithValue (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
    in comp
  (VecType [ia, ib] aty', VecType [_] bty') ->
    let comp = Compiled
               { withDest = \dest -> do (abl, aloc) <- asLoc $ compileStat a
                                        (bbl, bloc) <- asLoc $ compileStat b
                                        forbl1 <- makeFor ia $ \i -> do
                                          (abl', aloc') <- apIndex aloc i
                                          sumname <- freshName "sum"
                                          let sumty = compileType rty
                                          forbl2 <- makeFor ib $ \j -> do
                                            (abl'', aex) <- apIndex aloc' j
                                                            `bindBl` (withValue . asRValue)
                                            (bbl', bex) <- apIndex bloc j
                                                           `bindBl` (withValue . asRValue)
                                            return (abl'' ++ bbl',
                                                    [citems| $id:sumname += $aex * $bex; |])
                                          (dbl, dest') <- apIndex dest i
                                          st <- storeExp dest' [cexp| $id:sumname |]
                                          return $ (abl' ++ dbl, [citems| $ty:sumty $id:sumname = 0; |] ++ forbl2 ++ st)
                                        return $ abl ++ bbl ++ forbl1
               , withValue = defaultWithValue (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               , asLoc = defaultAsLoc (getType v) comp
               }
    in comp
  (VecType [ia] aty', VecType [_] bty') ->
    let comp = Compiled
               { withValue = do (abl, aloc) <- asLoc $ compileStat a
                                (bbl, bloc) <- asLoc $ compileStat b
                                sumname <- freshName "sum"
                                let sumty = compileType rty
                                forbl <- makeFor ia $ \i -> do
                                  (abl', aex) <- apIndex aloc i `bindBl` (withValue . asRValue)
                                  (bbl', bex) <- apIndex bloc i `bindBl` (withValue . asRValue)
                                  return (abl' ++ bbl',
                                          [citems| $id:sumname += $aex * $bex; |])
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

compileStat v@(Binary pos Concat v1 v2) = comp
  where comp = Compiled
               { withDest = \dest -> do
                    (v1bl, v1loc) <- asLoc $ compileStat v1
                    (v2bl, v2loc) <- asLoc $ compileStat v2
                    (idx1bl, idx1ex) <- withValue $ compileStat idx1
                    for1 <- makeFor idx1 $ \i -> do
                      (dbl, dest') <- apIndex dest i
                      (v1bl', v1loc') <- apIndex v1loc i
                      st1 <- storeLoc dest' v1loc'
                      return $ (dbl ++ v1bl', st1)
                    for2 <- makeFor idx2 $ \i -> do
                      (dbl, dest') <- apIndex dest [cexp| $i + $idx1ex |]
                      (v2bl', v2loc') <- apIndex v2loc i
                      st2 <- storeLoc dest' v2loc'
                      return $ (dbl ++ v2bl', st2)
                    return $ v1bl ++ v2bl ++ idx1bl ++ for1 ++ for2
               , asLoc = defaultAsLoc (getType v) comp
               , withValue = defaultWithValue (getType v) comp
               , noValue = defaultNoValue (getType v) comp
               }
        (VecType (idx1:idxs1) bt1) = normalizeTypes $ getType v1
        (VecType (idx2:idxs2) bt2) = normalizeTypes $ getType v2

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

compileLoc l@(Field a field) = do (sbl, sex) <- withValue $ compileStat a
                                  let sex' = [cexp| $sex.$id:field |]
                                  case getLocType l of
                                   ty@(VecType bnds bty) -> return (sbl, mkVecLoc bty sex' bnds)
                                   ty -> return (sbl, expLoc ty sex')
