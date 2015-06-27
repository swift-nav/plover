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

data CodeGenState = CodeGenState
                    { bindings :: M.Map String String
                    , usedNames :: [String]
                    }
                    deriving Show

type CM a = State CodeGenState a

newScope :: CM a -> CM a
newScope m = do bs <- bindings <$> get
                un <- usedNames <$> get
                v <- m
                modify $ \state -> state { bindings = bs, usedNames = un }
                return v

getOkIdentifier :: String -> String -> String
getOkIdentifier def [] = def
getOkIdentifier def (v:vs) | v `elem` okStart = v : takeWhile (`elem` okRest) vs
                           | otherwise = getOkIdentifier def []
  where okStart = ['A'..'Z'] ++ ['a'..'z'] ++ "_"
        okRest = okStart ++ ['0'..'9']

-- | Gets a C identifier for a given Plover identifier
getName :: String -> String -> CM String
getName def v = do bs <- bindings <$> get
                   case M.lookup v bs of
                    Just v' -> return v'
                    Nothing -> newName def v

-- | Gets a unique name.  The argument is the base for the name, and
-- must be a valid C identifier.
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

-- | Gets a new C identifier for a given Plover identifier (i.e., it should shadow a previous binding)
newName :: String -> String -> CM String
newName def v = do v' <- freshName (getOkIdentifier def v)
                   modify $ \state -> state { bindings = M.insert v v' (bindings state) }
                   return v'

-- | Generates a name for a temporary variable based on a Plover
-- variable name.
genName :: String -> CM String
genName v = freshName (getOkIdentifier "temp" v)


runCM :: CM a -> a
runCM m = evalState m (CodeGenState M.empty [])

compileTopLevel :: [DefBinding] -> CM [C.Definition]
compileTopLevel defbs = do forM_ defbs $ \defb ->
                             getName (error "Invalid top-level name") (binding defb)
                           d1 <- fmap concat $ forM defbs $ \defb -> newScope $ case definition defb of
                             FunctionDef mexp ft -> compileFunctionDecl (binding defb) ft
                             _ -> return []
                           d2 <- fmap concat $ forM defbs $ \defb -> newScope $ case definition defb of
                             FunctionDef (Just body) ft -> compileFunction (binding defb) ft body
                             _ -> return []
                           return (d1 ++ d2)

compileFunctionDecl :: String -> FunctionType -> CM [C.Definition]
compileFunctionDecl name ft = do
  args'' <- compileParams args'
  return [ [cedecl| $ty:(compileType retty) $id:(name)($params:(args'')); |] ]
  where (FnT args retty, _) = getEffectiveFunType ft
        nonVoid ty = case ty of
                      Void -> False
                      _ -> True
        args' = [(v, ty) | (v, _, ty) <- args, nonVoid ty]

compileFunction :: String -> FunctionType -> CExpr -> CM [C.Definition]
compileFunction name ft exp = do
  args'' <- compileParams args'
  blks <- case retty of
    Void -> noResult $ compileStat exp
    _ -> do (expbl, expex) <- withValue $ compileStat exp
            return (expbl ++ [ [citem| return $expex; |] ])
  return [ [cedecl| $ty:(compileType retty) $id:(name)($params:(args'')) { $items:blks } |] ]
  where (FnT args retty, _) = getEffectiveFunType ft
        nonVoid ty = case ty of
                      Void -> False
                      _ -> True
        args' = [(v, ty) | (v, _, ty) <- args, nonVoid ty]
  

compileParams :: [(Variable, Type)] -> CM [C.Param]
compileParams = mapM compileParam

compileParam :: (Variable, Type) -> CM C.Param
compileParam (v, ty) = do v' <- getName "arg" v
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
--compileType' (StructType v _) = [cty|typename $id:v|]  -- structs are weird
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

data Compiled = Compiled { noResult :: CM [C.BlockItem]
                         , withDest :: CmLoc -> CM [C.BlockItem]
                         , asLoc :: CM CmLoc -- ^ so that values are exposed to the vector interface
                         }

withValue :: Compiled -> CM ([C.BlockItem], C.Exp)
withValue com = asLoc com >>= asRValue

data CmLoc = CmLoc { apIndex :: C.Exp -> CmLoc -- ^ apply an index to a vector location
                   , store :: C.Exp -> CM [C.BlockItem] -- ^ store an expression if this is a simple (i.e, non-vector) location
                   , asRValue :: CM ([C.BlockItem], C.Exp) -- ^ get the compiled simple (i.e., non-vector) expression
                   }

exprLoc :: CM ([C.BlockItem], C.Exp) -> CmLoc
exprLoc rval = CmLoc { apIndex = error "Cannot apIndex expression"
                     , store = error "Cannot store to expression"
                     , asRValue = rval }

newLoc :: String -> Type -> CM ([C.BlockItem], CmLoc)
newLoc v ty = case normalizeTypes ty of
  VecType idxs bty -> do v' <- genName v
                         (vbl, vty) <- compileInitType ty
                         return $ (vbl ++ [ [citem| $ty:vty $id:(v'); |] ],
                                   mkVecLoc [cexp| $id:(v')|] idxs)
  _ -> do v' <- genName v
          (vbl, vty) <- compileInitType ty
          return $ (vbl ++ [ [citem| $ty:vty $id:(v'); |] ],
                    refLoc v')

genLoc :: String -> Type -> CM ([C.BlockItem], CmLoc)
genLoc v ty = case normalizeTypes ty of
  VecType idxs bty -> do v' <- genName v
                         (vbl, vty) <- compileInitType ty
                         return $ (vbl ++ [ [citem| $ty:vty $id:(v'); |] ],
                                   mkVecLoc [cexp| $id:(v')|] idxs)
  _ -> do v' <- genName v
          (vbl, vty) <- compileInitType ty
          return $ (vbl ++ [ [citem| $ty:vty $id:(v'); |] ],
                    refLoc v')


-- | takes a C identifier
refLoc :: String -> CmLoc
refLoc v = CmLoc { apIndex = error "Cannot apIndex refLoc"
                 , store = \exp -> return $ [ [citem| $id:v = $exp; |] ]
                 , asRValue = return ([], [cexp| $id:v |])
                 }

-- | Makes a location which will execute some code before storing or
-- getting some location.
blockLoc :: CM [C.BlockItem] -> CmLoc -> CmLoc
blockLoc mblk loc = CmLoc { apIndex = \idx -> blockLoc mblk (apIndex loc idx)
                          , store = \exp -> do blk <- mblk
                                               stblks <- store loc exp
                                               return $ blk ++ stblks
                          , asRValue = do blk <- mblk
                                          (exblks, exp) <- asRValue loc
                                          return (blk ++ exblks, exp)
                          }

scopeBlockLoc :: (C.Exp -> CM [C.BlockItem]) -> CM CmLoc -> CmLoc
scopeBlockLoc mblk mloc = sbl []
  where sbl idxAcc = CmLoc { apIndex = \idx -> sbl (idxAcc ++ [idx])
                           , store = \exp -> newScope $ do
                                blk <- mblk (head idxAcc)
                                loc <- mloc
                                let loc' = deIndex loc (tail idxAcc)
                                stblks <- store loc' exp
                                return $ blk ++ stblks
                           , asRValue = newScope $ do
                                blk <- mblk (head idxAcc)
                                loc <- mloc
                                let loc' = deIndex loc (tail idxAcc)
                                (exblks, exp) <- asRValue loc'
                                return $ (blk ++ exblks, exp)
                           }
          where deIndex loc [] = loc
                deIndex loc (idx:idxs) = deIndex (apIndex loc idx) idxs

genStore :: CmLoc -> CmLoc -> Type -> CM [C.BlockItem]
genStore loc src ty = case normalizeTypes ty of
  VecType (idx:idxs) b -> newScope $ do
    let itty = compileType $ getType idx
    i <- genName "idx"
    (boundBl, boundEx) <- withValue $ compileStat idx
    substore <- genStore (apIndex loc [cexp| $id:i |]) (apIndex src [cexp| $id:i|]) (VecType idxs b)
    return $ boundBl ++ [[citem| for ($ty:itty $id:i = 0; $id:i < $boundEx; $id:i++) { $items:substore } |]]
  _ -> do (blks, exp) <- asRValue src
          sblks <- store loc exp
          return $ blks ++ sblks

-- | an expression with no side effects does not need to be computed
-- if no result is needed.
pureExpr :: C.Exp -> Compiled
pureExpr exp = pureBExpr [] exp

pureBExpr :: [C.BlockItem] -> C.Exp -> Compiled
pureBExpr setup exp = Compiled { noResult = return []
                               , withDest = \v -> (setup ++) <$> store v exp
                               , asLoc = return $ exprLoc $ return (setup, exp) }


-- | an expression with side effects must be computed even if no
-- result is needed.
impureExpr :: C.Exp -> Compiled
impureExpr exp = Compiled { noResult = return [ [citem| $exp; |] ]
                          , withDest = \v -> store v exp
                          , asLoc = return $ exprLoc $ return ([], exp) }


testCompileExpr :: CExpr -> String
testCompileExpr exp = let (blks, v) = evalState (withValue $ compileStat exp) (CodeGenState M.empty [])
                          item = if null blks
                                 then [citem| { return $v; } |]
                                 else [citem| { $items:blks return $v; } |]
                      in show $ ppr item

compileStat :: CExpr -> Compiled

compileStat v@(Vec _ i range exp) =
  let compiled = Compiled
                 { noResult = return []
                 , withDest = \dest -> do loc' <- asLoc compiled
                                          genStore dest loc' (getType v)
                 , asLoc = return $ scopeBlockLoc (\idx -> do i' <- newName "i" i
                                                              let VecType (bnd:_) _ = getType v
                                                                  ity = getType bnd
                                                              (vbl, vex) <- rngExp idx
                                                              return $ vbl ++ [ [citem| $ty:(compileType ity) $id:(i') = $vex; |] ])
                                  (asLoc $ compileStat exp)
                 }
      rngExp idx = case range of
        Range (IntLit _ _ 0) end (IntLit _ _ 1) -> return ([], [cexp| $idx |])
        Range start end (IntLit _ _ 1) -> do (stblk, stex) <- withValue $ compileStat start
                                             return (stblk, [cexp| $stex + $idx |])
        Range (IntLit _ _ 0) end step -> do (stepblk, stepex) <- withValue $ compileStat step
                                            return (stepblk, [cexp| $stepex * $idx |])
        Range start end step -> do (stblk, stex) <- withValue $ compileStat start
                                   (stepblk, stepex) <- withValue $ compileStat step
                                   return (stblk ++ stepblk, [cexp| $stex + $idx * $stepex |])
  in compiled

compileStat (If _ a b c) = Compiled
                           { noResult = do (abl, aexp) <- withValue $ compileStat a
                                           bbl <- noResult $ compileStat b
                                           cbl <- noResult $ compileStat c
                                           return (abl ++
                                                   [ [citem| if ($(aexp)) { $items:bbl } else { $items:cbl } |] ])
                           , withDest = \v -> do (abl, aexp) <- withValue $ compileStat a
                                                 bbl <- withDest (compileStat b) v
                                                 cbl <- withDest (compileStat c) v
                                                 return (abl ++
                                                     [ [citem| if ($(aexp)) { $items:bbl } else { $items:cbl } |] ])
                           , asLoc = do (abl, aexp) <- withValue $ compileStat a
                                        (vbl, v) <- genLoc "v" (getType b) -- type b == type c
                                        bbl <- withDest (compileStat b) v
                                        cbl <- withDest (compileStat c) v
                                        return $ blockLoc (return $ abl ++ vbl ++
                                                   [ [citem| if ($(aexp)) { $items:bbl } else { $items:cbl } |] ])
                                                   v
                          }

compileStat (VoidExpr _) = Compiled { noResult = return []
                                    , withDest = \v -> error "Cannot store VoidExpr"
                                    , asLoc = return $ error "Cannot get VoidExpr" }
compileStat (IntLit _ _ v) = pureExpr [cexp| $int:v |] -- TODO consider type
compileStat (FloatLit _ _ v) = pureExpr [cexp| $double:(toRational v) |] -- TODO consider type
compileStat (StrLit _ s) = pureExpr [cexp| $string:s |]
compileStat (BoolLit _ b) = pureExpr [cexp| $id:lit |]
  where lit :: String
        lit = if b then "TRUE" else "FALSE"

-- compileStat (VecLit pos []) = compileStat (VoidExpr pos)
-- compileStat v@(VecLit pos xs) = let xs' = map compileStat xs
--                                     xty = getType (head xs)
--                                    case xty of
--                                     VecType {} -> error "TODO compile VecLit of vecs"
--                                     _ -> return ()
--                                    xty' <- compileInitType $ xty
--                                    return $ Compiled
--                                      { noResult = concat <$> mapM noResult xs'
--                                      , withDest = \v -> do (xsbl, vec) <- mkVecLit xty xty' xs'
--                                                            return $ xsbl ++ [
--                                                              [citem| $v = $vec; |] ]
--                                      , withValue =  mkVecLit xty xty' xs'
--                                      }
--   where mkVecLit xty (xtybl, xty') xs' = do
--           xs'' <- mapM withValue xs'
--           let xsbl = concat $ map fst xs''
--           let xsex = map snd xs''
--           let xsex' = map (\x -> C.ExpInitializer x (SrcLoc NoLoc)) xsex
--           return $ (xtybl ++ xsbl, [cexp| ($ty:xty'[]) { $inits:(xsex') } |])

compileStat (Let _ v val x) = Compiled
                              { noResult = compileLet $ \bbl -> do
                                   x' <- noResult $ compileStat x
                                   return $ bbl ++ x'
                              , withDest = \dest -> compileLet $ \bbl -> do
                                   x' <- withDest (compileStat x) dest
                                   return $ bbl ++ x'
                              , asLoc = do bbl <- compileLet $ \bbl -> do -- not sure about this one...
                                             return bbl
                                             (vbl, x') <- genLoc "temp" (getType x)
                                           cx <- withDest (compileStat x) x'
                                           return $ blockLoc (return $ bbl ++ vbl ++ cx) x'
--                                   sto <- genStore x' 
--                                   return $ scopeBlockLoc (\idx -> do return bbl) (asLoc $ compileStat x)
                              }
  where compileLet f = newScope $ do
          v' <- newName "let" v
          (vbl, vty) <- compileInitType (getType ty)
          
          
          (vbl, v') <- newLoc v (getType val)
          val'' <- case val of
                    Uninitialized {} -> return []
                    _ -> do withDest (compileStat) v'
          f (vbl ++ val'')

-- skipping Uninitialized

compileStat (Seq _ a b)  = Compiled
                           { noResult = do abl <- noResult $ compileStat a
                                           bbl <- noResult $ compileStat b
                                           return (abl ++ bbl)
                           , withDest = \dest -> do abl <- noResult $ compileStat a
                                                    bbl <- withDest (compileStat b) dest
                                                    return (abl ++ bbl)
                           , asLoc = do abl <- noResult $ compileStat a
                                        bloc <- asLoc $ compileStat b
                                        return $ blockLoc (return abl) bloc
                                }

compileStat (ConcreteApp pos (Get _ (Ref fty f)) args) =
    Compiled
    { noResult = do (fbl, fex) <- theCall f args (map compileStat args)
                    return $ fbl ++ [ [citem| $fex; |] ]
    , withDest = \v -> do (fbl, fex) <- theCall f args (map compileStat args)
                          let FnType (FnT _ retty) = fty
                          sto <- genStore v (exprLoc (return ([], fex))) retty
                          return $ fbl ++ sto
    , asLoc = return $ exprLoc $ theCall f args (map compileStat args)
    }
  
  where nonVoid a = case getType a of
                     Void -> False
                     _ -> True
        theCall :: String -> [CExpr] -> [Compiled] -> CM ([C.BlockItem], C.Exp)
        theCall f args args' = do
          args'' <- forM (zip args args') $ \(a, a') ->
            case nonVoid a of
             False -> do c' <- noResult a'
                         return $ Left c'
             True -> do (cbl, cex) <- withValue a'
                        return $ Right (cbl, cex)
          let bbl = concat $ flip map args'' $ \x -> case x of
                                                      Left c' -> c'
                                                      Right (c', _) -> c'
          let args''' = map snd $ rights args''
          return (bbl, [cexp| $id:(f)( $args:(args''') ) |])

compileStat (Get pos (Index a [])) = compileStat a
compileStat (Get pos loc) = Compiled
                            { noResult = return []
                            , withDest = \dest -> do loc' <- compileLoc loc
                                                     genStore dest loc' (getLocType loc)
                            , asLoc = compileLoc loc }

-- compileStat (Addr pos loc) = error "Addr not impl"

compileStat (Set pos loc v) = Compiled
                              { noResult = do loc' <- compileLoc loc
                                              src' <- asLoc $ compileStat v
                                              genStore loc' src' (getType v)
                              , withDest = error "Set has no destination"
                              , asLoc = error "Set is not a location"
                              }

compileStat (Hole {}) = error "No holes allowed"
-- compileStat (AssertType pos a ty) = compileStat a

-- unary
-- binary

compileStat v = error $ "compileStat not implemented: " ++ show v

flattenLoc :: Location CExpr -> Location CExpr
flattenLoc (Index (Get _ (Index a idxs1)) idxs2) = flattenLoc $ Index a (idxs1 ++ idxs2)
flattenLoc loc = loc

compileLoc loc = compileLoc' (flattenLoc loc)

compileLoc' :: Location CExpr -> CM CmLoc
compileLoc' (Ref ty v) =  case normalizeTypes ty of
  VecType idxs bty -> do v <- getName "v" v
                         return $ mkVecLoc [cexp| $id:v |] idxs
  _ -> do v' <- getName "v" v
          return $ refLoc v'

-- mkVecLoc :: C.Exp -> [CExpr] -> CmLoc
-- mkVecLoc vec idxs = mkVecLoc' [] [cexp|0|] idxs
--   where mkVecLoc' setup curridx [] = CmLoc {
--           apIndex = error "All indices already applied."
--           , store = \exp -> return $ setup ++ [ [citem| $(vec)[$curridx] = $exp; |] ]
--           , asRValue = return (setup, [cexp| $(vec) |])
--           }
--         mkVecLoc' setup curridx (idx:idxs) = CmLoc {
--           apIndex = \exp -> do (idxbl, idxex) <- withValue $ compileStat idx
--                                return $ mkVecLoc' (setup ++ idxbl) [cexp| $idxex * $curridx + $exp |] idxs
--           , store = error "Cannot store to vec loc"
--           , asRValue = error "Cannot get vec loc as rvalue"
--           }

mkVecLoc :: C.Exp -> [CExpr] -> CmLoc
mkVecLoc vec bnds = mkVecLoc' [] bnds
  where mkVecLoc' :: [(C.Exp, CExpr)] -> [CExpr] -> CmLoc
        mkVecLoc' acc [] = CmLoc {
          apIndex = error "All indices already applied."
          , store = \exp -> let (idx:idxs, bnds) = unzip acc
                            in do (blks, idxc) <- collapseIdx idx idxs bnds []
                                  return $ blks ++ [ [citem| $vec[$idxc] = $exp; |] ]
          , asRValue = let (idx:idxs, bnds) = unzip acc
                       in do (blks, idxc) <- collapseIdx idx idxs bnds []
                             return $ (blks, [cexp| $vec[$idxc] |])
          }
        mkVecLoc' acc (bnd:bnds) = CmLoc {
          apIndex = \idx -> mkVecLoc' (acc ++ [(idx, bnd)]) bnds
          , store = error "Cannot do simple store into vector"
          , asRValue = return $ ([], vec) --error "Cannot get vector as simple value"
        }
        collapseIdx :: C.Exp -> [C.Exp] -> [CExpr] -> [C.BlockItem] -> CM ([C.BlockItem], C.Exp)
        collapseIdx accidx [] _ blks = return (blks, accidx)
        collapseIdx accidx (idx:idxs) (bnd:bnds) blks = do (bndbl, bndex) <- withValue $ compileStat bnd
                                                           collapseIdx [cexp| $bndex * $accidx + $idx |]
                                                             idxs bnds (blks ++ bndbl)

-- --compileLoc (Index a idxs)
