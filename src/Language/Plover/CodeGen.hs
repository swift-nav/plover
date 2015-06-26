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

import Language.Plover.Types

import Data.Loc (SrcLoc(SrcLoc), Loc(NoLoc))

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
                                     else v ++ "_" ++ show i
                            if v' `elem` usedNames
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
compileInitType' (VecType idxs base) = do size <- compileStat (foldr1 (*) idxs)
                                          (sizebl, sizeex) <- withValue size
                                          (basebl, basety) <- compileInitType base
                                          return (sizebl ++ basebl,
                                                  [cty|$ty:basety[$sizeex] |])
--compileInitType' -- structs are weird
compileInitType' t = return ([], compileType t)

data Compiled = Compiled { noResult :: CM [C.BlockItem]
                         , withDest :: CmLoc -> CM [C.BlockItem]
                         , withValue :: CM ([C.BlockItem], C.Exp)
                         }

data CmLoc = CmLoc { apIndex :: C.Exp -> CmLoc -- ^ apply an index to a vector location
                   , store :: C.Exp -> CM [C.BlockItem] -- ^ store an expression if this is a simple (i.e, non-vector) location
                   , asRValue :: Compiled -- ^ get the compiled simple (i.e., non-vector) expression
                   }

newLoc :: String -> Type -> CM CmLoc
newLoc v ty = case normalizeTypes ty of
  VecType idxs bty -> do v <- genName v
                         return $ mkVecLoc 

genLoc :: String -> CM CmLoc
genLoc def v = do v' <- freshName (getOkIdentifier def v)
              return $ CmLoc { apIndex = error "Cannot apIndex genLoc"
                             , store = \exp -> return $ [ [cexp| $id:(v') = $exp |] ]
                             , asRValue = pureExpr [cexp| $id:(v') |]
                             }

exprAsLoc :: CExpr -> CmLoc
exprAsLoc exp = case exp of
  Vec pos idx range val -> return $ CmLoc
                           { apIndex :: \exp -> newName
                                          }
               
genStore :: CmLoc -> CExpr -> CM [C.BlockItem]
genStore loc exp = case exp of
  Vec pos idx range val -> newScope $ do
    i <- newName "i" idx
    let VecType _ itty = getType range
        citty = compileType itty
    eou
  Get locSource -> case normalizeTypes $ getType exp of
    VecType [idx:idxs] _ -> do i <- genName "i"
                               let ci = [cexp| $id:i |]
                               genStore (apIndex loc ci)
  _ -> do temp <- genName "x"
  compileStat 


  _ -> case normalizeTypes $ getType exp of
        VecType [idx:idxs] _ -> 

      case normalizeTypes $ getType exp of
  VecType [idx:idxs] _ -> do let itty = compileType $ getType idx
                             i <- offerNextIndex loc
                             (boundBl, boundEx) <- withValue idx
                             compileLoc (Index exp 
                             [citem| for ($ty:itty $id:i = 0; $id:i < $boundEx; i++) { 


loc <- genLoc

-- | an expression with no side effects does not need to be computed
-- if no result is needed.
pureExpr :: C.Exp -> Compiled
pureExpr exp = pureBExpr [] exp

pureBExpr :: [C.BlockItem] -> C.Exp -> Compiled
pureBExpr setup exp = Compiled { noResult = return []
                               , withDest = \v -> return $ setup ++ [ [citem| $v = $exp; |] ]
                               , withValue = return (setup, exp) }


-- | an expression with side effects must be computed even if no
-- result is needed.
impureExpr :: C.Exp -> Compiled
impureExpr exp = Compiled { noResult = return [ [citem| $exp; |] ]
                          , withDest = \v -> return [ [citem| $v = $exp; |] ]
                          , withValue = return ([], exp) }


testCompileExpr :: CExpr -> String
testCompileExpr exp = let (blks, v) = evalState (compileStat exp >>= withValue) (CodeGenState M.empty)
                          item = if null blks
                                 then [citem| { return $v; } |]
                                 else [citem| { $items:blks return $v; } |]
                      in show $ ppr item

compileStat :: CExpr -> Compiled

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
                           , withValue = do (abl, aexp) <- withValue $ compileStat a
                                            v <- genName "v"
                                            let v' = [cexp| $id:v |]
                                            bbl <- withDest (compileStat b) v'
                                            cbl <- withDest (compileStat c) v'
                                            (vbl, vty) <- compileInitType (getType b) -- c same
                                            return (abl ++ vbl ++
                                                [ [citem| $ty:vty $id:v; |]
                                                  , [citem| if ($(aexp)) { $items:bbl } else { $items:cbl } |] ]
                                                , v')
                          }

compileStat (VoidExpr _) = Compiled { noResult = return []
                                    , withDest = \v -> error "Cannot store VoidExpr"
                                    , withValue = return ([], error "Cannot get VoidExpr") }
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

compileStat (Let _ v val x) = do x' <- compileStat x
                                 return $ Compiled
                                   { noResult = compileLet $ \bbl -> do
                                      x'' <- noResult x'
                                      return $ bbl ++ x''
                                   , withDest = \w -> compileLet $ \bbl -> do
                                        x'' <- withDest x' w
                                        return $ bbl ++ x''
                                   , withValue = compileLet $ \bbl -> do
                                        (x'', xv) <- withValue x'
                                        return $ (bbl ++ x'', xv)
                                   }
  where compileLet f = newScope $ do
          v' <- newName "v" v
          let v'' = [cexp| $id:(v') |]
          val'' <- case val of
                    Uninitialized {} -> return []
                    _ -> do val' <- compileStat val
                            withDest val' v''
          (vbl, vty) <- compileInitType $ getType val
          f (vbl ++ [ [citem| $ty:vty $id:(v'); |] ] ++ val'')

-- skipping Uninitialized

compileStat (Seq _ a b)  = do a' <- compileStat a
                              b' <- compileStat b
                              return $ Compiled
                                { noResult = do abl <- noResult a'
                                                bbl <- noResult b'
                                                return (abl ++ bbl)
                                , withDest = \v -> do abl <- noResult a'
                                                      bbl <- withDest b' v
                                                      return (abl ++ bbl)
                                , withValue = do abl <- noResult a'
                                                 (bbl, bexp) <- withValue b'
                                                 return (abl ++ bbl, bexp)
                                }

compileStat (ConcreteApp pos (Get _ (Ref fty f)) args) = do
  args' <- mapM compileStat args
  return $ Compiled
    { noResult = do (fbl, fex) <- theCall f args args'
                    return $ fbl ++ [ [citem| $fex; |] ]
    , withDest = \v -> do (fbl, fex) <- theCall f args args'
                          return $ fbl ++ [ [citem| $v = $fex; |] ]
    , withValue = theCall f args args'
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
compileStat (Get pos loc) = do loc' <- compileLoc loc
                               return $ Compiled
                                 { noResult = fst <$> getLoc loc'
                                 , withDest = \v -> do (bl, lexp) <- getLoc loc'
                                                       return $ bl ++ [[citem| $v = $lexp; |]]
                                 , withValue = getLoc loc'
                                 }
compileStat (Addr pos loc) = error "Addr not impl"
compileStat (Set pos loc v) = error "not impl"

compileStat (Hole {}) = error "No holes allowed"
compileStat (AssertType pos a ty) = compileStat a

-- unary
-- binary

flattenLoc :: Location CExpr -> Location CExpr
flattenLoc (Index (Get _ (Index a idxs1)) idxs2) = flattenLoc $ Index a (idxs1 ++ idxs2)
flattenLoc loc = loc

compileLoc loc = compileLoc' (flattenLoc loc)

compileLoc' :: Location CExpr -> CmLoc
compileLoc' (Ref ty v) = case normalizeTypes ty of
  VecType idxs bty -> mkVecLoc (getName "v" v) idxs
  _ -> CmLoc { apIndex = error "Cannot apIndex non-vec"
             , store = \exp -> do v' <- getName "v" v
                                  return $ [ [cexp| $id:(v') = $exp; |] ]
             , asRValue = do v' <- getName "v" v
                             pureExpr [cexp| $id:(v') |]
             }

mkVecLoc :: CM String -> [CExpr] -> CmLoc
mkVecLoc mref idxs = mkVecLoc' [] [cexp|0|] idxs
  where mkVecLoc' setup curridx [] = CmLoc {
          apIndex = error "All indices already applied."
          , store = \exp -> do v' <- mref
                               return $ setup ++ [ [citem| $id:(v')[$curridx] = $exp; |] ]
          , asRValue = do v' <- mref
                          return $ pureBExpr setup [citem| $id:(v') |]
          }
        mkVecLoc' setup curridx (idx:idxs) = CmLoc {
          apIndex = \exp -> do (idxbl, idxex) <- withValue $ compileStat idx
                               return $ mkVecLoc' (setup ++ idxbl) [cexp| $idxex * $curridx + $exp |] idxs
          , store = error "Cannot store to vec loc"
          , asRValue = error "Cannot get vec loc as rvalue"
          }
  
--compileLoc (Index a idxs)
