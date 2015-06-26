{-# LANGUAGE QuasiQuotes #-}
module Language.Plover.CodeGen where

import Language.C.Quote.C
import qualified Language.C.Syntax as C
import Language.C.Pretty
import Text.PrettyPrint.Mainland

import Data.Tag
import Control.Monad.State
import qualified Data.Map as M

import Language.Plover.Types

import Data.Loc (SrcLoc(SrcLoc), Loc(NoLoc))

data CodeGenState = CodeGenState
                    { bindings :: M.Map String String
                    }
                    deriving Show

type CM a = State CodeGenState a

newScope :: CM a -> CM a
newScope m = do bs <- bindings <$> get
                v <- m
                modify $ \state -> state { bindings = bs }
                return v

getOkIdentifier :: String -> String -> String
getOkIdentifier def [] = def
getOkIdentifier def (v:vs) | v `elem` okStart = v : takeWhile (`elem` okRest) vs
                           | otherwise = getOkIdentifier def []
  where okStart = ['A'..'Z'] ++ ['a'..'z'] ++ "_"
        okRest = okStart ++ ['0'..'9']

getName :: String -> String -> CM String
getName def v = do bs <- bindings <$> get
                   case M.lookup v bs of
                    Just v' -> return v'
                    Nothing -> newName def v

newName :: String -> String -> CM String
newName def w = newName' 1 (getOkIdentifier def w)
  where newName' :: Int -> String -> CM String
        newName' i v = do bs <- bindings <$> get
                          let v' = if i == 1
                                   then v
                                   else v ++ "_" ++ show i
                          case M.lookup v' bs of
                           Just _ -> newName' (i + 1) v
                           Nothing -> do modify $ \state -> state { bindings = M.insert w v' bs }
                                         return v'

genName :: String -> CM String
genName v = newName "temp" v

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
                         , withDest :: String -> CM [C.BlockItem]
                         , withValue :: CM ([C.BlockItem], C.Exp)
                         }

-- | an expression with no side effects does not need to be computed
-- if no result is needed.
pureExpr :: C.Exp -> Compiled
pureExpr exp = Compiled { noResult = return []
                        , withDest = \v -> return [ [citem| $id:v = $exp; |] ]
                        , withValue = return ([], exp) }

-- | an expression with side effects must be computed even if no
-- result is needed.
impureExpr :: C.Exp -> Compiled
impureExpr exp = Compiled { noResult = return [ [citem| $exp; |] ]
                          , withDest = \v -> return [ [citem| $id:v = $exp; |] ]
                          , withValue = return ([], exp) }


testCompileExpr :: CExpr -> String
testCompileExpr exp = let (blks, v) = evalState (compileStat exp >>= withValue) (CodeGenState M.empty)
                          item = if null blks
                                 then [citem| { return $v; } |]
                                 else [citem| { $items:blks return $v; } |]
                      in show $ ppr item

compileStat :: CExpr -> CM Compiled

compileStat (If _ a b c) = do a' <- compileStat a
                              b' <- compileStat b
                              c' <- compileStat c
                              (abl, aexp) <- withValue a'
                              return $ Compiled
                                { noResult = do bbl <- noResult b'
                                                cbl <- noResult c'
                                                return (abl ++
                                                     [ [citem| if ($(aexp)) { $items:bbl } else { $items:cbl } |] ])
                                , withDest = \v -> do bbl <- withDest b' v
                                                      cbl <- withDest c' v
                                                      return (abl ++
                                                          [ [citem| if ($(aexp)) { $items:bbl } else { $items:cbl } |] ])
                                , withValue = do v <- genName "v"
                                                 bbl <- withDest b' v
                                                 cbl <- withDest c' v
                                                 (vbl, vty) <- compileInitType (getType b) -- c same
                                                 return (abl ++ vbl ++
                                                     [ [citem| $ty:vty $id:v; |]
                                                       , [citem| if ($(aexp)) { $items:bbl } else { $items:cbl } |] ]
                                                     , [cexp| $id:v |])
                                 }

compileStat (VoidExpr _) = return $ Compiled { noResult = return []
                                             , withDest = \v -> error "Cannot store VoidExpr"
                                             , withValue = return ([], error "Cannot get VoidExpr") }
compileStat (IntLit _ _ v) = return $ pureExpr [cexp| $int:v |] -- TODO consider type
compileStat (FloatLit _ _ v) = return $ pureExpr [cexp| $double:(toRational v) |] -- TODO consider type
compileStat (StrLit _ s) = return $ pureExpr [cexp| $string:s |]
compileStat (BoolLit _ b) = return $ pureExpr [cexp| $id:lit |]
  where lit :: String
        lit = if b then "TRUE" else "FALSE"

-- compileStat (VecLit pos []) = compileStat (VoidExpr pos)
-- compileStat v@(VecLit pos xs) = do xs' <- mapM compileStat xs
--                                    let xty = compileType $ getType (head xs)
--                                    return $ Compiled
--                                      { noResult = concat <$> mapM noResult xs'
--                                      , withDest = \v -> do (xsbl, vec) <- mkVecLit xty xs'
--                                                            return $ xsbl ++ [
--                                                              [citem| $id:v = $vec; |] ]
--                                      , withValue =  mkVecLit xty xs'
--                                      }
--   where mkVecLit xty xs' = do xs'' <- mapM withValue xs'
--                               let xsbl = concat $ map fst xs''
--                               let xsex = map snd xs''
--                               let xsex' = map (\x -> C.ExpInitializer x (SrcLoc NoLoc)) xsex
--                               return $ (xsbl, [cexp| ($ty:xty*) { $inits:(xsex') } |])

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
          val'' <- case val of
                    Uninitialized {} -> return []
                    _ -> do val' <- compileStat val
                            withDest val' v'
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

--compileStat (ConcreteApp f args) = let args' = [a |
