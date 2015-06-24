{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Unification and type checking
module Language.Plover.Unify
       where

import Debug.Trace
import Language.Plover.Types
import Language.Plover.UsedNames
import Data.List
import Data.Tag
import Data.Maybe
import Control.Monad.Identity
import Control.Monad.State
import qualified Data.Map as M
import Text.ParserCombinators.Parsec (SourcePos)

data UnifierData = UnifierData
                   { usedVars :: [Variable]
                   , uTypes :: M.Map Variable (Tag SourcePos, Type) -- ^ unification variables -> types
                   , uExprs :: M.Map Variable (Tag SourcePos, CExpr) -- ^ unification variables -> exprs
                   , uErrors :: [UnificationError]
                   , uTypeEnv :: M.Map Variable (Tag SourcePos, Type) -- ^ variables -> types
                   }

data UnificationError = UError (Tag SourcePos) String
                      deriving (Show, Eq, Ord)

type UM = State UnifierData

runUM :: [DefBinding] -> UM a -> Either [UnificationError] a
runUM defbs m = let (v, s) = runState m (initUniData defbs)
                in case uErrors s of
                    [] -> Right v
                    errs -> Left errs

initUniData :: [DefBinding] -> UnifierData
initUniData defbs = UnifierData
                    { usedVars = allToplevelNames defbs
                    , uTypes = M.empty
                    , uExprs = M.empty
                    , uErrors = []
                    , uTypeEnv = M.fromList [(binding d, (bindingPos d, definitionType d))
                                            | d <- defbs]
                    }

gensym :: String -> UM String
gensym prefix = do names <- usedVars <$> get
                   gensym' names (length names)
  where gensym' :: [String] -> Int -> UM String
        gensym' names i = let newName = prefix ++ "$" ++ show i
                          in if newName `elem` names
                             then gensym' names (1 + i)
                             else do modify $ \state -> state { usedVars = newName : usedVars state }
                                     return newName

-- | Adds a type binding to a variable (i.e., global variables or parameters to a function)
addBinding :: Tag SourcePos -> String -> Type -> UM ()
addBinding pos v ty = do bindings <- uTypeEnv <$> get
                         modify $ \state -> state { uTypeEnv = M.insert v (pos, ty) bindings }
-- | Gets a type for a variable (i.e., global variables or function parameters)
getBinding :: String -> UM (Maybe (Tag SourcePos, Type))
getBinding v = do env <- uTypeEnv <$> get
                  return $ M.lookup v env
-- | Adds a type for a typehole
addUTypeBinding :: Tag SourcePos -> String -> Type -> UM ()
addUTypeBinding pos v ty = do bindings <- uTypes <$> get
                              modify $ \state -> state { uTypes = M.insert v (pos, ty) bindings }
-- | Gets a type for a typehole
getUTypeBinding :: Variable -> UM (Maybe (Tag SourcePos, Type))
getUTypeBinding v = do env <- uTypes <$> get
                       return $ M.lookup v env
-- | Adds a type for a typehole
addUExprBinding :: Tag SourcePos -> String -> CExpr -> UM ()
addUExprBinding pos v ex = do bindings <- uExprs <$> get
                              modify $ \state -> state { uExprs = M.insert v (pos, ex) bindings }
-- | Gets an expression for a hole
getUExprBinding :: Variable -> UM (Maybe (Tag SourcePos, CExpr))
getUExprBinding v = do env <- uExprs <$> get
                       return $ M.lookup v env

expandTerm :: TermMappable a => a -> UM a
expandTerm term = do tenv <- uTypes <$> get
                     eenv <- uExprs <$> get
                     let tty (TypeHole (Just v)) | Just (_, ty') <- M.lookup v tenv  = return ty'
                         tty ty = return ty

                         texp (Hole pos (Just v)) | Just (_, exp') <- M.lookup v eenv  = return exp'
                         texp exp = return exp

                         tloc = return
                         trng = return
                     return $ runIdentity $ traverseTerm tty texp tloc trng term

-- | This is a weird one: to cleanly unify generic integers/floats against
-- specific integers, we replace all of the generic integers/floats
-- with holes, putting the originals into the environment.
replaceIntegers :: TermMappable a => a -> UM a
replaceIntegers term = traverseTerm tty texp tloc trng term
  where tty ty@(IntType Nothing) = do g <- gensym "intType"
                                      addUTypeBinding NoTag g ty
                                      return $ TypeHole (Just g)
        tty ty@(FloatType Nothing) = do g <- gensym "floatType"
                                        addUTypeBinding NoTag g ty
                                        return $ TypeHole (Just g)
        tty ty = return ty
        
        texp exp@(IntLit pos Nothing _) = do g <- gensym "int"
                                             addUExprBinding pos g exp
                                             return $ Hole pos (Just g)
        texp exp@(FloatLit pos Nothing _) = do g <- gensym "float"
                                               addUExprBinding pos g exp
                                               return $ Hole pos (Just g)
        texp exp = return exp

        tloc = return
        trng = return


-- | "occurs check" for type holes
typeOccursIn :: TermMappable a => Variable -> a -> Bool
typeOccursIn v term = isNothing $ traverseTerm tty texp tloc trng term
  where tty ty@(TypeHole (Just v')) | v == v'  = Nothing
        tty ty = Just ty

        texp = return
        tloc = return
        trng = return

-- | "occurs check" for holes
expOccursIn :: TermMappable a => Variable -> a -> Bool
expOccursIn v exp = isNothing $ traverseTerm tty texp tloc trng exp
  where tty = return

        texp exp@(Hole pos (Just v')) | v == v'  = Nothing
        texp exp = Just exp

        tloc = return
        trng = return

typeCheckToplevel :: [DefBinding] -> UM ()
typeCheckToplevel defbs = forM_ defbs typeCheckDefBinding

typeCheckDefBinding :: DefBinding -> UM ()
typeCheckDefBinding def = case definition def of
  FunctionDef mexp ft -> let (FnT args retty, _) = getEffectiveFunType ft
                         in do typeCheckType (FnType $ FnT args retty)
                               uft <- universalizeFunType ft
                               mexp' <- trace (show uft) (return mexp)
                               case mexp' of
                                  Nothing -> return ()
                                  Just exp -> return () --typeCheck retty
  _ -> return ()

unifyInt :: Type -> UM Type
unifyInt ty = case ty of
  IntType _ -> return ty
  _ -> error "Put in unification failures."

typeCheckType :: Type -> UM Type
typeCheckType ty = return ty


data FunctionEnv = FnEnv [(Variable, Type)] Type
                 deriving Show

-- | When unifying against a function type, it is something like
-- calling a function or evaluating a Prolog rule.  One way to model
-- this is by instantiating a new version of it with all of its
-- variables replaced with fresh symbols.  This returns a version of
-- the getEffectiveFunType, so it can be immediately used with a
-- ConcreteApp.
universalizeFunType :: FunctionType -> UM FunctionEnv
universalizeFunType ft = do
  let (ft'@(FnT args retty), _) = getEffectiveFunType ft
  repAList <- forM args $ \(v, req, ty) -> do
    v' <- gensym v
    return (v, v')
  let vMap = M.fromList repAList
  let args' = [(vMap M.! v, universalizeTypeVars vMap ty)
              | (v, req, ty) <- args]
  return $ FnEnv args' (universalizeTypeVars vMap retty)


class TermMappable a where
  mapTerm :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
          -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
          -> a -> m a
  termMapper :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
             -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
             -> a -> m a

instance TermMappable Type where
  mapTerm tty texp tloc trng ty = case ty of
    VecType idxs ety -> VecType <$> mapM texp idxs <*> tty ety
    PtrType pty -> PtrType <$> tty pty
    FnType {} -> error "Not sure how to map across functions properly"
    _ -> return ty
  termMapper tty texp tloc trng = tty

instance TermMappable CExpr where
  mapTerm tty texp tloc trng exp = case exp of
    Vec pos v range expr -> Vec pos v <$> trng range <*> texp expr
    Return pos v -> Return pos <$> texp v
    Assert pos v -> Assert pos <$> texp v
    RangeVal pos range -> RangeVal pos <$> trng range
    If pos a b c -> If pos <$> texp a <*> texp b <*> texp c
    VecLit pos exprs -> VecLit pos <$> mapM texp exprs
    Let pos v val expr -> Let pos v <$> texp val <*> texp expr
    Uninitialized pos ty -> Uninitialized pos <$> tty ty
    Seq pos p1 p2 -> Seq pos <$> texp p1 <*> texp p2
    App pos fn args -> App pos <$> texp fn <*> mapM targ args
      where targ (Arg a) = Arg <$> texp a
            targ (ImpArg a) = ImpArg <$> texp a
    ConcreteApp pos fn args -> ConcreteApp pos <$> texp fn <*> mapM texp args
    Get pos loc -> Get pos <$> tloc loc
    Addr pos loc -> Addr pos <$> tloc loc
    Set pos loc val -> Set pos <$> tloc loc <*> texp val
    AssertType pos v ty -> AssertType pos <$> texp v <*> tty ty
    Unary pos op v -> Unary pos op <$> texp v
    Binary pos op v1 v2 -> Binary pos op <$> texp v1 <*> texp v2
    _ -> return exp
  termMapper tty texp tloc trng = texp

instance TermMappable (Location CExpr) where
  mapTerm tty texp tloc trng loc = case loc of
    Ref ty v -> Ref <$> tty ty <*> pure v
    Index a idxs -> Index <$> texp a <*> mapM texp idxs
    Field a member -> Field <$> texp a <*> pure member
    Deref a -> Deref <$> texp a
  termMapper tty texp tloc trng = tloc

instance TermMappable (Range CExpr) where
  mapTerm tty texp tloc trng (Range from to step) =
    Range <$> texp from <*> texp to <*> texp step
  termMapper tty texp tloc trng = trng

traverseTerm :: (Monad m, TermMappable a) => (Type -> m Type) -> (CExpr -> m CExpr)
             -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
             -> a -> m a
traverseTerm fty fexp floc frng x = mapTerm tty texp tloc trng x >>= termMapper fty fexp floc frng
  where tty = traverseTerm fty fexp floc frng
        texp = traverseTerm fty fexp floc frng
        tloc = traverseTerm fty fexp floc frng
        trng = traverseTerm fty fexp floc frng

universalizeTypeVars :: M.Map Variable Variable -> Type -> Type
universalizeTypeVars repMap ty = runIdentity $ traverseTerm tty texp tloc trng ty
  where tty = return
        texp expr = case expr of
          Get pos (Ref ty v) -> case M.lookup v repMap of
            Just v' -> return $ Hole pos (Just v')
            Nothing -> return expr
        tloc = return
        trng = return
