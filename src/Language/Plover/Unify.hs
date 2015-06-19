-- | Unification and type checking
module Language.Plover.Unify
       where

import Debug.Trace
import Language.Plover.Types
import Language.Plover.UsedNames
import Data.List
import Data.Tag
import Control.Monad.Identity
import Control.Monad.State
import qualified Data.Map as M
import Text.ParserCombinators.Parsec (SourcePos)

data UnifierData = UnifierData
                   { usedVars :: [Variable]
                   , uTypes :: M.Map Variable Type -- ^ unification variables -> types
                   , uExprs :: M.Map Variable Type -- ^ unification variables -> exprs
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

addBinding :: String -> Tag SourcePos -> Type -> UM ()
addBinding v pos ty = do bindings <- uTypeEnv <$> get
                         modify $ \state -> state { uTypeEnv = M.insert v (pos, ty) bindings }


typeCheckToplevel :: [DefBinding] -> UM ()
typeCheckToplevel defbs = forM_ defbs typeCheckDefBinding

typeCheckDefBinding :: DefBinding -> UM ()
typeCheckDefBinding def = case definition def of
  FunctionDef mexp ft -> let (FnT args retty, _) = getEffectiveFunType ft
                         in do typeCheckType (FnType $ FnT args retty)
                               case mexp of
                                  Nothing -> return ()
                                  Just exp -> return () --typeCheck retty
  _ -> return ()

unifyInt :: Type -> UM Type
unifyInt ty = case ty of
  IntType _ -> return ty
  _ -> error "Put in unification failures."

typeCheckType :: Type -> UM Type
typeCheckType ty = return ty
  

-- | When unifying against a function type, it is something like
-- calling a function or evaluating a Prolog rule.  One way to model
-- this is by instantiating a new version of it with all of its
-- variables replaced with fresh symbols.  This returns a version of
-- the getEffectiveFunType, so it can be immediately used with a
-- ConcreteApp.
generifyFunType :: FunctionType -> UM FunctionType
generifyFunType ft = do let (ft'@(FnT args retty), _) = getEffectiveFunType ft
                        repAList <- forM args $ \(v, req, ty) -> do
                          v' <- gensym v
                          return (v, v')
                        let repMap = M.fromList repAList
                        let args' = [(repMap M.! v, req, replaceTypeVars repMap ty)
                                    | (v, req, ty) <- args]
                        return $ FnT args' (replaceTypeVars repMap retty)

fmapTypes :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
          -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
          -> Type -> m Type
fmapTypes tty texp tloc trng ty = case ty of
  VecType idxs ety -> VecType <$> mapM texp idxs <*> tty ety
  PtrType pty -> PtrType <$> tty pty
  FnType {} -> error "Not sure how to fmap across function properly"
  _ -> return ty

  -- where tty' = traverseTypes tty texp tloc trng
  --       texp' = traverseExprs tty texp tloc trng

fmapExprs :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
              -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
              -> CExpr -> m CExpr
fmapExprs tty texp tloc trng exp = case exp of
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

  -- where tty' = traverseTypes tty texp tloc trng
  --       texp' = traverseExprs tty texp tloc trng
  --       tloc' = traverseLocs tty texp tloc trng
  --       trng' = traverseRange tty texp tloc trng

fmapLocs :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
             -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
             -> Location CExpr -> m (Location CExpr)
fmapLocs tty texp tloc trng loc = case loc of
  Ref ty v -> Ref <$> tty ty <*> pure v
  Index a idxs -> Index <$> texp a <*> mapM texp idxs
  Field a member -> Field <$> texp a <*> pure member
  Deref a -> Deref <$> texp a

fmapRange :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
              -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
              -> Range CExpr -> m (Range CExpr)
fmapRange tty texp tloc trng (Range from to step) =
  Range <$> texp from <*> texp to <*> texp step


traverseTypes :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
              -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
              -> Type -> m Type
traverseTypes fty fexp floc frng ty = fmapTypes tty texp tloc trng ty >>= fty
  where tty = traverseTypes fty fexp floc frng
        texp = traverseExprs fty fexp floc frng
        tloc = traverseLocs fty fexp floc frng
        trng = traverseRange fty fexp floc frng

traverseExprs :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
              -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
              -> CExpr -> m CExpr
traverseExprs fty fexp floc frng exp = fmapExprs tty texp tloc trng exp >>= fexp
  where tty = traverseTypes fty fexp floc frng
        texp = traverseExprs fty fexp floc frng
        tloc = traverseLocs fty fexp floc frng
        trng = traverseRange fty fexp floc frng

traverseLocs :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
             -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
             -> Location CExpr -> m (Location CExpr)
traverseLocs fty fexp floc frng loc = fmapLocs tty texp tloc trng loc >>= floc
  where tty = traverseTypes fty fexp floc frng
        texp = traverseExprs fty fexp floc frng
        tloc = traverseLocs fty fexp floc frng
        trng = traverseRange fty fexp floc frng

traverseRange :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
              -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
              -> Range CExpr -> m (Range CExpr)
traverseRange fty fexp floc frng rng = fmapRange tty texp tloc trng rng >>= frng
  where tty = traverseTypes fty fexp floc frng
        texp = traverseExprs fty fexp floc frng
        tloc = traverseLocs fty fexp floc frng
        trng = traverseRange fty fexp floc frng


replaceTypeVars :: M.Map Variable Variable -> Type -> Type
replaceTypeVars repMap ty = runIdentity $ traverseTypes tty texp tloc trng ty
  where tty = return
        texp = return
        tloc loc = case loc of
          Ref ty v -> return $ Ref ty (M.findWithDefault v v repMap)
          _ -> return loc
        trng = return
