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
                   deriving Show

data UnificationError = UError (Tag SourcePos) String
                      | UTyFailure (Tag SourcePos) Type Type
                      | UExFailure (Tag SourcePos) CExpr CExpr
                      | ULocFailure (Tag SourcePos) (Location CExpr) (Location CExpr)
                      | UTyOccurs (Tag SourcePos) Variable Type
                      | UExOccurs (Tag SourcePos) Variable CExpr
                      | UNoField (Tag SourcePos) Variable
                      | UGenTyError (Tag SourcePos) Type String -- ^ A generic type error with a message
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

addUError :: UnificationError -> UM ()
addUError err = do s <- get
                   put $ s { uErrors = uErrors s ++ [err] }

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
                     let tty (TypeHole (Just v)) | Just (_, ty') <- M.lookup v tenv  = expand ty'
                         tty ty = return ty

                         -- TODO maybe unify ty against exp'
                         texp (HoleJ pos ty v) | Just (_, exp') <- M.lookup v eenv  = expand exp'
                         texp exp = return exp

                         tloc = return
                         trng = return
                         expand :: TermMappable a => a -> Identity a
                         expand = traverseTerm tty texp tloc trng
                     return $ runIdentity $ expand term

normalizeTypesM :: TermMappable a => a -> UM a
normalizeTypesM term = normalizeTypes <$> traverseTerm tty texp tloc trng term
  where tty ty = case ty of
          TypedefType name -> do mty' <- getBinding name
                                 case mty' of
                                  Just (pos, st@(StructType {})) -> return st
                                  _ -> do addUError $ UError NoTag $
                                            "COMPILER ERROR: The typedef " ++ show name
                                            ++ " should be defined."
                                          g <- gensym "typedef"
                                          return $ TypeHoleJ g
          _ -> return ty
        texp = return
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
exprOccursIn :: TermMappable a => Variable -> a -> Bool
exprOccursIn v exp = isNothing $ traverseTerm tty texp tloc trng exp
  where tty = return

        texp exp@(HoleJ pos _ v') | v == v'  = Nothing
        texp exp = Just exp

        tloc = return
        trng = return

typeCheckToplevel :: [DefBinding] -> UM [DefBinding]
typeCheckToplevel defbs = do
  forM_ defbs $ \def -> do
    withNewUScope $ typeCheckDefBinding def
  defbs' <- forM defbs $ \def -> do
    withNewUScope $ typeCheckDefBinding def
  s <- get
  --trace (show s) $
  return defbs'

withNewUScope :: UM a -> UM a
withNewUScope m = do
  bindings <- uTypeEnv <$> get
  v <- m
  modify $ \state -> state { uTypeEnv = bindings }
  return v

typeCheckDefBinding :: DefBinding -> UM DefBinding
typeCheckDefBinding def = do
  d' <- case definition def of
    FunctionDef mexp ft -> let (FnT args retty, _) = getEffectiveFunType ft
                           in do (FnType (FnT _ _)) <- typeCheckType (bindingPos def) (FnType $ FnT args retty)
                                 case mexp of
                                  Just exp | not (extern def) -> do
                                    expty <- typeCheck exp
                                    unify (bindingPos def) expty retty
                                  
                                    exp' <- expandTerm exp
                                    args' <- forM args $ \(v, b, ty) -> do
                                      ty' <- expandTerm ty
                                      return (v, b, ty')
                                    retty' <- expandTerm retty
                                    return $ FunctionDef (Just exp') (FnT args' retty)
                                  _ -> do args' <- forM args $ \(v, b, ty) -> do
                                            ty' <- expandTerm ty
                                            return (v, b, ty')
                                          retty' <- expandTerm retty
                                          return $ FunctionDef Nothing (FnT args' retty')
    StructDef fields -> return $ StructDef fields
    ValueDef mexp ty -> do ty' <- typeCheckType (bindingPos def) ty
                           case mexp of
                            Just exp -> do
                              expty <- typeCheck exp
                              unify (bindingPos def) expty ty

                              exp' <- expandTerm exp
                              ty' <- expandTerm ty
                              return $ ValueDef (Just exp') ty'
                            Nothing -> do ty' <- expandTerm ty
                                          return $ ValueDef Nothing ty'
  return $ def { definition = d' }


class Unifiable a where
  unify :: Tag SourcePos -> a -> a -> UM a

unifyN :: (Unifiable a, TermMappable a) => Tag SourcePos -> a -> a -> UM a
unifyN pos x y = do x' <- normalizeTypesM x
                    y' <- normalizeTypesM y
                    unify pos x' y'

instance Unifiable Type where
  unify pos (TypeHoleJ v) y = unifyTVar pos v y
  unify pos x (TypeHoleJ v) = unifyTVar pos v x

  unify pos (VecType idxs1 ty1) (VecType idxs2 ty2) | length idxs1 == length idxs2  = do
    ty' <- unify pos ty1 ty2
    idxs' <- forM (zip idxs1 idxs2) $ \(i1, i2) -> unify pos i1 i2
    return $ VecType idxs' ty'
  unify pos Void Void = return Void
  unify pos x@(FnType _) (FnType _) = return x -- TODO handle this better.
  unify pos NumType NumType = return NumType
  -- NumType always loses
  unify pos NumType y@(IntType {}) = return y
  unify pos x@(IntType {}) NumType = return x
  unify pos NumType y@(FloatType {}) = return y
  unify pos x@(FloatType {}) NumType = return x
  -- IntType loses to FloatType
  unify pos (IntType {}) y@(FloatType {}) = return y
  unify pos x@(FloatType {}) (IntType {}) = return x
  -- integers can go into bigger sizes
  unify pos (IntType t1) (IntType t2) | Just t' <- intPromotePreserveBits t1 t2 = return $ IntType t'
  unify pos (FloatType t1) (FloatType t2) = return $ FloatType (floatPromote t1 t2)
  
  unify pos StringType StringType = return StringType
  unify pos BoolType BoolType = return BoolType

  unify pos (PtrType a1) (PtrType a2) = do
    a' <- unify pos a1 a2
    return $ PtrType a'

  unify pos s@(StructType v1 _) (StructType v2 _) | v1 == v2  = return s
  
  unify pos x y = do addUError $ UTyFailure pos x y
                     return x

instance Unifiable CExpr where
  unify pos (HoleJ pos1 ty1 v) y = do ex <- unifyEVar (MergeTags [pos, pos1]) v y
                                      exty <- typeCheck ex
                                      unify pos ty1 exty
                                      return ex
  unify pos x y@(HoleJ {}) = unify pos y x

  -- skipping Vec
  -- skipping Return/Assert

  unify pos (RangeVal pos1 rng1) (RangeVal pos2 rng2) = RangeVal pos' <$> unify pos' rng1 rng2
    where pos' = MergeTags [pos, pos1, pos2]

  unify pos (If pos1 a1 b1 c1) (If pos2 a2 b2 c2) =
    If pos' <$> unify pos' a1 a2 <*> unify pos' b1 b2 <*> unify pos' c1 c2
    where pos' = MergeTags [pos, pos1, pos2]

  unify pos (VoidExpr pos1) (VoidExpr pos2) = return $ VoidExpr (MergeTags [pos, pos1, pos2])

  unify pos x@(IntLit {}) y@(IntLit {}) | x == y  = return x  -- TODO consider lifting integer types later?
  unify pos x@(FloatLit {}) y@(FloatLit {}) | x == y  = return x
  unify pos x@(StrLit {}) y@(StrLit {}) | x == y = return x
  unify pos x@(BoolLit {}) y@(BoolLit {}) | x == y = return x

  unify pos (VecLit pos1 xs1) (VecLit pos2 xs2)  | length xs1 == length xs2 = do
    xs' <- forM (zip xs1 xs2) $ \(x1, x2) -> unify pos' x1 x2
    return $ VecLit pos' xs'
    where pos' = MergeTags [pos, pos1, pos2]

  -- skipping Let
  -- skipping Uninitialized

  unify pos x@(Seq pos1 a1 b1) y@(Seq pos2 a2 b2) = Seq pos' <$> unify pos' a1 b1 <*> unify pos' a2 b2
    where pos' = MergeTags [pos, pos1, pos2]

  -- skipping App
  unify pos (ConcreteApp pos1 f1 args1) (ConcreteApp pos2 f2 args2) | length args1 == length args2 = do
    f' <- unify pos' f1 f2
    args' <- forM (zip args1 args2) $ \(a1, a2) -> unify pos' a1 a2
    return $ ConcreteApp pos' f' args'
    where pos' = MergeTags [pos, pos1, pos2]

  unify pos (Get pos1 loc1) (Get pos2 loc2) = Get pos' <$> unify pos' loc1 loc2
    where pos' = MergeTags [pos, pos1, pos2]
  unify pos (Addr pos1 loc1) (Addr pos2 loc2) = Addr pos' <$> unify pos' loc1 loc2
    where pos' = MergeTags [pos, pos1, pos2]
  unify pos (Set pos1 loc1 v1) (Set pos2 loc2 v2) = Set pos' <$> unify pos' loc1 loc2 <*> unify pos' v1 v2
    where pos' = MergeTags [pos, pos1, pos2]

  -- skipping AssertType  TODO handle it later?

  -- TODO Perhaps need algebraic simplification?
  unify pos (Unary pos1 op1 a1) (Unary pos2 op2 a2) | op1 == op2 = Unary pos' op1 <$> unify pos' a1 a2
    where pos' = MergeTags [pos, pos1, pos2]
  unify pos (Binary pos1 op1 a1 b1) (Binary pos2 op2 a2 b2) | op1 == op2 =
    Binary pos' op1 <$> unify pos' a1 a2 <*> unify pos' a2 b2
    where pos' = MergeTags [pos, pos1, pos2]

  unify pos x y = do addUError $ UExFailure pos x y
                     return x

instance Unifiable (Location CExpr) where
  unify pos x@(Ref _ v1) (Ref _ v2) | v1 == v2   = return x
  unify pos (Index a1 idxs1) (Index a2 idxs2) | length idxs1 == length idxs2  = do
    a' <- unify pos a1 a2
    idxs' <- forM (zip idxs1 idxs2) $ \(i1, i2) -> unify pos i1 i2
    return $ Index a' idxs'
  unify pos (Field a1 f1) (Field a2 f2) | f1 == f2  = do
    a' <- unify pos a1 a2
    return $ Field a' f1
  unify pos (Deref a1) (Deref a2) = do
    a' <- unify pos a1 a2
    return $ Deref a'
  unify pos x y = do addUError $ ULocFailure pos x y
                     return x

instance Unifiable (Range CExpr) where
  unify pos (Range from1 to1 step1) (Range from2 to2 step2) = do
    from' <- unify pos from1 from2
    to' <- unify pos to1 to2
    step' <- unify pos step1 step2
    return $ Range from' to' step'

unifyTVar :: Tag SourcePos -> Variable -> Type -> UM Type
unifyTVar pos v1 (TypeHoleJ v2)
  | v1 == v2  = return (TypeHoleJ v1)
  | otherwise = do mb1 <- getUTypeBinding v1
                   case mb1 of
                    Just (pos1, b1) -> unify (MergeTags [pos, pos1])
                                       b1 (TypeHoleJ v2)
                    Nothing ->
                      do mb2 <- getUTypeBinding v2
                         case mb2 of
                          Just (pos2, b2) -> unify (MergeTags [pos, pos2])
                                             (TypeHoleJ v1) b2
                          Nothing -> do addUTypeBinding pos v1 (TypeHoleJ v2)
                                        return $ TypeHoleJ v2
unifyTVar pos v1 t = do mb1 <- getUTypeBinding v1
                        case mb1 of
                         Just (pos1, b1) -> unify (MergeTags [pos, pos1])
                                            b1 t
                         Nothing -> do if v1 `typeOccursIn` t
                                         then addUError $ UTyOccurs pos v1 t
                                         else addUTypeBinding pos v1 t
                                       return t


unifyEVar :: Tag SourcePos -> Variable -> CExpr -> UM CExpr
unifyEVar pos v1 (HoleJ posv2 ty2 v2)
  | v1 == v2  = return (HoleJ (MergeTags [pos, posv2]) ty2 v1)
  | otherwise = do mb1 <- getUExprBinding v1
                   case mb1 of
                    Just (pos1, b1) -> unify (MergeTags [pos, posv2, pos1])
                                       b1 (HoleJ posv2 ty2 v2)
                    Nothing ->
                      do mb2 <- getUExprBinding v2
                         case mb2 of
                          Just (pos2, b2) -> unify (MergeTags [pos, posv2, pos2])
                                             (HoleJ (MergeTags [pos, posv2, pos2]) ty2 v1) b2
                          Nothing -> do addUExprBinding pos v1 (HoleJ (MergeTags [pos, posv2]) ty2 v2)
                                        return $ HoleJ (MergeTags [pos, posv2]) ty2 v2
unifyEVar pos v1 t = do mb1 <- getUExprBinding v1
                        case mb1 of
                         Just (pos1, b1) -> unify (MergeTags [pos, pos1])
                                            b1 t
                         Nothing -> do if v1 `exprOccursIn` t
                                         then addUError $ UExOccurs pos v1 t
                                         else addUExprBinding pos v1 t
                                       return t


expectInt :: Tag SourcePos -> Type -> UM IntType
expectInt pos ty = do
  ty' <- unify pos ty (IntType defaultIntType)
  case ty' of
   IntType t -> return t
   _ -> return defaultIntType

expectBool :: Tag SourcePos -> Type -> UM ()
expectBool pos ty = do
  ty' <- unify pos ty BoolType
  return ()

typeCheckType :: Tag SourcePos -> Type -> UM Type
typeCheckType pos (VecType idxs ty) = do
  idxs' <- forM idxs $ \idx -> do
    idxty <- typeCheck idx
    expectInt pos idxty
    return idx
  ty' <- typeCheckType pos ty
  return $ VecType idxs' ty'
typeCheckType pos Void = return Void
typeCheckType pos (FnType fn) = do
  let (FnT args retty, _) = getEffectiveFunType fn
  args' <- forM args $ \(v, b, vty) -> do
    vty' <- typeCheckType pos vty 
    addBinding pos v vty' -- assumes bindings cleared between functions
    return (v, b, vty')
  retty' <- typeCheckType pos retty
  return $ FnType $ FnT args' retty' -- N.B. this is the effective func type
typeCheckType pos NumType = return NumType
typeCheckType pos t@(IntType {}) = return t
typeCheckType pos t@(FloatType {}) = return t
typeCheckType pos StringType = return StringType
typeCheckType pos BoolType = return BoolType
typeCheckType pos (PtrType ty) = PtrType <$> typeCheckType pos ty
typeCheckType pos t@(TypedefType _) = normalizeTypesM t >>= typeCheckType pos
typeCheckType pos t@(StructType v (ST fields)) = return t
typeCheckType pos t@(TypeHole {}) = expandTerm t
--typeCheckType pos ty = return ty

typeCheck :: CExpr -> UM Type
typeCheck (Vec pos v range body) = do
  rt <- typeCheckRange pos range
  -- alpha renamed, so can just add v to scope
  addBinding pos v (IntType rt)
  bt <- typeCheck body
  return $ VecType [rangeSize pos range] bt
typeCheck (Return pos a) = do
  typeCheck a
  return Void
typeCheck (Assert pos a) = do
  typeCheck a
  return Void
typeCheck (RangeVal pos range) = do
  rt <- typeCheckRange pos range
  return $ VecType [rangeSize pos range] (IntType rt)
typeCheck (If pos a b c) = do
  tya <- typeCheck a
  expectBool pos tya
  tyb <- typeCheck b
  tyc <- typeCheck c
  unify pos tyb tyc
typeCheck (VoidExpr {}) = return Void
typeCheck (IntLit pos ty _) = return $ IntType ty
typeCheck (FloatLit pos ty _) = return $ FloatType ty
typeCheck (StrLit {}) = return $ StringType
typeCheck (BoolLit {}) = return $ BoolType
typeCheck (VecLit pos []) = return $ Void -- TODO is this correct? (probably not)
typeCheck (VecLit pos (x:xs)) = do
  xty <- typeCheck x
  forM_ xs $ \y -> do
    yty <- typeCheck y
    unify pos xty yty
  return $ VecType [IntLit pos defaultIntType (fromIntegral $ 1 + length xs)] xty
typeCheck (Let pos v x body) = do
  tyx <- typeCheck x
  addBinding pos v tyx
  bt <- typeCheck body
  return  bt
typeCheck (Uninitialized pos ty) = typeCheckType pos ty
typeCheck (Seq pos a b) = do
  typeCheck a
  typeCheck b
-- skip App
typeCheck (ConcreteApp pos (Get _ (Ref ty v)) args) = do
  Just (gpos, (FnType fty)) <- getBinding v
  unify pos ty (FnType fty)
  FnEnv fargs ret <- universalizeFunType fty
  when (length args /= length fargs) $ do
    addUError $ UError (MergeTags [pos, gpos]) "COMPILER ERROR. Incorrect number of arguments."
  forM_ (zip args fargs) $ \(arg, (v, vty)) -> do
    unify (MergeTags [pos, gpos]) arg (HoleJ pos vty v)
    tyarg <- typeCheck arg
    unify (MergeTags [pos, gpos]) tyarg vty
  return ret
typeCheck t@(HoleJ pos ty _) = do t' <- expandTerm t
                                  case t' of
                                   HoleJ pos' ty' _ -> typeCheckType (MergeTags [pos, pos']) ty'
                                   _ -> do ty' <- typeCheck t'
                                           unify pos ty ty'
                                           return ty'
typeCheck (Get pos loc) = do
  tyloc <- typeCheckLoc pos loc
  return tyloc
typeCheck (Addr pos loc) = do
  tyloc <- typeCheckLoc pos loc
  return $ PtrType tyloc
typeCheck (Set pos loc v) = do
  tyloc <- typeCheckLoc pos loc >>= normalizeTypesM
  tyv <- typeCheck v >>= normalizeTypesM
  unify pos tyloc tyv
  return $ Void
typeCheck (AssertType pos v ty) = do
  vty <- typeCheck v
  ty' <- typeCheckType pos ty
  unify pos vty ty'
typeCheck (Unary pos op a) = do error "not implemented"
typeCheck (Binary pos op a b) = do error "not implemented"

typeCheckRange :: Tag SourcePos -> Range CExpr -> UM IntType
typeCheckRange pos (Range from to step) = do
  t1 <- typeCheck from >>= expectInt pos
  t2 <- typeCheck to >>= expectInt pos
  t3 <- typeCheck step >>= expectInt pos
  case intPromotePreserveBits t1 t2 >>= intPromotePreserveBits t3 of
   Just t -> return $ t
   Nothing -> do addUError $ UError (MergeTags [pos, getTag from, getTag to, getTag step])
                   "Cannot promote to same integer types."
                 return $ t1

typeCheckLoc :: Tag SourcePos -> Location CExpr -> UM Type
typeCheckLoc pos (Ref ty v) = do
  Just (vpos, vty) <- getBinding v
  ty' <- unify (MergeTags [pos, vpos]) ty vty
  return ty'
typeCheckLoc pos (Index a idxs) = do
  aty <- typeCheck a >>= normalizeTypesM
  trace ("***" ++ show idxs ++ "\n  --" ++ show aty) $ typeCheckIdx aty idxs aty
  where typeCheckIdx oty [] aty = normalizeTypesM aty
        typeCheckIdx oty (idx:idxs) (VecType (ibnd:ibnds) bty) = do
          -- idx is next index value, ibnd is next vec bound
          idxty <- typeCheck idx
          case idxty of
           IntType _ -> typeCheckIdx oty idxs (VecType ibnds bty)
           VecType [idx'] (IntType _) -> do
             case idx of
               -- N.B. this is a special case so that ranges with
               -- unbounded top are unified to the length of the
               -- underlying vector. Otherwise, the unbounded slice
               -- will have a length determined by uses of the vector
               -- slice.
               RangeVal rpos (Range { rangeTo = h@(HoleJ {}) } ) -> unify (MergeTags [pos, rpos]) h ibnd >> return ()
               _ -> return ()
             bty' <- typeCheckIdx oty idxs (VecType ibnds bty)
             return $ VecType [idx'] bty'
           _ -> do unify pos (IntType IDefault) idxty
                   hole <- gensym "hole"
                   return $ TypeHoleJ hole
        typeCheckIdx oty (idx:idxs) ty = do
          addUError $ UGenTyError pos oty "Too many indices on expression of type"
          hole <- gensym "hole"
          return $ TypeHoleJ hole
typeCheckLoc pos (Field a field) = do
  aty <- typeCheck a
  case aty of
   StructType v (ST fields) -> case lookup field fields of
     Just fieldTy -> error "Need to replace dependent fields with struct members"
     Nothing -> do addUError $ UNoField pos field
                   TypeHoleJ <$> gensym "field"
   _ -> do addUError $ UError pos $ "Expecting struct when accessing field " ++ show field
           TypeHoleJ <$> gensym "field"
typeCheckLoc pos (Deref a) = do
  aty <- typeCheck a
  g <- gensym "deref"
  aty' <- unify pos aty (PtrType (TypeHoleJ g))
  case aty of
   PtrType dty -> return dty
   _ -> return (TypeHoleJ g)

rangeSize :: Tag SourcePos -> Range CExpr -> CExpr
rangeSize pos (Range (IntLit _ _ 0) to (IntLit _ _ 1)) = to
rangeSize pos (Range from to step) = Binary pos Div (Binary pos Sub to from) step

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



universalizeTypeVars :: M.Map Variable Variable -> Type -> Type
universalizeTypeVars repMap ty = runIdentity $ traverseTerm tty texp tloc trng ty
  where tty = return
        texp expr = case expr of
          Get pos (Ref ty v) -> case M.lookup v repMap of
            Just v' -> return $ HoleJ pos ty v'
            Nothing -> return expr
          _ -> return expr
        tloc = return
        trng = return
