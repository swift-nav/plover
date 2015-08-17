{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Unification and type checking
module Language.Plover.Unify
       where

import Debug.Trace
import Language.Plover.Types
import Language.Plover.UsedNames
import Language.Plover.Algebra
import Data.List
import Data.Tag
import Data.Maybe
import Control.Monad.Identity
import Control.Monad.State
import Control.Applicative ((<$>), (<*>), (<*), pure)
import qualified Data.Map as M
import Text.ParserCombinators.Parsec (SourcePos)

-- [unification] The unifier is trying to solve for the types of each
-- type and value hole which appear in the program.  These generally
-- arise from the use of implicit arguments to functions.
--
-- The UnifierData object contains two maps from names.  Value holes
-- use both so that they have both an expanded expression and a type.
-- Type holes only use the map to types.
--
-- During unification, all references to (non-unification-)variables
-- should be of the form (Ref (TypeHole Nothing) v).  The (TypeHole
-- Nothing) will be filled in during the expansion phase.
--
-- Thou shalt not introduce unification variables which use parameters
-- from multiple functions: this is a purpose of universalizeFunType.
--
-- Thou shalt give types to value holes as they are introduced (if
-- known)

data UnifierData = UnifierData
                   { usedVars :: [Variable]
                   , uTypes :: M.Map Variable (Tag SourcePos, Type) -- ^ unification variables -> types (see note [unification])
                   , uExprs :: M.Map Variable (Tag SourcePos, CExpr) -- ^ unification variables -> exprs (see note [unification])
                   , uErrors :: [UnificationError]
                   , uTypeEnv :: M.Map Variable (Tag SourcePos, Type) -- ^ variables -> types
                   , uRetType :: Maybe (Tag SourcePos, Type) -- ^ The expected return type of the current function
                   , uSpecializations :: M.Map Variable CExpr
                   }
                   deriving Show

data UnificationError = UError (Tag SourcePos) String
                      | UTyFailure (Tag SourcePos) Type Type
                      | UTyAssertFailure (Tag SourcePos) Type Type
                      | UExFailure (Tag SourcePos) CExpr CExpr
                      | ULocFailure (Tag SourcePos) (Location CExpr) (Location CExpr)
                      | UTyOccurs (Tag SourcePos) Variable Type
                      | UExOccurs (Tag SourcePos) Variable CExpr
                      | URefOccurs (Tag SourcePos) Variable Type
                      | UNoField (Tag SourcePos) Variable
                      | UGenTyError (Tag SourcePos) Type String -- ^ A generic type error with a message
                      deriving (Show, Eq, Ord)

type UM = State UnifierData

type HoleData = (M.Map Variable Type, M.Map Variable CExpr)

-- | Takes the list of bindings, a list of holes one would like value/type
-- information about, and the monadic value to evaluate.
runUM :: [DefBinding] -> [String] -> UM a -> Either [UnificationError] (HoleData, a)
runUM defbs holes m = let (v, s) = runState (m <* expandMapErrors) (initUniData defbs)
                          p v x = (v, x)
                          htys = M.fromList $ mapMaybe
                                 (\v -> p v <$> snd <$> M.lookup v (uTypes s)) holes
                          hexs = M.fromList $ mapMaybe
                                 (\v -> p v <$> snd <$> M.lookup v (uExprs s)) holes
                      in case uErrors s of
                           [] -> Right ((htys, hexs), v)
                           errs -> Left errs
  where
    sm f (a, b) = do
      b <- f b
      return (a, b)
    expandMapErrors = do
      s <- get
      types' <- sequence $ M.map (sm expandTerm) (uTypes s)
      exprs' <- sequence $ M.map (sm expandTerm) (uExprs s)
      modify $ \s -> s { uTypes = types', uExprs = exprs'}

instance TermMappable UnificationError where
  mapTerm tty texp tloc trng err = case err of
    UError {} -> return err
    UTyFailure tag ty1 ty2 -> UTyFailure tag <$> tty ty1 <*> tty ty2
    UTyAssertFailure tag ty1 ty2 -> UTyAssertFailure tag <$> tty ty1 <*> tty ty2
    UExFailure tag ex1 ex2 -> UExFailure tag <$> texp ex1 <*> texp ex2
    ULocFailure tag loc1 loc2 -> ULocFailure tag <$> tloc loc1 <*> tloc loc2
    UTyOccurs tag v ty -> UTyOccurs tag v <$> tty ty
    UExOccurs tag v ex -> UExOccurs tag v <$> texp ex
    URefOccurs tag v ty -> URefOccurs tag v <$> tty ty
    UNoField {} -> return err
    UGenTyError tag ty str -> UGenTyError tag <$> tty ty <*> pure str
  termMapper = error "Cannot get termMapper for UnificationError"

expandErrors :: UM ()
expandErrors = do errors <- gets uErrors
                  errors' <- mapM (mapTerm expandTerm expandTerm expandTerm expandTerm) errors
                  modify $ \state -> state { uErrors = errors' }

initUniData :: [DefBinding] -> UnifierData
initUniData defbs = UnifierData
                    { usedVars = allToplevelNames defbs
                    , uTypes = M.empty
                    , uExprs = M.empty
                    , uErrors = []
                    , uTypeEnv = M.fromList [(binding d, (bindingPos d, definitionType d))
                                            | d <- defbs]
                    , uRetType = error "Return type not set"
                    , uSpecializations = M.empty
                    }

addUError :: UnificationError -> UM ()
addUError err = do
  err' <- mapTerm expandTerm expandTerm expandTerm expandTerm $ err
  modify $ \s -> s { uErrors = uErrors s ++ [err'] }

-- | Used for checking whether the typechecking should be aborted,
-- since the typechecking occurs in two passes (once to solve, once to
-- recompute bindings during full expansion).
hasUErrors :: UM Bool
hasUErrors = do errs <- uErrors <$> get
                return $ not (null errs)

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
-- | Adds a type for a typehole or hole
addUTypeBinding :: Tag SourcePos -> String -> Type -> UM ()
addUTypeBinding pos v ty = do bindings <- uTypes <$> get
                              modify $ \state -> state { uTypes = M.insert v (pos, ty) bindings }
-- | Gets a type for a typehole or hole
getUTypeBinding :: Variable -> UM (Maybe (Tag SourcePos, Type))
getUTypeBinding v = do env <- uTypes <$> get
                       return $ M.lookup v env
-- | Adds an expression for a hole
addUExprBinding :: Tag SourcePos -> String -> CExpr -> UM ()
addUExprBinding pos v ex = do bindings <- uExprs <$> get
                              modify $ \state -> state { uExprs = M.insert v (pos, ex) bindings }
-- | Gets an expression for a hole
getUExprBinding :: Variable -> UM (Maybe (Tag SourcePos, CExpr))
getUExprBinding v = do env <- uExprs <$> get
                       return $ M.lookup v env

expandTerm :: TermMappable a => a -> UM a
expandTerm term = do
  tenv <- uTypes <$> get
  eenv <- uExprs <$> get
  let tty (TypeHoleJ v) | Just (_, ty') <- M.lookup v tenv = expand ty'
      tty ty = return ty

      texp x@(Get pos (Ref _ v)) = do spec <- lookupSpecialization v
                                      maybe (return x) texp spec
      texp (HoleJ pos v) | Just (_, exp') <- M.lookup v eenv = expand exp'
      texp exp = return exp

      tloc = return
      trng = return

      expand :: TermMappable a => a -> UM a
      expand = traverseTerm tty texp tloc trng

  expand term


-- | Removes holes like `expandTerm`, and adds types to Refs (so then getType may be used).
fullExpandTerm :: TermMappable a => a -> UM a
fullExpandTerm term = do
  tenv <- uTypes <$> get
  eenv <- uExprs <$> get
  let tty (TypeHoleJ v) | Just (_, ty') <- M.lookup v tenv = expand ty'
      tty (TypedefType _ v) = do mty <- getBinding v
                                 let Just (_, ty) = mty
                                 ty' <- expand ty
                                 return $ TypedefType ty' v
      tty ty = return ty

      texp (Return pos ty v) = do ty' <- expand ty
                                  v' <- expand v
                                  -- Default continuation type is Void
                                  case ty' of
                                    TypeHole {} -> return $ Return pos Void v'
                                    _ -> return $ Return pos ty' v'
      texp (HoleJ pos v) | Just (_, exp') <- M.lookup v eenv = expand exp'
      texp exp = return exp

      tloc (Ref _ v) = do mty <- getBinding v
                          let Just (_, ty) = mty
                          ty' <- expand ty
                          return $ Ref ty' v
      tloc loc = return loc

      trng = return

      expand :: TermMappable a => a -> UM a
      expand = traverseTerm tty texp tloc trng

  expand term

-- | Expands just enough typedefs to see how many indices a vector has
baseExpandTypedefM :: Type -> UM Type
baseExpandTypedefM (TypedefType _ name) = do
  mty' <- getBinding name
  case mty' of -- Relies on the fact that the semchecker already checked this name refers to a type
    Just (pos, ty) -> baseExpandTypedefM ty
    _ -> do addUError $ UError NoTag $ "COMPILER ERROR: The type " ++ show name ++ " should be defined."
            TypeHoleJ <$> gensym "typedef"
baseExpandTypedefM (VecType st idxs bty) = VecType st idxs <$> baseExpandTypedefM bty
baseExpandTypedefM x@(TypeHoleJ {}) = do x' <- expandTerm x
                                         if x' == x
                                           then return x
                                           else baseExpandTypedefM x
baseExpandTypedefM x = return x

-- | Expands typedefs and then normalizes
normalizeTypesM :: TermMappable a => a -> UM a
normalizeTypesM ty = normalizeTypes <$> termMapper baseExpandTypedefM return return return ty

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

        texp exp@(HoleJ pos v') | v == v'  = Nothing
        texp exp = Just exp

        tloc = return
        trng = return

-- | "occurs check" for refs.  Used to check that a vector of vectors
-- does not having changing-size subvectors
refOccursIn :: TermMappable a => Variable -> a -> Bool
refOccursIn v exp = isNothing $ traverseTerm tty texp tloc trng exp
  where tty = return

        texp = return

        tloc loc@(Ref _ v') | v == v'  = Nothing
        tloc loc = Just loc

        trng = return

-- | This is the main unification function.
typeCheckToplevel :: [DefBinding] -> UM [DefBinding]
typeCheckToplevel defbs = do mapM_ (withNewUScope . typeCheckDefBinding) defbs
                             errsp <- hasUErrors
                             if errsp
                               then return []
                               else expandToplevel defbs

expandToplevel :: [DefBinding] -> UM [DefBinding]
expandToplevel defbs = mapM (withNewUScope . expandDefBinding) defbs

withNewUScope :: UM a -> UM a
withNewUScope m = do
  bindings <- uTypeEnv <$> get
  retty <- uRetType <$> get
  v <- m
  modify $ \state -> state { uTypeEnv = bindings, uRetType = retty }
  return v

withSpecialization :: String -> CExpr -> UM a -> UM a
withSpecialization v val m = do
  specs <- uSpecializations <$> get
  modify $ \state -> state { uSpecializations = M.insert v val specs }
  a <- m
  modify $ \state -> state { uSpecializations = specs }
  return a

lookupSpecialization :: String -> UM (Maybe CExpr)
lookupSpecialization v = do
  specs <- uSpecializations <$> get
  return $ M.lookup v specs

typeCheckDefBinding :: DefBinding -> UM ()
typeCheckDefBinding def = case definition def of
  FunctionDef mexp ft -> do
    (FnType (FnT args mva retty)) <- typeCheckType (bindingPos def) (FnType ft) -- this introduces function arguments into scope
    retty' <- typeCheckType (bindingPos def) retty
    modify $ \state -> state { uRetType = Just (bindingPos def, retty') }
    case mexp of
      Just exp | not (extern def) -> do
                   expty <- typeCheck exp
                   void $ unifyN (bindingPos def) expty retty'
      _ -> return ()
  StructDef members -> do
    forM_ members $ \(v, (vpos, exty, inty)) -> do
      typeCheckType vpos exty
      inty' <- typeCheckType vpos inty
      addBinding vpos v inty'
  ValueDef mexp ty -> do
    ty' <- typeCheckType (bindingPos def) ty
    case mexp of
      Just exp -> do
        expty <- typeCheck exp
        void $ unifyN (bindingPos def) expty ty
      Nothing -> return ()
  TypeDef ty -> void $ typeCheckType (bindingPos def) ty
  InlineCDef {} -> return ()

expandDefBinding :: DefBinding -> UM DefBinding
expandDefBinding db = do def' <- expandDefBinding' db
                         return $ db { definition = def' }

expandDefBinding' :: DefBinding -> UM Definition
expandDefBinding' def = case definition def of
  FunctionDef mexp ft -> do
    (FnType (FnT args mva retty)) <- typeCheckType (bindingPos def) (FnType ft) -- this introduces function arguments into scope (TODO just add them directly)
    case mexp of
      Just exp | not (extern def) -> do
                   args' <- forM args $ \(pos, v, b, dir, ty) -> do
                     ty' <- fullExpandTerm ty
                     return (pos, v, b, dir, ty')
                   modify $ \state -> state { uRetType = Just (bindingPos def, retty) }
                   retty' <- fullExpandTerm retty
                   _ <- typeCheck exp -- need to typeCheck to introduce bindings
                   exp' <- fullExpandTerm exp
                   return $ FunctionDef (Just exp') (FnT args' mva retty')
      _ -> do args' <- forM args $ \(pos, v, b, dir, ty) -> do
                ty' <- fullExpandTerm ty
                return (pos, v, b, dir, ty')
              retty' <- fullExpandTerm retty
              return $ FunctionDef Nothing (FnT args' mva retty')
  StructDef members -> StructDef <$> do
    forM members $ \(v, (vpos, exty, inty)) -> do
      exty' <- fullExpandTerm exty
      inty' <- fullExpandTerm inty
      addBinding vpos v inty'
      return (v, (vpos, exty', inty'))
  ValueDef mexp ty -> do
    ty' <- fullExpandTerm ty
    case mexp of
      Just exp -> do
        exp' <- fullExpandTerm exp
        return $ ValueDef (Just exp') ty'
      Nothing -> return $ ValueDef Nothing ty'
  TypeDef ty -> do
    ty' <- fullExpandTerm ty
    return $ TypeDef ty'
  InlineCDef {} -> return $ definition def

class Unifiable a where
  unify :: Tag SourcePos -> a -> a -> UM a

-- | Unifies after normalizing types
unifyN :: (Unifiable a, TermMappable a) => Tag SourcePos -> a -> a -> UM a
unifyN pos x y = do x' <- normalizeTypesM x
                    y' <- normalizeTypesM y
                    unify pos x' y'

instance Unifiable Type where
  unify pos (TypeHoleJ v) y = unifyTVar pos v y
  unify pos x (TypeHoleJ v) = unifyTVar pos v x

  -- See note [Dense matrix rules]
  unify pos (VecType DenseMatrix [] ty1) y = unify pos ty1 y
  unify pos x (VecType DenseMatrix [] ty2) = unify pos x ty2
  unify pos (VecType DenseMatrix (idx1:idxs1) ty1) (VecType DenseMatrix (idx2:idxs2) ty2) = do
    idx <- unifyArithmetic pos idx1 idx2
    subvecty <- unify pos (VecType DenseMatrix idxs1 ty1) (VecType DenseMatrix idxs2 ty2)
    return $ normalizeTypes $ VecType DenseMatrix [idx] subvecty
  unify pos (VecType st1 idxs1 ty1) (VecType st2 idxs2 ty2) | st1 == st2 && length idxs1 == length idxs2  = do
    ty' <- unify pos ty1 ty2
    idxs' <- forM (zip idxs1 idxs2) $ \(i1, i2) -> unifyArithmetic pos i1 i2
    return $ VecType st1 idxs' ty'
  unify pos (TupleType tys1) (TupleType tys2) | length tys1 == length tys2 = do
    tys <- forM (zip tys1 tys2) $ \(ty1, ty2) -> unify pos ty1 ty2
    return $ TupleType tys
  unify pos x@(FnType _) (FnType _) = return x -- TODO handle this better (or at all? it shouldn't show up)
  -- IntType loses to FloatType
  unify pos (IntType {}) y@(FloatType {}) = return y
  unify pos x@(FloatType {}) (IntType {}) = return x
  -- integers can go into bigger sizes
  unify pos (IntType t1) (IntType t2) = return $ IntType $ intMerge t1 t2
  unify pos (FloatType t1) (FloatType t2) = return $ FloatType $ floatMerge t1 t2

  unify pos StringType StringType = return StringType
  unify pos BoolType BoolType = return BoolType

  unify pos (PtrType a1) (PtrType a2) = do
    a' <- unify pos a1 a2
    return $ PtrType a'

  unify pos s@(StructType v1 _) (StructType v2 _) | v1 == v2  = return s

  -- Expand about enough for unification (for handling mutual recursion)
  unify pos s@(TypedefType _ v1) (TypedefType _ v2) | v1 == v2 = return s
  unify pos s@(TypedefType _ v1) ty2 = do ty1 <- normalizeTypesM s
                                          unify pos ty1 ty2
  unify pos ty1 s@(TypedefType _ v2) = do ty2 <- normalizeTypesM s
                                          unify pos ty1 ty2

  unify pos x y = do addUError $ UTyFailure pos x y
                     return x

-- N.B. This instance mainly shows up in index unification
instance Unifiable CExpr where
  unify pos (HoleJ pos1 v) y = do ex <- unifyEVar pos1 v y
--                                      exty <- typeCheck ex
--                                      unify pos ty1 exty
                                  return ex
  unify pos x y@(HoleJ {}) = unify pos y x

  -- skipping Vec/For
  -- skipping Return/Assert

  unify pos (RangeVal pos1 rng1) (RangeVal pos2 rng2) = RangeVal pos' <$> unify pos' rng1 rng2
    where pos' = MergeTags [pos1, pos2]

  unify pos (If pos1 a1 b1 c1) (If pos2 a2 b2 c2) =
    If pos' <$> unify pos' a1 a2 <*> unify pos' b1 b2 <*> unify pos' c1 c2
    where pos' = MergeTags [pos1, pos2]

  unify pos x@(IntLit {}) y@(IntLit {}) | x == y  = return x
  unify pos x@(FloatLit {}) y@(FloatLit {}) | x == y  = return x
  unify pos x@(StrLit {}) y@(StrLit {}) | x == y = return x
  unify pos x@(BoolLit {}) y@(BoolLit {}) | x == y = return x

  unify pos (VecLit pos1 ty1 xs1) (VecLit pos2 ty2 xs2)  | length xs1 == length xs2 = do
    ty' <- unify pos' ty1 ty2
    xs' <- forM (zip xs1 xs2) $ \(x1, x2) -> unify pos' x1 x2
    return $ VecLit pos' ty' xs'
    where pos' = MergeTags [pos1, pos2]

  unify pos (TupleLit pos1 xs1) (TupleLit pos2 xs2) | length xs1 == length xs2 = do
    xs <- forM (zip xs1 xs2) $ \(x1, x2) -> unify pos' x1 x2
    return $ TupleLit pos' xs
    where pos' = MergeTags [pos1, pos2]

  -- skipping Let
  -- skipping Uninitialized

  unify pos x@(Seq pos1 a1 b1) y@(Seq pos2 a2 b2) = Seq pos' <$> unify pos' a1 b1 <*> unify pos' a2 b2
    where pos' = MergeTags [pos1, pos2]

  -- skipping App
  unify pos (ConcreteApp pos1 f1 args1 rty1) (ConcreteApp pos2 f2 args2 rty2) | length args1 == length args2 = do
    f' <- unify pos' f1 f2
    args' <- forM (zip args1 args2) $ \(a1, a2) -> unify pos' a1 a2
    rty' <- unify pos' rty1 rty2
    return $ ConcreteApp pos' f' args' rty'
    where pos' = MergeTags [pos1, pos2]

  unify pos (Get pos1 loc1) (Get pos2 loc2) = do
    spec1 <- spec loc1
    spec2 <- spec loc2
    case (spec1, spec2) of
      (Just s1, Just s2) -> unify pos s1 s2
      (Just s1, _) -> unify pos s1 (Get pos2 loc2)
      (_, Just s2) -> unify pos (Get pos1 loc1) s2
      _ -> Get pos' <$> unify pos' loc1 loc2
    where pos' = MergeTags [pos1, pos2]
          spec (Ref _ v) = lookupSpecialization v
          spec _ = return Nothing
  unify pos (Addr pos1 loc1) (Addr pos2 loc2) = Addr pos' <$> unify pos' loc1 loc2
    where pos' = MergeTags [pos1, pos2]
  unify pos (Set pos1 loc1 v1) (Set pos2 loc2 v2) = Set pos' <$> unify pos' loc1 loc2 <*> unify pos' v1 v2
    where pos' = MergeTags [pos1, pos2]

  -- skipping AssertType  TODO handle it later?

  -- TODO Perhaps need algebraic simplification?
  unify pos (Unary pos1 op1 a1) (Unary pos2 op2 a2)
    | op1 == op2 =
      Unary pos' op1 <$> unify pos' a1 a2
    where pos' = MergeTags [pos1, pos2]
  unify pos (Binary pos1 op1 a1 b1) (Binary pos2 op2 a2 b2)
    | op1 == op2 =
      Binary pos' op1 <$> unify pos' a1 a2 <*> unify pos' b1 b2
    where pos' = MergeTags [pos1, pos2]

  unify pos x y = do addUError $ UExFailure pos x y
                     return x

instance Unifiable (Location CExpr) where
  unify pos x@(Ref _ v1) (Ref _ v2) | v1 == v2   = return x
  -- The rules for Index may be incorrect: (see [indexing rules])
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
unifyEVar pos v1 (HoleJ posv2 v2)
  | v1 == v2  = return (HoleJ (MergeTags [pos, posv2]) v1)
  | otherwise = do mb1 <- getUExprBinding v1
                   case mb1 of
                    Just (pos1, b1) -> unify (MergeTags [pos, posv2, pos1])
                                       b1 (HoleJ posv2 v2)
                    Nothing ->
                      do mb2 <- getUExprBinding v2
                         case mb2 of
                          Just (pos2, b2) -> unify (MergeTags [pos, posv2, pos2])
                                             (HoleJ (MergeTags [pos, posv2, pos2]) v1) b2
                          Nothing -> do addUExprBinding pos v1 (HoleJ (MergeTags [pos, posv2]) v2)
                                        return $ HoleJ (MergeTags [pos, posv2]) v2
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
   _ -> do addUError $ UError pos "Expecting integer."
           return defaultIntType

expectFloat :: Tag SourcePos -> Type -> UM FloatType
expectFloat pos ty = do
  ty' <- unify pos ty (FloatType defaultFloatType)
  case ty' of
    FloatType t -> return t
    _ -> do addUError $ UError pos "Expecting float."
            return defaultFloatType

expectBool :: Tag SourcePos -> Type -> UM ()
expectBool pos ty = do
  ty' <- unify pos ty BoolType
  return ()

isZero :: CExpr -> Bool
isZero (IntLit _ _ 0) = True
isZero _ = False

unifyArithmetic :: Tag SourcePos -> CExpr -> CExpr -> UM CExpr
unifyArithmetic pos x y = do
  unify pos x x
  unify pos y y
  x <- expandTerm x
  y <- expandTerm y
  let zq = reduceArithmetic (x - y)
  case substForm zq of
    Nothing -> do
      when (not $ isZero zq) $
        void $ unify pos (reduceArithmetic x) (reduceArithmetic y)
--        addUError $ UExFailure pos (reduceArithmetic x) (reduceArithmetic y)
    Just p@(var, e) -> do
      void $ unify pos (reduceArithmetic e) (HoleJ pos var)
  return $ reduceArithmetic x

typeCheckType :: Tag SourcePos -> Type -> UM Type
typeCheckType pos (VecType st idxs ty) = do
  idxs' <- forM idxs $ \idx -> do
    idxty <- typeCheck idx
    expectInt pos idxty
    return idx
  ty' <- typeCheckType pos ty
  case st of
    DenseMatrix -> return ()
    DiagonalMatrix -> checkSqrType idxs >> return ()
    UpperTriangular -> checkSqrType idxs >> return ()
    UpperUnitTriangular -> checkSqrType idxs >> return ()
    LowerTriangular -> checkSqrType idxs >> return ()
    LowerUnitTriangular -> checkSqrType idxs >> return ()
    SymmetricMatrix -> checkSqrType idxs >> return ()
  return $ VecType st idxs' ty'
  where checkSqrType [m, n] = do unifyArithmetic pos m n
                                 return ()
        checkSqrType _ = addUError $ UError pos "Expecting two-dimensional vector type."
typeCheckType pos (TupleType tys) = TupleType <$> mapM (typeCheckType pos) tys
typeCheckType pos (FnType fn) = do  -- Adds function parameters as bindings
  let (FnT args mva retty) = fn
  args' <- forM args $ \(vpos, v, b, dir, vty) -> do
    vty' <- typeCheckType vpos vty
    addBinding vpos v vty' -- assumes bindings cleared between functions
    return (vpos, v, b, dir, vty')
  retty' <- typeCheckType pos retty
  return $ FnType $ FnT args' mva retty' -- N.B. this is the effective func type
typeCheckType pos t@(IntType {}) = return t
typeCheckType pos t@(FloatType {}) = return t
typeCheckType pos StringType = return StringType
typeCheckType pos BoolType = return BoolType
typeCheckType pos (PtrType ty) = PtrType <$> typeCheckType pos ty
typeCheckType pos t@(TypedefType _ _) = return t -- it is perfect as it is
typeCheckType pos t@(StructType v (ST fields)) = return t
typeCheckType pos t@(TypeHole {}) = expandTerm t

typeCheck :: CExpr -> UM Type
typeCheck (Vec pos v range body) = do
  rt <- typeCheckRange pos range
  -- alpha renamed, so can just add v to scope
  addBinding pos v (IntType rt)
  bt <- typeCheck body
  when (refOccursIn v bt) $ do
    addUError $ URefOccurs pos v bt
  return $ VecType DenseMatrix [rangeLength pos range] bt
typeCheck (For pos v range body) = do
  rt <- typeCheckRange pos range
  -- alpha renamed, so can just add v to scope
  addBinding pos v (IntType rt)
  typeCheck body
  return Void
typeCheck (While pos test body) = do
  expectBool pos =<< typeCheck test
  typeCheck body
  return Void
typeCheck (Return pos ty a) = do
  mretty <- uRetType <$> get
  aty <- typeCheck a
  case mretty of
    Nothing -> addUError $ UError pos "Unexpected 'return' outside function."
    Just (pos', retty) -> void $ unify (MergeTags [pos, pos']) aty retty
  return ty
typeCheck (Assert pos a) = do
  expectBool pos =<< typeCheck a
  return Void
typeCheck (RangeVal pos range) = do
  rt <- typeCheckRange pos range
  return $ VecType DenseMatrix [rangeLength pos range] (IntType rt)
typeCheck (If pos a b c) = do
  tya <- typeCheck a
  expectBool pos tya
  tyb <- typeCheck b
  tyc <- typeCheck c
  unify pos tyb tyc
typeCheck (Specialize pos v cases dflt) = do
  Just (vpos, vty) <- getBinding v
  _ <- expectInt pos vty
  dty <- typeCheck dflt
  forM_ cases $ \(cond, cons) -> do
    consty <- withSpecialization v (fromInteger cond) $ typeCheck cons
    unify pos consty dty
  return dty
typeCheck (IntLit pos ty _) = return $ IntType ty
typeCheck (FloatLit pos ty _) = return $ FloatType ty
typeCheck (StrLit {}) = return $ StringType
typeCheck (BoolLit {}) = return $ BoolType
typeCheck (VecLit pos ty []) = typeCheckType pos ty
typeCheck (VecLit pos ty xs) = do
  xtys <- mapM typeCheck xs
  -- Take care to unify against ty last so that ty doesn't become wrong number type too early:
  ty' <- foldM (unify pos) (head xtys) $ tail xtys ++ [ty]
  return $ normalizeTypes $ VecType DenseMatrix [IntLit pos defaultIntType (fromIntegral $ length xs)] ty'
typeCheck (TupleLit pos xs) = TupleType <$> mapM typeCheck xs
typeCheck (Let pos v x body) = do
  tyx <- typeCheck x
  addBinding pos v tyx -- alpha renamed, so ok
  bt <- typeCheck body
  when (refOccursIn v bt) $ do
    addUError $ URefOccurs (MergeTags [pos, getTag body]) v bt
  return bt
typeCheck (Uninitialized pos ty) = typeCheckType pos ty
typeCheck (Seq pos a b) = do
  typeCheck a
  typeCheck b
-- skip App
typeCheck (ConcreteApp pos (Get _ (Ref _ v)) args rty) = do
  Just (gpos, (FnType fty)) <- getBinding v
  FnEnv fargs mva ret <- universalizeFunType fty
  when (length args < length fargs || (not mva && length args > length fargs)) $ do
    addUError $ UError (MergeTags [pos, gpos]) "COMPILER ERROR. Incorrect number of arguments."
  forM_ (zip args fargs) $ \(arg, (vpos, v, vty)) -> do
    unify (MergeTags [vpos, pos, gpos]) arg (HoleJ pos v)
    tyarg <- typeCheck arg
    unify (MergeTags [vpos, pos, gpos]) tyarg vty
  when  mva $ forM_ (drop (length $ zip args fargs) args) $ typeCheck
  unify (MergeTags [pos, gpos]) rty ret
  return ret
typeCheck t@(HoleJ pos v) = do
  t' <- expandTerm t
  ty' <- case t' of
    HoleJ pos' v' -> typeCheckType pos' (TypeHoleJ v')
    _ -> typeCheck t'
  unify pos ty' (TypeHoleJ v)
typeCheck (Get pos loc) = do
  tyloc <- typeCheckLoc pos loc
  return $ normalizeTypes tyloc
typeCheck (Addr pos loc) = do
  tyloc <- typeCheckLoc pos loc
  return $ PtrType tyloc
typeCheck (Set pos loc v) = do
  tyloc <- typeCheckLoc pos loc >>= expandTerm >>= normalizeTypesM
  tyv <- typeCheck v >>= expandTerm >>= normalizeTypesM
  unifySet tyloc tyv
  return $ Void
  where unifySet :: Type -> Type -> UM ()
        unifySet (VecType _ [] bty1) ty2 = unifySet bty1 ty2
        unifySet ty1 (VecType _ [] bty2) = unifySet ty1 bty2
        unifySet (VecType st1 (idx1:idxs1) bty1) (VecType st2 (idx2:idxs2) bty2)
          = do unifyArithmetic pos idx1 idx2
               unifySet (VecType st1 idxs1 bty1) (VecType st2 idxs2 bty2)
        unifySet ty1 ty2 = void $ unify pos ty1 ty2
typeCheck (AssertType pos v ty) = do
  vty <- typeCheck v
  ty' <- typeCheckType pos ty
  _ <- unifyN pos vty ty'
  return ty'
typeCheck (Unary pos op a) | op `elem` [Pos, Neg] = do
  aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
  numTypeVectorize pos aty aty
typeCheck (Unary pos Not a) = do
  aty <- typeCheck a
  expectBool pos aty
  return BoolType
typeCheck (Unary pos Sum a) = do
  aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
  aty' <- numTypeVectorize pos aty aty -- HACK (but ok)
  case aty' of
   VecType _ (idx:idxs) aty'' -> return $ normalizeTypes $ VecType DenseMatrix idxs aty''
   _ -> return aty'
typeCheck (Unary pos Inverse a) = do
  aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
  case aty of
   VecType _ [i1, i2] aty' -> do i' <- unify pos i1 i2
                                 aty'' <- unify pos aty' (FloatType defaultFloatType)
                                 return $ VecType DenseMatrix [i', i'] aty''
   _ -> do addUError $ UError pos "Inverse must be of a square matrix."
           TypeHoleJ <$> gensym "inverse"
typeCheck (Unary pos Transpose a) = do
  aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
  case aty of
   VecType _ (i1:i2:idxs) aty' -> return $ VecType DenseMatrix (i2:i1:idxs) aty'
   VecType _ [idx] aty' -> return $ VecType DenseMatrix [1,idx] aty'
   _ -> do addUError $ UError pos "Transpose must be of a vector."
           TypeHoleJ <$> gensym "transpose"
typeCheck (Unary pos Diag a) = do
  aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
  case aty of
    VecType _ (i1:idxs) aty' -> do mapM_ (unifyArithmetic pos i1) idxs
                                   return $ VecType DenseMatrix [i1] aty'
    _ -> do addUError $ UError pos "Diag must be of a vector."
            TypeHoleJ <$> gensym "diag"
typeCheck (Unary pos Shape a) = do
  aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
  sh <- doShape aty
  return $ VecType DenseMatrix [fromIntegral sh] (IntType defaultIntType)
  where doShape :: Type -> UM Int
        doShape (VecType _ [] aty') = doShape aty'
        doShape (VecType _ idxs aty') = (length idxs +) <$> doShape aty'
        doShape (TypedefType tdty _) = doShape tdty
        doShape v@(TypeHoleJ _) = do unify pos v (FloatType defaultFloatType)
                                     return 0
        doShape _ = return 0
typeCheck (Unary pos (VecCons st) a) = do
  aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
  case (st,aty) of
    (DiagonalMatrix, VecType _ [i1] bty) ->
      do bty' <- arithType pos bty bty -- since we must ensure it's not the next case
         typeCheckType pos $ VecType DiagonalMatrix [i1, i1] bty'
    (_, VecType _ (i1:_:bnds) bty) ->
      typeCheckType pos $ VecType st [i1,i1] (VecType st bnds bty)
    _ -> do idx <- HoleJ pos <$> gensym "idx"
            base <- TypeHoleJ <$> gensym "base"
            aty' <- unify pos aty (VecType DenseMatrix [idx,idx] base)
            case aty' of
              VecType _ (i1:_:bnds) bty -> typeCheckType pos $ VecType st [i1,i1]
                                           (VecType DenseMatrix bnds bty)
              _ -> do addUError $ UError pos "Matrix constructor expecting vector."
                      return aty'
typeCheck (Unary pos op a) = do error $ "unary " ++ show op ++ " not implemented"
typeCheck (Binary pos op a b)
  | op `elem` [Add, Sub, Hadamard, Div]  = do
      aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
      bty <- typeCheck b >>= expandTerm >>= normalizeTypesM
      numTypeVectorize pos aty bty
  | op == Pow = do
      aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
      bty <- typeCheck b >>= expandTerm >>= normalizeTypesM
      aty' <- unify pos aty (IntType defaultIntType)
      bty' <- unify pos bty (IntType defaultIntType)
      return $ case (aty', bty') of
        (IntType ai, IntType {}) -> IntType $ promoteInt ai
        (FloatType af, FloatType bf) -> FloatType $ arithFloat af bf
        (_, FloatType bf) -> FloatType $ promoteFloat bf
        (FloatType af, _) -> FloatType $ promoteFloat af
  | op == Mul  = do
      aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
      bty <- typeCheck b >>= expandTerm >>= normalizeTypesM
      case (aty, bty) of
       (VecType _ [a, b1] aty', VecType _ [b2, c] bty') -> do
         _ <- unifyArithmetic pos b1 b2
         ty' <- arithType pos aty' bty'
         return $ VecType DenseMatrix [a, c] ty'
       (VecType _ [a] aty', VecType _ [b2, c] bty') -> do -- Left vector is treated as column vector matrix (n x 1)
         _ <- unifyArithmetic pos 1 b2
         ty' <- arithType pos aty' bty'
         return $ VecType DenseMatrix [a, c] ty'
       (VecType _ [a, b1] aty', VecType _ [b2] bty') -> do -- Right vector is treated as column vector (result is vector)
         _ <- unifyArithmetic pos b1 b2
         ty' <- arithType pos aty' bty'
         return $ VecType DenseMatrix [a] ty'
       (VecType _ [a1] aty', VecType _ [a2] bty') -> do -- Special case: vector times vector is dot product
         _ <- unifyArithmetic pos a1 a2
         ty' <- arithType pos aty' bty'
         return $ ty'
       (VecType {}, VecType {}) -> do
         addUError $ UError pos "Only 1-d and 2-d vectors may be multiplied."
         return $ TypeHole Nothing
       _ -> typeCheck $ Binary pos Hadamard a b
  | op == Concat = do
      aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
      bty <- typeCheck b >>= expandTerm >>= normalizeTypesM
      case (aty, bty) of
       (VecType _ (aidx:aidxs) aty', VecType _ (bidx:bidxs) bty') -> do
         ty' <- unify pos (VecType DenseMatrix aidxs aty') (VecType DenseMatrix bidxs bty')
         typeCheckType pos $ normalizeTypes $ VecType DenseMatrix [Binary pos Add aidx bidx] ty'
       _ -> do addUError $ UError pos "Bad argument types to concatenation operator."
               hole <- gensym "concat"
               return $ TypeHoleJ hole
  | op `elem` [EqOp, NEqOp, LTOp, LTEOp] = do
      aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
      bty <- typeCheck b >>= expandTerm >>= normalizeTypesM
      _ <- arithType pos aty bty
      return BoolType
  | op `elem` [And, Or] = do
      aty <- typeCheck a
      bty <- typeCheck b
      expectBool pos aty
      expectBool pos bty
      return BoolType
  | otherwise = error $ "binary " ++ show op ++ " not implemented"

numTypeVectorize :: Tag SourcePos -> Type -> Type -> UM Type
numTypeVectorize pos ty1 ty2 =
  case (ty1, ty2) of
   (VecType _ [] bty1, ty2) -> numTypeVectorize pos bty1 ty2
   (ty1, VecType _ [] bty2) -> numTypeVectorize pos ty1 bty2
   (VecType _ (idx1:idxs1) bty1, VecType _ (idx2:idxs2) bty2)  -> do
     idx' <- unifyArithmetic pos idx1 idx2
     normalizeTypes <$> (VecType DenseMatrix [idx'] <$> numTypeVectorize pos
                         (VecType DenseMatrix idxs1 bty1) (VecType DenseMatrix idxs2 bty2))
   (VecType _ idxs1 bty1, ty2)  -> do
     bty' <- numTypeVectorize pos bty1 ty2
     return $ VecType DenseMatrix idxs1 bty'
   (ty1, VecType _ idxs2 bty2) -> do
     bty' <- numTypeVectorize pos ty1 bty2
     return $ VecType DenseMatrix idxs2 bty'
   (ty1, ty2) -> arithType pos ty1 ty2

arithType :: Tag SourcePos -> Type -> Type -> UM Type
arithType pos ty1 ty2 = do ty1' <- expandTerm ty1
                           ty2' <- expandTerm ty2
                           arithType' ty1' ty2'
  where arithType' :: Type -> Type -> UM Type
        arithType' ty1 ty2 = case (ty1, ty2) of
          (TypeHoleJ {}, _) -> do ty1' <- unify pos (IntType defaultIntType) ty1
                                  arithType' ty1' ty2
          (_, TypeHoleJ {}) -> do ty2' <- unify pos (IntType defaultIntType) ty2
                                  arithType' ty1 ty2'
          (IntType t1, IntType t2) -> return $ IntType $ arithInt t1 t2
          (FloatType t1, IntType {}) -> return $ FloatType $ promoteFloat t1
          (IntType {}, FloatType t2) -> return $ FloatType $ promoteFloat t2
          (FloatType t1, FloatType t2) -> return $ FloatType $ arithFloat t1 t2
          _ -> do addUError $ UError pos "Invalid types for arithmetic."
                  return $ IntType defaultIntType

-- Ranges must give signed integers because they might be counting
-- down to zero.
typeCheckRange :: Tag SourcePos -> Range CExpr -> UM IntType
typeCheckRange pos (Range from to step) = do
  t1 <- typeCheck from >>= expectInt pos
  t2 <- typeCheck to >>= expectInt pos
  t3 <- typeCheck step >>= expectInt pos
  let ty = intMerge S32 $ arithInt (arithInt t1 t2) t3
  when (intUnsigned ty) $
    addUError $ UError (MergeTags [pos, getTag from, getTag to, getTag step])
      "Range integer type became unsigned, but it must be signed."
  return ty

typeCheckLoc :: Tag SourcePos -> Location CExpr -> UM Type
typeCheckLoc pos (Ref _ v) = do -- We DO NOT unify against the type of the Ref.  Filled in later.
  Just (vpos, vty) <- getBinding v
  return vty
typeCheckLoc pos (Index a idxs) = do -- see note [indexing rules] and see `getLocType`
  aty <- typeCheck a >>= expandTerm >>= normalizeTypesM
  normalizeTypes <$> typeCheckIdx aty idxs aty
  where typeCheckIdx :: Type -- ^ type of 'a' (never changes)
                        -> [CExpr] -- ^ indexes
                        -> Type -- ^ type of 'a' (recursively destructured)
                        -> UM Type -- ^ type after indexing
        typeCheckIdx oty [] aty = normalizeTypesM aty
        typeCheckIdx oty (idx:idxs) aty@(VecType _ (ibnd:_) _) = do
          unifyRangeIndex pos idx ibnd
          idxty <- typeCheck idx
          typeCheckIdxty oty idxty idxs aty
        typeCheckIdx oty (idx:idxs) ty = do
          addUError $ UGenTyError pos oty "Too many indices on expression of type"
          return ty

        typeCheckIdxty :: Type -> Type -> [CExpr] -> Type -> UM Type
        typeCheckIdxty oty idxty idxs (VecType st ibnds bty) =
          case normalizeTypes idxty of
           VecType st' idxs' idxtybase -> -- result shape equals shape of index
             VecType st' idxs' <$> (typeCheckIdxty oty idxtybase idxs $ VecType st ibnds bty)
           ty -> do nidxs <- iSize ty
                    when (nidxs > length ibnds) $
                      addUError $ UGenTyError pos oty "Too many indices on expression of type"
                    typeCheckIdx oty idxs (VecType DenseMatrix (drop nidxs ibnds) bty)

        iSize :: Type -> UM Int
        iSize (IntType {}) = return 1
        iSize (TupleType tys) = sum <$> mapM iSize tys
        iSize ty = iSize . IntType =<< expectInt pos ty -- Default to int

        unifyRangeIndex pos idx ibound = do
          case idx of
            -- N.B. this is a special case so that ranges with
            -- unbounded top are unified to the length of the
            -- underlying vector. Otherwise, the unbounded slice will
            -- have a length determined by uses of the vector slice.
           RangeVal rpos (Range { rangeTo = h@(HoleJ {}) }) ->
             unify (MergeTags [pos, rpos]) h ibound >> return ()
           _ -> return ()
typeCheckLoc pos (Field a field) = do
  aty <- typeCheck a
  aty' <- stripPtr aty
  case aty' of
   StructType v (ST fields) -> case lookup field fields of
     Just (fpos, _, fieldTy) -> return $ structField fields a fieldTy
     Nothing -> do addUError $ UNoField pos field
                   TypeHoleJ <$> gensym "field"
   _ -> do addUError $ UError pos $ "Expecting struct when accessing field " ++ show field ++ " (not " ++ show (pretty aty') ++ ")"
           TypeHoleJ <$> gensym "field"
  where stripPtr (PtrType aty) = stripPtr aty
        stripPtr ty@(TypedefType {}) = stripPtr =<< baseExpandTypedefM ty
        stripPtr aty = return aty
typeCheckLoc pos (Deref a) = do
  aty <- typeCheck a
  g <- gensym "deref"
  aty' <- unify pos aty (PtrType (TypeHoleJ g))
  case aty' of
   PtrType dty -> return dty
   _ -> return (TypeHoleJ g)

-- | The boolean is whether this allows varargs
data FunctionEnv = FnEnv [(Tag SourcePos, Variable, Type)] Bool Type
                 deriving Show

-- | When unifying against a function type, it is something like
-- calling a function or evaluating a Prolog rule.  One way to model
-- this is by instantiating a new version of it with all of its
-- variables replaced with fresh symbols.
universalizeFunType :: FunctionType -> UM FunctionEnv
universalizeFunType ft = do
  let ft'@(FnT args mva retty)= ft
  repAList <- forM args $ \(pos, v, req, dir, ty) -> do
    v' <- gensym v
    return (v, v')
  let vMap = M.fromList repAList
  args' <- forM args $ \(pos, v, req, dir, ty) -> do
    uty <- universalizeTypeVars vMap ty
    addUTypeBinding pos (vMap M.! v) uty
    return (pos, vMap M.! v, uty)
  uretty <- universalizeTypeVars vMap retty
  return $ FnEnv args' (isJust mva) uretty


universalizeTypeVars :: M.Map Variable Variable -> Type -> UM Type
universalizeTypeVars repMap ty = traverseTerm tty texp tloc trng ty
  where tty = return
        texp expr = case expr of
          Get pos (Ref ty v) -> case M.lookup v repMap of
            Just v' -> return $ HoleJ pos v'
            Nothing -> return expr
          Addr pos (Ref ty v) -> case M.lookup v repMap of
            -- TODO this is an example of impedance mismatch between Ref and Hole
            Just {} -> error "Embarassingly, you cannot dependently use the address of an argument."
            Nothing -> return expr
          _ -> return expr
        tloc = return
        trng = return
