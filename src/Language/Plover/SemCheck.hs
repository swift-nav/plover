module Language.Plover.SemCheck where

import Debug.Trace
import Language.Plover.Types
import Language.Plover.UsedNames
import Language.Plover.Unify hiding (gensym)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Tag
import Data.Function
import Data.Maybe
import Control.Monad
import Control.Monad.State
import Text.ParserCombinators.Parsec (SourcePos)

data SemError = SemError (Tag SourcePos) String
              | SemUnbound (Tag SourcePos) Variable
              | SemUnboundType (Tag SourcePos) Variable
              | SemUniError UnificationError
              deriving (Show, Eq, Ord)

data SemCheckData = SemCheckData
                    { semErrors :: [SemError]
                    , gensymState :: [String] -- already-used variables
                    , globalBindings :: Map Variable DefBinding
                    , localBindings :: Map Variable (Tag SourcePos, Variable) -- for α-renaming
                    }
                  deriving Show

newSemCheckData :: [UVar] -> SemCheckData
newSemCheckData vs = SemCheckData
                     { semErrors = []
                     , gensymState = vs
                     , globalBindings = M.empty
                     , localBindings = M.empty
                     }


runSemChecker :: SemChecker v -> Either [SemError] v
runSemChecker m = let (v, s) = runState m (newSemCheckData [])
                  in case semErrors s of
                      [] -> Right v
                      errs -> Left errs

doSemCheck :: [DefBinding] -> Either [SemError] [DefBinding]
doSemCheck defs = runSemChecker dochecks
  where dochecks = do modify $ \state -> state { gensymState = allToplevelNames defs }
                      condenseBindings defs
                      globalFillHoles
                      defs' <- (M.elems . globalBindings <$> get) >>= mapM fillHoles
                      modify $ \state -> state { globalBindings = M.fromList [(binding d, d) | d <- defs'] }
                      defs' <- M.elems . globalBindings <$> get

                      he <- hasErrors
                      if not he
                        then case runUM defs' (typeCheckToplevel defs') of
                              Right defs'' -> return defs''
                              Left errs -> do mapM_ (addError . SemUniError) errs
                                              return []
                        else return []
--                      globalBindings <$> get


gensym :: String -> SemChecker String
gensym prefix = do names <- gensymState <$> get
                   gensym' names (length names)
  where gensym' :: [String] -> Int -> SemChecker String
        gensym' names i = let newName = prefix ++ "$" ++ show i
                          in if newName `elem` names
                             then gensym' names (1 + i)
                             else do modify $ \state -> state { gensymState = newName : gensymState state }
                                     return newName

-- | Generates a fresh variable name.
genVar :: SemChecker Variable
genVar = gensym ""

genUVar :: SemChecker UVar
genUVar = gensym ""

type SemChecker = State SemCheckData

addError :: SemError -> SemChecker ()
addError e = do sd <- get
                put $ sd { semErrors = semErrors sd ++ [e] }

hasErrors :: SemChecker Bool
hasErrors = not . null . semErrors <$> get

-- | Adds the error to the error list of the condition is false.
semAssert :: Bool -> SemError -> SemChecker ()
semAssert b e = if b then return () else addError e

lookupGlobalType :: Variable -> SemChecker (Maybe Type)
lookupGlobalType v = do bindings <- globalBindings <$> get
                        case M.lookup v bindings of
                         Just def -> return $ Just $ definitionType def
                         Nothing -> return Nothing

lookupSym :: Variable -> SemChecker (Maybe (Maybe Type, Variable))
lookupSym v = do bindings <- localBindings <$> get
                 case M.lookup v bindings of
                  Just (pos, v') -> return $ Just (Nothing, v')
                  Nothing -> do mt <- lookupGlobalType v
                                case mt of
                                 Just _ -> return $ Just (mt, v)
                                 Nothing -> return Nothing

resetLocalBindings :: SemChecker ()
resetLocalBindings = modify $ \state -> state { localBindings = M.empty }

withNewScope :: SemChecker v -> SemChecker v
withNewScope m = do bindings <- localBindings <$> get
                    v <- m
                    modify $ \state -> state { localBindings = bindings }
                    return v

-- | adds a new binding, and if one already exists, return the tag for
-- it.  The v' is for α-renaming, and it should come from gensym.
addNewLocalBinding :: Tag SourcePos -> Variable -> Variable -> SemChecker (Maybe (Tag SourcePos))
addNewLocalBinding pos v v' = do bindings <- localBindings <$> get
                                 modify $ \state -> state { localBindings = M.insert v (pos, v')
                                                                            bindings }
                                 case M.lookup v bindings of
                                  Just (pos, _) -> return $ Just pos
                                  Nothing -> return Nothing

-- | Take the list of bindings and convert them into a map of
-- filled-out bindings.  This is to support prototypes.
condenseBindings :: [DefBinding] -> SemChecker ()
condenseBindings defs = do mapM_ addGlobalBinding defs

lookupGlobalBinding :: Variable -> SemChecker (Maybe DefBinding)
lookupGlobalBinding v = M.lookup v . globalBindings <$> get

-- | Adds a global binding, though if one already exists with that
-- name, attempts to reconcile.
addGlobalBinding :: DefBinding -> SemChecker ()
addGlobalBinding def = do molddef <- lookupGlobalBinding (binding def)
                          case molddef of
                           Just olddef -> reconcileBindings olddef def
                           Nothing -> newBinding def

-- | Determines whether a definition has a value definition.  Struct
-- declarations don't count as having values.  This is for the purpose
-- of seeing whether extern declarations have an associated value.
defHasValue :: DefBinding -> Bool
defHasValue (DefBinding { definition = def }) = case def of
  FunctionDef me _ -> isJust me
  StructDef _ -> False
  ValueDef me _ -> isJust me

-- | This is a new binding, not already in the SemChecker state.  Put
-- it there, and do some consistency checks.
newBinding :: DefBinding -> SemChecker ()
newBinding def = do
  modify $ \state -> state { globalBindings = M.insert (binding def) def (globalBindings state) }
  semAssert (not (extern def && defHasValue def)) $
    SemError (bindingPos def) "Extern definition cannot have value or function body."
  semAssert (not (extern def && static def)) $
    SemError (bindingPos def) "Cannot be both static and extern simultaneously."

-- | These two bindings are for the same variable.  Make sure they are
-- reconcilable, and bring them into a single binding (stored in the
-- SemChecker state)
reconcileBindings :: DefBinding -> DefBinding -> SemChecker ()
reconcileBindings oldDef newDef = do
  semAssert (extern oldDef || not (extern newDef)) $
    SemError rtag "Conflicting extern modifiers."
  semAssert (static oldDef || not (static newDef)) $
    SemError rtag "Conflicting static modifiers."
  semAssert (not (defHasValue oldDef)) $
    SemError rtag "Cannot redefine definition which already has a value or function body."
  semAssert (not (extern oldDef && defHasValue newDef)) $
    SemError rtag "Cannot give value to prototyped extern definition."
  definition' <- reconcileDefinitions rtag (definition oldDef) (definition newDef)
  let newDef' = oldDef { bindingPos = rtag
                       , definition = definition' }
      v = binding newDef'
  modify $ \state -> state { globalBindings = M.insert v newDef' (globalBindings state) }
  where rtag = MergeTags [bindingPos oldDef, bindingPos newDef]

reconcileDefinitions :: Tag SourcePos -> Definition -> Definition -> SemChecker Definition
reconcileDefinitions tag (FunctionDef oldMce oldFt) (FunctionDef newMce newFt) = do
  semAssert (oldFt == newFt) $ SemError tag "Inconsistent function types."
  return $ FunctionDef (oldMce `mplus` newMce) oldFt
reconcileDefinitions tag (ValueDef oldMce oldType) (ValueDef newMce newType) = do
  semAssert (oldType == newType) $ SemError tag "Inconsistent global variable types."
  return $ ValueDef (oldMce `mplus` newMce) oldType
reconcileDefinitions tag (StructDef oldMembers) (StructDef newMembers) = do
  semAssert (oldMembers == newMembers) $ SemError tag "Inconsistent structure definitions."
  return $ StructDef oldMembers
reconcileDefinitions tag oldDef newDef = do
  addError $ SemError tag "Redefinition of global variable with inconsistent types."
  return oldDef

-- | This fills the holes of each top-level type.  Later, we fill the
-- holes inside the expressions themselves.  This is so that type
-- holes are not propagated into the expressions.
globalFillHoles :: SemChecker ()
globalFillHoles = do defbs <- M.elems . globalBindings <$> get
                     defbs' <- forM defbs $ \defb -> do
                       let pos = bindingPos defb
                       resetLocalBindings
                       def' <- case (definition defb) of
                         FunctionDef mexp ft -> do ft' <- completeFunType pos ft
                                                   let mexp' = case getEffectiveFunType ft of
                                                         (_, Just (rv, rty)) ->
                                                           Set pos (Ref (TypeHole Nothing) rv) <$> mexp
                                                         _ -> mexp
                                                   return $ FunctionDef mexp' ft'
                         ValueDef mexp ty -> do ty' <- fillTypeHoles pos ty
                                                return $ ValueDef mexp ty'
                         StructDef members -> do
                           members' <- forM members $ \(v,ty) -> do
                             ty' <- fillTypeHoles pos ty
                             mtag <- addNewLocalBinding pos v v
                             case mtag of
                              Just otag -> do
                                addError $ SemError (MergeTags [otag, pos]) $
                                  "Redefinition of member " ++ show v ++ " in struct."
                              Nothing -> return ()
                             return (v, ty')
                           return $ StructDef members'
                       return $ defb { definition = def' }
                     modify $ \state -> state { globalBindings = M.fromList [(binding d, d) | d <- defbs'] }

completeFunType :: Tag SourcePos -> FunctionType -> SemChecker FunctionType
completeFunType pos ft = do let FnT args rty = ft
                            args' <- forM args $ \(v, req, vty) -> do
                              vty' <- fillTypeHoles pos vty
                              mglob <- lookupGlobalBinding v
                              when (isJust mglob) $ addError $
                                SemError (MergeTags [bindingPos (fromJust mglob), pos]) $
                                "Argument " ++ show v ++ " cannot mask global definition."
                              mlastpos <- addNewLocalBinding pos v v
                              case mlastpos of
                               Just otag -> do
                                 addError $ SemError (MergeTags [otag, pos]) $
                                   "Redefinition of argument " ++ show v ++ " in function type."
                               Nothing -> return ()
                              return (v, req, vty')
                            rty' <- fillTypeHoles pos rty
                            return $ FnT args' rty'
                                       
-- | Initializes the scope so that it has all of a functions parameters
withinFun :: Tag SourcePos -> FunctionType -> SemChecker a -> SemChecker a
withinFun pos ft m = withNewScope $ do
  let (FnT args rty, _) = getEffectiveFunType ft
  forM_ args $ \(v, req, vty) -> do
    void $ addNewLocalBinding pos v v
  m

-- | Fill holes in AST, add implicit arguments, check for undefined
-- variables, and α-rename.
fillHoles :: DefBinding -> SemChecker DefBinding
fillHoles defb = do resetLocalBindings
                    newDef <- if extern defb
                              then return (definition defb) -- already handled with globalFillHoles
                              else fillDefHoles (definition defb)
                    return $ defb { definition = newDef }

  where fillDefHoles :: Definition -> SemChecker Definition  -- Non-extern types may have holes
        fillDefHoles def = case def of
          FunctionDef mexp ft ->
            -- The function has already had its type completed
            case mexp of
             Nothing -> do addError $
                             SemError (bindingPos defb) "Function missing body."
                           return $ FunctionDef mexp ft
             Just exp -> withinFun (bindingPos defb) ft $ do exp' <- fillValHoles exp
                                                             return $ FunctionDef (Just exp') ft
          ValueDef mexp ty -> do mexp' <- case mexp of
                                           Just exp -> Just <$> fillValHoles exp
                                           Nothing -> return Nothing -- It is OK since it can get a C-default value
                                 return $ ValueDef mexp' ty -- and the type has been completed
          StructDef {} -> return def -- already handled

fillValHoles :: CExpr -> SemChecker CExpr
fillValHoles exp = case exp of
  Vec pos v range expr ->
    withNewScope $ do
      v' <- gensym v
      range' <- fillRangeHoles range
      _ <- addNewLocalBinding pos v v'
      expr' <- fillValHoles expr
      return $ Vec pos v' range' expr'
  Return pos v -> Return pos <$> fillValHoles v
  Assert pos a -> Assert pos <$> fillValHoles a
  RangeVal pos range -> RangeVal pos <$> fillRangeHoles range
  If pos a b c -> do [a', b', c'] <- mapM fillValHoles [a, b, c]
                     return $ If pos a' b' c'
  VoidExpr _ -> return exp
  IntLit _ _ _ -> return exp
  FloatLit _ _ _ -> return exp
  StrLit _ _ -> return exp
  BoolLit _ _ -> return exp
  VecLit pos exprs -> VecLit pos <$> mapM fillValHoles exprs
  Let pos v val expr -> do
    val' <- fillValHoles val
    withNewScope $ do
      v' <- gensym v
      _ <- addNewLocalBinding pos v v'
      expr' <- fillValHoles expr
      return $ Let pos v' val' expr'
  Uninitialized pos ty -> Uninitialized pos <$> fillTypeHoles pos ty
  Seq pos e1 e2 -> Seq pos <$> fillValHoles e1 <*> fillValHoles e2
  App pos fn@(Get _ (Ref _ f)) args -> do
    mf <- lookupGlobalType f
    case mf of
     Just (FnType ft) -> let (ft', mretvar) = getEffectiveFunType ft
                         in case mretvar of
                             Just (retvar, ty) -> do tv <- genVar
                                                     matched <- matchArgs pos
                                                                (args ++ [Arg $ Get pos (Ref (TypeHole Nothing) tv)])
                                                                ft'
                                                     fillValHoles $ Let pos tv (Uninitialized pos (TypeHole Nothing))
                                                       (Seq pos (ConcreteApp pos fn matched)
                                                        (Get pos (Ref (TypeHole Nothing) tv)))
                             Nothing -> (ConcreteApp pos fn <$> matchArgs pos args (withPossibleVoid ft)) >>= fillValHoles
     Just _ -> do addError $ SemError pos "Cannot call non-function."
                  return exp
     Nothing -> do addError $ SemError pos "No such global function."
                   return exp
  App pos _ _ -> do addError $ SemError pos "Cannot call expression."
                    return exp
  ConcreteApp pos fn@(Get _ (Ref _ f)) args -> do
    mf <- lookupGlobalType f
    case mf of
     Just (FnType ft@(FnT fargs ret)) -> do semAssert (length args == reqargs) $
                                              SemError pos "Incorrect number of arguments in function application."
                                            ConcreteApp pos <$> fillValHoles fn <*> mapM fillValHoles args
       where reqargs = let ((FnT fargs' _), mretvar) = getEffectiveFunType ft
                       in length fargs'
     Just _ -> do addError $ SemError pos "Cannot call non-function."
                  return exp
     Nothing -> do addError $ SemError pos "No such global function."
                   return exp
  ConcreteApp pos _ _ -> do addError $ SemError pos "Cannot call expression."
                            return exp
  Hole pos Nothing -> do name <- genUVar
                         ty <- genUVar
                         return $ HoleJ pos (TypeHoleJ ty) name
  Hole _ _ -> return exp
  Get pos loc -> Get pos <$> fillLocHoles pos loc
  Addr pos loc -> Addr pos <$> fillLocHoles pos loc
  Set pos loc val -> Set pos <$> fillLocHoles pos loc <*> fillValHoles val
  AssertType pos v ty -> do ty' <- fillTypeHoles pos ty
                            v' <- fillValHoles v
                            return $ AssertType pos v' ty'
  Unary pos op v -> Unary pos op <$> fillValHoles v
  Binary pos op v1 v2 -> Binary pos op <$> fillValHoles v1 <*> fillValHoles v2

fillTypeHoles :: Tag SourcePos -> Type -> SemChecker Type
fillTypeHoles pos ty = case ty of
  VecType idxs ety -> do ety' <- fillTypeHoles pos ety
                         idxs' <- mapM fillValHoles idxs
                         return $ VecType idxs' ety'
  Void -> return ty
  FnType (FnT args ret) -> do addError $ SemError pos "COMPILER ERROR. Scoping issues when filling type holes of function type."
                              return ty
  NumType -> return ty
  IntType mt -> return ty
  FloatType mt -> return ty
  StringType -> return ty
  BoolType -> return ty
  PtrType ty -> do ty' <- fillTypeHoles pos ty
                   return $ PtrType ty'
  TypedefType v -> do mty <- lookupGlobalType v
                      case mty of
                       Just (StructType {}) -> return () -- TODO reconsider types being in the same namespace as values.
                       Just _ -> addError $ SemError pos "Non-struct reference used as type."
                       Nothing -> addError $ SemUnboundType pos v
                      return ty
  StructType v st -> do mty <- lookupGlobalType v
                        case mty of
                         Just ty -> semAssert ((StructType v st) == ty) $
                                    SemError pos "COMPILER ERROR. Struct type differs from looked up type."
                         Nothing -> addError $ SemError pos "COMPILER ERROR. Struct type exists for non-existant type."
                        return ty
  TypeHole Nothing -> do name <- genUVar
                         return $ TypeHole (Just name)
  TypeHole _ -> return ty

fillLocHoles :: Tag SourcePos -> Location CExpr -> SemChecker (Location CExpr)
fillLocHoles pos loc = case loc of
  Ref ty v -> do mv' <- lookupSym v
                 case mv' of
                  Just (_, v') -> do ty' <- fillTypeHoles pos ty
                                     return $ Ref ty' v'
                  Nothing -> do addError $ SemUnbound pos v
                                return loc
  Index a idxs -> do a' <- fillValHoles a
                     idxs' <- mapM fillValHoles idxs
                     return $ Index a' idxs'
  Field a member -> do a' <- fillValHoles a
                       return $ Field a' member
  Deref a -> Deref <$> fillValHoles a

fillRangeHoles :: Range CExpr -> SemChecker (Range CExpr)
fillRangeHoles (Range from to step) = do [from', to', step'] <- mapM fillValHoles [from, to, step]
                                         return $ Range from' to' step'

-- | Match the arguments with the formal parameters for making a
-- ConcreteApp.  Note that this expects the effective type of the
-- function (i.e., the one where a complex return value is a pointer
-- argument).
matchArgs :: Tag SourcePos -> [Arg CExpr] -> FunctionType -> SemChecker [CExpr]
matchArgs pos args (FnT fargs _) = matchArgs' 1 args fargs
  where
    -- A passed argument matches a required argument
    matchArgs' i (Arg x : xs) ((v, True, ty) : fxs) = (x :) <$> matchArgs' (1 + i) xs fxs
    -- An omitted implicit argument is filled with a value hole
    matchArgs' i (Arg x : xs) ((v, False, ty) : fxs) = do name <- genUVar
                                                          ty <- genUVar
                                                          (HoleJ pos (TypeHoleJ ty) name :) <$> matchArgs' i (Arg x : xs) fxs
    -- (error) An implicit argument where a required argument is expected
    matchArgs' i (ImpArg x : xs) ((v, True, ty) : fxs) = do
      addError $ SemError pos $ "Unexpected implicit argument in position " ++ show i ++ "."
      matchArgs' (1 + i) xs ((v, True, ty) : fxs)
    -- An implicit argument given where an implicit argument expected
    matchArgs' i (ImpArg x : xs) ((v, False, ty) : fxs) = (x :) <$> matchArgs' (1 + i) xs fxs
    -- (error) Fewer arguments than parameters
    matchArgs' i [] (fx : fxs) = do addError $ SemError pos $ "Not enough arguments.  Given " ++ show i ++ "."
                                    name <- genUVar -- try to recover for error message's sake
                                    ty <- genUVar
                                    (HoleJ pos (TypeHoleJ ty) name :) <$> matchArgs' i [] fxs
    -- Exactly the correct number of arguments
    matchArgs' i [] [] = return []
    matchArgs' i xs [] = do addError $ SemError pos $ "Too many arguments.  Given " ++ show i ++ ", " ++ validRange ++ "."
                            return []

    numReq = length $ filter (\(_, b, _) -> b) fargs
    validRange = "expecting " ++ show numReq ++ " required and " ++ show (length fargs - numReq) ++ " implicit arguments"
