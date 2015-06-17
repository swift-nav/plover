module Language.Plover.SemCheck where

import Language.Plover.Types
import Language.Plover.Unify
import qualified Data.Map as M
import Data.Map (Map)
import Data.Tag
import Data.Function
import Data.Maybe
import Control.Monad.State
import Text.ParserCombinators.Parsec (SourcePos)

data SemError = SemError (Tag SourcePos) String
              deriving Show

data SemCheckData = SemCheckData
                    { semErrors :: [SemError]
                    , gensymState :: [UVar] -- already-used variables
                    , globalBindings :: Map Variable DefBinding
                    }
                  deriving Show

newSemCheckData :: [UVar] -> SemCheckData
newSemCheckData vs = SemCheckData
                     { semErrors = []
                     , gensymState = vs
                     , globalBindings = M.empty
                     }

type SemChecker = State SemCheckData

addError :: SemError -> SemChecker ()
addError e = do sd <- get
                put $ sd { semErrors = semErrors sd ++ [e] }

semAssert :: Bool -> SemError -> SemChecker ()
semAssert b e = if b then return () else addError e

lookupGlobalType :: Variable -> SemChecker (Maybe Type)
lookupGlobalType v = do bindings <- globalBindings <$> get
                        case M.lookup v bindings of
                         Just def -> case definition def of
                                      FunctionDef _ ft -> return $ Just $ FnType ft
                                      StructDef fields -> return $ Just $ StructType v $ ST fields
                                      ValueDef _ ty -> return $ Just ty
                         Nothing -> return Nothing

runSemChecker :: SemChecker v -> Either [SemError] v
runSemChecker m = let (v, s) = runState m (newSemCheckData [])
                  in case semErrors s of
                      [] -> Right v
                      errs -> Left errs

-- | Take the list of bindings and convert them into a map of
-- filled-out bindings.  This is to support prototypes.
condenseBindings :: [DefBinding] -> SemChecker (Map Variable DefBinding)
condenseBindings defs = do mapM addBinding defs
                           globalBindings <$> get

lookupBinding :: Variable -> SemChecker (Maybe DefBinding)
lookupBinding v = M.lookup v . globalBindings <$> get

addBinding :: DefBinding -> SemChecker ()
addBinding def = do molddef <- lookupBinding (binding def)
                    case molddef of
                     Just olddef -> reconcileBindings olddef def
                     Nothing -> newBinding def

-- | Determines whether a definition has a value definition.  Struct declarations don't count as having values.
defHasValue :: DefBinding -> Bool
defHasValue (DefBinding { definition = def }) = case def of
  FunctionDef me _ -> isJust me
  StructDef _ -> False
  ValueDef me _ -> isJust me

newBinding :: DefBinding -> SemChecker ()
newBinding def = let v = binding def
                 in do modify $ \state -> state { globalBindings = M.insert v def (globalBindings state) }
                       semAssert (not (extern def && defHasValue def)) $
                         SemError (bindingPos def) "Extern definition cannot have value or function body."
                       semAssert (not (extern def && static def)) $
                         SemError (bindingPos def) "Cannot be both static and extern simultaneously."


tagFromDefs :: [DefBinding] -> Tag SourcePos
tagFromDefs [] = NoTag
tagFromDefs [x] = bindingPos x
tagFromDefs xs = MergeTags $ map bindingPos xs

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
  where rtag = tagFromDefs [oldDef, newDef]

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
  addError $ SemError tag "Inconsistent types for definition of same name."
  return oldDef

--  semAssert (extern oldDef

{-
-- | Take the bindings and condense them into 
checkAndCompleteDefs :: [DefBinding] -> SemChecker [DefBinding]
checkAndCompleteDefs defs = do modify $ \x -> x { gensymState = allToplevelNames defs }
                               semCheckDefs defs

semCheckDefs :: [DefBinding] -> SemChecker [DefBinding]
semCheckDefs defs = mapM semCheckDef defs

semCheckDef :: DefBinding -> SemChecker DefBinding
semCheckDef def = do checkRedef
  where checkRedef = case lookupGlobalType 

  case definition def of
  FunctionDef mcexpr ft -> error ""
  StructDef _ -> do addError $ SemError (bindingPos def) "Structures not implemented"
                    return def
  ValueDef mcexpr ty -> error ""
-}
