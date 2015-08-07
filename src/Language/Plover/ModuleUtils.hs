{-# LANGUAGE RecordWildCards #-}
module Language.Plover.ModuleUtils where

import qualified Language.Plover.Types as T
import qualified Language.Plover.ParserTypes as PT
import qualified Language.Plover.Parser as Parser
import qualified Language.Plover.Convert as Convert
import qualified Language.Plover.SemCheck as SemCheck
import qualified Language.Plover.CodeGen as CodeGen
import Language.Plover.ErrorUtil
import Language.Plover.CLI
import Text.ParserCombinators.Parsec (parse)

import Data.Tag
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isJust, isNothing, mapMaybe)
import Data.List (nub, sortOn)
import Data.Either (partitionEithers, isLeft)
import Control.Monad
import Control.Monad.Trans.Either
import Control.Monad.State
import Control.Monad.Trans
import Control.Arrow (first, second)

import System.Directory
import System.FilePath
import Debug.Trace

type Error = String
type Action = EitherT Error (StateT ModuleState IO)
type SearchPath = FilePath
type Import = (String, Maybe T.DefBinding)
type ModuleImports = [T.DefBinding]
type CheckedBindings = ([T.DefBinding], [T.DefBinding])
type ModuleMap =
  M.Map String
        (Either (Int, Import) CheckedBindings)
data ModuleState = ModuleState
  { ms_opts :: CompilerOpts
  , ms_map :: ModuleMap
  , ms_count :: Int
  }

initialModMap = M.empty

runAction :: CompilerOpts -> Action a -> IO (Either Error a)
runAction opts m = evalStateT (runEitherT m) (ModuleState opts initialModMap 0)

plvExt = "plv"

getImportTrace :: ModuleMap -> [T.DefBinding]
getImportTrace = mapMaybe id . getImportTrace'

getImportTrace' =
    map (snd . snd) . sortOn fst . mapMaybe fromLeft . M.elems
  where
    fromLeft = either Just (const Nothing)


pushStatic :: Bool -> T.DefBinding -> T.DefBinding
pushStatic stat b = b { T.static = stat || T.static b }

loadModules :: [T.DefBinding] -> Action [T.DefBinding]
loadModules bindings = do
  modMap <- gets ms_map
  bss <- mapM processBinding bindings
  return $ concat bss

insertAction :: String -> Either (Int, Import) CheckedBindings -> Action ()
insertAction k v = do
  modify $ \ms -> ms { ms_map = M.insert k v (ms_map ms) }

beginDef :: Import -> Action ()
beginDef i@(name, _) = do
  c <- gets ms_count 
  insertAction name $ Left (c, i)
  modify $ \ms -> ms { ms_count = c + 1 }

isImport b | T.ImportDef _ <- T.definition b = True
isImport _ = False

loadNewModule :: Maybe FilePath -> Import -> Action CheckedBindings
loadNewModule mfilepath imp@(name, mbinding) = do
  ModuleState{ms_map = mm, ms_opts = opts} <- get
  -- Needed for cycle detection
  beginDef imp
  liftIO $ putStrLn $ replicate (2 * length (getImportTrace' mm)) ' ' ++
    "Loading module " ++ name ++ "..."
  (fileName, content) <-
    case mfilepath of
      Just filePath -> do
        content <- liftIO (readFile filePath)
        return (filePath, content)
      Nothing -> findImport (includePaths opts) name
  expr <- doParse opts (Just fileName, content)
  defs <- doConvert opts (return expr)
  defsOK <- doTypeCheck opts (return defs)
  let importLines = filter (isImport) defs
  insertAction name (Right (importLines, defsOK))
  return (importLines, defsOK)

filterImportedBindings name b =
    map (pushStatic (T.static b) . mplusName) . filter (not . T.static) . filter importable
   where
    mplusName b = b { T.imported = T.imported b `mplus` Just name }
    importable defb = case T.definition defb of
      T.InlineCDef {} -> False
      _ -> True

removeImports = filter (isNothing . T.imported)

processBinding :: T.DefBinding -> Action [T.DefBinding]
processBinding b | T.ImportDef name <- T.definition b = do
  ModuleState{ms_map = modMap, ms_opts = opts} <- get
  case M.lookup name modMap of
    Nothing -> fmap (filterImportedBindings name b . snd) $
                 loadNewModule Nothing (name, Just b)
    -- Error: we are currently trying to load this module already
    Just (Left _) -> do
      -- For the error report only:
      beginDef (name, Just b)
      importCycle <- getImportTrace . ms_map <$> get
      let tag = MergeTags $ map T.bindingPos importCycle
      tags <- liftIO $ showTagPositions tag
      left $ tags ++ "Module cycle detected when processing import. Cyclic imports are not allowed."
    -- Memoize
    -- If a module is multiply imported, it will be handled by reconcileBindings.
    Just (Right bs) -> 
      -- Filter out static defs, mark bindings with the module name they come from,
      -- and mark as static if the import is static.
      return $ filterImportedBindings name b $ snd $ bs
processBinding b = return [b]

findImport :: [SearchPath] -> String -> Action (FilePath, String)
findImport searchPaths moduleName = do
  mname <- liftIO $ findFile searchPaths (moduleName ++ "." ++ plvExt)
  case mname of
    Nothing -> left errMsg
    Just name -> do
      content <- liftIO $ readFile name
      return (name, content)
    where
      errMsg = unlines $ ["Couldn't find module: " ++ moduleName ++
                          ". Tried the following paths:"]
                          ++ if null searchPaths
                             then ["[None given]"]
                             else searchPaths

-- | Wrappers around core Plover functions
-- | Parses (filename, source) pairs into (source, expr) pairs.
doParse :: CompilerOpts -> (Maybe FilePath, String) -> Action PT.Expr
doParse opts (fileName, source) = 
  case parse Parser.toplevel (fromMaybe "*stdin*" fileName) source of
   Left err -> do
     -- reads file
     msg <- liftIO $ Parser.reportErr err
     left msg
   Right expr -> return expr

doConvert :: CompilerOpts -> Action PT.Expr -> Action [T.DefBinding]
doConvert opts mparsed = do
  expr <- mparsed
  case Convert.makeDefs expr of
    Left err -> do
      -- reads file
      msg <- liftIO $ Convert.reportConvertErr err
      left msg
    Right defs -> return defs

doTypeCheck :: CompilerOpts -> Action [T.DefBinding] -> Action [T.DefBinding]
doTypeCheck opts mdefs = do
  literalDefs <- mdefs
    -- TODO remove notes
    -- HERE select imports, find them/compile,
    --      splice defs:
    --        toggle import flag on/remove static,
      --      if static, make all defs static
    --      return ([(import, static)], [defbinding])
    --      ?? reconciledefbindings who imported what ??
  defs <- loadModules literalDefs
  case SemCheck.doSemCheck defs of
    Left errs -> do
      msg <- liftIO $ mapM SemCheck.reportSemErr (nub errs)
      left $ unlines msg
    Right defs' -> return defs'

doCodegen :: CompilerOpts -> Action CheckedBindings -> Action ((String, String), ModuleImports)
doCodegen opts mchecked = do
  (imports, defs) <- mchecked
  let defs' = removeImports defs
  return (CodeGen.doCompile defs', imports)

fromRight (Right x) = x

doCodegenAll :: Action ()
doCodegenAll = do
  modMap <- gets ms_map
  opts <- gets ms_opts
  let pairs = M.toList modMap
  forM_ pairs $ \(mod, bs) -> do
    (pair, imports) <- doCodegen opts (return $ fromRight bs)
    liftIO $ writeFiles pair imports opts (Just mod)


splitStatic b | T.static b = Left b
splitStatic b = Right b

importName (T.ImportDef n) = n
both f (a, b) = (f a, f b)

writeFiles :: (String, String) -> [T.DefBinding] -> CompilerOpts -> Maybe String -> IO ()
writeFiles (header, source) imports opts unitName =
  let (staticIncludes, normalIncludes) =
        both (map $ importName . T.definition) . partitionEithers . map splitStatic $ imports
  in
  case unitName of
   Nothing -> do putStrLn "/* START HEADER */"
                 putStrLn (wrapHeader normalIncludes "DEFAULT" header)
                 putStrLn "/* START SOURCE */"
                 putStrLn source
   Just name -> do
     let cfile = joinPath [fromMaybe "" (cFilePrefix opts), name ++ ".c"]
     let hfile = joinPath [fromMaybe "" (hFilePrefix opts), name ++ ".h"]
     let addPrefix name = joinPath [fromMaybe "" (libPrefix opts), name]
     let includeName = addPrefix name
     writeFile hfile (wrapHeader (map addPrefix normalIncludes) name header)
     writeFile cfile (addIncludes (map addPrefix staticIncludes) includeName source)

makeHeaderName :: String -> String
makeHeaderName unitName = "PLOVER_GENERATED_" ++ clean' unitName
  where clean' = map clean''
        clean'' c | c `elem` (['A'..'Z'] ++ ['a' .. 'z'] ++ ['0'..'9'])  = c
                  | otherwise  = '_'

wrapHeader :: [String] -> String -> String -> String
wrapHeader moduleNames unitName body = unlines $
  [ "#ifndef " ++ headername
  , "#define " ++ headername
  , "" ] ++
  ["#include \"" ++ mod ++ ".h\"" | mod <- moduleNames] ++
  [ ""
  , body
  , ""
  , "#endif /* " ++ headername ++ " */"
  ]
  where headername = makeHeaderName unitName

addIncludes :: [String] -> String -> String -> String
addIncludes moduleNames name body = unlines $
  [ "#include \"" ++ name ++ ".h\""
  , "" ] ++
  ["#include \"" ++ mod ++ ".h\"" | mod <- moduleNames] ++
  [ "" , body ]
