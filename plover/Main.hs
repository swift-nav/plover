module Main where

import System.IO
import System.Environment
import System.Exit
import System.FilePath
import Language.Plover.CLI
import Control.Monad
import Control.Applicative ((<$>))
import Data.List
import Data.Maybe (fromMaybe)
import qualified Language.Plover.ParserTypes as PT
import qualified Language.Plover.Parser as Parser
import qualified Language.Plover.Convert as Convert
import qualified Language.Plover.SemCheck as SemCheck
import qualified Language.Plover.CodeGen as CodeGen
import qualified Language.Plover.Types as T
import Text.ParserCombinators.Parsec (parse)
import qualified Text.Show.Pretty as Pr

import Language.Plover.Unify
import Language.Plover.Algebra

main :: IO ()
main = do
  args <- getArgs
  opts <- compilerOpts args
  when (debugMode opts) $ do
    hPutStrLn stderr $ "Compiler options:\n" ++ show opts
  files <- case inputFiles opts of
            [] -> do contents <- getContents
                     return [("*stdin*", contents)]
            _ -> forM (inputFiles opts) $ \fileName -> do contents <- readFile fileName
                                                          return (fileName, contents)
  let mparsed = doParse opts files
      mconvert = doConvert opts mparsed
      mchecked = doTypeCheck opts mconvert
      mgen = doCodegen opts mchecked
  let tgt = case target opts of
             TargetDefault -> TargetCodeGen
             x -> x
  case tgt of
    TargetParse -> do
      parsed <- mparsed
      case parsed of
        Left err -> do hPutStrLn stderr err
                       exitWith $ ExitFailure 1
        Right exprs -> forM_ exprs $ \expr -> do
          putStrLn $ show $ T.pretty expr
    TargetConvert -> do
      convert <- mconvert
      case convert of
        Left err -> do hPutStrLn stderr err
                       exitWith $ ExitFailure 1
        Right defs -> putStrLn $ Pr.ppShow defs
    TargetTypeCheck -> do
      checked <- mchecked
      case checked of
        Left err -> do hPutStrLn stderr err
                       exitWith $ ExitFailure 1
        Right defs -> putStrLn $ Pr.ppShow defs
    TargetCodeGen -> do
      gen <- mgen
      case gen of
        Left err -> do hPutStrLn stderr err
                       exitWith $ ExitFailure 1
        Right (header, source) ->
          case unitName opts of
           Nothing -> do putStrLn "/* START HEADER */"
                         putStrLn (wrapHeader opts header)
                         putStrLn "/* START SOURCE */"
                         putStrLn source
           Just name -> do
             let cfile = joinPath [fromMaybe "" (cFilePrefix opts), name ++ ".c"]
             let hfile = joinPath [fromMaybe "" (hFilePrefix opts), name ++ ".h"]
             let includeName = joinPath [fromMaybe "" (libPrefix opts), name]
             writeFile hfile (wrapHeader opts header)
             writeFile cfile (addIncludes opts includeName source)
    _ -> putStrLn "Unimplemented target"
  return ()

makeHeaderName :: CompilerOpts -> String
makeHeaderName opts = "PLOVER_GENERATED_" ++ case unitName opts of
  Nothing -> case inputFiles opts of
              [] -> "DEFAULT"
              files -> clean' (last files)
  Just name -> clean' name
  
  where clean' = map clean''
        clean'' c | c `elem` (['A'..'Z'] ++ ['a' .. 'z'] ++ ['0'..'9'])  = c
                  | otherwise  = '_'

wrapHeader :: CompilerOpts -> String -> String
wrapHeader opts body = unlines
                       [ "#ifndef " ++ headername
                       , "#define " ++ headername
                       , ""
                       , body
                       , ""
                       , "#endif /* " ++ headername ++ " */"
                       ]
  where headername = makeHeaderName opts

addIncludes :: CompilerOpts -> String -> String -> String
addIncludes opts name body = unlines
                             [ "#include \"" ++ name ++ ".h\""
                             , ""
                             , body
                             ]

--  writeProgram "pvt_gen.c" ["extern_defs.c"] testPVT

-- | Parses (filename, source) pairs into (source, expr) pairs.
doParse :: CompilerOpts -> [(String, String)] -> IO (Either String [PT.Expr])
doParse opts files = sequence <$> (forM files $ \(fileName, source) ->
  case parse Parser.toplevel fileName source of
   Left err -> Left <$> Parser.reportErr err
   Right expr -> return $ Right expr)

doConvert :: CompilerOpts -> IO (Either String [PT.Expr]) -> IO (Either String [T.DefBinding])
doConvert opts mparsed = do
  parsed <- mparsed
  case parsed of
   Left err -> return $ Left err
   Right exprs -> fmap (fmap concat) $
     sequence <$> (forM exprs $ \expr ->
                      case Convert.makeDefs expr of
                       Left err -> Left <$> Convert.reportConvertErr err
                       Right defs -> return $ Right defs)

doTypeCheck :: CompilerOpts -> IO (Either String [T.DefBinding]) -> IO (Either String [T.DefBinding])
doTypeCheck opts mdefs = do
  edefs <- mdefs
  case edefs of
   Left err -> return $ Left err
   Right defs -> case SemCheck.doSemCheck defs of
                  Left errs -> Left . unlines <$> mapM SemCheck.reportSemErr (nub errs)
                  Right defs' -> return $ Right defs'

doCodegen :: CompilerOpts -> IO (Either String [T.DefBinding]) -> IO (Either String (String, String))
doCodegen opts mchecked = do
  checked <- mchecked
  case checked of
   Left err -> return $ Left err
   Right defs -> return $ Right $ CodeGen.doCompile defs
