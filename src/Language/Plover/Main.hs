module Language.Plover.Main
  ( main
  , main'
  , module Language.Plover.ModuleUtils
  , module Language.Plover.CLI
  ) where

import qualified Language.Plover.Types as T
import qualified Language.Plover.ParserTypes as PT
import qualified Language.Plover.Parser as Parser
import qualified Language.Plover.Convert as Convert
import qualified Language.Plover.SemCheck as SemCheck
import qualified Language.Plover.CodeGen as CodeGen

import Language.Plover.CLI

-- Main functionality defined here
import Language.Plover.ModuleUtils

import Control.Monad
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import Data.List
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Map as M
import Control.Monad.Trans.Either (runEitherT)

import System.IO
import System.Environment
import System.Exit
import System.FilePath
import Text.ParserCombinators.Parsec (parse)
import qualified Text.Show.Pretty as Pr

moduleName :: CompilerOpts -> Maybe FilePath -> Maybe String
moduleName opts mfile = mconcat [explicit, fromFile]
  where
    explicit = unitName opts
    fromFile = dropExtension . takeFileName <$> mfile


runAction_ :: CompilerOpts -> Action a -> IO ()
runAction_ opts m = do
  result <- runAction opts m
  case result of
    Left err -> do
      hPutStrLn stderr err
      exitWith $ ExitFailure 1
    Right _ -> return ()

type FileList = [(FilePath, FilePath)]

main :: IO ()
main = do
  args <- getArgs 
  _ <- main' args
  return ()

main' :: [String] -> IO (Either Error FileList)
main' args = do
  opts <- compilerOpts args
  runAction opts $ do
    when (debugMode opts) $ liftIO $
      hPutStrLn stderr $ "Compiler options:\n" ++ show opts
    files <- case inputFiles opts of
               [] -> do contents <- liftIO $ getContents
                        return [(Nothing, contents)]
               _ -> forM (inputFiles opts) $ \fileName -> do contents <- liftIO $ readFile fileName
                                                             return (Just fileName, contents)
    fmap concat $ forM files $ \file -> do
      let mfilename = fst file
          mparsed = doParse opts file
          mconvert = doConvert opts mparsed
          modname = (fromMaybe "Main" $ moduleName opts mfilename)
          mchecked = loadNewModule mfilename (modname, Nothing)
          mgen = doCodegen opts mchecked
      let tgt = case target opts of
                 TargetDefault -> TargetCodeGen
                 x -> x
      case tgt of
        TargetParse -> do
          expr <- mparsed
          liftIO $ print $ T.pretty expr
          return []
        TargetConvert -> do
          defs <- mconvert
          liftIO $ putStrLn $ Pr.ppShow defs
          return []
        TargetTypeCheck -> do
          defs <- mchecked
          liftIO $ putStrLn $ Pr.ppShow defs
          return []
        TargetCodeGen -> do
          -- Needed to populate internal module map
          _ <- mgen
          doCodegenAll
        _ -> do
          liftIO $ putStrLn "Unimplemented target"
          return []
