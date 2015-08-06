module Language.Plover.Main
  ( main
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
import Data.List
import Data.Maybe (fromMaybe)
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


main :: IO ()
main = do
  args <- getArgs
  opts <- compilerOpts args
  when (debugMode opts) $ do
    hPutStrLn stderr $ "Compiler options:\n" ++ show opts
  files <- case inputFiles opts of
             [] -> do contents <- getContents
                      return [(Nothing, contents)]
             _ -> forM (inputFiles opts) $ \fileName -> do contents <- readFile fileName
                                                           return (Just fileName, contents)
  forM_ files $ \file -> do
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
        parsed <- runAction opts $ mparsed
        case parsed of
          Left err -> do hPutStrLn stderr err
                         exitWith $ ExitFailure 1
          Right expr ->
            putStrLn $ show $ T.pretty expr
      TargetConvert -> do
        convert <- runAction opts $ mconvert
        case convert of
          Left err -> do hPutStrLn stderr err
                         exitWith $ ExitFailure 1
          Right defs -> putStrLn $ Pr.ppShow defs
      TargetTypeCheck -> do
        checked <- runAction opts $ mchecked
        case checked of
          Left err -> do hPutStrLn stderr err
                         exitWith $ ExitFailure 1
          Right defs -> do
            putStrLn $ Pr.ppShow defs
      TargetCodeGen -> do
        gen <- runAction opts $ mgen
        case gen of
          Left err -> do hPutStrLn stderr err
                         exitWith $ ExitFailure 1
          Right (pair, imports) -> writeFiles pair imports opts $ moduleName opts mfilename
      _ -> putStrLn "Unimplemented target"
  return ()
