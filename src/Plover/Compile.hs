{-# LANGUAGE RecordWildCards #-}
module Plover.Compile
  ( writeProgram
  , generateLib
  , generateMain
  , testWithGcc
  , printExpr
  , printType
  , runM
  ) where

import Control.Monad.Trans.Either
import Control.Monad.State

import System.Process

import Plover.Types
import Plover.Reduce
import Plover.Print
import Plover.Macros (externs, seqList)

runM :: M a -> (Either Error a, Context)
runM m = runState (runEitherT m) initialState

wrapExterns :: M CExpr -> M CExpr
wrapExterns e = do
  e' <- e
  return (externs :> e')

--compileExpr :: M CExpr -> Either Error String
--compileLine :: CExpr -> Either Error String

noFlatten expr = printOutput $ fmap show $ do
  fst . runM $ compile =<< wrapExterns expr

compileProgram :: [String] -> M CExpr -> Either Error String
compileProgram includes expr = do
  expr' <- fst . runM $ compile =<< wrapExterns expr
  program <- flatten expr'
  return $ ppProgram $ Block (map Include includes ++ [program])

printFailure :: String -> IO ()
printFailure err = putStrLn (err ++ "\nCOMPILATION FAILED")

main' :: M CExpr -> IO ()
main' m =
  case compileProgram [] m of
    Left err -> printFailure err
    Right str -> putStrLn str

main :: CExpr -> IO ()
main = main' . return

printOutput mp =
  case mp of
    Left err -> printFailure err
    Right p -> do
      putStrLn p

printExpr' :: M CExpr -> IO ()
printExpr' expr = printOutput (compileProgram [] expr)

printExpr :: CExpr -> IO ()
printExpr expr = printOutput (compileProgram [] (return expr))

printType :: CExpr -> IO ()
printType expr = printOutput (fmap show $ fst $ runM $ typeCheck expr)

writeProgram :: FilePath -> [String] -> M CExpr -> IO ()
writeProgram fn includes expr =
  let mp = compileProgram includes expr in
  case mp of
    Left err -> printFailure err
    Right p -> do
      putStrLn p
      writeFile fn p

data TestingError = CompileError String | GCCError String
  deriving (Eq)

instance Show TestingError where
  show (GCCError str) = "gcc error:\n" ++ str
  show (CompileError str) = "rewrite compiler error:\n" ++ str

execGcc :: FilePath -> IO (Maybe String)
execGcc fp =  do
  out <- readProcess "gcc" [fp, "-w"] ""
  case out of
    "" -> return Nothing
    _ -> return $ Just out

-- See test/Main.hs for primary tests
testWithGcc :: M CExpr -> IO (Maybe TestingError)
testWithGcc expr =
  case compileProgram ["extern_defs.c"] expr of
    Left err -> return $ Just (CompileError err)
    Right p -> do
      let fp = "testing/compiler_output.c"
      writeFile fp p
      code <- execGcc fp
      case code of
        Nothing -> return $ Nothing
        Just output -> return $ Just (GCCError output)

-- Generates .h and .c file as text
generateLib :: CompilationUnit -> Either Error (String, String)
generateLib CU{..} =
  let (decls, defs) = unzip $ map splitDef definitions
      headerTerm = seqList headerDefs
      cfileExpr = Extension headerTerm :> seqList defs
      forwardDecls = ppProgram (Block decls)
  in do
    cfile <- compileProgram includes (return cfileExpr)
    header <- compileProgram includes (return headerTerm)
    return (header ++ forwardDecls, cfile)
  where
    splitDef (name, fntype, def) =
      (ForwardDecl name fntype, FunctionDef name fntype def)

-- Generates .h and .c file and writes them to given filepaths
generateMain :: FilePath -> FilePath -> CompilationUnit -> IO ()
generateMain hdir cdir cu =
  case generateLib cu of
    Right (hout, cout) -> do
      let hfile = hdir ++ "/" ++ unitName cu ++ ".h"
      let cfile = cdir ++ "/" ++ unitName cu ++ ".c"
      writeFile hfile hout
      putStrLn $ "generated file " ++ show hfile
      writeFile cfile cout
      putStrLn $ "generated file " ++ show cfile
    Left err -> putStrLn $ "error: " ++ err
