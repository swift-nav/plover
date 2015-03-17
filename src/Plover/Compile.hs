module Plover.Compile where

import Control.Monad.Trans.Either
import Control.Monad.State

import System.Process

import Plover.Types
import Plover.Reduce
import Plover.Print
import Plover.Macros (externs)

runM :: M a -> (Either Error a, TypeEnv)
runM m = runState (runEitherT m) initialState

compileMain :: Bool -> M CExpr -> Either Error String
compileMain reduce expr = do
  expr' : _ <- fst . runM $ compile =<< expr
  let expr'' = (if reduce then reduceArith else id) expr'
  program <- flatten $ expr''
  return (ppMain program)

printFailure :: String -> IO ()
printFailure err = putStrLn (err ++ "\nCOMPILATION FAILED")

-- TODO handle numeric simplification better
main' :: M CExpr -> IO ()
main' m = 
  case compileMain False m of
    Left err -> printFailure err
    Right str -> putStrLn str

main :: CExpr -> IO ()
main = main' . return

writeMain :: M CExpr -> IO ()
writeMain expr =
  let mp = compileMain False expr in
  case mp of
    Left err -> printFailure err
    Right p -> do
      putStrLn p
      writeFile "testing/compiler_output.c" p

data TestingError = CompileError String | GCCError String
  deriving (Eq)

instance Show TestingError where
  show (GCCError str) = "gcc error:\n" ++ str
  show (CompileError str) = "rewrite compiler error:\n" ++ str

execGcc :: FilePath -> IO (Maybe String)
execGcc fp =  do
  out <- readProcess "gcc" [fp] ""
  case out of
    "" -> return Nothing
    _ -> return $ Just out

-- See test/Main.hs for primary tests
testWithGcc :: M CExpr -> IO (Maybe TestingError)
testWithGcc expr =
  let expr' = do e <- expr
                 return (externs :> e)
  in
  case compileMain False expr' of
    Left err -> return $ Just (CompileError err)
    Right p -> do
      let fp = "testing/compiler_output.c"
      writeFile fp p
      code <- execGcc fp
      case code of
        Nothing -> return $ Nothing
        Just output -> return $ Just (GCCError output)

