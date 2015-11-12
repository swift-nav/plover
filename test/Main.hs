module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Language.Plover.Types
import Language.Plover.Main (main')

import System.Process
import System.Exit

-- import Simplify

main :: IO ()
main = defaultMain tests

type Args = [String]
-- Should compile successfully, return code
type Outcome = (Bool, Maybe ExitCode)

testFailure = not . fst
testSuccess =       fst
testCode v = (== v) . snd

gccCompile files outcome = do
  _ <- readProcess "gcc" (files ++ ["-w", "-std=c99", "-otest_bin", "-lm"]) ""
  -- ExitCode, stdout :: String, stderr :: String
  (code, _, _) <- readProcessWithExitCode "./test_bin" [] ""

  assert (testCode (Just code) outcome)

type TestCase = (String, Args, FilePath, Outcome)

doCase :: TestCase -> TestTree
doCase (label, args, fn, outcome) = testCase label $ do
  mlist <- main' (args ++ [fn])
  case mlist of
    Left err -> assert (testFailure outcome)
    Right files -> do
      assert (testSuccess outcome)
      let (hfiles, cfiles) = unzip files
      gccCompile cfiles outcome

cases :: [TestCase]
cases =
  [ ("qr", ["-I", "examples"], "examples/qr_test.plv", (True, Just ExitSuccess))
  , ("cyclic", ["-I", "examples/module-tests"],
     "examples/module-tests/cycleA.plv", (False, Nothing))
  ]

tests :: TestTree
tests = testGroup "Tests" [
  testGroup "Units" $ map doCase cases
  ]

