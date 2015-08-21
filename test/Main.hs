module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Language.Plover.Types
import Language.Plover.Main

-- import Simplify

main :: IO ()
main = defaultMain tests

gccCase :: (TestName, M CExpr) -> TestTree
gccCase (label, expr) = testCase label $ do
  merror <- testWithGcc expr
  case merror of
    Just err -> assertFailure (show err)
    Nothing -> return ()

tests :: TestTree
tests = testGroup "Tests" [
  testGroup "Units" $ map gccCase Exprs.good_cases
  ]

