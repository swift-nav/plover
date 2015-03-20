module Plover.Main where

import Plover.Types
import Plover.Expressions
import Plover.Reduce

import Plover.Compile (writeProgram)
import Plover.Expressions (testPVT)

main :: IO ()
main = writeProgram "testing/compiler_output.c" testPVT
