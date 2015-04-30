module Language.Plover.Main where

import Language.Plover.Compile (writeProgram)
import Language.Plover.Expressions (testPVT)

main :: IO ()
main = writeProgram "pvt_gen.c" ["extern_defs.c"] testPVT
