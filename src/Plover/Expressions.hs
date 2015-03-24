-- Various expressions and testing utilities --
{-# LANGUAGE OverloadedStrings #-}
module Plover.Expressions where

import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Arrow (second)

import Plover.Types
import Plover.Macros

-- Simple Test Expressions --
l1, l2 :: CExpr
l1 = Lam "i" 2 1
l2 = Lam "i" 2 (Lam "j" 2 ("i" + "j"))

e, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12 :: CExpr
e = "x" := Lam "i" 1 2
e0 = "x" := Lam "i" 2 (Lam "j" 2 ("i" + "j"))
e1 = "a" := Lam "i" 1 (("x" := 2) :> "x")
e2 = "x" := Lam "i" 1 1 + Lam "i" 1 1
e3 = "x" := Sig (Lam "i" 3 "i")

e4 = seqList [
  "x" := Lam "i" 3 1,
  "y" := Lam "i" 3 1,
  "z" := "x" * "x" + "y",
  "n" := norm "z",
  "xy" := "x" :# "y"
 ]

e5 = "x" := Lam "i" 1 (2 * 3)

e6 = seqList [
  "x" := Lam "i" 1 (2 * 3),
  "y" := (- (normalize "x"))
 ]

e7 = seqList [
  "v" := Lam "i" 1 1,
  "x" := norm "v"
 ]

e8 = "x" := l2 * l2
e9 = "x" := l2 * l2 * l2
e10 = seqList [
  "x" := Lam "i" 2 (Lam "j" 2 1),
  "y" := "x" * "x" * "x"
 ]

e11 = "a" := l1 :# l1
e12 = seqList [
  "x" := l1,
  "y" := (- "x")
 ]

p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12 :: CExpr
p1 = seqList [
  ("x" := Lam "i" 1 (Lam "j" 2 (("temp" := "i" + "j") :> "temp"))),
  ("y" := Lam "i" 2 (Lam "j" 3 ("i" + "j"))),
  ("z" := "x" * "y")
 ]

p2 = seqList [
  "x" := Lam "i" 1 (Lam "j" 2 0),
  "y" := transpose "x" * "x"
 ]
p3 = seqList [
  "y" := 1 / 2
 ]
p4 = seqList [
  "x" := l2,
  "y" := l1,
  "z" := "x" * "y"
 ]
p5 = seqList [
  Free (Extern "sqrt" (FnType $ FT [] [numType] numType)),
  "y" := "sqrt" :$ 2
 ]
p6 = seqList [
  "x" := l1,
  "x2" := normalize "x"
 ]
p7 = seqList [
  "x" := 1 + 1 + 1,
  "y" := 3,
  "z" := "x" * "y"
 ]
p8 = "x" := rot_small 22
p9 = seqList [
  externs,
  "z" := (s (s 1)),
  "x_inv" := s (s 1),
  Free $ App "inverse" ["z", "x_inv"]
 ]

p10 = seqList [
  externs,
  "z" := (s (s 1)),
  "x" := inverse "z"
 ]

p11 = seqList [
  externs,
  "r" := rot_small 2,
  "x" := inverse "r"
 ]
p12 = seqList [
  externs,
  Free (FunctionDecl "foo" (FD [("x", numType), ("y", numType)] numType) $ seqList [
    "z" := "x" * "y",
    Ret "z"])
 ]

-- Test cases that fail
b1, b2 :: CExpr
b1 = 2 * 3
b2 = "x" := "y"

-- TODO functional test cases
f1 = seqList [
  "x" := l2,
  "y" := inverse "x"
  -- check output
 ]

-- The PVT Example --
decls :: CExpr
decls = seqList [
  externs,
  Ext "GPS_OMEGAE_DOT" numType,
  Ext "GPS_C" numType 
 ]

loop :: CExpr -> CExpr
loop j = seqList $ [
  "tau" := norm ("rx_state" - "sat_pos" :! j) / "GPS_C",
  "we_tau" := "GPS_OMEGAE_DOT" * "tau",
  -- TODO rewrite bug forces this onto its own line
  "rot" := rot_small "we_tau",
  "xk_new" := "rot" * ("sat_pos" :! j),
  --"xk_new" := rot_small "we_tau" * ("sat_pos" :! j),
  "xk_new" - "rx_state"
 ]

pvtSig = FD
  { fd_params =
      [("sat_pos", ExprType [4, 3])
      ,("pseudo", ExprType [4])
      ,("rx_state", ExprType [3])
      ,("correction", ExprType [4])]
  , fd_output = Void
  }

pvt :: CExpr
pvt = seqList $ [
  decls,
  Ext "pvt2" (FnType $ FT [] (map snd . fd_params $ pvtSig) Void),
  Free (FunctionDecl "pvt" pvtSig $ seqList [
    -- TODO this doesn't have to be 4
    "los" := Lam "j" 4 (loop "j"),
    "G" := Lam "j" 4 (normalize ((- "los") :! "j") :# (Lam "i" 1 1)),
    "omp" := "pseudo" - Lam "j" 4 (norm ("los" :! "j")),
    "X" := inverse (transpose "G" * "G") * transpose "G",
    "correction" :< "X" * "omp"
  ])
 ]

testPVT = do
  test1 <- generateTestArguments "pvt" pvtSig
  let test2 = Free (App (R "pvt2") (map (R . fst) (fd_params pvtSig)))
  n <- freshName
  let printer = Lam n 4 ("printNumber" :$ ("correction" :! R n))
  return $ pvt :> (wrapMain $ seqList $
    [ 
      test1
    , newline "generated output:"
    , printer
    , test2
    , newline "reference output:"
    , printer
    , newline ""
    ])

-- Test cases
good_cases :: [(String, M CExpr)]
good_cases = map (second (return . wrapMain)) [
  ("e", e),
  ("e0", e0),
  ("e1", e1),
  ("e2", e2),
  ("e3", e3),
  ("e4", e4),
  ("e5", e5),
  ("e6", e6),
  ("e7", e7),
  ("e8", e8),
  ("e9", e9),
  ("e10", e10),
  ("e11", e11),
  ("e12", e12),

  ("p1", p1),
  ("p2", p2),
  ("p3", p3),
  ("p4", p4),
  ("p5", p5),
  ("p6", p6),
  ("p9", p9),
  ("p10", p10),
  ("p11", p11)] ++

  [("pvt", testPVT)]

bad_cases :: [CExpr]
bad_cases = [b1, b2]

