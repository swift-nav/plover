{-# LANGUAGE OverloadedStrings #-}
module Smash.Parse.PVT where
import Smash.Parse.Types3

norm :: CExpr -> CExpr
norm x = Sig (x * x)

normalize :: CExpr -> CExpr
normalize x = x / norm x

-- TODO need dense matrix notation
rot_small :: CExpr -> CExpr
rot_small x = x

decls :: CExpr
decls = seqList $ [
  "nav_meas" := Lam "j" 4 (Lam "x" 3 0),
  "sat_pos" := Lam "j" 4 (Lam "x" 3 0),
  "gps_omega_e_dot" := 1,
  "rx_state" := (Lam "x" 3 0)
 ]


loop :: CExpr -> CExpr
loop j = seqList $ [
  "tau" := norm ("rx_state" - "sat_pos" :! j),
  "we_tau" := "gps_omega_e_dot" * "tau",
  "xk_new" := rot_small "we_tau" * ("nav_meas" :! j),
  "xk_new" - "rx_state"
 ]

pvt :: CExpr
pvt = seqList $ [
  decls,
  "los" := Lam "j" 4 (loop "j"),
  "G" := Lam "j" 4 (normalize ((- "los") :! "j") :# (Lam "i" 1 1))
 ]

-- Tests Expressions --
l0 = Lam "i" 1 (Lam "j" 1 ("i" + "j"))
e0, e1, e2 :: CExpr
e0 = "x" := Lam "i" 1 (Lam "j" 1 ("i" + "j"))
e1 = "a" := Lam "i" 1 ("x" := 2 :> "x")
e2 = "x" := Lam "i" 1 1 + Lam "i" 1 1
e3 = "x" := Sig (Lam "i" 3 "i")

e4 = seqList [
  "x" := Lam "i" 3 1,
  "y" := Lam "i" 3 1,
  "z" := "x" * "x" + "y",
  "n" := norm "z"
 ]

p1 :: CExpr
p1 = seqList [
  ("x" := Lam "i" 1 (Lam "j" 2 (("temp" := "i" + "j") :> "temp"))),
  ("y" := Lam "i" 2 (Lam "j" 3 ("i" + "j"))),
  ("z" := "x" * "y")
 ]

st0 = subst "x" (R "y") (R "x")
st1 = subst "x" (R "y") (R "x" + R "z")
