-- Various expressions and testing utilities --
{-# LANGUAGE OverloadedStrings #-}
module Plover.Expressions where

import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Arrow (second)

import Plover.Types
import Plover.Macros
import Plover.Reduce (typeCheck)

-- Simple Test Expressions --
l1, l2 :: CExpr
l1 = Vec "i" 2 1
l2 = Vec "i" 2 (Vec "j" 2 ("i" + "j"))
l3 = Vec "i" 3 (Vec "j" 3 ("i" + "j"))

e, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12 :: CExpr
e = "x" := Vec "i" 1 2
e0 = "x" := Vec "i" 2 (Vec "j" 2 ("i" + "j"))
e1 = "a" := Vec "i" 1 (("x" := 2) :> "x")
e2 = "x" := Vec "i" 1 1 + Vec "i" 1 1
e3 = "x" := Sigma (Vec "i" 3 "i")

e4 = seqList [
  "x" := Vec "i" 3 1,
  "y" := Vec "i" 3 1,
  "z" := "x" * "x" + "y",
  "n" := norm "z",
  "xy" := "x" :# "y"
 ]

e5 = "x" := Vec "i" 1 (2 * 3)

e6 = seqList [
  "x" := Vec "i" 1 (2 * 3),
  "y" := (- (normalize "x"))
 ]

e7 = seqList [
  "v" := Vec "i" 1 1,
  "x" := norm "v"
 ]

e8 = "x" := l2 * l2

e9 = "x" := l2 * l2 * l2

e10 = seqList [
  "x" := Vec "i" 2 (Vec "j" 2 1),
  "y" := "x" * "x" * "x"
 ]

e11 = "a" := l1 :# l1

e12 = seqList [
  "x" := l1,
  "y" := (- "x")
 ]

p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17 :: CExpr

p1 = seqList [
  ("x" := Vec "i" 1 (Vec "j" 2 (("temp" := "i" + "j") :> "temp"))),
  ("y" := Vec "i" 2 (Vec "j" 3 ("i" + "j"))),
  ("z" := "x" * "y")
 ]

p2 = seqList [
  "x" := Vec "i" 1 (Vec "j" 2 0),
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
  --(Extern "sqrt" (FnType $ fnT [numType] numType)),
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
  "z" := (s (s 1)),
  "x_inv" := s (s 1),
  App "inverse" ["z", "x_inv"]
 ]

p10 = seqList [
  "z" := (s (s 1)),
  "x" := inverse "z"
 ]

p11 = seqList [
  "r" := rot_small 2,
  "x" := inverse "r"
 ]

p12 = seqList [
  FunctionDef "foo" (FnT [] [("x", numType), ("y", numType)] numType) $ seqList [
    "z" := "x" * "y",
    Return "z"],
  App "foo" [2, 3]
 ]

p13 = seqList [
  "x" := l2,
  "x" :<= l1
 ]

p14 = seqList [
  FunctionDef "test" (FnT [] [("x", VecType [1,1] NumType)] Void) $ seqList [
    "x" :<= l1
    ]
 ]

p15 = seqList [
  StructDecl "pair" (ST Generated [("a", numType), ("b", numType)]),

  Declare (TypedefType "pair") "x",
  Declare (TypedefType "pair") "y",

  ("x" :. "a") :<= 0,
  "y" :<= "x"
 ]
p16 = seqList
  [ StructDecl "pair" (ST Generated [("a", numType), ("b", VecType ["len"] NumType)])
  , Declare (TypedefType "pair") "x"
  , "x" :. "a" :<= 2
  , "y" := Vec "i" ("x" :. "a") "i"
  , "x" :. "b" :<= "y"
  ]

p17 = "x" := l3 :# (l3 * l3)

p18 = "x" := 0

p19 = Declare IntType "x" :> "x" :<= 0

-- Example compilation units
cu1, cu_pvt :: CompilationUnit
cu1 = CU
  -- name
  "test" 
  -- function defs
  [("testfn", FnT [] [] Void, VoidExpr)]
  -- includes
  []
  -- header definitions
  [("x" := 22)]
  -- header includes
  []

cu_pvt = CU "gen_pvt" [("pvt", pvtSig, pvtBody)] ["extern_defs.c"] [nav_meas_def] []

-- Test cases that fail
b1, b2 :: CExpr
b1 = 2 * 3
b2 = "x" := "y"
b3 = "x" := 22 :> "x" := 0

-- The PVT Example --
-- Current version will live in libswiftnav repository
decls :: CExpr
decls = seqList [
  Extern "GPS_OMEGAE_DOT" numType,
  Extern "GPS_C" numType
 ]

losLoop :: CExpr
losLoop = Vec "j" "n_used" $ seqList [
  "tau" := norm ("rx_state" - "sat_pos" :! "j") / "GPS_C",
  "we_tau" := "GPS_OMEGAE_DOT" * "tau",
  -- TODO rewrite issue forces this onto its own line
  "rot" := rot_small "we_tau",
  "xk_new" := "rot" * ("sat_pos" :! "j"),
  --"xk_new" := rot_small "we_tau" * ("sat_pos" :! "j"),
  "xk_new" - "rx_state"
 ]

-- Externally defined (and has additional fields)
nav_meas_def = StructDecl "navigation_measurement_t" $ ST
  External [("pseudorange", numType)]

pvtSig = FnT
  { ft_imp = [("n_used", IntType)]
  , ft_exp =
      [("sat_pos", vecType ["n_used", 3])
      --,("pseudo", vecType ["n_used"])
      ,("nav_meas", VecType ["n_used"] (TypedefType "navigation_measurement_t"))
      ,("rx_state", vecType [3])
      ,("correction", vecType [4])
      ,("G", vecType ["n_used", (3+1)])
      ,("X", vecType [4, "n_used"])
      ]
  , ft_out = Void
  }

pvtBody = seqList [
    decls,
    "los" :=  losLoop,
    "G" :<= Vec "j" "n_used" (normalize ((- "los") :! "j") :# (Vec "i" 1 1)),

    -- TODO struct
    --Declare (vecType ["n_used"]) "pseudo",
    "pseudo" := (Vec "i" "n_used" $ ("nav_meas" :! "i") :. "pseudorange"),

    "omp" := "pseudo" - Vec "j" "n_used" (norm ("los" :! "j")),
    "X" :<= inverse (transpose "G" * "G") * transpose "G",
    "correction" :<= "X" * "omp"
 ]

pvt :: CExpr
pvt = nav_meas_def :> FunctionDef "pvt" pvtSig pvtBody

testPVT = do
  -- Load struct def into context
  typeCheck nav_meas_def
  -- Generate random arguments, call "pvt" defined above
  test1 <- generateTestArguments "pvt" pvtSig
  -- Print n_used
  let pnused = ("printInt" :$ "n_used")
  -- Call the wrapped libswiftnav version
  let test2 = App "pvt2" (map (Ref . fst) (ft_exp pvtSig))
  n <- freshName
  let printer = Vec n 4 ("printDouble" :$ ("correction" :! Ref n))
  -- Definition of pvt, then main that calls test code
  return
    $ Extern "pvt2" (FnType $ pvtSig )
    :> pvt
    :> (wrapMain $ seqList
         [ test1
         , pnused
         , newline "generated output:"
         , printer
         , test2
         , newline "reference output:"
         , printer
         , newline ""
         ])

-- Test cases.
good_cases :: [(String, M CExpr)]
good_cases =
  [ ("pvt", testPVT) ] ++
  map (second (return . wrapMain))
  [ ("e", e)
  , ("e0", e0)
  , ("e1", e1)
  , ("e2", e2)
  , ("e3", e3)
  , ("e4", e4)
  , ("e5", e5)
  , ("e6", e6)
  , ("e7", e7)
  , ("e8", e8)
  , ("e9", e9)
  , ("e10", e10)
  , ("e11", e11)
  , ("e12", e12)

  , ("p1", p1)
  , ("p2", p2)
  , ("p3", p3)
  , ("p4", p4)
  , ("p5", p5)
  , ("p6", p6)
  , ("p9", p9)
  , ("p10", p10)
  , ("p11", p11)
  -- , ("p12", p12)
  , ("p15", p15)
  , ("p17", p17)
  , ("p18", p18)
  , ("p19", p19)
  ]

bad_cases :: [CExpr]
bad_cases = [b1, b2]
