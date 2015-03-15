-- Various expressions and testing utilities --
{-# LANGUAGE OverloadedStrings #-}
module Smash.Parse.PVT where
import Smash.Parse.Types3

import System.Process
import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Arrow (second)

norm :: CExpr -> CExpr
norm x = "sqrt" :$ (Sig (x * x))

normalize :: CExpr -> CExpr
normalize x = x / norm x

-- TODO
transpose m = Free (Unary "transpose" m)
inverse m = Free (Unary "inverse" m)

s x = Lam "i" 1 x

-- TODO need dense matrix notation
rot_small :: CExpr -> CExpr
rot_small x =
  s (s 1     :# s x :# s 0) :#
  s (s (- x) :# s 1 :# s 0) :#
  s (s 0     :# s 0 :# s 1)

exts = seqList [
  Free (Extern "sqrt" (FT [] [numType] numType)),
  Free (Extern "inverse" (FT [TV "n"]
                             [ExprType [TV "n", TV "n"], ExprType [TV "n", TV "n"]]
                             (ExprType [TV "n", TV "n"]))),
  Free (Extern "randf" (FT [] [] numType)),
  Free (Extern "printFloat" (FT [] [numType] Void))
 ]

decls :: CExpr
decls = seqList [
  exts,
  Declare numType "gps_omega_e_dot"
  -- "gps_omega_e_dot" := 1

  --"sat_pos" := Lam "j" 4 (Lam "x" 3 0),
  --"pseudo" := Lam "j" 4 0,
  --"rx_state" := (Lam "x" 3 0)
 ]

loop :: CExpr -> CExpr
loop j = seqList $ [
  "tau" := norm ("rx_state" - "sat_pos" :! j),
  "we_tau" := "gps_omega_e_dot" * "tau",
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

testPVT = do
  test <- generateTestArguments "pvt" pvtSig
  n <- freshName
  let printer = Lam n 4 ("printFloat" :$ ("correction" :! R n))
  return $ pvt :> wrapMain (test :> printer)

pvt :: CExpr
pvt = seqList $ [
  decls,
  Free (FunctionDecl "pvt" pvtSig $ seqList [
    -- TODO this doesn't have to be 4
    "los" := Lam "j" 4 (loop "j"),
    "G" := Lam "j" 4 (normalize ((- "los") :! "j") :# (Lam "i" 1 1)),
    "omp" := "pseudo" - Lam "j" 4 (norm ("los" :! "j")),
    "X" := inverse ((transpose "G" * "G") * transpose "G"),
    "correction" :< "X" * "omp"
  ])
 ]

-- Tests Expressions --
l1 = Lam "i" 2 1
l2 = Lam "i" 2 (Lam "j" 2 ("i" + "j"))
e, e0, e1, e2 :: CExpr
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

p1 :: CExpr
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
  Free (Extern "sqrt" (FT [] [numType] numType)),
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
  exts,
  "z" := (s (s 1)),
  "x_inv" := s (s 1),
  Free $ App "inverse" ["z", "x_inv"]
 ]

p10 = seqList [
  exts,
  "z" := (s (s 1)),
  "x" := inverse "z"
 ]

p11 = seqList [
  exts,
  "r" := rot_small 2,
  "x" := inverse "r"
 ]

p12 = seqList [
  exts,
  Free (FunctionDecl "foo" (FD [("x", numType), ("y", numType)] numType) $ seqList [
    "z" := "x" * "y",
    Ret "z"])
 ]

st0 = subst "x" (R "y") (R "x")
st1 = subst "x" (R "y") (R "x" + R "z")

b1 = 2 * 3
b2 = "x" := "y"

-- Test cases
good_cases :: [(String, CExpr)]
good_cases = map (second wrapMain) [
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

  [
   --("p12", p12),
   ("pvt", pvt)]

bad_cases :: [CExpr]
bad_cases = [b1, b2]

wrapMain = Free . FunctionDecl "main" (FD [] IntType)

testAll = do
  putStrLn "should pass:"
  l1 <- mapM (testWithGcc . snd) good_cases
  print l1
  putStrLn "should fail:"
  l2 <- mapM testWithGcc bad_cases
  mapM_ print l2

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
testWithGcc :: CExpr -> IO (Maybe TestingError)
testWithGcc expr =
  let expr' = exts :> expr in
  case compileMain False (return expr') of
    Left err -> return $ Just (CompileError err)
    Right p -> do
      let fp = "compiler_output.c"
      writeFile fp p
      code <- execGcc fp
      case code of
        Nothing -> return $ Nothing
        Just output -> return $ Just (GCCError output)


generateTestArguments :: Variable -> FnDecl CExpr -> M CExpr
generateTestArguments fnName (FD params output) = do
  es <- mapM pValue params
  let decls = seqList es
      call = Free (App (R fnName) (map (R . fst) params))
  return (decls :> call)
  
  where
    pValue (var, ExprType ds) = do
      rhs <- vec ds
      return $ R var := rhs
    vec [] = return $ Free $ App "randf" []
    vec (d : ds) = do
      n <- freshName
      body <- vec ds
      return $ Lam n d body

