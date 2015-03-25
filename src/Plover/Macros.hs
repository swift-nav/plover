{-# LANGUAGE OverloadedStrings #-}
module Plover.Macros where

import Control.Monad.Free

import Plover.Types

-- Sequence a list of CExprs
seqList :: [CExpr] -> CExpr
seqList es = foldr1 (:>) es

-- Vector norm
norm :: CExpr -> CExpr
norm x = "sqrt" :$ (Sig (x * x))

normalize :: CExpr -> CExpr
normalize x = x / norm x

transpose m = Free (Unary "transpose" m)
inverse m = Free (Unary "inverse" m)

-- TODO better dense matrix notation
rot_small :: CExpr -> CExpr
rot_small x =
  s (s 1     :# s x :# s 0) :#
  s (s (- x) :# s 1 :# s 0) :#
  s (s 0     :# s 0 :# s 1)

-- Make a length 1 vector to hold the argument
s :: CExpr -> CExpr
s x = Lam "i" 1 x

-- Wrap an expression in a main function
wrapMain = Free . FunctionDecl "main" (FD [] IntType)

-- Print a string with newlines
newline s = "printf" :$ (Str $ "\n" ++ s ++ "\n")

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

generatePrinter :: Variable -> Type -> M CExpr
generatePrinter var (ExprType ds) = do
  names <- mapM (\_ -> freshName) ds
  let body = ("printNumber" :$ foldl (:!) (R var) (map R names))
  let e = foldr (uncurry Lam) body (zip names ds)
  return e

testFunction var sig output tp = do
  test <- generateTestArguments var sig
  printer <- generatePrinter output tp
  return $ wrapMain (test :> printer)

-- The extern file declarations

externs = seqList
 [ Ext "sqrt"        (FnType $ FT [] [numType] numType)
 , Ext "inverse"     (FnType $ FT [TV "n"]
                                  [ExprType [TV "n", TV "n"], ExprType [TV "n", TV "n"]]
                                  (ExprType [TV "n", TV "n"]))
 , Ext "randf"       (FnType $ FT [] [] numType)
 , Ext "printf"      (FnType $ FT [] [stringType] Void)
 , Ext "printNumber" (FnType $ FT [] [numType] Void)
 ]
