{-# LANGUAGE OverloadedStrings #-}
module Plover.Macros where

import Control.Monad.Free

import Plover.Types

seqList :: [CExpr] -> CExpr
seqList es = foldr1 (:>) es

norm :: CExpr -> CExpr
norm x = "sqrt" :$ (Sig (x * x))

normalize :: CExpr -> CExpr
normalize x = x / norm x

transpose m = Free (Unary "transpose" m)
inverse m = Free (Unary "inverse" m)

wrapMain = Free . FunctionDecl "main" (FD [] IntType)

s x = Lam "i" 1 x

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
  let body = foldl (:!) (R var) (map R names)
  let e = foldr (uncurry Lam) body (zip names ds)
  return e

testFunction var sig output tp = do
  test <- generateTestArguments var sig
  printer <- generatePrinter output tp
  return $ wrapMain (test :> printer)

-- The extern file declarations

externs = seqList [
  Ext "sqrt" (FnType $ FT [] [numType] numType),
  Ext "inverse" (FnType $ FT [TV "n"]
                             [ExprType [TV "n", TV "n"], ExprType [TV "n", TV "n"]]
                             (ExprType [TV "n", TV "n"])),
  Ext "randf" (FnType $ FT [] [] numType),
  Ext "printFloat" (FnType $ FT [] [numType] Void)
 ]
