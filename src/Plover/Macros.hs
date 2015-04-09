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
wrapMain = FnDef "main" (FnT [] [] IntType)

-- Print a string with newlines
newline s = "printf" :$ (Str $ "\n" ++ s ++ "\n")

generateTestArguments :: Variable -> FunctionType -> M CExpr
generateTestArguments fnName (FnT implicits params output) = do
  is <- mapM pBind implicits
  es <- mapM pBind params
  let decls = seqList (is ++ es)
      call = Free (App (R fnName) (map (R . fst) params))
  return (decls :> call)
  
  where
    pBind (var, t) = do
      val <- pValue t
      return $ var := val
    pValue IntType =
      return (Call "randInt")
    pValue NumType =
      return (Call "randFloat")
    pValue t@(TypedefType _) = do
      n <- freshName
      let decl = Declare t n
      StructType _ (ST _ fields) <- normalizeType t
      fs <- mapM pBind fields
      let bs = map (\f -> (R n :. f) :< R f) (map fst fields)
      return $ seqList $
        [ decl ] ++ fs ++ bs ++ [ R n ]
    pValue (VecType ds t) = do
      body <- pValue t
      vec ds body
    vec [] body = return $ body
    vec (d : ds) b = do
      n <- freshName
      body <- vec ds b
      return $ Lam n d body

generatePrinter :: Variable -> Type -> M CExpr
generatePrinter var (VecType ds NumType) = do
  names <- mapM (\_ -> freshName) ds
  let body = ("printDouble" :$ foldl (:!) (R var) (map R names))
  let e = foldr (uncurry Lam) body (zip names ds)
  return e

testFunction var sig output tp = do
  test <- generateTestArguments var sig
  printer <- generatePrinter output tp
  return $ wrapMain (test :> printer)

-- The extern file declarations

externs = seqList
 [ Ext "sqrt"        (FnType $ fnT [numType] numType)
 , Ext "inverse"     (FnType $ FnT [("n", IntType)]
                                   [("input", VecType [R "n", R "n"] NumType),
                                    ("output", VecType [R "n", R "n"] NumType)]
                                   Void)
 , Ext "randFloat"       (FnType $ fnT [] numType)
 , Ext "randInt"       (FnType $ fnT [] IntType)
 , Ext "printf"      (FnType $ fnT [stringType] Void)
 , Ext "printDouble" (FnType $ fnT [numType] Void)
 , Ext "printInt" (FnType $ fnT [IntType] Void)
 ]
