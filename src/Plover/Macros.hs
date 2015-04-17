{-# LANGUAGE OverloadedStrings #-}
module Plover.Macros where

import Control.Monad.Free

import Plover.Types

-- Sequence a list of CExprs
-- TODO add a noop to Expr so this is total
seqList :: [CExpr] -> CExpr
seqList es = foldr1 (:>) es

-- Slice vector from index i, length l
slice :: CExpr -> CExpr -> CExpr -> CExpr
slice x i l = Vec "i" l (x :! ("i" + i))

-- Vector dot product
dot :: CExpr -> CExpr -> CExpr
dot x y = Sigma (x * y)

-- Vector norm
norm :: CExpr -> CExpr
norm x = "sqrt" :$ x `dot` x

normalize :: CExpr -> CExpr
normalize x = x / norm x

transpose m = (Unary "transpose" m)
inverse m = (Unary "inverse" m)

-- TODO better dense matrix notation
rot_small :: CExpr -> CExpr
rot_small x =
  s (s 1     :# s x :# s 0) :#
  s (s (- x) :# s 1 :# s 0) :#
  s (s 0     :# s 0 :# s 1)

-- Make a length 1 vector to hold the argument
s :: CExpr -> CExpr
s x = Vec "i" 1 x

-- Wrap an expression in a main function
wrapMain = FunctionDef "main" (FnT [] [] IntType)

-- Print a string with newlines
newline s = "printf" :$ (StrLit $ "\n" ++ s ++ "\n")

generateTestArguments :: Variable -> FunctionType -> M CExpr
generateTestArguments fnName (FnT implicits params output) = do
  is <- mapM pBind implicits
  es <- mapM pBind params
  let decls = seqList (is ++ es)
      call = (App (Ref fnName) (map (Ref . fst) params))
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
      let bs = map (\f -> (Ref n :. f) :<= Ref f) (map fst fields)
      return $ seqList $
        [ decl ] ++ fs ++ bs ++ [ Ref n ]
    pValue (VecType ds t) = do
      body <- pValue t
      vec ds body
    vec [] body = return $ body
    vec (d : ds) b = do
      n <- freshName
      body <- vec ds b
      return $ Vec n d body

generatePrinter :: Variable -> Type -> M CExpr
generatePrinter var (VecType ds NumType) = do
  names <- mapM (\_ -> freshName) ds
  let body = ("printDouble" :$ foldl (:!) (Ref var) (map Ref names))
  let e = foldr (uncurry Vec) body (zip names ds)
  return e

testFunction var sig output tp = do
  test <- generateTestArguments var sig
  printer <- generatePrinter output tp
  return $ wrapMain (test :> printer)

-- The extern file declarations

externs = seqList
 [ Extern "sqrt"        (FnType $ fnT [numType] numType)
 , Extern "inverse"     (FnType $ FnT [("n", IntType)]
                                   [("input", VecType [Ref "n", Ref "n"] NumType),
                                    ("output", VecType [Ref "n", Ref "n"] NumType)]
                                   Void)
 , Extern "randFloat"       (FnType $ fnT [] numType)
 , Extern "randInt"       (FnType $ fnT [] IntType)
 , Extern "printf"      (FnType $ fnT [stringType] Void)
 , Extern "printDouble" (FnType $ fnT [numType] Void)
 , Extern "printInt" (FnType $ fnT [IntType] Void)
 ]
