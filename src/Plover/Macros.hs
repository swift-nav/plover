{-# LANGUAGE OverloadedStrings #-}
module Plover.Macros where

import Control.Monad (foldM)
import Control.Monad.Free
import Data.List (foldl')

import Plover.Types

-- Sequence a list of CExprs
-- nb: cannot use foldr
seqList :: [CExpr] -> CExpr
seqList es = foldl' (:>) VoidExpr es

-- Vector norm
norm :: CExpr -> CExpr
norm x = "sqrt" :$ (Sigma (x * x))

normalize :: CExpr -> CExpr
normalize x = x / norm x

transpose m = (Unary "transpose" m)
inverse m = (Unary "inverse" m)

-- TODO better dense matrix notation
rot_small :: CExpr -> CExpr
rot_small (IntLit x) = rot_small $ NumLit (fromIntegral x)
rot_small x =
  blockMatrix [3,3]
    [ 1.0,  x,   0.0,
      (-x), 1.0, 0.0,
      0.0,  0.0, 1.0 ]

--rot_small' :: CExpr -> CExpr
--rot_small' (IntLit x) = rot_small $ NumLit (fromIntegral x)
--rot_small' x =
--  s (s 1.0     :# s x   :# s 0.0) :#
--  s (s (- x)   :# s 1.0 :# s 0.0) :#
--  s (s 0.0     :# s 0.0 :# s 1.0)

-- form a block matrix
blockMatrix :: [Int] -> [CExpr] -> CExpr
blockMatrix ds es | product ds /= length es = error $
    "blockMatrix. expr list length does not match given dimensions: " ++ sep ds es
blockMatrix [] [e] = e
blockMatrix (dim : dims) exprs =
  --assert (dim * product dims == length exprs) $
  --  "blockMatrix. expr list length does not match given dimensions: " ++ sep dims exprs
  let size = product dims in
  let exprs' = map (blockMatrix dims) (split size exprs) in
    foldr1 (:#) (map Ptr exprs')
  where
    split n [] = []
    split n ds = take n ds : split n (drop n ds)

-- Make a length 1 vector from x
s :: CExpr -> CExpr
s x = Ptr x

-- Wrap an expression in a main function
wrapMain body = FunctionDef "main" (FnT [] [] IntType) (body :> Return 0)

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
