{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.Plover.Macros where

import Language.Plover.Types

-- Sequence a list of CExprs
-- nb: cannot use foldr
seqList :: [CExpr] -> CExpr
seqList [] = VoidExpr
seqList es = foldl1 (:>) es

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

transpose :: CExpr -> CExpr
transpose m = (Unary "transpose" m)

inverse :: CExpr -> CExpr
inverse m = (Unary "inverse" m)

-- TODO better dense matrix notation
rot_small :: CExpr -> CExpr
rot_small (IntLit x) = rot_small $ NumLit (fromIntegral x)
rot_small x =
  blockMatrix [3,3]
    [ 1.0,  x,   0.0,
      (-x), 1.0, 0.0,
      0.0,  0.0, 1.0 ]

-- form a block matrix
blockMatrix :: [Int] -> [CExpr] -> CExpr
blockMatrix ds es | product ds /= length es = error $
    "blockMatrix. expr list length does not match given dimensions: " ++ sep ds es
blockMatrix [] [e] = e
blockMatrix [] e = error $
    "blockMatrix. zero dimension matrix with non-scalar expr: " ++ show e
blockMatrix (_ : dims) exprs =
  let size = product dims in
  let exprs' = map (blockMatrix dims) (split size exprs) in
    foldr1 (:#) (map Ptr exprs')
  where
    split _ [] = []
    split n ds = take n ds : split n (drop n ds)

-- Make a length 1 vector from x
s :: CExpr -> CExpr
s x = Ptr x

-- Wrap an expression in a main function
wrapMain :: CExpr -> CExpr
wrapMain body = FunctionDef "main" (FnT [] [] IntType) (body :> Return 0)

-- Print a string with newlines
newline :: String -> CExpr
newline str = "printf" :$ (StrLit $ "\n" ++ str ++ "\n")

generateTestArguments :: Variable -> FunctionType -> M CExpr
generateTestArguments fnName (FnT implicits params _) = do
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
      StructType _ (ST _ fields ) <- normalizeType t
      fs <- mapM pBind fields
      let bs = map (\f -> (Ref n :. f) :<= Ref f) (map fst fields)
      return $ seqList $
        [ decl ] ++ fs ++ bs ++ [ Ref n ]
    pValue (VecType ds t) = do
      body <- pValue t
      vec ds body
    pValue t = error $
      "generateTestArguments: don't know how to generate random value of type: "
      ++ show t
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
generatePrinter _ t = error $
  "generatePrinter: don't know how to generate printer for type: " ++ show t


testFunction :: Variable -> FunctionType -> Variable -> Type -> M CExpr
testFunction var sig output tp = do
  test <- generateTestArguments var sig
  printer <- generatePrinter output tp
  return $ wrapMain (test :> printer)

-- The extern file declarations

externs :: CExpr
externs = seqList
 [ Extern "assert"      (FnType $ fnT [BoolType] Void)
 , Extern "sqrt"        (FnType $ fnT [numType] numType)
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
