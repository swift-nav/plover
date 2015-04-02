{-# LANGUAGE PatternSynonyms #-}

-- Print a C ast
module Plover.Print where

import Control.Monad.Free
import Data.List (intercalate)

import Plover.Types

-- Printing output --
flatten :: CExpr -> Either Error Line
flatten (Declare t var) = return $ LineDecl t var
flatten (Lam var bound body) = do
  body' <- flatten body
  return $ Each var bound (body')
flatten (R a :< val) = return $ Store (R a) val
flatten (n :< val) = return $ Store (n) val
flatten (a :> b) = do
  a' <- flatten a
  b' <- flatten b
  return $ mergeBlocks a' b'
flatten (n := val) = return $ Store n val
flatten (Ext _ _) = return EmptyLine
flatten e@(Free (App _ _)) = return $ LineExpr e
flatten e@(Free (AppImpl _ _ _)) = return $ LineExpr e
flatten e@(FnDef name fd body) = do
  body' <- flatten body
  return $ Function name fd body'
flatten (Ret x) = return (LineReturn x)
flatten x = Left $ "flatten: " ++ show x

mergeBlocks :: Line -> Line -> Line
mergeBlocks (Block ls1) (Block ls2) = Block (ls1 ++ ls2)
mergeBlocks (Block ls) x = Block (ls ++ [x])
mergeBlocks x (Block ls) = Block (x : ls)
mergeBlocks x y = Block [x, y]

indent :: String -> String
indent off = "  " ++ off

-- Expects input to have a main function; adds includes
ppProgram :: Line -> String
ppProgram line = ppLine Strict "" line

-- Lax: printing will procede even if a term is not fully reduced, using its "Show" method
-- Strict: requires that the term is fully reduced by compile
data StrictGen = Strict | Lax
ppLine :: StrictGen -> String -> Line -> String
ppLine _ _ EmptyLine = ""
ppLine _ off (Include str) = off ++ "#include \"" ++ str ++ "\"\n"
ppLine strict off (Block ls) = concat $ map (ppLine strict off) ls
ppLine strict off (Each var expr body) = 
  let vs = ppVar var in
  off ++ "for (int " ++ vs ++ " = 0; " ++
  vs ++ " < " ++ ppExpr strict expr ++ "; " ++
  vs ++ "++) {\n"
    ++ ppLine strict (indent off) body
  ++ off ++ "}\n"
ppLine strict off (Store x e) =
  off ++ ppExpr strict (x) ++ " = " ++
  ppExpr strict e ++ lineEnd
ppLine strict off (LineExpr e) =
  off ++ ppExpr strict e ++ lineEnd
ppLine strict off (LineDecl t var) = 
  let (pre, post) = ppTypeDecl strict t in
  off ++ pre ++ " " ++ ppVar var ++ post ++ lineEnd
ppLine strict off (Function name (FnT ps1 ps2 out) body) =
  off ++ ppType out ++ " " ++ name ++
    wrapp (intercalate ", " (map (ppParam strict) (ps1 ++ ps2))) ++ "\n" ++
  off ++ "{\n" ++
    ppLine strict (indent off) body ++
  off ++ "}\n"
ppLine strict off (LineReturn x) =
  off ++ "return " ++ ppExpr strict x ++ lineEnd
ppLine strict off (ForwardDecl name (FnT ps1 ps2 out)) =
  off ++ ppType out ++ " " ++ name ++
    wrapp (intercalate ", " (map (ppParam strict) (ps1 ++ ps2))) ++ lineEnd
ppLine _ _ x = error $ "ppline. " ++ show x

lineEnd = ";\n"

ppParam strict (var, t) =
  let (pre, post) = ppTypeDecl strict t in
  pre ++ " " ++ ppVar var ++ post 

ppVar = id
ppNumber = "double"
-- TODO generalize
ppType :: Type -> String
ppType (ExprType []) = ppNumber
ppType (ExprType _) = ppNumber ++ " *"
ppType (Dimension _) = "int"
ppType IntType = "int"
ppType Void = "void"

ppTypeDecl :: StrictGen -> Type -> (String, String)
ppTypeDecl _ (Void) = ("void", "")
-- TODO general base type
ppTypeDecl strict t = printArrayType t
  where
    printVecType (ExprType []) = (ppNumber, "")
    printVecType (ExprType es) = (ppNumber, "[" ++ intercalate " * " (map (ppExpr strict) es) ++ "]")
    printArrayType (ExprType es) = (ppNumber, concatMap printOne es)
    printArrayType StringType = ("char *", "")
    printArrayType IntType = ("int", "")
    printArrayType e = error $ "printArrayType: " ++ show e
    printOne e = "[" ++ ppExpr strict e ++ "]"
wrapp s = "(" ++ s ++ ")"
ppExpr :: StrictGen -> CExpr -> String
ppExpr strict e =
  let pe = ppExpr strict in
  case e of
    (a :+ b) -> wrapp $ pe a ++ " + " ++ pe b
    (a :* b) -> wrapp $ pe a ++ " * " ++ pe b
    (a :/ b) -> wrapp $ pe a ++ " / " ++ pe b
    (R v) -> ppVar v
    (Lit i) -> show i
    (Str s) -> show s
    (a :! b) -> pe a ++ "[" ++ pe b ++ "]"
    (DR x) -> "(*(" ++ pe x ++ "))"
    (Neg x) -> "-(" ++ pe x ++ ")"
    (Free (App a args)) -> pe a ++ wrapp (intercalate ", " (map pe args))
    (Free (AppImpl a impls args)) -> pe a ++ wrapp (intercalate ", " (map pe (impls ++ args)))
    (a :< b) -> error "ppExpr.  :<"
    e -> case strict of
           Strict -> error $ "ppExpr. " ++ show e
           Lax -> show e

