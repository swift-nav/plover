{-# LANGUAGE PatternSynonyms #-}

-- Print a C ast
module Plover.Print where

import Control.Monad.Free
import Data.List (intercalate)

import Plover.Types

-- Printing output --
flatten :: CExpr -> Either Error Line
flatten (Extension _) = return EmptyLine
flatten (Declare t var) = return $ LineDecl t var
flatten (Vec var bound body) = do
  body' <- flatten body
  return $ Each var bound (body')
flatten (Ref a :<= val) = return $ Store (Ref a) val
flatten (n :<= val) = return $ Store (n) val
flatten (a :> b) = do
  a' <- flatten a
  b' <- flatten b
  return $ mergeBlocks a' b'
flatten (n := val) = return $ Store (Ref n) val
flatten (Extern _ _) = return EmptyLine
flatten e@(App _ _) = return $ LineExpr e
flatten e@(AppImpl _ _ _) = return $ LineExpr e
flatten e@(FunctionDef name fd body) = do
  body' <- flatten body
  return $ Function name fd body'
flatten (Return x) = return (LineReturn x)
flatten (StructDecl name (ST External _)) = return EmptyLine
flatten (StructDecl name (ST Generated fields)) =
  return $ TypeDefStruct name fields
flatten VoidExpr = return EmptyLine
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
-- TODO pp monad
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
    wrapp argString ++ "\n" ++
  off ++ "{\n" ++
    ppLine strict (indent off) body ++
  off ++ "}\n"
  where args = map (ppParam strict) (ps1 ++ ps2)
        argString = case args of
          [] -> "void"
          as -> intercalate ", " $ map (ppParam strict) (ps1 ++ ps2)
ppLine strict off (LineReturn x) =
  off ++ "return " ++ ppExpr strict x ++ lineEnd
ppLine strict off (ForwardDecl name (FnT ps1 ps2 out)) =
  off ++ ppType out ++ " " ++ name ++
    wrapp argString ++ lineEnd
  where args = map (ppParam strict) (ps1 ++ ps2)
        argString = case args of
          [] -> "void"
          as -> intercalate ", " $ map (ppParam strict) (ps1 ++ ps2)
ppLine strict off (TypeDefStruct name fields) =
  off ++ "typedef struct {\n" ++
    concatMap printField fields ++
  off ++ "} " ++ ppVar name ++ ";\n"
  where
    printField p@(name, t) = off ++ "  " ++ ppParam strict p ++ ";\n"
ppLine _ _ x = error $ "ppline. " ++ show x

lineEnd = ";\n"

ppParam strict (var, t) =
  let (pre, post) = ppTypeDecl strict t in
  pre ++ " " ++ ppVar var ++ post

ppVar = id

ppNumber = "double"

ppType :: Type -> String
ppType (NumType) = ppNumber
ppType (VecType _ t) = ppType t ++ " *"
ppType (Dimension _) = "int"
ppType IntType = "int"
ppType (TypedefType n) = ppVar n
ppType (StructType name _) = ppVar name
ppType Void = "void"
ppType t = error $ "ppType. " ++ show t

ppTypeDecl :: StrictGen -> Type -> (String, String)
ppTypeDecl _ (Void) = ("void", "")
ppTypeDecl strict t = printArrayType t
  where
    printArrayType (VecType es t) = (ppType t, concatMap printOne es)
    printArrayType StringType = ("char *", "")
    printArrayType IntType = ("int", "")
    printArrayType NumType = (ppNumber, "")
    printArrayType (TypedefType name) = (name, "")
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
    (Ref v) -> ppVar v
    (IntLit i) -> show i
    (NumLit f) -> show f
    (StrLit s) -> show s
    (a :! b) -> pe a ++ "[" ++ pe b ++ "]"
    (Deref x) -> "(*(" ++ pe x ++ "))"
    (Offset p off) -> pe (p :+ off)
    (Negate x) -> "-(" ++ pe x ++ ")"
    (App a args) -> pe a ++ wrapp (intercalate ", " (map pe args))
    (AppImpl a impls args) -> pe a ++ wrapp (intercalate ", " (map pe (impls ++ args)))
    (a :<= b)| Lax <- strict -> pe a ++ " <- " ++ pe b
    (a :. b) -> pe a ++ "." ++ ppVar b
    (a :> b) | Lax <- strict -> ppExpr Lax a ++ ";\n" ++ ppExpr Lax b
    e -> case strict of
           Strict -> error $ "ppExpr. " ++ show e
           Lax -> show e

