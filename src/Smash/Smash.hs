{-# LANGUAGE ExistentialQuantification, Rank2Types #-}
{-# LANGUAGE PatternSynonyms #-}
module Smash.Smash where
import Smash.Parse.Tests
import Smash.Parse.Types as Types
import qualified Smash.Parse as P
import qualified Smash.Compile as C

import Control.Monad.Free
import Data.Maybe (fromJust)

totalCompile :: [Line] -> Either [UError] String
totalCompile lines =
  case P.typeCheck lines of
    Left errors -> Left errors
    Right lines -> return $ C.compileBlock (map convert lines)

convert :: TypedLine CType -> C.InputLine
convert (TLine ctype (LStore (Loc name) expr) context) =
  let (tp, e) =
        case ctype of
          TMatrix (Dim e1 e2) bt ->
            let rows = convertExpr e1
                cols = convertExpr e2
            in
            (C.IArray (rows * cols) (cbt bt),
             C.IRM (convertMatrix context expr))
          TLit bt -> (C.ISingle (cbt bt), C.IRE (convertExpr expr))
  in
    C.IL tp name e

type EMixed = Free Expr' C.MExpr

cbt :: BaseType -> C.BaseType
cbt Int = C.Int
cbt Float = C.Float
cbt VoidType = C.Void

type FCExpr = FExpr C.E

conjFn :: Types.MatFn -> C.E -> C.E -> C.E
conjFn fn e1 e2 = ce' $ fn (Pure e1) (Pure e2)
convertMatrix ::[(Variable, CType)] -> CExpr -> C.MExpr
convertMatrix c = cm c . fromFix

cm :: [(Variable, CType)] -> FCExpr -> C.MExpr
cm c (Free (EMul a b)) = cm c a * cm c b
cm c (Free (ESum a b)) = cm c a + cm c b
cm c (Free (ENeg x)) = - (cm c x)
cm c (Free (EMLit (Mat bt (Dim e1 e2) fn))) = 
  let fn' = conjFn fn
  in (C.MLit (C.Mat (convertExpr e1) (convertExpr e2) fn'))
cm c (Free (ERef var)) = 
  let TMatrix (Dim e1 e2) _ = fromJust $ lookup var c
  in C.MRef var (convertExpr e1) (convertExpr e2)

convertExpr :: ExprU -> C.E
convertExpr = ce' . fromFix
ce' :: FCExpr -> C.E
ce' (Free (EMul a b)) = ce' a * ce' b
ce' (Free (ESum a b)) = ce' a + ce' b
ce' (Free (ENeg a)) = - (ce' a)
ce' (Free (EIntLit i)) = fromIntegral i
ce' (Free (ERef var)) = (C.ELit (C.R var))
ce' (Pure e) = e

toExprU :: C.E -> FCExpr
toExprU = Pure


-- Testing
chk lines =
  case totalCompile lines of
    Left errors -> print "ERROR" >> mapM_ print errors
    Right str -> do
      putStrLn str

