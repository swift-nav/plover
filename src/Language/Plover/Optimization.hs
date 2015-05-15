{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Plover.Optimization 
  ( refs
  , defs
  , seqExpr
  , hoist
  , canHoist
  , hoistTerm
  ) where

import Control.Monad.Free
import qualified Data.Foldable as F (fold)
import Debug.Trace (trace)
import Control.Monad.Writer

import Language.Plover.Types
import Language.Plover.Macros (seqList)
import Language.Plover.Generics (visitAny)

data Side = LHS | RHS

refs :: CExpr -> [Variable]
refs = refs' RHS

defs :: CExpr -> [Variable]
defs = defs' RHS

-- prototypical example:
--   x[i] <- z
--     =>
--   ["i", "z"]
refs' :: Side -> CExpr -> [Variable]
refs' RHS ((Ref _) :<= b) = refs' RHS b
refs' RHS (_ := b) = refs' RHS b
refs' RHS (a :<= b) = refs' LHS a `mappend` refs' RHS b
refs' LHS ((Ref _) :! ind) = refs' RHS ind
refs' _ (Ref v) = [v]
refs' side (Free f) = F.fold $ fmap (refs' side) f
refs' _ (Pure _) = mempty

defs' :: Side -> CExpr -> [Variable]
defs' _ (v := _) = [v]
defs' _ ((Ref v) :<= b) = [v] ++ defs' RHS b
defs' RHS (a :<= b) = defs' LHS a ++ defs' RHS b
defs' LHS ((Ref v) :! ind) = [v] ++ defs' RHS ind
defs' side (Free f) = F.fold $ fmap (defs' side) f
defs' _ (Pure _) = mempty


seqExpr :: CExpr -> [CExpr]
seqExpr (a :> b) = seqExpr a ++ seqExpr b
seqExpr VoidExpr = []
seqExpr e = [e]

canHoist :: CExpr -> Bool
canHoist = not . visitAny isCall
  where
    isCall (App _ _) = True
    isCall (AppImpl _ _ _) = True
    isCall _ = False

isAssignment :: CExpr -> Maybe CExpr
isAssignment (_ := r) = Just r
isAssignment (_ :<= r) = Just r
isAssignment _ = Nothing

setRHS :: CExpr -> CExpr -> CExpr
setRHS (a := _) e = a := e
setRHS (a :<= _) e = a :<= e
setRHS e _ = error $ "setRHS. not an assignment: " ++ show e

hoist :: Variable -> CExpr -> M ([CExpr], [CExpr])
hoist var expr =
  let exprs = seqExpr expr
      localDefs = var : defs expr
      canLift :: CExpr -> M (Writer [CExpr] CExpr)
      canLift e | Just rhs <- isAssignment e
                , not (any (`elem` localDefs) $ refs e) =
        case rhs of
          Ref _ -> return $ return e
          _ -> do
            n <- freshName
            return $ tell [(n := rhs)] >> return (setRHS e (Ref n))
      canLift e = return $ return e
  in do
    writers <- mapM canLift exprs
    return $ swap $ runWriter $ sequence writers
  where
    swap (a, b) = (b, a)


hoistTerm :: CExpr -> M CExpr
hoistTerm e@(Vec var bound body) =
  if canHoist body
  then do
    (pre, body') <- hoist var body
    let term =
          if length body' == 0
          then trace ("warning: hoisting optimization removed all contents of loop body")
               $ seqList pre
          else seqList $ pre ++ [(Vec var bound (seqList body'))]
    return term
  else return e
hoistTerm e = return e
