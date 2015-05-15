{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Plover.Optimization 
  ( refs
  , defs
  , seqExpr
  , hoist
  ) where

import Control.Monad.Free
import qualified Data.Foldable as F (fold)
import Data.Monoid (mappend, mempty, mconcat)
import Data.List (partition)

import Language.Plover.Types
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
refs' RHS (a :<= b) = refs' LHS a `mappend` refs' RHS b
refs' LHS ((Ref _) :! ind) = refs' RHS ind
refs' _ (Ref v) = [v]
refs' side (Free f) = F.fold $ fmap (refs' side) f
refs' _ (Pure _) = mempty

defs' :: Side -> CExpr -> [Variable]
defs' _ (v := _) = [v]
defs' _ ((Ref v) :<= b) = [v] ++ defs' RHS b
defs' RHS (a :<= b) = defs' LHS a ++ defs' RHS b
defs' LHS ((Ref v) :! ind) = [v]
defs' side (Free f) = F.fold $ fmap (defs' side) f


seqExpr :: CExpr -> [CExpr]
seqExpr (a :> b) = seqExpr a ++ seqExpr b
seqExpr VoidExpr = []
seqExpr e = [e]

canHoist :: CExpr -> Bool
canHoist = not . visitAny isCall
  where
    isCall (App _ _) = True
    isCall _ = False

hoist :: CExpr -> ([CExpr], [CExpr])
hoist expr =
  let exprs = seqExpr expr
      localDefs = defs expr
      canLift e = not $ any (`elem` localDefs) $ refs e
  in
    partition canLift exprs
