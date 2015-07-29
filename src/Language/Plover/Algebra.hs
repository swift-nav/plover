{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Plover.Algebra where

import Language.Plover.Types

flattenSum :: CExpr -> [CExpr]
flattenSum (Binary _ Add a b) = flattenSum a ++ flattenSum b
flattenSum x = [x]

isSimpleHole :: CExpr -> Maybe (Integer, Variable)
isSimpleHole (HoleJ _ v) = Just (1, v)
isSimpleHole (Unary _ Neg (HoleJ _ v)) = Just (-1, v)
isSimpleHole (Binary _ Mul (IntLit _ _ u) (HoleJ _ v)) | isUnit u = Just (u, v)
  where
    isUnit x = x == 1 || x == -1
isSimpleHole _ = Nothing

splitFirst f [] = Nothing
splitFirst f (x : xs) | Just v <- f x = return (v, xs)
splitFirst f (x : xs) = do
  (v, xs) <- splitFirst f xs
  return (v, x : xs)

substForm :: CExpr -> Maybe (Variable, CExpr)
substForm expr =
  let exprs = flattenSum expr
  in do
    ((u, v), es) <- splitFirst isSimpleHole exprs
    return (v, fromInteger (-u) * foldl (+) 0 es)


