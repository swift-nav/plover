{-# LANGUAGE QuasiQuotes #-}
module Language.Plover.QuoteTest where

import Language.Plover.Quote
import Language.Plover.ParserTypes

rot_small :: Expr -> Expr
rot_small x = [pexp| vec(vec(1.0, ~x, 0.0),
                         vec(- ~x, 1.0, 0.0),
                         vec(0.0, 0.0, 1.0)) |]

cunit = [ptop|
         foo (v :: double[3]) :: double[3]
           := ~(rot_small 22.0) * v;
        |]

f :: Expr -> Expr
f [pexp| ~x + ~y |] = x * y
f z = z

--main = compileUnit "pvt" [f, cunit
