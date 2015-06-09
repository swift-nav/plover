{-# LANGUAGE QuasiQuotes #-}
module Language.Plover.QuoteTest where

import Language.Plover.Quote

cunit = [plover|
x := 2
|]
