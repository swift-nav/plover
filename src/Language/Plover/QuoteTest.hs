{-# LANGUAGE QuasiQuotes #-}
module Language.Plover.QuoteTest where

import Language.Plover.Quote

cunit = [plover|
          struct ((x))

x = 2 :: u8
         
|]
