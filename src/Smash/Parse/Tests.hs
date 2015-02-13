{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Smash.Parse.Tests where
import Smash.Parse.Types
import Control.Monad.Free

-- TODO monad syntax
pattern dim ::: fn = Free (EMLit (Mat Float dim fn))
pattern rs :* cs = Dim rs cs

m1 = (2 :* 2 ::: \_ _ -> 1)

p1 =
  [ "x" := 2
  , "z" := ("x" + "x") * "x"
  , "y" := 2 :* 2 ::: \i j -> i + j
  ]

pn = [ "z" := m1 - m1 ]
pn' = [ "z" := m1 + m1 ]
pm = [ "z" := -2 ]

p2 =
  [ "x" := 1 :* 2 ::: \_ _ -> 1
  , "y" := 2 :* 3 ::: \i j -> i + j
  , "z" := "x" * "y"
  ]
p3 =
  [ "x" := 1 :* 2 ::: \_ _ -> 1
  , "y" := 1 :* 2 ::: \i j -> i + j
  , "z" := "x" + "y"
  ]

p4 =
  let b = id in
  [
    "y" := 22
  , "w" := 1 :* 1 ::: \_ _ -> 1
  , "z" := b "w"
  ]

-- Bad program:
p5 =
  let b x y = x * y in
  [
    "u" := 2 :* 1 ::: \_ _ -> 1
  , "w" := 2 :* 2 ::: \_ _ -> 1
  , "a" := b "u" "w"
  ]

p6 =
  [ "m" := "y" :* "z" ::: \_ _ -> 1
  , "n" := "z" :* "y" ::: \_ _ -> 1
  , "k" := "m" * "n"
  ]


p7 =
  let one = (1 :* 1 ::: \_ _ -> 1) in
  [ "x" := one * one ]
