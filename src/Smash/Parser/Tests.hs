{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Smash.Parser.Tests where
import Smash.Parser.Types
import Name hiding (store, put, get)
import Control.Monad.Free
import Control.Monad.Trans.Either
import qualified Data.Map.Strict as M
import Data.Foldable (Foldable)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence, mapM)

pattern dim ::: fn = Free (EMLit (Mat Float dim fn))
pattern rs :* cs = Dim rs cs

p1 =
  [ "x" := 2
  , "y" := 2 :* 2 ::: \i j -> i + j
  ]

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
  [ "b" :> B ["x"] [] "x"
  , "y" := 22
  , "w" := 1 :* 1 ::: \_ _ -> 1
  , "z" := "b" :< ["w"]
  ]

p5 =
  [ "b" :> B ["x", "y"] ["z" := "x" * "y"] "z"
  , "u" := 2 :* 1 ::: \_ _ -> 1
  , "w" := 1 :* 2 ::: \_ _ -> 1
  , "a" := "b" :< ["u", "w"]
  ]
