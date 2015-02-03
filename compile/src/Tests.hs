{-# LANGUAGE PatternSynonyms #-}
module Tests where
import Types
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
