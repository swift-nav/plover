module Plover.Generics where

import Data.List (intercalate)
import Data.Monoid hiding (Sum)
import qualified Data.Foldable as F (Foldable, fold)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence, mapM, traverse)
import Control.Applicative ((<$>))
import Control.Monad.Free
import Control.Monad.Trans.Either
import Control.Monad.State
import Data.String
import Data.Maybe (fromJust)
import Data.Function (on)

import Plover.Types

-- Generic fold
iterMon :: (Monoid m, Functor f) => (f m -> m) -> Free f m -> m
iterMon _ (Pure m) = m
iterMon fn (Free f) = fn $ fmap (iterMon fn) f

-- Generic map
unwrap :: Functor f => Free f a -> Free f (Free f a)
unwrap (Free f) = Free $ fmap unwrap f
unwrap (Pure a) = Pure (Pure a)

-- TODO why is this so slow?
visit :: (Functor f) => (Free f a -> Free f a) -> Free f a -> Free f a
---- iterM passes in an unwrapped expr (:: Expr CExpr),
---- so we fmap subst and then rewrap it with Free
visit f = f . iter (Free . fmap (visit f)) . unwrap

mvisit f g x =
  case f x of
    Nothing -> iterM (Free . fmap (mvisit f g)) x
    Just x' -> g x'

fromFix :: (Functor f) => Free f Void -> Free f a
fromFix = fmap undefined

fixM :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixM f x = do
  x' <- f x
  if x == x' then return x else fixM f x'

scanM :: (Eq a, Monad m) => (a -> m a) -> a -> m [a]
scanM f x = scan [] x
  where
    scan xs x = do
      x' <- f x
      let l = x : xs
      if x == x' then return l else scan l x'
