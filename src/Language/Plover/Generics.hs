module Language.Plover.Generics where

import Data.Monoid hiding (Sum)
import Control.Monad.Free

import Language.Plover.Types

-- Generic fold
iterMon :: (Monoid m, Functor f) => (f m -> m) -> Free f m -> m
iterMon _ (Pure m) = m
iterMon fn (Free f) = fn $ fmap (iterMon fn) f

visit :: (Functor f) => (Free f a -> Free f a) -> Free f a -> Free f a
visit f (Free t) = f $ Free $ fmap (visit f) t
visit f x = f x

mvisit :: Functor f => (Free f a -> Maybe t) -> (t -> Free f a) -> Free f a -> Free f a
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
scanM f a = scan [] a
  where
    scan xs x = do
      x' <- f x
      let l = x : xs
      if x == x' then return l else scan l x'
