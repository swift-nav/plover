{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module Data.Tag
       ( Tag(..), Tagged(..)
       , FixTagged, FixTagged'(..)
       , pattern FTag
       , untagged, wrapTag, wrapTags, addTag, addProv, newTag, newProv, getTag, getTags
       , Unique, TagGraph(..), toTagGraph
       ) where

import qualified Data.Foldable as F (Foldable, foldr)
import qualified Data.Traversable as T (Traversable, traverse)
import Data.Function
import Data.Fix
import Data.List
import Data.Data
import Control.Monad.State
import Control.Applicative ((<$>))

data Tag a = NoTag
           | Tag !a (Tag a)
           | ProvTag String (Tag a)
           | MergeTags [Tag a]
             deriving (Show, Eq, Ord, Typeable, Data)

data Tagged tag x = WithTag { maybeTag :: !(Tag tag)
                            , stripTag :: x }
                    deriving (Typeable, Data)

instance Eq a => Eq (Tagged tag a) where
  x == y  = stripTag x == stripTag y

instance Ord a => Ord (Tagged tag a) where
  compare = compare `on` stripTag

instance Functor (Tagged tag) where
  fmap f (WithTag mt a) = WithTag mt (f a)

instance F.Foldable (Tagged tag) where
  foldr f z x = f (stripTag x) z

instance T.Traversable (Tagged tag) where
  traverse f (WithTag tag a) = WithTag tag <$> f a


data FixTagged' tag t a = FixTagged' (Tagged tag (t a))
                        deriving (Typeable, Data)

instance Functor t => Functor (FixTagged' tag t) where
  fmap f (FixTagged' x) = FixTagged' (fmap (fmap f) x)

instance F.Foldable t => F.Foldable (FixTagged' tag t) where
  foldr f z (FixTagged' x) = F.foldr f z (stripTag x)

instance T.Traversable t => T.Traversable (FixTagged' tag t) where
  traverse f (FixTagged' (WithTag tag a)) = FixTagged' . WithTag tag <$> T.traverse f a

instance Show (t a) => Show (FixTagged' tag t a) where
  show (FixTagged' x) = "(" ++ show (stripTag x) ++ ")"

type FixTagged tag t = Fix (FixTagged' tag t)
pattern FTag tag a = Fix (FixTagged' (WithTag tag a))

instance Eq (t a) => Eq (FixTagged' tag t a) where
  (FixTagged' x) == (FixTagged' y)  =  stripTag x == stripTag y
instance Ord (t a) => Ord (FixTagged' tag t a) where
  compare (FixTagged' x) (FixTagged' y) = (compare `on` stripTag) x y


-- | Lifts an untagged type to the fixed tagged type.
untagged :: t (FixTagged tag t) -> FixTagged tag t
untagged x = FTag NoTag x

-- | Lifts an untagged type to the fixed tagged type by adding a given tag.
wrapTag :: Tag tag -> t (FixTagged tag t) -> FixTagged tag t
wrapTag = FTag

-- | Lifts an untagged type to the fixed tagged type by adding a number of tags.
wrapTags :: [Tag tag] -> t (FixTagged tag t) -> FixTagged tag t
wrapTags tags = FTag (MergeTags tags)

-- | Add a tag of the base tag type to the front of the tag list
addTag :: tag -> FixTagged tag t -> FixTagged tag t
addTag tag' (FTag mt x) = FTag (Tag tag' mt) x

-- | Add a provenance tag to the front of the tag list
addProv :: String -> FixTagged tag t -> FixTagged tag t
addProv prov (FTag mt x) = FTag (ProvTag prov mt) x

-- | Add a new tag of the base tag type to an untagged tree
newTag :: tag -> t (FixTagged tag t) -> FixTagged tag t
newTag tag x = addTag tag $ untagged x

-- | Add provenance to an untagged tree
newProv :: String -> t (FixTagged tag t) -> FixTagged tag t
newProv prov x = addProv prov $ untagged x

getTag :: FixTagged tag t -> Tag tag
getTag (FTag mt _) = mt

-- | Gets all tags from a tag node
getTags :: Tag t -> [t]
getTags NoTag = []
getTags (Tag t mt) = t : getTags mt
getTags (ProvTag _ mt) = getTags mt
getTags (MergeTags tags) = tags >>= getTags

-- Making a graph

newtype Unique = Unique Int
data TagGraph tag t = TagGraph [(Unique, Tag tag, t Unique)]

instance Show Unique where
  show (Unique i) = "#" ++ show i

instance (Show tag, Show (t Unique)) => Show (TagGraph tag t) where
  show (TagGraph xs) = "TagGraph [\n" ++ intercalate "\n" (map f xs) ++ "\n]"
    where f (i, msp, expr) = " " ++ show i
                             ++ " = " ++ show expr ++ ";"
                             ++ "   \t[" ++ show_tag msp ++ "]"
          show_tag NoTag = ""
          show_tag (Tag pos msp)  = show pos ++ "; " ++ show_tag msp
          show_tag (ProvTag s msp) = show msp ++ "; " ++ show_tag msp
          show_tag (MergeTags tags) = "Merged: [" ++ intercalate ", " (map show_tag tags) ++ "]"

toTagGraph :: T.Traversable t => FixTagged tag t -> TagGraph tag t
toTagGraph x = TagGraph $ evalState (f x >> get) []
  where f (FTag tag e) = do
          e' <- T.traverse f e
          i <- Unique . length <$> get
          modify (++ [(i, tag, e')])
          return i
