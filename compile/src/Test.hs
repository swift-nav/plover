{-# LANGUAGE DeriveFunctor #-}

data T a = L | T a a
 deriving (Eq, Show, Functor)

same :: (Functor f, Eq (f ())) => f a -> f a -> Bool
same x y = fix x == fix y
 where
  fix = fmap (const ())
