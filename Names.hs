module Names
  ( freshName, NameMonad, Name
  , runName
  ) where
import Control.Monad.State 
import Control.Applicative

type Name = String
type NameMonad = State Int

toName :: Int -> Name
toName = ("n" ++) . show 

fresh :: NameMonad Int
fresh = do
  n <- get
  put (n+1)
  return n
freshName :: NameMonad Name
freshName = toName <$> fresh
-- Dangerous?
lastName :: NameMonad Name
lastName = toName <$> get

runName m = evalState m 0
