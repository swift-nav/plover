-- TODO make this general and apply in MGen
module Unification where
import Name
import Control.Monad.Trans.Either
import Control.Monad.Trans.Class
import Control.Applicative ((<$>))

import qualified Data.Map as M
import qualified Control.Monad.State as S

type Lens a b = (a -> b, b -> a -> a)

liftL :: Lens b a -> S.State a out -> S.State b out
liftL (get, set) m = do
  s <- S.gets get
  let (out, s') = S.runState m s
  S.modify $ set s'
  return out

idLens = (id, const)

type Hook m a = a -> Maybe (m ())
data UnState m a = UnState
  { env :: (Int, Env a)
  , hooks :: Env [Hook m a]
  }
type UnMonad m a = S.State (UnState m a)

ulens = (env, \e s -> s {env = e})

ulift :: EnvMonad a b -> UnMonad m a b
ulift = liftL ulens

ustore :: a -> UnMonad m a Name
ustore = ulift . store

partitionM :: [a] -> (a -> Maybe b) -> ([b], [a])
partitionM [] f = ([], [])
partitionM (x : xs) f =
  let (bs, as) = partitionM xs f in
  case f x of
    Nothing -> (bs, x : as)
    Just b -> (b : bs, as)

refine :: Monad m => Name -> a -> UnMonad m a (m ())
refine name val = do
  hs <- maybe [] id . (M.lookup name) <$> S.gets hooks
  let (ready, waiting) = partitionM hs ($ val)
  ulift $ put name val
  S.modify $ \s -> s {hooks = M.insert name waiting (hooks s)}
  return (sequence_ ready)

hook :: Monad m => Name -> Hook m a -> UnMonad m a (m ())
hook name h = do
  S.modify $ \s -> s {hooks = M.insertWith (++) name [h] (hooks s)}
  -- Call hook with existing value in case it is already resolvable
  current <- ulift (get name)
  refine name current

--prodProp :: Name -> Name -> Name -> Type -> Maybe (EnvMonad Type ())
--prodProp m1 m2 prod Mat = Just $ do
--  unifyMatProd m1 m2 prod
--prodProp e1 e2 prod Int = Just $ do
--  unifyInt e1
--  unifyInt e2
--  unifyInt prod
--prod _ _ _ _ = Nothing
