-- TODO make this general and apply in MGen
module Unification where
import Name
import Control.Monad.Trans.Either
import Control.Monad.Trans.Class

data UValue = Foo Int | Bar Int | Var

type UnMonad error = EitherT error (EnvMonad UValue)
type M = UnMonad String

match :: Name -> M Int
match n = do
  val <- lift $ get n
  case val of
    Var -> do
      lift $ store (Foo 22)
      right 22
    Bar _ -> left $ "bar: " ++ show n
    Foo n -> right n


runM = evalEnv . runEitherT 

test1 = runM $ do
  n1 <- lift . store $ Bar 2
  n2 <- lift . store $ Foo 3
  match n2
test2 = runM $ do
  n1 <- lift . store $ Bar 2
  n2 <- lift . store $ Foo 3
  match n1
  match n2
