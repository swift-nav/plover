{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification, Rank2Types #-}
module Smash.Parse.Types where
import Name hiding (store, put, get)
import Data.String
import Control.Monad.Free
import Control.Monad.Trans.Either
import qualified Data.Map.Strict as M
import Data.Foldable (Foldable)
import qualified Data.Traversable as T (Traversable)

type Variable = String

type RHS = ExprU
type LHS = ExprU

--data Loc 
--  = LName Variable
--  | LRef Loc RHS
--  deriving (Show, Eq, Ord)

data Line
  = LStore LHS RHS
  | Return RHS
  | Call Variable [RHS]

  | If RHS [Line] [Line]
  -- Output that gets value
  -- Variable
  -- Upper bound
  -- body function
  -- Last line should be `Return`
  | For LHS Variable RHS ([Line])
  deriving (Show, Eq, Ord)

pattern Loc l = Free (ERef l)

data TypedLine a = TLine a Line [(Variable, a)]
  deriving (Show, Eq, Ord)

--data RHS = RHSExpr ExprU
--  deriving (Show, Eq, Ord)

-- TODO
-- Free monad:
--data Program' a
--  = PLine Line a
--  | Done 
data False
deriving instance Show False
deriving instance Eq False
deriving instance Ord False
--type Program = Free Program' ()
--pattern l :== r = Free (PLine (l := r) ())
--declInt var = Free (PLine (LDecl var Int) ())
--declFloat var = Free (PLine (LDecl var Float) ())

fromFix :: Functor f => Free f False -> Free f a
fromFix = fmap (const undefined)

infix 4 :=
pattern l := r = LStore (Loc l) (r)

data Dim' a = Dim
  { dimRows :: a
  , dimColumns :: a
  }
  deriving (Show, Eq, Ord)
type Dim = Dim' Name
type DimU = Dim' ExprU

type MatFn = forall a. FExpr a -> FExpr a -> FExpr a
data Mat = Mat BaseType DimU MatFn
deriving instance Show Mat
deriving instance Eq Mat
deriving instance Ord Mat

data Expr' a
  = ERef Variable
  | EIntLit Int
  | EMul a a
  | ESum a a
  | ENeg a
  | EMLit Mat
  | Void
  -- Array index, struct membership?
  | a :! a
  | a :> a
  | a :< a

  deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)

type Expr = Expr' Name
type FExpr a = Free Expr' a
type ExprU = FExpr False
type CExpr = FExpr False

type TypeContext = M.Map Variable Name
type Context = TypeContext

data BaseType = Int | Float | VoidType
  deriving (Show, Eq, Ord)

data Type' b a
  = TMatrix (Dim' b) a
  | TLit BaseType
  deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)

type Type = Type' Name Name
type CType = Type' CExpr BaseType

-- IR of Unifier
data UValue
  = UType Type | UExpr Expr
  | UVar
  | UEq Name | UProduct Name Name | USum Name Name
  deriving (Show, Eq, Ord)

data UError = UError [Name] String
  deriving (Show, Eq, Ord)

type UnMonad = EnvMonad UValue

-- Operations that unify and may fail
type InnerM = EitherT UError UnMonad
-- Operations that run InnerM actions, handle errors
-- TODO aggregate errors?
type OuterM = UnMonad
-- Operations that simply use store/get
type M = UnMonad

-- STUFF --
instance Show (a -> b) where
  show _ = "<fn>"
-- TODO is this desirable?
instance Eq (a -> b) where
  _ == _ = False
instance Ord (a -> b) where
  compare _ _ = GT -- ???

instance IsString ExprU where
  fromString = Free . ERef
instance Num (Free Expr' a) where
  x * y = Free (EMul x y)
  x + y = Free (ESum x y)
  fromInteger x = Free (EIntLit $ fromInteger x)
  --abs = undefined
  --signum = undefined
  negate = Free . ENeg
