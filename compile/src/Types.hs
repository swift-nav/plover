{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Types where
import Data.String
import Name hiding (store, put, get)
import Control.Monad.Free
import Control.Monad.Trans.Either
import qualified Data.Map.Strict as M
import Data.Foldable (Foldable)
import qualified Data.Traversable as T (Traversable, mapAccumR, sequence, mapM)

type Variable = String

data Loc 
  = LName Variable
  -- | LIndex Loc Expr -- TODO
  | LVoid
  deriving (Show, Eq, Ord)

data Line = LStore Loc RHS
  deriving (Show, Eq, Ord)

data RHS = RHSExpr ExprU
         | RHSBlock [Variable] [Line]
         | RHSVoid -- TODO remove?
  deriving (Show, Eq, Ord)

infix 4 :=, :<, :>
pattern l := r = LStore (LName l) (RHSExpr r)
pattern ps :> body = RHSBlock ps body
pattern l :< rhsb = LStore (LName l) rhsb

type View2 a = a -> a -> a
data Dim' a = Dim a a
  deriving (Show, Eq, Ord)
type Dim = Dim' Name
type DimU = Dim' ExprU
rows (Dim r _) = r
cols (Dim _ c) = c

data Mat = Mat BaseType DimU (View2 ExprU)
  deriving (Show, Eq, Ord)

data Expr' a
  = ERef Variable
  | EIntLit Int
  | EMLit Mat
  | EMul a a
  | ESum a a
  | ECall Variable [a]
  deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)
type Expr = Expr' Name
type ExprU = Free Expr' Name

-- Parameters, body, definition context
data Block = Block [Variable] [Line] Context
  deriving (Show, Eq, Ord)

type BlockContext = M.Map Variable Block
type TypeContext = M.Map Variable Name
type Context = (BlockContext, TypeContext)

data BaseType = Int | Float | Void
  deriving (Show, Eq, Ord)

data Type' a
  = TMatrix (Dim' Name) a
  | TLit BaseType
  deriving (Show, Eq, Ord, Functor, Foldable, T.Traversable)

type Type = Type' Name

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
  show f = "<fn>"
-- TODO is this desirable?
instance Eq (a -> b) where
  a == b = False
instance Ord (a -> b) where
  compare a b = GT -- ???

instance IsString ExprU where
  fromString = Free . ERef
instance Num ExprU where
  x * y = Free (EMul x y)
  x + y = Free (ESum x y)
  fromInteger x = Free (EIntLit $ fromInteger x)
  abs = undefined
  signum = undefined
  negate = undefined
