{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Plover.Types where

import qualified Data.Foldable as F (Foldable)
import qualified Data.Traversable as T (Traversable)
import Control.Monad.Free
import Control.Monad.Trans.Either
import Control.Monad.State
import Data.String

data Void
deriving instance Show Void
deriving instance Eq Void
deriving instance Ord Void

type Tag = String
type Variable = String

-- Main program type
-- Input programs are specified in this type, and the
-- reduction compiler operates on this type.
data Expr a
  = Abs Variable a a
  | Ref Variable
  | Index a a
  | Concat a a
  | Sigma a

  | Decl (Type' a) Variable
  | Init a a
  | Assign a a
  | Seq a a
  | Return a

  | IntLit Int
  | StrLit String

  | FunctionDecl Variable (FnDecl a) a
  | Extern Variable (Type' a)
  | App a [a]
  | AppImpl a [a] [a]

  -- TODO generalize these?
  | Sum a a
  | Mul a a
  | Div a a
  | Negate a

  | Unary Tag a
  | Binary Tag a a

  | Deref a

  -- Used to define parametric functions
  | TVar Variable

 deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

type CExpr = Free Expr Void

-- Basic subset of C
-- Output of reduction compiler is transformed into Line
-- by Plover.Print.flatten
data Line
  -- All instances of CExpr should be numeric arithmetic only
  = Each Variable CExpr Line
  | Block [Line]
  | Store CExpr CExpr
  | LineDecl Type Variable
  | LineExpr CExpr
  | EmptyLine
  | Function Variable (FnDecl CExpr) Line
  | LineReturn CExpr
  | Include String
  deriving (Show, Eq, Ord)

-- Datatypes to represent Expr types
-- TODO combine these two types
data FnType a = FT
  { implicits :: [a]
  , explicits :: [Type' a]
  , outputType :: Type' a
  }
  deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

data FnDecl a = FD
  { fd_params :: [(Variable, Type' a)]
  , fd_output :: Type' a
  }
  deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

data Type' a
  = ExprType [a]
  | Void
  | FnType (FnType a)
  | Dimension a
  | IntType
  | StringType
  deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

type Type = Type' CExpr

numType :: Type
numType = ExprType []

stringType :: Type
stringType = StringType

-- Typechecking/Compilation Monad --
type TypeEnv = (Int, [(Variable, Type)])
initialState :: TypeEnv
initialState = (0, [])

type Error = String
type M = EitherT Error (State TypeEnv)

-- Basic monad operations
freshName :: M Variable
freshName = do
  (c, env) <- get
  put (c+1, env)
  return ("var" ++ show c)

extend :: Variable -> Type -> M ()
extend var t = modify $ \(c, env) -> (c, (var, t) : env)

sep :: (Show a, Show b) => a -> b -> String
sep s1 s2 = show s1 ++ ", " ++ show s2

-- Syntax
infix  4 :=, :<
infix  5 :$
infixl 1 :>
infixl  6 :+, :*
infixr 6 :#
infix 7 :!
pattern a :< b = Free (Assign a b)
pattern a := b = Free (Init a b)
pattern a :# b = Free (Concat a b)
pattern a :+ b = Free (Sum a b)
pattern a :* b = Free (Mul a b)
pattern a :/ b = Free (Div a b)
pattern Lit a = Free (IntLit a)
pattern Lam a b c = Free (Abs a b c)
pattern R a = Free (Ref a)
pattern DR a = Free (Deref a)
pattern Sig x = Free (Sigma x)
pattern Neg x = Free (Negate x)
pattern Declare t x = Free (Decl t x)
pattern FnDeclare a b c = Free (FunctionDecl a b c)
pattern Ret x = Free (Return x)
pattern a :! b = Free (Index a b)
pattern a :> b = Free (Seq a b)
pattern a :$ b = Free (App a [b])
pattern TV v = Free (TVar v)
pattern Ext v t = Free (Extern v t)
pattern Str s = Free (StrLit s)

instance IsString (Free Expr a) where
  fromString = Free . Ref

instance Num (Free Expr a) where
  x * y = Free (Mul x y)
  x + y = Free (Sum x y)
  fromInteger x = Free (IntLit $ fromInteger x)
  abs = undefined
  signum = undefined
  negate = Free . Negate

instance Fractional (Free Expr a) where
  x / y = Free (Div x y)
