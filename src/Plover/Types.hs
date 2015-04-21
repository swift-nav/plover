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
import Control.Monad.Trans.Either hiding (left)
import qualified Control.Monad.Trans.Either as E (left)
import Control.Monad.State
import Control.Arrow (first, second)
import Data.String
import Data.Ratio

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
  = Vec' Variable a a
  | Ref' Variable
  | Sigma' a
  | Ptr' a

  | VoidExpr'
  | IntLit' Int
  | NumLit' Float
  -- | INumLit' Int
  | StrLit' String

  | Declare' (Type) Variable
  | Return' a

  | FunctionDef' Variable (FunctionType) a
  | Extern' Variable (Type)
  | App' a [a]
  | AppImpl' a [a] [a]

  | Negate' a
  | Deref' a
  | Offset' a a

  | Unary' Tag a
  -- | Binary Tag a a

  -- structs
  | StructDecl' Variable StructType

  -- Operators
  | Index a a
  | Concat a a
  | Init Variable a
  | Assign a a
  | Seq a a
  | Sum a a
  | Mul a a
  | Div a a
  | StructMemberRef a Variable
  | StructPtrRef a Variable

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
  | Function Variable (FunctionType) Line
  | ForwardDecl Variable (FunctionType)
  | LineReturn CExpr
  | Include String
  | TypeDefStruct Variable [(Variable, Type)]
  deriving (Show, Eq, Ord)

-- Represents the type of an Expr
-- Separates implicit parameters, explicit parameters, output type
data FunctionType = FnT
  { ft_imp :: [(Variable, Type)]
  , ft_exp :: [(Variable, Type)]
  , ft_out :: Type
  }
  deriving (Show, Eq, Ord)

data ExternalDef = External | Generated
 deriving (Show, Eq, Ord)

data StructType = ST
  { st_extern :: ExternalDef
  , st_fields :: [(Variable, Type)]
  }
 deriving (Show, Eq, Ord)

-- Function without implicits or a dependent type
fnT :: [Type] -> Type -> FunctionType
fnT params out = FnT [] (zip (repeat "") params) out

data Type' a
  = VecType [a] (Type' a)
  | Void
  | FnType FunctionType
  | Dimension a
  | IntType
  | NumType
  | StringType
  | PtrType (Type' a)
  | TypedefType Variable
  | StructType Variable StructType
  deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

type Type = Type' CExpr

numType :: Type
numType = NumType

stringType :: Type
stringType = StringType

vecType t = VecType t NumType

-- Used for module definitions
-- (name, requirements (eg external parameters, struct defs), type, function body
type FunctionDefinition = (Variable, [CExpr], FunctionType, CExpr)

type TypeEnv = [(Variable, Type)]
-- Typechecking/Compilation Monad --
-- (name counter, (variable types, typedef types))
data Context = TE
  { count :: Int
  , var_types :: TypeEnv
  , typedefs :: TypeEnv
  , term_stack :: [CExpr]
  }
  deriving (Show, Eq, Ord)

initialState :: Context
initialState = TE 0 [] [] []

type Error = String
type M = EitherT Error (State Context)

showEnv = unlines . map show

-- Basic monad operations
left :: Error -> M a
left msg = do
  stack <- gets term_stack
  env <- getVarTypes
  E.left $ msg ++ "\n\nexpr stack:\n" ++ unlines (map (++ "\n") $ map (show) $ take 1 stack)
    ++ "\n" ++ (unlines (map show env))

assert :: Bool -> Error -> M ()
assert cond msg = if cond then return () else left msg

freshName :: M Variable
freshName = do
  c <- gets count
  modify $ \s -> s { count = count s + 1 }
  return ("var" ++ show c)

getVarTypes :: M TypeEnv
getVarTypes = gets var_types

setVarTypes :: TypeEnv -> M ()
setVarTypes e = modify $ \s -> s { var_types = e }

varType :: Variable -> M Type
varType var = do
  env <- getVarTypes
  case lookup var env of
    Nothing -> left $ "undefined var: \"" ++ var ++ "\"\nin environment:\n" ++ showEnv env
    Just t -> return t

typedefType :: Variable -> M Type
typedefType var = do
  env <- gets typedefs
  case lookup var env of
    Nothing -> left $ "undefined typedef: \"" ++ var ++ "\"\nin environment:\n" ++ showEnv env
    Just t -> return t

-- Walks typedef chains before assigning a type
extend :: Variable -> Type -> M ()
extend var t =
  case t of
    TypedefType name -> do
      t' <- typedefType name
      extend var t'
    _ -> do
      env <- getVarTypes
      case lookup var env of
        Nothing ->
          modify $ \s -> s { var_types = (var, t) : var_types s }
        _ -> left $ "variable redefinition: " ++ show var ++ "\n" ++ showEnv env

extendTypedef :: Variable -> Type -> M ()
extendTypedef var t = modify $ \s -> s { typedefs = (var, t) : typedefs s }

normalizeType :: Type -> M Type
normalizeType (TypedefType name) = typedefType name >>= normalizeType
normalizeType (VecType [] t) = return t
normalizeType t = return t

sep :: (Show a, Show b) => a -> b -> String
sep s1 s2 = show s1 ++ ", " ++ show s2

-- Syntax
infix  4 :=, :<=
infixr 5 :$
infixl 1 :>
infixl  6 :+, :*
infixr 6 :#
infix 7 :!
infix 8 :., :->
pattern Vec a b c = Free (Vec' a b c)
pattern Ref a = Free (Ref' a)
pattern Sigma x = Free (Sigma' x)
pattern Ptr x = Free (Ptr' x)
pattern VoidExpr = Free VoidExpr'
pattern IntLit a = Free (IntLit' a)
pattern NumLit a = Free (NumLit' a)
-- pattern INumLit a = Free (INumLit' a)
pattern StrLit s = Free (StrLit' s)
pattern Declare t x = Free (Declare' t x)
pattern Return x = Free (Return' x)
pattern FunctionDef a b c = Free (FunctionDef' a b c)
pattern Extern v t = Free (Extern' v t)
pattern App f args = Free (App' f args)
pattern a :$ b = Free (App' a [b])
pattern Call a = Free (App' a [])
pattern AppImpl a b c = Free (AppImpl' a b c)
pattern StructDecl a b = Free (StructDecl' a b)
pattern Negate x = Free (Negate' x)
pattern Deref a = Free (Deref' a)
pattern Offset a b = Free (Offset' a b)
pattern Unary tag x = Free (Unary' tag x)
pattern a :<= b = Free (Assign a b)
pattern a := b = Free (Init a b)
pattern a :# b = Free (Concat a b)
pattern a :+ b = Free (Sum a b)
pattern a :* b = Free (Mul a b)
pattern a :/ b = Free (Div a b)
pattern a :! b = Free (Index a b)
pattern a :> b = Free (Seq a b)
pattern a :-> b = Free (StructPtrRef a b)
pattern a :. b = Free (StructMemberRef a b)

instance IsString (Free Expr a) where
  fromString = Ref

instance Num (Free Expr a) where
  x * y = x :* y
  x + y = x :+ y
  fromInteger x = (IntLit $ fromInteger x)
  abs = undefined
  signum = undefined
  negate = Negate

instance Fractional (Free Expr a) where
  x / y = x :/ y
  fromRational x = NumLit $ fromIntegral (numerator x) / fromIntegral (denominator x)
