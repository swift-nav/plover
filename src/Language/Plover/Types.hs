{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Plover.Types where

import qualified Data.Foldable as F (Foldable)
import qualified Data.Traversable as T (Traversable)
--import Control.Monad.Free
import Data.Functor.Fixedpoint
import Control.Monad.Trans.Either hiding (left)
import qualified Control.Monad.Trans.Either as E (left)
import Control.Monad.State
import Data.String
import Data.Ratio

--data Void
--deriving instance Show Void
--deriving instance Eq Void
--deriving instance Ord Void

--type Tag = String
type Variable = String

data IntType = U8 | S8
             | U16 | S16
             | U32 | S32
             | U64 | S64
             deriving (Eq, Ord, Show)
data FloatType = Float | Double
               deriving (Eq, Ord, Show)

data UnOp = Neg | Not
          | Transpose | Inverse
          | Sum | For
          deriving (Show, Eq, Ord)
data BinOp = Add | Sub | Mul | Div
           | Pow | Dot | Concat
           | And | Or
           | EqOp | LTOp | LTEOp
           deriving (Show, Eq, Ord)

data Range a = Range { rangeFrom :: a, rangeTo :: a, rangeStep :: a }
             deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

data Arg a = Arg a
           | ImpArg a
           deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

-- Main program type
-- Input programs are specified in the fixpoint of this type (CExpr).
-- The reduction compiler operates on them.
data Expr a
  -- Things at the top of the constructor list
  = Vec' Variable (Range a) a
  | Return' a -- TODO where is this allowed to appear? (Not inside a Vec, for example, maybe?)
  | Assert' a
  | RangeVal' (Range a)

  -- Control flow
  | If' a a a

  -- Elementary expressions
  | VoidExpr'
  | IntLit' (Maybe IntType) Integer
  | FloatLit' (Maybe FloatType) Double
  | StrLit' String
  | BoolLit' Bool
  | VecLit' [a]

  -- Things that change the context
--  | Extension' a
--  | Declare' (Type) Variable
--  | FunctionDef' Variable (FunctionType) a
--  | Extern' Variable (Type)
  | StructDecl' Variable StructType

  | Let' Variable a a
  | Seq a a

  -- Function application   TODO change for implicit arguments
  | App' a [Arg a]
  | ConcreteApp' a [a]

  -- Operators
  -- Symbolic patterns given below
  | Hole'
  | Get' (Location a)
  | Set' (Location a) a
  | AssertType' a Type
--  | FlatIndex' a a [a]
--  | Init Variable a
  | Unary' UnOp a
  | Binary' BinOp a a
 deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

data Location a = Ref' Type Variable
                | Index' a [a]
                | Field' a String
                | Deref' a
                deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

type CExpr = Fix Expr
pattern Free x = Fix x

-- Basic subset of C
-- Output of reduction compiler is transformed into Line
-- by Plover.Print.flatten
data Line
  -- All instances of CExpr should be numeric arithmetic only
  = Each Variable CExpr Line
  | IfStmt CExpr Line Line
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
-- The boolean means whether the argument is required (False means implicit)
data FunctionType = FnT [(Variable, Bool, Type)] Type
  deriving (Show, Eq, Ord)

data ExternalDef = External | Generated
 deriving (Show, Eq, Ord)

data StructType = ST
  { st_extern :: ExternalDef
  , st_fields :: [(Variable, Type)]
  -- , st_params :: [Type]
  }
 deriving (Show, Eq, Ord)

-- Function without implicits or a dependent type
fnT :: [Type] -> Type -> FunctionType
fnT params out = FnT [("", True, t) | t <- params] out

data Type' a
  = VecType [a] (Type' a)
  | Void
  | FnType FunctionType
--  | Dimension a
  | NumType -- some kind of number.  temporary; must become concrete numeric type
  | IntType (Maybe IntType)
  | FloatType (Maybe FloatType)
  | StringType -- null-terminated C string
  | BoolType
  | PtrType (Type' a)
  | TypedefType Variable
  -- Concrete ST has name, values for type parameters
  | StructType Variable StructType -- [a]
  | TypeHole
  deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

type Type = Type' CExpr

numType :: Type
numType = NumType

stringType :: Type
stringType = StringType

vecType :: [CExpr] -> Type
vecType t = VecType t NumType

data Definition = FunctionDef (Maybe CExpr) FunctionType
                | StructDef [(Variable, Type)]
                | ValueDef (Maybe CExpr) Type -- also used for function prototypes
                deriving Show
data DefBinding = DefBinding { binding :: Variable
                             , extern :: Bool
                             , static :: Bool
                             , def :: Definition }
                deriving Show

mkBinding :: Variable -> Definition -> DefBinding
mkBinding v d = DefBinding { binding = v
                           , extern = False
                           , static = False
                           , def = d }

-- Used for module definitions
-- (name, requirements (eg external parameters, struct defs), type, function body
--type FunctionDefinition = (Variable, FunctionType, CExpr)

data CompilationUnit = CU
  { unitName :: String
  , sourceDefs :: [DefBinding]
  , sourceIncs :: [String]
  , headerDefs :: [Variable] -- refers to DefBindings
  , headerIncs :: [String]
  }

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

showEnv :: TypeEnv -> String
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
--infix 4 :=
infix  4 :<=
infixr 5 :$
infixr 5 :=:
infixl 1 :>
infixl  6 :+, :*
infixr 6 :#
infix 7 :!
infix 8 :., :->
pattern Vec a b c = Free (Vec' a b c)
pattern If a b c = Free (If' a b c)
pattern RangeVal r = Free (RangeVal' r)
--pattern Ref a = Free (Ref' a)
--pattern Sigma x = Free (Unary' Sum x)
--pattern For x = Free (Unary' For x)
--pattern Ptr x = Free (Ptr' x)
pattern VoidExpr = Free VoidExpr'
pattern IntLit t a = Free (IntLit' t a)
pattern FloatLit t a = Free (FloatLit' t a)
-- pattern INumLit a = Free (INumLit' a)
pattern StrLit s = Free (StrLit' s)
pattern BoolLit s = Free (BoolLit' s)
pattern VecLit s = Free (VecLit' s)
--pattern Extension x = Free (Extension' x)
--pattern Declare t x = Free (Declare' t x)
pattern Return x = Free (Return' x)
pattern Assert x = Free (Assert' x)
--pattern FunctionDef a b c = Free (FunctionDef' a b c)
--pattern Extern v t = Free (Extern' v t)
pattern App f args = Free (App' f args)
pattern ConcreteApp f args = Free (ConcreteApp' f args)
pattern a :$ b = Free (App' a [b])
pattern Call a = Free (App' a [])
pattern StructDecl a b = Free (StructDecl' a b)
pattern Negate x = Free (Unary' Neg x)
pattern Equal a b = Free (Binary' EqOp a b)
pattern Unary tag x = Free (Unary' tag x)
pattern Binary tag x y = Free (Binary' tag x y)
pattern AssertType a ty = Free (AssertType' a ty)
pattern Hole = Free (Hole')
pattern Get x = Free (Get' x)
pattern Set l x = Free (Set' l x)
pattern a :<= b = Free (Set' a b)
--pattern a := b = Free (Init a b)
pattern a :=: b = Equal a b
pattern a :# b = Binary Concat a b
pattern a :+ b = Binary Add a b
pattern a :* b = Binary Mul a b
pattern a :/ b = Binary Div a b
--pattern FlatIndex a b c = Free (FlatIndex' a b c)
pattern a :> b = Free (Seq a b)
pattern Let v a b = Free (Let' v a b)

-- Locations
pattern a :! b = Index' a b
pattern Deref a = Deref' a
pattern a :. b = Field' a b
pattern a :-> b = Deref (Get (Field' a b))

instance IsString (Location (Fix Expr)) where
  fromString = Ref' TypeHole
instance IsString (Fix Expr) where
  fromString = Free . Get' . Ref' TypeHole

instance Num (Fix Expr) where
  x * y = x :* y
  x + y = x :+ y
  fromInteger x = (IntLit Nothing $ fromInteger x)
  abs = undefined
  signum = undefined
  negate = Negate

instance Fractional (Fix Expr) where
  x / y = x :/ y
  fromRational x = FloatLit Nothing $ fromIntegral (numerator x) / fromIntegral (denominator x)
