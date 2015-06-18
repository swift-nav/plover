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
--import Data.Functor.Fixedpoint
import Control.Monad.Trans.Either hiding (left)
import qualified Control.Monad.Trans.Either as E (left)
import Control.Monad.State
import Data.String
import Data.Ratio
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Data.Tag


-- Core AST

type Variable = String
-- | Unification variable
type UVar = String

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
--  | StructDecl' Variable StructType

  | Let' Variable a a
  | Uninitialized' Type -- Only for using Let to create a new variable to be used as a return value from a function
  | Seq' a a

  -- Function application   TODO change for implicit arguments
  | App' a [Arg a]
  | ConcreteApp' a [a]

  -- Operators
  -- Symbolic patterns given below
  | Hole' (Maybe UVar)
  | Get' (Location a)
  | Set' (Location a) a
  | Addr' (Location a)
  | AssertType' a Type
--  | FlatIndex' a a [a]
--  | Init Variable a
  | Unary' UnOp a
  | Binary' BinOp a a
 deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

data Location a = Ref Type Variable
                | Index a [a]
                | Field a String
                | Deref a
                deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

type CExpr = FixTagged SourcePos Expr
pattern PExpr pos x = FTag pos x

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
  { --st_extern :: ExternalDef
     st_fields :: [(Variable, Type)]
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
  | TypeHole (Maybe UVar)
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
                | ValueDef (Maybe CExpr) Type
                deriving Show
data DefBinding = DefBinding { binding :: Variable
                             , bindingPos :: Tag SourcePos
                             , extern :: Bool
                             , static :: Bool
                             , definition :: Definition }
                deriving Show

mkBinding :: Tag SourcePos -> Variable -> Definition -> DefBinding
mkBinding pos v d = DefBinding { binding = v
                               , bindingPos = pos
                               , extern = False
                               , static = False
                               , definition = d }

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

pattern Vec tag a b c = PExpr tag (Vec' a b c)
pattern If tag a b c = PExpr tag (If' a b c)
pattern RangeVal tag r = PExpr tag (RangeVal' r)
pattern VoidExpr tag = PExpr tag VoidExpr'
pattern IntLit tag t a = PExpr tag (IntLit' t a)
pattern FloatLit tag t a = PExpr tag (FloatLit' t a)
pattern StrLit tag s = PExpr tag (StrLit' s)
pattern BoolLit tag s = PExpr tag (BoolLit' s)
pattern VecLit tag s = PExpr tag (VecLit' s)
pattern Return tag x = PExpr tag (Return' x)
pattern Assert tag x = PExpr tag (Assert' x)
pattern App tag f args = PExpr tag (App' f args)
pattern ConcreteApp tag f args = PExpr tag (ConcreteApp' f args)
pattern Call tag a = PExpr tag (App' a [])
pattern Unary tag op x = PExpr tag (Unary' op x)
pattern Binary tag op x y = PExpr tag (Binary' op x y)
pattern Negate tag x = Unary tag Neg x
pattern Equal tag a b = Binary tag EqOp a b
pattern AssertType tag a ty = PExpr tag (AssertType' a ty)
pattern Hole tag muvar= PExpr tag (Hole' muvar)
pattern Get tag x = PExpr tag (Get' x)
pattern Addr tag x = PExpr tag (Addr' x)
pattern Set tag l x = PExpr tag (Set' l x)
pattern Seq tag a b = PExpr tag (Seq' a b)
pattern Let tag v a b = PExpr tag (Let' v a b)
pattern Uninitialized tag ty = PExpr tag (Uninitialized' ty)
--pattern FlatIndex a b c = Fix (FlatIndex' a b c)
--pattern Ref a = Fix (Ref' a)
--pattern Sigma x = Fix (Unary' Sum x)
--pattern For x = Fix (Unary' For x)
--pattern Ptr x = Fix (Ptr' x)
--pattern FunctionDef a b c = Fix (FunctionDef' a b c)
--pattern Extern v t = Fix (Extern' v t)
--pattern Extension x = Fix (Extension' x)
--pattern Declare t x = Fix (Declare' t x)
-- pattern INumLit a = Fix (INumLit' a)
--pattern StructDecl tag a b = PExpr tag (StructDecl' a b)

-- Warning: These operators use NoTag, so they cannot be used in a pattern position correctly.
pattern a :<= b = Set NoTag a b
pattern a :=: b = Equal NoTag a b
pattern a :# b = Binary NoTag Concat a b
pattern a :+ b = Binary NoTag Add a b
pattern a :* b = Binary NoTag Mul a b
pattern a :/ b = Binary NoTag Div a b
pattern a :> b = Seq NoTag a b
pattern a :$ b = App NoTag a [b]
--pattern a := b = Fix (Init a b)

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


-- Locations
pattern a :! b = Index a b
pattern a :. b = Field a b
pattern a :-> b = Deref (Get NoTag (Field a b))

instance IsString (Location CExpr) where
  fromString = Ref (TypeHole Nothing)
instance IsString CExpr where
  fromString = untagged . Get' . Ref (TypeHole Nothing)

instance Num CExpr where
  x * y = x :* y
  x + y = x :+ y
  fromInteger x = untagged $ IntLit' Nothing $ fromInteger x
  abs = undefined
  signum = undefined
  negate = untagged . Unary' Neg

instance Fractional CExpr where
  x / y = x :/ y
  fromRational x = untagged $ FloatLit' Nothing $ fromIntegral (numerator x) / fromIntegral (denominator x)
