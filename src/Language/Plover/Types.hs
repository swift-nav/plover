{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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
import Control.Monad.Identity
import Control.Applicative ((<$>), (<*>), pure, Applicative)
import Data.String
import Data.Ratio
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Data.Tag
import Data.Functor.Fixedpoint
import Data.Char
import Data.Data
import Text.PrettyPrint

import qualified Language.Plover.Simplify as S

-- Core AST

type Variable = String
-- | Unification variable
type UVar = String

data IntType = U8 | S8
             | U16 | S16
             | U32 | S32
             | U64 | S64
             | IDefault
             deriving (Eq, Ord, Show, Typeable, Data)
data FloatType = Float | Double
               | FDefault
               deriving (Eq, Ord, Show, Typeable, Data)

-- data StorageType = DenseMatrix
--                  | DiagonalMatrix
--                  | UpperTriangular
--                  | UpperUnitTriangular
--                  | LowerTriangular
--                  | LowerUnitTriangular
--                  | SymmetricMatrix
--                  | BlockMatrix [[Type]]
--                  deriving (Eq, Ord, Show, Typeable, Data)

defaultIntType :: IntType
defaultIntType = IDefault

actualDefaultIntType :: IntType
actualDefaultIntType = S32

defaultFloatType :: FloatType
defaultFloatType = FDefault

actualDefaultFloatType :: FloatType
actualDefaultFloatType = Double

data UnOp = Neg | Not
          | Transpose | Inverse
          | Sum
          deriving (Show, Eq, Ord)
data BinOp = Add | Sub | Mul | Div
           | Pow | Dot | Concat
           | And | Or
           | EqOp | LTOp | LTEOp
           deriving (Show, Eq, Ord)

data Range a = Range { rangeFrom :: a, rangeTo :: a, rangeStep :: a }
             deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

rangeLength :: Tag SourcePos -> Range CExpr -> CExpr
--rangeLength pos (Range (IntLit _ _ 0) to (IntLit _ _ 1)) = to
--rangeLength pos (Range from to (IntLit _ _ 1)) = Binary pos Sub to from
rangeLength pos (Range from to step) = reduceArithmetic $ Binary pos Div (Binary pos Sub to from) step

data Arg a = Arg a
           | ImpArg a
           deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

-- Main program type
-- Input programs are specified in the fixpoint of this type (CExpr).
-- The reduction compiler operates on them.
data Expr a
  -- Things at the top of the constructor list
  = Vec' Variable (Range a) a
  | For' Variable (Range a) a
  | Return' a -- TODO where is this allowed to appear? (Not inside a Vec, for example, maybe?)
  | Assert' a
  | RangeVal' (Range a)

  -- Control flow
  | If' a a a

  -- Elementary expressions
  | VoidExpr'
  | IntLit' IntType Integer
  | FloatLit' FloatType Double
  | StrLit' String
  | BoolLit' Bool
  | VecLit' Type [a] -- the type is the base type of the vector (for 0-element case)

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
  | Hole' (Maybe (Type, UVar)) -- type and value hole
  | Get' (Location a)
  | Addr' (Location a)
  | Set' (Location a) a
  | AssertType' a Type
--  | FlatIndex' a a [a]
--  | Init Variable a
  | Unary' UnOp a
  | Binary' BinOp a a
 deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

data Location a = Ref Type Variable
                | Index a [a]
                | Field a String -- auto-dereferences 'a' if it is a pointer^n to a struct
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
data FunctionType = FnT [(Variable, Bool, ArgDir, Type)] Type
  deriving (Show, Eq, Ord)

data ArgDir = ArgIn | ArgOut | ArgInOut
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
fnT params out = FnT [("", True, ArgIn, t) | t <- params] out


-- | If a function returns a complex type, it must be passed as an
-- extra argument.  The maybe variable gives the new variable name.
-- N.B. The new variable name is _deterministically_ chosen.  This
-- means `getEffectiveFunType` must be what is called whenever one
-- wants to know the return variable name.
-- TODO: returning a tuple? (right now can just return a struct)
getEffectiveFunType :: FunctionType -> (FunctionType, Maybe (Variable, Type))
getEffectiveFunType ft@(FnT args retty) = if complexRet retty
                                          then internReturn args' retty
                                          else ((FnT args' retty), Nothing)
  where complexRet :: Type -> Bool
        complexRet (VecType _ _) = True
--        complexRet (TypedefType _) = True  -- don't worry about structs: C will provide!
--        complexRet (StructType _ _) = True
        -- Any mistake in here will just end up causing a "don't know how to program this" message later
        complexRet _ = False

        --args' = maybeAddVoid args
        args' = args

        -- Puts the return into the argument list.  TODO should it be
        -- the type itself, or should it be Ptrized?  The semantics of
        -- type itself seem correct so far.  Perhaps In/Out/InOut are
        -- in order to record these things better
        internReturn :: [(Variable, Bool, ArgDir, Type)] -> Type -> (FunctionType, Maybe (Variable, Type))
        internReturn args retty = (FnT (args ++ [(retName, True, ArgOut, retty')]) Void, Just (retName, retty'))
          where retName = genName [v | (v, _, _, _) <- args] "result$"
                genName :: [Variable] -> Variable -> Variable
                genName names test = if test `elem` names
                                     then genName names (test ++ "$")
                                     else test
                retty' = retty

-- | Adds a void argument if there are no required arguments.
withPossibleVoid :: FunctionType -> FunctionType
withPossibleVoid (FnT args retty) = FnT (maybeAddVoid args) retty
  where maybeAddVoid :: [(Variable, Bool, ArgDir, Type)] -> [(Variable, Bool, ArgDir, Type)]
        maybeAddVoid args | null [True | (_,r,_,_) <- args, r]  = args ++ [("", True, ArgIn, Void)]
                          | otherwise                           = args

-- withoutVoids :: FunctionType -> FunctionType
-- withoutVoids (FnT args retty) = FnT (removeVoid args) retty
--   where removeVoid :: [(Variable, Bool, ArgDir, Type)] -> [(Variable, Bool, ArgDir, Type)]
--         removeVoid = filter

data Type' a
  = VecType [a] (Type' a)
  | Void
  | FnType FunctionType
--  | Dimension a
  | NumType -- some kind of number.  temporary; must become concrete numeric type
  | IntType IntType
  | FloatType FloatType
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

definitionType :: DefBinding -> Type
definitionType def = case definition def of
  FunctionDef _ ft -> FnType ft
  StructDef fields -> StructType (binding def) $ ST fields
  ValueDef _ ty -> ty

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

--sep :: (Show a, Show b) => a -> b -> String
--sep s1 s2 = show s1 ++ ", " ++ show s2

pattern Vec tag a b c = PExpr tag (Vec' a b c)
pattern For tag a b c = PExpr tag (For' a b c)
pattern If tag a b c = PExpr tag (If' a b c)
pattern RangeVal tag r = PExpr tag (RangeVal' r)
pattern VoidExpr tag = PExpr tag VoidExpr'
pattern IntLit tag t a = PExpr tag (IntLit' t a)
pattern FloatLit tag t a = PExpr tag (FloatLit' t a)
pattern StrLit tag s = PExpr tag (StrLit' s)
pattern BoolLit tag s = PExpr tag (BoolLit' s)
pattern VecLit tag ty s = PExpr tag (VecLit' ty s)
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

pattern HoleJ pos ty a = Hole pos (Just (ty, a))
pattern TypeHoleJ a = TypeHole (Just a)

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
  fromInteger x = untagged $ IntLit' defaultIntType $ fromInteger x
  abs = undefined
  signum = undefined
  negate = untagged . Unary' Neg

instance Fractional CExpr where
  x / y = x :/ y
  fromRational x = untagged $ FloatLit' defaultFloatType $ fromIntegral (numerator x) / fromIntegral (denominator x)




class TermMappable a where
  mapTerm :: (Applicative m, Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
          -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
          -> a -> m a
  termMapper :: (Applicative m, Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
             -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
             -> a -> m a

instance TermMappable Type where
  mapTerm tty texp tloc trng ty = case ty of
    VecType idxs ety -> VecType <$> mapM texp idxs <*> tty ety
    PtrType pty -> PtrType <$> tty pty
    FnType (FnT args retty) -> do
      args' <- forM args $ \(v, b, dir, ty) -> do
        ty' <- tty ty
        return (v, b, dir, ty')
      retty' <- tty retty
      return $ FnType $ FnT args' retty'
    _ -> return ty
  termMapper tty texp tloc trng = tty

instance TermMappable CExpr where
  mapTerm tty texp tloc trng exp = case exp of
    Vec pos v range expr -> Vec pos v <$> trng range <*> texp expr
    For pos v range expr -> For pos v <$> trng range <*> texp expr
    Return pos v -> Return pos <$> texp v
    Assert pos v -> Assert pos <$> texp v
    RangeVal pos range -> RangeVal pos <$> trng range
    If pos a b c -> If pos <$> texp a <*> texp b <*> texp c
    VecLit pos ty exprs -> VecLit pos <$> tty ty <*> mapM texp exprs
    Let pos v val expr -> Let pos v <$> texp val <*> texp expr
    Uninitialized pos ty -> Uninitialized pos <$> tty ty
    Seq pos p1 p2 -> Seq pos <$> texp p1 <*> texp p2
    App pos fn args -> App pos <$> texp fn <*> mapM targ args
      where targ (Arg a) = Arg <$> texp a
            targ (ImpArg a) = ImpArg <$> texp a
    ConcreteApp pos fn args -> ConcreteApp pos <$> texp fn <*> mapM texp args
    Get pos loc -> Get pos <$> tloc loc
    Addr pos loc -> Addr pos <$> tloc loc
    Set pos loc val -> Set pos <$> tloc loc <*> texp val
    AssertType pos v ty -> AssertType pos <$> texp v <*> tty ty
    Unary pos op v -> Unary pos op <$> texp v
    Binary pos op v1 v2 -> Binary pos op <$> texp v1 <*> texp v2
    _ -> return exp
  termMapper tty texp tloc trng = texp

instance TermMappable (Location CExpr) where
  mapTerm tty texp tloc trng loc = case loc of
    Ref ty v -> Ref <$> tty ty <*> pure v
    Index a idxs -> Index <$> texp a <*> mapM texp idxs
    Field a member -> Field <$> texp a <*> pure member
    Deref a -> Deref <$> texp a
  termMapper tty texp tloc trng = tloc

instance TermMappable (Range CExpr) where
  mapTerm tty texp tloc trng (Range from to step) =
    Range <$> texp from <*> texp to <*> texp step
  termMapper tty texp tloc trng = trng

traverseTerm :: (Applicative m, Monad m, TermMappable a)
             => (Type -> m Type) -> (CExpr -> m CExpr)
             -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
             -> a -> m a
traverseTerm fty fexp floc frng x = mapTerm tty texp tloc trng x >>= termMapper fty fexp floc frng
  where tty = traverseTerm fty fexp floc frng
        texp = traverseTerm fty fexp floc frng
        tloc = traverseTerm fty fexp floc frng
        trng = traverseTerm fty fexp floc frng


intUnsigned :: IntType -> Bool
intUnsigned IDefault = intUnsigned actualDefaultIntType
intUnsigned U8 = True
intUnsigned U16 = True
intUnsigned U32 = True
intUnsigned U64 = True
intUnsigned _ = False

intBits :: IntType -> Int
intBits IDefault = intBits actualDefaultIntType
intBits U8 = 8
intBits S8 = 8
intBits U16 = 16
intBits S16 = 16
intBits U32 = 32
intBits S32 = 32
intBits U64 = 64
intBits S64 = 64

floatBits :: FloatType -> Int
floatBits FDefault = floatBits actualDefaultFloatType
floatBits Float = 32
floatBits Double = 64

-- | Promote to an int type for use in arithmetic
promoteInt :: IntType -> IntType
promoteInt t
  | intBits t < intBits IDefault  = IDefault
  | otherwise = t

arithInt :: IntType -> IntType -> IntType
arithInt t1 t2 = arithInt' t1' t2'
  where t1' = promoteInt t1
        t2' = promoteInt t2

        arithInt' IDefault y = y
        arithInt' x IDefault = x
        arithInt' x y
          | intBits x > intBits y = x
          | intBits x < intBits y = y
          | intUnsigned x  = x
          | intUnsigned y  = y
          | otherwise = x

-- | Promote a float type for use in arithmetic
promoteFloat :: FloatType -> FloatType
promoteFloat t
  | floatBits t < floatBits FDefault = FDefault
  | otherwise = t

intMerge :: IntType -> IntType -> IntType
intMerge IDefault y = intMerge actualDefaultIntType y
intMerge x IDefault = intMerge x actualDefaultIntType
intMerge x y
  | x == y   = x
  | intBits x < intBits y  = intMerge y x
  | intBits x == intBits y  = case x of -- then y has opposite sign
                               U8 -> S16
                               S8 -> S16
                               U16 -> S32
                               S16 -> S32
                               _ -> S64
  | intUnsigned x == intUnsigned y  = x -- x has more bits
  | intUnsigned x  = case x of
                      U8 -> S16
                      S8 -> S16
                      U16 -> S32
                      S16 -> S32
                      _ -> S64
  | otherwise = x 

-- | Gets the int type (of the two) which can hold both ints (maybe).
intPromotePreserveBits :: IntType -> IntType -> Maybe IntType
intPromotePreserveBits IDefault y = Just y
intPromotePreserveBits x IDefault = Just x
intPromotePreserveBits x y
  | x == y  = Just x
  | intBits x > intBits y  = intPromotePreserveBits y x
  | intUnsigned x == intUnsigned y  = Just y -- y has more bits and signedness is the same
  | intBits x == intBits y  = Nothing -- signedness different
  | intUnsigned x  = Just y  -- then x surely fits
  | otherwise  = Nothing

arithFloat :: FloatType -> FloatType -> FloatType
arithFloat x y = floatMerge (promoteFloat x) (promoteFloat y)

floatMerge :: FloatType -> FloatType -> FloatType
floatMerge FDefault y = y
floatMerge x FDefault = x
floatMerge Float y = y
floatMerge x Float = x
floatMerge x y = Double

-- | Determines whether a location of the first int type can comfortably
-- hold a location of the second.
intCanHold :: IntType -> IntType -> Bool
intCanHold _ IDefault = True
intCanHold d s
  | intBits d < intBits s = False
  | intUnsigned d = intUnsigned s
  | otherwise = not (intUnsigned s) || intBits d > intBits s

-- | Determines whether a location of the first float type can
-- comfortably hold a location of the second.
floatCanHold :: FloatType -> FloatType -> Bool
floatCanHold _ FDefault = True
floatCanHold Float Double = False
floatCanHold _ _ = True

-- | Assumes already unified, so only really need to look at integer/float types.
typeCanHold :: Type -> Type -> Bool
typeCanHold ty1 ty2 = typeCanHold' (normalizeTypes ty1) (normalizeTypes ty2)

typeCanHold' :: Type -> Type -> Bool
typeCanHold' (VecType idxs1 bty1) (VecType idxs2 bty2)
  | length idxs1 == length idxs2  = typeCanHold' bty1 bty2
typeCanHold' Void Void = True
typeCanHold' (FnType _) (FnType _) = False -- TODO
typeCanHold' NumType NumType = True
typeCanHold' NumType (IntType {}) = True
typeCanHold' NumType (FloatType {}) = True
typeCanHold' (IntType t1) NumType = False
typeCanHold' (IntType t1) (IntType t2) = True -- intCanHold t1 t2
typeCanHold' (IntType t1) (FloatType {}) = False
typeCanHold' (FloatType t1) NumType = False
typeCanHold' (FloatType t1) (IntType {}) = True
typeCanHold' (FloatType t1) (FloatType t2) = floatCanHold t1 t2
typeCanHold' StringType StringType = True
typeCanHold' BoolType BoolType = True
typeCanHold' (PtrType t1) (PtrType t2) = typeCanHold' t1 t2
typeCanHold' (TypedefType v1) (TypedefType v2)
  | v1 == v2  = True
typeCanHold' (TypedefType v1) (StructType v2 _)
  | v1 == v2  = True
typeCanHold' (StructType v1 _) (TypedefType v2)
  | v1 == v2  = True
typeCanHold' (StructType v1 _) (StructType v2 _)
  | v1 == v2  = True
typeCanHold' (TypeHole mv1) (TypeHole mv2) = mv1 == mv2
typeCanHold' _ _ = False

normalizeTypes :: TermMappable a => a -> a
normalizeTypes = runIdentity . (traverseTerm tty texp tloc trng)
  where tty ty = case ty of
          VecType [] ty -> return ty
          VecType idxs1 (VecType idxs2 ty) -> return $ VecType (idxs1 ++ idxs2) ty
          _ -> return ty
        texp = return
        tloc = return
        trng = return

reduceArithmetic :: CExpr -> CExpr
reduceArithmetic expr =
  case (toExpr expr) of
    Nothing -> expr
    Just e' -> S.simplify scale e'
  where
    scale :: Integer -> CExpr -> CExpr
    scale (-1) x = -x
    scale 1 x = x
    scale 0 x = 0
    scale x (IntLit tag tp 1) = IntLit tag tp x
    scale x y = fromInteger x * y

    toExpr :: CExpr -> Maybe (S.Expr CExpr Integer)
    toExpr (Unary _ Neg (IntLit _ _ i)) = return $ S.Prim (-i)
    toExpr (Unary _ Neg a) = do
      a' <- toExpr a
      return $ S.Mul [S.Prim (-1), a']
    toExpr (Binary _ op a b) = do
      a' <- toExpr a
      b' <- toExpr b
      case op of
        Add -> return $ S.Sum [a', b']
        Mul -> return $ S.Mul [a', b']
        Sub -> return $ S.Sum [a', S.Mul [S.Prim (-1), b']]
        -- TODO
        Div | S.Prim 1 <- b' -> return a'
        Div | S.Prim (-1) <- b' -> return $ S.Mul [S.Prim (-1), a']
        _ -> Nothing
    toExpr (IntLit _ _ i) = return $ S.Prim i
    toExpr g@(Get _ (Ref _ _)) = return $ S.Atom g
    toExpr g@(HoleJ _ _ _) = return $ S.Atom g
    toExpr _ = Nothing

class PP a where
  pretty :: a -> Doc

instance PP (t a) => PP (FixTagged' tag t a) where
  pretty (FixTagged' x) = pretty (stripTag x)

instance PP (a (Fix a)) => PP (Fix a) where
  pretty (Fix x) = pretty x


instance PP Type where
  pretty v@(VecType {}) = case normalizeTypes v of
                           VecType idxs ty -> pretty ty <> brackets (sep $ punctuate comma (map pretty idxs))
                           ty' -> pretty ty'
  pretty Void = text "Void"
  pretty (FnType (FnT args retty)) = parens $ hang (text "func") 5 (sep $ map prarg args)
    where prarg (v, req, dir, ty) = (rqimp req) $ pdir (sep $ punctuate (text "::") [text v, pretty ty])
            where pdir x = case dir of
                    ArgIn -> x
                    ArgOut -> sep [text "out", x]
                    ArgInOut -> sep [text "inout", x]
          rqimp True = parens
          rqimp False = braces
  pretty NumType = text "Num"
  pretty (IntType IDefault) = text "int"
  pretty (IntType t) = text $ map toLower $ show t
  pretty (FloatType FDefault) = text "double"
  pretty (FloatType t) = text $ map toLower $ show t
  pretty StringType = text "string"
  pretty BoolType = text "bool"
  pretty (PtrType t) = parens $ hang (text "*") 2 (pretty t)
  pretty (TypedefType v) = text v
  pretty (StructType v _) = text v
  pretty (TypeHole (Just v)) = text v -- should have $ so shouldn't conflict
  pretty (TypeHole Nothing) = text "$hole"
  pretty x = text $ show x

instance (Show a, PP a) => PP (Expr a) where
  pretty (VoidExpr') = text "Void"
  pretty (IntLit' _ x) = text $ show x
  pretty (FloatLit' _ x) = text $ show x
  pretty (StrLit' x) = text $ show x
  pretty (BoolLit' x) = text $ show x
  pretty (Hole' (Just (ty, v))) = text v -- <+> text "::" <+> pretty ty -- it should start with $ so shouldn't conflict
  pretty (Hole' Nothing) = parens $ text "$hole"
  pretty (Get' loc) = pretty loc
  pretty (Addr' loc) = parens $ hang (text "&") 2 (pretty loc)
  pretty (Unary' op expr) = parens $ pretty op <+> pretty expr
  pretty (Binary' op x y) = parens $ pretty x <+> pretty op <+> pretty y
  pretty x = text $ show x

instance PP UnOp where
  pretty Neg = text "-"
  pretty Not = text "not"
  pretty Transpose = text "transpose"
  pretty Inverse = text "inverse"
  pretty Sum = text "sum"

instance PP BinOp where
  pretty Add = text "+"
  pretty Sub = text "-"
  pretty Mul = text "*"
  pretty Div = text "/"
  pretty Pow = text "^"
  pretty Concat = text "#"
  pretty And = text "and"
  pretty Or = text "or"
  pretty EqOp = text "=="
  pretty LTOp = text "<"
  pretty LTEOp = text "<="

instance PP a => PP (Location a) where
  pretty (Ref ty v) = text v -- <+> text "::" <+> pretty ty
  pretty (Index ty idxs) = pretty ty <> brackets (sep $ punctuate comma (map pretty idxs))
  pretty (Field a field) = pretty a <> text ("." ++ field)
  pretty (Deref a) = parens $ hang (text "*") 2 (pretty a)


getType :: CExpr -> Type
getType (Vec pos _ range base) = VecType [rangeLength pos range] (getType base)
getType (For {}) = Void
-- getType (Return ) -- what type?
-- getType (Assert )
getType (RangeVal pos range) = VecType [rangeLength pos range] (IntType IDefault)
getType (If pos a b c) = getType b
getType (VoidExpr pos) = Void
getType (IntLit pos t _) = IntType t
getType (FloatLit pos t _) = FloatType t
getType (StrLit {}) = StringType
getType (BoolLit {}) = BoolType
getType (VecLit pos ty xs) = VecType [IntLit pos IDefault (fromIntegral $ length xs)] ty
getType (Let pos v x body) = getType body
getType (Uninitialized pos ty) = ty
getType (Seq pos a b) = getType b
getType (ConcreteApp pos f args) = let FnType (FnT params retty) = getType f
                                   in retty
getType (App {}) = error "App should not be here"
getType (Hole pos Nothing) = error "Hole should not be here"
getType (Hole pos (Just (ty, _))) = ty
getType (Get pos loc) = getLocType loc
getType (Addr pos loc) = PtrType (getLocType loc)
getType (Set {}) = Void
getType (AssertType _ _ ty) = ty
getType (Unary pos Neg a) = getVectorizedType (getType a) (getType a)
getType (Unary pos Sum a) = case getVectorizedType (getType a) (getType a) of
  VecType (idx:idxs) aty' -> normalizeTypes $ VecType idxs aty'
  aty' -> aty'
getType (Unary pos Inverse a) = do
  case normalizeTypes $ getType a of
   VecType [a, _] aty' -> VecType [a, a] (getArithType aty' $ FloatType defaultFloatType)
   _ -> error "Unary inverse on not a rectangular vector"
getType (Unary pos Transpose a) = do
  case normalizeTypes $ getType a of
   VecType (i1:i2:idxs) aty' -> VecType (i2:i1:idxs) aty'
   VecType [idx] aty' -> VecType [1,idx] aty'
   _ -> error "Unary transpose not on vector."
getType (Binary pos op a b)
  | op `elem` [Add, Sub, Div] = getVectorizedType aty bty
  | op == Mul  = case (aty, bty) of
    (VecType [a, _] aty', VecType [_, c] bty') -> VecType [a, c] (getArithType aty' bty')
    (VecType [a] aty', VecType [_, c] bty') -> VecType [a, c] (getArithType aty' bty') -- left vector is a x 1
    (VecType [a, _] aty', VecType [c] bty') -> VecType [a] (getArithType aty' bty')
    (VecType [a] aty', VecType [_] bty') -> getArithType aty' bty' -- dot product
    (VecType {}, VecType {}) -> error "getType: Bad vector sizes for multiplication"
    _ -> getArithType aty bty
  | op == Concat = case (aty, bty) of
    (VecType (aidx:aidxs) aty', VecType (bidx:_) bty') -> VecType [Binary pos Add aidx bidx]
                                                          (getArithType aty' bty')
  | otherwise = error "getType for binary not implemented"
  where aty = normalizeTypes $ getType a
        bty = normalizeTypes $ getType b

getLocType :: Location CExpr -> Type
getLocType (Ref ty v) = ty
getLocType (Index a idxs) = normalizeTypes $ getTypeIdx idxs (normalizeTypes $ getType a)
  where getTypeIdx [] aty = aty
        getTypeIdx (idx:idxs) (VecType (ibnd:ibnds) bty) =
          case normalizeTypes (getType idx) of
           IntType _               ->                getTypeIdx idxs (VecType ibnds bty)
           VecType idxs' idxtybase -> VecType idxs' (getTypeIdx idxs (VecType ibnds bty))
getLocType (Field a field) = case stripPtr (getType a) of -- TODO need to replace dependent fields
  StructType v (ST fields) -> case lookup field fields of
    Just fieldTy -> fieldTy
  where stripPtr (PtrType aty) = stripPtr aty
        stripPtr aty = aty
getLocType (Deref a) = let (PtrType a') = getType a
                       in a'

-- | Gets the type of an auto-vectorized expression.  Assumes types
-- have been unified.
-- Rules:
--  1) if A and B are vectors, (A + B)[i] = A[i] + B[i]
--  2) if (wlog) A is a vector and B is not, (A + B)[i] = A[i] + B
--  3) if neither are, it is just A + B
getVectorizedType :: Type -> Type -> Type
getVectorizedType ty1 ty2 = case (normalizeTypes ty1, normalizeTypes ty2) of
   (VecType [] bty1, ty2) -> getVectorizedType bty1 ty2
   (ty1, VecType [] bty2) -> getVectorizedType ty1 bty2
   (VecType (idx1:idxs1) bty1, VecType (idx2:idxs2) bty2)  ->
     case getVectorizedType (VecType idxs1 bty1) (VecType idxs2 bty2) of
      VecType idxs' bty' -> VecType (idx1:idxs') bty'
      bty' -> VecType [idx1] bty'
   (VecType idxs1 bty1, ty2)  -> VecType idxs1 (getVectorizedType bty1 ty2)
   (ty1, VecType idxs2 bty2) -> VecType idxs2 (getVectorizedType ty1 bty2)
   (ty1, ty2) -> getArithType ty1 ty2

getArithType :: Type -> Type -> Type
getArithType ty1 ty2 = case (normalizeTypes ty1, normalizeTypes ty2) of
  (IntType t1, IntType t2) -> IntType $ arithInt t1 t2
  (FloatType t1, IntType {}) -> FloatType $ promoteFloat t1
  (IntType {}, FloatType t2) -> FloatType $ promoteFloat t2
  (FloatType t1, FloatType t2) -> FloatType $ arithFloat t1 t2
  (ty1, _) -> ty1
