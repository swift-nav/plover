{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Plover.Types where

import qualified Data.Foldable as F (Foldable)
import qualified Data.Traversable as T (Traversable)
import Control.Monad.Identity
import Control.Applicative ((<$>), (<*>), pure, Applicative)
import Data.String
import Data.Ratio
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Data.Tag
import Data.Fix
import Data.Char
import Data.Data
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Data.Function (on)
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

data StorageType = DenseMatrix -- ^ See note [Dense matrix rules]
                 | DiagonalMatrix
                 | UpperTriangular
                 | UpperUnitTriangular
                 | LowerTriangular
                 | LowerUnitTriangular
                 | SymmetricMatrix
--                 | BlockMatrix [[Type]]
                 deriving (Eq, Ord, Show)

-- Note [Dense matrix rules]
-- These are equivalences:
-- 1. VecType DenseMatrix [] ty === ty
-- 2. VecType DenseMatrix bnd1 (VecType DenseMatrix bnd2 ty) === VecType (bnd1 ++ bnd2) ty

defaultIntType :: IntType
defaultIntType = IDefault

actualDefaultIntType :: IntType
actualDefaultIntType = S32

defaultFloatType :: FloatType
defaultFloatType = FDefault

actualDefaultFloatType :: FloatType
actualDefaultFloatType = Double

data UnOp = Pos | Neg | Not
          | Transpose | Inverse
          | Diag
          | Sum
          | Shape
          deriving (Show, Eq, Ord)
data BinOp = Add | Sub | Mul | Div | Hadamard
           | Pow | Concat
           | And | Or
           | EqOp | LTOp | LTEOp
           deriving (Show, Eq, Ord)

data Range a = Range { rangeFrom :: a, rangeTo :: a, rangeStep :: a }
             deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

rangeLength :: Tag SourcePos -> Range CExpr -> CExpr
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
  | Return' Type a -- The type is that of the aborted continuation
  | Assert' a
  | RangeVal' (Range a) -- TODO rename RangeLit'

  -- Control flow
  | If' a a a

  -- Elementary expressions
  | IntLit' IntType Integer
  | FloatLit' FloatType Double
  | StrLit' String
  | BoolLit' Bool
  | VecLit' Type [a] -- the type is the base type of the vector (for 0-element case)
  | TupleLit' [a]

  | Let' Variable a a
  | Uninitialized' Type -- Only for using Let to create a new variable to be used as a return value from a function
  | Seq' a a

  -- Function application   TODO change for implicit arguments
  | App' a [Arg a]
  | ConcreteApp' a [a] Type -- function, arguments, solved return type

  -- Operators
  -- Symbolic patterns given below
  | Hole' (Maybe UVar) -- value hole
  | Get' (Location a)
  | Addr' (Location a)
  | Set' (Location a) a
  | AssertType' a Type
  | Unary' UnOp a
  | Binary' BinOp a a
 deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

data Location a = Ref Type Variable
                | Index a [a] -- ^ See note [indexing rules]
                | Field a String -- ^ See note [Field dereferencing rules]
                | Deref a
                deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

-- Note [indexing rules]
--
-- These are equivalences:
--
-- 1. A[i_1,...,i_n] is the (i_1,...,i_n) entry of A, if n has n indices
-- 2. A[i_1,...,i_k][i_{k+1},...,i_n] === A[i_1,...,i_n]
-- 3. A[I_1,...,I_m] === A[I_{1,1}, I_{1,2}, I_{1,3}, ...] if I_i are
--    tuples, with a scalar being a 1-tuple
-- 4. A[J_1,...,J_m][I_1,...,I_m] === A[J_1[I_1],...,J_m[I_m]], where
--    I_i are n_i-tuples (with a scalar being a 1-tuple), and J_k are
--    vectors with n_i indices of tuples.

-- Note [Field dereferencing rules]
--
-- This is an equivalences:
-- 1. If x is a pointer, then x.a === (*x).a

data Type' a
  = VecType StorageType [a] (Type' a)
  | TupleType [Type' a]
  | FnType FunctionType
--  | NumType NumCtxt -- some kind of number.  temporary; must become concrete numeric type
  | IntType IntType
  | FloatType FloatType
  | StringType -- null-terminated C string
  | BoolType
  | PtrType (Type' a)
  | TypedefType (Type' a) Variable -- Like Ref
  | StructType Variable StructType
  | TypeHole (Maybe UVar)
  deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

type CExpr = FixTagged SourcePos Expr
pattern PExpr pos x = FTag pos x
type Type = Type' CExpr

-- Note [De-tuplitizing function arguments]:
--
-- The idea of a rule f (x,y) === f x y has come up a couple of times,
-- but the problem is that when converting from an App to a
-- ConcreteApp that you have to know the type of each argument to the
-- function to properly do the conversion, which we do not yet know
-- because unification has yet to happen.  It is probably possible
-- with a more complex system, but for now it will not happen.

-- Note [Vectorizing element-wise operators]
-- Rules:
-- 1. A + b === A + [b, ..., b]

-- TODO: if we want to create constraints on number types (for
-- instance, if x + 1 occurs, then we can default to x being a number
-- rather than an int; later on if it is clear that x must be a float
-- there is no error)
-- data NumCtxt = NumRef Variable -- The number has the same type as the given unification variable
--              | NumArith NumCtxt NumCtxt -- The number has the type after doing an arithmetic operation on the two nums
--              deriving (Show, Eq, Ord)

-- Represents the type of an Expr
-- Separates implicit parameters, explicit parameters, output type
-- The boolean means whether the argument is required (False means implicit)
data FunctionType = FnT [(Tag SourcePos, Variable, Bool, ArgDir, Type)] Type
  deriving (Show)

instance Eq FunctionType where
  (==) = (==) `on` strippedFunctionType
instance Ord FunctionType where
  compare = compare `on` strippedFunctionType

-- | Removes argument source position information for Eq and Ord instances
strippedFunctionType :: FunctionType -> ([(Variable, Bool, ArgDir, Type)], Type)
strippedFunctionType (FnT args ty) = (map (\(pos, v, b, dir, ty) -> (v, b, dir, ty)) args,
                                      ty)

-- Right now only works for vectors
data ArgDir = ArgIn | ArgOut | ArgInOut
            deriving (Show, Eq, Ord)

-- | A struct contains external (C) and internal (Plover) types.  This
-- is controlled using the 'storing' keyword.
data StructType = ST
  { st_fields :: [(Variable, (Tag SourcePos, Type, Type))]
  }
 deriving (Show, Eq, Ord)

-- Function without implicits or a dependent type
fnT :: [Type] -> Type -> FunctionType
fnT params out = FnT [(NoTag, "", True, ArgIn, t) | t <- params] out


-- | If a function returns a complex type, it must be passed as an
-- extra argument.  The maybe variable gives the new variable name.
-- N.B. The new variable name is _deterministically_ chosen.  This
-- means `getEffectiveFunType` must be what is called whenever one
-- wants to know the return variable name.  Not to be used with at a
-- call site (i.e., ConcreteApp), since it will not be
-- universalized.
-- TODO: returning a tuple?  (right now can just return a struct)
getEffectiveFunType :: FunctionType -> (FunctionType, Maybe (Variable, Type))
getEffectiveFunType ft@(FnT args retty) = if complexRet retty
                                          then internReturn args' retty
                                          else ((FnT args' retty), Nothing)
  where complexRet :: Type -> Bool
        complexRet (VecType {}) = True
        -- TODO tuple
        -- Any mistake in here will just end up causing a "don't know how to program this" message later
        complexRet _ = False

        --args' = maybeAddVoid args
        args' = args

        -- Puts the return into the argument list.  TODO should it be
        -- the type itself, or should it be Ptrized?  The semantics of
        -- type itself seem correct so far.  Perhaps In/Out/InOut are
        -- in order to record these things better
        internReturn :: [(Tag SourcePos, Variable, Bool, ArgDir, Type)] -> Type -> (FunctionType, Maybe (Variable, Type))
        internReturn args retty = (FnT (args ++ [(NoTag, retName, True, ArgOut, retty')]) Void, Just (retName, retty'))
          where retName = genName [v | (_, v, _, _, _) <- args] "result$" -- since $ cannot occur in a normal argument
                genName :: [Variable] -> Variable -> Variable
                genName names test = if test `elem` names
                                     then genName names (test ++ "$")
                                     else test
                retty' = retty

type StructMember = (Variable, (Tag SourcePos, Type, Type))

data Definition = FunctionDef (Maybe CExpr) FunctionType
                | StructDef [StructMember]
                | TypeDef Type
                | ValueDef (Maybe CExpr) Type
                | ImportDef String
                deriving (Show, Eq)
data DefBinding = DefBinding { binding :: Variable
                             , bindingPos :: Tag SourcePos
                             , extern :: Bool -- ^ Whether this definition should not be included in the compilation unit
                             , static :: Bool -- ^ Whether this definition should by private to the compilation unit
                             , imported :: Maybe String -- ^ Defining module, if this binding was imported
                             , definition :: Definition }
                deriving (Show, Eq)

mkBinding :: Tag SourcePos -> Variable -> Definition -> DefBinding
mkBinding pos v d = DefBinding { binding = v
                               , bindingPos = pos
                               , extern = False
                               , static = False
                               , imported = Nothing
                               , definition = d }

definitionType :: DefBinding -> Type
definitionType def = case definition def of
  FunctionDef _ ft -> FnType ft
  StructDef fields -> StructType (binding def) $ ST fields
  ValueDef _ ty -> ty
  TypeDef ty -> ty

pattern Vec tag a b c = PExpr tag (Vec' a b c)
pattern For tag a b c = PExpr tag (For' a b c)
pattern If tag a b c = PExpr tag (If' a b c)
pattern RangeVal tag r = PExpr tag (RangeVal' r)
pattern VoidExpr tag = PExpr tag (TupleLit' [])
pattern IntLit tag t a = PExpr tag (IntLit' t a)
pattern FloatLit tag t a = PExpr tag (FloatLit' t a)
pattern StrLit tag s = PExpr tag (StrLit' s)
pattern BoolLit tag s = PExpr tag (BoolLit' s)
pattern VecLit tag ty s = PExpr tag (VecLit' ty s)
pattern TupleLit tag s = PExpr tag (TupleLit' s)
pattern Return tag ty x = PExpr tag (Return' ty x)
pattern Assert tag x = PExpr tag (Assert' x)
pattern App tag f args = PExpr tag (App' f args)
pattern ConcreteApp tag f args rty = PExpr tag (ConcreteApp' f args rty)
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

pattern HoleJ pos a = Hole pos (Just a)
pattern TypeHoleJ a = TypeHole (Just a)

pattern Void = TupleType []


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
-- | warning: uses NoTag
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
  -- | Like a monadic fmap, but transforming each part of the
  -- constructor using the given functions.
  mapTerm :: (Applicative m, Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
          -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
          -> a -> m a
  -- | Returns a transformation function based on `a`.  (It is one of the given transformations.)
  termMapper :: (Applicative m, Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
             -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
             -> a -> m a

instance TermMappable Type where
  mapTerm tty texp tloc trng ty = case ty of
    VecType st bnds ety -> VecType st <$> mapM texp bnds <*> tty ety
    TupleType tys -> TupleType <$> mapM tty tys
    FnType {} -> return ty -- Functions types are different (TODO?)
    IntType {} -> return ty
    FloatType {} -> return ty
    StringType -> return ty
    BoolType -> return ty
    PtrType pty -> PtrType <$> tty pty
    TypedefType ty v -> TypedefType <$> tty ty <*> pure v
    StructType {} -> return ty -- Struct types are different (TODO?)
    TypeHole {} -> return ty
  termMapper tty texp tloc trng = tty

instance TermMappable CExpr where
  mapTerm tty texp tloc trng exp = case exp of
    Vec pos v range expr -> Vec pos v <$> trng range <*> texp expr
    For pos v range expr -> For pos v <$> trng range <*> texp expr
    Return pos ty v -> Return pos <$> tty ty <*> texp v
    Assert pos v -> Assert pos <$> texp v
    RangeVal pos range -> RangeVal pos <$> trng range
    If pos a b c -> If pos <$> texp a <*> texp b <*> texp c
    IntLit {} -> return exp
    FloatLit {} -> return exp
    StrLit {} -> return exp
    BoolLit {} -> return exp
    VecLit pos ty exprs -> VecLit pos <$> tty ty <*> mapM texp exprs
    TupleLit pos exprs -> TupleLit pos <$> mapM texp exprs
    Let pos v val expr -> Let pos v <$> texp val <*> texp expr
    Uninitialized pos ty -> Uninitialized pos <$> tty ty
    Seq pos p1 p2 -> Seq pos <$> texp p1 <*> texp p2
    App pos fn args -> App pos <$> texp fn <*> mapM targ args
      where targ (Arg a) = Arg <$> texp a
            targ (ImpArg a) = ImpArg <$> texp a
    ConcreteApp pos fn args rty -> ConcreteApp pos <$> texp fn <*> mapM texp args <*> tty rty
    Hole {} -> return exp
    Get pos loc -> Get pos <$> tloc loc
    Addr pos loc -> Addr pos <$> tloc loc
    Set pos loc val -> Set pos <$> tloc loc <*> texp val
    AssertType pos v ty -> AssertType pos <$> texp v <*> tty ty
    Unary pos op v -> Unary pos op <$> texp v
    Binary pos op v1 v2 -> Binary pos op <$> texp v1 <*> texp v2
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

data ScopedTraverserRec m = ScopedTraverserRec
                            { stTy :: Tag SourcePos -> Type -> m Type
                            , stEx :: Tag SourcePos -> CExpr -> m CExpr
                            , stLoc :: Tag SourcePos -> Location CExpr -> m (Location CExpr)
                            , stRng :: Tag SourcePos -> Range CExpr -> m (Range CExpr)
                            , stScope :: forall b . Variable -> Tag SourcePos -> (Variable -> m b) -> m b
                            }

-- | Traverses the term in evaluation order inside the monad.
class ScopedTraverser a where
  scopedTraverseTerm :: Monad m => ScopedTraverserRec m -> Tag SourcePos -> a -> m a

-- | Performs a level of scoped traversing on subterms, in the order defined by mapTerm.
simpleScopedTraverse :: (Monad m, ScopedTraverser a, TermMappable a) => ScopedTraverserRec m -> Tag SourcePos -> a -> m a
simpleScopedTraverse tr pos t = termMapper mty mex mloc mrng =<< submap t
  where submap = mapTerm (subTrav()) (subTrav()) (subTrav()) (subTrav())
        subTrav() = scopedTraverseTerm tr pos

        mty = stTy tr pos
        mex = stEx tr pos
        mloc = stLoc tr pos
        mrng = stRng tr pos

instance ScopedTraverser CExpr where
  scopedTraverseTerm tr _ x = case x of
    Vec pos v range expr -> stLetLike tr Vec pos v range expr
    For pos v range expr -> stLetLike tr For pos v range expr
    Let pos v val expr -> stLetLike tr Let pos v val expr
    _ -> simpleScopedTraverse tr (getTag x) x

stLetLike :: (Monad m, ScopedTraverser a) => ScopedTraverserRec m
           -> (Tag SourcePos -> Variable -> a -> CExpr -> CExpr)
           -> Tag SourcePos -> Variable -> a -> CExpr
           -> m CExpr
stLetLike tr cons pos v val expr = stEx tr pos =<< do
  val' <- scopedTraverseTerm tr pos val
  stScope tr v pos $ \v' -> do
    expr' <- scopedTraverseTerm tr pos expr
    return $ cons pos v' val' expr'

instance ScopedTraverser Type where
  scopedTraverseTerm = simpleScopedTraverse

instance ScopedTraverser (Location CExpr) where
  scopedTraverseTerm = simpleScopedTraverse

instance ScopedTraverser (Range CExpr) where
  scopedTraverseTerm = simpleScopedTraverse

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

-- | Promote to an int type for use in arithmetic (following C convention)
promoteInt :: IntType -> IntType
promoteInt t
  | intBits t < intBits IDefault  = IDefault
  | otherwise = t

-- | Integer arithmetic promotion rules (following C convention)
arithInt :: IntType -> IntType -> IntType
arithInt t1 t2 = arithInt' t1' t2'
  where t1' = promoteInt t1
        t2' = promoteInt t2

        arithInt' IDefault y = y
        arithInt' x IDefault = x
        arithInt' x y
          -- Take the one with more bits
          | intBits x > intBits y = x
          | intBits x < intBits y = y
          -- Otherwise take the unsigned one, if there is one (yes, that is how C works)
          | intUnsigned x  = x
          | otherwise = y

-- | For use in unification: determines the smallest integer type
-- which can hold both integer types.  See note [intMerge table].
intMerge :: IntType -> IntType -> IntType
intMerge IDefault y = intMerge actualDefaultIntType y
intMerge x IDefault = intMerge x actualDefaultIntType
intMerge x y = fromMaybe U64 $ suitableInt $ merge (intRange x) (intRange y)

  where intRange :: IntType -> (Int, Int) -- ^ min, max (roughly) (in bits)
        intRange x | intUnsigned x = (0, intBits x)
                   | otherwise = (1 - intBits x, intBits x - 1)

        merge (min1, max1) (min2, max2) = (min min1 min2, max max1 max2)

        fits' :: (Int, Int) -> (Int, Int) -> Bool
        fits' (min1, max1) (min2, max2) = min1 <= min2 && max1 >= max2

        fits ty rng = fits' (intRange ty) rng

        suitableInt :: (Int, Int) -> Maybe IntType
        suitableInt rng = find (`fits` rng) [U8, S8, U16, S16, U32, S32, U64, S64]

-- Note [intMerge table]
--    |  U8   S8  U16  S16  U32  S32  U64  S64
-- ---+---------------------------------------
--  U8|  U8  S16  U16  S16  U32  S32  U64  S64
--  S8|       S8  S32  S16  S64  S32  U64  S64
-- U16|           U16  S32  U32  S32  U64  S64
-- S16|                S16  S64  S32  U64  S64
-- U32|                     U32  S64  U64  S64
-- S32|                          S32  U64  S64
-- U64|                               U64  U64
-- S64|                                    S64

-- | Promote a float type for use in arithmetic (following C convention; notice it actually just outputs Double)
promoteFloat :: FloatType -> FloatType
promoteFloat t
  | floatBits t < floatBits FDefault = FDefault
  | otherwise = t

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
intCanHold IDefault s = intCanHold actualDefaultIntType s
intCanHold d s =  d == intMerge d s

-- | Determines whether a location of the first float type can
-- comfortably hold a location of the second.
floatCanHold :: FloatType -> FloatType -> Bool
floatCanHold FDefault s = floatCanHold actualDefaultFloatType s
floatCanHold d s =  d == floatMerge d s

-- | Assumes already unified.  Checks whether a store from the second
-- type to the first type succeeds.  Not to be confused with whether
-- they have equivalent memory representations (which is instead
-- needed for passing an argument to a function).
typeCanHold :: Type -> Type -> Bool
typeCanHold ty1 ty2 = typeCanHold' (normalizeTypes ty1) (normalizeTypes ty2)

typeCanHold' :: Type -> Type -> Bool
typeCanHold' (VecType _ [] bty1) ty2 = typeCanHold bty1 ty2
typeCanHold' ty1 (VecType _ [] bty2) = typeCanHold ty1 bty2
typeCanHold' (VecType st1 (bnd1:bnds1) bty1) (VecType st2 (bnd2:bnds2) bty2) =
  reduceArithmetic bnd1 == reduceArithmetic bnd2
  && typeCanHold' (VecType st1 bnds1 bty1) (VecType st2 bnds2 bty2)
typeCanHold' (TupleType tys1) (TupleType tys2) =
  length tys1 == length tys2 && and (map (uncurry typeCanHold') (zip tys1 tys2))
typeCanHold' (FnType _) (FnType _) = False -- TODO (?)
typeCanHold' (IntType t1) (IntType t2) = True -- intCanHold t1 t2   -- TODO always allowing follows C convention (but should we?)
typeCanHold' (IntType t1) (FloatType {}) = False
typeCanHold' (FloatType t1) (IntType {}) = True
typeCanHold' (FloatType t1) (FloatType t2) = floatCanHold t1 t2
typeCanHold' StringType StringType = True
typeCanHold' BoolType BoolType = True
typeCanHold' (PtrType t1) (PtrType t2) = typeCanHold' t1 t2 -- TODO should check t1 == t2
typeCanHold' (TypedefType ty1 v1) (TypedefType ty2 v2)  = v1 == v2 || typeCanHold' ty1 ty2
typeCanHold' (TypedefType ty1 _) ty2 = typeCanHold' ty1 ty2
typeCanHold' ty1 (TypedefType ty2 _) = typeCanHold' ty1 ty2
typeCanHold' (StructType v1 _) (StructType v2 _) = v1 == v2
typeCanHold' (TypeHole mv1) (TypeHole mv2) = mv1 == mv2
typeCanHold' ty1 ty2 = ty1 == ty2

-- | Collapses dense matrices and expands typedefs along the spine using baseExpandTypedef
normalizeTypes :: TermMappable a => a -> a
normalizeTypes x = runIdentity $ traverseTerm tty texp tloc trng =<< termMapper ety return return return x
  where tty ty = case ty of
          VecType _ [] ty -> return ty
          VecType DenseMatrix bnds1 (VecType DenseMatrix bnds2 ty) -> return $ VecType DenseMatrix (bnds1 ++ bnds2) ty
          _ -> return ty
        texp = return
        tloc = return
        trng = return

        ety x = return $ baseExpandTypedef x

-- | Splits dense matrices into single-indexed entities
denormalizeTypes :: TermMappable a => a -> a
denormalizeTypes = runIdentity . (traverseTerm tty texp tloc trng)
  where tty ty = case ty of
          VecType _ [] ty -> return ty
          VecType DenseMatrix bnds ty | length bnds >= 2 ->
            return $ foldr (\bnd bty -> VecType DenseMatrix [bnd] bty) ty bnds
          _ -> return ty
        texp = return
        tloc = return
        trng = return

-- | Recursively expands typedefs along the spine.  The spine includes
-- vector basetypes, though the vector may terminate in a typedef.
baseExpandTypedef :: Type -> Type
baseExpandTypedef ty@(TypedefType (TypeHole {}) _) = ty
baseExpandTypedef (TypedefType ty _) = ty
--baseExpandTypedef (TypedefType ty@(VecType {}) _) = baseExpandTypedef ty
--baseExpandTypedef ty@(TypedefType _ _) = ty
baseExpandTypedef (VecType st idxs bty) = VecType st idxs (baseExpandTypedef bty)
baseExpandTypedef ty = ty

-- | Gets the bounds for indices in a vector
getIndices :: Type -> [CExpr]
getIndices ty = getIndices' $ normalizeTypes ty
  where getIndices' (VecType _ bnds bty) = bnds ++ getIndices' bty
        getIndices' _ = []

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
    toExpr g@(HoleJ _ _) = return $ S.Atom g
    toExpr _ = Nothing

class PP a where
  pretty :: a -> Doc

instance PP (t a) => PP (FixTagged' tag t a) where
  pretty (FixTagged' x) = pretty (stripTag x)

instance PP (a (Fix a)) => PP (Fix a) where
  pretty (Fix x) = pretty x


instance PP Type where
  pretty v@(VecType {}) = case normalizeTypes v of
                           VecType st bnds ty -> pst $ pretty ty <> brackets (sep $ punctuate comma (map pretty bnds))
                             where pst = case st of
                                     DenseMatrix -> id
                                     _ -> \x -> text (show st) <+> x
                           ty' -> pretty ty'
  pretty (TupleType xs) = parens $ sep $ punctuate (text ",") $ map pretty xs
  pretty (FnType (FnT args retty)) = parens $ hang (text "func") 5 (sep $ map prarg args)
    where prarg (pos, v, req, dir, ty) = (rqimp req) $ pdir (sep $ punctuate (text "::") [text v, pretty ty])
            where pdir x = case dir of
                    ArgIn -> x
                    ArgOut -> sep [text "out", x]
                    ArgInOut -> sep [text "inout", x]
          rqimp True = parens
          rqimp False = braces
--  pretty (NumType _) = text "Num"
  pretty (IntType IDefault) = text "int"
  pretty (IntType t) = text $ map toLower $ show t
  pretty (FloatType FDefault) = text "double"
  pretty (FloatType t) = text $ map toLower $ show t
  pretty StringType = text "string"
  pretty BoolType = text "bool"
  pretty (PtrType t) = parens $ hang (text "*") 2 (pretty t)
  pretty (TypedefType ty v) = text v
  pretty (StructType v _) = text v
  pretty (TypeHole (Just v)) = text v -- should have $ so shouldn't conflict
  pretty (TypeHole Nothing) = text "$hole"
--  pretty x = text $ show x

instance (Show a, PP a) => PP (Expr a) where
  pretty (TupleLit' xs) = parens $ sep $ punctuate (text ",") $ map pretty xs
  pretty (IntLit' _ x) = text $ show x
  pretty (FloatLit' _ x) = text $ show x
  pretty (StrLit' x) = text $ show x
  pretty (BoolLit' x) = text $ show x
  pretty (Hole' (Just v)) = text v -- it should start with $ so shouldn't conflict
  pretty (Hole' Nothing) = parens $ text "$hole"
  pretty (Get' loc) = pretty loc
  pretty (Addr' loc) = parens $ hang (text "&") 2 (pretty loc)
  pretty (Unary' op expr) = parens $ pretty op <+> pretty expr
  pretty (Binary' op x y) = parens $ pretty x <+> pretty op <+> pretty y
  pretty x = text $ show x

instance PP UnOp where
  pretty Pos = text "+"
  pretty Neg = text "-"
  pretty Not = text "not"
  pretty Transpose = text "transpose"
  pretty Inverse = text "inverse"
  pretty Sum = text "sum"
  pretty Diag = text "diag"
  pretty Shape = text "shape"

instance PP BinOp where
  pretty Add = text "+"
  pretty Sub = text "-"
  pretty Mul = text "*"
  pretty Hadamard = text ".*"
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


getRangeType :: Range CExpr -> IntType
getRangeType (Range from to step) = intMerge S32 $ arithInt (arithInt t1 t2) t3
  where IntType t1 = getType from
        IntType t2 = getType to
        IntType t3 = getType step

getType :: CExpr -> Type
getType (Vec pos _ range base) = VecType DenseMatrix [rangeLength pos range] (getType base)
getType (For {}) = Void
getType (Return _ ty _) = ty -- the type of the aborted continuation
getType (Assert {}) = Void
getType (RangeVal pos range) = VecType DenseMatrix [rangeLength pos range] (IntType $ getRangeType range)
getType (If pos a b c) = getType b
getType (IntLit pos t _) = IntType t
getType (FloatLit pos t _) = FloatType t
getType (StrLit {}) = StringType
getType (BoolLit {}) = BoolType
getType (VecLit pos ty xs) = VecType DenseMatrix [IntLit pos IDefault (fromIntegral $ length xs)] ty
getType (TupleLit pos xs) = TupleType $ map getType xs
getType (Let pos v x body) = getType body
getType (Uninitialized pos ty) = ty
getType (Seq pos a b) = getType b
getType (App {}) = error "App should not be here"
getType (ConcreteApp pos f args rty) = rty
getType (Hole pos _) = error "Hole should not be here"
getType (Get pos loc) = getLocType loc
getType (Addr pos loc) = PtrType (getLocType loc)
getType (Set {}) = Void
getType (AssertType _ _ ty) = ty
getType (Unary pos op a) | op `elem` [Pos, Neg] = getVectorizedType (getType a) (getType a)
getType (Unary pos Sum a) = case getVectorizedType (getType a) (getType a) of
  VecType _ (bnd:bnds) aty' -> normalizeTypes $ VecType DenseMatrix bnds aty'
  aty' -> aty'
getType (Unary pos Inverse a) =
  case normalizeTypes $ getType a of
   VecType _ [a, _] aty' -> VecType DenseMatrix [a, a] (getArithType aty' $ FloatType defaultFloatType)
   _ -> error "Unary inverse on not a rectangular vector"
getType (Unary pos Transpose a) =
  case normalizeTypes $ getType a of
   VecType _ (i1:i2:bnds) aty' -> VecType DenseMatrix (i2:i1:bnds) aty'
   VecType _ [bnd] aty' -> VecType DenseMatrix [1,bnd] aty'
   _ -> error "Unary transpose not on vector."
getType (Unary pos Diag a) =
  case normalizeTypes $ getType a of
    VecType _ (i1:_) aty' -> VecType DenseMatrix [i1] aty'
    _ -> error "Unary diag not on vector."
getType (Unary pos Shape a) = VecType DenseMatrix [fromIntegral $ length $ getIndices $ getType a] (IntType defaultIntType)
getType (Unary pos Not a) = BoolType
getType (Binary pos op a b)
  | op `elem` [Add, Sub, Div, Hadamard] = getVectorizedType aty bty
  | op == Mul  = case (aty, bty) of
    (VecType _ [a, _] aty', VecType _ [_, c] bty') -> VecType DenseMatrix [a, c] (getArithType aty' bty')
    (VecType _ [a] aty', VecType _ [_, c] bty') -> VecType DenseMatrix [a, c] (getArithType aty' bty') -- left vector is a x 1
    (VecType _ [a, _] aty', VecType _ [c] bty') -> VecType DenseMatrix [a] (getArithType aty' bty')
    (VecType _ [a] aty', VecType _ [_] bty') -> getArithType aty' bty' -- dot product
    (VecType {}, VecType {}) -> error "getType: Bad vector sizes for multiplication"
    _ -> getArithType aty bty
  | op == Concat = case (aty, bty) of
    (VecType _ (abnd:abnds) aty', VecType _ (bbnd:_) bty') -> VecType DenseMatrix
                                                              (reduceArithmetic (Binary pos Add abnd bbnd) : abnds)
                                                              (getMinimalType aty' bty')
  | op `elem` [And, Or, EqOp, LTOp, LTEOp]  = BoolType
  | op == Pow = case (aty, bty) of
    (IntType ai, IntType {}) -> IntType $ promoteInt ai
    (FloatType af, FloatType bf) -> FloatType $ arithFloat af bf
    (_, FloatType bf) -> FloatType $ promoteFloat bf
    (FloatType af, _) -> FloatType $ promoteFloat af
  where aty = normalizeTypes $ getType a
        bty = normalizeTypes $ getType b

getLocType :: Location CExpr -> Type
getLocType (Ref ty v) = ty
getLocType (Index a idxs) = normalizeTypes $ getTypeIdx idxs (normalizeTypes $ getType a)
  where getTypeIdx [] aty = aty
        getTypeIdx (idx:idxs) aty@(VecType {}) = getTypeIdxty (getType idx) idxs aty

        getTypeIdxty idxty idxs (VecType st ibnds bty) =
          case normalizeTypes idxty of
            VecType st' idxs' idxtybase -> VecType st' idxs' (getTypeIdxty idxtybase idxs
                                                              (VecType st ibnds bty))
            ty -> getTypeIdx idxs
                  (VecType DenseMatrix (drop (iSize ty) ibnds) bty)

        iSize (IntType {}) = 1
        iSize (TupleType tys) = sum $ map iSize tys

getLocType (Field a field) = case stripPtr (normalizeTypes $ getType a) of -- TODO need to replace dependent fields which show up b/c of Storing
  StructType v (ST fields) -> case lookup field fields of
    Just (_, _ ,fieldTy) -> structField fields a fieldTy
  ty -> error $ show ty
  where stripPtr (PtrType aty) = stripPtr $ normalizeTypes aty
        stripPtr aty = aty
getLocType (Deref a) = let (PtrType a') = normalizeTypes $ getType a
                       in a'

-- | Gets the type of an auto-vectorized expression.  Assumes types
-- have been unified.  Result (if vector) is always DenseMatrix storage type.
-- Rules:
--  1) if A and B are vectors, (A + B)[i] = A[i] + B[i]
--  2) if (wlog) A is a vector and B is not, (A + B)[i] = A[i] + B
--  3) if neither are, it is just A + B
getVectorizedType :: Type -> Type -> Type
getVectorizedType ty1 ty2 = case (normalizeTypes ty1, normalizeTypes ty2) of
   (VecType _ [] bty1, ty2) -> getVectorizedType bty1 ty2
   (ty1, VecType _ [] bty2) -> getVectorizedType ty1 bty2
   (VecType _ (bnd1:bnds1) bty1, VecType _ (bnd2:bnds2) bty2)  ->
     VecType DenseMatrix [bnd1] (getVectorizedType (VecType DenseMatrix bnds1 bty1) (VecType DenseMatrix bnds2 bty2))
   (VecType _ bnds1 bty1, ty2)  -> VecType DenseMatrix bnds1 (getVectorizedType bty1 ty2)
   (ty1, VecType _ bnds2 bty2) -> VecType DenseMatrix bnds2 (getVectorizedType ty1 bty2)
   (ty1, ty2) -> getArithType ty1 ty2

getArithType :: Type -> Type -> Type
getArithType ty1 ty2 = case (normalizeTypes ty1, normalizeTypes ty2) of
  (IntType t1, IntType t2) -> IntType $ arithInt t1 t2
  (FloatType t1, IntType {}) -> FloatType $ promoteFloat t1
  (IntType {}, FloatType t2) -> FloatType $ promoteFloat t2
  (FloatType t1, FloatType t2) -> FloatType $ arithFloat t1 t2
  (ty1, _) -> ty1

-- | Assumes types are already unified.  Gets the smallest type which
-- can hold both types.  Really should only be used on arithmetic
-- types.
getMinimalType :: Type -> Type -> Type
getMinimalType ty1 ty2 = case (normalizeTypes ty1, normalizeTypes ty2) of
  (IntType t1, IntType t2) -> IntType $ intMerge t1 t2
  (FloatType t1, IntType {}) -> FloatType t1
  (IntType {}, FloatType t2) -> FloatType t2
  (FloatType t1, FloatType t2) -> FloatType $ floatMerge t1 t2
  (ty1, _) -> ty1


structField :: [StructMember] -> CExpr -> Type -> Type
structField members base memberTy = replaceMemberRefs memberTy
  where vMap = M.fromList [(v, inty) | (v, (pos, exty, inty)) <- members]

        replaceMemberRefs :: TermMappable a => a -> a
        replaceMemberRefs = runIdentity . traverseTerm tty texp tloc trng
          where tty = return
                texp = return
                tloc loc = case loc of
                  Ref ty v -> case M.lookup v vMap of
                    Just vty -> return $ Field base v
                    Nothing -> return loc
                trng = return


---
--- Old stuff
---

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

data CompilationUnit = CU
  { unitName :: String
  , sourceDefs :: [DefBinding]
  , sourceIncs :: [String]
  , headerDefs :: [Variable] -- refers to DefBindings
  , headerIncs :: [String]
  }
