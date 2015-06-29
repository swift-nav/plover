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
import Data.String
import Data.Ratio
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Data.Tag
import Data.Functor.Fixedpoint
import Data.Char
import Text.PrettyPrint


-- Core AST

type Variable = String
-- | Unification variable
type UVar = String

data IntType = U8 | S8
             | U16 | S16
             | U32 | S32
             | U64 | S64
             | IDefault
             deriving (Eq, Ord, Show)
data FloatType = Float | Double
               | FDefault
               deriving (Eq, Ord, Show)

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
          | Sum | For
          deriving (Show, Eq, Ord)
data BinOp = Add | Sub | Mul | Div
           | Pow | Dot | Concat
           | And | Or
           | EqOp | LTOp | LTEOp
           deriving (Show, Eq, Ord)

data Range a = Range { rangeFrom :: a, rangeTo :: a, rangeStep :: a }
             deriving (Eq, Ord, Show, Functor, F.Foldable, T.Traversable)

rangeLength :: Tag SourcePos -> Range CExpr -> CExpr
rangeLength pos (Range (IntLit _ _ 0) to (IntLit _ _ 1)) = to
rangeLength pos (Range from to (IntLit _ _ 1)) = Binary pos Sub to from
rangeLength pos (Range from to step) = Binary pos Div (Binary pos Sub to from) step

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
        complexRet (TypedefType _) = True
        complexRet (StructType _ _) = True
        -- Any mistake in here will just end up causing a "don't know how to program this" message later
        complexRet _ = False

        args' = maybeAddVoid args

        -- Puts the return into the argument list.  TODO should it be
        -- the type itself, or should it be Ptrized?  The semantics of
        -- type itself seem correct so far.  Perhaps In/Out/InOut are
        -- in order to record these things better
        internReturn :: [(Variable, Bool, Type)] -> Type -> (FunctionType, Maybe (Variable, Type))
        internReturn args retty = (FnT (args ++ [(retName, True, retty')]) Void, Just (retName, retty'))
          where retName = genName [v | (v, _, _) <- args] "result$"
                genName :: [Variable] -> Variable -> Variable
                genName names test = if test `elem` names
                                     then genName names (test ++ "$")
                                     else test
                retty' = retty

-- Checks that there is at least one required argument
maybeAddVoid :: [(Variable, Bool, Type)] -> [(Variable, Bool, Type)]
maybeAddVoid args | null [True | (_,r,_) <- args, r]  = args ++ [("", True, Void)]
                  | otherwise                         = args

withPossibleVoid :: FunctionType -> FunctionType
withPossibleVoid (FnT args retty) = (FnT (maybeAddVoid args) retty)

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
  mapTerm :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
          -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
          -> a -> m a
  termMapper :: (Monad m) => (Type -> m Type) -> (CExpr -> m CExpr)
             -> (Location CExpr -> m (Location CExpr)) -> (Range CExpr -> m (Range CExpr))
             -> a -> m a

instance TermMappable Type where
  mapTerm tty texp tloc trng ty = case ty of
    VecType idxs ety -> VecType <$> mapM texp idxs <*> tty ety
    PtrType pty -> PtrType <$> tty pty
    FnType (FnT args retty) -> do
      args' <- forM args $ \(v, b, ty) -> do
        ty' <- tty ty
        return (v, b, ty')
      retty' <- tty retty
      return $ FnType $ FnT args' retty'
    _ -> return ty
  termMapper tty texp tloc trng = tty

instance TermMappable CExpr where
  mapTerm tty texp tloc trng exp = case exp of
    Vec pos v range expr -> Vec pos v <$> trng range <*> texp expr
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

traverseTerm :: (Monad m, TermMappable a) => (Type -> m Type) -> (CExpr -> m CExpr)
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

floatPromote :: FloatType -> FloatType -> FloatType
floatPromote FDefault y = y
floatPromote x FDefault = x
floatPromote Float y = y
floatPromote x Float = x
floatPromote x y = Double

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


normalizeTypes :: TermMappable a => a -> a
normalizeTypes = runIdentity . (traverseTerm tty texp tloc trng)
  where tty ty = case ty of
          VecType [] ty -> return ty
          VecType idxs1 (VecType idxs2 ty) -> return $ VecType (idxs1 ++ idxs2) ty
          _ -> return ty
        texp = return
        tloc = return
        trng = return


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
    where prarg (v, req, ty) = (rqimp req) (sep $ punctuate (text "::") [text v, pretty ty])
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
--  pretty x = text $ show x

instance (Show a, PP a) => PP (Expr a) where
  pretty (VoidExpr') = text "Void"
  pretty (IntLit' _ x) = text $ show x
  pretty (FloatLit' _ x) = text $ show x
  pretty (StrLit' x) = text $ show x
  pretty (BoolLit' x) = text $ show x
  pretty (Hole' (Just (_, v))) = text v -- should start with $ so shouldn't conflict
  pretty (Hole' Nothing) = parens $ text "$hole"
  pretty (Get' loc) = pretty loc
  pretty (Addr' loc) = parens $ hang (text "&") 2 (pretty loc)
  pretty x = text $ show x

instance PP a => PP (Location a) where
  pretty (Ref _ v) = text v
  pretty (Index ty idxs) = pretty ty <> brackets (sep $ punctuate comma (map pretty idxs))
  pretty (Field a field) = pretty a <> text ("." ++ field)
  pretty (Deref a) = parens $ hang (text "*") 2 (pretty a)


getType :: CExpr -> Type
getType (Vec pos _ range base) = VecType [rangeLength pos range] (getType base)
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
getType (ConcreteApp pos f args) = let FnType fn = getType f
                                       (FnT params retty, _) = getEffectiveFunType fn
                                   in retty
getType (App {}) = error "App should not be here"
getType (Hole pos Nothing) = error "Hole should not be here"
getType (Hole pos (Just (ty, _))) = ty
getType (Get pos loc) = getLocType loc
getType (Addr pos loc) = PtrType (getLocType loc)
getType (Set {}) = Void
getType (AssertType _ _ ty) = ty
--getType (Unary
--getType (Binary

getLocType :: Location CExpr -> Type
getLocType (Ref ty v) = ty
getLocType (Index a idxs) = getTypeIdx idxs (normalizeTypes $ getType a)
  where getTypeIdx [] aty = normalizeTypes aty
        getTypeIdx (idx:idxs) (VecType (ibnd:ibnds) bty) =
          case normalizeTypes (getType idx) of
           IntType _               ->                getTypeIdx idxs (VecType ibnds bty)
           VecType idxs' idxtybase -> VecType idxs' (getTypeIdx idxs (VecType ibnds bty))
getLocType (Field a field) = error "getLocType field not implemented"
getLocType (Deref a) = let (PtrType a') = getType a
                       in a'
