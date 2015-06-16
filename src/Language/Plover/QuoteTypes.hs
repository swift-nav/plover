{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Plover.QuoteTypes
       where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import Control.Monad
import Control.Monad.State
import Control.Applicative hiding (many, (<|>))
import Data.Maybe
import Data.Traversable
import Data.Functor.Fixedpoint
import Data.List
import Text.PrettyPrint

import Language.Plover.Types (IntType, FloatType)

data Tag a = Tag !a | NoTag
           deriving (Show)

data Tagged tag a = WithTag { maybeTag :: !(Tag tag), stripTag :: a }
                  deriving (Show)

instance Eq a => Eq (Tagged tag a) where
  x == y  = stripTag x == stripTag y

instance Functor (Tagged tag) where
  fmap f (WithTag mt a) = WithTag mt (f a)

instance Foldable (Tagged tag) where
  foldr f z x = f (stripTag x) z

instance Traversable (Tagged tag) where
  traverse f (WithTag tag a) = WithTag tag <$> f a

data PosExpr' a = PosExpr' (Tagged SourcePos (Expr' a))

instance Functor PosExpr' where
  fmap f (PosExpr' x) = PosExpr' (fmap (fmap f) x)

instance Foldable PosExpr' where
  foldr f z (PosExpr' x) = foldr f z (stripTag x)

instance Traversable PosExpr' where
  traverse f (PosExpr' (WithTag tag a)) = PosExpr' . WithTag tag <$> traverse f a

instance Show a => Show (PosExpr' a) where
  show (PosExpr' x) = "(" ++ show (stripTag x) ++ ")"

type Expr = Fix PosExpr'

pattern PExpr tag a = Fix (PosExpr' (WithTag tag a))

liftExpr :: Expr' Expr -> Expr
liftExpr x = PExpr NoTag x

wrapPos :: SourcePos -> Expr' Expr -> Expr
wrapPos pos x = PExpr (Tag pos) x

-- | This is really just a synonym for PExpr
wrapTag :: Tag SourcePos -> Expr' Expr -> Expr
wrapTag mpos x = PExpr mpos x

newtype Unique = Unique Int
data PosGraph a = PosGraph [(Unique, Tag SourcePos, a Unique)]

instance Show Unique where
  show (Unique i) = "#" ++ show i

instance Show (PosGraph Expr') where
  show (PosGraph xs) = "PosGraph [\n" ++ intercalate "\n" (map f xs) ++ "\n]"
    where f (i, msp, expr) = " " ++ show i
                             ++ " = " ++ show expr ++ ";"
                             ++ (case msp of
                                  NoTag -> ""
                                  Tag pos -> "     (position " ++ show pos ++ ")")

toPosGraph :: Expr -> PosGraph Expr'
toPosGraph (Fix (PosExpr' e)) = PosGraph $ evalState (g e) []
  where g e = do e' <- traverse f (stripTag e)
                 i <- Unique . length <$> get
                 graph <- get
                 return $ graph ++ [(i, maybeTag e, e')]
        f (Fix (PosExpr' e)) = do
          e' <- traverse f (stripTag e)
          i <- Unique . length <$> get
          modify (++ [(i, maybeTag e, e')])
          return i

-- data IntType = U8 | I8
--              | U16 | I16
--              | U32 | I32
--              | U64 | I64
--              deriving (Eq, Show)
-- data FloatType = Float | Double
--                deriving (Eq, Show)

type Variable = String


data UnOp = Neg
          | Pos
          | Deref
          | Transpose
          | Inverse
          | Not
          deriving (Show, Eq)

data BinOp = Add
           | Sub
           | Mul
           | Div
           | Pow
           | Dot
           | Concat
           | Type
           | And
           | Or
           | EqualOp
           | LTOp
           | LTEOp
           deriving (Show, Eq)

data Expr' a = Vec [(Variable,a)] a
          | Sum [(Variable,a)] a
          | For [(Variable,a)] a
            
            -- Elementary Expressions
          | Ref Variable
          | VoidExpr
          | T
          | Hole
          | IntLit (Maybe IntType) Integer
          | FloatLit (Maybe FloatType) Double
          | BoolLit Bool
          | StrLit String
          | VecLit [a]
          | If a a a

            -- Operators
          | UnExpr UnOp a
          | BinExpr BinOp a a

            -- Structures
          | Field a String
          | FieldDeref a String

            -- Vectors
          | Index a a
          | Tuple [a]
          | Range (Maybe a) (Maybe a) (Maybe a)

            -- Calling
          | App a [Arg a]

            -- Sequencing
          | SeqExpr [a]

            -- State
          | DefExpr a a
          | StoreExpr a a

            -- Declarations
          | Extern a
          | Static a
          | Struct Variable [a]
          deriving (Eq, Show, Functor, Traversable, Foldable)

data Arg a = ImpArg a
           | Arg a
           deriving (Eq, Show, Functor, Traversable, Foldable)


integer :: Integer -> Expr' a
integer x = IntLit Nothing x

float :: Double -> Expr' a
float x = FloatLit Nothing x

class PP a where
  pretty :: a -> Doc

instance PP a => PP (Tagged tag a) where
  pretty x = pretty (stripTag x)

instance PP (a (Fix a)) => PP (Fix a) where
  pretty (Fix x) = pretty x

instance PP a => PP (PosExpr' a) where
  pretty (PosExpr' x) = pretty x

instance PP a => PP (Expr' a) where
  pretty (Ref v) = text v
  pretty VoidExpr = text "Void"
  pretty T = text "T"
  pretty Hole = text "_"
  pretty (IntLit Nothing x) = parens $ text $ "IntLit " ++ show x
  pretty (IntLit (Just t) x) = parens $ text $ "IntLit " ++ show t ++ " " ++ show x
  pretty (FloatLit Nothing x) = parens $ text $ "FloatLit " ++ show x
  pretty (FloatLit (Just t) x) = parens $ text $ "(FloatLit " ++ show t ++ " " ++ show x
  pretty (BoolLit b) = parens $ text $ "BoolLit " ++ show b
  pretty (StrLit s) = parens $ text $ "StrLit " ++ show s
  pretty (VecLit xs) = parens $ text "VecLit" <+> sep (map pretty xs)

  pretty (If a b c) = parens $ (text "if" <+> nest 3 (pretty a)) $$ (nest 1 (vcat [text "then" <+> pretty b, text "else" <+> pretty c]))

  pretty (UnExpr op exp) = parens $ hang (text $ show op) 1 (pretty exp)
  pretty (BinExpr op a b) = parens $ hang (text $ f op) (length (f op) + 1) $ sep [pretty a, pretty b]
    where
      f Add = "+"
      f Sub = "-"
      f Mul = "*"
      f Div = "/"
      f Pow = "^"
      f EqualOp = "=="
      f LTOp = "<"
      f LTEOp = "<="
      f Type = "::"
      f op = show op

  pretty (Field e field) = parens $ hang (text "Field") 1 $ sep [pretty e, text $ show field]
  pretty (FieldDeref e field) = parens $ hang (text "FieldDeref") 1 $ sep [pretty e, text $ show field]

  pretty (Index e ei) = parens $ hang (text "Index") 1 $ sep [nest 5 $ pretty e, pretty ei]
  pretty (Tuple exps) = parens $ hang (text "Tuple") 1 $ sep (map pretty exps)
  pretty (Range a b c) = parens $ hang (text "Range") 1 $
                         hcat $ punctuate (text ":") [p a, p b, p c]
    where p Nothing = text "Nothing"
          p (Just x) = pretty x

  pretty (Vec vs e) = parens $ hang (text "Vec") 1 $ sep [nest 3 $ sep (map iter vs) <+> text "->", pretty e]
    where iter (v, e) = parens $ text v <+> text "in" <+> pretty e
  pretty (Sum vs e) = parens $ hang (text "Sum") 1 $ sep [nest 5 $ sep (map iter vs) <+> text "->", pretty e]
    where iter (v, e) = parens $ text v <+> text "in" <+> pretty e
  pretty (For vs e) = parens $ hang (text "For") 1 $ sep [nest 3 $ sep (map iter vs) <+> text "->", pretty e]
    where iter (v, e) = parens $ text v <+> text "in" <+> pretty e

  pretty (App f args) = parens $ hang (pretty f) 0 $ sep (map pretty args)

  pretty (SeqExpr args) = parens $ hang (text "Seq") 4 $ vcat $ punctuate semi (map pretty args)

  pretty (DefExpr a b) = parens $ hang (text "Def") 1 $ sep [nest 3 $ pretty a, pretty b]
  pretty (StoreExpr a b) = parens $ hang (text "Store") 1 $ sep [nest 5 $ pretty a, pretty b]

  pretty (Extern a) = parens $ hang (text "Extern") 1 $ pretty a
  pretty (Static a) = parens $ hang (text "Static") 1 $ pretty a
  pretty (Struct n a) = parens $ (text "Struct" <+> text n) $$ nest 1 (vcat $ map pretty a)

instance PP a => PP (Arg a) where
  pretty (Arg a) = pretty a
  pretty (ImpArg a) = braces $ pretty a
