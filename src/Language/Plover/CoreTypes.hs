module Language.Plover.CoreTypes
       where

data IntType = U8 | I8
             | U16 | I16
             | U32 | I32
             | U64 | I64
             deriving (Eq, Show)
data FloatType = Float | Double
               deriving (Eq, Show)

 -- TODO is this how to deal with different matrix formats?
data MatrixForm = RowNormal
                | ColumnNormal
                | Diagonal
                | UpperTriangular
                | LowerTriangular
                | Symmetric

data Type e = IntType IntType
            | FloatType FloatType
            | BoolType
            | StringType
            | VoidType
            | VecType (Type e) (Expr e)
            | MatrixType MatrixForm (Type e) [Expr e]
            | FunctionType [Type e] (Type e)
            | PtrType (Type e)
            | StructType [(String, Type e)]
            | TypeRef String (Type e)

data UnOp = Neg | Not
          | Deref
          | Transpose | Inverse
          | Sum | For
          deriving (Show, Eq, Ord)
data BinOp = Add | Sub | Mul | Div
           | Pow | Dot | Concat
           | And | Or
           | EqOp | LTOp | LTEOp
           deriving (Show, Eq, Ord)

data Id e = Id String (Type e)

data Expr e = VoidExpr
            | IntLit IntType Integer
            | FloatLit FloatType Double
            | BoolLit Bool
            | StrLit String
            | Vec { vecVar :: (Id e)
                  , vecStart :: e, vecStop :: e, vecStep :: e
                  , vecBody :: e }
            | If e e e
            | UnExpr UnOp e
            | BinExpr BinOp e e
            | Get (Location e)
            | Set (Location e) e
            | Seq e e
            | Let (Id e) e e
            | App e [e]

data Location e = Index e [e]
                | Field e String
--                | FieldDeref e String
                | Deref e
                | Var (Id e)
