{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Converts the parser's AST into the core AST.
module Language.Plover.Convert where

import Language.Plover.ParserTypes
import Language.Plover.ErrorUtil
import Data.Tag
import Data.Maybe
import Text.ParserCombinators.Parsec.Pos
import Control.Monad
import Control.Applicative ((<$>), (<*>))
import qualified Language.Plover.Types as T

data ConvertError = ConvertError !SourcePos [String]
                  deriving (Show)

makePos :: Expr -> SourcePos
makePos (PExpr tag _) = makePos' tag

makePos' :: Tag SourcePos -> SourcePos
makePos' NoTag = newPos "<unknown>" (-1) (-1)
makePos' (Tag a _) = a
makePos' (ProvTag _ mt) = makePos' mt
makePos' (MergeTags {}) = error "Unexpected MergeTags in makePos (parser doesn't generate these)"

makeExpr :: Expr -> Either ConvertError T.CExpr
makeExpr exp@(PExpr pos e') = case e' of
  Vec [] e -> makeExpr e
  Vec ((v,r):bs) e -> T.Vec pos v <$> makeRange r <*> makeExpr (PExpr pos (Vec bs e))
  For [] e -> makeExpr e
  For ((v,r):bs) e -> T.For pos v <$> makeRange r <*> makeExpr (PExpr pos (For bs e))
  While test body -> T.While pos <$> makeExpr test <*> makeExpr body
  Ref v -> return $ T.Get pos $ T.Ref (T.TypeHole Nothing) v
  T -> Left $ ConvertError (makePos exp) ["Unexpected transpose operator in non-exponent position"]
  Hole -> return $ T.Hole pos Nothing
  NoisyHole -> return $ T.NoisyHole pos
  IntLit t i -> return $ T.IntLit pos t i
  FloatLit t x -> return $ T.FloatLit pos t x
  BoolLit b -> return $ T.BoolLit pos b
  StrLit s -> return $ T.StrLit pos s
  VecLit es -> T.VecLit pos (T.TypeHole Nothing) <$> mapM makeExpr es
  If a b c -> T.If pos <$> makeExpr a <*> makeExpr b <*> makeExpr c
  Specialize v cases -> do (cases', dflt) <- processCases [] cases
                           return $ T.Specialize pos v cases' dflt
    where processCases acc [] = Left $ ConvertError (makePos exp)
                                ["Missing default case."]
          processCases acc [(PExpr _ Hole, dflt)] = do dflt' <- makeExpr dflt
                                                       return $ (reverse acc, dflt')
          processCases acc ((PExpr _ Hole, _):xs) = Left $ ConvertError (makePos exp)
                                                    ["Default case must not precede other cases."]
          processCases acc ((PExpr _ (IntLit _ i),cons):xs) = do
            cons' <- makeExpr cons
            processCases ((i,cons'):acc) xs
          processCases acc _ = Left $ ConvertError (makePos exp)
                               ["Can only specialize on integers."]
  Return e -> T.Return pos (T.TypeHole Nothing) <$> makeExpr e
  Assert e -> T.Assert pos <$> makeExpr e
  UnExpr Deref a -> T.Get pos . T.Deref <$> makeExpr a
  UnExpr Addr a -> T.Addr pos <$> makeLocation a
  UnExpr op a -> T.Unary pos (tr op) <$> makeExpr a
    where tr Pos = T.Pos
          tr Neg = T.Neg
          tr Deref = error "Not translatable here"
          tr Transpose = T.Transpose
          tr Inverse = T.Inverse
  BinExpr Pow a (PExpr _ T) -> -- A^T is transpose of A
    T.Unary pos T.Transpose <$> makeExpr a
  BinExpr Pow a (PExpr _ (UnExpr Neg (PExpr _ (IntLit _ 1)))) -> -- A^(-1) is A inverse
    T.Unary pos T.Inverse <$> makeExpr a
  BinExpr Pow a (PExpr _ (UnExpr Neg (PExpr _ T))) -> -- A^(-T) is transpose of A inverse
    T.Unary pos T.Transpose . T.Unary pos T.Inverse <$> makeExpr a
  BinExpr Type a b -> T.AssertType pos <$> makeExpr a <*> makeType b
  BinExpr op a b -> T.Binary pos (tr op) <$> makeExpr a <*> makeExpr b
    where tr Add = T.Add
          tr Sub = T.Sub
          tr Mul = T.Mul
          tr Hadamard = T.Hadamard
          tr Div = T.Div
          tr Pow = T.Pow
          tr Concat = T.Concat
          tr Type = error "Not translatable here"
          tr And = T.And
          tr Or = T.Or
          tr EqualOp = T.EqOp
          tr NEqOp = T.NEqOp
          tr LTOp = T.LTOp
          tr LTEOp = T.LTEOp

  Field {} -> T.Get pos <$> makeLocation exp
  Index {} -> T.Get pos <$> makeLocation exp

  Tuple xs -> T.TupleLit pos <$> mapM makeExpr xs
  Range {} -> T.RangeVal pos <$> makeRange exp

  App (PExpr _ (Ref v)) args | Just f <- lookup v builtinFuncs  -> f pos args
  App f args -> T.App pos <$> makeExpr f <*> (forM args' $ \arg -> case arg of
                                                Arg d a -> T.Arg d <$> makeExpr a
                                                ImpArg a -> T.ImpArg <$> makeExpr a)
    where args' = filter novoid args
          novoid (Arg _ (PExpr _ VoidExpr)) = False
          novoid _ = True
  SeqExpr xs -> makeSequence pos xs
  DefExpr _ _ -> Left $ ConvertError (makePos exp) ["Unexpected definition outside sequence."]
  StoreExpr loc a -> T.Set pos <$> makeLocation loc <*> makeExpr a

  Extern _ -> Left $ ConvertError (makePos exp) ["Non-toplevel extern."]
  Static _ -> Left $ ConvertError (makePos exp) ["Non-toplevel static."]
  _ -> Left $ ConvertError (makePos exp) ["Unexpected or unimplemented expression."]

exArgs pos args n = do args' <- forM args $ \arg ->
                         case arg of
                           ImpArg _ -> Left $ ConvertError pos ["Unexpected implicit argument."]
                           Arg ArgIn a -> makeExpr a
                           Arg _ _ -> Left $ ConvertError pos ["Expecting in-argument."]
                       if length args' == n
                         then return args'
                         else Left $ ConvertError pos
                              ["Expecting " ++ show n ++ " argument(s) for builtin function."]

type BuiltinFunc = Tag SourcePos -> [Arg Expr] -> Either ConvertError T.CExpr

builtinUFunc :: (Tag SourcePos -> T.CExpr -> Either ConvertError T.CExpr)
                -> BuiltinFunc
builtinUFunc f pos args = do [a] <- exArgs (makePos' pos) args 1
                             f pos a
builtinBFunc :: (Tag SourcePos -> T.CExpr -> T.CExpr -> Either ConvertError T.CExpr)
                -> BuiltinFunc
builtinBFunc f pos args = do [a, b] <- exArgs (makePos' pos) args 2
                             f pos a b

builtinScalarFunc :: BuiltinFunc
builtinScalarFunc pos args = do [n,a] <- scalarArgs args
                                return $ T.ScalarMatLit pos n a
  where scalarArgs [Arg ArgIn a] = do a' <- makeExpr a
                                      return [T.Hole pos Nothing, a']
        scalarArgs [ImpArg n, Arg ArgIn a] = do n' <- makeExpr n
                                                a' <- makeExpr a
                                                return [n', a']
        scalarArgs _ = Left $ ConvertError (makePos' pos) ["Expecting maybe an implicit argument and an in-argument."]


builtinFuncs = [ ("not", builtinUFunc (\pos arg -> return $ T.Unary pos T.Not arg))
               , ("sum", builtinUFunc (\pos arg -> return $ T.Unary pos T.Sum arg))
               , ("diag", builtinUFunc (\pos arg -> return $ T.Unary pos T.Diag arg))
               , ("shape", builtinUFunc (\pos arg -> return $ T.Unary pos T.Shape arg))
               , ("nospill", builtinUFunc (\pos arg -> return $ T.Unary pos T.NoSpill arg))
               , ("reshape", builtinBFunc (\pos a b -> return $ T.Binary pos T.Reshape a b))
               , ("scalar", builtinScalarFunc)
               ]
               ++ [(v, builtinUFunc (\pos arg -> return $ T.Unary pos (T.VecCons st) arg))
                  | (v, st) <- storageTypeMap]

makeLocation :: Expr -> Either ConvertError (T.Location T.CExpr)
makeLocation exp@(PExpr pos e') = case e' of
  Field a n -> T.Field <$> makeExpr a <*> pure n
  Index a (PExpr _ (Tuple idxs)) -> T.Index <$> makeExpr a <*> mapM makeExpr idxs
  Index a b -> T.Index <$> makeExpr a <*> (return <$> makeExpr b)
  UnExpr Deref a -> T.Deref <$> makeExpr a
  Ref v -> return $ T.Ref (T.TypeHole Nothing) v
  _ -> Left $ ConvertError (makePos exp) ["Expecting location."]

makeRange :: Expr -> Either ConvertError (T.Range T.CExpr)
makeRange exp@(PExpr pos e') = case e' of
  Range start stop step -> do start' <- maybe (return $ T.IntLit pos T.defaultIntType 0) makeExpr start
                              stop' <- maybe (return $ T.Hole pos Nothing) makeExpr stop
                              step' <- maybe (return $ T.IntLit pos T.defaultIntType 1) makeExpr step
                              return $ T.Range start' stop' step'
  _ -> do ee <- makeExpr exp
          return $ T.Range (T.IntLit pos T.defaultIntType 0) ee (T.IntLit pos T.defaultIntType 1)

makeSequence :: Tag SourcePos -> [Expr] -> Either ConvertError T.CExpr
makeSequence pos [] = return $ T.VoidExpr pos
makeSequence pos (x@(PExpr pos' x') : xs) = case x' of
  DefExpr (PExpr pos2 a) b
    | null xs -> Left $ ConvertError (makePos x) ["Definition cannot be last thing in sequence."]
    | otherwise -> case a of
      BinExpr Type av at -> -- ((av :: at) := b; ...) => (av := (b :: at); ...)
        makeSequence pos $ (wrapTag pos' $ DefExpr av $ wrapTag pos2 $ BinExpr Type b at) : xs
      Ref v -> T.Let pos' v <$> makeExpr b <*> makeSequence pos xs
      _ -> Left $ ConvertError (makePos x) ["Expecting symbol for definition."]
  BinExpr Type (PExpr pos'' (Ref v)) vt
    | null xs -> Left $ ConvertError (makePos x) ["Definition cannot be last thing in sequence."]
    | otherwise -> T.Let pos' v . T.Uninitialized pos'' <$> makeType vt <*> makeSequence pos xs
  _ | null xs -> makeExpr x
    | otherwise -> T.Seq pos <$> makeExpr x <*> makeSequence pos xs


makeType :: Expr -> Either ConvertError T.Type
makeType exp@(PExpr pos e') = case e' of
  Index a (PExpr _ (Tuple idxs)) -> T.VecType T.DenseMatrix <$> mapM makeExpr idxs <*> makeType a
  Index a b -> T.VecType T.DenseMatrix <$> (return <$> makeExpr b) <*> makeType a
  App (PExpr _ (Ref v)) args -> makeTypeFunc (makePos exp) v args
  -- (no way to write the type of a function.)
  Ref v -> case v of
    "u8" -> return $ T.IntType T.U8
    "s8" -> return $ T.IntType T.S8
    "u16" -> return $ T.IntType T.U16
    "s16" -> return $ T.IntType T.S16
    "u32" -> return $ T.IntType T.U32
    "s32" -> return $ T.IntType T.S32
    "u64" -> return $ T.IntType T.U64
    "s64" -> return $ T.IntType T.S64
    "int" -> return $ T.IntType T.defaultIntType
    "float" -> return $ T.FloatType T.Float
    "double" -> return $ T.FloatType T.Double
    "string" -> return $ T.StringType
    "bool" -> return $ T.BoolType
    _ -> return $ T.TypedefType (T.TypeHole Nothing) v
  UnExpr Deref a -> T.PtrType <$> makeType a
  Tuple xs -> T.TupleType <$> mapM makeType xs
  Hole -> return $ T.TypeHole Nothing
  NoisyHole -> return $ T.NoisyTypeHole pos
  _ -> Left $ ConvertError (makePos exp) ["Expecting type"]

storageTypeMap :: [(String, T.StorageType)]
storageTypeMap = [ ("Dense", T.DenseMatrix)
                 , ("Diagonal", T.DiagonalMatrix)
                 , ("UpperTriangular", T.UpperTriangular)
                 , ("UpperUnitTriangular", T.UpperUnitTriangular)
                 , ("LowerTriangular", T.LowerTriangular)
                 , ("LowerUnitTriangular", T.LowerUnitTriangular)
                 , ("Symmetric", T.SymmetricMatrix)
                 , ("Scalar", T.ScalarMatrix)
                 ]

makeTypeFunc :: SourcePos -> String -> [Arg Expr] -> Either ConvertError T.Type
makeTypeFunc pos v args
  | Just st <- lookup v storageTypeMap = vecStoreType st
  | otherwise = Left $ ConvertError pos ["Unknown type-level function."]

  where vecStoreType st = case args of
          [Arg ArgIn a] -> do
            aty <- makeType a
            case aty of
              T.VecType _ bnds bty -> return $ T.VecType st bnds bty
              _ -> Left $ ConvertError (makePos a) ["Expecting matrix type."]
          _ -> Left $ ConvertError pos ["Expecting exactly one type argument to type-level function."]

makeDefs :: Expr -> Either ConvertError [T.DefBinding]
makeDefs exp@(PExpr pos pe) = case pe of
  SeqExpr xs -> fmap mconcat $ mapM makeDefs xs
  Extern a -> fmap (map (\z -> z { T.extern = True })) $ makeDefs a
  Static a -> fmap (map (\z -> z { T.static = True })) $ makeDefs a
  BinExpr Type a b -> return <$> makeTopType exp Nothing
  DefExpr a b -> return <$> (makeTopType a . Just =<< makeExpr b)
  Struct v members -> return <$> makeStructDecl pos v members
  Typedef v ty -> return <$> (T.mkBinding pos v . T.TypeDef <$> makeType ty)
  Import s -> return [T.mkBinding pos s $ T.ImportDef s]
  InlineC s -> return [T.mkBinding pos uniqueName $ T.InlineCDef s]
  _ -> Left $ ConvertError (makePos exp) ["Unexpected top-level form."]

  where uniqueName = "[:-D]" ++ show pos

makeStructDecl :: Tag SourcePos -> Variable -> [Expr] -> Either ConvertError T.DefBinding
makeStructDecl pos v members = T.mkBinding pos v . T.StructDef <$> mapM makeStructMember members
  where makeStructMember (PExpr _ (BinExpr Type (PExpr pos (Ref v)) b))
          = do (t, t') <- makeMemberType b
               return (v, (pos, t, t'))
        -- TODO parse asserts inside struct
        makeStructMember exp
          = Left $ ConvertError (makePos exp) ["Expecting member in struct."]

        makeMemberType (PExpr _ (BinExpr Storing a b)) = do t <- makeType a
                                                            t' <- makeType b
                                                            return (t, t')
        makeMemberType a = do t <- makeType a
                              return (t, t)

makeTopType :: Expr -> Maybe T.CExpr -> Either ConvertError T.DefBinding
makeTopType exp@(PExpr _ pe) val = case pe of
  BinExpr Type (PExpr pos (Ref v)) b -> T.mkBinding pos v . T.ValueDef val <$> makeType b
  BinExpr Type (PExpr pos (App (PExpr pos' (Ref v)) args)) b ->
    do fnt <- funArgs T.FnT args
       t <- makeType b
       return $ T.mkBinding pos' v $ T.FunctionDef val $ fnt t
  _ -> Left $ ConvertError (makePos exp) ["Expecting variable or function type definition (possibly missing return type)."]


funArgs :: ([(Tag SourcePos, Variable, Bool, T.ArgDir, T.Type)] -> Maybe T.ArgDir -> a)
        -> [Arg Expr] -> Either ConvertError a
funArgs f args = funArgs' [] args
  where
    funArgs' acc [] = return $ f (reverse acc) Nothing
    funArgs' acc ((Arg dir e@(PExpr apos pe)):args) = case pe of
      Ref "__VARARGS__" -> case args of
        [] -> return $ f (reverse acc) (Just dir)
        _ -> Left $ ConvertError (makePos e)
             ["No function parameters definitions may come after varargs."]
      Ref v -> funArgs' ((apos, v, True, T.ArgIn, T.TypeHole Nothing):acc) args
      BinExpr Type (PExpr pos (Ref v)) b  -> do t <- makeType b
                                                funArgs' ((pos, v, True, dir, t):acc) args
      VoidExpr -> funArgs' acc args
      _ -> Left $ ConvertError (makePos e) ["Bad argument definition."]
    funArgs' acc ((ImpArg e@(PExpr pos pe)):args) = case pe of
      Tuple idxs -> funArgs' acc (map ImpArg idxs ++ args) -- shorthand: f {n,m}
      Ref v -> funArgs' ((pos, v, False, T.ArgIn, T.IntType T.IDefault):acc) args
      BinExpr Type (PExpr pos' (Ref v)) b  -> do t <- makeType b
                                                 funArgs' ((pos', v, False, T.ArgIn, t):acc) args
      _ -> Left $ ConvertError (makePos e) ["Bad implicit argument definition."]

reportConvertErr :: ConvertError
                 -> IO String
reportConvertErr (ConvertError pos messages)
  = do sl <- showLineFromFile pos
       return $ "Error at " ++ sl
         ++ "\n" ++ (unlines messages)
