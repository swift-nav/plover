{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Converts the parser's AST into the core AST.
module Language.Plover.Convert where

import Language.Plover.ParserTypes
import Language.Plover.ErrorUtil
import Data.Tag
import Text.ParserCombinators.Parsec.Pos
import Control.Monad
import Control.Applicative ((<$>), (<*>))
import qualified Language.Plover.Types as T

data ConvertError = ConvertError !SourcePos [String]
                  deriving (Show)

makePos :: Expr -> SourcePos
makePos (PExpr tag _) = makePos' tag
  where makePos' NoTag = newPos "<unknown>" (-1) (-1)
        makePos' (Tag a _) = a
        makePos' (ProvTag _ mt) = makePos' mt
        makePos' (MergeTags {}) = error "Unexpected MergeTags in makePos (parser doesn't generate these)"

makeExpr :: Expr -> Either ConvertError T.CExpr
makeExpr exp@(PExpr pos e') = case e' of
  Vec [] e -> makeExpr e
  Vec ((v,r):bs) e -> do rng <- makeRange r
                         ee <- makeExpr (PExpr pos (Vec bs e))
                         return $ T.Vec pos v rng ee
  For [] e -> makeExpr e
  For ((v,r):bs) e -> do rng <- makeRange r
                         ee <- makeExpr (PExpr pos (For bs e))
                         return $ T.For pos v rng ee
  Sum [] e -> makeExpr e
  Sum ((v,r):bs) e -> do rng <- makeRange r
                         ee <- makeExpr (PExpr pos (Sum bs e))
                         return $ T.Unary pos T.Sum $ T.Vec pos v rng ee
  Ref v -> return $ T.Get pos $ T.Ref (T.TypeHole Nothing) v
  VoidExpr -> return $ T.VoidExpr pos
  T -> Left $ ConvertError (makePos exp) ["Unexpected transpose operator in non-exponent position"]
  Hole -> return $ T.Hole pos Nothing
  IntLit t i -> return $ T.IntLit pos t i
  FloatLit t x -> return $ T.FloatLit pos t x
  BoolLit b -> return $ T.BoolLit pos b
  StrLit s -> return $ T.StrLit pos s
  VecLit es -> do es' <- mapM makeExpr es
                  return $ T.VecLit pos (T.TypeHole Nothing) es'
  If a b c -> do a' <- makeExpr a
                 b' <- makeExpr b
                 c' <- makeExpr c
                 return $ T.If pos a' b' c'
  UnExpr Deref a -> do a' <- makeExpr a
                       return $ T.Get pos $ T.Deref a'
  UnExpr Addr a -> do a' <- makeLocation a
                      return $ T.Addr pos a'
  UnExpr Pos a -> do a' <- makeExpr a
                     return $ T.AssertType pos a' T.NumType -- This is just an assertion, and will be removed after unification
  UnExpr op a -> do a' <- makeExpr a
                    return $ T.Unary pos (tr op) a'
    where tr Neg = T.Neg
          tr Pos = error "Not translatable here"
          tr Deref = error "Not translatable here"
          tr Transpose = T.Transpose
          tr Inverse = T.Inverse
          tr Not = T.Not
  BinExpr Pow a (PExpr _ T)
    -> T.Unary pos T.Transpose <$> makeExpr a  -- A^T is transpose of A
  BinExpr Pow a (PExpr _ (UnExpr Neg (PExpr _ (IntLit _ 1))))
    -> T.Unary pos T.Inverse <$> makeExpr a  -- A^(-1) is A inverse
  BinExpr Pow a (PExpr _ (UnExpr Neg (PExpr _ T)))
    -> do a' <- makeExpr a -- A^(-T) is transpose of A inverse
          return $ T.Unary pos T.Transpose (T.Unary pos T.Inverse a')
  BinExpr Pow a b -> T.Binary pos T.Pow <$> makeExpr a <*> makeExpr b
  BinExpr Type a b -> do a' <- makeExpr a
                         b' <- makeType b
                         return $ T.AssertType pos a' b'
  BinExpr op a b -> do a' <- makeExpr a
                       b' <- makeExpr b
                       return $ T.Binary pos (tr op) a' b'
    where tr Add = T.Add
          tr Sub = T.Sub
          tr Mul = T.Mul
          tr Div = T.Div
          tr Pow = error "Not translatable here"
          tr Concat = T.Concat
          tr Type = error "Not translatable here"
          tr And = T.And
          tr Or = T.Or
          tr EqualOp = T.EqOp
          tr LTOp = T.LTOp
          tr LTEOp = T.LTEOp

  Field _ _ -> T.Get pos <$> makeLocation exp
  Index _ _ -> T.Get pos <$> makeLocation exp

  Tuple _ -> Left $ ConvertError (makePos exp) ["What do we do with tuples?"]
  Range _ _ _ -> T.RangeVal pos <$> makeRange exp

  App f args -> T.App pos <$> makeExpr f <*> (mapM $ \arg -> case arg of
                                               Arg a -> T.Arg <$> makeExpr a
                                               ImpArg a -> T.ImpArg <$> makeExpr a) args'
    where args' = filter (\arg -> case arg of { Arg (PExpr _ VoidExpr) -> False; _ -> True }) args
  SeqExpr xs -> makeSequence pos xs
  DefExpr _ _ -> Left $ ConvertError (makePos exp) ["Unexpected definition outside sequence."]
  StoreExpr loc a -> do loc' <- makeLocation loc
                        a' <- makeExpr a
                        return $ T.Set pos loc' a'

  Extern _ -> Left $ ConvertError (makePos exp) ["Non-toplevel extern"]
  Static _ -> Left $ ConvertError (makePos exp) ["Non-toplevel static"]
  _ -> Left $ ConvertError (makePos exp) ["Unimplemented expression " ++ show exp]

makeLocation :: Expr -> Either ConvertError (T.Location T.CExpr)
makeLocation exp@(PExpr pos e') = case e' of
  Field a n -> do a' <- makeExpr a
                  return $ T.Field a' n
  Index a (PExpr _ (Tuple idxs)) -> do a' <- makeExpr a
                                       idxs' <- mapM makeExpr idxs
                                       return $ T.Index a' idxs'
  UnExpr Deref a -> do a' <- makeExpr a
                       return $ T.Deref a'
  Index a b -> do a' <- makeExpr a
                  idx' <- makeExpr b
                  return $ T.Index a' [idx']

  Ref v -> return $ T.Ref (T.TypeHole Nothing) v

  _ -> Left $ ConvertError (makePos exp) ["Expecting location instead of " ++ show exp]

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
makeSequence pos [x] = makeExpr x
makeSequence pos (x@(PExpr pos' x') : xs) = case x' of
  (DefExpr (PExpr pos2 a) b) -> case a of
    BinExpr Type av at ->
      makeSequence pos ((wrapTag pos' $ (DefExpr av (wrapTag pos2 $ BinExpr Type b at)))
                        : xs)
    Ref v -> do b' <- makeExpr b
                T.Let pos' v b' <$> makeSequence pos xs
  _ -> T.Seq pos <$> makeExpr x <*> makeSequence pos xs


makeType :: Expr -> Either ConvertError (T.Type)
makeType exp@(PExpr _ e') = case e' of
  Index a (PExpr _ (Tuple idxs)) -> do a' <- makeType a
                                       idxs' <- mapM makeExpr idxs
                                       return $ T.VecType T.DenseMatrix idxs' a'
  Index a b -> do a' <- makeType a
                  b' <- makeExpr b
                  return $ T.VecType T.DenseMatrix [b'] a'
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
    "float" -> return $ T.FloatType T.Float
    "double" -> return $ T.FloatType T.Double
    "string" -> return $ T.StringType
    "bool" -> return $ T.BoolType
    _ -> return $ T.TypedefType v
  UnExpr Deref a -> T.PtrType <$> makeType a
  VoidExpr -> return T.Void
  Hole -> return $ T.TypeHole Nothing
  _ -> Left $ ConvertError (makePos exp) ["Expecting type instead of " ++ show exp]

--  ee <- makeExpr exp
--  case ee of

makeDefs :: Expr -> Either ConvertError [T.DefBinding]
makeDefs exp@(PExpr pos pe) = case pe of
  SeqExpr xs -> fmap join $ mapM makeDefs xs
  Extern a -> fmap (map (\z -> z { T.extern = True })) $ makeDefs a
  Static a -> fmap (map (\z -> z { T.static = True })) $ makeDefs a
  BinExpr Type a b -> do bind <- makeTopType exp Nothing
                         return [bind]
  DefExpr a b -> do b' <- makeExpr b
                    bind <- makeTopType a (Just b')
                    return [bind]
  Struct v members -> do b <- makeStructDecl pos v members
                         return [b]
  _ -> Left $ ConvertError (makePos exp) ["Unexpected top-level form."]

makeStructDecl :: Tag SourcePos -> Variable -> [Expr] -> Either ConvertError T.DefBinding
makeStructDecl pos v members = do members' <- mapM makeStructMember members
                                  return $ T.mkBinding pos v $ T.StructDef members'
  where makeStructMember (PExpr _ (BinExpr Type (PExpr _ (Ref v)) b)) = do t <- makeType b
                                                                           return (v, t)
        makeStructMember exp = Left $ ConvertError (makePos exp) ["Expecting member in struct."]

makeTopType :: Expr -> Maybe T.CExpr -> Either ConvertError T.DefBinding
makeTopType exp@(PExpr _ pe) val = case pe of
  BinExpr Type (PExpr pos a) b -> case a of
    Ref v -> do t <- makeType b
                return $ T.mkBinding pos v $ T.ValueDef val t
    App (PExpr pos f) args -> case f of
                             Ref v -> do t <- makeType b
                                         at <- funArgs args
                                         return $ T.mkBinding pos v $ T.FunctionDef val (T.FnT at t)
    _ -> Left $ ConvertError (makePos exp) ["Expecting variable or function type definition."]
  _ -> Left $ ConvertError (makePos exp) ["Expecting variable or function type definition (possibly missing return type)."]


funArgs :: [Arg Expr] -> Either ConvertError [(Variable, Bool, T.ArgDir, T.Type)]
funArgs [] = return []
funArgs ((Arg e@(PExpr _ pe)):args) = case pe of
  BinExpr Type (PExpr _ (Ref v)) b  -> do t <- makeType b
                                          ([(v, True, T.ArgIn, t)] ++) <$> funArgs args
  BinExpr Type (PExpr _ (App (PExpr _ (Ref dir)) [Arg (PExpr _ (Ref v))])) b -> do
    dir <- decodeDir dir
    t <- makeType b
    ([(v, True, dir, t)] ++) <$> funArgs args

    where decodeDir dir = case dir of
            "in" -> Right T.ArgIn
            "out" -> Right T.ArgOut
            "inout" -> Right T.ArgInOut
            _ -> Left $ ConvertError (makePos e) ["Invalid argument direction specifier " ++ show dir]
  VoidExpr -> funArgs args
  _ -> Left $ ConvertError (makePos e) ["Argument definition must have explicit type."]
funArgs ((ImpArg e@(PExpr _ pe)):args) = case pe of
  Tuple idxs -> funArgs ((map ImpArg idxs) ++ args)
  Ref v -> ([(v, False, T.ArgIn, T.IntType T.IDefault)] ++) <$> funArgs args
  BinExpr Type (PExpr _ (Ref v)) b  -> do t <- makeType b
                                          ([(v, False, T.ArgIn, t)] ++) <$> funArgs args
  _ -> Left $ ConvertError (makePos e) ["Implicit argument definition must have explicit type."]

reportConvertErr :: ConvertError
                 -> IO String
reportConvertErr (ConvertError pos messages)
  = do sl <- showLineFromFile pos
       return $ "Error at " ++ sl
         ++ "\n" ++ (unlines messages)
