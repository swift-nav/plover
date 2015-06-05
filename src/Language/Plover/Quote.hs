module Language.Plover.Quote
 ( plover
 ) where

import Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
--import Data.Typeable
--import Data.Data
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Text.Printf
import Control.Monad
import Control.Applicative hiding (many, (<|>))
import qualified Text.PrettyPrint as PP
import Data.Maybe

plover :: QuasiQuoter
plover = QuasiQuoter
         { quoteExp = ploverQuoteExp
         , quotePat = undefined
         , quoteType = undefined
         , quoteDec = undefined
         }

ploverQuoteExp :: String -> Q Exp
ploverQuoteExp s =
  do loc <- TH.location
     let parser' = do setPosition
                        (newPos
                         (TH.loc_filename loc)
                         (fst $ TH.loc_start loc)
                         (snd $ TH.loc_start loc))
                      eparser
     case parse parser' "" s of
      Left e -> do fail ("Parse error " ++ show e) --reportError $ show e
                   --fail "Parse error" --reportError (show e) >> fail "Parse error"
      Right r -> return undefined


data IntType = U8 | I8
             | U16 | I16
             | U32 | I32
             | U64 | I64
             deriving (Eq, Show)
data FloatType = Float | Double
               deriving (Eq, Show)

type Variable = String

data UnOp = Neg
          | Pos
          | Deref
          | Transpose
          | Inverse
          deriving (Show, Eq)

data BinOp = Add
           | Sub
           | Mul
           | Div
           | Pow
           | Dot
           | In
           | Concat
           deriving (Show, Eq)

data Expr = Vec !SourcePos Expr Expr
          | Sigma !SourcePos Expr Expr
          | For !SourcePos Expr Expr
            
            -- Elementary Expressions
          | Ref !SourcePos Variable
          | VoidExpr !SourcePos
          | IntLit !SourcePos (Maybe IntType) Integer
          | FloatLit !SourcePos (Maybe FloatType) Double
          | BoolLit !SourcePos Bool
          | StrLit !SourcePos String

            -- Operators
          | UnExpr !SourcePos UnOp Expr
          | BinExpr !SourcePos BinOp Expr Expr

            -- Structures
          | Field !SourcePos Expr String

            -- Vectors
          | Index !SourcePos Expr Expr
          | Tuple !SourcePos [Expr]
          | Range !SourcePos (Maybe Expr) (Maybe Expr) (Maybe Expr)

            -- Calling
          | App !SourcePos Expr [Arg]

            -- Sequencing
          | SeqExpr !SourcePos [Expr]

            -- State
          | DefExpr !SourcePos Expr Expr
          | StoreExpr !SourcePos Expr Expr
          deriving (Eq, Show)

data Arg = ImpArg !SourcePos Expr
         | Arg !SourcePos Expr
         deriving (Eq, Show)

class PP a where
  pretty :: a -> PP.Doc

instance PP Expr where
  pretty (Ref _ v) = PP.text v
  pretty (VoidExpr _) = PP.text "VoidExpr"
  pretty (IntLit _ Nothing x) = PP.parens $ PP.text $ "IntLit " ++ show x
  pretty (IntLit _ (Just t) x) = PP.parens $ PP.text $ "IntLit " ++ show t ++ " " ++ show x
  pretty (FloatLit _ Nothing x) = PP.parens $ PP.text $ "FloatLit " ++ show x
  pretty (FloatLit _ (Just t) x) = PP.parens $ PP.text $ "(FloatLit " ++ show t ++ " " ++ show x
  pretty (BoolLit _ b) = PP.parens $ PP.text $ "BoolLit " ++ show b
  pretty (StrLit _ s) = PP.parens $ PP.text $ "StrLit " ++ show s

  pretty (UnExpr _ op exp) = PP.parens $ PP.hang (PP.text $ show op) 2 (pretty exp)
  pretty (BinExpr _ op a b) = PP.parens $ PP.hang (PP.text $ show op) 2 $ PP.sep [pretty a, pretty b]

  pretty (Field _ e field) = PP.parens $ PP.hang (PP.text "Field") 2 $ PP.sep [pretty e, PP.text $ show field]

  pretty (Index _ e ei) = PP.parens $ PP.hang (PP.text "Index") 2 $ PP.sep [pretty e, pretty ei]
  pretty (Tuple _ exps) = PP.parens $ PP.hang (PP.text "Tuple") 2 $ PP.sep (map pretty exps)
  pretty (Range _ a b c) = PP.parens $ PP.hang (PP.text "Range") 2 $
                           PP.hcat $ PP.punctuate (PP.text ":") [p a, p b, p c]
    where p Nothing = PP.text "Nothing"
          p (Just x) = pretty x

  pretty (Vec _ v e) = PP.parens $ PP.hang (PP.text "Vec") 4 $ PP.sep [pretty v PP.<+> PP.text "->", pretty e]
  pretty (Sigma _ v e) = PP.parens $ PP.hang (PP.text "Sigma") 6 $ PP.sep [pretty v PP.<+> PP.text "->", pretty e]
  pretty (For _ v e) = PP.parens $ PP.hang (PP.text "For") 4 $ PP.sep [pretty v PP.<+> PP.text "->", pretty e]

  pretty (App _ f args) = PP.parens $ PP.hang (pretty f) 2 $ PP.sep (map pretty args)

  pretty (SeqExpr _ args) = PP.parens $ PP.vcat $ PP.punctuate PP.semi (map pretty args)

  pretty (DefExpr _ a b) = PP.parens $ PP.hang (PP.text "Def") 2 $ PP.sep [pretty a, PP.text ":=", pretty b]
  pretty (StoreExpr _ a b) = PP.parens $ PP.hang (PP.text "Store") 2 $ PP.sep [pretty a, PP.text "<-", pretty b]
  
  --pretty x = error $ "pretty not implemented: " ++ show x

instance PP Arg where
  pretty (Arg _ a) = pretty a
  pretty (ImpArg _ a) = PP.braces $ pretty a

type Lexer = GenParser Char LexerState
data LexerState = LexerState {}

--runLexer :: String -- ^ Input file name
--            -> String -- ^ Input file contents
--            -> Either ParseError [Token]
--runLexer ifname input
--  = runParser lexer lexerState ifname input
--    where lexerState = LexerState {}

structFieldName = (:) <$> letter <*> many (alphaNum <|> char '_')

languageDef =
  emptyDef { Token.commentStart = "{-"
           , Token.commentEnd = "-}"
           , Token.commentLine = "--"
           , Token.nestedComments = True
           , Token.identStart = letter
           , Token.identLetter = alphaNum <|> oneOf "_'"
           , Token.opStart = mzero -- Token.opLetter languageDef
           , Token.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
           , Token.reservedOpNames = ["::", ":", "<-", "->", ":=", "~", "*", "-", "+", "/",
                                      "#", ".", "^T", "^", "$"]
           , Token.reservedNames = [
             "module", "function", "declare", "define", "extern", "static", "inline",
             "struct", "field",
             "vec", "in",
             "True", "False"
             ]
           , caseSensitive = True
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
lexeme = Token.lexeme lexer
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer
symbol = Token.symbol lexer
brackets = Token.brackets lexer
braces = Token.braces lexer
naturalOrFloat = Token.naturalOrFloat lexer
stringLiteral = Token.stringLiteral lexer
semi = Token.semi lexer
whiteSpace = Token.whiteSpace lexer

expr = store

-- Parse stores
store :: Parser Expr
store = do pos <- getPosition
           d <- tuple
           st pos d <|> def pos d <|> return d
  where st pos d = reservedOp "<-" >> (StoreExpr pos d <$> tuple)
        def pos d = reservedOp ":=" >> (DefExpr pos d <$> tuple)

-- Parse tuples
tuple :: Parser Expr
tuple = do pos <- getPosition
           ts <- tupleSep inExpr (reservedOp ",")
           case ts of
            Right v -> return v
            Left vs -> return $ Tuple pos vs
  where tupleSep p sep = do v <- p
                            vs <- many (try $ sep >> p)
                            trailing <- optionMaybe sep
                            if isNothing trailing && null vs
                              then return $ Right v
                              else return $ Left (v : vs)

inExpr :: Parser Expr
inExpr = do pos <- getPosition
            e <- range
            (reserved "in" >> (BinExpr pos In e <$> range)) <|> return e

range :: Parser Expr
range = noStart <|> withStart
  where noStart = do pos <- getPosition
                     reservedOp ":"
                     restRange pos Nothing
        withStart = do pos <- getPosition
                       t <- form
                       (reservedOp ":" >> restRange pos (Just t)) <|> return t
        restRange pos t = do end <- optionMaybe form
                             step <- optionMaybe (reservedOp ":" >> form)
                             return $ Range pos t end step

form :: Parser Expr
form = vecExpr <|> sigmaExpr <|> forExpr <|> ops
  where vecExpr = Vec <$> getPosition
                  <* reserved "vec" <*> expr <* reservedOp "->"
                  <*> expr
        sigmaExpr = Sigma <$> getPosition
                    <* reserved "sigma" <*> expr <* reservedOp "->"
                    <*> expr
        forExpr = For <$> getPosition
                    <* reserved "for" <*> expr <* reservedOp "->"
                    <*> expr


ops :: Parser Expr
ops = buildExpressionParser operators infixCarat

-- NB prefix operators at same precedence cannot appear together (like "-*x"; do "-(*x)")
operators = [ [ Postfix (flip UnExpr Transpose <$> getPosition <* lexeme (try $ string "^T")) ]
            , [ Prefix (un Deref "*") ]
            , [ Prefix (un Neg "-")
              , Prefix (un Pos "+")
              ]
            , [ Infix (bin Pow "^") AssocRight ]
            , [ Infix (bin Mul "*") AssocLeft
              , Infix (bin Div "/") AssocLeft
              ]
            , [ Infix (bin Concat "#") AssocLeft ]
            , [ Infix (bin Add "+") AssocLeft
              , Infix (bin Sub "-") AssocLeft
              ]
            ]
  where un op s = flip UnExpr op <$> getPosition <* reservedOp s
        bin op s = flip BinExpr op <$> getPosition <* reservedOp s

infixCarat :: Parser Expr
infixCarat = do e <- termMember
                return e
--                pos <- getPosition
--                (reservedOp "^"

termMember :: Parser Expr
termMember = term >>= doMember
  where doMember e = do pos <- getPosition
                        (brackets (Index pos e <$> expr) >>= doMember)
                          <|> (reservedOp "." >> (Field pos e <$> structFieldName) >>= doMember)
                          <|> return e

term :: Parser Expr
term = app

-- Parse application
app :: Parser Expr
app = do pos <- getPosition
         f <- term'
         args <- many parg
         case args of
          [] -> return f
          _ -> return $ App pos f args
  where parg = do pos <- getPosition
                  braces (ImpArg pos <$> expr) <|> (Arg pos <$> term')

-- Lowest lever parser for individual terms
term' :: Parser Expr
term' = ref <|> numlit <|> blit <|> slit <|> paren
  where ref = Ref <$> getPosition <*> identifier
        numlit = do pos <- getPosition
                    let w c = c pos Nothing
                    either (w IntLit) (w FloatLit) <$> naturalOrFloat
        blit = (BoolLit <$> getPosition <* reserved "True" <*> pure True)
               <|> (BoolLit <$> getPosition <* reserved "False" <*> pure False)
               <?> "boolean"
        slit = StrLit <$> getPosition <*> stringLiteral
        paren = do symbol "("
                   vlit <|> (mstatements <* symbol ")")
        vlit = symbol ")" >> VoidExpr <$> getPosition

mstatements :: Parser Expr
mstatements = do pos <- getPosition
                 xs <- sepEndBy1 expr (symbol ";")
                 case xs of
                  [x] -> return x
                  _ -> return $ SeqExpr pos xs

eparser = whiteSpace >> expr

parseString :: String -> Expr
parseString str =
  case parse eparser "*parseString*" str of
   Left e -> error $ show e
   Right r -> r
   
parseFile :: String -> IO Expr
parseFile file =
  do program <- readFile file
     case parse eparser file program of
      Left e -> print e >> fail "Parse error"
      Right r -> return r
