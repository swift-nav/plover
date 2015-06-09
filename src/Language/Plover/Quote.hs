{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

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
import Control.Monad.Free
import Control.Applicative hiding (many, (<|>))
import Data.Maybe
import Language.Plover.QuoteTypes

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
                      toplevel
     case parse parser' "" s of
      Left e -> do fail ("Parse error " ++ show e) --reportError $ show e
                   --fail "Parse error" --reportError (show e) >> fail "Parse error"
      Right r -> return undefined

type Lexer = GenParser Char LexerState
data LexerState = LexerState {}

--runLexer :: String -- ^ Input file name
--            -> String -- ^ Input file contents
--            -> Either ParseError [Token]
--runLexer ifname input
--  = runParser lexer lexerState ifname input
--    where lexerState = LexerState {}

structFieldName = (:) <$> letter <*> many (alphaNum <|> char '_') <* whiteSpace

languageDef =
  emptyDef { Token.commentStart = "{-"
           , Token.commentEnd = "-}"
           , Token.commentLine = "--"
           , Token.nestedComments = True
           , Token.identStart = letter <|> oneOf "_"
           , Token.identLetter = alphaNum <|> oneOf "_'"
           , Token.opStart = mzero -- Token.opLetter languageDef
           , Token.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
           , Token.reservedOpNames = ["::", ":", "<-", "->", ":=", "~", "*", "-", "+", "/",
                                      "#", ".", ".*", "^", "$"]
           , Token.reservedNames = [
             "module", "function", "declare", "define", "extern", "static", "inline",
             "struct", "field",
             "vec", "for", "sigma", "in",
             "True", "False", "Void", "T", "_",
             "array"
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


withPos :: Parser (Expr' Expr) -> Parser Expr
withPos p = do pos <- getPosition
               v <- p
               return $ wrapPos pos v

-- Expression parser
expr :: Parser Expr
expr = store

-- Parse stores
store :: Parser Expr
store = do pos <- getPosition
           d <- tuple
           st pos d <|> def pos d <|> return d
  where st pos d = reservedOp "<-" >> (wrapPos pos . StoreExpr d <$> tuple)
        def pos d = reservedOp ":=" >> (wrapPos pos . DefExpr d <$> tuple)

-- Parse tuples
tuple :: Parser Expr
tuple = do pos <- getPosition
           ts <- tupleSep range (reservedOp ",")
           case ts of
            Right v -> return v
            Left vs -> return $ wrapPos pos $ Tuple vs
  where tupleSep p sep = do v <- p
                            vs <- many (try $ sep >> p)
                            trailing <- optionMaybe sep
                            if isNothing trailing && null vs
                              then return $ Right v
                              else return $ Left (v : vs)

range :: Parser Expr
range = noStart <|> withStart
  where noStart = do pos <- getPosition
                     reservedOp ":"
                     restRange pos Nothing
        withStart = do pos <- getPosition
                       t <- operators
                       (reservedOp ":" >> restRange pos (Just t)) <|> return t
        restRange pos t = do end <- optionMaybe operators
                             step <- optionMaybe (reservedOp ":" >> operators)
                             return $ wrapPos pos $ Range t end step

operators :: Parser Expr
operators = buildExpressionParser ops application
  where
    -- NB prefix operators at same precedence cannot appear together (like "-*x"; do "-(*x)")
    ops = [ [ Prefix (un Deref "*")
            ]
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
          , [ Infix dollar AssocRight ] -- TODO Should this be a real operator? or is App suff.?
          , [ Infix (bin Type "::") AssocNone ]
          ]
    un op s = do pos <- getPosition
                 reservedOp s
                 return $ wrapPos pos . UnExpr op
    bin op s = do pos <- getPosition
                  reservedOp s
                  return $ (wrapPos pos .) . BinExpr op
    dollar = do pos <- getPosition
                reservedOp "$"
                return $ \x y -> wrapPos pos $ App x [Arg y]

-- Parse a sequence of terms as a function application
application :: Parser Expr
application = do pos <- getPosition
                 f <- term
                 args <- many parg
                 case args of
                  [] -> return f -- so not actually a function application
                  _ -> return $ wrapPos pos $ App f args
  where parg = braces (ImpArg <$> expr) <|> (Arg <$> term)

term :: Parser Expr
term = literal >>= doMember
  where doMember e = do pos <- getPosition
                        (brackets (wrapPos pos . Index e <$> expr) >>= doMember)
                          <|> (reservedOp ".*" >> (wrapPos pos . FieldDeref e <$> structFieldName)
                               >>= doMember)
                          <|> (reservedOp "." >> (wrapPos pos . Field e <$> structFieldName)
                               >>= doMember)
                          <|> return e

-- Parse a literal or parenthesis group
literal :: Parser Expr
literal = voidlit <|> holelit <|> transposelit <|> numlit <|> binlit <|> strlit
          <|> ref <|> parenGroup
          <|> veclit <|> form
  where ref = withPos $ Ref <$> identifier
        voidlit = withPos $ reserved "Void" >> return VoidExpr
        holelit = withPos $ reserved "_" >> return Hole
        transposelit = withPos $ reserved "T" >> return T
        numlit = withPos $ either integer float <$> naturalOrFloat
        binlit = withPos $ do
          b <- ((reserved "True" >> return True)
                <|> (reserved "False" >> return False))
               <?> "boolean"
          return $ BoolLit b
        strlit = withPos $ StrLit <$> stringLiteral
        parenGroup = symbol "(" *> mstatements <* symbol ")"
        veclit = -- basically match tuple. TODO better vec literal?
          withPos $ do
            try (reserved "vec" >> symbol "(")
            xs <- sepEndBy range (symbol ",")
            symbol ")"
            return $ VecLit xs


form :: Parser Expr
form = iter Vec "vec" <|> iter Sigma "sigma" <|> iter For "for"
  where iter cons s = withPos $ do
          reserved s
          vs <- sepBy ((,) <$> identifier <* reserved "in" <*> range) (symbol ",")
          reservedOp "->"
          cons vs <$> expr

-- Parse semicolon-separated sequenced statements
mstatements :: Parser Expr
mstatements = do pos <- getPosition
                 xs <- sepEndBy1 expr (symbol ";")
                 case xs of
                  [x] -> return x -- so no need to sequence
                  _ -> return $ wrapPos pos $ SeqExpr xs

toplevelStatement :: Parser Expr
toplevelStatement = extern <|> struct <|> expr
  where extern = withPos $ do reserved "extern"
                              x <- toplevelStatement
                              return $ Extern x
        struct = withPos $ do reserved "struct"
                              name <- identifier
                              xs <- parens $ sepEndBy1 expr (symbol ";")
                              return $ Struct name xs


-- Parse entire toplevel
toplevel :: Parser Expr
toplevel = do whiteSpace
              withPos $ SeqExpr <$> sepEndBy toplevelStatement (symbol ";") <* eof

parseString :: String -> Expr
parseString str =
  case parse toplevel "*parseString*" str of
   Left e -> error $ show e
   Right r -> r
   
parseFile :: String -> IO Expr
parseFile file =
  do program <- readFile file
     case parse toplevel file program of
      Left e -> print e >> fail "Parse error"
      Right r -> return r
