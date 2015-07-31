module Language.Plover.Parser
       where

import Language.Plover.ParserTypes
import Language.Plover.ErrorUtil
import Control.Monad
import Control.Applicative ((<$>), (<*>), (<*))
import Data.Tag
import Data.Maybe
import Data.List
import qualified Data.Map as M
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

type Lexer = GenParser Char LexerState
data LexerState = LexerState {}

languageDef =
  emptyDef { Token.commentStart = "{-"
           , Token.commentEnd = "-}"
           , Token.commentLine = "--"
           , Token.nestedComments = True
           , Token.identStart = letter <|> oneOf "_"
           , Token.identLetter = alphaNum <|> oneOf "_'"
           , Token.opStart = mzero -- Token.opLetter languageDef   -- No opStart because all operators are reserved
           , Token.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
           , Token.reservedOpNames = ["::", ":", "..", "<-", "->", ":=", "~", "*", "-", "+", "/", ".*", "&",
                                      "#", ".", "^", "$", "==", "!=", "<", "<=", ">", ">="]
           , Token.reservedNames = [
             "module", "function", "declare", "define", "extern", "static", "inline",
             "struct", "type",
             "vec", "for", "sum", "in", "if", "then", "else",
             "True", "False", "Void", "T", "_",
             "array", "and", "or", "not",
             "storing",
             "return", "assert"
             ]
           , caseSensitive = True
           }

-- | A map of reserved operator names to lists of operators it
-- prefixes (with the shared part dropped).  This is for our version
-- of 'reservedOp'.
reservedOpPrefixes :: M.Map String [String]
reservedOpPrefixes = M.fromList [(name, [rop
                                        | rop <- Token.reservedOpNames languageDef,
                                          isPrefixOf name rop,
                                          name /= rop])
                                | name <- Token.reservedOpNames languageDef]

getReservedOpPrefixes :: String -> [String]
getReservedOpPrefixes name = case M.lookup name reservedOpPrefixes of
                              Just lst -> lst
                              Nothing -> error $ "In getReservedOpPrefixes: the operator "
                                         ++ show name ++ " is not in the reserved operator list."

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
lexeme = Token.lexeme lexer
reserved = Token.reserved lexer
-- | Rather than 'Token.reservedOp lexer', we make the reservedOp
-- parser a little smarter for our needs (since, unlike Haskell, we do
-- not support arbitrary user-specified operators).  In particular, it
-- will match 'name' if it is not the prefix of another reserved
-- operator which could also be parsed here.
reservedOp name = lexeme $ try $ do
  lookAhead $ string name
  mapM_ (notFollowedBy . string) (getReservedOpPrefixes name) <?> show name
  string name
  return ()
parens = Token.parens lexer
symbol = Token.symbol lexer
brackets = Token.brackets lexer
braces = Token.braces lexer
naturalOrFloat = Token.naturalOrFloat lexer
stringLiteral = Token.stringLiteral lexer
semi = Token.semi lexer
whiteSpace = Token.whiteSpace lexer


structFieldName = (:) <$> letter <*> many (alphaNum <|> char '_') <* whiteSpace

-- | Records the current parser position, runs a parser, then wraps
-- the result with a tag as a position.
withPos :: Parser (Expr' Expr) -> Parser Expr
withPos p = do pos <- getPosition
               v <- p
               return $ newTag pos v


-- Expression parser
-- <expr> ::= <store>
expr :: Parser Expr
expr = whiteSpace >> store

-- Parse stores and definitions
-- <store> ::= <tuple> [("<-" | ":=") <store>]
store :: Parser Expr
store = do pos <- getPosition
           d <- tuple
           st pos d <|> def pos d <|> return d
  where st pos d = reservedOp "<-" >> (wrapPos pos . StoreExpr d <$> store)
        def pos d = reservedOp ":=" >> (wrapPos pos . DefExpr d <$> store)

-- Parse tuples.  Trailing comma is tolerated, and enables 1-tuples
-- <tuple> ::= <range> ("," <range>)* [","]
tuple :: Parser Expr
tuple = do pos <- getPosition
           ts <- tupleSep range (symbol ",")
           case ts of
            Right v -> return v
            Left vs -> return $ wrapPos pos $ Tuple vs
  where tupleSep p sep = do v <- p
                            vs <- many (try $ sep >> p)
                            trailing <- optionMaybe sep
                            if isNothing trailing && null vs
                              then return $ Right v
                              else return $ Left (v : vs)

-- <range> ::= ":" [<typeSpec>] [":" <typeSpec>]
--           | <typeSpec> [":" [<typeSpec>] [":" <typeSpec>]]
--           | ".." [<typespec>] [":" <typeSpec>]
--           | <typespec> [".." [<typespec>] [":" <typespec>]]
-- (note that the colons must have a space between them, otherwise it is a typeSpec)
range :: Parser Expr
range = noStart1 <|> noStart2 <|> withStart
  where noStart1 = do pos <- getPosition
                      reservedOp ":"
                      restRange1 pos Nothing
        withStart = do pos <- getPosition
                       t <- typeSpec
                       (reservedOp ":" >> restRange1 pos (Just t))
                         <|> (reservedOp ".." >> restRange2 pos (Just t))
                         <|> return t
        restRange1 pos t = do end <- optionMaybe typeSpec
                              step <- optionMaybe (reservedOp ":" >> typeSpec)
                              return $ wrapPos pos $ Range t end step
        noStart2 = do pos <- getPosition
                      reservedOp ".."
                      restRange2 pos Nothing
        restRange2 pos t = do end <- optionMaybe typeSpec
                              step <- optionMaybe (reservedOp ":" >> typeSpec)
                              return $ wrapPos pos $ Range t ((+ fromMaybe 1 step) <$> end) step

-- This is hand-coded to make a common error have a better error
-- message.
-- <typeSpec> ::= <operators> ["::" <operators>]
typeSpec :: Parser Expr
typeSpec = do pos <- getPosition
              a <- operators
              ty pos a <|> return a
  where ty pos a = do reservedOp "::"
                      wrapPos pos . BinExpr Type a <$> operators

operators :: Parser Expr
operators = buildExpressionParser ops application
  where
    -- NB prefix operators at same precedence cannot appear together (like "-*x"; do "-(*x)")
    ops = [ [ Prefix (un Deref (reservedOp "*"))
            , Prefix (un Addr (reservedOp "&"))
            ]
          , [ Infix (bin Pow (reservedOp "^")) AssocRight ] -- TODO how to deal with -x^y and x^-y both properly
          , [ Infix (bin Mul (reservedOp "*")) AssocLeft
            , Infix (bin Div (reservedOp "/")) AssocLeft
            , Infix (bin Hadamard (reservedOp ".*")) AssocLeft
            ]
          , [ Prefix (un Neg (reservedOp "-"))
            , Prefix (un Pos (reservedOp "+"))
            ]
          , [ Infix (bin Add (reservedOp "+")) AssocLeft
            , Infix (bin Sub (reservedOp "-")) AssocLeft
            ]
          , [ Infix (bin Concat (reservedOp "#")) AssocLeft ]
          , [ Infix (bin EqualOp (reservedOp "==")) AssocNone
            , Infix (bin NEqOp (reservedOp "!=")) AssocNone
            , Infix (bin LTOp (reservedOp "<")) AssocNone
            , Infix (bin LTEOp (reservedOp "<=")) AssocNone
            , Infix (fmap flip $ bin LTOp (reservedOp ">")) AssocNone
            , Infix (fmap flip $ bin LTEOp (reservedOp ">=")) AssocNone
            ]
          , [ Prefix (un Not (reserved "not")) ]
          , [ Infix (bin And (reserved "and")) AssocLeft ]
          , [ Infix (bin Or (reserved "or")) AssocLeft ]
          , [ Infix dollar AssocRight ] -- TODO Should this be a real operator? or is App suff.?
          , [ Infix (bin Storing (reserved "storing")) AssocNone ]
          ]
    un op s = do pos <- getPosition
                 s
                 return $ wrapPos pos . UnExpr op
    bin op s = do pos <- getPosition
                  s
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
                          <|> (reservedOp "." >> (wrapPos pos . Field e <$> structFieldName)
                               >>= doMember)
                          <|> return e

-- Parse a literal or parenthesis group
literal :: Parser Expr
literal = voidlit <|> holelit <|> transposelit <|> numlit <|> binlit <|> strlit
          <|> ref <|> parenGroup
          <|> veclit <|> form <|> antiquote
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
        parenGroup = do pos <- getPosition
                        symbol "("
                        (symbol ")" >> (return $ wrapPos pos VoidExpr))
                          <|> (mstatements <* symbol ")")
        veclit = -- basically match tuple. TODO better vec literal?
          withPos $ do
            try (reserved "vec" >> symbol "(")
            xs <- sepEndBy range (symbol ",")
            symbol ")"
            return $ VecLit xs

antiquote = do reservedOp "~"
               idAntiquote <|> parens exprAntiquote
  where idAntiquote = withPos $ Antiquote <$> identifier
        exprAntiquote = withPos $ Antiquote <$> balanced
        balanced :: Parser String
        balanced = do before <- many $ noneOf "()"
                      during <- join <$> (many $ ((\x -> "(" ++ x ++ ")") <$> parens balanced))
                      after <- many $ noneOf "()"
                      return $ before ++ during ++ after

form :: Parser Expr
form = iter Vec "vec" <|> iter Sum "sum" <|> iter For "for" <|> ifexpr <|> retexp <|> assertexp
  where iter cons s = withPos $ do
          reserved s
          vs <- sepBy ((,) <$> identifier <* reserved "in" <*> range) (symbol ",")
          reservedOp "->"
          cons vs <$> expr
        ifexpr = withPos $ do
          reserved "if"
          cond <- expr
          reserved "then"
          cons <- expr
          elseexpr cond cons <|> (do pos <- getPosition
                                     return $ If cond cons (wrapPos pos $ VoidExpr))
        elseexpr cond cons = do
          reserved "else"
          alt <- expr
          return $ If cond cons alt

        retexp = withPos $ do
          reserved "return"
          ex <- expr <|> withPos (return VoidExpr)
          return $ Return ex
        assertexp = withPos $ do
          reserved "assert"
          Assert <$> expr

-- Parse semicolon-separated sequenced statements
mstatements :: Parser Expr
mstatements = do pos <- getPosition
                 xs <- sepEndBy1 expr (symbol ";")
                 case xs of
                  [x] -> return x -- so no need to sequence
                  _ -> return $ wrapPos pos $ SeqExpr xs

toplevelStatement :: Parser Expr
toplevelStatement = extern <|> static <|> struct <|> typedef <|> expr
  where extern = withPos $ do reserved "extern"
                              x <- toplevelStatement
                              return $ Extern x
        static = withPos $ do reserved "static"
                              x <- toplevelStatement
                              return $ Static x
        struct = withPos $ do reserved "struct"
                              name <- identifier
                              xs <- parens $ sepEndBy1 expr (symbol ";")
                              return $ Struct name xs
        typedef = withPos $ do reserved "type"
                               name <- identifier
                               reservedOp ":="
                               ty <- expr
                               return $ Typedef name ty


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




reportErr :: ParseError
          -> IO String
reportErr err
  = do sl <- showLineFromFile (errorPos err)
       return $ "Parse error at " ++ sl
         ++ (showErrorMessages
             "or" "unknown parse error"
             "expecting" "unexpected" "end of input"
             (errorMessages err)) ++ "\n"
