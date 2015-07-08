module Language.Plover.Compile where

import qualified Language.Plover.Parser as Parser
import qualified Language.Plover.Convert as Convert
import qualified Language.Plover.ParserTypes as PT
import qualified Language.Plover.Types as T
--import Language.Plover.ErrorUtil
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos

doParseToplevel :: Either SourcePos String -> String -> Either String PT.Expr
doParseToplevel posOrFilename source = case parse parser' filename source of
                                        Left err -> Left $ Parser.reportErr (lines source) err
                                        Right expr -> Right $ expr
  where parser' = case posOrFilename of
                   Left pos -> setPosition pos >> Parser.toplevel
                   Right _ -> Parser.toplevel
        filename = case posOrFilename of
                    Left pos -> sourceName pos
                    Right fn -> fn

doConvert :: String -> PT.Expr -> Either String [T.DefBinding]
doConvert source expr = case Convert.makeDefs expr of
                         Left err -> Left $ Convert.reportConvertErr (lines source) err
                         Right defs -> Right defs
