{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Plover.Quote
 ( pexp, ptop
 ) where
import Language.Plover.Parser
import Language.Plover.Convert
import Language.Plover.SemCheck
import Language.Plover.ErrorUtil
import Language.Plover.Unify
import Language.Plover.CodeGen (compileTopLevel, runCM)
import qualified Text.Show.Pretty as Pr  -- Pr.ppShow <$> (makeDefs <$> parseFile ...) >>= putStrLn
import qualified Text.PrettyPrint as PP
import qualified Text.PrettyPrint.Mainland as Mainland

import Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
--import Data.Typeable
--import Data.Data
import Text.Printf
import Control.Monad
import Control.Monad.Free
import Control.Applicative hiding (many, (<|>))
import Data.Maybe
import qualified Data.Map as M
import Language.Plover.ParserTypes
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Data.Tag
import Data.List
import Debug.Trace
import Data.Generics

import qualified Language.Haskell.Meta.Parse as MetaParse

import qualified Language.Plover.Types as T

pexp :: QuasiQuoter
pexp = QuasiQuoter
       { quoteExp = ploverQuoteExp expr
       , quotePat = ploverQuotePat expr
       , quoteType = error "No pexp type quasiquoter"
       , quoteDec = error "No pexp declaration quasiquoter"
       }

ptop :: QuasiQuoter
ptop = QuasiQuoter
       { quoteExp = ploverQuoteExp toplevel
       , quotePat = ploverQuotePat toplevel
       , quoteType = error "No ptop type quasiquoter"
       , quoteDec = error "No ptop declaration quasiquoter"
       }

ploverQuoteExp :: Parser Expr -> String -> Q Exp
ploverQuoteExp parser s =
  do loc <- TH.location
     let parser' = do setPosition
                        (newPos
                         (TH.loc_filename loc)
                         (fst $ TH.loc_start loc)
                         (snd $ TH.loc_start loc))
                      parser
     case parse parser' "" s of
      Left e -> do fail ("Parse error " ++ show e) --reportError $ show e
                   --fail "Parse error" --reportError (show e) >> fail "Parse error"
      Right r -> dataToExpQ (const Nothing `extQ` antiQuoteExp) r

ploverQuotePat :: Parser Expr -> String -> Q Pat
ploverQuotePat parser s =
  do loc <- TH.location
     let parser' = do setPosition
                        (newPos
                         (TH.loc_filename loc)
                         (fst $ TH.loc_start loc)
                         (snd $ TH.loc_start loc))
                      parser
     case parse parser' "" s of
      Left e -> do fail ("Parse error " ++ show e) --reportError $ show e
                   --fail "Parse error" --reportError (show e) >> fail "Parse error"
      Right r -> replacePExpr <$> dataToPatQ (const Nothing `extQ` antiQuotePat) r


antiQuoteExp :: Expr -> Maybe (Q Exp)
antiQuoteExp (PExpr _ (Antiquote str)) = Just $ case MetaParse.parseExp str of
                                                 Left err -> fail err
                                                 Right exp -> return exp
antiQuoteExp _ = Nothing

antiQuotePat :: Expr -> Maybe (Q Pat)
antiQuotePat (PExpr _ (Antiquote str)) = Just $ case MetaParse.parsePat str of
                                                 Left err -> fail err
                                                 Right pat -> return pat
antiQuotePat _ = Nothing

replacePExpr :: Pat -> Pat
replacePExpr pat = everywhere (extT id replacePExpr') pat
  where replacePExpr' :: Pat -> Pat
        replacePExpr' (ConP p [_, x]) | p == 'WithTag   = ConP 'WithTag [WildP, x]
        replacePExpr' x = x

-- runStuff fileName = do source <- readFile fileName
--                        case doParseToplevel (Right fileName) source of
--                         Left err -> putStrLn err
--                         Right expr -> 
--                          case makeDefs expr of
--                           Left err -> putStrLn (reportConvertErr (lines source) err)
--                           Right defs ->
--                             case doSemCheck $ defs of
--                              Left errs -> forM_ errs $ \err -> do
--                                putStrLn (reportSemErr (lines source) err)
--                              Right v -> do --putStrLn $ Pr.ppShow v
--                                            let cdefs = runCM (compileTopLevel v)
--                                            putStrLn "\n\nCompilation unit:\n"
--                                            putStrLn $ show $ Mainland.ppr cdefs
--   --                                                   return defs''putStrLn $ Pr.ppShow v


