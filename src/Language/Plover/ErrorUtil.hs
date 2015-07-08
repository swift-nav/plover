module Language.Plover.ErrorUtil where

import Text.ParserCombinators.Parsec
import System.IO.Error

showLineFromFile :: SourcePos -> IO String
showLineFromFile pos = case sourceName pos of
                        "*stdin*" -> return $ show pos ++ ":\n"
                        fileName -> catchIOError (do ls <- lines <$> readFile fileName
                                                     return $ showLine ls pos)
                                    (\err -> return $ show pos ++ ":\n")

-- | Gives a carat pointing to a position in a line in a source file
showLine :: [String] -- ^ the lines from the source file
         -> SourcePos
         -> String
showLine ls pos
  = show pos ++ ":\n"
    ++ line
  where line = if sourceLine pos <= length ls
               then ls !! (sourceLine pos - 1) ++ "\n" ++ errptr
               else "(end of file)\n"
        errptr = replicate (sourceColumn pos - 1) ' ' ++ "^"
