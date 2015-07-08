module Language.Plover.CLI
       (CompilerOpts(..), TargetFlag(..), hasOptFlag, compilerOpts)
       where

import System.Console.GetOpt
import System.Exit
import qualified Data.Set as S
import Data.Maybe
import Data.List

data CompilerOpts
  = CompilerOpts
    { inputFiles :: [String]
    , unitName :: Maybe String
    , target :: TargetFlag
    , debugMode :: Bool
    , helpMode :: Bool
    , optMode :: OptFlags
    } deriving (Show)

data TargetFlag = TargetParse
                | TargetConvert
                | TargetTypeCheck
                | TargetCodeGen
                | TargetDefault
                deriving (Show, Eq)

type OptFlags = S.Set String

defaultOptions :: CompilerOpts
defaultOptions = CompilerOpts
                 { inputFiles = []
                 , unitName = Nothing
                 , target = TargetDefault
                 , debugMode = False
                 , helpMode = False
                 , optMode = defaultOptFlags
                 }

defaultOptFlags :: OptFlags
defaultOptFlags = S.empty

hasOptFlag :: String -> OptFlags -> Bool
hasOptFlag name opts = name `S.member` opts

optimizations :: [(String, String)]
optimizations =
  [
    ("test", "A placeholder optimization")
  ]

optimizationClasses =
  [ ("all", map fst optimizations) ]

showOptimizations :: String
showOptimizations = unlines $ map showOpt optimizations
  where maxnamelength = maximum $ map (length . fst) optimizations
        showOpt (name, desc) = replicate (maxnamelength - length name) ' '
                               ++ name ++ " : " ++ desc

showOptClasses :: String
showOptClasses = "\n Optimization classes which can be passed to --opt:\n"
                 ++ (unlines $ map showOptClass optimizationClasses)
  where maxnamelength = max 10 (maximum $ map (length . fst) optimizationClasses)
        showOptClass (name, opts) = replicate (maxnamelength - length name) ' '
                                    ++ name ++ " : " ++ optlist opts
        optlist opts = prelines $ map (intercalate " ") $ intoFive opts
        prelines = intercalate ("\n   " ++ replicate maxnamelength ' ')
        intoFive :: [a] -> [[a]]
        intoFive list | null list = []
                      | length list < 5 = [list]
                      | otherwise = let (xs, ys) = splitAt 5 list
                                    in xs:(intoFive ys)

options :: [OptDescr (CompilerOpts -> CompilerOpts)]
options =
  [ Option ['o'] ["out"] (ReqArg unitName' "NAME")  "Output unit NAME"
  , Option ['t'] ["target"] (ReqArg target' "TARGET") ("Set target type:\n" ++
                                                       "\t     parse : Parses the input file\n" ++
                                                       "\t   convert : Converts the input file to core\n" ++
                                                       "\t typecheck : Typechecks the file\n" ++
                                                       "\t   codegen : Outputs the generated C" )
  , Option ['d'] ["debug"] (NoArg debug') "Enables debug mode"
  , Option ['h'] ["help"] (NoArg help') "Prints this usage information"
  , Option ['O'] ["opt"] (ReqArg optimize' "OPTIMIZATION") ("Enables optimizations:\n"
                                                            ++ showOptimizations
                                                            ++ "\nPrefixing an optimization with '-' disables it."
                                                            ++ "\nall/none enables/disables ALL optimizations.")
  ]
  where unitName' s opts = opts { unitName = Just s }
        target' t opts = opts { target = targetOpt t }
        debug' opts = opts { debugMode = True }
        help' opts = opts { helpMode = True }
        optimize' t opts
          = opts { optMode = foldl (flip id) (optMode opts)
                             [optOpt p | p <- splitOn ',' t] }
        splitOn :: Char -> String -> [String]
        splitOn delim = foldr split' [""]
          where split' c l@(x:xs) | c == delim  = []:l
                                  | otherwise   = (c:x):xs

targetOpt :: String -> TargetFlag
targetOpt s = case s of
  "parse" -> TargetParse
  "convert" -> TargetConvert
  "typecheck" -> TargetTypeCheck
  "codegen" -> TargetCodeGen
  _ -> TargetDefault

optOpt :: String -> OptFlags -> OptFlags
optOpt s opts = case s of
                 "none" -> S.empty
                 '-':name -> opts S.\\ optLookup name
                 name -> opts `S.union` optLookup name
  where optLookup name = case lookup name optimizationClasses of
                          Just s -> S.fromList s
                          Nothing -> case lookup name optimizations of
                                      Just _ -> S.singleton name
                                      Nothing -> S.empty

-- | Takes an argument list and gives a 'CompilerOpts'.  If there is a
-- parse error or help request, this function uses 'System.Exit' to
-- halt the entire program.
compilerOpts :: [String] -> IO CompilerOpts
compilerOpts argv = case getOpt argorder options argv of
                     (o,_,[]) -> let opts = foldl (flip id) defaultOptions o
                                 in case helpMode opts of
                                     True -> do putStr $ usageInfo header options
                                                putStr $ showOptClasses
                                                exitSuccess
                                     False -> return opts
                     (_,_,errs) -> do putStr (concat errs ++ usageInfo header options)
                                      exitWith $ ExitFailure 1
  where header = "Usage: plover [OPTIONS...] sources"
        argorder = ReturnInOrder (\s opts -> opts { inputFiles = inputFiles opts ++ [s] })
