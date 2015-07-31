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
    , hFilePrefix :: Maybe String
    , cFilePrefix :: Maybe String
    , libPrefix :: Maybe String
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
                 , hFilePrefix = Nothing
                 , cFilePrefix = Nothing
                 , libPrefix = Nothing
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
  , Option [] ["cdir"] (ReqArg cFilePrefix' "DIR")
      "Directory to place generated .c files."
  , Option [] ["hdir"] (ReqArg hFilePrefix' "DIR")
      "Directory to place generated .h files."
  , Option [] ["libprefix"] (ReqArg libPrefix' "STRING")
      "Library prefix to prefix includes with"
  , Option ['t'] ["target"] (ReqArg target' "TARGET")
      ("Set target type:\n" ++
       "\t     parse : Parses the input file\n" ++
       "\t   convert : Converts the input file to core\n" ++
       "\t typecheck : Typechecks the file\n" ++
       "\t   codegen : Outputs the generated C" )
  , Option ['d'] ["debug"] (NoArg debug') "Enables debug mode"
  , Option ['h'] ["help"] (NoArg help') "Prints this usage information"
  , Option ['O'] ["opt"] (ReqArg optimize' "OPTIMIZATION")
      ("Enables optimizations:\n"
       ++ showOptimizations
       ++ "\nPrefixing an optimization with '-' disables it."
       ++ "\nall/none enables/disables ALL optimizations.")
  ]
  where unitName' s opts = opts { unitName = Just s }
        cFilePrefix' s opts = opts { cFilePrefix = Just s }
        hFilePrefix' s opts = opts { hFilePrefix = Just s }
        libPrefix' s opts = opts { libPrefix = Just s }
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
                                 in do
                                   mapM_ (doHandler opts) optionHandlers
                                   return opts
                     (_,_,errs) -> do putStr (concat errs ++ usageInfo usageHeader options)
                                      exitWith $ ExitFailure 1
  where
        argorder = ReturnInOrder (\s opts -> opts { inputFiles = inputFiles opts ++ [s] })


-- Option handling stuff
type OptionChecker = (CompilerOpts -> Bool, IO ())

usageHeader :: String
usageHeader = "Usage: plover [OPTIONS...] sources"

doHandler :: CompilerOpts -> OptionChecker -> IO ()
doHandler opts (p, m) = if p opts then m else return ()

implies :: Bool -> Bool -> Bool
implies a b = not a || b

equiv :: Bool -> Bool -> Bool
equiv a b = implies a b && implies b a

badO :: CompilerOpts -> Bool
badO opts = not $ and
  [ (isJust (cFilePrefix opts) `equiv` isJust (hFilePrefix opts))
  , (isJust (cFilePrefix opts) `implies` isJust (unitName opts))]

optionHandlers :: [OptionChecker]
optionHandlers =
  [ (helpMode, printHelpMode)
  , (badO, printError "c_output and h_output options must accompany each other and require the --out option.")
  ]

printError :: String -> IO ()
printError str = do
  putStrLn $ "Error: " ++ str
  exitWith $ ExitFailure 1

printHelpMode :: IO ()
printHelpMode = do
    putStr $ usageInfo usageHeader options
    putStr $ showOptClasses
    exitSuccess
