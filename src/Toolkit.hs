module Toolkit
    ( start
    ) where

import Translator
import Encapsulator
import Encapsulator.Extractor
import FMD
import Output

import System.Console.GetOpt
import System.IO hiding (withFile)
import System.Exit
import System.Environment
import Data.List
import Control.Monad

import Debug.Trace

data Flag = Help
          | Version
          | Format String
          | Rank String
          | Breadth String
          | NoEncaps
          | Heur1 String
          | Heur2 String
          | Att String
          -- Dev flags
          | Lex
          | Token String
          | Parse
          | Extract
          -- DUMMY
          | Dummy
          deriving (Eq,Ord,Show)

start :: IO ()
start = do
  (args, file) <- getArgs >>= parse
  mapM_ (mznsps args) file

mznsps :: [Flag] -> String -> IO ()
mznsps as f = do
  -- Flags
  token <- toToken as
  rank <- toRank as
  breadth <- toBreadth as
  format <- toFormat as
  (heur1, heur2) <- toHeur as
  att <- toAtt as

  -- Construction
  mzn <- readFile f
  let eTokens = lexString mzn
  case eTokens of
    Left err -> errMini [err] >> exitWith (ExitFailure 1)
    Right tokens -> when (Lex `elem` as)
                    $ print tokens
                    >> if token >= 0
                         then putStrLn $ show token ++ "-th token: "
                              ++ show (tokens !! token)
                         else putStrLn ""
  let Right tokens = eTokens
  let eCST = parseTokens tokens
  case eCST of
      Left err -> errMini [err] >> exitWith (ExitFailure 1)
      Right cst -> when (Parse `elem` as) $ print cst
  let Right cst = eCST
  let fmd1 = extractCST cst breadth heur1 att
  let (fmd2, mPredicate) = if NoEncaps `elem` as
                             then (fmd1, Nothing)
                             else Just <$> encapsulateFMD fmd1 (rank-1) heur2 att
  let output = case format of
                 0 -> "" -- none
                 1 -> produceMzn fmd2 cst mPredicate -- model
                 2 -> produceGraph fmd2 -- graph
                 3 -> undefined -- list

  -- Output
  putStrLn output

  -- Exit
  exitSuccess

printListRow :: [String] -> IO ()
printListRow [] = putStrLn ""
printListRow (x:xs) = putStrLn x >> printListRow xs

dfsPrint :: (Subformula a, Show a) => Environment -> Int -> [a] -> [String]
dfsPrint _ _ [] = []
dfsPrint bools i (x:xs) =
  let (children, env') = subformula x bools
  in [replicate (2*i) ' ' ++ show x] ++
     dfsPrint bools (i+1) children ++
     dfsPrint bools i xs

toToken :: [Flag] -> IO Int
toToken [] = return (-1) -- Default
toToken (Token n : _) =
  case reads n :: [(Int, String)] of
    [(i, "")] | i >=0 -> return i
    _ -> errShort ["invalid `--token' value.\n"]
      >> exitWith (ExitFailure 1)
toToken as = toToken $ tail as

toFormat :: [Flag] -> IO Int
toFormat [] = return 1 -- Default
toFormat (Format m : _) =
  case m of
    "none" -> return 0
    "model" -> return 1
    "graph" -> return 2 -- TODO keep?
    --"list" -> return 3 -- TODO keep?
    _ -> errShort ["invalid output format value.\n"]
      >> exitWith (ExitFailure 1)
toFormat as = toFormat $ tail as

toAtt :: [Flag] -> IO Int
toAtt [] = return 1 -- Default
toAtt (Att m : _) =
  case m of
    "optimism" -> return 0
    "pessimism" -> return 1
    "balanced" -> return 2
    _ -> errShort ["invalid attitude value.\n"]
      >> exitWith (ExitFailure 1)
toAtt as = toAtt $ tail as

toRank :: [Flag] -> IO Int
toRank [] = return 1 -- Default
toRank (Rank n : _) =
  case reads n :: [(Int, String)] of
   [(i, "")] | i > 0 -> return i
   _ -> errShort ["invalid rank value.\n"]
        >> exitWith (ExitFailure 1)
toRank as = toRank $ tail as

toBreadth :: [Flag] -> IO Int
toBreadth [] = return 3 -- Default
toBreadth (Breadth n : _) =
  case reads n :: [(Int, String)] of
   [(i, "")] | i >= 0 -> return i
   _ -> errShort ["invalid breadth value.\n"]
        >> exitWith (ExitFailure 1)
toBreadth as = toBreadth $ tail as

toHeur :: [Flag] -> IO (Int, Int)
toHeur fs = toHeur' fs (-1) (-1)

toHeur' :: [Flag] -> Int -> Int -> IO (Int, Int)
toHeur' [] (-1) (-1) = return (1, 1)
toHeur' [] h1 (-1) = return (h1, h1)
toHeur' [] h1 h2 = return (h1, h2)
toHeur' (Heur1 n : fs) _ h2 =
  case reads n :: [(Int, String)] of
   [(i, "")] | i >= 0 && i <= nHeuristics -> toHeur' fs i h2
   _ -> errShort ["invalid heur1 value.\n"]
        >> exitWith (ExitFailure 1)
toHeur' (Heur2 n : fs) h1 _ =
  case reads n :: [(Int, String)] of
   [(i, "")] | i >= 0 && i <= nHeuristics -> toHeur' fs h1 i
   _ -> errShort ["invalid heur2 value.\n"]
        >> exitWith (ExitFailure 1)
toHeur' as h1 h2 = toHeur' (tail as) h1 h2

flags :: [OptDescr Flag]
flags =
   [Option ['h'] ["help"] (NoArg Help)
    "Display this information."
   ,Option [] ["version"] (NoArg Version)
    "Display version information."
   ,Option ['f'] ["format"] (ReqArg Format "f")
    "The output format to use can be one of either:\n  model (default): Output a MiniZinc model.\n  list: Show a list of the best candidates for\n        encapsulation according to the chosen\n        heuristics.\n  graph: Output the FMD in xdot format. \n  none: No output."
   ,Option ['r'] ["rank"] (ReqArg Rank "r")
    "Encapsulate the r-th best encapsulation.\n(default is 1)"
   ,Option ['s'] ["breadth"] (ReqArg Breadth "s")
    "Consider up to s abstractions when constructing the FMD.\n(default is 3)"
   ,Option [] ["no-encaps"] (NoArg NoEncaps)
    "Skip the encapsulation phase."
   ,Option [] ["heur1"] (ReqArg Heur1 "h")
    "Use the h-th heuristic (see above for details) when\ngenerating the FMD. (default is 1)."
   ,Option [] ["heur2"] (ReqArg Heur2 "h")
    "Use the h-th heuristic (see above for details) when\nchoosing candidate to encapsulate in the FMD.\n(default is same as heur1)"
   ,Option [] ["att"] (ReqArg Att "a")
    "Use attitude a when comparing heuristic values. Can be one of either:\n  optimism\n  pessimism\n  balanced (default)"

   ,Option [] [] (NoArg Dummy) "\n--- DEV OPTIONS ---\n\n"
   ,Option [] ["lex"] (NoArg Lex)
    "Show the output of the lexer in\nreadable format."
   ,Option [] ["token"] (ReqArg Token "i")
    "Show the i-th token in the token string,\nrequires --lex."
   ,Option [] ["parse"] (NoArg Parse)
    "Show the output of the parser in\nreadable (and parse-able) format."
--   ,Option [] ["extract"] (NoArg Extract)
--    "Show the output of the extractor in\nreadable format."
   ]

parse :: [String] -> IO ([Flag], [String])
parse argv = case getOpt Permute flags argv of
  (args,fs,[]) -> do
    when (Help `elem` args) $ errLong []
      >> exitSuccess
    when (Version `elem` args) $ putStrLn versionInfo
      >> exitSuccess
    when (null fs) $ errShort ["no input file(s)\n"]
      >> exitWith (ExitFailure 1)

    return (nub (concatMap set args), fs)

  (_,_,errs) -> errLong errs >> exitWith (ExitFailure 1)
  where set f = [f]

errLong :: [String] -> IO ()
errLong errs = hPutStrLn stderr (concat errs ++ usageInfo header flags ++ heurInfo)

errShort :: [String] -> IO ()
errShort errs = do
  name <- getProgName
  hPutStrLn stderr (concat errs ++
                    "Try `" ++ name ++ " --help' for more information.\n")

errMini :: [String] -> IO ()
errMini errs = hPutStrLn stderr $ concat errs ++ "\n"

header :: String
header = "\
\usage: analysis-tool-exe [options] file...\n\
\  file: MiniZinc model to analyse.\n\
\\n\
\options:"

nHeuristics :: Int
nHeuristics = 8

heurInfo :: String
heurInfo = "\
\\n\
\base heuristics: (read documentation for more information)\n\
\  0  Order of occurence\n\
\  1  Argument Modesty Heuristic\n\
\  2  Argument Significance Heurisic\n\
\  3  Objective Function Heuristic\n\
\  4  Local Variable Heuristic\n\
\  5  (Unimplemented) Solution Modesty Heuristic\n\
\  6  Multi-encapsulation Heuristic\n\
\\n\
\  7  Mix I Heuristic\n\
\  8  Mix II Heuristic\n\
\\n\
\attitudes:\n\
\  optimism   (compare lower bounds)\n\
\  pessimism  (compare upper bounds)\n\
\  balanced   ()?\n"

versionInfo :: String
versionInfo = "\
\version info"

nicePrint :: Show a => a -> IO ()
nicePrint x = putStrLn ("\n" ++ show x ++ "\n")
