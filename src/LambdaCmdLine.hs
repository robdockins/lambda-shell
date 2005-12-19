module LambdaCmdLine 
( lambdaCmdLine
) where

import Numeric
import Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map
import System.IO
import System.Exit
import System.Console.GetOpt
import Text.ParserCombinators.Parsec (parse)

import Lambda
import LambdaParser
import LambdaShell
import Version

-----------------------------------------------------------------------
-- Main entry point for the command line tool

-- | Parse command line options and run the lambda shell
lambdaCmdLine :: [String] -> IO ()
lambdaCmdLine argv =
   do st <- parseCmdLine argv
      if (cmd_help st)
         then putStrLn (printUsage usageNotes)
         else if (cmd_version st) 
                 then putStrLn versionInfo
                 else doCmdLine st


doCmdLine :: LambdaCmdLineState -> IO ()
doCmdLine st =
   case (cmd_input st) of
       Just expr -> evalInput st expr
       Nothing -> 
           if (cmd_stdin st)
              then evalStdin st
              else runShell st


--------------------------------------------------------------
-- Holds important values parsed from the command line

data LambdaCmdLineState
   = LambdaCmdLineState
     { cmd_unfold  :: Bool
     , cmd_stdin   :: Bool
     , cmd_input   :: Maybe String
     , cmd_binds   :: Bindings () String
     , cmd_help    :: Bool
     , cmd_version :: Bool
     , cmd_trace   :: Maybe (Maybe Int)
     , cmd_red     :: RS
     }

initialCmdLineState =
  LambdaCmdLineState
  { cmd_unfold  = False
  , cmd_stdin   = False
  , cmd_input   = Nothing
  , cmd_binds   = Map.empty
  , cmd_help    = False
  , cmd_version = False
  , cmd_trace   = Nothing
  , cmd_red     = lamReduceNF
  }


-------------------------------------------------------------
-- Set up the command line options

data LambdaCmdLineArgs
  = FullUnfold
  | ReadStdIn
  | Program String
  | Trace (Maybe String)
  | PrintUsage
  | PrintVersion
  | Reduction String


options :: [OptDescr LambdaCmdLineArgs]
options = 
  [ Option ['u']     ["unfold"]      (NoArg FullUnfold)             "perform full unfolding of let-bound terms"
  , Option ['s']     ["stdin"]       (NoArg ReadStdIn)              "read from standard in"
  , Option ['e']     ["program"]     (ReqArg Program "PROGRAM")     "evaluate statements from command line"
  , Option ['r']     ["trace"]       (OptArg Trace "TRACE_NUM")     "set tracing (and optional trace display length)"
  , Option ['h','?'] ["help"]        (NoArg PrintUsage)             "print this message"
  , Option ['v']     ["version"]     (NoArg PrintVersion)           "print version information"
  , Option ['t']     ["strategy"]    (ReqArg Reduction "REDUCTION_STRATEGY")
           "set the reduction strategy (one of whnf, hnf, nf, strict)"
  ]



-----------------------------------------------------------------
-- Parser for the command line

parseCmdLine :: [String] -> IO LambdaCmdLineState
parseCmdLine argv = 
   case getOpt RequireOrder options argv of
     (opts,files,[]) -> (foldl (>>=) (return initialCmdLineState) $ map applyFlag opts) >>= \st ->
                        (foldl (>>=) (return st)                  $ map loadDefs files)

     (_,_,errs)      -> fail (errMsg errs)

  where errMsg errs = printUsage (concat (intersperse "\n" errs))
  
        applyFlag :: LambdaCmdLineArgs -> LambdaCmdLineState -> IO LambdaCmdLineState
        applyFlag FullUnfold            st = return st{ cmd_unfold  = True }
        applyFlag ReadStdIn             st = return st{ cmd_stdin   = True }
        applyFlag PrintUsage            st = return st{ cmd_help    = True }
        applyFlag PrintVersion          st = return st{ cmd_version = True }
        applyFlag (Trace Nothing)       st = return st{ cmd_trace   = Just Nothing }
        applyFlag (Trace (Just num))    st = case readDec num of
                                                ((n,[]):_) -> return st{ cmd_trace = Just (Just n) }
                                                _          -> fail (errMsg [concat ["'",num,"' must be a positive integer"]])

        applyFlag (Program pgm)         st = case cmd_input st of
                                                Nothing -> return st{ cmd_input = Just pgm }
                                                _       -> fail (errMsg ["'-e' option may only occur once"])

        applyFlag (Reduction str) st =
            case map toLower str of
                "whnf"   -> return st{ cmd_red = lamReduceWHNF }
		"hnf"    -> return st{ cmd_red = lamReduceHNF }
                "nf"     -> return st{ cmd_red = lamReduceNF }
                "strict" -> return st{ cmd_red = lamStrictNF }
                _        -> fail (concat ["'",str,"' is not a valid reduction strategy"])
                

-----------------------------------------------------------------------
-- Actually run the shell

mapToShellState :: LambdaCmdLineState -> LambdaShellState
mapToShellState st = 
  initialShellState
  { letBindings = cmd_binds st
  , fullUnfold  = cmd_unfold st
  , trace       = isJust (cmd_trace st)
  , traceNum    = let x = traceNum initialShellState
                  in maybe x (maybe x id) (cmd_trace st)
  , redStrategy = cmd_red st
  }

runShell :: LambdaCmdLineState -> IO ()
runShell st = do
   putStrLn versionInfo
   lambdaShell (mapToShellState st)
   return ()



--------------------------------------------------------------------------
-- For dealing with input from stdin or the command line

evalInput :: LambdaCmdLineState -> String -> IO ()
evalInput st expr = do
    case parse (statementsParser (cmd_binds st)) "" expr of
       Left msg    -> fail (show msg)
       Right stmts -> foldl (>>=) (return st) $ map (flip evalStmt) $ stmts
    return ()

evalStdin :: LambdaCmdLineState -> IO ()
evalStdin st = hGetContents stdin >>= evalInput st


evalStmt :: LambdaCmdLineState -> Statement -> IO LambdaCmdLineState
evalStmt st (Stmt_eval t)     = evalTerm st t         >> return st
evalStmt st (Stmt_isEq t1 t2) = compareTerms st t1 t2 >> return st
evalStmt st (Stmt_let name t) = return st{ cmd_binds = Map.insert name t (cmd_binds st) }
evalStmt st (Stmt_empty)      = return st



evalTerm :: LambdaCmdLineState -> PureLambda () String -> IO ()
evalTerm st t = doEval (unfoldTop (cmd_binds st) t)
 where doEval t = 
         case cmd_trace st of
            Nothing       -> putStrLn (printLam (eval t))
            Just Nothing  -> printTrace 50 t
            Just (Just x) -> printTrace x t

       printTrace x t = putStr $ unlines $ map printLam $ take x $ trace t

       eval t  = lamEval      (cmd_binds st) (cmd_unfold st) (cmd_red st) t
       trace t = lamEvalTrace (cmd_binds st) (cmd_unfold st) (cmd_red st) t


compareTerms :: LambdaCmdLineState 
            -> PureLambda () String
            -> PureLambda () String
            -> IO ()

compareTerms st t1 t2 = do
  if normalEq (cmd_binds st) t1 t2 
     then putStrLn "equal"     >> exitWith ExitSuccess
     else putStrLn "not equal" >> exitWith (ExitFailure 100)



-------------------------------------------------------------------------
-- Read definitions from a file

loadDefs :: FilePath -> LambdaCmdLineState -> IO LambdaCmdLineState
loadDefs path st = do
  binds <- readDefinitionFile (cmd_binds st) path
  return st{ cmd_binds = Map.union binds (cmd_binds st) }

readDefinitionFile :: Bindings () String -> String -> IO (Bindings () String)
readDefinitionFile b file = do
  str <- openFile file ReadMode >>= hGetContents
  case parse (definitionFileParser b) file str of
        Left err -> fail (show err)
        Right b' -> return b'



-----------------------------------------------------------------------
-- Printing stuff

printUsage :: String -> String
printUsage str = concat
   [usageInfo "usage: lambda {<option>} [{<file>}]\n" options
   ,"\n\n"
   ,str
   ,"\n\n"
   ,versionInfo
   ,"\n"
   ]

usageNotes :: String
usageNotes =
    "Any files listed after the options will be parsed as a series of "++
    "\"let\" definitions, which will be in scope when the shell starts "++
    "(or when the -e expression is evaluated)"
