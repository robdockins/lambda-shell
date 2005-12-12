module LambdaCmdLine 
( lambdaCmdLine
) where

import Numeric
import Maybe
import Data.List
import qualified Data.Map as Map
import System.IO
import System.Console.GetOpt
import Text.ParserCombinators.Parsec (parse)

import Lambda
import LambdaParser
import LambdaShell
import Version

data LambdaCmdLineArgs
  = FullUnfold
  | ReadStdIn
  | Expression String
  | DefinitionFile String
  | Trace (Maybe String)
  | PrintUsage
  | PrintVersion

data LambdaCmdLineState
   = LambdaCmdLineState
     { cmd_unfold  :: Bool
     , cmd_stdin   :: Bool
     , cmd_expr    :: Maybe String
     , cmd_binds   :: Bindings () String
     , cmd_help    :: Bool
     , cmd_version :: Bool
     , cmd_trace   :: Maybe (Maybe Int)
     }

initialCmdLineState =
  LambdaCmdLineState
  { cmd_unfold  = False
  , cmd_stdin   = False
  , cmd_expr    = Nothing
  , cmd_binds   = Map.empty
  , cmd_help    = False
  , cmd_version = False
  , cmd_trace   = Nothing
  }

options :: [OptDescr LambdaCmdLineArgs]
options = 
  [ Option ['u']     ["unfold"]      (NoArg FullUnfold)             "perform full unfolding of let-bound terms"
  , Option ['s']     ["stdin"]       (NoArg ReadStdIn)              "read from standard in"
  , Option ['e']     ["expression"]  (ReqArg Expression "EXPR")     "evaluate expression from command line"
  , Option ['f']     ["file"]        (ReqArg DefinitionFile "FILE") "read let definitions from a file"
  , Option ['r']     ["trace"]       (OptArg Trace "TRACE_NUM")     "set tracing (and optional trace display length)"
  , Option ['h','?'] ["help"]        (NoArg PrintUsage)             "print this message"
  , Option ['v']     ["version"]     (NoArg PrintVersion)           "print version information"
  ]

parseCmdLine :: [String] -> IO LambdaCmdLineState
parseCmdLine argv = 
   case getOpt RequireOrder options argv of
     (opts,_,[]) -> foldl (>>=) (return initialCmdLineState) $ map applyFlag opts
     (_,_,errs)  -> fail (errMsg errs)

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

        applyFlag (Expression ex)       st = case cmd_expr st of
                                                Nothing -> return st{ cmd_expr = Just ex }
                                                _       -> fail (errMsg ["'-e' option may only occur once"])
        applyFlag (DefinitionFile file) st = do binds <- readDefinitionFile (cmd_binds st) file
                                                return st{ cmd_binds = Map.union binds (cmd_binds st) }

printUsage :: String -> String
printUsage str = (usageInfo "usage: lambda {OPTION}\n" options) ++ str


readDefinitionFile :: Bindings () String -> String -> IO (Bindings () String)
readDefinitionFile b file =
  do str <- openFile file ReadMode >>= hGetContents
     case parse (definitionFileParser b) file str of
        Left err -> fail (show err)
        Right b' -> return b'

evalStdin :: LambdaCmdLineState -> IO ()
evalStdin st = 
   do expr <- hGetContents stdin
      evalExpr st expr

evalExpr :: LambdaCmdLineState -> String -> IO ()
evalExpr st expr = 
    case parse (lambdaParser (cmd_binds st)) "" expr of
       Left msg -> fail (show msg)
       Right t  -> evalTerm st t

evalTerm :: LambdaCmdLineState -> PureLambda () String -> IO ()
evalTerm st t = putStrLn (printLam (eval t))

 where -- special case, if the top level lambda term is just a binding, always unfold it
       eval (Binding a x) = eval' (Map.findWithDefault (error $ concat ["'",x,"' not bound"]) x (cmd_binds st))
       eval x             = eval' x
 
       eval' t = lamEval (cmd_binds st) (cmd_unfold st) lamReduceHNF t


mapToShellState :: LambdaCmdLineState -> LambdaShellState
mapToShellState st = 
  initialShellState
  { letBindings = cmd_binds st
  , fullUnfold  = cmd_unfold st
  , trace       = isJust (cmd_trace st)
  , traceNum    = let x = traceNum initialShellState
                  in maybe x (maybe x id) (cmd_trace st)
  }

runShell :: LambdaCmdLineState -> IO ()
runShell st = lambdaShell (mapToShellState st) >> return ()

doCmdLine :: LambdaCmdLineState -> IO ()
doCmdLine st =
   case (cmd_expr st) of
       Just expr -> evalExpr st expr
       Nothing   -> 
           if (cmd_stdin st) 
              then evalStdin st
              else runShell st

lambdaCmdLine :: [String] -> IO ()
lambdaCmdLine argv =
   do st <- parseCmdLine argv
      if (cmd_help st)
         then putStrLn (printUsage "")
         else if (cmd_version st) 
                 then putStrLn versionInfo
                 else doCmdLine st
