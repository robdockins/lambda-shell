module LambdaShell
( LambdaShellState (..)
, initialShellState
, lambdaShell
, RS
)
where

import Data.List (isPrefixOf)

import Lambda
import LambdaParser

import qualified Data.Map as Map
import System.Console.Shell
import Text.ParserCombinators.Parsec (parse)

type RS = ReductionStrategy () String

data LetBinding = LetBinding

instance Completion LetBinding LambdaShellState where
  complete _ st prefix = return 
                         $ filter (prefix `isPrefixOf`)
                         $ Map.keys
                         $ letBindings st

  completableLabel _ = "<name>"

-- | Keeps track of all the state that is needed for the
--   operation of the lambda shell.
data LambdaShellState =
  LambdaShellState
  { trace       :: Bool      -- ^ Step through the reduction one redex at a time
  , traceNum    :: Int       -- ^ Number of reduction steps to display during tracing
  , letBindings :: Map.Map String (PureLambda () String)
                             -- ^ All \"let\" bindings currently in scope
  , fullUnfold  :: Bool      -- ^ Should binding names be eagerly unfolded?
  , redStrategy :: RS        -- ^ The reduction strategy currently in use
  }

-- | Default settings for all elements of shell state.
initialShellState =
  LambdaShellState
  { trace       = False
  , traceNum    = 10
  , letBindings = Map.empty
  , fullUnfold  = False
  , redStrategy = lamReduceWHNF
  }

-- | Run an interactive shell starting with the
--   given shell state and returning the final,
--   possibly modified, state.
lambdaShell :: LambdaShellState -> IO LambdaShellState
lambdaShell init = do
    desc <- mkShellDescription commands evaluate
    runShell desc init

commands :: [ShellCommand LambdaShellState]
commands =
  [ exitCommand "quit"
  , exitCommand "exit"
  , helpCommand "help"
  , cmd "trace"   toggleTrace   "Toggles the trace mode"
  , cmd "traceStep" setTraceStep "Sets the number of steps shown in trace mode"
  , cmd "unfold"  toggleUnfold "Toggles the full unfold mode"
  , cmd "showall" showBindings "Shows all let bindings"
  , cmd "show"    showBinding "Show a let binding"
  , cmd "whnf"    setRedWHNF "Set reduction strategy to weak head normal form"
  , cmd "hnf"     setRedHNF "Set reduction strategy to head normal form"
  , cmd "nf"      setRedNF  "Set reduction strategy to normal form"
  , cmd "strict"  setRedStrict "Use applicative order (strict) reduction"
  ]
  
toggleTrace :: StateCommand LambdaShellState
toggleTrace = StateCommand $ \st -> do
   if trace st 
      then putStrLn "trace off" >> return st{ trace = False }
      else putStrLn "trace on"  >> return st{ trace = True }

toggleUnfold :: StateCommand LambdaShellState
toggleUnfold = StateCommand $ \st -> do
   if fullUnfold st
      then putStrLn "full unfold off" >> return st{ fullUnfold = False }
      else putStrLn "full unfold on"  >> return st{ fullUnfold = True }


setTraceStep :: Int -> StateCommand LambdaShellState
setTraceStep step = StateCommand $ \st -> return st{ traceNum = step }

showBinding :: Completable LetBinding -> StateCommand LambdaShellState
showBinding (Completable name) = StateCommand $ \st -> do
    case Map.lookup name (letBindings st) of
        Nothing -> putStrLn $ concat ["'",name,"' not bound"]
        Just t  -> putStrLn $ concat [name," = ",printLam t]
    return st

showBindings :: StateCommand LambdaShellState
showBindings = StateCommand $ \st -> do
   putStrLn $
     Map.foldWithKey
       (\name t x -> concat [name," = ",printLam t,"\n",x])
       ""
       (letBindings st)
   return st


setRedWHNF :: StateCommand LambdaShellState
setRedWHNF = setRed lamReduceWHNF "weak head normal form"

setRedHNF :: StateCommand LambdaShellState
setRedHNF = setRed lamReduceHNF "head normal form"

setRedNF :: StateCommand LambdaShellState
setRedNF = setRed lamReduceNF "normal form"

setRedStrict :: StateCommand LambdaShellState
setRedStrict = setRed lamStrictNF "applicative order"

setRed :: RS -> String -> StateCommand LambdaShellState
setRed strategy name = StateCommand $ \st -> do
  putStrLn ("using reduction strategy: "++name)
  return st{ redStrategy = strategy }

evaluate :: String -> LambdaShellState -> IO LambdaShellState
evaluate str st = do
  case parse (statementParser (letBindings st)) "" str of
     Left err   -> putStrLn (show err) >> return st
     Right stmt -> evalStmt stmt st

evalStmt :: Statement -> LambdaShellState -> IO LambdaShellState
evalStmt (Stmt_eval expr) st     = evalExpr expr st
evalStmt (Stmt_isEq x y) st      = compareExpr x y st
evalStmt (Stmt_let name expr) st = return st{ letBindings = Map.insert name expr (letBindings st) }
evalStmt (Stmt_empty) st         = return st


evalExpr :: PureLambda () String -> LambdaShellState -> IO LambdaShellState
evalExpr t st = doEval t >> return st
 where
       -- special case, if the top level lambda term is just a binding, always unfold it
       doEval (Binding a x) = doEval' (Map.findWithDefault (error $ concat ["'",x,"' not bound"]) x (letBindings st))
       doEval x             = doEval' x

       doEval' x = if (trace st)
                      then traceEval x st
                      else (putStrLn (printLam (eval x))) >> return st

       eval t = lamEval (letBindings st) (fullUnfold st) (redStrategy st) t

compareExpr :: PureLambda () String 
            -> PureLambda () String
	    -> LambdaShellState 
	    -> IO LambdaShellState
compareExpr x y st = do
     let x' = eval x
     let y' = eval y
     if alphaEq x' y'
        then putStrLn "equal"
        else putStrLn "not equal"
     return st

  where eval t = lamEval (letBindings st) True lamReduceNF t


data TraceShellState 
   = TraceShellState
     { tracePos  :: Int
     , traceStep :: Int
     , traceList :: [PureLambda () String]
     }

mkTraceDesc :: IO (ShellDescription TraceShellState)
mkTraceDesc = do
  desc <- initialShellDescription
  return desc{ prompt = tracePrompt
             , commandStyle = OnlyCommands
	     , shellCommands = traceShellCommands
             , beforePrompt = printTrace
             }
        
tracePrompt :: String
tracePrompt = "  ]"

traceShellCommands :: [ShellCommand TraceShellState]
traceShellCommands =
  [ cmd "p" tracePrev "previous"
  , cmd "n" traceNext "next"
  , exitCommand "q"
  ]

printTrace :: TraceShellState -> IO ()
printTrace st = do
  putStr $ unlines $ map (\(n,t) -> concat[show n,") ",printLam t]) $
	take (traceStep st) $ drop (tracePos st) $ zip [1..] (traceList st)

tracePrev :: StateCommand TraceShellState
tracePrev = StateCommand $ \st -> do
  let x = max 0 (tracePos st - traceStep st)
  return st{ tracePos = x}

traceNext :: StateCommand TraceShellState
traceNext = StateCommand $ \st -> do
  let x = tracePos st + traceStep st
  if null (drop (tracePos st) (traceList st))
     then return st
     else return st{ tracePos = x }

mkTraceState :: PureLambda () String -> LambdaShellState -> IO TraceShellState
mkTraceState term st =
   return TraceShellState
          { tracePos = 0
          , traceStep = traceNum st
          , traceList = lamEvalTrace (letBindings st) (fullUnfold st) (redStrategy st) term
          }

traceSubshell :: PureLambda () String -> IO (Subshell LambdaShellState TraceShellState)
traceSubshell term = do
  desc <- mkTraceDesc
  simpleSubshell (mkTraceState term) desc

traceEval :: PureLambda () String -> LambdaShellState -> IO LambdaShellState
traceEval term st = do
  subShell <- traceSubshell term
  runSubshell subShell st
