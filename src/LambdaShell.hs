module LambdaShell
( LambdaShellState (..)
, initialShellState
, lambdaShell
)
where

import Lambda
import LambdaParser

import qualified Data.Map as Map
import System.Console.Shell (runShell, cmd, exitCommand, helpCommand,
			     ShellCommand, StateCommand(..), mkShellDescription)
import Text.ParserCombinators.Parsec (parse)

data LambdaShellState =
  LambdaShellState
  { trace       :: Bool
  , traceNum    :: Int
  , letBindings :: Map.Map String (PureLambda () String)
  , fullUnfold  :: Bool
  }

initialShellState =
  LambdaShellState
  { trace       = False
  , traceNum    = 10
  , letBindings = Map.empty
  , fullUnfold  = False
  }

lambdaShell :: LambdaShellState -> IO LambdaShellState
lambdaShell init = do
    desc <- mkShellDescription commands evaluate
    runShell desc init

commands :: [ShellCommand LambdaShellState]
commands =
  [ exitCommand "quit"
  , helpCommand "help"
  , cmd "trace" toggleTrace   "Toggles the trace mode"
  , cmd "unfold" toggleUnfold "Toggles the full unfold mode"
  , cmd "showall" showBindings "Shows all let bindings"
  , cmd "show" showBinding "Show a let binding"
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

showBinding :: String -> StateCommand LambdaShellState
showBinding name = StateCommand $ \st -> do
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

evaluate :: String -> LambdaShellState -> IO LambdaShellState
evaluate str st = do
  case parse (statementParser (letBindings st)) "" str of
     Left err   -> putStrLn (show err) >> return st
     Right stmt -> evalStmt stmt st

evalStmt :: Statement -> LambdaShellState -> IO LambdaShellState
evalStmt (Stmt_eval expr) st     = evalExpr expr st
evalStmt (Stmt_let name expr) st = return st{ letBindings = Map.insert name expr (letBindings st) }

evalExpr :: PureLambda () String -> LambdaShellState -> IO LambdaShellState
evalExpr t st = eval t >> return st
 where
       -- special case, if the top level lambda term is just a binding, always unfold it
       eval (Binding a x) = eval' (Map.findWithDefault (error $ concat ["'",x,"' not bound"]) x (letBindings st))
       eval x             = eval' x

       eval'  t = putStrLn (printLam (eval'' t))
       eval'' t = lamEval (letBindings st) (fullUnfold st) lamReduceHNF t
