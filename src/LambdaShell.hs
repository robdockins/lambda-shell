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
import System.Console.Shell (runShell, cmd, exitCommand, helpCommand,
			     ShellCommand, StateCommand(..), mkShellDescription,
                             Completion (..), Completable(..) )
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
evalExpr t st = eval t >> return st
 where
       -- special case, if the top level lambda term is just a binding, always unfold it
       eval (Binding a x) = eval' (Map.findWithDefault (error $ concat ["'",x,"' not bound"]) x (letBindings st))
       eval x             = eval' x

       eval'  t = putStrLn (printLam (eval'' t))
       eval'' t = lamEval (letBindings st) (fullUnfold st) (redStrategy st) t

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