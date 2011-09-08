{-
 -   The Lambda Shell, an interactive environment for evaluating pure untyped lambda terms.
 -   Copyright (C) 2005-2007, Robert Dockins
 -
 -   This program is free software; you can redistribute it and/or modify
 -   it under the terms of the GNU General Public License as published by
 -   the Free Software Foundation; either version 2 of the License, or
 -   (at your option) any later version.
 -
 -   This program is distributed in the hope that it will be useful,
 -   but WITHOUT ANY WARRANTY; without even the implied warranty of
 -   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -   GNU General Public License for more details.
 -
 -   You should have received a copy of the GNU General Public License
 -   along with this program; if not, write to the Free Software
 -   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 -}


module LambdaShell
( LambdaShellState (..)
, initialShellState
, lambdaShell
, readDefinitionFile
, RS
)
where

import Control.Monad.Trans
import System.IO
import Data.List (isPrefixOf)

import Lambda
import LambdaParser
import CPS
import Version

import qualified Data.Map as Map
import Text.ParserCombinators.Parsec (runParser)

import System.Console.Shell
import System.Console.Shell.ShellMonad

import System.Console.Shell.Backend.Compatline
--import System.Console.Shell.Backend.Haskeline

defaultBackend = compatlineBackend
--defaultBackend = haskelineBackend

type RS = ReductionStrategy () String


-------------------------------------------------------
-- Define types to allow completion of let-bound names

completeLetBindings :: LambdaShellState -> String -> IO [String]
completeLetBindings st prefix =
    return . filter (prefix `isPrefixOf`) . Map.keys . letBindings $ st

data LetBinding = LetBinding

instance Completion LetBinding LambdaShellState where
  complete _         = completeLetBindings
  completableLabel _ = "<name>"



----------------------------------------------------------
-- Define the shell state

-- | Keeps track of all the state that is needed for the
--   operation of the lambda shell.

data LambdaShellState =
  LambdaShellState
  { trace       :: Bool      -- ^ Step through the reduction one redex at a time
  , traceNum    :: Int       -- ^ Number of reduction steps to display during tracing
  , letBindings :: Bindings () String
                             -- ^ All \"let\" bindings currently in scope
  , fullUnfold  :: Bool      -- ^ Should binding names be eagerly unfolded?
  , redStrategy :: RS        -- ^ The reduction strategy currently in use
  , showCount   :: Bool      -- ^ If true, show the number of reductions at each step
  , cpsStrategy :: CPS LamParser -- ^ The current CPS strategy
  , extSyntax   :: Bool      -- ^ Is extended syntax enabled?
  , histFile    :: Maybe String -- ^ A file for command history
  }


-- | Default settings for all elements of shell state.
initialShellState =
  LambdaShellState
  { trace       = False
  , traceNum    = 10
  , letBindings = Map.empty
  , fullUnfold  = False
  , redStrategy = lamReduceWHNF
  , showCount   = False
  , cpsStrategy = simple_cps
  , extSyntax   = True
  , histFile    = Nothing
  }

-----------------------------------------------------------------
-- Main entry point to the shell

-- | Run an interactive shell starting with the
--   given shell state and returning the final,
--   possibly modified, state.
lambdaShell :: LambdaShellState -> IO LambdaShellState
lambdaShell init = do
    let
      desc =
         (mkShellDescription commands evaluate)
         { defaultCompletions = Just completeLetBindings
         , historyFile        = histFile init
         , greetingText       = Just (versionInfo ++ shellMessage)
         , secondaryPrompt    = Just $ \_ -> return "] "
         }
    runShell desc defaultBackend init



-----------------------------------------------------------------
-- read definitions from a file

readDefinitionFile :: LamParseState
                   -> Bindings () String
                   -> String
                   -> IO (Bindings () String)
readDefinitionFile parseSt b file = do
    str  <- openFile file ReadMode >>= hGetContents
    let str' = stripComments str
    case runParser (definitionFileParser b) parseSt file str' of
        Left err -> fail (show err)
        Right b' -> return b'



----------------------------------------------------------------
-- Definition of all the shell commands

commands :: [ShellCommand LambdaShellState]
commands =
  [ exitCommand "quit"
  , exitCommand "exit"
  , helpCommand "help"
  , toggle "trace"     "Toggle the trace mode"      trace      (\x st -> st { trace = x })
  , toggle "unfold"    "Toggle the unfold mode"     fullUnfold (\x st -> st { fullUnfold = x })
  , toggle "showcount" "Toggle the show count mode" showCount  (\x st -> st { showCount = x })
  , toggle "extsyn"    "Toggle extended syntax"     extSyntax  (\x st -> st { extSyntax = x })

  , cmd "tracestep"  setTraceStep    "Set the number of steps shown in trace mode"
  , cmd "dumptrace"  dumpTrace       "Dump a trace of the named term into a file"
  , cmd "showall"    showBindings    "Show all let bindings"
  , cmd "show"       showBinding     "Show a let binding"
  , cmd "whnf"       setRedWHNF      "Set reduction strategy to weak head normal form"
  , cmd "hnf"        setRedHNF       "Set reduction strategy to head normal form"
  , cmd "nf"         setRedNF        "Set reduction strategy to normal form"
  , cmd "null"       setRedNull      "Set the null reduction strategy (no reduction)"
  , cmd "strict"     setRedStrict    "Use applicative order (strict) reduction"
  , cmd "load"       loadDefFile     "Load definitions from a file"
  , cmd "clear"      clearBindings   "Clear all let bindings"

  , cmd "nowarranty" (shellPutInfo noWarranty)  "Print the warranty disclaimer"
  , cmd "gpl"        (shellPutInfo gpl)         "Print the GNU GPLv2, under which this software is licensed"
  , cmd "version"    (shellPutInfo versionInfo) "Print version info"
  , cmd "simple_cps"  setCPSSimple   "Use the simple CPS strategy"
  , cmd "onepass_cps" setCPSOnepass  "Use the onepass optimizing CPS strategy"

  , cmd "backend"    printBackend "Print the backend configuration"
  ]


printBackend :: Sh LambdaShellState ()
printBackend =
  shellPutStrLn (show compatlineConfig)


dumpTrace :: File -> Int -> Completable LetBinding -> Sh LambdaShellState ()
dumpTrace (File f) steps (Completable termStr) = do
   st <- getShellSt
   let parseSt = LamParseState (cpsStrategy st) (extSyntax st)
   case runParser (lambdaParser (letBindings st)) parseSt "" termStr of
      Left msg   -> shellPutErrLn (show msg)
      Right term -> do
         let trace = lamEvalTrace (letBindings st) (fullUnfold st)
                                  (redStrategy st)
                                  (unfoldTop (letBindings st) term)
         liftIO (writeFile f (unlines . map printLam . take steps $ trace))


setTraceStep :: Int -> Sh LambdaShellState ()
setTraceStep step = getShellSt >>= \st -> putShellSt st{ traceNum = step }

showBinding :: Completable LetBinding -> Sh LambdaShellState ()
showBinding (Completable name) = do
    st <- getShellSt
    case Map.lookup name (letBindings st) of
        Nothing -> shellPutErrLn  $ concat ["'",name,"' not bound"]
        Just Nothing  -> shellPutInfoLn $ concat [name," << free variable >>"]
        Just (Just t) -> shellPutInfoLn $ concat [name," = ",printLam t]

showBindings :: Sh LambdaShellState ()
showBindings = do
   st <- getShellSt
   shellPutStrLn $
     Map.foldWithKey
       (\name t x -> case t of
              Nothing -> concat [name," << free variable >>\n",x]
              Just t  -> concat [name," = ",printLam t,"\n",x])
       ""
       (letBindings st)

clearBindings :: Sh LambdaShellState ()
clearBindings = modifyShellSt (\st -> st{ letBindings = Map.empty })

loadDefFile :: File -> Sh LambdaShellState ()
loadDefFile (File path) = do
   st <- getShellSt
   let parseSt = LamParseState (cpsStrategy st) (extSyntax st)
   newBinds <- liftIO (readDefinitionFile parseSt (letBindings st) path)
   putShellSt st{ letBindings = newBinds }


setRedWHNF :: Sh LambdaShellState ()
setRedWHNF = setRed lamReduceWHNF "weak head normal form"

setRedHNF :: Sh LambdaShellState ()
setRedHNF = setRed lamReduceHNF "head normal form"

setRedNF :: Sh LambdaShellState ()
setRedNF = setRed lamReduceNF "normal form"

setRedStrict :: Sh LambdaShellState ()
setRedStrict = setRed lamStrictNF "applicative order"

setRedNull :: Sh LambdaShellState ()
setRedNull = setRed lamReduceNull "no reduction"

setRed :: RS -> String -> Sh LambdaShellState ()
setRed strategy name = do
   shellPutInfoLn $ concat ["using reduction strategy: ",name]
   modifyShellSt (\st -> st{ redStrategy = strategy })

setCPSSimple :: Sh LambdaShellState ()
setCPSSimple = setCPS simple_cps "simple"

setCPSOnepass :: Sh LambdaShellState ()
setCPSOnepass = setCPS onepass_cps "onepass"

setCPS :: CPS LamParser -> String -> Sh LambdaShellState ()
setCPS cps name = do
   shellPutInfoLn $ concat ["unsing CPS strategy: ",name]
   modifyShellSt (\st -> st{ cpsStrategy = cps })

----------------------------------------------------------------
-- Normal statement evaluation

evaluate :: String -> Sh LambdaShellState ()
evaluate str = do
  case reverse str of
   '@':_ -> shellSpecial (ShellContinueLine (init str))
   _ -> do
      st <- getShellSt
      let parseSt = LamParseState (cpsStrategy st) (extSyntax st)
      case runParser (statementParser (letBindings st)) parseSt "" str of
        Left err   -> shellPutErrLn (show err)
        Right stmt ->
          case stmt of
           Stmt_eval expr      -> evalExpr expr
           Stmt_isEq x y       -> compareExpr x y
           Stmt_decl nm        -> modifyShellSt (\st -> st{ letBindings = Map.insert nm Nothing (letBindings st) })
           Stmt_let nm expr    -> modifyShellSt (\st -> st{ letBindings = Map.insert nm (Just expr) (letBindings st) })
           Stmt_empty          -> return ()


evalExpr :: PureLambda () String -> Sh LambdaShellState ()
evalExpr t = getShellSt >>= \st -> doEval (unfoldTop (letBindings st) t) st

 where
   doEval x st
    | trace st     = traceEval x
    | showCount st = evalCount x st
    | otherwise    = eval x st

   traceEval x = do
      subshell <- liftIO (traceSubshell x)
      shellSpecial (ExecSubshell subshell)

   evalCount t st = do
      let (z,n) = lamEvalCount (letBindings st) (fullUnfold st) (redStrategy st) t
      shellPutStrLn $ printLam z
      shellPutInfoLn $ concat ["<<",show n," reductions>>"]

   eval t st = do
      let z = lamEval (letBindings st) (fullUnfold st) (redStrategy st) t
      shellPutStrLn $ printLam z


compareExpr :: PureLambda () String
            -> PureLambda () String
            -> Sh LambdaShellState ()

compareExpr x y = do
    st <- getShellSt
    if normalEq (letBindings st) x y
        then shellPutInfoLn "equal"
        else shellPutInfoLn "not equal"


----------------------------------------------------------------
-- All the stuff for the tracing subshell

data TraceShellState
   = TraceShellState
     { tracePos  :: Int
     , traceStep :: Int
     , traceList :: [PureLambda () String]
     }

mkTraceDesc :: ShellDescription TraceShellState
mkTraceDesc =
  initialShellDescription
      { prompt         = \_ -> return "  ]"
      , commandStyle   = SingleCharCommands
      , shellCommands  = traceShellCommands
      , beforePrompt   = printTrace
      , historyEnabled = False
      }

traceShellCommands :: [ShellCommand TraceShellState]
traceShellCommands =
  [ cmd "p" tracePrev "previous"
  , cmd "n" traceNext "next"
  , helpCommand "h"
  , helpCommand "?"
  , exitCommand "q"
  ]

printTrace :: Sh TraceShellState ()
printTrace = do
  st <- getShellSt
  shellPutStr $ unlines $ map (\(n,t) -> concat[show n,") ",printLam t]) $
        take (traceStep st) $ drop (tracePos st) $ zip [1..] (traceList st)

tracePrev :: Sh TraceShellState ()
tracePrev = do
  modifyShellSt $ \st ->
      let x = max 0 (tracePos st - traceStep st) in
      st{ tracePos = x }

traceNext :: Sh TraceShellState ()
traceNext = do
  st <- getShellSt
  let x = tracePos st + traceStep st
  if null (drop (tracePos st) (traceList st))
     then return ()
     else putShellSt st{ tracePos = x }

mkTraceState :: PureLambda () String -> LambdaShellState -> IO TraceShellState
mkTraceState term st =
   return TraceShellState
          { tracePos  = 0
          , traceStep = traceNum st
          , traceList = lamEvalTrace (letBindings st) (fullUnfold st) (redStrategy st) term
          }

traceSubshell :: PureLambda () String -> IO (Subshell LambdaShellState TraceShellState)
traceSubshell term =
   simpleSubshell (mkTraceState term) mkTraceDesc
