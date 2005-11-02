module LambdaShell
( ShellState (..)
, initialShellState
, lambdaShell
)
where

import qualified Env as Env
import Lambda
import LambdaParser
import LambdaSearchTree

import Control.Monad
import Control.Concurrent
import Control.Concurrent.MVar
import qualified Control.Exception as Ex
import qualified System.Console.Readline as Readline
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

data ShellState =
  ShellState
  { trace       :: Bool
  , traceNum    :: Int
  , termCheck   :: Bool
  , letBindings :: Map.Map String (PureLambda () String)
  , fullUnfold  :: Bool
  }

initialShellState =
  ShellState
  { trace       = False
  , traceNum    = 10
  , termCheck   = True
  , letBindings = Map.empty
  , fullUnfold  = False
  }

lambdaShell :: ShellState -> IO ()
lambdaShell state
     = do Readline.initialize
          Ex.finally (Readline.resetTerminal Nothing)
                     (shellLoop state)

  where shellLoop state =
         do input <- Readline.readline "> "
            case input of
              Nothing  -> return ()
              Just inp -> handleInput inp state shellLoop

data ShellCommand
  = SC_quit
  | SC_termCheck
  | SC_trace
  | SC_setTraceNum Int
  | SC_help
  | SC_show String
  | SC_showAll
  | SC_unfold
  | SC_eval Statement

data Statement
  = Stmt_eval (PureLambda () String)
  | Stmt_let String (PureLambda () String)

handleInput :: String -> ShellState -> (ShellState -> IO ()) -> IO ()
handleInput input state cont =
   case parse (commandParser state) "" input of
      Left err  -> putStrLn (show err) >> cont state
      Right cmd -> interpretCommand cmd state cont

commandParser :: ShellState -> Parser ShellCommand
commandParser state = do spaces; c <- cmdParser <|> stmtParser; spaces; eof; return c

 where stmtParser =
        (do string "let"; spaces;
            w <- nameParser
            spaces; char '='; spaces
            e <- lambdaParser (letBindings state)
            return (SC_eval (Stmt_let w e)))
        <|>
        (lambdaParser (letBindings state) >>= return . SC_eval . Stmt_eval)

       cmdParser = do
          char ':'
          (    try (string "quit"        >> return SC_quit)
           <|> try (string "trace"       >> return SC_trace)
           <|> try (string "termination" >> return SC_termCheck)
           <|> try (string "help"        >> return SC_help)
           <|> try (string "unfold"      >> return SC_unfold)
           <|> try (string "showAll"     >> return SC_showAll)
           <|> try
               (do string "show"
                   spaces
                   name <- nameParser
                   return (SC_show name))
           <|> try
               (do string "traceNum"
                   spaces
                   i <- many1 digit
                   return (SC_setTraceNum (read i)) )
           )

interpretCommand :: ShellCommand -> ShellState -> (ShellState -> IO ()) -> IO ()
interpretCommand cmd state cont =
  case cmd of
    SC_quit          -> putStrLn "goodbye"
    SC_trace         -> if trace state
                          then putStrLn "trace off" >> cont state{ trace = False }
                          else putStrLn "trace on"  >> cont state{ trace = True }
    SC_unfold        -> if fullUnfold state
                          then putStrLn "full unfolding off" >> cont state{ fullUnfold = False }
                          else putStrLn "full unfolding on"  >> cont state{ fullUnfold = True }
    SC_setTraceNum i -> cont state{ traceNum = i }
    SC_termCheck     -> if termCheck state
                          then putStrLn "termination checking off" >> cont state{ termCheck = False }
                          else putStrLn "termination checking on"  >> cont state{ termCheck = True }
    SC_help          -> printHelp state >> cont state
    SC_show name     -> showBinding name state >> cont state
    SC_showAll       -> showBindings state >> cont state
    SC_eval stmt     -> evalStmt stmt state cont

printHelp :: ShellState -> IO ()
printHelp state = putStrLn "you need help..."

showBinding :: String -> ShellState -> IO ()
showBinding name state =
    case Map.lookup name (letBindings state) of
        Nothing -> putStrLn $ concat ["'",name,"' not bound"]
        Just t  -> putStrLn $ concat [name," = ",printLam t]

showBindings :: ShellState -> IO ()
showBindings state = putStrLn $
   Map.foldWithKey
       (\name t x -> concat [name," = ",printLam t,"\n",x])
       ""
       (letBindings state)

evalStmt :: Statement -> ShellState -> (ShellState -> IO ()) -> IO ()
evalStmt (Stmt_eval expr) state cont     = evalExpr expr state cont
evalStmt (Stmt_let name expr) state cont = cont state{ letBindings = Map.insert name expr (letBindings state) }

evalExpr :: PureLambda () String -> ShellState -> (ShellState -> IO ()) -> IO ()
evalExpr t state cont = eval t
 where
       -- special case, if the top level lambda term is just a binding, always unfold it
       eval (Binding a x) = eval' (Map.findWithDefault (error $ concat ["'",x,"' not bound"]) x (letBindings state))
       eval x             = eval' x

       eval' t  = if trace state 
                     then traceEval t state cont
                     else putStrLn (printLam (eval'' t)) >> cont state


       eval'' t = if termCheck state
                     then lamEvalMemo (letBindings state) (fullUnfold state) t
                     else lamEval     (letBindings state) (fullUnfold state) lamReduceHNF t


traceEval :: PureLambda () String -> ShellState -> (ShellState -> IO ()) -> IO ()
traceEval t state cont = showTrace 0

  where -- list of evaluation steps
        evalTrace = zip [1..] (lamEvalTrace (letBindings state) (fullUnfold state) lamReduceHNF t)

        -- runs a mini-shell for displaying evaluation traces

        showTrace start =
	  do let showList = take (traceNum state) $ drop start evalTrace
             if (null showList) 
                then showTrace (max 0 (start-(traceNum state)))
                else do putStrLn $ unlines $ map (\(n,t) -> (show n)++"  "++(printLam t)) $ showList
                        putStrLn "  (n)ext (p)revious (q)uit"
                        getAction start

        getAction start =
         do input <- Readline.readline " ] "
            case input of
              Nothing       -> return ()
              Just ('n':_)  -> showTrace (start+(traceNum state))
              Just ('p':_)  -> showTrace (max 0 (start-(traceNum state)))
              Just ('q':_)  -> cont state
              _             -> getAction start
