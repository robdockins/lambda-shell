-- | This module defines parsers for lambda terms
--   and for \"let\" bound definitions.

module LambdaParser 
( nameParser
, lambdaParser
, definitionFileParser
, Statement (..)
, statementParser
, statementsParser
)
where

import Data.List
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

import Lambda

-- | A type representing either a lambda term to evaluate
--   or a let binding.
data Statement
  = Stmt_eval (PureLambda () String)
  | Stmt_let String (PureLambda () String)
  | Stmt_isEq (PureLambda () String) 
              (PureLambda () String)
  | Stmt_empty

-- | Parser for an identifier.  An identifier is
--   a letter followed by zero or more alphanumeric characters (or underscores).
nameParser :: Parser String
nameParser = 
  do a  <- letter
     as <- many (char '_' <|> alphaNum)
     return (a:as)

-- | Parser for multiple statements.
--
-- @
--   stmts -\> stmt ';' stmts
--   stmts -\>
-- @
statementsParser :: Bindings () String -> Parser [Statement]
statementsParser b = do spaces; x <- p b; eof; return x

 where p b = do x <- stmtParser b
                let b' = case x of
                          (Stmt_let name t) -> Map.insert name t b
                          _ -> b
                spaces
                ( do char ';'
                     spaces
                     xs <- p b'
                     return (x:xs))
                 <|> (return [x])

-- | Parser for a statement.
-- 
-- @
--    stmt -\> \'let\' name \'=\' lambda
--    stmt -\> lambda
-- @
statementParser :: Bindings () String -> Parser Statement
statementParser b = do
   spaces
   x <- stmtParser b
   spaces
   eof
   return x


stmtParser :: Bindings () String -> Parser Statement
stmtParser b =
       try (letDefParser b     >>= return . uncurry Stmt_let)
   <|> try (compParser b       >>= return . uncurry Stmt_isEq)
   <|> (lambdaParser b         >>= return . Stmt_eval)
   <|> (return Stmt_empty)

-- | Parser for a lambda term.  Function application is left associative.
-- 
-- @
--   lambda -\> name
--   lambda -\> \'(\' lambda \')\'
--   lambda -\> lambda lambda
--   lambda -\> \'\\\' {name} \'.\' lambda
-- @

lambdaParser :: Bindings () String -> Parser (PureLambda () String)
lambdaParser b = do spaces; e <- appParser b []; spaces; return e

compParser :: Bindings () String -> Parser (PureLambda () String,PureLambda () String)
compParser b = do
    x <- lambdaParser b
    spaces
    string "=="
    spaces
    y <- lambdaParser b
    spaces
    return (x,y)

letDefParser :: Bindings () String -> Parser (String,PureLambda () String)
letDefParser b = do
    string "let"
    many1 space
    n <- nameParser
    spaces
    char '='
    spaces
    e <- appParser b []
    spaces
    return (n,e)

-- | Parser a file of definitions.  Each definition takes the form
--
-- @
--  def -\> \'let\' name \'=\' lambda \';\'
-- @

definitionFileParser :: Bindings () String -> Parser (Bindings () String)
definitionFileParser b = 
  (do spaces
      (n,t) <- definitionParser b
      spaces
      let b' = Map.insert n t b
      definitionFileParser b'
  )
  <|> (eof >> return b)
      
definitionParser :: Bindings () String -> Parser (String,PureLambda () String)
definitionParser b = 
   do n <- nameParser
      spaces
      char '='
      spaces
      e <- appParser b []
      spaces
      char ';'
      return (n,e)

lambdaParser' :: Bindings () String -> [String] -> Parser (PureLambda () String)
lambdaParser' b labels =
     (do char '('; spaces; e <- appParser b labels; spaces; char ')'; return e)

 <|> (do char '\\'
         spaces
         vars <- sepEndBy1 nameParser spaces
         char '.'
         spaces
         let labels' = foldr (:) labels (reverse vars)
         exp <- appParser b labels'
         let expr = foldr (Lam ()) exp vars
         return expr)

 <|> (do var <- nameParser
         let i = elemIndex var labels
         case i of
            Just i  -> return (Var () i)
            Nothing -> if Map.member var b
                         then return (Binding () var)
                         else fail ("variable '"++var++"' not in scope") )

appParser :: Bindings () String -> [String] -> Parser (PureLambda () String)
appParser b labels = 
   do exprs <- sepEndBy1 (lambdaParser' b labels) (many1 space)
      return (foldl1 (App ()) exprs)
