-- | This module defines parsers for lambda terms
--   and for \"let\" bound definitions.

module LambdaParser 
( nameParser
, lambdaParser
, definitionFileParser
, Statement (..)
, statementParser
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
--   a letter followed by zero or more alphanumeric characters.
nameParser :: Parser String
nameParser = 
  do a  <- letter
     as <- many alphaNum
     return (a:as)

-- | Parser for a statement.
-- 
-- @
--    stmt -\> \'let\' name \'=\' lambda
--    stmt -\> lambda
-- @

statementParser :: Bindings () String -> Parser Statement
statementParser b = do
  spaces
  x <- (   try (letDefParser b     >>= return . uncurry Stmt_let)
       <|> try (compParser b       >>= return . uncurry Stmt_isEq)
       <|> (lambdaParser b         >>= return . Stmt_eval)
       <|> (return Stmt_empty)
       )
  eof 
  return x

-- | Parser for a lambda term.  Function application is left associative.
-- 
-- @
--   lambda -\> name
--   lambda -\> \'(\' lambda \')\'
--   lambda -\> lambda lambda
--   lambda -\> \'\\\' {name} \'.\' lambda
-- @

lambdaParser :: Bindings () String -> Parser (PureLambda () String)
lambdaParser b = do e <- appParser b []; spaces; return e

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
