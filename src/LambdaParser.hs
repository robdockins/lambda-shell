{-
 -   The Lambda Shell, an interactive environment for evaluating pure untyped lambda terms.
 -   Copyright (C) 2005-2011, Robert Dockins
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


-- | This module defines parsers for lambda terms
--   and for \"let\" bound definitions.

module LambdaParser
( nameParser
, lambdaParser
, definitionFileParser
, stripComments
, Statement (..)
, statementParser
, statementsParser
, LamParseState (..)
, LamParser
)
where

import Data.List
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

import Lambda
import CPS

-- | A type representing "statements".  A statement is
--   either a lambda form to reduce, a let binding,
--   a confluence test, a cps transform,
--   or the empty statement.

data Statement
  = Stmt_eval (PureLambda () String)
  | Stmt_decl [String]
  | Stmt_let String (PureLambda () String)
  | Stmt_isEq (PureLambda () String)
              (PureLambda () String)
  | Stmt_empty

data LamParseState
   = LamParseState
   { cpsTransform   :: CPS LamParser
   , extendedSyntax :: Bool
   }

type LamParser = GenParser Char LamParseState

-- | Parser for an identifier.  An identifier is
--   a letter followed by zero or more alphanumeric characters (or underscores).
nameParser :: LamParser String
nameParser =
  do a  <- letter
     as <- many (char '_' <|> alphaNum)
     return (a:as)

-- | Parser for a lambda term.  Function application is left associative.
--
-- @
--   lambda -\> name
--   lambda -\> \'(\' lambda \')\'
--   lambda -\> lambda lambda
--   lambda -\> \'\\\' {name} \'.\' lambda
-- @

lambdaParser :: Bindings () String -> LamParser (PureLambda () String)
lambdaParser b = do
    st <- getState
    let p = if (extendedSyntax st) then extSyntax else basicSyntax
    spaces
    e <- appParser p b []
    spaces
    return e


-- | Parser for multiple statements.
--
-- @
--   stmts -\> stmt ';' stmts
--   stmts -\>
-- @
statementsParser :: Bindings () String -> LamParser [Statement]
statementsParser b = do spaces; x <- p b; eof; return x

 where p b = do x <- stmtParser b
                let b' = case x of
                          (Stmt_let name t) -> Map.insert name (Just t) b
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
statementParser :: Bindings () String -> LamParser Statement
statementParser b = do
   spaces
   x <- stmtParser b
   spaces
   eof
   return x



stmtParser :: Bindings () String -> LamParser Statement
stmtParser b =
       try (letDefParser b     >>= return . uncurry Stmt_let)
   <|> try (declParser b       >>= return . Stmt_decl)
   <|> try (compParser b       >>= return . uncurry Stmt_isEq)
   <|> (lambdaParser b         >>= return . Stmt_eval)
   <|> (return Stmt_empty)

compParser :: Bindings () String -> LamParser (PureLambda () String,PureLambda () String)
compParser b = do
    x <- lambdaParser b
    spaces
    string "=="
    spaces
    y <- lambdaParser b
    spaces
    return (x,y)

declParser :: Bindings () String -> LamParser [String]
declParser b = do
    string "decl"
    many1 space
    sepBy1 nameParser (many1 space)

letDefParser :: Bindings () String -> LamParser (String,PureLambda () String)
letDefParser b = do
    string "let"
    many1 space
    n <- nameParser
    spaces
    char '='
    e <- lambdaParser b
    return (n,e)

stripComments :: String -> String
stripComments (x:xs)
  | x == '#'  = stripComments (dropWhile (/= '\n') xs)
  | otherwise = x : stripComments xs
stripComments [] = []

-- | Parser a file of definitions.  Each definition takes the form
--
-- @
--  def -\> \'let\' name \'=\' lambda \';\'
-- @

definitionFileParser :: Bindings () String -> LamParser (Bindings () String)
definitionFileParser b =
  (do spaces
      (n,t) <- definitionParser b
      spaces
      let b' = Map.insert n (Just t) b
      definitionFileParser b'
  )
  <|> (eof >> return b)



definitionParser :: Bindings () String -> LamParser (String,PureLambda () String)
definitionParser b =
   do n <- nameParser
      spaces
      char '='
      e <- lambdaParser b
      char ';'
      return (n,e)

type P = Bindings () String -> [String] -> LamParser (PureLambda () String)


cpsParser :: P -> P
cpsParser p b l = do
    string "[["
    spaces
    x <- (appParser p) b l
    spaces
    string "]]"
    st <- getState
    cpsTransform st b x

parensParser :: P -> P
parensParser p b l = do
    char '('
    spaces
    e <- (appParser p) b l
    spaces
    char ')'
    return e

varParser :: P
varParser b labels = do
    var <- nameParser
    let i = elemIndex var labels
    case i of
       Just i  -> return (Var () i)
       Nothing -> if Map.member var b
                     then return (Binding () var)
                     else fail ("variable '"++var++"' not in scope")


absParser :: P -> P
absParser p b labels = do
    char '\\'
    spaces
    vars <- sepEndBy1 nameParser spaces
    char '.'
    spaces
    let labels' = foldr (:) labels (reverse vars)
    exp <- (appParser p) b labels'
    let expr = foldr (Lam ()) exp vars
    return expr


appParser :: P -> P
appParser p b l = do
    exprs <- sepEndBy1 (p b l) (many1 space)
    return (foldl1 (App ()) exprs)

basicSyntax :: P
basicSyntax b l =
    parensParser basicSyntax b l <|>
    absParser    basicSyntax b l <|>
    varParser b l

extSyntax :: P
extSyntax b l =
    parensParser extSyntax b l <|>
    absParser    extSyntax b l <|>
    cpsParser    extSyntax b l <|>
    varParser b l
