module LambdaParser 
( nameParser
, lambdaParser
, definitionFileParser
)
where

import Data.List
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

import Lambda

nameParser :: Parser String
nameParser = 
  do a  <- letter
     as <- many alphaNum
     return (a:as)

lambdaParser :: Bindings () String -> Parser (PureLambda () String)
lambdaParser b = do spaces; e <- appParser b []; spaces; return e

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

