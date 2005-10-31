module Syntax where

data PureLambda a
   = Lam a String (PureLambda a)
   | App a (PureLambda a) (PureLambda a)
   | Var a Int

