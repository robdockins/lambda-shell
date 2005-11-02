module Env
( Env
, empty
, insert
, lookup
) where

import Prelude hiding (lookup)
import qualified Data.Set as Set

data Env = Env !Int ![String] !(Set.Set String)

empty :: Env
empty = Env 0 [] (Set.empty)

insert :: String -> Env -> Env
insert label (Env z labels set)
    | label `Set.member` set = Env (z+1) ( (label++"_"++(show z)) : labels) set
    | otherwise              = Env z     ( label : labels )                 (Set.insert label set)

lookup :: Int -> Env -> String
--lookup x (Env z labels _) = labels !! x

lookup x (Env z labels set) =
   case drop x labels of
      l:_ -> l
      []  -> error (concat ["'",show x,"' out of bounds in environment ",show labels])
