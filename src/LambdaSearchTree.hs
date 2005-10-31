module LambdaSearchTree where

import Maybe (fromJust)
import Data.Array

import Lambda

data LamSymbol a
  = Sym_Lam a String
  | Sym_App a
  | Sym_Var a Int
 
linearForm :: PureLambda a -> [LamSymbol a]
linearForm t = let (xs,_) = linearForm' t 0 in xs

linearForm' :: PureLambda a -> Int -> ([LamSymbol a],Int)
linearForm' (Lam a l t)   n = let (xs,n') = linearForm' t n in (Sym_Lam a l : xs,n')

linearForm' (App a t1 t2) n = 
   let (xs1,n')  = linearForm' t1 n
       (xs2,n'') = linearForm' t2 n'
   in (Sym_App a : xs1 ++ xs2,n'')

linearForm' (Var a x)     n = ([Sym_Var a x],max n x)

treeForm :: [LamSymbol a] -> Maybe (PureLambda a)
treeForm xs = 
   case treeForm' xs of
      (Just t,[]) -> Just t
      _           -> Nothing


treeForm' :: [LamSymbol a] -> (Maybe (PureLambda a),[LamSymbol a])
treeForm' (Sym_Var a x : xs) = (Just (Var a x),xs)

treeForm' (Sym_Lam a l : xs) = 
   case treeForm' xs of
       (Nothing, xs') -> (Nothing, xs')
       (Just t , xs') -> (Just (Lam a l t),xs')

treeForm' (Sym_App a   : xs) = 
   case treeForm' xs of
        (Nothing, xs') -> (Nothing,xs)
        (Just t1, xs') -> 
           case treeForm' xs' of
               (Nothing, xs'') -> (Nothing,xs'')
               (Just t2, xs'') -> (Just (App a t1 t2),xs'')

treeForm' [] = (Nothing,[])

data LamSearchTree a = 
   LSTNode 
   { node_value  :: [String] -> a
   , lam_subtree :: LamSearchTree a
   , app_subtree :: LamSearchTree a
   , var_subtree :: Array Int (LamSearchTree a)
   }

data NFormSearchTree a = NFST !Int (Array Int (LamSearchTree a)) (NFormSearchTree a)

lookupLinearForm :: [LamSymbol a] -> [String] -> LamSearchTree b -> b
lookupLinearForm (Sym_Lam _ l : xs) ls tree = lookupLinearForm xs (l:ls) (lam_subtree tree)
lookupLinearForm (Sym_App _   : xs) ls tree = lookupLinearForm xs ls     (app_subtree tree)
lookupLinearForm (Sym_Var _ x : xs) ls tree = lookupLinearForm xs ls     ((var_subtree tree) ! x)
lookupLinearForm []                 ls tree = node_value tree ls

lookup_nForm :: [LamSymbol a] -> Int -> NFormSearchTree b -> b
lookup_nForm term n (NFST x arr nfst)
   | n <= x    = lookupLinearForm term [] (arr ! n)
   | otherwise = lookup_nForm term n nfst

buildLamSearchTree :: Int -> [LamSymbol ()] -> ([LamSymbol ()] -> [String] -> a) -> LamSearchTree a
buildLamSearchTree n xs f =
   LSTNode
   { node_value  = f xs 
   , lam_subtree = buildLamSearchTree n (Sym_Lam () "" : xs) f
   , app_subtree = buildLamSearchTree n (Sym_App ()    : xs) f
   , var_subtree = listArray (0,n) [ buildLamSearchTree n (Sym_Var () i : xs) f | i <- [0..n] ]
   }

applyNamesAndReverse :: [LamSymbol ()] -> [String] -> [LamSymbol ()] -> [LamSymbol ()]
applyNamesAndReverse (Sym_Lam () _ : xs) (l:ls) zs = applyNamesAndReverse xs ls (Sym_Lam () l : zs)
applyNamesAndReverse (x:xs) ls zs = applyNamesAndReverse xs ls (x:zs)
applyNamesAndReverse [] [] zs = zs

buildNFormSearchTree :: Int -> Int -> ([LamSymbol ()] -> [String] -> a) -> NFormSearchTree a
buildNFormSearchTree n m f = 
     NFST m (listArray (n,m) [ buildLamSearchTree i [] f | i <- [n..m] ])
            (buildNFormSearchTree (m+1) (m*m) f)

linearEvalMemo :: [LamSymbol ()] -> ([LamSymbol ()],Int)
linearEvalMemo x = inner x
 where memo = buildNFormSearchTree 0 8 aux
       aux xs ls = let ts  = applyNamesAndReverse xs ls [] 
                       t   = fromJust (treeForm ts)
                       in lamEvalF inner undefined t

       inner (xs,n) = lookup_nForm xs n memo

{-
lookupLam :: PureLambda a -> NFormSearchTree b -> b
lookupLam t nfst =
   let (xs,n) = linearForm' t 0
   in lookup_nForm xs n nfst

lamEvalMemo :: PureLambda () -> PureLambda ()
lamEvalMemo x = lookupLam x memo
 where memo = buildNFormSearchTree 0 8 (lamEvalF (\x -> lookupLam x memo) id)
-}

lamEvalMemo :: PureLambda () -> PureLambda ()
lamEvalMemo t = let ts  = linearForm t
                    ts' = linearEvalMemo ts
                    t'  = treeForm ts'
                in fromJust t'