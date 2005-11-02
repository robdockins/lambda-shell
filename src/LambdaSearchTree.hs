module LambdaSearchTree
( lamEvalMemo
) where

import Maybe (fromJust)
import Data.Array
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap

import Lambda

data LamSymbol a l
  = Sym_Lam a l
  | Sym_App a
  | Sym_Var a Int
  | Sym_Bind a String

instance Show l => Show (LamSymbol a l) where
   show (Sym_Lam _ l)  = "Sym_Lam "++(show l)
   show (Sym_App _)    = "Sym_App"
   show (Sym_Var _ x)  = "Sym_Var "++(show x)
   show (Sym_Bind _ n) = "Sym_Bind "++n

linearForm :: PureLambda a l -> [LamSymbol a l]
linearForm t = let (_,xs) = linearForm' t 0 in xs

linearForm' :: PureLambda a l -> Int -> (Int,[LamSymbol a l])
linearForm' (Lam a l t)   n = let (n',xs) = linearForm' t n in (n',Sym_Lam a l : xs)

linearForm' (App a t1 t2) n =
   let (n' ,xs1) = linearForm' t1 n
       (n'',xs2) = linearForm' t2 n'
   in (n'',Sym_App a : xs1 ++ xs2)

linearForm' (Var a x)     n = (max n x,[Sym_Var a x])
linearForm' (Binding a x) n = (n,[Sym_Bind a x])

treeForm :: [LamSymbol a l] -> Maybe (PureLambda a l)
treeForm xs =
   case treeForm' xs of
      (Just t,[]) -> Just t
      _           -> Nothing


treeForm' :: [LamSymbol a l] -> (Maybe (PureLambda a l),[LamSymbol a l])
treeForm' (Sym_Var a x  : xs) = (Just (Var a x),xs)
treeForm' (Sym_Bind a x : xs) = (Just (Binding a x),xs)

treeForm' (Sym_Lam a l  : xs) =
   case treeForm' xs of
       (Nothing, xs') -> (Nothing, xs')
       (Just t , xs') -> (Just (Lam a l t),xs')

treeForm' (Sym_App a    : xs) =
   case treeForm' xs of
        (Nothing, xs') -> (Nothing,xs)
        (Just t1, xs') ->
           case treeForm' xs' of
               (Nothing, xs'') -> (Nothing,xs'')
               (Just t2, xs'') -> (Just (App a t1 t2),xs'')

treeForm' [] = (Nothing,[])

data LamSearchTree a =
   LSTNode
   { node_value   :: a
   , lam_subtree  :: LamSearchTree a
   , app_subtree  :: LamSearchTree a
   , var_subtree  :: Array Int (LamSearchTree a)
   , bind_subtree :: Map.Map String (LamSearchTree a)
   }

data NFormSearchTree a = NFST !Int (Array Int (LamSearchTree a)) (NFormSearchTree a)

type LinearForm = [LamSymbol () (Either Int String)]
type NForm      = (Int,LinearForm)

lookupLinearForm :: LinearForm -> LamSearchTree b -> b
lookupLinearForm (Sym_Lam _ _  : xs) tree = lookupLinearForm xs (lam_subtree tree)
lookupLinearForm (Sym_App _    : xs) tree = lookupLinearForm xs (app_subtree tree)
lookupLinearForm (Sym_Var _ x  : xs) tree = lookupLinearForm xs ((var_subtree tree)  ! x)
lookupLinearForm (Sym_Bind _ x : xs) tree = lookupLinearForm xs ((bind_subtree tree) Map.! x)
lookupLinearForm []                  tree = node_value tree

lookup_nForm :: NForm -> NFormSearchTree b -> b
lookup_nForm t@(n,term) (NFST x arr nfst)
   | n <= x    = lookupLinearForm term (arr ! n)
   | otherwise = lookup_nForm t nfst

buildLamSearchTree :: Bindings () (Either Int String) -> Int -> Int -> LinearForm -> (LinearForm -> a) -> LamSearchTree a
buildLamSearchTree b n l xs f =
   LSTNode
   { node_value   = f (reverse xs)
   , lam_subtree  = buildLamSearchTree b n (l+1) (Sym_Lam () (Left l) : xs) f
   , app_subtree  = buildLamSearchTree b n l     (Sym_App ()          : xs) f
   , var_subtree  = listArray (0,n) [ buildLamSearchTree b n l (Sym_Var () i : xs) f | i <- [0..n] ]
   , bind_subtree = Map.mapWithKey (\name _ -> buildLamSearchTree b n l (Sym_Bind () name : xs) f) b
   }

buildNFormSearchTree :: Bindings () (Either Int String) -> Int -> Int -> (LinearForm -> a) -> NFormSearchTree a
buildNFormSearchTree b n m f =
     NFST m (listArray (n,m) [ buildLamSearchTree b i 0 [] f | i <- [n..m] ])
            (buildNFormSearchTree b (m+1) (m*m) f)

nFormEvalMemo :: Bindings () (Either Int String) -> Bool -> NForm -> NForm
nFormEvalMemo b unfold nform = lookup_nForm nform memo
  where memo = buildNFormSearchTree b 0 8 eval
        eval xs =
           let x = maybe (error $ "bad linear form"++(show xs)) id (treeForm xs)
           in lamEvalF b unfold (\t -> lookup_nForm (linearForm' t 0) memo) (\t -> linearForm' t 0) x

removeLabels :: [LamSymbol () String] -> (LinearForm,IntMap.IntMap String)
removeLabels xs = f 0 xs [] IntMap.empty
  where f n []                 zs map = (reverse zs,map)
        f n (Sym_Lam a l  : xs) zs map = f (n+1) xs (Sym_Lam a (Left n) : zs) (IntMap.insert n l map)
        f n (Sym_App a    : xs) zs map = f n     xs (Sym_App a          : zs) map
        f n (Sym_Var a x  : xs) zs map = f n     xs (Sym_Var a x        : zs) map
        f n (Sym_Bind a x : xs) zs map = f n     xs (Sym_Bind a x       : zs) map

restoreLabels :: LinearForm -> IntMap.IntMap String -> [LamSymbol () String]
restoreLabels xs labelMap = f xs []
  where f []                         zs = reverse zs
        f (Sym_Lam a (Left i)  : xs) zs = f xs (Sym_Lam a (getLabel i) : zs)
        f (Sym_Lam a (Right l) : xs) zs = f xs (Sym_Lam a l            : zs)
        f (Sym_App a           : xs) zs = f xs (Sym_App a              : zs)
        f (Sym_Var a x         : xs) zs = f xs (Sym_Var a x            : zs)
        f (Sym_Bind a x        : xs) zs = f xs (Sym_Bind a x           : zs)

        getLabel i = IntMap.findWithDefault (error "label not found: "++(show i)) i labelMap

liftLabels :: PureLambda () String -> PureLambda () (Either Int String)
liftLabels (Var a x)       = Var a x
liftLabels (Binding a x)   = Binding a x
liftLabels (Lam a l t)     = Lam a (Right l) (liftLabels t)
liftLabels (App a t1 t2)   = App a (liftLabels t1) (liftLabels t2)

lamEvalMemo :: Bindings () String -> Bool -> PureLambda () String -> PureLambda () String
lamEvalMemo b unfold t =
	let b'            = Map.map liftLabels b
            (n,xs)        = linearForm' t 0
            (xs',nameMap) = removeLabels xs
            (_,xs'')      = nFormEvalMemo b' unfold (n,xs')
            xs'''         = restoreLabels xs'' nameMap
        in maybe (error $ "bad linear form "++(show xs)) id (treeForm xs''')
