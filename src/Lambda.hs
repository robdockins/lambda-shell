{-# OPTIONS -fglasgow-exts #-}

module Lambda where

import qualified Env as Env
import qualified Data.Map as Map

type Bindings a l = Map.Map String (PureLambda a l)

{-
 Lambda terms are represented with de Brujin indicies.  Lambdas
 are annotated with a label for the variable that is used when
 displaying.  Lambda terms may be references to let-bound terms;
 These are unfolded in explicit reduction steps.  Let bindings are
 non-recursive; that is, the bound name is not in scope during
 the definition.
-}


----------------------------------------------------------------
-- the type of lambda terms
-- they are polymorphic in an annotation type "a" and the type
-- of labels "l"

data PureLambda a l
   = Lam a l (PureLambda a l)
   | App a (PureLambda a l) (PureLambda a l)
   | Var a Int
   | Binding a String

------------------------------------------------------------------
-- alpha equivalance on lambda terms

alphaEq      :: PureLambda a l 
             -> PureLambda a l 
             -> Bool

alphaEq (Lam _ _ t1)   (Lam _ _ t2)   = alphaEq t1 t2
alphaEq (App _ x1 y1)  (App _ x2 y2)  = alphaEq x1 x2 && alphaEq y1 y2
alphaEq (Var _ i1)     (Var _ i2)     = i1 == i2
alphaEq (Binding _ n1) (Binding _ n2) = n1 == n2


-------------------------------------------------------------------
-- show a lambda term, minimizing parenthises and disambiguating
-- variables in nested scopes with identical labels

showLam      :: Env.Env
             -> LamContext
             -> PureLambda a String
             -> String

data LamContext
   = TopContext
   | AppLeft
   | AppRight
 deriving (Eq)

showLam env c (Binding _ name) = name
showLam env c (Var _ x)        = Env.lookup x env
showLam env c (App _ t1 t2)    = 
   parenIf (c == AppRight) $ 
      concat [showLam env AppLeft t1
             ," "
             ,showLam env AppRight t2
             ]

showLam env c (Lam _ label t) = 
    let env' = Env.insert label env
    in parenIf (c == AppLeft) $ 
          concat ["\\"
                 ,Env.lookup 0 env'
                 ,". "
                 ,showLam env' TopContext t
                 ]

parenIf :: Bool -> String -> String
parenIf False x = x
parenIf True  x = "("++x++")"


----------------------------------------------------------------------------
-- Show instance for PureLambda defined in terms of showLam
-- ugh, requires glasgow-exts

instance Show (PureLambda a String) where
  show = showLam Env.empty TopContext

-----------------------------------------------------------------------------
-- shifts all free variables by a specified amount
-- ancillary function for substitution

lamShift     :: Int 
             -> Int 
             -> PureLambda a l 
             -> PureLambda a l

lamShift z shift v@(Var a x)
   | x < z     = v
   | otherwise = Var a (x+shift)

lamShift z shift (Lam a label t)  = Lam a label (lamShift (z+1) (shift+1) t)
lamShift z shift (App a t1 t2)    = App a (lamShift z shift t1) (lamShift z shift t2)
lamShift z shift b@(Binding _ _)  = b

------------------------------------------------------------------------------
-- capture-avoiding substitution

lamSubst     :: PureLambda a l 
             -> Int 
             -> PureLambda a l 
             -> PureLambda a l

lamSubst subst var v@(Var _ x)
   | x == var  = subst
   | otherwise = v

lamSubst subst var (Lam a label t)  = Lam a label (lamShift 0 (-1) (lamSubst (lamShift 0 1 subst) (var+1) t))
lamSubst subst var (App a t1 t2)    = App a (lamSubst subst var t1) (lamSubst subst var t2)
lamSubst subst var b@(Binding _ _)  = b


--------------------------------------------------------------------------------
-- single-step normal order reduction

lamReduce    :: Bindings a l 
             -> Bool 
             -> PureLambda a l 
             -> Maybe (PureLambda a l)

-- standard beta-reduction
lamReduce b unfold (App _ t@(Lam _ _ t1) t2) = return (lamShift 0 (-1) (lamSubst (lamShift 0 1 t2) 0 t1))

-- reduce on the left side of applications; force unfolding to expose further redexes
lamReduce b unfold (App a t1 t2)     = lamReduce b True t1   >>= \t1' -> return (App a t1' t2)

-- reduce under lambda 
lamReduce b unfold (Lam a l t)       = lamReduce b unfold t  >>= \t'  -> return (Lam a l t')

-- variables don't reduce
lamReduce b unfold (Var _ _)         = Nothing

-- unfold bindings if we need them for further evaluation, or if full 
-- unfolding is requested
lamReduce b unfold (Binding a name)  = 
    if unfold 
       then return (Map.findWithDefault (error $ concat ["'",name,"' not bound"]) name b)
       else Nothing


---------------------------------------------------------------------------------------
-- helper for various kinds of full evaluation

lamEvalF     :: Bindings a l 
             -> Bool 
             -> (PureLambda a l -> b) 
             -> (PureLambda a l -> b) 
             -> PureLambda a l -> b

lamEvalF b unfold f z x = 
   case lamReduce b unfold x of
        Just x' -> f x'
        Nothing -> z x

-------------------------------------------------------------------------------------
-- big-step normal order reduction

lamEval      :: Bindings a l 
             -> Bool 
             -> PureLambda a l 
             -> PureLambda a l

lamEval b unfold = lamEvalF b unfold (lamEval b unfold) id

-------------------------------------------------------------------------------------
-- creates a list of intermediate steps in a reduction sequence

lamEvalTrace :: Bindings a l 
             -> Bool 
             -> PureLambda a l 
             -> [PureLambda a l]

lamEvalTrace b unfold x = lamEvalF b unfold ((x:) . lamEvalTrace b unfold) (:[]) x
