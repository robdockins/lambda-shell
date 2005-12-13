{- |
 This module defines the pure lambda calculus and
 some associated operations.

 Lambda terms are represented with de Brujin indicies.  Lambdas
 are annotated with a label for the variable that is used when
 displaying.  Lambda terms may be references to let-bound terms;
 These are unfolded in explicit reduction steps.  Let bindings are
 non-recursive; that is, the bound name is not in scope during
 the definition.
-}

module Lambda( 
-- * Type Definitions
  Bindings
, ReductionStrategy

-- * Lamda Term Datatype
, PureLambda (..)


-- * Auxilary Functions
, lookupBinding
, alphaEq
, printLam
, lamSubst

-- * Reduction Strategies
, lamReduceWHNF
, lamReduceHNF
, lamReduceNF
, lamStrictNF

-- * Evaluation Functions
, lamEvalF
, lamEval
, lamEvalTrace
) where

import qualified Env as Env
import qualified Data.Map as Map
import Control.Monad (MonadPlus (..))

type Bindings a l = Map.Map String (PureLambda a l)
lookupBinding name b = Map.findWithDefault (error $ concat ["'",name,"' not bound"]) name b



----------------------------------------------------------------
-- | The type of lambda terms;
--   they are polymorphic in an annotation type \'a\' and the type
--   of labels \'l\'.

data PureLambda a l
   = Lam a l (PureLambda a l)
   | App a (PureLambda a l) (PureLambda a l)
   | Var a Int
   | Binding a String
 deriving (Show)

------------------------------------------------------------------
-- | Alpha equivalance on lambda terms.  Defined in the usual
--   way, except that bindings are compared by name.

alphaEq      :: PureLambda a l
             -> PureLambda a l
             -> Bool

alphaEq (Lam _ _ t1)   (Lam _ _ t2)   = alphaEq t1 t2
alphaEq (App _ x1 y1)  (App _ x2 y2)  = alphaEq x1 x2 && alphaEq y1 y2
alphaEq (Var _ i1)     (Var _ i2)     = i1 == i2
alphaEq (Binding _ n1) (Binding _ n2) = n1 == n2
alphaEq _              _              = False

-------------------------------------------------------------------
-- | Show a lambda term, minimizing parenthises and disambiguating
--   variables in nested scopes with identical labels.

printLam     :: PureLambda a String
             -> String

printLam = showLam Env.empty TopContext


data LamContext
   = TopContext
   | AppLeft
   | AppRight
 deriving (Eq)


showLam      :: Env.Env
             -> LamContext
             -> PureLambda a String
             -> String

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


-----------------------------------------------------------------------------
-- shifts all free variables by a specified amount
-- ancillary function for substitution

lamShift     :: Int
             -> Int
             -> PureLambda a l
             -> PureLambda a l

lamShift c d v@(Var a x)
   | x >= c    = Var a (x+d)
   | otherwise = v

lamShift c d (Lam a label t)  = Lam a label (lamShift (c+1) d t)
lamShift c d (App a t1 t2)    = App a (lamShift c d t1) (lamShift c d t2)
lamShift c d b@(Binding _ _)  = b

------------------------------------------------------------------------------
-- | Capture-avoiding substitution;
--   substitute \'s\' into \'t\', replacing all free variables with index 0.

lamSubst     :: PureLambda a l -- ^ s
             -> PureLambda a l -- ^ t
             -> PureLambda a l

lamSubst s t = lamShift 0 (-1) (lamSubst' (lamShift 0 1 s) 0 0 t)



lamSubst'    :: PureLambda a l
             -> Int
             -> Int
             -> PureLambda a l
             -> PureLambda a l

lamSubst' s var c v@(Var _ x)
   | x == (var+c) = lamShift 0 c s
   | otherwise    = v

lamSubst' s var c (Lam a label t)  = Lam a label (lamSubst' s var (c+1) t)
lamSubst' s var c (App a t1 t2)    = App a (lamSubst' s var c t1) (lamSubst' s var c t2)
lamSubst' s var c b@(Binding _ _)  = b


-------------------------------------------------------------------------------------
-- | The type of reduction strategies.

type ReductionStrategy a l
     = Bindings a l
    -> Bool
    -> PureLambda a l
    -> Maybe (PureLambda a l)

-------------------------------------------------------------------------------------
-- | Single-step normal order reduction to Weak Head Normal Form (WHNF)

lamReduceWHNF :: ReductionStrategy a l

lamReduceWHNF b unfold (App _ (Lam _ _ t1) t2) = Just (lamSubst t2 t1)
lamReduceWHNF b unfold (App a t1 t2)           = lamReduceWHNF b True t1   >>= \t1' -> return (App a t1' t2)
lamReduceWHNF b unfold (Lam a l t)             = Nothing
lamReduceWHNF b unfold (Var _ _)               = Nothing
lamReduceWHNF b unfold (Binding a name)        = if unfold then Just (lookupBinding name b) else Nothing

-------------------------------------------------------------------------------------
-- | Single-step normal order reduction to Head Normal Form (HNF)

lamReduceHNF :: ReductionStrategy a l

lamReduceHNF b unfold (App _ (Lam _ _ t1) t2)  = Just (lamSubst t2 t1)
lamReduceHNF b unfold (App a t1 t2)            = lamReduceHNF b True t1   >>= \t1' -> return (App a t1' t2)
lamReduceHNF b unfold (Lam a l t)              = lamReduceHNF b unfold t  >>= \t'  -> return (Lam a l t')
lamReduceHNF b unfold (Var _ _)                = Nothing
lamReduceHNF b unfold (Binding a name)         = if unfold then Just (lookupBinding name b) else Nothing


--------------------------------------------------------------------------------------
-- | Single-step normal order reduction to Normal Form (NF)

lamReduceNF :: ReductionStrategy a l

lamReduceNF b unfold (App _ (Lam _ _ t1) t2)   = Just (lamSubst t2 t1)
lamReduceNF b unfold (App a t1 t2)             = (lamReduceNF b True t1   >>= \t1' -> return (App a t1' t2))
                                                   `mplus`
                                                 (lamReduceNF b unfold t2 >>= \t2' -> return (App a t1 t2'))
lamReduceNF b unfold (Lam a l t)               = lamReduceNF b unfold t   >>= \t'  -> return (Lam a l t')
lamReduceNF b unfold (Var _ _)                 = Nothing
lamReduceNF b unfold (Binding a name)          = if unfold then Just (lookupBinding name b) else Nothing

---------------------------------------------------------------------------------------
-- | Single-step applicative order reduction to Normal Form (NF)

lamStrictNF :: ReductionStrategy a l

lamStrictNF b unfold (App a (Lam al l t1) t2)  = (lamStrictNF b True t2 >>= \t2' -> return (App a (Lam al l t1) t2'))
                                                   `mplus`
                                                 (Just (lamSubst t2 t1))
lamStrictNF b unfold (App a t1 t2)             = (lamStrictNF b True t1   >>= \t1' -> return (App a t1' t2))
                                                   `mplus`
                                                 (lamStrictNF b unfold t2 >>= \t2' -> return (App a t1 t2'))
lamStrictNF b unfold (Lam a l t)               = lamStrictNF b unfold t   >>= \t'  -> return (Lam a l t')
lamStrictNF b unfold (Var _ _)                 = Nothing
lamStrictNF b unfold (Binding a name)          = if unfold then Just (lookupBinding name b) else Nothing

---------------------------------------------------------------------------------------
-- | Helper for various kinds of evaluation.  Applies the function \'z\' if
--   the evaluation strategy has terminated, and applies \'f\' to the
--   reduced term otherwise.

lamEvalF     :: Bindings a l             -- ^ A set of bindings for unfolding
             -> Bool                     -- ^ Apply full unfolding?
             -> ReductionStrategy a l    -- ^ Reduction strategy to use
             -> (PureLambda a l -> b)    -- ^ f
             -> (PureLambda a l -> b)    -- ^ z
             -> PureLambda a l           -- ^ The term to reduce
             -> b

lamEvalF b unfold reduce f z x =
   case reduce b unfold x of
        Just x' -> f x'
        Nothing -> z x

-------------------------------------------------------------------------------------
-- | Big-step reduction; that is, apply the reduction strategy until
--   it fails to reduce any futher.

lamEval     :: Bindings a l            -- ^ A set of bindings for unfolding
             -> Bool                   -- ^ Apply full unfolding ?
             -> ReductionStrategy a l  -- ^ Reduction strategy to use
             -> PureLambda a l         -- ^ The term to reduce             
             -> PureLambda a l         -- ^ The evaluated term

lamEval bind unfold red = eval
  where evalF  = lamEvalF bind unfold red
        eval x = evalF eval id x


-------------------------------------------------------------------------------------
-- | Traced evaluation; the result is a list of the reduction
--   steps taken by the given reduction stragegy.  A non-terminating
--   term (under the given strategy) will result an infinite list.

lamEvalTrace :: Bindings a l          -- ^ A set of bindings for unfolding
             -> Bool		      -- ^ Apply full unfolding ?	   
             -> ReductionStrategy a l -- ^ Reduction strategy to use	   
             -> PureLambda a l	      -- ^ The term to reduce             
             -> [PureLambda a l]      -- ^ The list of reductions

lamEvalTrace bind unfold red = eval
  where evalF  = lamEvalF bind unfold red
        eval x = evalF ((x:) . eval) (:[]) x
