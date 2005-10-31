module Lambda where

import qualified Env as Env

data PureLambda a
   = Lam a String (PureLambda a)
   | App a (PureLambda a) (PureLambda a)
   | Var a Int

-- shows closed lambda forms
instance Show (PureLambda a) where
  show = showLam Env.empty TopContext

data LamContext
   = TopContext
   | AppLeft
   | AppRight
 deriving (Eq)

showLam :: Env.Env -> LamContext -> PureLambda a -> String
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

lamShift :: Int -> Int -> PureLambda a -> PureLambda a
lamShift z shift v@(Var a x)
   | x < z     = v
   | otherwise = Var a (x+shift)

lamShift z shift (Lam a label t) = Lam a label (lamShift (z+1) (shift+1) t)
lamShift z shift (App a t1 t2)   = App a (lamShift z shift t1) (lamShift z shift t2)

lamSubst :: PureLambda a -> Int -> PureLambda a -> PureLambda a
lamSubst subst var v@(Var _ x)
   | x == var  = subst
   | otherwise = v

lamSubst subst var (Lam a label t) = Lam a label (lamShift 0 (-1) (lamSubst (lamShift 0 1 subst) (var+1) t))
lamSubst subst var (App a t1 t2)   = App a (lamSubst subst var t1) (lamSubst subst var t2)

-- single-step normal order reduction
lamReduce :: PureLambda a -> Maybe (PureLambda a)
lamReduce (App _ t@(Lam _ _ t1) t2) = return (lamShift 0 (-1) (lamSubst (lamShift 0 1 t2) 0 t1))
lamReduce (App a t1 t2) = lamReduce t1 >>= \t1' -> return (App a t1' t2)
lamReduce (Lam a l t)   = lamReduce t  >>= \t'  -> return (Lam a l t')
lamReduce (Var _ _)     = Nothing

lamEvalF :: (PureLambda a -> b) -> (PureLambda a -> b) -> PureLambda a -> b
lamEvalF f z x = 
   case lamReduce x of
        Just x' -> f x'
        Nothing -> z x

-- big-step normal order reduction
lamEval :: PureLambda a -> PureLambda a
lamEval = lamEvalF lamEval id

-- creates a list of intermediate steps in a reduction sequence
lamEvalTrace :: PureLambda a -> [PureLambda a]
lamEvalTrace x = lamEvalF ((x:) . lamEvalTrace) (:[]) x
