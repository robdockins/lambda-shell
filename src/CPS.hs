{-
 -   The Lambda Shell, an interactive environment for evaluating pure untyped lambda terms.
 -   Copyright (C) 2005-2006, Robert Dockins
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

{- | 
  This module defines CPS transformations on lambda terms.
-}

module CPS
( simple_cps
, eta_cps
-- , onepass_cps
, CPS
) where

import Lambda

type CPS 
    =  Monad m 
    => Bindings () String
    -> PureLambda () String
    -> m (PureLambda () String)

-- | The simple CPS transform defined by Plotkin
simple_cps :: CPS

simple_cps b t = do
    x <- do_simple_cps b t
    return (App () x (Lam () "q" (Var () 0)))

do_simple_cps :: CPS

do_simple_cps b (Binding _ name) =
    lookupBindingM name b >>= \t -> do_simple_cps b t

do_simple_cps b (Var _ i) = 
    return (Lam () "k" $ App () (Var () 0) $ (Var () (i+1)))

do_simple_cps b (Lam _ l t) = do
    t' <- do_simple_cps b (lamShift 1 1 t)
    return
      (Lam () "k" $ App () (Var () 0) $ Lam () l t')

do_simple_cps b (App _ t1 t2) = do
    t1' <- do_simple_cps b (lamShift 0 1 t1)
    t2' <- do_simple_cps b (lamShift 0 2 t2)
    return
      (Lam () "k" $ App () t1' $
         Lam () "m" $ App () t2' $
           Lam () "n" $
             App () (App () (Var () 1) (Var () 0)) (Var () 2))


-- | A version of Plotkin's CPS transform with additional
--   eta expansions, preparing for the one-pass
--   simplifying transform
eta_cps :: CPS
eta_cps b t = do
   x <- do_eta_cps b t
   return (App () x (Lam () "q" (Var () 0)))

do_eta_cps :: CPS

do_eta_cps b (Binding _ name) =
    lookupBindingM name b >>= \t -> do_simple_cps b t

do_eta_cps b (Var _ i) =
    return (Lam () "k" $ App () (Var () 0) $ (Var () (i+1)))


do_eta_cps b (Lam _ l t) = do
    t' <- do_eta_cps b (lamShift 2 1 (lamShift 0 1 t))
    return
      (Lam () "k" $ App () (Var () 0) $
        Lam () l $
          Lam () "kk" $ App () t' $
            Lam () "m" $ App () (Var () 1) (Var () 0)
      )


do_eta_cps b (App _ t1 t2) = do
    t1' <- do_eta_cps b (lamShift 0 1 t1)
    t2' <- do_eta_cps b (lamShift 0 2 t2)
    return
      (Lam () "k" $ App () t1' $
        Lam () "m" $ App () t2' $
          Lam () "n" $
            App () (App () (Var () 1) (Var () 0)) $
              Lam () "a" $ App () (Var () 3) (Var () 0)
      )




{- I can't figure out how to make this work,
   so it's commented out for now

-- | one-pass simplifying CPS, due to Danvy and Filinski
onepass_cps :: CPS
onepass_cps b t = return (do_onepass_cps b t id)

do_onepass_cps
    :: Bindings () String
    -> PureLambda () String
    -> (PureLambda () String -> PureLambda () String)
    -> PureLambda () String

do_onepass_cps b (Binding _ name) k =
   do_onepass_cps b (lookupBinding name b) k

do_onepass_cps b t@(Var _ i) k = k t

do_onepass_cps b (Lam _ l t) k =
   k (Lam () l $
       Lam () "k" $
         do_onepass_cps b (lamShift 0 1 t)
           (\m -> App () (Var () 0) m)
     )

do_onepass_cps b (App _ t1 t2) k =
   do_onepass_cps b t1 (\m ->
	do_onepass_cps b t2 (\n ->
	    App () (App () m n) (Lam () "a" (k (Var () 0))) ))




do_onepass_cps
    :: Monad m
    => Bindings () String
    -> PureLambda () String
    -> (PureLambda () String -> m (PureLambda () String))
    -> m (PureLambda () String)

do_onepass_cps b (Binding _ name) k =
   lookupBindingM name b >>= \t -> do_onepass_cps b t k

do_onepass_cps b t@(Var _ i) k = k t

do_onepass_cps b (Lam _ l t) k = do
   t' <- do_onepass_cps_tail b (lamShift (lamShift 0 1 t) (Var () 0)
   k (Lam () l $ Lam () "k" t')
   
do_onepass_cps b (App _ t1 t2) k =
   do_onepass_cps b t1 (\m -> do_onepass_cps b t2 (\n -> do
       z <- k (Var () 0)
       return (App () (App () m n) (Lam () "a" z)) ))

do_onepass_cps_tail
    :: Monad m
    => Bindings () String
    -> PureLambda () String
    -> PureLambda () String
    -> m (PureLambda () String)

do_onepass_cps_tail b (Binding _ name) k =
   lookupBindingM name b >>= \t -> do_onepass_cps_tail b t k

do_onepass_cps_tail b t@(Var _ _) k = return (App () k t)

do_onepass_cps_tail b (Lam _ l t) k = do
   t' <- do_onepass_cps_tail b (lamShift 0 1 t) (Var () 0) 
   return (App () k $ Lam () l $ Lam () "k" t')

do_onepass_cps_tail b (App _ t1 t2) k =
   do_onepass_cps b t1 (\m -> do_onepass_cps b t2 (\n -> 
      return (App () (App () m n) k)))

-}
