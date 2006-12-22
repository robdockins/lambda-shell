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
, onepass_cps
, CPS
) where

import Lambda

type CPS m
     = Bindings () String
    -> PureLambda () String
    -> m (PureLambda () String)

-- | The simple CPS transform defined by Plotkin
simple_cps :: Monad m => CPS m

simple_cps b t = do
    x <- do_simple_cps b t
    return (App () x (Lam () "q" (Var () 0)))

do_simple_cps :: Monad m => CPS m

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
eta_cps :: Monad m => CPS m
eta_cps b t = do
   x <- do_eta_cps b t
   return (App () x (Lam () "q" (Var () 0)))

do_eta_cps :: Monad m => CPS m

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




-- | The \"one-pass\" properly-tail-recursive CPS tranform due to Danvy and Filinski,
--   from the paper \"Representing Control: A Study of the CPS Transformation\",
--   in /Mathematical Structures in Computer Science/, 1991.
--
--   Here is is actually implemented as a two-pass tranform.
--   In the first pass we create the eta-expanded version and note
--   which redexes are adminstrative.  In the second pass all administrative
--   redexes are reduced, leaving only the dynamic redexes.

onepass_cps :: Monad m => CPS m
onepass_cps b t = do
   x <- do_onepass_cps b t
   simplify_onepass (App True x (Lam True "q" (Var True 0)))


simplify_onepass
    :: Monad m
    => PureLambda Bool String
    -> m (PureLambda () String)

simplify_onepass (Binding _ _) = fail "bug: binding found in simplify_onepass"

simplify_onepass (Var False i)     = return (Var () i)
simplify_onepass (Lam False l t)   = simplify_onepass t >>= \t' -> return (Lam () l t')
simplify_onepass (App False t1 t2) = do
    t1' <- simplify_onepass t1
    t2' <- simplify_onepass t2
    return (App () t1' t2')

simplify_onepass (App True (Lam True _ t) s) = simplify_onepass (lamSubst s t)
simplify_onepass t  = fail $ "bug: found unexpected administrative terms in simplify_onepass\n"++(show t)


do_onepass_cps
    :: Monad m
    => Bindings () String
    -> PureLambda () String
    -> m (PureLambda Bool String)

do_onepass_cps b (Binding _ name) =
     lookupBindingM name b >>= \t -> do_onepass_cps b t

do_onepass_cps b (Var _ i) =
     return (Lam True "k" $ App True (Var True 0) $ (Var False (i+1)))

do_onepass_cps b (Lam _ l t) = do
    t' <- do_onepass_cps_tail b (lamShift 2 1 (lamShift 0 1 t))
    return
       (Lam True "k0" $ App True (Var True 0) $
          Lam False l $ Lam False "k" $ App True t' $ (Var False 0)
       )

do_onepass_cps b (App _ t1 t2) = do
    t1' <- do_onepass_cps b (lamShift 0 1 t1)
    t2' <- do_onepass_cps b (lamShift 0 2 t2)
    return
        (Lam True "k0" $ App True t1' $
           Lam True "m0" $ App True t2' $
             Lam True "n" $
               App False (App False (Var True 1) (Var True 0)) $
                 Lam False "a" $ App True (Var True 3) (Var False 0)
        )


do_onepass_cps_tail
    :: Monad m
    => Bindings () String
    -> PureLambda () String
    -> m (PureLambda Bool String)

do_onepass_cps_tail b (Var _ i) =
    return (Lam True "k0" (App False (Var True 0) (Var False (i+1))))

do_onepass_cps_tail b (Lam _ l t) = do
    t' <- do_onepass_cps_tail b (lamShift 2 1 (lamShift 0 1 t))
    return
      (Lam True "k0" $ App False (Var True 0) $
         Lam False l $ Lam False "k" $ App True t' $ (Var False 0)
      )

do_onepass_cps_tail b (App _ t1 t2) = do
    t1' <- do_onepass_cps b (lamShift 0 1 t1)
    t2' <- do_onepass_cps b (lamShift 0 2 t2)
    return
      (Lam True "k0" $ App True t1' $
         Lam True "m" $ App True t2' $
           Lam True "n" $
             App False (App False (Var True 1) (Var True 0))
               (Var True 2)
      )
