{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric, LambdaCase #-}

module Hopper.Internal.Core.NormalizeANF where


import Hopper.Internal.Core.OldANF
import Data.Data
-- put normalizer here

{-

 Either (NeutralSyntax GG a) (OrdinaryValue a)

-}
{-
why can't it derive functor? this aint a gadt!
or foldable or traversable
is this a ghc 7.10 bug? investigate and report when time permits
-}
data NeutralTermsANF gv a
    =  NeutVarANF  !gv
    | NeutralComp (OldAppAnf a) -- see notes at AppANF for when these constitute neutral terms
    -- this doesn't guarantee that one of the args is a neutral term
    -- but one value on the heap MUST be a neutral term,
    --- for a primapp to be a neutral term
       deriving ( Ord,Functor,Foldable,Traversable,Typeable,Eq,Read,Show )
{-

our HEAP Value TYPE will be
    Either (Value Ref)  (NeutralTermsANF Text Ref)
-}


-- $(deriveBifunctor ''NeutralTermsANF)

-- $(deriveBifoldable ''NeutralTermsANF)

-- $(deriveBitraversable ''NeutralTermsANF)
{-
instance Functor (NeutralTermsANF gv) where
    fmap = \ f x  -> second f x
    {-# INLINE fmap #-}
instance Foldable (NeutralTermsANF gv) where
    foldMap f =  \x ->   foldMap f (WrapBifunctor x)
    # INLINE foldMap #
instance Traversable(NeutralTermsANF gv) where
    traverse f = \x -> fmap   unwrapBifunctor $ traverse f (WrapBifunctor x)
    {-# INLINE  traverse  #-}

-}

{-
  eventually our case construct will need to be added here,
  and roughly  only  stuck when we have
      case neutralterm of
        stuff -> something
        ....
    It is OK for some / all

we DO NOT need to have LET be explicit, because in our USAGE, we have
EXPLICIT SHARING VIA THE HEAP, so reflecting back to CORE/Term syntax
entails identifying the Lowest Common ancestor  of the subtrees of the neutral
term graph that mention the same heap value / netural term syntax to recover sharing
-}
