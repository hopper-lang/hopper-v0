{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
--{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric, LambdaCase,TypeOperators #-}

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE BangPatterns #-}

{- |
the core type theory of Hopper is based on
connor mcrbride's paper https://personal.cis.strath.ac.uk/conor.mcbride/pub/Rig.pdf
accordingly we need to provide the applicable machinery !

what are some Laws that instances must have?

1) if  p <= 0 then p == 0
  thus isZero p = p <= 0
2) <= needs to be reflexive, transitive, and play nice with Rig multiplication and factorization rules as follows

-}
module Hopper.Internal.Type.Relevance where

import qualified Prelude as P  -- (Eq(..),Read,Show,Num(..),Integer,Bool)
import Prelude (Eq(..), Maybe(..),Bool(..),Ord,Num,Show,Read,($),not,(&&), (||))
import Numeric.Natural
import GHC.Integer.GMP.Internals (gcdInteger)
import GHC.Generics
import Data.Data
import Algebra.PartialOrd
import Algebra.Lattice
--import JoinSemiLattice

infixl 7 *
infixl 6 +
--infix 4 <=

data GCD a = GCD {extractGCD :: !a, leftCoprime :: !a, rightCoprime :: !a }
  deriving(Eq,Ord,P.Show,P.Read)
--checkGCD :: (Eq a, Rig a) => a -> a -> GCD a -> Bool
--ched
gcdNat :: Natural -> Natural -> Maybe  (GCD Natural)
gcdNat a b  |  (a== 0 ||  b == 0) =  Nothing -- if either factor is zero, gcd is zero
gcdNat a b  = Just $ P.undefined theGCD
  where
   theGCD :: Natural
   theGCD = P.fromInteger $ gcdInteger (P.fromIntegral a ) (P.fromIntegral b)
-- NB: can't make Integer an instance of Rig because we want
--- x <= 0 to imply zero
class Rig a where
  zero :: a
  default zero :: Num a => a
  zero = P.fromInteger 0
  {-# INLINE zero #-}
  one :: a
  default one :: Num a => a
  one = P.fromInteger 1
  {-# INLINE one #-}
  (*) :: a -> a -> a
  default (*) :: Num a =>  a  -> a -> a
  (*) = (P.*)
  {-# INLINE (*) #-}
  (+) :: a -> a -> a
  default (+) :: Num a => a -> a -> a
  (+) = (P.+)
  {-# INLINE (+) #-}

instance Rig Natural

data Relevance =
    Zero  -- irrelevant
    | One -- linear
    | Omega -- normal / any usage between 0 and \infty!
  deriving(Eq,Ord,Show,Read,Data,Typeable,Generic)
  -- i define vanilla ord
instance Rig Relevance where
  one = One
  zero = Zero
  Zero + (!a) = a --- zero doesn't change a thing
  One + Zero = One
  One + One = Omega
  One + Omega = Omega
  Omega + Zero = Omega --- omega plus anything is zero
  Omega + One = Omega
  Omega + Omega = Omega
  Zero * (!_) = Zero
  One * (!a) = a
  Omega * Zero = Zero
  Omega * (!_) = Omega

incomparableElements :: PartialOrd a => a -> a -> Bool
incomparableElements a b = (not  $ a `leq`b) && (not $ b `leq` a)
-- this comes up with the lattice structure we're using here!
--instance  PartialOrd Natural

-- we have incomparableElements Zero One == True
-- for our model of relevance
instance PartialOrd Relevance where
  Zero `leq` Omega = True
  Zero `leq` Zero = True
  Zero `leq` One = False --- Zero and One are incomparable, maybe?
  One `leq` Omega = True
  One `leq` One = True
  One `leq` Zero = False
  Omega `leq` Omega = True
  Omega `leq` One = False
  Omega `leq` Zero = False


{-# SPECIALIZE isZero :: Relevance -> Bool #-}
isZero :: (Rig a,PartialOrd a)=> a -> Bool
isZero a = if a `leq` zero then True else False

{-
our "Relevance type" kinda is a subset of the lattice induced by
the collection of sets {}, {1}, {0}, and {0,1}, but without {}

ie our partial order is the one modeled by the collection of sets
{0}, {1}, {0,1} with ordering by the subset relation and the Join operator
being set Union
what would augmenting our partial order with a member corresponding to {}, the empty set,
mean?
Would that come up in external language elaboration when we have a type error
in unification because of mismatch in demand/useages?
-}

-- we are a Joint lattice becquse  Omega \/ x = Omega <--> x `leq` Omega, which is always true
instance JoinSemiLattice Relevance where
    Zero \/ Zero = Zero
    Zero \/ One = Omega
    Zero \/ Omega = Omega
    One \/ Zero = Omega --- this is the funny looking spot here :)
    One \/ One = One
    One \/ Omega = Omega
    Omega  \/ Zero = Omega
    Omega \/ One = Omega
    Omega \/ Omega = Omega



