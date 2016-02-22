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
2) <= needs to be reflexive, transitive, and play nice with
-}
module Hopper.Internal.Type.Relevance where

import qualified Prelude as P  -- (Eq(..),Read,Show,Num(..),Integer,Bool)
import Prelude (Eq,Bool(..),Ord,Num,Show,Read,($),not,(&&))
import Numeric.Natural
import GHC.Integer.GMP.Internals (gcdInteger)
import GHC.Generics
import Data.Data

infixl 7 *
infixl 6 +
infix 4 <=

data GCD a = GCD {extractGCD :: !a, leftCoprime :: !a, rightCoprime :: !a }
  deriving(Eq,Ord,P.Show,P.Read)
--checkGCD :: (Eq a, Rig a) => a -> a -> GCD a -> Bool
--ched
gcdNat :: Natural -> Natural -> GCD Natural
gcdNat a b = P.undefined theGCD
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

data Relevance = Zero | One | Omega
  deriving(Eq,Ord,Show,Read,Data,Typeable,Generic)
  -- i define vanilla ord
instance Rig Relevance where
  one = One
  zero = Zero
  Zero + (!a) = a
  One + Zero = One
  One + One = Omega
  One + Omega = Omega
  Omega + (!_) = Omega
  Zero * (!_) = Zero
  One * (!a) = a
  Omega * Zero = Zero
  Omega * (!_) = Omega
class (Eq a, Rig a )=> PartialOrd a where
  -- this is a weak or perhaps even "partial" order
  (<=) :: a -> a -> Bool
  default (<=) :: Ord a => a -> a -> Bool
  (<=) = (P.<=)
  {-# INLINE (<=)#-}

incomparableElements :: PartialOrd a => a -> a -> Bool
incomparableElements a b = (not  $ a <= b) && (not $ b <= a)
-- this comes up with the lattice structure we're using here!
instance  PartialOrd Natural
instance PartialOrd Relevance where
  Zero <= Omega = True
  Zero <= Zero = True
  Zero <= One = False --- YES, surprising but important
  One <= Omega = True
  One <= One = True
  One <= Zero = False
  Omega <= Omega = True
  Omega <= One = False
  Omega <= Zero = False



