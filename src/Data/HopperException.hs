{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
module Data.HopperException where

import Data.Typeable (Typeable, cast)

data SomeHopperException where
  SomeHopperException :: forall e. HopperException e => e -> SomeHopperException
  deriving Typeable

instance Show SomeHopperException where
  showsPrec p (SomeHopperException e) = showsPrec p e

class (Typeable e, Show e) => HopperException e where
  toHopperException :: e -> SomeHopperException
  fromHopperException :: SomeHopperException -> Maybe e

  toHopperException = SomeHopperException
  fromHopperException (SomeHopperException e) = cast e

instance HopperException SomeHopperException where
  toHopperException she = she
  fromHopperException = Just
