{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Hopper.Internal.Core.Closed
    (Closed(..)
    ,closedPoly
    )
where

import Unsafe.Coerce(unsafeCoerce)
import Data.Typeable

newtype Closed f
  = Closed { unClosed :: forall a . f a  }
  deriving Typeable

closedPoly :: Traversable f => f a -> Maybe (Closed f )
closedPoly = \x -> unsafeCoerce $ traverse (const Nothing) x
--- this is safe because Closed is a new type, so it has NO runtime rep
--- the safe Coerce machinery doesn't work because of the higher rank type
