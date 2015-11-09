{-# LANGUAGE DeriveDataTypeable #-}
module Language.Hopper.Internal.Core.Literal where

import Numeric.Natural
import Data.Typeable
import Data.Data

data Literal = LInteger !Integer | LRational !Rational | LNatural !Natural

-- should we add primop namessss?
  deriving(Eq,Ord,Show,Read,Data,Typeable)
