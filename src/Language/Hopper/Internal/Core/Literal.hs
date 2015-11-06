{-# LANGUAGE DeriveDataTypeable #-}
module Language.Hopper.Internal.Core.Literal where

import Numeric.Natural
import Data.Typeable
import Data.Data

data Literal = LInteger !Integer | LRational !Rational | LNatural !Natural
  deriving(Eq,Ord,Show,Read,Data,Typeable)
