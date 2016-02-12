{-# LANGUAGE DeriveDataTypeable #-}
module Language.Hopper.Internal.Core.Literal(
    Literal(..)
    ,PrimOpId(..)
    ,ConstrId(..)
    )
where

import Numeric.Natural
import Data.Data
import  Data.Text (Text)

data Literal = LInteger !Integer | LRational !Rational | LNatural !Natural | LText !Text
  deriving(Eq,Ord,Show,Read,Typeable)

-- | ConstrId is the tag name for data type constructors, we dont have those yet
-- likewise, if we want to contemplate type directed name resolution,
-- we will need to do enriched name spacing!
newtype ConstrId  = ConstrId { unConstrId :: Text } deriving (Eq, Show,Typeable,Ord,Read)

-- Primops for a language have names
newtype PrimOpId = PrimopId {unPrimopId :: Text}  deriving  (Eq, Show,Typeable,Ord,Read)
