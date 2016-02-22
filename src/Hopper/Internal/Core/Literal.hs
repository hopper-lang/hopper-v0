{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}

{- |
Design note:
for now `Hopper.Internal.Core.Literal` corresponds specifically with built in datatypes
and operations whose reduction count complexity must be wired in directly,
along with

-}


module Hopper.Internal.Core.Literal
  ( Literal(..)
  , PrimOpId(..)
  , ConstrId(..)
  , evalTotalPrimopCode
  , integerLog
  ) where

import Data.Data
import Data.Text (Text)
import Data.Ratio (numerator, denominator)
import GHC.Exts (Word(W#))
import GHC.Generics
import GHC.Integer.GMP.Internals (sqrInteger, lcmInteger, gcdInteger,
                                  gcdExtInteger, recipModInteger,
                                  sizeInBaseInteger)
import GHC.Natural (powModNatural, wordToNatural)
import Numeric.Natural

data Literal
  = LInteger !Integer
  | LRational !Rational
  | LNatural !Natural
  | LText !Text
  deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)

-- | ConstrId is the tag name for data type constructors, we dont have those yet
-- likewise, if we want to contemplate type directed name resolution,
-- we will need to do enriched name spacing!
newtype ConstrId
  = ConstrId { unConstrId :: Text }
  deriving (Eq,Show,Typeable,Ord,Read,Data,Generic)

-- Primops for a language have names
newtype PrimOpId
  = PrimopId { unPrimopId :: Text }
  deriving (Eq,Show,Typeable,Ord,Read,Data,Generic)

-- Evaluation
--- currently we only provide the operations which are total for
data LiteralOp
  = IntAdd      Integer  Integer
  | IntSub      Integer  Integer
  | IntMult     Integer  Integer
  | IntSquare   Integer
  -- | IntQuotRem  Integer  Integer
  -- | IntDivMod   Integer  Integer
  -- | IntPowMod   Integer  Integer  Integer -- a^b mod abs(c)
  | IntRecipMod Integer  Integer          -- inv of a mod m. 0 if no inv exists
  | IntLcm      Integer  Integer
  | IntGcd      Integer  Integer
  | IntGcdExt   Integer  Integer
  | RatAdd      Rational Rational
  | RatSub      Rational Rational
  | RatMult     Rational Rational
  -- | RatDiv      Rational Rational
  | NatAdd      Natural  Natural
  | NatMult     Natural  Natural
  -- | NatQuotRem  Natural  Natural
  -- | NatDivMod   Natural  Natural          -- identical to QuotRem for nats
  | NatPowMod   Natural  Natural  Natural -- a^b mod c
  deriving (Show)

integerLog :: Integral a => a -> Natural
integerLog i = wordToNatural (W# (sizeInBaseInteger (toInteger i) 2#))

ratNSquaredCost :: Rational -> Rational -> Natural
ratNSquaredCost x y = n * n
  where
    n = maximum (fmap integerLog [ numerator x, denominator x
                                 , numerator y, denominator y])

-- TODO:
-- - determine how to equate math and heap costs
-- - increment counter before evaluating math op

cost :: LiteralOp -> Natural
cost (IntAdd  x y) = integerLog (max x y)
cost (IntSub  x y) = integerLog (max x y)
cost (IntMult x y) = integerLog x * integerLog y
cost (IntSquare x) = integerLog x * integerLog x
cost (IntRecipMod _ m) = integerLog m * integerLog m -- euclid's
cost (IntLcm x y) = integerLog x * integerLog y -- due to (a*b)/gcd(a,b)
cost (IntGcd x y) = integerLog x * integerLog y -- euclid's
cost (IntGcdExt x y) = integerLog x * integerLog y -- euclid's
cost (RatAdd x y) = 6 * ratNSquaredCost x y -- 3 mult, 1 gcd, 2 div
cost (RatSub x y) = 6 * ratNSquaredCost x y -- 3 mult, 1 gcd, 2 div
cost (RatMult x y) = 5 * ratNSquaredCost x y -- 2 mult, 1 gcd, 2 div
cost (NatAdd  x y) = integerLog (max x y)
cost (NatMult x y) = integerLog x * integerLog y
cost (NatPowMod x y m) = integerLog x * integerLog y * integerLog m

evalTotalPrimopCode :: LiteralOp -> [Literal]
evalTotalPrimopCode (IntAdd      a b) = [LInteger (a + b)]
evalTotalPrimopCode (IntSub      a b) = [LInteger (a - b)]
evalTotalPrimopCode (IntMult     a b) = [LInteger (a * b)]
evalTotalPrimopCode (IntSquare   a)   = [LInteger (sqrInteger a)]
--evalTotalPrimopCode (IntQuotRem  a b) = [LInteger q, LInteger r] -- UNDEFINED for b = 0
--  where (q, r) = a `quotRem` b
--evalTotalPrimopCode (IntDivMod   a b) = [LInteger d, LInteger m] -- UNDEFINED for b = 0
--  where (d, m) = a `divMod` b
--evalTotalPrimopCode (IntPowMod   b e m) = [LInteger (powModInteger b e m)] -- UNDEFINED for some e < 0
evalTotalPrimopCode (IntRecipMod a b) = [LInteger (recipModInteger a b)]
evalTotalPrimopCode (IntLcm      a b) = [LInteger (lcmInteger a b)]
evalTotalPrimopCode (IntGcd      a b) = [LInteger (gcdInteger a b)]
evalTotalPrimopCode (IntGcdExt   a b) = [LInteger g, LInteger s]
  where (# g, s #) = gcdExtInteger a b
evalTotalPrimopCode (RatAdd      a b) = [LRational (a + b)]
evalTotalPrimopCode (RatSub      a b) = [LRational (a - b)]
evalTotalPrimopCode (RatMult     a b) = [LRational (a * b)]
--evalTotalPrimopCode (RatDiv      a b) = [LRational (a / b)]         -- UNDEFINED for b = 0
evalTotalPrimopCode (NatAdd      a b) = [LNatural (a + b)]
evalTotalPrimopCode (NatMult     a b) = [LNatural (a * b)]
-- NOTE: for nats, QuotRem and DivMod are identical
--evalTotalPrimopCode (NatQuotRem a b) = let (q, r) = a `quotRem` b  -- UNDEFINED for b = 0
--                        in [LNatural q, LNatural r]
--evalTotalPrimopCode (NatDivMod  a b) = let (d, m) = a `divMod` b   -- UNDEFINED for b = 0
--                        in [LNatural d, LNatural m]
evalTotalPrimopCode (NatPowMod  b e m) = [LNatural (powModNatural b e m)]
