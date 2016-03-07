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



{-
TODO / FIXME
use GMP limb count instead of integer log

later on
look at gmp-impl.h for how the algorithm selection for different asymptotic ranges is done
for the default routines

-}

module Hopper.Internal.Core.Literal
  ( Literal(..)
  , PrimOpId(..)
  , ConstrId(..)
  , evalTotalMathPrimopCode
  , hoistTotalMathLiteralOp
  , GmpMathOpId(..)
  , gmpMathCost
  , LiteralOp(..)
  ,naturalLimbSize
  ,integerLimbSize
  ) where

import Data.Data
import Data.Word
import Data.Text (Text)
import Data.Ratio (numerator, denominator)
--import GHC.Exts (Word(W#))
import GHC.Generics
import GHC.Integer.GMP.Internals (sqrInteger ,lcmInteger , gcdInteger
                                 ,gcdExtInteger, recipModInteger )
import GHC.Natural (powModNatural)
import Numeric.Natural
import Hopper.Utils.BigMath

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
data PrimOpId =
    PrimopIdGeneral  !Text
    | TotalMathOpGmp !GmpMathOpId

  deriving (Eq,Show,Typeable,Ord,Read,Data,Generic)

data GmpMathOpId =
    IntAddOpId
  | IntSubOpId
  | IntMultOpId
  | IntSquareOpId
  | IntRecipModOpId
  | IntLcmOpId
  | IntGcdOpId
  | IntGcdExtOpId
  | RatAddOpId
  | RatSubOpId
  | RatMultOpId
  | NatAddOpId
  | NatMultOpId
  | NatPowModOpId
  deriving (Eq,Ord,Show,Read,Data,Typeable,Generic )



hoistTotalMathLiteralOp :: GmpMathOpId -> [Literal] -> Either String LiteralOp
hoistTotalMathLiteralOp gmoOp args = go gmoOp args
  where
    go :: GmpMathOpId -> [Literal] -> Either String LiteralOp
    go IntAddOpId     [LInteger a, LInteger b] = Right $ IntAdd a b
    go op@IntAddOpId       ls = Left (show (op,ls))
    go IntSubOpId     [LInteger a, LInteger b] = Right $ IntSub a b
    go op@IntSubOpId       ls = Left (show (op,ls))
    go IntMultOpId    [LInteger a, LInteger b] = Right $ IntMult a b
    go op@IntMultOpId        ls = Left (show (op,ls))
    go IntSquareOpId  [LInteger a ] =   Right $ IntSquare a
    go op@IntSquareOpId        ls = Left (show (op,ls))
    go IntRecipModOpId [LInteger a, LInteger b] =     Right $ IntRecipMod a b
    go op@IntRecipModOpId       ls = Left (show (op,ls))
    go IntLcmOpId     [LInteger a, LInteger b] = Right $ IntLcm a b
    go op@IntLcmOpId       ls = Left (show (op,ls))
    go IntGcdOpId     [LInteger a, LInteger b] = Right $ IntGcd a b
    go op@IntGcdOpId       ls = Left (show (op,ls))
    go IntGcdExtOpId  [LInteger a, LInteger b] =   Right $ IntGcdExt a b
    go op@IntGcdExtOpId        ls = Left (show (op,ls))
    go RatAddOpId     [LRational a, LRational b] = Right $ RatAdd a b
    go op@RatAddOpId       ls = Left (show (op,ls))
    go RatSubOpId     [LRational a, LRational b] = Right $ RatSub a b
    go op@RatSubOpId       ls = Left (show (op,ls))
    go RatMultOpId    [LRational a, LRational b] = Right $ RatMult a b
    go op@RatMultOpId        ls = Left (show (op,ls))
    go NatAddOpId     [LNatural a, LNatural b] = Right $ NatAdd a b
    go op@NatAddOpId       ls = Left (show (op,ls))
    go NatMultOpId    [LNatural a, LNatural b] = Right $ NatMult a b
    go op@NatMultOpId        ls = Left (show (op,ls))
    go NatPowModOpId  [LNatural a, LNatural b, LNatural c] =   Right $ NatPowMod a b c
    go op@NatPowModOpId        ls = Left (show (op,ls))



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

naturalLimbSize :: Natural -> Word64
naturalLimbSize = naturalSizeInWord64

integerLimbSize :: Integer -> Word64
integerLimbSize = integerSizeInWord64

ratNSquaredCost :: Rational -> Rational -> Word64
ratNSquaredCost x y = n * n
  where
    n = maximum (fmap integerLimbSize [ numerator x, denominator x
                                 , numerator y, denominator y])

-- TODO:
-- - determine how to equate math and heap costs
-- - increment counter before evaluating math op

{- | gmpMathCost is an approximation of the complexity of the operations
that ghc exposes from GMP.

these are currently VERY VERY crude upper bounds on complexity
-}

gmpMathCost :: LiteralOp -> Word64
gmpMathCost (IntAdd  x y) = integerLimbSize (max x y)
gmpMathCost (IntSub  x y) = integerLimbSize (max x y)
gmpMathCost (IntMult x y) = integerLimbSize x * integerLimbSize y
gmpMathCost (IntSquare x) = integerLimbSize x * integerLimbSize x
gmpMathCost (IntRecipMod _ m) = integerLimbSize m *  integerLimbSize m -- euclid's
gmpMathCost (IntLcm x y) = integerLimbSize x * integerLimbSize y -- due to (a*b)/gcd(a,b)
gmpMathCost (IntGcd x y) = integerLimbSize x * integerLimbSize y -- euclid's
gmpMathCost (IntGcdExt x y) = integerLimbSize x * integerLimbSize y -- euclid's
gmpMathCost (RatAdd x y) = 6 * ratNSquaredCost x y -- 3 mult, 1 gcd, 2 div
gmpMathCost (RatSub x y) = 6 * ratNSquaredCost x y -- 3 mult, 1 gcd, 2 div
gmpMathCost (RatMult x y) = 5 * ratNSquaredCost x y -- 2 mult, 1 gcd, 2 div
gmpMathCost (NatAdd  x y) = naturalLimbSize (max x y)
gmpMathCost (NatMult x y) = naturalLimbSize x * naturalLimbSize y
gmpMathCost (NatPowMod x y m) = naturalLimbSize x * naturalLimbSize y * naturalLimbSize m

evalTotalMathPrimopCode :: LiteralOp -> [Literal]
evalTotalMathPrimopCode (IntAdd      a b) = [LInteger (a + b)]
evalTotalMathPrimopCode (IntSub      a b) = [LInteger (a - b)]
evalTotalMathPrimopCode (IntMult     a b) = [LInteger (a * b)]
evalTotalMathPrimopCode (IntSquare   a)   = [LInteger (sqrInteger a)]
--evalTotalMathPrimopCode (IntQuotRem  a b) = [LInteger q, LInteger r] -- UNDEFINED for b = 0
--  where (q, r) = a `quotRem` b
--evalTotalMathPrimopCode (IntDivMod   a b) = [LInteger d, LInteger m] -- UNDEFINED for b = 0
--  where (d, m) = a `divMod` b
--evalTotalMathPrimopCode (IntPowMod   b e m) = [LInteger (powModInteger b e m)] -- UNDEFINED for some e < 0
evalTotalMathPrimopCode (IntRecipMod a b) = [LInteger (recipModInteger a b)]
evalTotalMathPrimopCode (IntLcm      a b) = [LInteger (lcmInteger a b)]
evalTotalMathPrimopCode (IntGcd      a b) = [LInteger (gcdInteger a b)]
evalTotalMathPrimopCode (IntGcdExt   a b) = [LInteger g, LInteger s]
  where (# g, s #) = gcdExtInteger a b
evalTotalMathPrimopCode (RatAdd      a b) = [LRational (a + b)]
evalTotalMathPrimopCode (RatSub      a b) = [LRational (a - b)]
evalTotalMathPrimopCode (RatMult     a b) = [LRational (a * b)]
--evalTotalMathPrimopCode (RatDiv      a b) = [LRational (a / b)]         -- UNDEFINED for b = 0
evalTotalMathPrimopCode (NatAdd      a b) = [LNatural (a + b)]
evalTotalMathPrimopCode (NatMult     a b) = [LNatural (a * b)]
-- NOTE: for nats, QuotRem and DivMod are identical
--evalTotalMathPrimopCode (NatQuotRem a b) = let (q, r) = a `quotRem` b  -- UNDEFINED for b = 0
--                        in [LNatural q, LNatural r]
--evalTotalMathPrimopCode (NatDivMod  a b) = let (d, m) = a `divMod` b   -- UNDEFINED for b = 0
--                        in [LNatural d, LNatural m]
evalTotalMathPrimopCode (NatPowMod  b e m) = [LNatural (powModNatural b e m)]
