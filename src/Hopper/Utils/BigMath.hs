{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
module Hopper.Utils.BigMath(
    integerSizeInWord64
    ,naturalSizeInWord64
    )
where


import GHC.Integer.GMP.Internals
import GHC.Natural
import GHC.Types(Int(I#))
import Data.Word

#include "MachDeps.h"

#if WORD_SIZE_IN_BITS < 64
#error "hopper code base is 64bit only, this is not a supported platform"
#endif

integerSizeInWord64 :: Integer -> Word64
integerSizeInWord64 (S# _) = 1
integerSizeInWord64 (Jp# blimb) = fromIntegral $ I# ( sizeofBigNat# blimb)
integerSizeInWord64 (Jn# blimb) = fromIntegral $ I# ( sizeofBigNat# blimb)

naturalSizeInWord64 :: Natural -> Word64
naturalSizeInWord64 (NatS#  _ ) = 1
naturalSizeInWord64 (NatJ# blimb) = fromIntegral $ I# (sizeofBigNat# blimb)
