module Hopper.Internal.Core.ShiftRemoval
  ( removeBinderShifts
  ) where

import Hopper.Internal.Core.Term (Term(..))
import Hopper.Utils.LocallyNameless

import Control.Lens ((+~), (^?))
import Data.Bits (bit, popCount, setBit, shift, zeroBits, (.&.))
import Data.Function ((&))

-- | Removes binder shifts from a 'Term'
removeBinderShifts :: Term -> Term
removeBinderShifts t0 = go zeroBits t0
  where
    -- We use an 'Integer' as a collection of bits to track binder shifts we've
    -- seen as we move towards the leaves of our AST. If we come across a binder
    -- shift of magnitude @k@, we set bit @k@. As we move into a new scope, we
    -- left bit-shift. When we hit a variable of depth @d@, we adjust its level
    -- by the popcount of all bits @<= d@.
    go :: Integer -> Term -> Term
    go bShifts (V var) = case var ^? localNameless.lnDepth of
      Just depth ->
        let applicable = pred $ bit $ succ $ fromIntegral depth
            displacement = fromIntegral $ popCount $ bShifts .&. applicable
        in V $ var & localNameless.lnDepth +~ displacement
      Nothing ->
        V var

    go bShifts (BinderLevelShiftUP k t) = go (setBit bShifts $ fromIntegral k) t

    go _shifts lit@(ELit _) = lit

    go bShifts (Return ts) = Return $ go bShifts <$> ts

    go bShifts (EnterThunk t) = EnterThunk $ go bShifts t

    go bShifts (Delay t) = Delay $ go bShifts t

    go bShifts (App ft ats) = App (go bShifts ft) (go bShifts <$> ats)

    go bShifts (PrimApp primId ts) = PrimApp primId $ go bShifts <$> ts

    go bShifts (Lam infos t) = Lam infos $ go (shift bShifts 1) t

    go bShifts (Let infos rhs bod) = Let infos (go bShifts rhs)
                                               (go (shift bShifts 1) bod)
