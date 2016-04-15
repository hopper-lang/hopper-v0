module Hopper.Internal.Core.ShiftRemoval
  ( removeBinderShifts
  ) where

import Hopper.Internal.Core.Term (Term(..))
import Hopper.Utils.LocallyNameless (localNameless, lnDepth)

import Control.Lens ((+~), (%~), (^?), ix)
import Data.Function ((&))
import Data.Word (Word32)

-- | A bump amount @b@ at index @k@ in 'BinderShifts' means that we have @b@
-- instances of @BinderLevelShiftUP k@ that we imagine we're tracking as we move
-- down the AST.
--
-- - When we enter a new scope, we @(0:)@ our list, effectively turning each
--   tracked @BinderLevelShiftUP k@ to @BinderLevelShiftUP (k+1)@.
-- - When we encounter a @BinderLevelShiftUP k@, we @(+1)@ the list at index
--   @k@.
-- - When we encounter a variable of depth @d@, we bump the variable by the sum
--   of the @b@ amounts for all of the shifts the variable is affected by --
--   namely, the first @d+1@ @b@ values in 'BinderShifts'.
type BinderShifts = [Word32]

-- | Removes binder shifts from a 'Term'
removeBinderShifts :: Term -> Term
removeBinderShifts = go $ repeat 0 -- NB: [] only works for well-formed ASTs,
                                   --     where no locally-nameless variables
                                   --     are free.
  where
    go :: BinderShifts -> Term -> Term
    go shifts (V var) = case var ^? localNameless.lnDepth of
      Just depth ->
        let adjustment = sum $ take (succ $ fromIntegral depth) shifts
        in V $ var & localNameless.lnDepth +~ adjustment
      Nothing ->
        V var

    go shifts (BinderLevelShiftUP k t) =
      go (shifts & ix (fromIntegral k) %~ succ) t

    go _shifts lit@(ELit _) = lit

    go shifts (Return ts) = Return $ go shifts <$> ts

    go shifts (EnterThunk t) = EnterThunk $ go shifts t

    go shifts (Delay t) = Delay $ go shifts t

    go shifts (App ft ats) = App (go shifts ft) (go shifts <$> ats)

    go shifts (PrimApp primId ts) = PrimApp primId $ go shifts <$> ts

    -- In the 'Lam' and 'Let' cases, we enter a new scope:

    go shifts (Lam infos t) = Lam infos $ go (0 : shifts) t

    go shifts (Let infos rhs bod) = Let infos (go shifts rhs)
                                              (go (0 : shifts) bod)
