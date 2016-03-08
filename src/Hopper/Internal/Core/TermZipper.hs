module Hopper.Internal.Core.TermZipper where

import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term

import Data.Word (Word32)
import qualified Data.Vector as V

-- TODO: MOVE TO MODELS

-- Carter's original formulation:
--
-- data DTerm a =
--     DShift Word32 ()
--   | DLit ()
--   | DReturn (V.Vector a) () (V.Vector Term) -- left to right evaluation order
--   | DEnterThunk ()
--   | DDelay ()
--   | DAppFun () (V.Vector Term)
--   | DAppArgs a (V.Vector a) () (V.Vector Term)
--   | DPrimApp PrimOpId (V.Vector a) () (V.Vector Term)
--   | DLam (V.Vector BinderInfo) ()
--   | DLetRhs (V.Vector BinderInfo) () Term
--   | DLetBody (V.Vector BinderInfo) a ()
--   deriving (Eq, Show)
-- -- "every spot where there's an 'a' becomes a variable"
-- -- "This is probably good for Term to Term ANF"
-- carter :: Term -> TermZipper Variable -> Term
-- carter = undefined

-- carter's other zipper-like type changing rep
-- data MiniDTerm a b =  AppArgs a [a]  () [b]
--                          [shiftStackValues]

-- Brian's first adaptation:
--
-- data DTerm =
--     DShift Word32 ()
--   | DReturn (V.Vector Term) () (V.Vector Term)
--   | DEnterThunk ()
--   | DDelay ()
--   -- | DApp (V.Vector Term) () (V.Vector Term) -- the first term is the function
--   | DAppFun () (V.Vector Term)
--   | DAppArgs Term (V.Vector Term) () (V.Vector Term)
--   | DPrimApp PrimOpId (V.Vector Term) () (V.Vector Term)
--   | DLam (V.Vector BinderInfo) ()
--   -- | DLet (V.Vector BinderInfo) (V.Vector Term) () (V.Vector Term) -- first term is rhs
--   | DLetRhs (V.Vector BinderInfo) () Term
--   | DLetBody (V.Vector BinderInfo) Term ()
--   deriving (Eq, Show)
--
-- data TermZipper = TZ [DTerm] -- context stack
--                      Term    -- current hole
--
-- next :: TermZipper -> Maybe TermZipper
-- next (TZ stack hole) = case hole of
--   V _ -> _todo
--
--   where
--     up = case stack of
--       [] -> Nothing
--       (d : ds) -> Just $ TZ ds (reconstruct d hole)
--
-- reconstruct :: DTerm -> Term -> Term
-- reconstruct (DShift amount ()) t = BinderLevelShiftUP amount t
-- reconstruct (DReturn before () after) t = Return $ V.concat [before, (V.singleton t), after]
-- reconstruct (DEnterThunk ()) t = EnterThunk t
-- reconstruct (DDelay ()) t = Delay t
-- reconstruct (DAppFun () args) t = App t args
-- reconstruct (DAppArgs f before () after) t = App f $ V.concat [before, (V.singleton t), after]
-- reconstruct (DPrimApp primId before () after) t = PrimApp primId $ V.concat [before, (V.singleton t), after]
-- reconstruct (DLam binders ()) t = Lam binders t
-- reconstruct (DLetRhs binders () body) t = Let binders t body
-- reconstruct (DLetBody binders rhs ()) t = Let binders rhs t


----------------------------------------


-- Adapted from:
--
-- data Path a
--   = Top
--   | Split a [Tree a] (Path a) [Tree a]
--
-- data Location a
--   = Location (Tree a) (Path a)
--
data Context
  = CShift Word32 ()
  | CReturn (V.Vector Term) () (V.Vector Term)
  | CEnterThunk ()
  | CDelay ()
  | CAppFun () (V.Vector Term)
  | CAppArgs Term (V.Vector Term) () (V.Vector Term)
  | CPrimApp PrimOpId (V.Vector Term) () (V.Vector Term)
  | CLam (V.Vector BinderInfo) ()
  | CLetRhs (V.Vector BinderInfo) () Term
  | CLetBody (V.Vector BinderInfo) Term ()

data Path
  = Top
  | Down Path Context

-- our zipper:
data Location
  = Loc Path Term

reconstruct :: Context -> Term -> Term
reconstruct (CShift amount ()) t = BinderLevelShiftUP amount t
reconstruct (CReturn before () after) t = Return $ V.concat [before, V.singleton t, after]
reconstruct (CEnterThunk ()) t = EnterThunk t
reconstruct (CDelay ()) t = Delay t
reconstruct (CAppFun () args) t = App t args
reconstruct (CAppArgs f before () after) t = App f $ V.concat [before, V.singleton t, after]
reconstruct (CPrimApp primId before () after) t = PrimApp primId $ V.concat [before, V.singleton t, after]
reconstruct (CLam binders ()) t = Lam binders t
reconstruct (CLetRhs binders () body) t = Let binders t body
reconstruct (CLetBody binders rhs ()) t = Let binders rhs t
