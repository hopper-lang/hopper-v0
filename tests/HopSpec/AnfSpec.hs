module HopSpec.AnfSpec
  ( spec
  ) where

import Hopper.Internal.LoweredCore.ANF
import Hopper.Internal.Core.Term
import Hopper.Internal.Core.Literal
import Hopper.Utils.LocallyNameless

import Test.Hspec
import qualified Data.Vector as V

spec :: Spec
spec =
  describe "ANF" $ do
    describe "toAnf" $ do
      let v0 = LocalVar $ LocalNamelessVar 0 $ BinderSlot 0
          v1 = LocalVar $ LocalNamelessVar 1 $ BinderSlot 0
          -- v2 = LocalVar $ LocalNamelessVar 2 $ BinderSlot 0

      describe "simple tail cases" $ do
        it "converts variables" $
          let term = V v0
              anf = AnfReturn $ V.singleton v0
          in toAnf term == anf

        it "converts shifted variables" $
          let term = BinderLevelShiftUP 2 $ V v0
              anf = AnfShift 2 $ AnfReturn $ V.singleton v0
          in anf == toAnf term

        it "converts literals" $
          let lit = LInteger 42
              term = ELit lit
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLit lit)
                           (AnfReturn $ V.singleton v0)
          in anf == toAnf term

        it "converts tail applications" $
          let term = App (V v0) $ V.singleton $ V v0
              anf = AnfTailCall $ AppFun v0 $ V.singleton v0
          in toAnf term == anf

      -- describe "non-tail cases" $ do
      --   it "converts shifted variable s" $
      --     let term = App (V v0) $ V.singleton $ BinderLevelShiftUP 1 $ V v1
      --         anf = _todo
      --     in anf == toAnf term
