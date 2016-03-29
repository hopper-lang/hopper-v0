module HopSpec.AnfSpec
  ( spec
  ) where

import Hopper.Internal.LoweredCore.ANF
import Hopper.Internal.Core.Term
import Hopper.Internal.Core.Literal
import Hopper.Internal.Type.Relevance
import Hopper.Utils.LocallyNameless

import Test.Hspec
import Test.Hspec.Expectations
import qualified Data.Vector as V

spec :: Spec
spec =
  describe "ANF" $ do
    describe "toAnf" $ do
      let v0 = LocalVar $ LocalNamelessVar 0 $ BinderSlot 0
          v1 = LocalVar $ LocalNamelessVar 1 $ BinderSlot 0
          -- v2 = LocalVar $ LocalNamelessVar 2 $ BinderSlot 0
          dummyBI = BinderInfoData Omega () Nothing

      describe "simple tail cases" $ do
        it "converts variables" $
          let term = V v0
              anf = AnfReturn $ V.singleton v0
          in toAnf term `shouldBe` anf

        -- TODO: need to add pass to remove shifts
        --
        -- it "converts shifted variables" $
        --   let term = BinderLevelShiftUP 2 $ V v0
        --       anf = AnfShift 2 $ AnfReturn $ V.singleton v0
        --   in toAnf term `shouldBe` anf

        it "converts literals" $
          let lit = LInteger 42
              term = ELit lit
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLit lit)
                           (AnfReturn $ V.singleton v0)
          in toAnf term `shouldBe` anf

        it "converts tail calls" $
          let term = App (V v0) $ V.singleton $ V v0
              anf = AnfTailCall $ AppFun v0 $ V.singleton v0
          in toAnf term `shouldBe` anf

        it "converts tail lambdas via allocation" $
          let term = Lam (V.singleton dummyBI)
                         (V v1)
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLam (Arity 1)
                                                (AnfReturn $ V.singleton v1))
                           (AnfReturn $ V.singleton v0)
          in toAnf term `shouldBe` anf

      describe "non-tail cases" $ do
        it "converts variables bumped by a literal allocation" $
          let lit = LInteger 5
              term = App (V v0) $ V.fromList [ELit lit]
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLit lit)
                           (AnfTailCall $ AppFun v1 $ V.fromList [v0])
          in toAnf term `shouldBe` anf

        -- TODO: need to add pass to remove shifts
        --
        -- it "converts shifted variable" $
        --   let term = App (V v0) $ V.singleton $ BinderLevelShiftUP 1 $ V v1
        --       anf = _todo
        --   in toAnf term `shouldBe` anf
