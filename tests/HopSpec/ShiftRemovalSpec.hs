{-# LANGUAGE OverloadedStrings #-}

module HopSpec.ShiftRemovalSpec
  ( spec
  ) where

import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term
import Hopper.Internal.Core.ShiftRemoval (removeBinderShifts)
import Hopper.Utils.LocallyNameless
import Hopper.Internal.Type.Relevance

import Test.Hspec
import Test.Hspec.Expectations
import qualified Data.Vector as V

spec :: Spec
spec =
  describe "Binder shift removal" $ do
    let v0 = V $ LocalVar $ LocalNamelessVar 0 $ BinderSlot 0
        v1 = V $ LocalVar $ LocalNamelessVar 1 $ BinderSlot 0
        v2 = V $ LocalVar $ LocalNamelessVar 2 $ BinderSlot 0
        v3 = V $ LocalVar $ LocalNamelessVar 3 $ BinderSlot 0
        lit = ELit $ LInteger 42
        prim0 = PrimopIdGeneral "test"
        dummyBIs = V.replicate 2 $ BinderInfoData Omega () Nothing
        shift = BinderLevelShiftUP

    it "bumps variables and removes binder shifts" $
      let term  = shift 1 $ shift 2 $ App (shift 0 v0) $ V.fromList [v0, v1]
          term' = App v1 $ V.fromList [v0, v2]
      in removeBinderShifts term `shouldBe` term'

    it "preserves binder slots when bumping variables" $
      let slot = BinderSlot 3
          term  = shift 1 $ V $ LocalVar $ LocalNamelessVar 1 slot
          term' = V $ LocalVar $ LocalNamelessVar 2 slot
      in removeBinderShifts term `shouldBe` term'

    it "does not succ shift levels as it moves through a Return" $
      let term  = shift 1 $ Return $ V.fromList [lit, v0, v1, v2]
          term' = Return $ V.fromList [lit, v0, v2, v3]
      in removeBinderShifts term `shouldBe` term'

    it "does not succ shift levels as it moves through an EnterThunk" $
      let term  = shift 1 $ EnterThunk v1
          term' = EnterThunk v2
      in removeBinderShifts term `shouldBe` term'

    it "does not succ shift levels as it moves through a Delay" $
      let term  = shift 1 $ Delay v1
          term' = Delay v2
      in removeBinderShifts term `shouldBe` term'

    it "does not succ shift levels as it moves through an App" $
       let term  = shift 1 $ App v1 $ V.fromList [lit, v0, v1, v2]
           term' = App v2 $ V.fromList [lit, v0, v2, v3]
       in removeBinderShifts term `shouldBe` term'

    it "does not succ shift levels as it moves through a PrimApp" $
       let term  = shift 1 $ PrimApp prim0 $ V.fromList [lit, v0, v1, v2]
           term' = PrimApp prim0 $ V.fromList [lit, v0, v2, v3]
       in removeBinderShifts term `shouldBe` term'

    it "succs shift levels as it moves through a Lam" $
       let term  = shift 1 $ Lam dummyBIs $ Return $ V.fromList [v0, v1, v2]
           term' = Lam dummyBIs $ Return $ V.fromList [v0, v1, v3]
       in removeBinderShifts term `shouldBe` term'

    it "succs shift levels as it moves through a Let body" $
       let term  = shift 1 $ Let dummyBIs (Return $ V.fromList [v0, v1, v2])
                                          (Return $ V.fromList [v0, v1, v2])
           term' = Let dummyBIs (Return $ V.fromList [v0, v2, v3])
                                (Return $ V.fromList [v0, v1, v3])
       in removeBinderShifts term `shouldBe` term'
