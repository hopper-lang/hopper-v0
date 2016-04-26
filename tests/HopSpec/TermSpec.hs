{-# LANGUAGE OverloadedStrings #-}

module HopSpec.TermSpec
  ( spec
  ) where

import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term
import Hopper.Utils.LocallyNameless
import Hopper.Internal.Type.Relevance
import Hopper.Internal.Type.BinderInfo

import Test.Hspec
import Test.Hspec.Expectations
import qualified Data.Vector as V

spec :: Spec
spec =
  describe "Term" $ do
    describe "using the Bound rep" $ do
      let v0 = V $ Local (Depth 0) $ Slot 0
          v1 = V $ Local (Depth 1) $ Slot 0
          v2 = V $ Local (Depth 2) $ Slot 0
          v3 = V $ Local (Depth 3) $ Slot 0
          lit = ELit $ LInteger 42
          prim0 = PrimopIdGeneral "test"
          dummyBIs = V.replicate 2 $ BinderInfoData Omega () Nothing
          shift = BinderLevelShiftUP

      describe "removeBinderShifts" $ do
        it "bumps variables and removes binder shifts" $
          let term  = shift 1 $ shift 2 $ App (shift 0 v0) $ V.fromList [v0, v1]
              term' = App v1 $ V.fromList [v0, v2]
          in removeBinderShifts term `shouldBe` term'

        it "bumps multiple times for a duplicate shift value" $
          let term  = shift 0 $ shift 0 $ v1
              term' = v3
          in removeBinderShifts term `shouldBe` term'

        it "preserves binder slots when bumping variables" $
          let slot = Slot 3
              term  = shift 1 $ V $ Local (Depth 1) slot
              term' = V $ Local (Depth 2) slot
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

    describe "using the Variable rep" $ do
      let add = V $ Bound $ Global $ GlobalSymbol "add"
          v0 = V $ Bound $ Local (Depth 0) (Slot 0)
          v0_0 = v0
          v0_1 = V $ Bound $ Local (Depth 0) (Slot 1)
          v1_0 = V $ Bound $ Local (Depth 1) (Slot 0)
          lit = ELit $ LInteger 42
          infos n = V.replicate n $ BinderInfoData Omega () Nothing

      describe "instantiate" $
        it "replaces vars bound to toplevel binders with given free names" $
          let term  = App add
                          (V.fromList
                            [ v0_1
                            , v0_0
                            , Let (infos 1)
                                  lit
                                  (Return $ V.fromList [ v0
                                                       , v1_0])
                            , Lam (infos 1)
                                  (Return $ V.fromList [ v0
                                                       , v1_0])])
              term' = App add
                          (V.fromList
                            [ V $ Atom "y"
                            , V $ Atom "x"
                            , Let (infos 1)
                                  lit
                                  (Return $ V.fromList [ v0
                                                       , V $ Atom "x"])
                            , Lam (infos 1)
                                  (Return $ V.fromList [ v0
                                                       , V $ Atom "x"])])
          in instantiate (V.fromList ["x", "y"]) term `shouldBe` term'

      describe "abstract" $
        it "replaces free vars with bound vars for given free names" $
          let term  = App add
                          (V.fromList
                            [ V $ Atom "y"
                            , V $ Atom "x"
                            , V $ Atom "z" -- not in names
                            , Let (infos 1)
                                  lit
                                  (Return $ V.fromList [ v0
                                                       , V $ Atom "x"])
                            , Lam (infos 1)
                                  (Return $ V.fromList [ v0
                                                       , V $ Atom "x"])])
              term' = App add
                          (V.fromList
                            [ v0_1
                            , v0_0
                            , V $ Atom "z" -- stays free
                            , Let (infos 1)
                                  lit
                                  (Return $ V.fromList [ v0
                                                       , v1_0])
                            , Lam (infos 1)
                                  (Return $ V.fromList [ v0
                                                       , v1_0])])
          in abstract (V.fromList ["x", "y"]) term `shouldBe` term'

    -- TODO: quickcheck tests for instantiate/abstract round trip would be nice
