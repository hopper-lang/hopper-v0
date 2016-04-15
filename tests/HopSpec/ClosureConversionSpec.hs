{-# LANGUAGE OverloadedStrings #-}

module HopSpec.ClosureConversionSpec
  ( spec
  ) where

import Hopper.Internal.LoweredCore.ANF
import Hopper.Internal.LoweredCore.ClosureConversion (closureConvert)
import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.Core.Literal
import Hopper.Internal.Type.Relevance
import Hopper.Internal.Type.BinderInfo
import Hopper.Utils.LocallyNameless

import Test.Hspec
import Test.Hspec.Expectations

import qualified Data.Vector as V
import qualified Data.Map as Map

spec :: Spec
spec =
  describe "Closure conversion" $ do
    let v0 = LocalVar $ LocalNamelessVar 0 $ BinderSlot 0
        v1 = LocalVar $ LocalNamelessVar 1 $ BinderSlot 0
        v2 = LocalVar $ LocalNamelessVar 2 $ BinderSlot 0
        add = GlobalVarSym $ GlobalSymbol "add"
        ten = LInteger 10
        dummyBI = BinderInfoData Omega () Nothing
        arity1 = V.singleton $ dummyBI
        emptyRegistry = SymbolRegistryCC Map.empty Map.empty Map.empty
        -- prim0 = PrimopIdGeneral "test"

    it "handles trivial closureless-code" $
      let anf = AnfLet arity1
                       (RhsAlloc $ AllocLit ten)
                       (AnfReturn $ V.singleton v0)
          ccd = LetNFCC arity1
                        (AllocRhsCC $ SharedLiteralCC ten)
                        (ReturnCC $ V.singleton v0)
      in closureConvert anf `shouldBe` (ccd, emptyRegistry)
