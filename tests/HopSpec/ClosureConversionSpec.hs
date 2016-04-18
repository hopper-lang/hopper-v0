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
        infos1 = V.singleton dummyBI
        infos2 = V.replicate 2 dummyBI
        arity1 = CodeArity 1
        -- arity2 = CodeArity 2
        emptyRegistry = SymbolRegistryCC Map.empty Map.empty Map.empty
        -- prim0 = PrimopIdGeneral "test"

    it "handles trivial closureless-code" $
      let anf = AnfLet infos1
                       (RhsAlloc $ AllocLit ten)
                       (AnfReturn $ V.singleton v0)
          ccd = LetNFCC infos1
                        (AllocRhsCC $ SharedLiteralCC ten)
                        (ReturnCC $ V.singleton v0)
          registry = emptyRegistry
      in closureConvert anf `shouldBe` (ccd, registry)

    it "converts closures" $
      let anf = AnfLet infos1
                       (RhsAlloc $ AllocLit ten)
                       (AnfLet infos1
                               (RhsAlloc $
                                 AllocLam infos1
                                          (AnfReturn $ V.fromList [v0, v1]))
                               (AnfReturn $ V.singleton v0))
          ccd = LetNFCC infos1
                        (AllocRhsCC $ SharedLiteralCC ten)
                        (LetNFCC infos1
                                 (AllocRhsCC $
                                   AllocateClosureCC (V.singleton v0)
                                                     arity1
                                                     (ClosureCodeId 0))
                                 (ReturnCC $ V.singleton v0))
          record = ClosureCodeRecordCC (EnvSize 1)
                                       infos1 -- for env
                                       arity1
                                       infos1 -- for args
                                       (ReturnCC $ V.fromList [ v1 -- arg slot 0
                                                              , v0 -- env slot 0
                                                              ])
          registry = SymbolRegistryCC Map.empty
                                      (Map.fromList [( (ClosureCodeId 0)
                                                     , record)])
                                      Map.empty
      in closureConvert anf `shouldBe` (ccd, registry)
