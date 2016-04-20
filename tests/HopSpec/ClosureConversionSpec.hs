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
        v0_0 = v0
        v0_1 = LocalVar $ LocalNamelessVar 0 $ BinderSlot 1
        v1 = LocalVar $ LocalNamelessVar 1 $ BinderSlot 0
        v2 = LocalVar $ LocalNamelessVar 2 $ BinderSlot 0
        v2_0 = v2
        v2_1 = LocalVar $ LocalNamelessVar 2 $ BinderSlot 1
        id_ = GlobalVarSym $ GlobalSymbol "id"
        ten = LInteger 10
        twenty = LInteger 20
        dummyBI = BinderInfoData Omega () Nothing
        infos0 = V.empty
        infos1 = V.singleton dummyBI
        infos2 = V.replicate 2 dummyBI
        arity0 = CodeArity 0
        arity1 = CodeArity 1
        emptyRegistry = SymbolRegistryCC Map.empty Map.empty Map.empty
        prim0 = PrimopIdGeneral "test"

    it "handles closure-less let and return" $
      let anf = AnfLet infos1
                       (RhsAlloc $ AllocLit ten)
                       (AnfReturn $ V.singleton v0)
          ccd = LetNFCC infos1
                        (AllocRhsCC $ SharedLiteralCC ten)
                        (ReturnCC $ V.singleton v0)
          registry = emptyRegistry
      in closureConvert anf `shouldBe` (ccd, registry)

    it "allows free vars" $
      let anf = AnfReturn $ V.singleton v1
          ccd = ReturnCC $ V.singleton v1
          registry = emptyRegistry
      in closureConvert anf `shouldBe` (ccd, registry)

    it "converts closures" $
      let anf = AnfLet infos1
                       (RhsAlloc $ AllocLit ten)
                       (AnfLet infos1
                               (RhsAlloc $
                                 AllocLam infos1 $
                                   AnfLet infos1
                                          (RhsAlloc $ AllocLit twenty)
                                          (AnfReturn $ V.fromList [ v0 -- local
                                                                  , v1 -- arg
                                                                  , v2 -- free
                                                                  ]))
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
                                       (LetNFCC infos1
                                                (AllocRhsCC $
                                                  SharedLiteralCC twenty)
                                                (ReturnCC $
                                                  V.fromList [ v0 -- local var
                                                             , v2 -- arg slot 0
                                                             , v1 -- env slot 0
                                                             ]))
          registry = SymbolRegistryCC Map.empty
                                      (Map.fromList [( ClosureCodeId 0
                                                     , record)])
                                      Map.empty
      in closureConvert anf `shouldBe` (ccd, registry)

    it "converts thunks" $
      let anf = AnfLet infos1
                       (RhsAlloc $ AllocLit ten)
                       (AnfLet infos1
                               (RhsAlloc $
                                 AllocThunk $
                                   AnfLet infos1
                                          (RhsAlloc $ AllocLit twenty)
                                          (AnfReturn $ V.fromList [v0, v1]))
                               (AnfReturn $ V.singleton v0))
          ccd = LetNFCC infos1
                        (AllocRhsCC $ SharedLiteralCC ten)
                        (LetNFCC infos1
                                 (AllocRhsCC $
                                   AllocateThunkCC (V.singleton v0)
                                                   (ThunkCodeId 0))
                                 (ReturnCC $ V.singleton v0))
          record = ThunkCodeRecordCC (EnvSize 1)
                                     infos1
                                     (LetNFCC infos1
                                              (AllocRhsCC $
                                                SharedLiteralCC twenty)
                                              (ReturnCC $
                                                V.fromList [ v0 -- local let
                                                           , v1 -- env slot 0
                                                           ]))
          registry = SymbolRegistryCC (Map.fromList [( ThunkCodeId 0
                                                     , record)])
                                      Map.empty
                                      Map.empty
      in closureConvert anf `shouldBe` (ccd, registry)

    it "allocates env vars from left to right" $
      let anf = AnfLet infos1
                       (RhsAlloc $ AllocLit ten)
                       (AnfLet infos1
                               (RhsAlloc $ AllocLit twenty)
                               (AnfLet infos1
                                       (RhsAlloc $
                                         AllocThunk $
                                           AnfReturn $ V.fromList [v1, v0])
                                       (AnfReturn $ V.singleton v0)))
          ccd = LetNFCC infos1
                        (AllocRhsCC $ SharedLiteralCC ten)
                        (LetNFCC infos1
                                 (AllocRhsCC $ SharedLiteralCC twenty)
                                 (LetNFCC infos1
                                          (AllocRhsCC $
                                            AllocateThunkCC (V.fromList [ v1
                                                                        , v0])
                                                            (ThunkCodeId 0))
                                          (ReturnCC $ V.singleton v0)))
          record = ThunkCodeRecordCC (EnvSize 2)
                                     infos2
                                     (ReturnCC $ V.fromList [v0_0, v0_1])
          registry = SymbolRegistryCC (Map.fromList [( ThunkCodeId 0
                                                     , record)])
                                      Map.empty
                                      Map.empty
      in closureConvert anf `shouldBe` (ccd, registry)

    it "only allocates an env var if an outside binder is referenced" $
      let anf = AnfLet infos1
                       (RhsAlloc $ AllocLit ten)
                       (AnfLet infos1
                               (RhsAlloc $
                                 AllocThunk $
                                   AnfTailCall $ AppFun id_ $ V.singleton id_)
                               (AnfReturn $ V.singleton v0))
          ccd = LetNFCC infos1
                        (AllocRhsCC $ SharedLiteralCC ten)
                        (LetNFCC infos1
                                 (AllocRhsCC $
                                   AllocateThunkCC (V.empty)
                                                   (ThunkCodeId 0))
                                 (ReturnCC $ V.singleton v0))
          record = ThunkCodeRecordCC (EnvSize 0)
                                     infos0
                                     (TailCallCC $ FunAppCC id_
                                                            (V.singleton id_))
          registry = SymbolRegistryCC (Map.fromList [( ThunkCodeId 0
                                                     , record)])
                                      Map.empty
                                      Map.empty
      in closureConvert anf `shouldBe` (ccd, registry)

    it "converts nested closures" $
      let anf = AnfLet infos2
                  (RhsApp $ AppPrim prim0 V.empty)
                  (AnfLet infos1
                    (RhsAlloc $ AllocLam infos1 $
                      AnfLet infos1
                        (RhsAlloc $ AllocLam infos1
                          (AnfReturn $ V.fromList [ v0   -- inner arg 0
                                                  , v2_0 -- outermost let slot 0
                                                  , v2_1 -- outermost let slot 1
                                                  ]))
                        (AnfTailCall $ AppFun v0                 -- inner lam
                                              (V.singleton v1))) -- outer arg 0
                    (AnfReturn $ V.singleton v0))
          ccd = LetNFCC infos2
                  (NonTailCallAppCC $ PrimAppCC prim0 V.empty)
                  (LetNFCC infos1
                    (AllocRhsCC $ AllocateClosureCC (V.fromList [ v0_0 -- let@0
                                                                , v0_1 -- let@1
                                                                ])
                                                    arity1
                                                    (ClosureCodeId 0))
                    (ReturnCC $ V.singleton v0))
          outerRec = ClosureCodeRecordCC (EnvSize 2) infos2 arity1 infos1 $
                       LetNFCC infos1
                        (AllocRhsCC $
                          AllocateClosureCC (V.fromList [ v0_0 -- env slot 0
                                                        , v0_1 -- env slot 1
                                                        ])
                                            arity1
                                            (ClosureCodeId 1))
                        (TailCallCC $ FunAppCC v0
                                               -- bumped past env:
                                               (V.singleton v2))
          innerRec = ClosureCodeRecordCC (EnvSize 2) infos2 arity1 infos1 $
                       ReturnCC $ V.fromList [ v1   -- arg0 bumped past env
                                             , v0_0 -- env slot 0
                                             , v0_1 -- env slot 1
                                             ]
          registry = SymbolRegistryCC Map.empty
                                      (Map.fromList
                                        [ (ClosureCodeId 0, outerRec)
                                        , (ClosureCodeId 1, innerRec)])
                                      Map.empty
      in closureConvert anf `shouldBe` (ccd, registry)

    it "re-uses env slots when multiple vars reference the same binder" $
      let anf = AnfLet infos1
                       (RhsAlloc $ AllocLit ten)
                       (AnfLet infos1
                               (RhsAlloc $ AllocLam infos0 $
                                 AnfReturn $ V.fromList [v1, v1])
                               (AnfReturn $ V.singleton v0))
          ccd = LetNFCC infos1
                  (AllocRhsCC $ SharedLiteralCC ten)
                  (LetNFCC infos1
                    (AllocRhsCC $
                      AllocateClosureCC (V.fromList [v0])
                                        arity0
                                        (ClosureCodeId 0))
                    (ReturnCC $ V.singleton v0))
          record = ClosureCodeRecordCC (EnvSize 1) infos1 arity0 infos0 $
                     ReturnCC $ V.fromList [v0_0, v0_0] -- both share env slot 0
          registry = SymbolRegistryCC Map.empty
                                      (Map.fromList [(ClosureCodeId 0, record)])
                                      Map.empty
      in closureConvert anf `shouldBe` (ccd, registry)
