{-# LANGUAGE OverloadedStrings #-}

module HopSpec.AnfSpec
  ( spec
  ) where

import Hopper.Internal.LoweredCore.ANF
import Hopper.Internal.Core.Term
import Hopper.Internal.Core.Literal
import Hopper.Internal.Type.Relevance
import Hopper.Internal.Type.BinderInfo
import Hopper.Utils.LocallyNameless

import Test.Hspec
import Test.Hspec.Expectations
import qualified Data.Vector as V

spec :: Spec
spec =
  describe "ANF" $
    describe "toAnf" $ do
      let v0 = LocalVar $ LocalNamelessVar 0 $ BinderSlot 0
          v0_0 = v0
          v0_1 = LocalVar $ LocalNamelessVar 0 $ BinderSlot 1
          v1 = LocalVar $ LocalNamelessVar 1 $ BinderSlot 0
          v1_1 = LocalVar $ LocalNamelessVar 1 $ BinderSlot 1
          v2 = LocalVar $ LocalNamelessVar 2 $ BinderSlot 0
          add = GlobalVarSym $ GlobalSymbol "add"
          abs = GlobalVarSym $ GlobalSymbol "abs"
          neg = GlobalVarSym $ GlobalSymbol "neg"
          id_ = GlobalVarSym $ GlobalSymbol "id"
          ten = LInteger 10
          twenty = LInteger 20
          dummyBI = BinderInfoData Omega () Nothing
          prim0 = PrimopIdGeneral "test"

      describe "simple tail cases" $ do
        it "converts variables" $
          let term = V v0
              anf = AnfReturn $ V.singleton v0
          in toAnf term `shouldBe` anf

        -- TODO(bts): add test for throwing errors upon binder shifts

        it "converts literals" $
          let lit = LInteger 42
              term = ELit lit
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLit lit)
                           (AnfReturn $ V.singleton v0)
          in toAnf term `shouldBe` anf

        it "converts returns" $
          let term = Return $ V.fromList [ELit ten, V v0]
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $ AllocLit ten)
                            (AnfReturn $ V.fromList [v0, v1])
           in toAnf term `shouldBe` anf

        it "converts delays" $
          let -- delay ((0) (0))
              term = Delay $ App (V v0) $ V.singleton (V v0)
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $
                              AllocThunk $
                               AnfTailCall $ AppFun v0 $ V.singleton v0)
                            (AnfReturn $ V.singleton v0)
          in toAnf term `shouldBe` anf

        it "converts thunk invocations" $
          let -- force (delay 10)
              term = EnterThunk (Delay $ ELit ten)
              -- letA (delay (letA 10 in (0)))
              -- in   force (0)
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $
                              AllocThunk (AnfLet (Arity 1)
                                                 (RhsAlloc $ AllocLit ten)
                                                 (AnfReturn $ V.singleton v0)))
                            (AnfTailCall $ AppThunk v0)
          in toAnf term `shouldBe` anf

        it "converts no-arg tail calls" $
          let term = App (V v0) $ V.fromList []
              anf  = AnfTailCall $ AppFun v0 $ V.fromList []
          in toAnf term `shouldBe` anf

        it "converts single-arg tail calls" $
          let term = App (V v0) $ V.singleton $ V v0
              anf  = AnfTailCall $ AppFun v0 $ V.singleton v0
          in toAnf term `shouldBe` anf

        it "converts multi-arg tail calls" $
          let term = App (V v0) $ V.fromList [ELit ten, V v0]
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $ AllocLit ten)
                            (AnfTailCall $ AppFun v1
                                                  (V.fromList [v0, v1]))
          in toAnf term `shouldBe` anf

        it "converts tail prim apps" $
          let term = PrimApp prim0 $ V.fromList [ELit ten, V v0]
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $ AllocLit ten)
                            (AnfTailCall $ AppPrim prim0
                                                   (V.fromList [v0, v1]))
          in toAnf term `shouldBe` anf

        it "converts lambdas by introducing an allocation" $
          let term = Lam (V.singleton dummyBI)
                         (V v1)
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLam (Arity 1)
                                                (AnfReturn $ V.singleton v1))
                           (AnfReturn $ V.singleton v0)
          in toAnf term `shouldBe` anf

        it "converts lets with a debruijn var on the RHS" $
          let term = Let (V.singleton dummyBI)
                         (V v1_1)
                         (V v0)
              anf = AnfReturn $ V.singleton v1_1
          in toAnf term `shouldBe` anf

        it "converts lets with a global var on the RHS" $
          let term = Let (V.singleton dummyBI)
                         (V add)
                         (V v0)
              anf = AnfReturn $ V.singleton add
          in toAnf term `shouldBe` anf

        it "converts non-trivial lets" $
          let term = Let (V.singleton dummyBI)
                         (App (V abs) $ V.singleton $ V v0)
                         (App (V neg) $ V.singleton $ V v0)
              anf = AnfLet (Arity 1)
                           (RhsApp $ AppFun abs $ V.singleton v0)
                           (AnfTailCall $ AppFun neg $ V.singleton v0)
          in toAnf term `shouldBe` anf

      describe "non-tail cases" $ do
        it "converts variables bumped by a literal allocation" $
          let lit = LInteger 5
              term = App (V v0) $ V.singleton $ ELit lit
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLit lit)
                           (AnfTailCall $ AppFun v1 $ V.singleton v0)
          in toAnf term `shouldBe` anf

        -- TODO(bts): add test for throwing errors upon binder shifts

        it "converts returns on the RHS of a let" $
           let term = Let (V.replicate 2 dummyBI)
                          (Return $ V.fromList [ELit ten, V v0])
                          (Return $ V.fromList [V v0_1, V v0_0])
               anf  = AnfLet (Arity 1)
                             (RhsAlloc $ AllocLit ten)
                             (AnfReturn $ V.fromList [v1, v0])
           in toAnf term `shouldBe` anf

        it "converts delays" $
          let -- (1) (delay ((0) (0)))
              term = App (V v1)
                         (V.singleton $
                           Delay $
                             App (V v0) $ V.singleton (V v0))
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $
                              AllocThunk $
                               AnfTailCall $ AppFun v0 $ V.singleton v0)
                            (AnfTailCall $
                              AppFun v2 $ V.singleton v0)
          in toAnf term `shouldBe` anf

        it "converts thunk invocations" $
          let -- (force (delay id)) 10
              term = App (EnterThunk (Delay $ V id_))
                         (V.singleton $ ELit ten)
              -- letA (delay id) in letA force (0) in letA 10 in letA (1) (0)
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $
                              AllocThunk $ AnfReturn $ V.singleton id_)
                            (AnfLet (Arity 1)
                                    (RhsApp $ AppThunk v0)
                                    (AnfLet (Arity 1)
                                            (RhsAlloc $ AllocLit ten)
                                            (AnfTailCall $
                                              AppFun v1 $ V.singleton v0)))
          in toAnf term `shouldBe` anf

        it "converts no-arg non-tail calls" $
          let term = App (V abs)
                         (V.singleton $ App (V v0)
                                            (V.fromList []))
              anf  = AnfLet (Arity 1)
                            (RhsApp $ AppFun v0 $ V.fromList [])
                            (AnfTailCall $ AppFun abs $ V.singleton v0)
          in toAnf term `shouldBe` anf

        it "converts single-arg non-tail calls" $
          let lit = LInteger (-10)
              -- abs (neg -10)
              term = App (V abs)
                         (V.singleton $ App (V neg)
                                            (V.singleton $ ELit lit))
              -- letA -10 in letA neg (0) in abs (0)
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLit lit)
                           (AnfLet (Arity 1)
                                   (RhsApp $ AppFun neg $ V.singleton v0)
                                   (AnfTailCall $ AppFun abs $ V.singleton v0))
          in toAnf term `shouldBe` anf

        it "converts multi-arg non-tail calls" $
          let -- abs ((0) 10 (0))
              term = App (V abs)
                         (V.singleton $ App (V v0)
                                            (V.fromList [ELit ten, V v0]))
              -- letA 10 in letA (1) (0) (1) in letA abs (0)
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $ AllocLit ten)
                            (AnfLet (Arity 1)
                                    (RhsApp $ AppFun v1 $ V.fromList [v0, v1])
                                    (AnfTailCall $ AppFun abs $ V.singleton v0))
          in toAnf term `shouldBe` anf

        it "converts non-tail prim apps" $
          let -- (prim0 10 (0)) 20
              term = App (PrimApp prim0 $ V.fromList [ELit ten, V v0])
                         (V.singleton $ ELit twenty)
              anf  = AnfLet (Arity 1)
                            (RhsAlloc $ AllocLit ten)
                            (AnfLet (Arity 1)
                                    (RhsApp $
                                      AppPrim prim0 (V.fromList [v0, v1]))
                                    (AnfLet (Arity 1)
                                            (RhsAlloc $ AllocLit twenty)
                                            (AnfTailCall $
                                              AppFun v1 (V.singleton v0))))
          in toAnf term `shouldBe` anf

        it "converts lambdas" $
          -- (λ. neg (abs (0))) (0)
          let term = App (Lam (V.singleton dummyBI)
                              (App (V neg)
                                   (V.singleton (App (V abs)
                                                     (V.singleton $ V v0)))))
                         (V.singleton $ V v0)
              -- letA (λ. letA abs (0) in neg (0)) in (0) (1)
              anf = AnfLet (Arity 1)
                           (RhsAlloc $
                             AllocLam (Arity 1)
                                      (AnfLet (Arity 1)
                                              (RhsApp $ AppFun abs $ V.singleton v0)
                                              (AnfTailCall $ AppFun neg $ V.singleton v0)))
                           (AnfTailCall $ AppFun v0 $ V.singleton v1)
          in toAnf term `shouldBe` anf

        it "converts lets (AnfBinding/trackBinding)" $
          let ten = LInteger 10
              -- let 10 in (let 20 in (λ. (1)) (0)
              term = Let (V.singleton dummyBI)
                         (ELit ten)
                         (App (Let (V.singleton dummyBI)
                                   (ELit twenty)
                                   (Lam (V.singleton dummyBI)
                                        (V v1)))
                              (V.singleton $ V v0))
              -- letT 10 in letT 20 in letA (λ. (1)) in (0) (2)
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLit ten)
                           (AnfLet (Arity 1)
                                   (RhsAlloc $ AllocLit twenty)
                                   (AnfLet (Arity 1)
                                           (RhsAlloc $
                                             AllocLam (Arity 1)
                                                      (AnfReturn $ V.singleton v1))
                                           (AnfTailCall $
                                             AppFun v0 $ V.singleton v2)))
          in toAnf term `shouldBe` anf

        it "eliminates lets with both a trivial RHS and body (AnfBinding/trackVariable)" $
          let ten = LInteger 10
              -- (let f = add in f) 10
              term = App (Let (V.singleton dummyBI)
                              (V add)
                              (V v0))
                         (V.singleton $ ELit ten)
              -- letA 10 in add (0)
              anf = AnfLet (Arity 1)
                           (RhsAlloc $ AllocLit ten)
                           (AnfTailCall $
                             AppFun add $ V.singleton v0)
          in toAnf term `shouldBe` anf

        it "converts lets with a non-trivial let on the rhs (TermBinding/trackBinding)" $
          let ten = LInteger 10
              -- let f = (let g = id abs in id g)
              -- in  f 10
              term = Let (V.singleton dummyBI)
                         (Let (V.singleton dummyBI)
                              (App (V id_) $ V.singleton $ V abs)
                              (App (V id_) $ V.singleton $ V v0))
                         (App (V v0) $ V.singleton $ ELit ten)
              --  letT id abs in letT id (0) in letA 10 in (1) (0)
              anf = AnfLet (Arity 1)
                           (RhsApp $ AppFun id_ $ V.singleton abs)
                           (AnfLet (Arity 1)
                                   (RhsApp $ AppFun id_ $ V.singleton v0)
                                   (AnfLet (Arity 1)
                                           (RhsAlloc $ AllocLit ten)
                                           (AnfTailCall $ AppFun v1 $ V.singleton v0)))
          in toAnf term `shouldBe` anf

        it "converts lets with a trivial-body let on the rhs (TermBinding/trackVariable)" $
          let ten = LInteger 10
              -- let (let (id abs) in (1))
              -- in  (0) 10
              term = Let (V.singleton dummyBI)
                         (Let (V.singleton dummyBI)
                              (App (V id_) $ V.singleton $ V abs)
                              (V v1))
                         (App (V v0) $ V.singleton $ ELit ten)
              -- letT id abs in letA 10 in (2) (0)
              anf = AnfLet (Arity 1)
                           (RhsApp $ AppFun id_ $ V.singleton abs)
                           (AnfLet (Arity 1)
                                   (RhsAlloc $ AllocLit ten)
                                   (AnfTailCall $ AppFun v2 $ V.singleton v0))
          in toAnf term `shouldBe` anf
