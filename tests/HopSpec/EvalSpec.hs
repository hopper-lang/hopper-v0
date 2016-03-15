{-# LANGUAGE LambdaCase, TypeOperators, RankNTypes, ScopedTypeVariables,BangPatterns #-}
module HopSpec.EvalSpec (spec) where

import Test.Hspec
import Test.HUnit.Base
import Control.Arrow (left)
import Control.Exception
import Control.Lens
import Control.Monad.STE
import Control.Monad.State
import Data.HopperException
import qualified Data.Map as Map
import Data.Word
import qualified Data.Vector as V
import Hopper.Internal.Core.Literal
import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.LoweredCore.EvalClosureConvertedANF as Eval
import Hopper.Internal.Runtime.Heap
import Hopper.Internal.Runtime.HeapRef
import Hopper.Internal.Type.Relevance
import Hopper.Utils.LocallyNameless

emptySymbolReg :: SymbolRegistryCC
emptySymbolReg = SymbolRegistryCC Map.empty Map.empty Map.empty

makeInt :: Integer -> ValueRepCC Ref
makeInt = ValueLitCC . LInteger

spec :: Spec
spec = describe "Evaluation Spec" $ do
  it "evaluates `1 + 1`" $
    let
      startHeap = Heap (Ref 2) Map.empty $ Map.fromList
        [ (Ref 0, makeInt 1)
        , (Ref 1, makeInt 1)
        ]
      stack = ControlStackEmptyCC
      envStack = Eval.envStackFromList [V.singleton (Ref 0), V.singleton (Ref 1)]
      addVars = V.fromList
        [ LocalVar (LocalNamelessVar 0 (BinderSlot 0))
        , LocalVar (LocalNamelessVar 1 (BinderSlot 0))
        ]
      tm = TailCallCC (PrimAppCC (TotalMathOpGmp IntAddOpId) addVars)
      calculation = evalCCAnf emptySymbolReg envStack stack tm

      results :: Either String (V.Vector Ref, CounterAndHeap (ValueRepCC Ref))
      results = handleSTE (left handleSTEErr) $ runHeap startHeap 100 calculation

    in case results of
         Left e -> assertFailure e
         Right (results', CounterAndHeap _ _ _ (Heap _ _ heap)) -> do
           assertBool "returns right number of results" $ V.length results' == 1
           assertBool "has right result" $
             (heap Map.! (results' V.! 0)) == makeInt 2


  it "throws a hard fault when a primop is not given enough args" $
    let startHeap = Heap (Ref 1) Map.empty $ Map.singleton (Ref 0) (makeInt 1)
        stack = ControlStackEmptyCC
        envStack = Eval.envStackFromList [V.singleton (Ref 0)]
        addVars = V.singleton (LocalVar (LocalNamelessVar 0 (BinderSlot 0)))
        tm = TailCallCC (PrimAppCC (TotalMathOpGmp IntAddOpId) addVars)
        calculation = evalCCAnf emptySymbolReg envStack stack tm
        handler :: Either SomeHopperException
                          (V.Vector Ref, CounterAndHeap (ValueRepCC Ref))
                -> Bool
        handler (Left she)
          | Just (HardFaultImpossiblePanicError _ _ _ _ _ _) <- she^?_EvalErrorCC
          = True
        handler _ = False

    in handleSTE handler (runHeap startHeap 100 calculation)

  it "evaluates closures" $ do
    -- let's try to evaluate "id 1 -> 1"
    --
    -- heap:
    --   0 -> id (ClosureCC)
    --   1 -> 1 (ValueLitCC)
    --
    -- term under evaluation:
    --   TailCallCC (id x)
    --
    -- control stack:
    --   <empty> (halt when the tail call returns)
    --
    -- environment stack:
    --   1
    --   id
    let idRef = Ref 0
        numRef = Ref 1

        -- let id be bound in the enclosing scope and x in the innermost scope
        deBruijn :: Word32 -> Variable
        deBruijn n = LocalVar (LocalNamelessVar n (BinderSlot 0))
        idCodeId = ClosureCodeId 0
        idCodeRecord = ClosureCodeRecordCC
          (EnvSize 0)
          V.empty
          (CodeArity 1)
          (V.singleton (BinderInfoDataCC Omega () Nothing))
          -- 1 since we need to skip over the closure env
          (ReturnCC (V.singleton (deBruijn 1)))
        startHeap = Heap (Ref 2) Map.empty $ Map.fromList
          [ (numRef, makeInt 1)
          , (idRef, ClosureCC V.empty idCodeId)
          ]
        stack = ControlStackEmptyCC
        symbolReg = SymbolRegistryCC
          Map.empty
          (Map.singleton idCodeId idCodeRecord)
          Map.empty
        envStack = Eval.envStackFromList [V.singleton numRef, V.singleton idRef]
        tm = TailCallCC (FunAppCC (deBruijn 1) (V.singleton (deBruijn 0)))
        calculation = evalCCAnf symbolReg envStack stack tm
        results = handleSTE (left handleSTEErr) $ runHeap startHeap 100 calculation

    case results of
         Left e -> assertFailure e
         Right (results', CounterAndHeap _ _ _ (Heap _ _ heap)) -> do
           assertEqual "returns the right number of results"
             (V.length results') 1
           assertBool "the old closure now points to an indirection" $
             case heap Map.! idRef of
               IndirectionCC _ -> True
               _ -> False
           assertEqual "has right result"
             (heap Map.! (results' V.! 0)) (makeInt 1)


-- We don't actually expect any exceptions in these tests so just use this
-- handler for all of them
handleSTEErr :: SomeHopperException -> String
handleSTEErr she
  | Just err <- she^?_EvalErrorCC = case err of
      HardFaultImpossiblePanicError stack offset step msg filename fileline ->
        unlines
          [ "-- Eval Error (this is bad, bad news) --"
          , ""
          , "Here's what we know:"
          , "> " ++ msg
          , ""
          , unwords ["via", filename, "line", show fileline]
          ]
      _ -> show err
  | Just err <- she^?_HeapError = show err
  | otherwise = "boom boom boom"
