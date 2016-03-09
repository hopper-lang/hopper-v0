{-# LANGUAGE LambdaCase, TypeOperators #-}
module HopSpec.EvalSpec (spec) where

import Test.Hspec
import Test.HUnit.Base
import Control.Arrow (left)
import Control.Exception
import Control.Monad.STE
import Control.Monad.State
import Data.Hop.Or
import qualified Data.Map as Map
import qualified Data.Vector as V
import Hopper.Internal.Core.Literal
import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.LoweredCore.EvalClosureConvertedANF
import Hopper.Internal.Runtime.Heap
import Hopper.Internal.Runtime.HeapRef
import Hopper.Utils.LocallyNameless

emptySymbolReg :: SymbolRegistryCC
emptySymbolReg = SymbolRegistryCC Map.empty Map.empty Map.empty

makeInt :: Integer -> ValueRepCC Ref
makeInt = ValueLitCC . LInteger

spec :: Spec
spec = describe "Evaluation Spec" $
  it "evaluates `1 + 1`" $
    let
      startHeap = Heap (Ref 1) $ Map.fromList
        [ (Ref 0, makeInt 1)
        , (Ref 1, makeInt 1)
        ]
      stack = UpdateHeapRefCC (Ref 3) ControlStackEmptyCC
      -- envStack = EnvConsCC (V.fromList [Ref 0, Ref 1]) EnvEmptyCC
      envStack = EnvConsCC (V.singleton (Ref 0))
                (EnvConsCC (V.singleton (Ref 1))
                 EnvEmptyCC)
      addVars = V.fromList
        [ LocalVar (LocalNamelessVar 0 (BinderSlot 0))
        , LocalVar (LocalNamelessVar 1 (BinderSlot 0))
        -- , LocalVar (LocalNamelessVar 0 (BinderSlot 1))
        ]
      tm = TailCallCC (PrimAppCC (TotalMathOpGmp IntAddOpId) addVars)

      calculation = evalCCAnf emptySymbolReg envStack stack tm

      results :: Either String (V.Vector Ref, CounterAndHeap (ValueRepCC Ref))
      results = runSTE (runHeap startHeap 0 calculation) (left handleSTEErr)

      handleSTEErr :: () :+ (EvalErrorCC (ValueRepCC Ref) :+ HeapError) -> String
      handleSTEErr = \case
        InL () -> "failed with a mysterious left"
        InR (InL evalErr) -> show evalErr
        InR (InR heapErr) -> show heapErr
    in case results of
         Left e -> assertFailure e
         Right (results', CounterAndHeap _ _ _ (Heap _ heap)) -> do
           assertBool "returns right number of results" $ V.length results' == 1
           assertBool "has right result" $
             (heap Map.! (results' V.! 0)) == makeInt 2
