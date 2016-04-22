{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Hopper.Internal.Playground where

import Control.Lens
import Control.Monad.STE
import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as BS
import Data.HopperException
import qualified Data.Map as Map
import qualified Data.Vector as V
import Hopper.Internal.Core.Literal
import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.LoweredCore.EvalClosureConvertedANF as Eval
import Hopper.Internal.Runtime.Heap
import Hopper.Internal.Runtime.HeapRef


emptySymbolReg :: SymbolRegistryCC
emptySymbolReg = SymbolRegistryCC Map.empty Map.empty Map.empty

makeInt :: Integer -> ValueRepCC Ref
makeInt = ValueLitCC . LInteger

handleDump
  :: Either SomeHopperException (V.Vector Ref, CounterAndHeap (ValueRepCC Ref))
  -> IO ()
handleDump = \case
  Left she
    | Just state <- she^?_DumpState
    -> BS.writeFile "statedump.json" (encode state)
    | otherwise -> putStrLn "unexpected error!"
  Right _ -> putStrLn "unexpected success!"

example :: IO ()
example = do
  -- one of the examples from EvalSpec, replacing the addition primop with a
  -- dump state primop
  let startHeap = Heap (Ref 2) Map.empty $ Map.fromList
        [ (Ref 0, makeInt 1)
        , (Ref 1, makeInt 1)
        ]
      stack = ControlStackEmptyCC
      envStack = Eval.envStackFromList [V.singleton (Ref 0), V.singleton (Ref 1)]
      addVars = V.fromList
        [ LocalVar (LocalNamelessVar 0 (BinderSlot 0))
        , LocalVar (LocalNamelessVar 1 (BinderSlot 0))
        ]
      tm = TailCallCC (PrimAppCC (PrimopIdGeneral "dump state") addVars)
      calculation = evalCCAnf emptySymbolReg envStack stack tm

  handleSTE handleDump $ runHeap startHeap 100 calculation
