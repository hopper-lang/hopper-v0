{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
module Hopper.Internal.LoweredCore.EvalClosureConvertedANF where

import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.Runtime.Heap
import Hopper.Internal.Runtime.HeapRef
import Data.Hop.Or
import Control.Monad.STE
import Data.Data
import Data.Word(Word64)
import GHC.Generics
import qualified Data.Vector as V
import Hopper.Internal.Core.Literal(PrimOpId)
import Control.Monad.Trans.Class (lift)

-- | CCAnfEnvStack will eventually blur into whatever register allocation execution model we adopt
data EnvStackCC =
    EnvConsCC !Ref !EnvStackCC
    | EnvEmptyCC
  deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)
data ControlStackCC  =
      LetBinderCC !(V.Vector BinderInfoCC)
                !()
                !EnvStackCC -- the current environment, only needed on nontail calls, not on simple allocations
                            -- this can be optimized / analyzed away later, for now lets conflate the two
                !AnfCC --- body of let
                !ControlStackCC -- what happens after the body of let returns!
      | ControlStackEmptyCC  -- we're done!
      | UpdateHeapRefCC
            !Ref
            !ControlStackCC
  deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)

data CCAnfEvalError =
    BadLocalVariable LocalVariableCC {- CODE LOCATION OR PARENT CLOSURE ON STACK?? -}

{-
NB: the use of the words enter, apply etc shouldn't be taken to mean push/enter vs eval/apply
because this is sort of in between! :)
-}


localEnvLookup ::  EnvStackCC -> LocalVariableCC -> (STE (c :+ CCAnfEvalError :+ HeapError ) s  Ref )
localEnvLookup env var@(LocalVarCC theVar) = go env theVar
  where
    go :: EnvStackCC -> Word64 ->  (STE (c :+ CCAnfEvalError :+ HeapError ) s  Ref )
    go EnvEmptyCC _ = throwSTE $ InR $   InL  $ BadLocalVariable var
    go (EnvConsCC theRef _) 0  = return theRef
    go (EnvConsCC _ rest) w = go rest (w - 1)

evalCCAnf :: CodeRegistryCC -> EnvStackCC -> ControlStackCC -> AnfCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
evalCCAnf codeReg envStack contStack  (ReturnCC localVarLS) =  do resRefs <- lift  $ traverse (localEnvLookup envStack) localVarLS
                                                                  enterControlStackCC codeReg contStack resRefs
evalCCAnf codeReg envStack contStack  (LetNFCC binders rhscc bodcc) =
                        dispatchRHSCC codeReg envStack
                                  (LetBinderCC binders () envStack bodcc contStack)
                                  rhscc
evalCCAnf codeReg envStack contStack  (TailCallCC appcc ) = applyCC codeReg envStack contStack appcc

-- | dispatchRHSCC is a wrapper for calling either allocateCC OR applyCC
dispatchRHSCC::  CodeRegistryCC -> EnvStackCC -> ControlStackCC -> RhsCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
dispatchRHSCC = undefined

--- allocateRHSCC always constructs a SINGLE heap ref to whatever it just allocated,
allocateRHSCC::  CodeRegistryCC -> EnvStackCC -> ControlStackCC -> AllocCC
  -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
allocateRHSCC = undefined

applyCC :: CodeRegistryCC -> EnvStackCC -> ControlStackCC -> AppCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
applyCC = undefined

-- enterOrResolveThunkCC will push a update Frame onto the control stack if its evaluating a thunk closure that hasn't been computed
-- yet
-- Will put a blackhole on that heap location in the mean time
-- if the initial lookup IS a blackhole, we have an infinite loop, abort!
-- because our type system will distinguish thunks from ordinary values
-- this is the only location that expects a black hole in our code base ??? (not sure, but maybe)
enterOrResolveThunkCC :: CodeRegistryCC -> EnvStackCC -> ControlStackCC -> LocalVariableCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
enterOrResolveThunkCC = undefined

{-
benchmarking Question: would passing the tuply args as unboxed tuples,
a la (# LocalVariableCC, V.Vector LocalVariableCC #) have decent performance impact?
AND/OR, should we use unboxed/storable vector for fixed size element types like LocalVariableCC

this will require analyzing core, and designing some sort of performance measurement!
-}

enterClosureCC :: CodeRegistryCC -> EnvStackCC -> ControlStackCC
        -> (LocalVariableCC,V.Vector LocalVariableCC)
        -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
enterClosureCC = undefined

enterPrimAppCC :: CodeRegistryCC -> EnvStackCC -> ControlStackCC
        -> (PrimOpId,V.Vector LocalVariableCC)
        -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
enterPrimAppCC = undefined

enterControlStackCC :: CodeRegistryCC  -> ControlStackCC -> (V.Vector Ref) -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
enterControlStackCC = undefined

{-    = ReturnCC ![LocalVariableCC]
    | LetNFCC
          {- TODO: src loc info -}
          ![(Bool,Maybe Text)]   -- TODO FIXME, replace with CCAnfBinderInfo
            -- the length == size of RHS multiple return value tuple
                 -- the True positions are the ones whose heap refs are copied into the
                 -- local environment stack
                 -- this is like a wimpy version of pattern matching on products
          !(RhsCC) -- right hand side of let binder, closure converted
          !(AnfCC) -- body of the let
    | TailCallCC !(AppCC)-}

-- evalANF ::  Anf Ref -> ControlStackAnf -> HeapStepCounterM hepRep (STE (c :+ ErrorEvalAnf :+ HeapError ) s) Ref
