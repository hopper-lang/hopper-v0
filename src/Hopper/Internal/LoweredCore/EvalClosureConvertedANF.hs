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
{-# LANGUAGE CPP #-}

module Hopper.Internal.LoweredCore.EvalClosureConvertedANF where

import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.Runtime.Heap (
  HeapError(..)
  ,HeapStepCounterM
  ,unsafeHeapUpdate
  ,heapAllocate
  ,heapLookup
  ,checkedCounterIncrement
  ,checkedCounterJump
  ,throwHeapErrorWithStepInfoSTE
  ,transitiveHeapLookup
  )
import Hopper.Internal.Runtime.HeapRef (Ref)
import Data.Hop.Or
import Control.Monad.STE
import Data.Data
import qualified Data.Map as Map
import Data.Word(Word64)
import GHC.Generics
import Numeric.Natural
import qualified Data.Vector as V
import Hopper.Internal.Core.Literal(PrimOpId)

type EvalCC c s a
  = HeapStepCounterM (ValueRepCC Ref)
                     (STE (c :+ EvalErrorCC (ValueRepCC Ref) :+ HeapError) s)
                     a

-- once i have explicit exports in this module, this will be dead code
suppressUnusedWarnings :: Int
suppressUnusedWarnings = undefined unsafeHeapUpdate
  heapAllocate
  heapLookup
  checkedCounterIncrement
  checkedCounterJump

{- FIXME: we currently have a quadratic blowup for high-arity curried functions
   with this naive (implicit) closure conversion setup. we can fix this by
   making packs and unpacks explicit and cons-style sharing when we desugar
   curried functions (or, more generally, user code that has similar semantics).

   we can assign metadata to our lambdas to hint at such optimizations
-}

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

newtype InterpreterStepCC = InterpreterStepCC { unInterpreterStep :: Natural } deriving (Eq, Read,Show,Ord,Typeable,Generic,Data)



{- |  EvalErrorCC is for runtime errors!
TODO: add code location and stack trace meta data
TODO: refactor duplicated fields into an outer ADT?-}
data EvalErrorCC val =
    BadLocalVariableCC
                      {eeCCOffendingOpenLocalVariable :: !LocalVariableCC
                      , eeCCcontrolStackAtError:: !ControlStackCC
                      , eeCCReductionStepAtError :: !InterpreterStepCC}
   |  UnexpectedNotAClosureInFunctionPosition
                      {eeCCOffendingClosureLocalVariable :: !LocalVariableCC
                      ,eeCCOffendingNotAClosure :: !val
                      ,eeCCcontrolStackAtError :: !ControlStackCC
                      ,eeCCHeapLookupStepOffset :: !Natural --
                      ,eeCCReductionStepAtError:: !InterpreterStepCC }
   | UnexpectedNotThunkInForcePosition
                      {eeCCOffendingClosureLocalVariable :: !LocalVariableCC
                      ,eeCCOffendingNotAClosure :: !val
                      ,eeCCcontrolStackAtError :: !ControlStackCC
                      ,eeCCHeapLookupStepOffset :: !Natural --
                      ,eeCCReductionStepAtError:: !InterpreterStepCC }
   | HardFaultImpossiblePanicError
                      {eeCCcontrolStackAtError :: !ControlStackCC
                      ,eeCCHeapLookupStepOffset :: !Natural -- this is a number to
                                                   -- subtract from the reported
                                                   -- interpreter step
                      ,eeCCReductionStepAtError:: !InterpreterStepCC
                      ,eeCCErrorPanicMessage :: String
                      ,eeCCErrorPanicFileName :: String
                      ,eeCCErrorPanicFileLine :: Int
                      -- TODO: add filename and line of haskell source
                      }
   deriving (Eq,Ord,Show,Typeable,Read)

#define PanicMessageConstructor(constack,stepAdjust,reductionStep,msg) \
  (HardFaultImpossiblePanicError (constack) (stepAdjust) \
      (reductionStep) (msg) \
      __FILE__ \
      __LINE__ \
      )


{-
NB: the use of the words enter, apply etc shouldn't be taken to mean push/enter vs eval/apply
because this is sort of in between! :)
-}

throwEvalError
  :: (Natural -> EvalErrorCC val)
  -> HeapStepCounterM val (STE (a :+ ((EvalErrorCC val) :+ HeapError)) s) result
throwEvalError handler = throwHeapErrorWithStepInfoSTE $ InR . InL . handler

localEnvLookup
  :: CodeRegistryCC -- TODO: will we need this here?
  -> EnvStackCC
  -> ControlStackCC
  -> LocalVariableCC
  -> forall c. EvalCC c s Ref
localEnvLookup _codeReg env controlStack var@(LocalVarCC theVar) = go env theVar
  where
    go :: EnvStackCC -> Word64 -> EvalCC c s Ref
    go EnvEmptyCC _ = throwEvalError (\n ->
                        BadLocalVariableCC var controlStack (InterpreterStepCC n))
    go (EnvConsCC theRef _) 0 = return theRef
    go (EnvConsCC _ rest) w = go rest (w - 1)

evalCCAnf
  :: CodeRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AnfCC
  -> forall c. EvalCC c s (V.Vector Ref)
evalCCAnf codeReg envStack contStack (ReturnCC localVarLS) = do
  resRefs <- traverse (localEnvLookup codeReg envStack contStack) localVarLS
  enterControlStackCC codeReg contStack resRefs
evalCCAnf codeReg envStack contStack (LetNFCC binders rhscc bodcc) =
  dispatchRHSCC codeReg
                envStack
                (LetBinderCC binders () envStack bodcc contStack)
                rhscc
evalCCAnf codeReg envStack contStack (TailCallCC appcc) =
  applyCC codeReg envStack contStack appcc

-- | dispatchRHSCC is a wrapper for calling either allocateCC OR applyCC
dispatchRHSCC
  :: CodeRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> RhsCC
  -> forall c. EvalCC c s (V.Vector Ref)
dispatchRHSCC = undefined

--- allocateRHSCC always constructs a SINGLE heap ref to whatever it just allocated,
allocateRHSCC
  :: CodeRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AllocCC
  -> forall c. EvalCC c s (V.Vector Ref)
allocateRHSCC = undefined

applyCC
  :: CodeRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AppCC
  -> forall c. EvalCC c s (V.Vector Ref)
applyCC = undefined

-- enterOrResolveThunkCC will push a update Frame onto the control stack if its evaluating a thunk closure that hasn't been computed
-- yet
-- Will put a blackhole on that heap location in the mean time
-- if the initial lookup IS a blackhole, we have an infinite loop, abort!
-- because our type system will distinguish thunks from ordinary values
-- this is the only location that expects a black hole in our code base ??? (not sure, but maybe)
enterOrResolveThunkCC
  :: CodeRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> LocalVariableCC
  -> forall c. EvalCC c s (V.Vector Ref)
enterOrResolveThunkCC = undefined

{-
benchmarking Question: would passing the tuply args as unboxed tuples,
a la (# LocalVariableCC, V.Vector LocalVariableCC #) have decent performance impact?
AND/OR, should we use unboxed/storable vector for fixed size element types like LocalVariableCC

this will require analyzing core, and designing some sort of performance measurement!
-}

-- FIXME : think about ways to make error extension easier

hoistedTransitiveLookup
  :: Ref
  -> forall c. EvalCC c s (Natural, ValueRepCC Ref)
hoistedTransitiveLookup ref = extendErrorTrans (transitiveHeapLookup ref)

{-# SPECIALIZE compatibleEnv :: V.Vector a -> ClosureCodeRecordCC -> Bool #-}
{-# SPECIALIZE compatibleEnv :: V.Vector a -> ThunkCodeRecordCC -> Bool #-}
compatibleEnv :: CodeRecord r => V.Vector a -> r -> Bool
compatibleEnv envRefs rec = refCount == V.length (envBinders rec)
                         && refCount == fromIntegral (envSize rec)
  where
    refCount = V.length envRefs

lookupHeapClosure
  :: CodeRegistryCC
  -> ControlStackCC
  -> LocalVariableCC
  -> Ref
  -> forall c. EvalCC c s (V.Vector Ref, ClosureCodeId, ClosureCodeRecordCC)
lookupHeapClosure (CodeRegistryCC _thunk closureMap) stack var initialRef = do
  (closureEnvRefs, codeId) <- deref initialRef
  mCodeRecord <- return $ Map.lookup codeId closureMap
  case mCodeRecord of
    Just cdRecord | compatibleEnv closureEnvRefs cdRecord ->
                      return (closureEnvRefs, codeId, cdRecord)
                  | otherwise -> throwEvalError (\step ->
                      PanicMessageConstructor(stack, 1, InterpreterStepCC step, "closure env size mismatch"))
    Nothing -> throwEvalError (\step ->
      PanicMessageConstructor(stack, 1, InterpreterStepCC step, "closure code ID " ++ show codeId ++ " not in code registry"))

  where
    deref :: Ref -> forall c. EvalCC c s (V.Vector Ref, ClosureCodeId)
    deref ref = do
      (lookups, val) <- hoistedTransitiveLookup ref
      case val of
         ClosureCC envRefs codeId -> return (envRefs, codeId)
         _ -> throwEvalError $ \step ->
           UnexpectedNotAClosureInFunctionPosition var
                                                   val
                                                   stack
                                                   lookups
                                                   (InterpreterStepCC step)

-- TODO: reduce duplication between lookupHeap{Closure,Thunk}.
--       e.g. logic for whether env is "compatible"
lookupHeapThunk
  :: CodeRegistryCC
  -> ControlStackCC
  -> LocalVariableCC
  -> Ref
  -> forall c. EvalCC c s (V.Vector Ref, ThunkCodeId, ThunkCodeRecordCC)
lookupHeapThunk (CodeRegistryCC thunks _closures) stack var initialRef = do
  (envRefs, codeId) <- deref initialRef
  let mCodeRecord = Map.lookup codeId thunks
  case mCodeRecord of
    Just codeRec
      | compatibleEnv envRefs codeRec -> return (envRefs, codeId, codeRec)
      | otherwise -> throwEvalError $ \step ->
          PanicMessageConstructor(stack, 1, InterpreterStepCC step, "thunk env size mismatch")
    Nothing -> throwEvalError $ \step ->
      PanicMessageConstructor(stack, 1, InterpreterStepCC step, "thunk code ID " ++ show codeId ++ " not in code registry")

  where
    deref :: Ref -> forall c. EvalCC c s (V.Vector Ref, ThunkCodeId)
    deref ref = do
      (lookups, val) <- hoistedTransitiveLookup ref
      case val of
         ThunkCC envRefs codeId -> return (envRefs, codeId)
         _ -> throwEvalError $ \step ->
           UnexpectedNotThunkInForcePosition var
                                             val
                                             stack
                                             lookups
                                             (InterpreterStepCC step)

{- | enterClosureCC has to resolve its first heap ref argument to the closure code id
and then it pushes
-}
-- TODO: reduce duplication between lookupHeap{Closure,Thunk}.
--       e.g. logic for whether env is "compatible"
enterClosureCC
  :: CodeRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> (LocalVariableCC, V.Vector LocalVariableCC)
  -> forall c. EvalCC c s (V.Vector Ref)
enterClosureCC _codReg@(CodeRegistryCC _thunk _closureMap)
               envStack
               controlstack
               (localClosureVar, localArgs)
                = undefined    envStack
                               controlstack
                               (localClosureVar,localArgs)

{- | enterPrimAppCC is special in a manner similar to enterOrResolveThunkCC
this is because some primitive operations are ONLY defined on suitably typed Literals,
such as natural number addition. So enterPrimAppCC will have to chase indirections for those operations,
AND validate that it has the right arguments etc.
This may sound like defensive programming, because a sound type system and type preserving
compiler / interpreter transformations DO guarantee that this shall never happen,
but cosmic radiation, a bug in GHC, or a bug in the hopper infrastructure (the most likely :) )  could
result in a mismatch between reality and our expectations, so never hurts to check.
-}
enterPrimAppCC
  :: CodeRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> (PrimOpId, V.Vector LocalVariableCC)
  -> forall c. EvalCC c s (V.Vector Ref)
enterPrimAppCC = undefined

enterControlStackCC
  :: CodeRegistryCC
  -> ControlStackCC
  -> V.Vector Ref
  -> forall c. EvalCC c s (V.Vector Ref)
enterControlStackCC = undefined

-- evalANF ::  Anf Ref -> ControlStackAnf -> EvalCC c s Ref
