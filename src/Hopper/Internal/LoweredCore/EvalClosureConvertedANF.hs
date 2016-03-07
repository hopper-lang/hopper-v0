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
  ,checkedCounterCost
  ,throwHeapErrorWithStepInfoSTE
  ,transitiveHeapLookup
  )
import Hopper.Internal.Runtime.HeapRef (Ref)
import Data.Hop.Or
import Control.Monad.STE
import Data.Data
import qualified Data.Map as Map
import Data.Word(Word64,Word32)
import GHC.Generics
import Numeric.Natural
import qualified Data.Vector as V
import Hopper.Internal.Core.Literal (Literal, PrimOpId)

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
  checkedCounterCost

{- FIXME: we currently have a quadratic blowup for high-arity curried functions
   with this naive (implicit) closure conversion setup. we can fix this by
   making packs and unpacks explicit and cons-style sharing when we desugar
   curried functions (or, more generally, user code that has similar semantics).

   we can assign metadata to our lambdas to hint at such optimizations
-}

{-
TODO: switch to 2dim style debruijn

-}

-- | CCAnfEnvStack will eventually blur into whatever register allocation execution model we adopt
data EnvStackCC =
    EnvConsCC !(V.Vector Ref) !EnvStackCC
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
    BadVariableCC
                      {eeCCOffendingOpenLocalVariable :: !Variable
                      , eeCCcontrolStackAtError:: !ControlStackCC
                      , eeCCReductionStepAtError :: !InterpreterStepCC}
   |  UnexpectedNotAClosureInFunctionPosition
                      {eeCCOffendingClosureLocalVariable :: !Variable
                      ,eeCCOffendingNotAClosure :: !val
                      ,eeCCcontrolStackAtError :: !ControlStackCC
                      ,eeCCHeapLookupStepOffset :: !Natural --
                      ,eeCCReductionStepAtError:: !InterpreterStepCC }
   | UnexpectedNotThunkInForcePosition
                      {eeCCOffendingClosureLocalVariable :: !Variable
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
   | UnexpectedNotLiteral
                      {eeCCOffendingClosureLocalVariable :: !Variable
                      ,eeCCOffendingNotAClosure :: !val
                      ,eeCCcontrolStackAtError :: !ControlStackCC
                      ,eeCCHeapLookupStepOffset :: !Natural --
                      ,eeCCReductionStepAtError:: !InterpreterStepCC }
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
  :: EnvStackCC
  -> ControlStackCC
  -> LocalNamelessVar
  -> forall c. EvalCC c s Ref
localEnvLookup env controlStack var@(LocalNamelessVar depth  (BinderSlot slot )  ) = go env depth
  where
    go :: EnvStackCC -> Word32  -> EvalCC c s Ref
    go EnvEmptyCC _ = throwEvalError (\n ->
                        BadVariableCC (LocalVar var) controlStack (InterpreterStepCC n))
    go (EnvConsCC theRefVect _) 0 = maybe
              (throwEvalError (\n ->
                              BadVariableCC (LocalVar var) controlStack (InterpreterStepCC n)))
              return
              (theRefVect V.!?  ( fromIntegral slot))
    go (EnvConsCC _ rest) w = go rest (w - 1)

evalCCAnf
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AnfCC
  -> forall c. EvalCC c s (V.Vector Ref)
evalCCAnf codeReg envStack contStack (ReturnCC (localVarLS)) = do
  resRefs <- traverse (localEnvLookup envStack contStack)  $ (error "FIX THIS") localVarLS
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
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> RhsCC
  -> forall c. EvalCC c s (V.Vector Ref)
dispatchRHSCC symbolReg envStk ctrlStack rhs = case rhs of
                AllocRhsCC allocExp ->  allocateRHSCC symbolReg envStk ctrlStack allocExp

--- allocateRHSCC always constructs a SINGLE heap ref to whatever it just allocated,
allocateRHSCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AllocCC
  -> forall c. EvalCC c s (V.Vector Ref)
allocateRHSCC = undefined

applyCC
  :: SymbolRegistryCC
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
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> Variable
  -> forall c. EvalCC c s (V.Vector Ref)
enterOrResolveThunkCC = undefined

{-
benchmarking Question: would passing the tuply args as unboxed tuples,
a la (# VariableCC, V.Vector VariableCC #) have decent performance impact?
AND/OR, should we use unboxed/storable vector for fixed size element types like VariableCC

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
compatibleEnv envRefs rec = refCount == V.length (envBindersInfo rec)
                         && refCount == fromIntegral (envSize rec)
  where
    refCount = V.length envRefs

lookupHeapClosure
  :: SymbolRegistryCC
  -> ControlStackCC
  -> Variable
  -> Ref
  -> forall c. EvalCC c s (V.Vector Ref, ClosureCodeId, ClosureCodeRecordCC)
lookupHeapClosure (SymbolRegistryCC _thunk closureMap _valueTable) stack var initialRef = do
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
  :: SymbolRegistryCC
  -> ControlStackCC
  -> Variable
  -> Ref
  -> forall c. EvalCC c s (V.Vector Ref, ThunkCodeId, ThunkCodeRecordCC)
lookupHeapThunk (SymbolRegistryCC thunks _closures _values) stack var initialRef = do
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

lookupHeapLiteral
  :: EnvStackCC
  -> ControlStackCC
  -> Variable
  -> forall c. EvalCC c s Literal
lookupHeapLiteral envStack controlStack var = do
  initRef <- localEnvLookup envStack controlStack  $ error "fix this toooo " var
  deref initRef

  where
    deref :: Ref -> forall c. EvalCC c s Literal
    deref ref = do
      (lookups, val) <- hoistedTransitiveLookup ref
      case val of
        ValueLitCC l -> return l
        _ -> throwEvalError $ \step ->
          UnexpectedNotLiteral var
                               val
                               controlStack
                               lookups
                               (InterpreterStepCC step)

{- | enterClosureCC has to resolve its first heap ref argument to the closure code id
and then it pushes
-}
-- TODO: reduce duplication between lookupHeap{Closure,Thunk}.
--       e.g. logic for whether env is "compatible"
enterClosureCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> (Variable, V.Vector Variable)
  -> forall c. EvalCC c s (V.Vector Ref)
enterClosureCC _codReg@(SymbolRegistryCC _thunk _closureMap _values)
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
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> (PrimOpId, V.Vector Variable)
  -> forall c. EvalCC c s (V.Vector Ref)
enterPrimAppCC = undefined

enterControlStackCC
  :: SymbolRegistryCC
  -> ControlStackCC
  -> V.Vector Ref
  -> forall c. EvalCC c s (V.Vector Ref)
enterControlStackCC = undefined

-- evalANF ::  Anf Ref -> ControlStackAnf -> EvalCC c s Ref
