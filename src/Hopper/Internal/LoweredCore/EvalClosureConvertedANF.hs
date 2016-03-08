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
{-# LANGUAGE LambdaCase #-}

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
import Hopper.Internal.Core.Literal (
  Literal
  ,GmpMathOpId
  ,PrimOpId(..)
  ,evalTotalMathPrimopCode
  ,gmpMathCost
  ,hoistTotalMathLiteralOp
  )

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

-- Make sure this only takes one line so it doesn't throw off line numbers
#define PanicMessageConstructor(constack,stepAdjust,reductionStep,msg) (HardFaultImpossiblePanicError (constack) (stepAdjust) (reductionStep) (msg) __FILE__ __LINE__)


{-
NB: the use of the words enter, apply etc shouldn't be taken to mean push/enter vs eval/apply
because this is sort of in between! :)
-}

throwEvalError
  :: (Natural -> EvalErrorCC val)
  -> HeapStepCounterM val (STE (a :+ ((EvalErrorCC val) :+ HeapError)) s) result
throwEvalError handler = throwHeapErrorWithStepInfoSTE $ InR . InL . handler

-- | Are all the Variables in this structure local?
allLocalVars :: Foldable t => t Variable -> Bool
allLocalVars = all (\case { LocalVar _ -> True; GlobalVarSym _ -> False })

-- | Allocate a literal.
allocLit :: Literal -> EvalCC c s Ref
allocLit x = extendErrorTrans (heapAllocate (ValueLitCC x))

-- | Unsafely get a Ref from a Variable
--
-- Unsafe because you need to guarantee that it's a LocalVar rather than a
-- GlobalVarSym.
unsafeLocalEnvLookup
  :: EnvStackCC
  -> ControlStackCC
  -> Variable
  -> forall c. EvalCC c s Ref
unsafeLocalEnvLookup env control (LocalVar lv) = localEnvLookup env control lv

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

-- | dispatchRHSCC is a wrapper for calling either allocateRHSCC OR applyCC
dispatchRHSCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> RhsCC
  -> forall c. EvalCC c s (V.Vector Ref)
dispatchRHSCC symbolReg envStk ctrlStack rhs = case rhs of
  AllocRhsCC allocExp -> allocateRHSCC symbolReg envStk ctrlStack allocExp
  NonTailCallAppCC appCC -> applyCC symbolReg envStk ctrlStack appCC

-- | Construct a single heap ref for an allocation.
allocateRHSCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AllocCC
  -> forall c. EvalCC c s (V.Vector Ref)
allocateRHSCC symbolReg envStk stack@(LetBinderCC _ _ _ _ newStack) alloc =
  let errMsg = "`allocateRHSCC` expected all local refs, received a global"
      err step = PanicMessageConstructor(stack, 1, InterpreterStepCC step, errMsg)
      localGuard vars continue = if allLocalVars vars
        then continue
        else throwEvalError err
  in case alloc of
    SharedLiteralCC lit -> V.singleton <$> allocLit lit
    -- TODO(joel) - there's a silly amount of duplication here
    ConstrAppCC constrId vars -> localGuard vars $ do
      refVect <- mapM (unsafeLocalEnvLookup envStk stack) vars
      ref <- extendErrorTrans $ heapAllocate (ConstructorCC constrId refVect)
      enterControlStackCC symbolReg newStack (V.singleton ref)
    AllocateThunkCC vars thunkId -> localGuard vars $ do
      refVect <- mapM (unsafeLocalEnvLookup envStk stack) vars
      ref <- extendErrorTrans $ heapAllocate (ThunkCC refVect thunkId)
      enterControlStackCC symbolReg newStack (V.singleton ref)
    AllocateClosureCC vars _ closureId -> localGuard vars $ do
      refVect <- mapM (unsafeLocalEnvLookup envStk stack) vars
      ref <- extendErrorTrans $ heapAllocate (ClosureCC refVect closureId)
      enterControlStackCC symbolReg newStack (V.singleton ref)

-- | Evaluate an application.
--
-- We just dispatch to either `enterOrResolveThunkCC`, `enterClosureCC`, or
-- `enterPrimAppCC`.
applyCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AppCC
  -> forall c. EvalCC c s (V.Vector Ref)
applyCC = symbolReg envStk stack alloc = case alloc of
  EnterThunkCC var -> enterOrResolveThunkCC symbolReg envStk stack var
  FunAppCC var vec -> enterClosureCC symbolReg envStk stack (var vec)
  PrimAppCC opId vec -> enterPrimAppCC symbolReg envStk stack (opId, vec)

-- enterOrResolveThunkCC will push a update Frame onto the control stack if its
-- evaluating a thunk closure that hasn't been computed yet
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
enterOrResolveThunkCC symbolReg env stack var = 
  case var of
    GlobalVarSym -> 
      let errMsg = "`enterOrResolveThunkCC` expected a local ref, received a global"
          err step = PanicMessageConstructor(stack, 1, InterpreterStepCC step, errMsg)
      in throwEvalError err
    LocalVar nameless -> do
      ref <- localEnvLookup env stack nameless
      (lookups, val) <- hoistedTransitiveLookup ref
      case val of
        BlackHoleCC ->
          let errMsg = "`enterOrResolveThunkCC` attempting to update a black hole"
              err step = PanicMessageConstructor(stack, 1, InterpreterStepCC step, errMsg)
          in throwEvalError err
        ThunkCC _ _ -> do
          -- TODO(joel):
          -- * what values do we continue with?
          -- * we probably need codeRec / codeId?
          (envRefs, codeId, codeRec) <- lookupHeapThunk symbolReg stack var ref

          enterControlStackCC
            symbolReg
            (UpdateHeapRefCC ref stack)
            envRefs
        _ -> 
          let errMsg = "`enterOrResolveThunkCC` got an unexpected value: `" ++ show val ++ "`"
              err step = PanicMessageConstructor(stack, 1, InterpreterStepCC step, errMsg)
          in throwEvalError err

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

-- | Enter a primop.
--
-- Currently limited to math primops and local variables (no globals!).
enterPrimSimple
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> (PrimOpId, V.Vector Variable)
  -> forall c. EvalCC c s (V.Vector Ref)
enterPrimSimple symreg envstack controlstack (op@(TotalMathOpGmp opId), vect)
  | allLocalVars vect
  = do nextVect <- mapM (unsafeLocalEnvLookup envstack controlstack) vect
       enterTotalMathPrimopSimple controlstack (opId, nextVect)
  | otherwise
  = let errMsg = unwords
          [ "A global symbol reference appeared in a primop."
          , "This is not yet supported."
          , "The opcode invoked was"
          , "`" ++ show op ++ "`."
          ]
        err step = PanicMessageConstructor(controlstack, 0, InterpreterStepCC step, errMsg)
    in throwEvalError err
enterPrimSimple _ _ controlstack (opcode, _)
  = let errMsg = "Unsupported opcode referenced: `" ++ show opcode ++ "`."
        err step = PanicMessageConstructor(controlstack, 0, InterpreterStepCC step, errMsg)
    in throwEvalError err

enterTotalMathPrimopSimple
  :: ControlStackCC
  -> (GmpMathOpId, V.Vector Ref)
  -> forall c. EvalCC c s (V.Vector Ref)
enterTotalMathPrimopSimple controlstack (opId, refs) = do
  args <- extendErrorTrans $ mapM heapLookup refs
  checkedOp <- return $ do
    areLiterals <- mapM argAsLiteral (V.toList args)
    hoistTotalMathLiteralOp opId areLiterals
  case checkedOp of
    Left str ->
      let errMsg = "Received a non-literal to a total math primop :\n" ++ str
          err step = PanicMessageConstructor(controlstack, 0, InterpreterStepCC step, errMsg)
      in throwEvalError err
    Right litOp -> do
      _ <- extendErrorTrans $ checkedCounterCost (fromIntegral $ gmpMathCost litOp)
      lits <- return $ evalTotalMathPrimopCode litOp
      allocated <- mapM allocLit $ V.fromList lits
      return allocated

  where argAsLiteral :: ValueRepCC Ref -> Either String Literal
        argAsLiteral (ValueLitCC lit) = Right lit
        argAsLiteral notLit = Left $ "Not a literal: `" ++ show notLit ++ "`"

enterControlStackCC
  :: SymbolRegistryCC
  -> ControlStackCC
  -> V.Vector Ref
  -> forall c. EvalCC c s (V.Vector Ref)
enterControlStackCC _ ControlStackEmptyCC refs = return refs
enterControlStackCC registry stack@(UpdateHeapRefCC ref newStack) refs = do
  val <- extendErrorTrans $ heapLookup ref
  if val == BlackHoleCC
    then do
      extendErrorTrans $ unsafeHeapUpdate ref (IndirectionCC refs)
      enterControlStackCC registry newStack refs
    else
      let errMsg = unwords
            [ "UpdateHeapRefCC expected a black hole instead of"
            , "`" ++ show val ++ "`"
            ]
          err step = PanicMessageConstructor(stack, 0, InterpreterStepCC step, errMsg)
      in throwEvalError err
enterControlStackCC registry (LetBinderCC binders () newEnv body newStack) refs = do
  envStack <- return (EnvConsCC refs newEnv)
  evalCCAnf registry envStack newStack body
