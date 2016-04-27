{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}

module Hopper.Internal.LoweredCore.EvalClosureConvertedANF where

import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.Runtime.Heap (
   HeapStepCounterM
  ,Heap(..)
  ,unsafeHeapUpdate
  ,heapAllocate
  ,heapAllocateValue
  ,heapLookup
  ,checkedCounterIncrement
  ,checkedCounterCost
  ,throwHeapErrorWithStepInfoSTE
  , getHSCM
  , setHSCM
  , _extractHeapCAH
  )
import Hopper.Internal.Runtime.HeapRef (Ref)
import Hopper.Internal.Type.BinderInfo (BinderInfo)
import Hopper.Utils.LocallyNameless (Bound(..), Depth(..), Slot(..),
                                     GlobalSymbol(..))
import Data.HopperException
import Control.Lens.Prism
import Control.Monad.Reader
import Control.Monad.STE
import Data.Data
import qualified Data.Map as Map
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

type EvalCC s a
  = HeapStepCounterM (ValueRepCC Ref)
                     (STE SomeHopperException s)
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

envStackFromList :: [V.Vector Ref] -> EnvStackCC
envStackFromList (x:xs) = EnvConsCC x (envStackFromList xs)
envStackFromList [] = EnvEmptyCC

data ControlStackCC  =
      LetBinderCC !(V.Vector BinderInfo)
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
                      {eeCCOffendingOpenLocalVariable :: !Bound
                      , eeCCcontrolStackAtError:: !ControlStackCC
                      , eeCCReductionStepAtError :: !InterpreterStepCC}
   |  UnexpectedNotAClosureInFunctionPosition
                      {eeCCOffendingClosureLocalVariable :: !Bound
                      ,eeCCOffendingNotAClosure :: !val
                      ,eeCCcontrolStackAtError :: !ControlStackCC
                      ,eeCCHeapLookupStepOffset :: !Natural --
                      ,eeCCReductionStepAtError:: !InterpreterStepCC }
   | UnexpectedNotThunkInForcePosition
                      {eeCCOffendingClosureLocalVariable :: !Bound
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
                      {eeCCOffendingClosureLocalVariable :: !Bound
                      ,eeCCOffendingNotAClosure :: !val
                      ,eeCCcontrolStackAtError :: !ControlStackCC
                      ,eeCCHeapLookupStepOffset :: !Natural --
                      ,eeCCReductionStepAtError:: !InterpreterStepCC }
   deriving (Eq,Ord,Show,Typeable,Read)

instance (Show val, Typeable val) => HopperException (EvalErrorCC val) where

_EvalErrorCC :: Prism' SomeHopperException (EvalErrorCC (ValueRepCC Ref))
_EvalErrorCC = prism' toHopperException fromHopperException

-- Make sure this only takes one line so it doesn't throw off line numbers
#define PanicMessageConstructor(constack,stepAdjust,reductionStep,msg) (HardFaultImpossiblePanicError (constack) (stepAdjust) (reductionStep) (msg) __FILE__ __LINE__)


{-
NB: the use of the words enter, apply etc shouldn't be taken to mean push/enter vs eval/apply
because this is sort of in between! :)
-}

throwEvalError
  :: (Typeable val, Show val)
  => (Natural -> EvalErrorCC val)
  -> HeapStepCounterM val (STE SomeHopperException s) result
throwEvalError = throwHeapErrorWithStepInfoSTE

panic :: forall s val result. (Natural -> EvalErrorCC (ValueRepCC Ref))
      -> HeapStepCounterM val (STE SomeHopperException s) result
panic = throwHeapErrorWithStepInfoSTE

-- | Are all the 'Bound's in this structure local?
allLocalVars :: Foldable t => t Bound -> Bool
allLocalVars = all (\case { Local _ _ -> True; Global _ -> False })

-- | Allocate a literal.
allocLit :: Literal -> EvalCC s Ref
allocLit x = heapAllocate (ValueLitCC x)

-- | Get a Ref from a Bound variable
envLookup
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> Bound
  -> EvalCC s Ref
envLookup _registry env control (Local depth slot) =
  localEnvLookup env control depth slot
envLookup registry _env _control (Global global) =
  lookupStaticValue registry global

localEnvLookup
  :: EnvStackCC
  -> ControlStackCC
  -> Depth
  -> Slot
  -> EvalCC s Ref
localEnvLookup env control depth0 slot@(Slot slotIdx) = go env depth0
  where
    go :: EnvStackCC -> Depth -> EvalCC s Ref
    go EnvEmptyCC _n = throwEvalError $ \step ->
      BadVariableCC (Local depth0 slot) control (InterpreterStepCC step)
    go (EnvConsCC refs _) (Depth 0)
      | Just val <- refs V.!? fromIntegral slotIdx = return val
      | otherwise = throwEvalError $ \step ->
          BadVariableCC (Local depth0 slot) control (InterpreterStepCC step)
    go (EnvConsCC _ rest) depth = go rest (pred depth)


-- | Evaluate a some term with the given environment and stack
evalCCAnf
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AnfCC
  -> EvalCC s (V.Vector Ref)

-- Returning an unpacked tuple of values, we look them up in the local
-- environment and enter the top of the stack.
evalCCAnf codeReg envStack contStack (ReturnCC localVarLS) = do
  -- resRefs <- traverse (localEnvLookup envStack contStack) $! localVarLS
  resRefs <- traverse (envLookup codeReg envStack contStack) $! localVarLS
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
  -> EvalCC s (V.Vector Ref)
dispatchRHSCC symbolReg envStk ctrlStack rhs = case rhs of
  AllocRhsCC allocExp -> allocateRHSCC symbolReg envStk ctrlStack allocExp
  NonTailCallAppCC appCC -> applyCC symbolReg envStk ctrlStack appCC

-- | Construct a single heap ref for an allocation.
allocateRHSCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AllocCC
  -> EvalCC s (V.Vector Ref)
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
      refVect <- mapM (envLookup symbolReg envStk stack) vars
      ref <- heapAllocate (ConstructorCC constrId refVect)
      enterControlStackCC symbolReg newStack (V.singleton ref)
    AllocateThunkCC vars thunkId -> localGuard vars $ do
      refVect <- mapM (envLookup symbolReg envStk stack) vars
      ref <- heapAllocate (ThunkCC refVect thunkId)
      enterControlStackCC symbolReg newStack (V.singleton ref)
    AllocateClosureCC vars _ closureId -> localGuard vars $ do
      refVect <- mapM (envLookup symbolReg envStk stack) vars
      ref <- heapAllocate (ClosureCC refVect closureId)
      enterControlStackCC symbolReg newStack (V.singleton ref)
allocateRHSCC _symbolReg _envStk stack _alloc = throwEvalError $ \step ->
  let errMsg = "`allocateRHSCC` can only handle let binding"
  in PanicMessageConstructor(stack, 1, InterpreterStepCC step, errMsg)

-- | Evaluate an application.
--
-- We just dispatch to either `enterOrResolveThunkCC`, `enterClosureCC`, or
-- `enterPrimAppCC`.
applyCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> AppCC
  -> EvalCC s (V.Vector Ref)
applyCC symbolReg envStk stack alloc = case alloc of
  EnterThunkCC var -> enterOrResolveThunkCC symbolReg envStk stack var
  FunAppCC var vec -> enterClosureCC symbolReg envStk stack (var, vec)
  PrimAppCC opId vec -> enterPrimAppCC symbolReg envStk stack (opId, vec)

{- | enterClosureCC has to resolve its first heap ref argument to the closure code id
and then it pushes
-}
-- TODO: reduce duplication between lookupHeap{Closure,Thunk}.
--       e.g. logic for whether env is "compatible"
enterClosureCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> (Bound, V.Vector Bound)
  -> EvalCC s (V.Vector Ref)
enterClosureCC _symbolReg _env stack (Global gvsym, _) = do
  errMsg <- return $
    "`enterClosureCC` expected a local ref, received a global: "++ show gvsym
  throwEvalError (\step -> PanicMessageConstructor(stack, 0, InterpreterStepCC step, errMsg))
enterClosureCC symbolReg env stack (Local depth slot, args) = do
  ref <- localEnvLookup env stack depth slot
  (lookups, val) <- transitiveHeapLookup ref
  argRefs <- mapM (envLookup symbolReg env stack) args
  case val of
    ClosureCC closureenv closureid -> do
      ClosureCodeRecordCC _esize _envBindersInfo _asize _argsBindersInfo bod <-
        case lookupClosureCodeId symbolReg closureid of
          Left errMsg -> panic $ \step ->
            PanicMessageConstructor(stack, 1 + lookups, InterpreterStepCC step, errMsg)
          Right closureRecord -> return closureRecord

      evalCCAnf
        symbolReg
        -- This is the implicit closure abi. We don't yet have an explicit pack
        -- / unpack. We need to document / codify this.
        --
        -- TODO(joel/carter): make this explicit.
        (EnvConsCC closureenv (EnvConsCC argRefs env))
        (UpdateHeapRefCC ref stack)
        bod
    badVal ->
      let errMsg = "`enterClosureCC` got an unexpected value: `" ++ show badVal ++ "`"
      in panic $ \step ->
        PanicMessageConstructor(stack, lookups, InterpreterStepCC step, errMsg)

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
  -> Bound
  -> forall s. EvalCC s (V.Vector Ref)
enterOrResolveThunkCC _symbolReg _env stack (Global gvsym) = do
  errMsg <- return $
    "`enterOrResolveThunkCC` expected a local ref, received a global: "++ show gvsym
  throwEvalError (\step -> PanicMessageConstructor(stack, 0, InterpreterStepCC step, errMsg))

enterOrResolveThunkCC symbolReg env stack (Local depth slot) = do
  ref <- localEnvLookup env stack depth slot
  (lookups, val) <- transitiveHeapLookup ref
  case val of
    BlackHoleCC -> do
      errMsg <- return "`enterOrResolveThunkCC` attempting to update a black hole"
      panic (\step -> PanicMessageConstructor(stack, lookups, InterpreterStepCC step, errMsg))
    (ThunkCC thunkEnv thunkid) -> do
      (ThunkCodeRecordCC _esize _envBindersInfo bod) <-
        case lookupThunkCodeId symbolReg thunkid of
            (Left errMsg)  ->
              (panic (\step ->
                 PanicMessageConstructor(stack, 1 + lookups, InterpreterStepCC step, errMsg))
              )
            (Right thunkrecord) -> return thunkrecord

      unsafeHeapUpdate ref BlackHoleCC
      evalCCAnf
        symbolReg
        (EnvConsCC thunkEnv EnvEmptyCC)
        (UpdateHeapRefCC ref stack)
        bod
    badVal -> do
      errMsg <- return $ "`enterOrResolveThunkCC` got an unexpected value: `" ++ show badVal ++ "`"
      panic (\step ->
          PanicMessageConstructor(stack, lookups, InterpreterStepCC step, errMsg))

{-
benchmarking Question: would passing the tuply args as unboxed tuples,
a la (# VariableCC, V.Vector VariableCC #) have decent performance impact?
AND/OR, should we use unboxed/storable vector for fixed size element types like VariableCC

this will require analyzing core, and designing some sort of performance measurement!
-}

{-# SPECIALIZE compatibleEnv :: V.Vector a -> ClosureCodeRecordCC -> Bool #-}
{-# SPECIALIZE compatibleEnv :: V.Vector a -> ThunkCodeRecordCC -> Bool #-}
compatibleEnv :: CodeRecord r => V.Vector a -> r -> Bool
compatibleEnv envRefs rec = refCount == V.length (codeEnvBinderInfos rec)
                         && refCount == fromIntegral (codeEnvSize rec)
  where
    refCount = V.length envRefs

lookupHeapClosure
  :: SymbolRegistryCC
  -> ControlStackCC
  -> Bound
  -> Ref
  -> EvalCC s (V.Vector Ref, ClosureCodeId, ClosureCodeRecordCC)
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
    deref :: Ref -> EvalCC s (V.Vector Ref, ClosureCodeId)
    deref ref = do
      (lookups, val) <- transitiveHeapLookup ref
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
  -> Bound
  -> Ref
  -> EvalCC s (V.Vector Ref, ThunkCodeId, ThunkCodeRecordCC)
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
    deref :: Ref -> EvalCC s (V.Vector Ref, ThunkCodeId)
    deref ref = do
      (lookups, val) <- transitiveHeapLookup ref
      case val of
         ThunkCC envRefs codeId -> return (envRefs, codeId)
         _ -> throwEvalError $ \step ->
           UnexpectedNotThunkInForcePosition var
                                             val
                                             stack
                                             lookups
                                             (InterpreterStepCC step)

lookupHeapLiteral
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> Bound
  -> EvalCC s Literal
lookupHeapLiteral symreg envStack controlStack var = do
  initRef <- envLookup symreg envStack controlStack var
  deref initRef

  where
    deref :: Ref -> EvalCC s Literal
    deref ref = do
      (lookups, val) <- transitiveHeapLookup ref
      case val of
        ValueLitCC l -> return l
        _ -> throwEvalError $ \step ->
          UnexpectedNotLiteral var
                               val
                               controlStack
                               lookups
                               (InterpreterStepCC step)

{- enterPrimAppCC is special in a manner similar to enterOrResolveThunkCC
this is because some primitive operations are ONLY defined on suitably typed Literals,
such as natural number addition. So enterPrimAppCC will have to chase indirections for those operations,
AND validate that it has the right arguments etc.
This may sound like defensive programming, because a sound type system and type preserving
compiler / interpreter transformations DO guarantee that this shall never happen,
but cosmic radiation, a bug in GHC, or a bug in the hopper infrastructure (the most likely :) )  could
result in a mismatch between reality and our expectations, so never hurts to check.
-}

-- | Enter a primop.
--
-- Currently limited to total math primops and local variables (no globals!).
enterPrimAppCC
  :: SymbolRegistryCC
  -> EnvStackCC
  -> ControlStackCC
  -> (PrimOpId, V.Vector Bound)
  -> EvalCC s (V.Vector Ref)
enterPrimAppCC symreg envstack stack (opId, args)
  | allLocalVars args
  = do nextVect <- mapM (envLookup symreg envstack stack) args
       case opId of
         (TotalMathOpGmp mathOpId) ->
           enterTotalMathPrimopSimple stack (mathOpId, nextVect)
         PrimopIdGeneral name ->
           let errMsg = "Unsupported opcode referenced: `" ++ show name ++ "`."
               err step = PanicMessageConstructor(stack, 0, InterpreterStepCC step, errMsg)
           in throwEvalError err
  | otherwise
  = let errMsg = unwords
          [ "A global symbol reference appeared when entering a prim app."
          , "This is not yet supported."
          , "The opcode invoked was"
          , "`" ++ show opId ++ "`."
          ]
        err step = PanicMessageConstructor(stack, 0, InterpreterStepCC step, errMsg)
    in throwEvalError err

enterTotalMathPrimopSimple
  :: ControlStackCC
  -> (GmpMathOpId, V.Vector Ref)
  -> EvalCC s (V.Vector Ref)
enterTotalMathPrimopSimple controlstack (opId, refs) = do
  args <- mapM heapLookup refs
  checkedOp <- return $ do
    areLiterals <- mapM argAsLiteral (V.toList args)
    hoistTotalMathLiteralOp opId areLiterals
  case checkedOp of
    Left str ->
      let errMsg = "Received a non-literal to a total math primop:\n" ++ str
          err step = PanicMessageConstructor(controlstack, 0, InterpreterStepCC step, errMsg)
      in throwEvalError err
    Right litOp -> do
      _ <- checkedCounterCost (fromIntegral $ gmpMathCost litOp)
      lits <- return $ evalTotalMathPrimopCode litOp
      mapM allocLit $ V.fromList lits

  where argAsLiteral :: ValueRepCC Ref -> Either String Literal
        argAsLiteral (ValueLitCC lit) = Right lit
        argAsLiteral notLit = Left $ "Not a literal: `" ++ show notLit ++ "`"

-- | Enter the top of the stack, adding some refs to scope.
enterControlStackCC
  :: SymbolRegistryCC
  -> ControlStackCC
  -> V.Vector Ref
  -> EvalCC s (V.Vector Ref)
enterControlStackCC _ ControlStackEmptyCC refs = return refs
enterControlStackCC registry (UpdateHeapRefCC ref newStack) refs = do
  unsafeHeapUpdate ref (IndirectionCC refs)
  enterControlStackCC registry newStack refs
enterControlStackCC registry (LetBinderCC _binders () newEnv body newStack) refs = do
  envStack <- return (EnvConsCC refs newEnv)
  evalCCAnf registry envStack newStack body


-- Some quick typedefs to make the `lookupStaticValue` reader stuff easier.
type SymbolTable = Map.Map GlobalSymbol (ValueRepCC GlobalSymbol)

type EvalCCT s
  = HeapStepCounterM (ValueRepCC Ref)
                     (STE SomeHopperException s)

type Inflate a = forall s. ReaderT SymbolTable (EvalCCT s) a

-- | Look up a global symbol.
--
-- This slightly belongs with `lookupClosureCodeId` and `lookupThunkCodeId`, but
-- looking up global symbols is more involved. We convert each `ValueRepCC
-- GlobalSymbol` to a `ValueRepCC Ref` as we encounter it and insert it in the
-- heap.
lookupStaticValue :: SymbolRegistryCC
                  -> GlobalSymbol
                  -> EvalCC s Ref
lookupStaticValue (SymbolRegistryCC _thk _closmap vals) symbol =
  runReaderT (inflateStaticValue symbol) vals

inflateStaticValue :: GlobalSymbol -> Inflate Ref
inflateStaticValue symbol = do
  counterAndHeap <- lift getHSCM
  let heap@(Heap _ symbolLookup _) = _extractHeapCAH counterAndHeap

  -- first check whether we've already inflated this value and can return the
  -- cached result
  case Map.lookup symbol symbolLookup of
    Just ref -> return ref
    Nothing -> do
      symbolTable <- ask

      -- we haven't previously inflated this value -- look up its
      -- representation, recursively inflate, put it in the heap cache
      case Map.lookup symbol symbolTable of
        Just symbolRep -> do
          refRep <- inflateStaticValue' symbolRep
          let (ref, heap') = heapAllocateValue heap refRep
          lift $ setHSCM $ counterAndHeap{_extractHeapCAH=heap'}
          return ref
        Nothing -> lift $ panic $ \step ->
          let errMsg = "Failed to find the specified global symbol in the symbol registry: " ++ show symbol
          in PanicMessageConstructor(error "no stack", 1, InterpreterStepCC step, errMsg)

inflateStaticValue' :: ValueRepCC GlobalSymbol -> Inflate (ValueRepCC Ref)
inflateStaticValue' (ValueLitCC lit) = return (ValueLitCC lit)
inflateStaticValue' (ConstructorCC constrId globalChildren) =
  ConstructorCC constrId <$> mapM inflateStaticValue globalChildren
inflateStaticValue' (ThunkCC globalChildren thunkId) =
  ThunkCC <$> mapM inflateStaticValue globalChildren <*> pure thunkId
inflateStaticValue' (ClosureCC globalChildren closureId) =
  ClosureCC <$> mapM inflateStaticValue globalChildren <*> pure closureId
inflateStaticValue' BlackHoleCC = return BlackHoleCC
inflateStaticValue' (IndirectionCC symbols) =
  IndirectionCC <$> mapM inflateStaticValue symbols
