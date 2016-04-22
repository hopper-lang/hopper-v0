{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Hopper.Internal.LoweredCore.ClosureConversion
  ( closureConvert
  ) where

import Hopper.Internal.LoweredCore.ANF
import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.Type.BinderInfo (BinderInfo(..))
import Hopper.Internal.Type.Relevance (Relevance(..))
import Hopper.Utils.LocallyNameless (Bound(..), localDepth, BinderSlot(..))

import Control.Arrow (second)
import Control.Lens (Lens', Traversal', (%~), (%=), (?=), _head, at, firstOf,
                     makeLenses, over, set, use)
import Control.Monad.State.Class (MonadState, get)
import Control.Monad.Trans.State.Strict (State, runState)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import Data.Word (Word32)

import qualified Data.DList as DL
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V

--------------------------
-- Data Types
--------------------------

-- | For tracking in 'EnvState' whether we're building a closure or thunk. We
-- need to differentiate to decide whether a variable we encounter reaches
-- outside of the closure or thunk; closures have an extra binding level for
-- explicit arguments to the function.
data ClosureType
  = Thunk
  | Closure
  deriving (Eq, Show)

-- | How far a variable within a closure or thunk "reaches"
data Reach
  = LocalReference
  -- ^ The variable refers to a local 'AnfLet' binding.
  | ArgReference
  -- ^ The variable (inside of a closure, not thunk) refers to a function
  -- argument.
  | FreeReference Word32
  -- ^ The variable reaches beyond the closure/thunk, with the de Bruijn depth
  -- of the binder relative to the closure/thunk boundary.
  deriving (Eq, Show)

-- | The state for environment we're building up for the creation of a closure
-- or thunk code record, and the accompanying 'AnfCC' closure/thunk allocation
-- node which replaces the lambda/delay in the AST.
data EnvState
  = EnvState { _esVars  :: DL.DList Bound
             -- ^ Environment vars allocated so far, for this closure/thunk. We
             -- use a DList so we can get O(1) 'snoc' (as opposed to building up
             -- a list in reverse.)
             , _esInfos :: DL.DList BinderInfo
             -- ^ Environment BinderInfos so far. Similarly we use a DList here
             -- for O(1) 'snoc'.
             , _esSize  :: EnvSize
             -- ^ Size of the environment so far, to avoid O(n) 'length' calls
             , _esSlots :: Map.Map Bound BinderSlot
             -- ^ Env vars mapped to their slot index, for sharing environment
             -- slots when multiple variables in the same closure refer to the
             -- same binder. Once translated to env vars, two different vars
             -- referring to the same binder will be equal.
             , _esClosureType :: ClosureType
             -- ^ Whether we're building a closure or thunk. This is necessary
             -- to calculate whether variables are reaching outside of the
             -- closure (because thunks don't induce new scopes, like closures).
             }
  deriving (Show)

makeLenses ''EnvState

-- | As we walk through the AST, we maintain a stack of 'EnvState's to handle
-- nested closures/thunks.
type EnvStack = [EnvState]

-- | The state in our 'ConversionM' monad. Contains bookkeeping for building our
-- 'SymbolRegistryCC' of closure and thunk code records.
data ConversionState
  = ConversionState { _csRegistry      :: SymbolRegistryCC
                    , _csNextThunkId   :: ThunkCodeId
                    , _csNextClosureId :: ClosureCodeId
                    , _csEnvStack      :: EnvStack
                    }
  deriving (Show)

makeLenses ''ConversionState

-- | The monad in which our closure conversion runs.
newtype ConversionM a
  = ConversionM { runConversion :: State ConversionState a }
  deriving (Functor, Applicative, Monad, MonadState ConversionState)

--------------------------
-- Algorithm
--------------------------

-- Some notes:
--
-- - "letsPassed" refers to the number of lets passed since entering the most
--   immediate closure or thunk.
--
-- - Our implicit ABI is currently such that explicit closure args and captured
--   env vars live on two separate levels, with env vars as the inner binding
--   level. This is temporary until we move to explicit unpacking/elaboration
--   of our environment by introducing new let bindings.
--
-- - We're currently populating our closure/thunk code records with dummy
--   'BinderInfo's.

-- | Traversal focusing on the top 'EnvState' in our 'EnvStack'.
topEnv :: Traversal' ConversionState EnvState
topEnv = csEnvStack._head

-- | Utility analogous to 'use' in lens. This utility should only be used when
-- we're guaranteed to have a non-empty 'EnvStack'.
topEnvUse :: Lens' EnvState a -> ConversionM a
topEnvUse l = projectValue <$> get
  where
    projectValue state = fromMaybe (error "impossible env stack underrun") $
      firstOf (topEnv.l) state

-- | Pushes an empty 'EnvState' onto our 'EnvStack'.
pushEmptyEnv :: ClosureType -> ConversionM ()
pushEmptyEnv closureType = csEnvStack %= (emptyEnv:)
  where
    emptyEnv = EnvState mempty mempty (EnvSize 0) Map.empty closureType

-- | Pops the top 'EnvState' off our our 'EnvStack'.
popEnv :: ConversionM EnvState
popEnv = do
  envState <- topEnvUse id
  csEnvStack %= tail
  return envState

-- | Issues a closure code ID to add the next closure to the registry.
allocClosureCodeId :: ConversionM ClosureCodeId
allocClosureCodeId = do
  curr <- use csNextClosureId
  csNextClosureId %= succ
  return curr

-- | Issues a thunk code ID to add the next thunk to the registry.
allocThunkCodeId :: ConversionM ThunkCodeId
allocThunkCodeId = do
  curr <- use csNextThunkId
  csNextThunkId %= succ
  return curr

-- TODO(bts): populate code records with real 'BinderInfo's
dummyBI :: BinderInfo
dummyBI = BinderInfoData Omega () Nothing

-- | Adjusts a variable as a function of the number of 'Let's we've passed since
-- entering the most immediate closure or thunk. We see whether the variable
-- reaches outside of the current closure/thunk, and adjust the depth of the
-- variable accordingly.
adjustVar :: Word32 -> Bound -> ConversionM Bound
adjustVar _letsPassed var@(Global _) = return var
adjustVar letsPassed  var@(Local depth slot) = do
  mClosureType <- firstOf (topEnv.esClosureType) <$> get

  case mClosureType of
    Nothing ->
      return var
    Just closureType ->
      case reach closureType of
        LocalReference -> return var
        ArgReference -> return $ bump var
        FreeReference depthBeyondClosure -> closeOver depthBeyondClosure

  where
    reach :: ClosureType -> Reach
    reach Thunk
      | depth >= letsPassed = FreeReference $ depth - letsPassed
      | otherwise           = LocalReference
    reach Closure
      | depth >  letsPassed = FreeReference $ depth - (letsPassed + 1)
      | depth == letsPassed = ArgReference
      | otherwise           = LocalReference

    bump :: Bound -> Bound
    bump = localDepth %~ succ

    closeOver :: Word32 -> ConversionM Bound
    closeOver depthBeyondClosure = do
      let envVar = Local depthBeyondClosure slot
      mSharedEnvSlot <- topEnvUse $ esSlots.at envVar

      case mSharedEnvSlot of
        Just sharedEnvSlot ->
          return $ Local letsPassed sharedEnvSlot
        Nothing -> do
          envSlot <- BinderSlot <$> topEnvUse (esSize.envSize)

          topEnv %= over esSize              succ
                  . over esInfos             (`DL.snoc` dummyBI)
                  . set  (esSlots.at envVar) (Just envSlot)
                  . over esVars              (`DL.snoc` envVar)

          return $ Local letsPassed envSlot

-- | Handles conversion of the 'Anf' syntax case. Note that this is not the main
-- function for closure conversion. See 'closureConvert'.
ccAnf :: Word32 -> Anf -> ConversionM AnfCC
ccAnf letsPassed anf = case anf of
  AnfReturn vars ->
    ReturnCC <$> traverse (adjustVar letsPassed) vars

  AnfLet infos rhs body -> do
    rhsCC <- ccRhs letsPassed rhs
    bodyCC <- ccAnf (succ letsPassed) body
    return $ LetNFCC infos rhsCC bodyCC

  AnfTailCall app ->
    TailCallCC <$> ccApp letsPassed app

-- | Handles conversion of the 'Rhs' syntax case.
ccRhs :: Word32 -> Rhs -> ConversionM RhsCC
ccRhs letsPassed (RhsAlloc alloc) = AllocRhsCC <$> ccAlloc letsPassed alloc
ccRhs letsPassed (RhsApp app) = NonTailCallAppCC <$> ccApp letsPassed app

-- | Handles conversion of the 'App' syntax case.
ccApp :: Word32 -> App -> ConversionM AppCC
ccApp letsPassed app = case app of
  AppFun fv avs -> do
    ccFnVar <- adjustVar letsPassed fv
    ccArgVars <- traverse (adjustVar letsPassed) avs
    return $ FunAppCC ccFnVar ccArgVars

  AppPrim primId avs -> do
    ccArgVars <- traverse (adjustVar letsPassed) avs
    return $ PrimAppCC primId ccArgVars

  AppThunk var ->
    EnterThunkCC <$> adjustVar letsPassed var

-- | Handles conversion of the 'Alloc' syntax case.
ccAlloc :: Word32 -> Alloc -> ConversionM AllocCC
ccAlloc letsPassed alloc = case alloc of
  AllocLit lit ->
    return $ SharedLiteralCC lit

  AllocLam argInfos body -> do
    pushEmptyEnv Closure
    closureId <- allocClosureCodeId
    bodyCC <- ccAnf 0 body
    envState <- popEnv
    let arity = CodeArity $ fromIntegral $ V.length argInfos
    csRegistry.symRegClosureMap.at closureId ?=
      ClosureCodeRecordCC (_esSize envState)
                          (V.fromList $ toList $ _esInfos envState)
                          arity
                          argInfos
                          bodyCC
    envVars <- V.fromList <$> traverse (adjustVar letsPassed)
                                       (toList $ _esVars envState)

    return $ AllocateClosureCC envVars arity closureId

  AllocThunk body -> do
    pushEmptyEnv Thunk
    thunkId <- allocThunkCodeId
    bodyCC <- ccAnf 0 body
    envState <- popEnv
    csRegistry.symRegThunkMap.at thunkId ?=
      ThunkCodeRecordCC (_esSize envState)
                        (V.fromList $ toList $ _esInfos envState)
                        bodyCC

    envVars <- V.fromList <$> traverse (adjustVar letsPassed)
                                       (toList $ _esVars envState)

    return $ AllocateThunkCC envVars thunkId

-- | The main function and entrypoint for closure-converting an 'Anf' term.
closureConvert :: Anf -> (AnfCC, SymbolRegistryCC)
closureConvert anf0 = second _csRegistry $
                             runState (runConversion $ ccAnf 0 anf0) state0
  where
    state0 :: ConversionState
    state0 = ConversionState (SymbolRegistryCC Map.empty Map.empty Map.empty)
                             (ThunkCodeId 0)
                             (ClosureCodeId 0)
                             []
