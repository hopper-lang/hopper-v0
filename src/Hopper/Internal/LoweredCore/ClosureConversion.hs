{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Hopper.Internal.LoweredCore.ClosureConversion
  ( closureConvert
  ) where

import Hopper.Internal.LoweredCore.ANF
import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.Type.BinderInfo (BinderInfo(..))
import Hopper.Internal.Type.Relevance (Relevance(..))
import Hopper.Utils.LocallyNameless

import Control.Arrow (second)
import Control.Lens (Lens', Traversal', (^.), (%~), (%=), (?=), _head,
                     makeLenses, firstOf, over, use, at)
import Control.Monad.Trans.State.Strict (State, runState, get)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import Data.Word (Word32)

import qualified Data.DList as DL
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V

data ClosureType
  = Thunk
  | Closure
  deriving (Eq, Show)

data Reach
  = LocalReference
  | ArgReference
  | FreeReference Word32 -- de Bruijn depth beyond the closure/thunk
  deriving (Eq, Show)

data EnvState
  = EnvState { _esVars  :: DL.DList Variable
             -- ^ Environment vars seen so far
             , _esInfos :: DL.DList BinderInfo
             -- ^ Environment BinderInfos seen so far
             , _esSize  :: EnvSize
             -- ^ Size of the environment so far, to avoid O(n) 'length' calls
             , _esClosureType :: ClosureType
             -- ^ Whether we're building a closure or thunk. This is necessary
             -- to calculate whether variables are reaching outside of the
             -- closure (because thunks don't induce new scopes, like closures).
             }
  deriving (Show)

makeLenses ''EnvState

type EnvStack = [EnvState]

data ConversionState
  = ConversionState { _csRegistry      :: SymbolRegistryCC
                    , _csNextThunkId   :: ThunkCodeId
                    , _csNextClosureId :: ClosureCodeId
                    , _csEnvStack      :: EnvStack
                    }
  deriving (Show)

makeLenses ''ConversionState

type ConversionM = State ConversionState

-- Some notes:
--
-- - "letsPassed" refers to the number of lets passed since entering the closure
--   or thunk.
--
-- - Our implicit ABI is currently such that explicit closure args and captured
--   env vars live on two separate levels, with env vars as the inner binding
--   level. TODO(bts): update the evaluator to reflect this new ABI.
--
-- - In the future we should move to elaborating explicit lets for the env

topEnv :: Traversal' ConversionState EnvState
topEnv = csEnvStack._head

topEnvUse :: Lens' EnvState a -> ConversionM a
topEnvUse l = projectValue <$> get
  where
    projectValue state = fromMaybe (error "impossible env stack underrun") $
      firstOf (topEnv.l) state

pushEmptyEnv :: ClosureType -> ConversionM ()
pushEmptyEnv closureType = csEnvStack %= (emptyEnv:)
  where
    emptyEnv = EnvState mempty mempty (EnvSize 0) closureType

popEnv :: ConversionM EnvState
popEnv = do
  envState <- topEnvUse id
  csEnvStack %= tail
  return envState

allocClosureCodeId :: ConversionM ClosureCodeId
allocClosureCodeId = do
  curr <- use csNextClosureId
  csNextClosureId %= succ
  return curr

allocThunkCodeId :: ConversionM ThunkCodeId
allocThunkCodeId = do
  curr <- use csNextThunkId
  csNextThunkId %= succ
  return curr

-- TODO(bts): integrate real binder infos
dummyBI :: BinderInfo
dummyBI = BinderInfoData Omega () Nothing

adjustVar :: Word32 -> Variable -> ConversionM Variable
adjustVar _letsPassed var@(GlobalVarSym _) = return var
adjustVar letsPassed  var@(LocalVar lnv) = do
  mClosureType <- firstOf (topEnv.esClosureType) <$> get

  case mClosureType of
    Nothing ->
      return var -- TODO(bts): possibly error that this var is free
    Just closureType ->
      case reach closureType of
        LocalReference -> return var
        ArgReference -> return $ bump var
        FreeReference depthBeyondClosure -> closeOver depthBeyondClosure

  where
    depth = lnv ^. lnDepth
    slot = lnv ^. lnSlot

    reach :: ClosureType -> Reach
    reach Thunk
      | depth >= letsPassed = FreeReference $ depth - letsPassed
      | otherwise           = LocalReference
    reach Closure
      | depth >  letsPassed = FreeReference $ depth - (letsPassed + 1)
      | depth == letsPassed = ArgReference
      | otherwise           = LocalReference

    bump :: Variable -> Variable
    bump = localNameless.lnDepth %~ succ

    closeOver :: Word32 -> ConversionM Variable
    closeOver depthBeyondClosure = do
      let envVar = LocalVar $ LocalNamelessVar depthBeyondClosure slot

      envSlot <- BinderSlot <$> topEnvUse (esSize.envSize)

      topEnv %= over esSize succ
              . over esInfos (`DL.snoc` dummyBI)
              . over esVars (`DL.snoc` envVar)

      return $ LocalVar $ LocalNamelessVar letsPassed envSlot

closureConvert :: Anf -> (AnfCC, SymbolRegistryCC)
closureConvert anf0 = second _csRegistry $ runState (ccAnf 0 anf0) state0
  where
    state0 :: ConversionState
    state0 = ConversionState (SymbolRegistryCC Map.empty Map.empty Map.empty)
                             (ThunkCodeId 0)
                             (ClosureCodeId 0)
                             []

    ccAnf :: Word32 -> Anf -> ConversionM AnfCC
    ccAnf letsPassed (AnfReturn vars) =
      ReturnCC <$> traverse (adjustVar letsPassed) vars

    ccAnf letsPassed (AnfLet infos rhs body) = do
      rhsCC <- ccRhs letsPassed rhs
      bodyCC <- ccAnf (succ letsPassed) body
      return $ LetNFCC infos rhsCC bodyCC

    ccAnf letsPassed (AnfTailCall app) = TailCallCC <$> ccApp letsPassed app

    ccRhs :: Word32 -> Rhs -> ConversionM RhsCC
    ccRhs _letsPassed (RhsAlloc alloc) = AllocRhsCC <$> ccAlloc alloc

    ccRhs letsPassed (RhsApp app) = NonTailCallAppCC <$> ccApp letsPassed app

    ccApp :: Word32 -> App -> ConversionM AppCC
    ccApp letsPassed (AppFun fv avs) = do
      ccFnVar <- adjustVar letsPassed fv
      ccArgVars <- traverse (adjustVar letsPassed) avs
      return $ FunAppCC ccFnVar ccArgVars

    ccApp letsPassed (AppPrim primId avs) = do
      ccArgVars <- traverse (adjustVar letsPassed) avs
      return $ PrimAppCC primId ccArgVars

    ccApp letsPassed (AppThunk var) = EnterThunkCC <$> adjustVar letsPassed var

    ccAlloc :: Alloc -> ConversionM AllocCC
    ccAlloc (AllocLit lit) = return $ SharedLiteralCC lit

    ccAlloc (AllocLam argInfos body) = do
      pushEmptyEnv Closure
      closureId <- allocClosureCodeId
      bodyCC <- ccAnf 0 body
      envState <- popEnv
      let arity = CodeArity $ fromIntegral $ V.length argInfos
          record = ClosureCodeRecordCC (_esSize envState)
                                       (V.fromList $ toList $ _esInfos envState)
                                       arity
                                       argInfos
                                       bodyCC
      csRegistry.symRegClosureMap.at closureId ?= record

      return $ AllocateClosureCC (V.fromList $ toList $ _esVars envState)
                                 arity
                                 closureId

    ccAlloc (AllocThunk body) = do
      pushEmptyEnv Thunk
      thunkId <- allocThunkCodeId
      bodyCC <- ccAnf 0 body
      envState <- popEnv
      let record = ThunkCodeRecordCC (_esSize envState)
                                     (V.fromList $ toList $ _esInfos envState)
                                     bodyCC
      csRegistry.symRegThunkMap.at thunkId ?= record

      return $ AllocateThunkCC (V.fromList $ toList $ _esVars envState)
                               thunkId
