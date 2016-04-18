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
                     makeLenses, firstOf, over, use, at, view)
import Control.Monad.Trans.State.Strict (State, runState, get)
import Data.Foldable (toList)
import Data.Function ((&))
import Data.Maybe (fromMaybe)
import Data.Word (Word32)

import qualified Data.DList as DL
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V

data EnvState
  = EnvState { _esVars  :: DL.DList Variable
             -- ^ Reversed env vars seen so far
             , _esInfos :: DL.DList BinderInfo
             -- ^ Reversed env binder infos seen so far
             , _esSize  :: EnvSize
             -- ^ Size of the env so far, to avoid O(n) 'length' calls
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
-- - "Closure height" refers to the number of lets passed since entering
--   the closure or thunk. TODO(bts): possibly rename this?
-- - Our implicit ABI is currently such that explicit closure args and captured
--   env vars live on two separate levels, with env vars as the inner binding
--   level. TODO(bts): update the evaluator to reflect this new ABI.
-- - In the future we should move to elaborating explicit lets for the env

emptyEnv :: EnvState
emptyEnv = EnvState mempty mempty $ EnvSize 0

topEnv :: Traversal' ConversionState EnvState
topEnv = csEnvStack._head

topEnvUse :: Lens' EnvState a -> ConversionM a
topEnvUse l = projectValue <$> get
  where
    projectValue state = fromMaybe (error "impossible env stack underrun") $
      firstOf (topEnv.l) state

pushEmptyEnv :: ConversionM ()
pushEmptyEnv = csEnvStack %= (emptyEnv:)

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
adjustVar _closureHeight var@(GlobalVarSym _) = return var
adjustVar closureHeight  var@(LocalVar lnv)
  | depth > closureHeight  = capturedVar
  | depth == closureHeight = bumpedVar   -- var refers to fn arg; bump past env
  | otherwise              = return var

  where
    depth = lnv ^. lnDepth
    slot = lnv ^. lnSlot

    capturedVar :: ConversionM Variable
    capturedVar = do
      let envVarDepth = depth - closureHeight - 1
          envVar = LocalVar $ LocalNamelessVar envVarDepth slot

      envSlot <- BinderSlot <$> topEnvUse (esSize.envSize)

      topEnv %= over esSize succ
              . over esInfos (`DL.snoc` dummyBI)
              . over esVars (`DL.snoc` envVar)

      return $ LocalVar $ LocalNamelessVar closureHeight envSlot

    bumpedVar :: ConversionM Variable
    bumpedVar = return $ var & localNameless.lnDepth %~ succ

closureConvert :: Anf -> (AnfCC, SymbolRegistryCC)
closureConvert anf0 = second _csRegistry $ runState (ccAnf 0 anf0) state0
  where
    state0 :: ConversionState
    state0 = ConversionState (SymbolRegistryCC Map.empty Map.empty Map.empty)
                             (ThunkCodeId 0)
                             (ClosureCodeId 0)
                             []

    ccAnf :: Word32 -> Anf -> ConversionM AnfCC
    ccAnf closureHeight (AnfReturn vars) =
      ReturnCC <$> traverse (adjustVar closureHeight) vars

    ccAnf closureHeight (AnfLet infos rhs body) = do
      rhsCC <- ccRhs closureHeight rhs
      bodyCC <- ccAnf (succ closureHeight) body
      return $ LetNFCC infos rhsCC bodyCC

    ccRhs :: Word32 -> Rhs -> ConversionM RhsCC
    ccRhs _closureHeight (RhsAlloc alloc) = AllocRhsCC <$> ccAlloc alloc

    ccAlloc :: Alloc -> ConversionM AllocCC
    ccAlloc (AllocLit lit) = return $ SharedLiteralCC lit

    ccAlloc (AllocLam argInfos body) = do
      pushEmptyEnv
      codeId <- allocClosureCodeId
      bodyCC <- ccAnf 0 body
      envState <- popEnv
      let arity = CodeArity $ fromIntegral $ V.length argInfos
          record = ClosureCodeRecordCC (view esSize envState)
                                       (V.fromList $ toList $ _esInfos envState)
                                       arity
                                       argInfos
                                       bodyCC
      csRegistry.symRegClosureMap.at codeId ?= record

      return $ AllocateClosureCC (V.fromList $ toList $ _esVars envState)
                                 arity
                                 codeId
