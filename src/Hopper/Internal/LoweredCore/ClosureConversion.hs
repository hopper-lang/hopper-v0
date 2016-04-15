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
import Control.Lens (Lens', Traversal', (^.), (%~), (%=), _head, makeLenses,
                     firstOf, over)
import Control.Monad.Trans.State.Strict (State, runState, get)
import Data.Function ((&))
import Data.Maybe (fromMaybe)
import Data.Word (Word32)

import qualified Data.Map.Strict as Map

data EnvState
  = EnvState { _esVars  :: [Variable]
             -- ^ Reversed env vars seen so far
             , _esInfos :: [BinderInfo]
             -- ^ Reversed env binder infos seen so far
             , _esSize  :: Word32
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

topEnv :: Traversal' ConversionState EnvState
topEnv = csEnvStack._head

topEnvUse :: Lens' EnvState a -> ConversionM a
topEnvUse l = projectValue <$> get
  where
    projectValue state = fromMaybe (error "impossible env stack underrun") $
      firstOf (topEnv.l) state

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
      let envVarDepth = depth - closureHeight + 1
          envVar = LocalVar $ LocalNamelessVar envVarDepth slot

      envSlot <- BinderSlot <$> topEnvUse esSize

      topEnv %= over esSize succ
              . over esInfos (dummyBI:) -- TODO(bts): populate useful BinderInfo
              . over esVars (envVar:)

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
    ccRhs closureHeight (RhsAlloc alloc) =
      AllocRhsCC <$> ccAlloc closureHeight alloc

    ccAlloc :: Word32 -> Alloc -> ConversionM AllocCC
    ccAlloc _closureHeight (AllocLit lit) = return $ SharedLiteralCC lit
