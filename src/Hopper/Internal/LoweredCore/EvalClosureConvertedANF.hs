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


localEnvLookup ::  EnvStackCC -> LocalVariableCC -> (STE (c :+ CCAnfEvalError :+ HeapError ) s  Ref )
localEnvLookup env var@(LocalVarCC theVar) = go env theVar
  where
    go :: EnvStackCC -> Word64 ->  (STE (c :+ CCAnfEvalError :+ HeapError ) s  Ref )
    go EnvEmptyCC _ = throwSTE $ InR $   InL  $ BadLocalVariable var
    go (EnvConsCC theRef _) 0  = return theRef
    go (EnvConsCC _ rest) w = go rest (w - 1)

evalCCAnf :: CodeRegistry -> EnvStackCC -> ControlStackCC -> AnfCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
evalCCAnf codeReg envStack contStack  (ReturnCC localVarLS) =  do resRefs <- lift  $ traverse (localEnvLookup envStack) localVarLS
                                                                  enterControlStackCC codeReg contStack resRefs
evalCCAnf codeReg envStack contStack  (LetNFCC binders rhscc bodcc) =
                        enterRHSCC codeReg envStack
                                  (LetBinderCC binders () envStack bodcc contStack)
                                  rhscc
evalCCAnf codeReg envStack contStack  (TailCallCC appcc ) = applyCC codeReg envStack contStack appcc

enterRHSCC::  CodeRegistry -> EnvStackCC -> ControlStackCC -> RhsCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
enterRHSCC = undefined

applyCC :: CodeRegistry -> EnvStackCC -> ControlStackCC -> AppCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
applyCC = undefined

enterControlStackCC :: CodeRegistry  -> ControlStackCC -> (V.Vector Ref) -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
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
