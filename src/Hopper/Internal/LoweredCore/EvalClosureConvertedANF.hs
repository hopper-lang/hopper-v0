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

-- | CCAnfEnvStack will eventually blur into whatever register allocation execution model we adopt
data EnvStackCC =
    EnvConsCC !Ref !EnvStackCC
    | EnvEmptyCC
  deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)
data ControlStackCC  =
      LetBinderCC !(V.Vector BinderInfoCC)
                !()
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

evalCCAnf :: CodeRegistry -> EnvStackCC -> ControlStackCC -> AnfCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
evalCCAnf codeReg envStack contStack  (ReturnCC localVarLS) = error "finish this next week"
evalCCAnf codeReg envStack contStack  (LetNFCC binders rhscc bodcc) = enterRHSCC codeReg envStack (LetBinderCC binders () bodcc contStack) rhscc
evalCCAnf codeReg envStack contStack  (TailCallCC appcc ) = applyCC codeReg envStack contStack appcc

enterRHSCC::  CodeRegistry -> EnvStackCC -> ControlStackCC -> RhsCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
enterRHSCC = undefined

applyCC :: CodeRegistry -> EnvStackCC -> ControlStackCC -> AppCC -> HeapStepCounterM (ValueRepCC Ref) (STE (c :+ CCAnfEvalError :+ HeapError ) s) (V.Vector Ref)
applyCC = undefined



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
