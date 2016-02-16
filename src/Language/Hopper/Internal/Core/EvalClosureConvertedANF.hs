{-# LANGUAGE TypeOperators #-}
module Language.Hopper.Internal.Core.EvalClosureConvertedANF where

import  Language.Hopper.Internal.Core.ClosureConvertedANF
import  Language.Hopper.Internal.Core.Heap
import  Language.Hopper.Internal.Core.HeapRef
import Data.Hop.Or
import Control.Monad.STE

data CcAnfEnvStack
data CcAnfControlStack
data CcAnfEvalError

evalCcAnf :: CodeRegistry -> CcAnfEnvStack -> CcAnfControlStack -> CcAnf -> HeapStepCounterM CcValueRep (STE (c :+ CcAnfEvalError :+ HeapError ) s) Ref
evalCcAnf = error "finish this next week"

-- evalANF ::  Anf Ref -> ControlStackAnf -> HeapStepCounterM hepRep (STE (c :+ ErrorEvalAnf :+ HeapError ) s) Ref
