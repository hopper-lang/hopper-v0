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
module Language.Hopper.Internal.Core.EvalClosureConvertedANF where

import Language.Hopper.Internal.Core.ClosureConvertedANF
import Language.Hopper.Internal.Core.Heap
import Language.Hopper.Internal.Core.HeapRef
import Data.Hop.Or
import Control.Monad.STE
import Data.Data
import GHC.Generics
import qualified Data.Vector as V

-- | CcAnfEnvStack will eventually blur into whatever register allocation execution model we adopt
data EnvStackCcAnf = EnvConsCcA !Ref !EnvStackCcAnf | EnvEmptyCcA
    deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)
data ControlStackCcA  =
      LetCSANF !(V.Vector AnfBinderInfoCc)
                !()
                !(AnfCc) --- body of let
                !ControlStackCcA -- what happens after the body of let returns!
      | ControlStackEmptyCcA  -- we're done!
      | Update
            !Ref
            !ControlStackCcA
  deriving (Eq,Ord,Show,Read,Typeable)

data CcAnfEvalError

evalCcAnf :: CodeRegistry -> EnvStackCcAnf -> ControlStackCcA -> AnfCc -> HeapStepCounterM CcValueRep (STE (c :+ CcAnfEvalError :+ HeapError ) s) Ref
evalCcAnf = error "finish this next week"

-- evalANF ::  Anf Ref -> ControlStackAnf -> HeapStepCounterM hepRep (STE (c :+ ErrorEvalAnf :+ HeapError ) s) Ref
