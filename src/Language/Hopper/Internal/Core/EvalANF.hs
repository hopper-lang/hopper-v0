{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

{-# LANGUAGE TypeOperators#-}

module Language.Hopper.Internal.Core.EvalANF

    where

import Language.Hopper.Internal.Core.Heap
import Language.Hopper.Internal.Core.ANF
import Language.Hopper.Internal.Core.Value
import Control.Monad.STExcept
import Data.Hop.Or
--import qualified Data.Map as Map
--import GHC.Generics
--import Numeric.Natural
--import Data.Typeable
--import Control.Monad.Trans.State.Strict as State

--import Bound hiding (Scope)
--import qualified Bound.Scope.Simple as Simple
--import Data.Text (Text)

-- import  Control.Monad.Free
--import Control.Lens
--import qualified Data.Vector as V



data ErrorEvalANF = Boom
data ControlStackANF = LetCS


evalANF ::  ANF Ref -> ControlStackANF -> HeapStepCounterM hepRep (STE (c :+ ErrorEvalANF :+ HeapError ) s) Ref
evalANF = undefined
