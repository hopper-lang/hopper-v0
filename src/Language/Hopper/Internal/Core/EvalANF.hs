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
import Numeric.Natural
import Data.Text (Text)
import Data.Data
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


{-
meta / design note: do we want to do an ST monad style branding of a heap
and its associated heap refs? (maybe.. but only mixing up two evaluations / heaps
actually crops up as an actual implementation bug)

eg

evalANF (forall s . (ANF a, Map a Ref, Heap (v s))) -> ....

probably not, but noting this for now
-}

data ErrorEvalANF = Boom
data ControlStackANF =
      LetCSANF ![(Either Natural Text, () {- put types info here -})]
                !() -- this is the right hand side of the let thats being evaluated
                !(ANF Ref)
                !ControlStackANF -- what happens after the body of let returns!
      | CSANFEmpty  -- we're done!
      | Update
            !Ref
            !ControlStackANF
  deriving (Eq,Ord,Show,Read,Typeable)




evalANF ::  ANF Ref -> ControlStackANF -> HeapStepCounterM hepRep (STE (c :+ ErrorEvalANF :+ HeapError ) s) Ref
evalANF = undefined
