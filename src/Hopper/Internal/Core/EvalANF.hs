{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures , RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}

{-# LANGUAGE TypeOperators#-}

module Hopper.Internal.Core.EvalANF

    where
import Hopper.Internal.Core.Literal
import Hopper.Internal.Runtime.Heap
import Hopper.Internal.Core.OldANF
import Hopper.Internal.Core.Closed
--import Hopper.Internal.Core.Value
import Control.Monad.STE
import Data.Hop.Or
import Data.Text (Text)
import Data.Data
import Hopper.Internal.Runtime.HeapRef(Ref())
import Prelude.Extras
import qualified Data.Vector as V
--import qualified Data.Map as Map
import GHC.Generics(type Generic)
--import Numeric.Natural
--import Data.Typeable
--import Control.Monad.Trans.State.Strict as State
--import Bound hiding (Scope)
--import qualified Bound.Scope.Simple as Simple



{-
meta / design note: do we want to do an ST monad style branding of a heap
and its associated heap refs? (maybe.. but only mixing up two evaluations / heaps
actually crops up as an actual implementation bug)

eg

evalANF (forall s . (ANF a, Map a Ref, Heap (v s))) -> ....

probably not, but noting this for now
-}



data ErrorEvalOldAnf = Boom
data ControlStackOldAnf =
      LetCSANF ![(OldAnfVariable, () {- put types info here -})]
                !() -- this is the right hand side of the let thats being evaluated
                !(OldAnf Ref) --- body of let
                !ControlStackOldAnf -- what happens after the body of let returns!
      | CSANFEmpty  -- we're done!
      | Update
            !Ref
            !ControlStackOldAnf
  deriving (Eq,Ord,Show,Read,Typeable)

newtype WrappedVector a = WrappedVector { unWrappedVector :: V.Vector a }
  deriving (Data,Eq, Show,Ord,Read,Typeable,Functor,Foldable,Traversable)
instance Show1 WrappedVector
instance Eq1 WrappedVector
instance Ord1 WrappedVector
instance Read1 WrappedVector

data Arity = ArityBoxed {_extractArityInfo :: !Text} --- for now our model of arity is boring and simple
                              -- for now lets keep the variable names?
                              -- it'll keep the debugging simpler (maybe?)
 deriving (Eq,Ord,Show,Read,Typeable)

--- | 'Closure' may need some rethinking ... later
--- they're kinda the erasure of a lambda ... for now
data Closure    a =  BORING  -- MkClosure ![Arity] !(Scope Text ast a)
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable,Typeable,Data,Generic)


-- | 'Tag' is a constructor tag sum
newtype Tag = Tag { unTag :: Text {-Word64-} } deriving (Data,Generic,Eq,Read, Show,Ord,Typeable)
--type HeapVal ast     =  ValueF ast  Ref --  ValueF ty Ref (ValRec ty)

data ValueF    v =    VLitF !Literal
              | ConstructorF  !Tag  !(WrappedVector v)
              | ThunkF !(OldAnf   v )
              --  should this be a heap ref to
              -- closure to have the right sharing ?
              | DirectClosureF !(Closure   v) -- heap ref?
              | BlackHoleF
              | IndirectionF !v
              --- in the types are calling conventions paper,
              --- indirections can point at pointer sized literals, or heap references (or tuples thereof???)

              -- | VRefF !Ref --- refs are so we can have  exlpicit  sharing
                        --- in a manner thats parametric in the choice
                        -- of execution  semantics
   deriving
     (Typeable
      ,Functor
      ,Foldable
      ,Traversable
      ,Data
      ,Generic
      --
      ,Eq
      ,Ord
      ,Show
      ,Read
      --,Eq1
      --,Ord1
      --,Show1
      --,Read1
      )


{-


type InterpStack s  ty b a = IdentityT (HeapStepCounterM (Exp ty) (STE ((b :+ InterpreterError ) :+ HeapError) s))  a

-- should this be ref or value in the return position? lets revisit later
-- maybe it should be (Ref,HeapVal (Exp ty))  in return position?
evalExp :: (Ord ty,Show ty)=>  ExpContext ty Ref -> Exp ty Ref
 -> InterpStack s  ty b ((HeapVal (Exp ty)), Ref)
-}
evalANF ::  Closed OldAnf  -> ControlStackOldAnf -> HeapStepCounterM hepRep (STE (c :+ ErrorEvalOldAnf :+ HeapError ) s) Ref
evalANF = undefined



