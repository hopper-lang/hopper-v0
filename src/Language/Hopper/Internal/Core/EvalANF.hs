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
import Language.Hopper.Internal.Core.Literal
import Language.Hopper.Internal.Core.Heap
import Language.Hopper.Internal.Core.ANF
--import Language.Hopper.Internal.Core.Value
import Control.Monad.STExcept
import Data.Hop.Or
import Numeric.Natural
import Data.Text (Text)
import Data.Data
import Language.Hopper.Internal.Core.HeapRef(Ref())
import Prelude.Extras
import qualified Data.Vector as V
--import qualified Data.Map as Map
import GHC.Generics(type Generic)
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

data ErrorEvalAnf = Boom
data ControlStackAnf =
      LetCSANF ![(Either Natural Text, () {- put types info here -})]
                !() -- this is the right hand side of the let thats being evaluated
                !(Anf Ref)
                !ControlStackAnf -- what happens after the body of let returns!
      | CSANFEmpty  -- we're done!
      | Update
            !Ref
            !ControlStackAnf
  deriving (Eq,Ord,Show,Read,Typeable)

newtype WrappedVector a = WrappedVector { unWrappedVector :: V.Vector a }
  deriving (Eq, Show,Ord,Read,Data,Typeable,Functor,Foldable,Traversable)
instance Show1 WrappedVector
instance Eq1 WrappedVector
instance Ord1 WrappedVector
instance Read1 WrappedVector

data Arity = ArityBoxed {_extractArityInfo :: !Text} --- for now our model of arity is boring and simple
                              -- for now lets keep the variable names?
                              -- it'll keep the debugging simpler (maybe?)
 deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)

--- | 'Closure' may need some rethinking ... later
--- they're kinda the erasure of a lambda ... for now
data Closure    a =  BORING  -- MkClosure ![Arity] !(Scope Text ast a)
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable,Generic,Typeable,Data)


-- | 'Tag' is a constructor tag sum
newtype Tag = Tag { unTag :: Text {-Word64-} } deriving (Eq,Read, Show,Ord,Data,Typeable,Generic)
--type HeapVal ast     =  ValueF ast  Ref --  ValueF ty Ref (ValRec ty)

data ValueF    v =    VLitF !Literal
              | ConstructorF  !Tag  !(WrappedVector v)
              | ThunkF !(Anf   v )
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
      ,Generic
      --,Data
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
evalANF ::  Anf Ref -> ControlStackAnf -> HeapStepCounterM hepRep (STE (c :+ ErrorEvalAnf :+ HeapError ) s) Ref
evalANF = undefined



