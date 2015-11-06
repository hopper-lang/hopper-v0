
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE CPP #-}


#include "MachDeps.h"
#if WORD_SIZE_IN_BITS != 64
#error "this code base only supports 64-bit haskell because certain mapping data structures are keyed by Int"
#endif

module Language.Hopper.Internal.Core.Eval where


--import Bound
import Numeric.Natural
--import Prelude.Extras
-- import Control.Applicative
--import Control.Monad
--import qualified  Data.Set as Set
import qualified  Data.Map.Strict as Map
--import Data.Foldable (foldl')
--import Data.Traversable
--import Data.Text (Text)
import Data.Data
--import qualified Data.Vector as V
--import Data.Word
--import Data.Int
import GHC.Generics (Generic)
--import Control.Lens
-- import qualified  Data.Bits as Bits
-- import  Control.Monad.Trans.State.Strict (StateT(..))
import qualified Control.Monad.Trans.State.Strict as State

--import  Control.Monad.Free

--import Language.Hopper.Internal.Core.Term
import Language.Hopper.Internal.Core.Value
import Language.Hopper.Internal.Core.ANF
--import Language.Hopper.Internal.Core.Literal

--import Language.Hopper.Internal.Core.STLC --- delet

{- Evaluation Contexts: theses are essentially the explicit control stack of the associated interpreter,
for Lazy Evaluation, we only push onto the control stack when evaluating a thunk,
everything else is definitionally a tail call per se (in terms of the naive lazy evaluation strategy)

for Strict Evaluation, we push onto the control stack when evaluating first the control position,
then when evaluating the argument position

the syntactic definition of a general tail call for strict evaluation corresponds with being the
last expression value in ANF or CPS transformed coded (ie every implicit intermediate value is named)
respresentations

-}

data LazyContext ty = LCEmpty |   LCThunkUpdate !Ref !(LazyContext ty)
                              | LCThunkEval () !(ValRec ty) !(LazyContext ty )
   deriving (Typeable
    --,Functor
    --,Foldable
    --,Traversable
    ,Generic
    -- ,Data
    ,Eq
    ,Ord
    ,Show)

data StrictContext ty  = SCEmpty
                        | SCArgEVal !(ValRec ty) !() !(StrictContext ty )
                        | SCFunEval !() !(ANF ty (ValRec ty)) !(StrictContext ty )
                         -- lets also add strict context thunk heap update here?
   deriving (Typeable
    --,Functor
    --,Foldable
    --,Traversable
    ,Generic
    -- ,Data
    ,Eq
    ,Ord
    ,Show)


--- This model implementation of the heap is kinda a hack --- Namely that
--- _minMaxFreshRef acts as a kinda heap pointer that is >= RefInMap + 1
data Heap ty = Heap {_minMaxFreshRef :: !Ref,_theHeap :: !(Map.Map Ref (HeapVal ty )) }
                            deriving (
                              -- Data
                                      Typeable
                                      ,Show
                                      ,Generic
                                      ,Eq
                                      ,Ord
                                      --,Foldable
                                      --,Traversable
                                      --,Functor
                                      )

heapRefLookup :: Heap ty  -> Ref -> Maybe (HeapVal ty )
heapRefLookup hp rf = Map.lookup rf (_theHeap hp)


-- this
heapRefUpdate :: Ref -> HeapVal ty -> Heap ty -> Heap ty
heapRefUpdate ref val (Heap ct mp)
        | ref < ct = Heap ct $ Map.insert ref val mp
        | otherwise = error $ "impossible heap ref greater than heap max " ++ show ref

heapAllocateValue :: Heap ty  -> HeapVal ty  -> (Ref,Heap ty )
heapAllocateValue hp val = (_minMaxFreshRef hp
                            , Heap (Ref $ refPointer minmax +1) newMap)
  where
      minmax = _minMaxFreshRef hp
      newMap = Map.insert minmax  val (_theHeap hp)

data CounterAndHeap ty =  CounterAndHeap {
                                        _extractCounterCAH :: !Natural
                                        -- this should be a Natural, represents  number of
                                        -- steps left
                                        ,_extractHeapCAH :: !(Heap ty) }
                            deriving (

                                      Typeable
                                      ,Show
                                      ,Generic
                                      ,Eq
                                      ,Ord
                                      --,Foldable
                                      --,Traversable
                                      --,Functor
                                      )

extractHeapCAH :: Functor f => ((Heap ty ) ->  f (Heap ty' ))
                  -> CounterAndHeap ty  -> f (CounterAndHeap ty' )
extractHeapCAH fun cnh = fmap (\mp' -> cnh{_extractHeapCAH=mp'}) $ fun $ _extractHeapCAH cnh

extractCounterCAH :: Functor f => (Natural -> f Natural )-> (CounterAndHeap ty  -> f (CounterAndHeap ty ))
extractCounterCAH  fun cnh = fmap (\i' -> cnh{_extractCounterCAH=i'}) $ fun $ _extractCounterCAH cnh

newtype HeapStepCounterM ty  a = HSCM {_xtractHSCM :: State.State (CounterAndHeap ty) a}
   deriving (Typeable,Functor,Generic)
instance Applicative (HeapStepCounterM ty ) where
    pure  = \v ->  HSCM $ pure v
    (<*>) = \ (HSCM f) (HSCM v) -> HSCM $ f <*> v
instance Monad (HeapStepCounterM ty ) where
    return = pure
    (>>=)= \ (HSCM mv) f -> HSCM (mv  >>= (_xtractHSCM. f))

getHSCM :: HeapStepCounterM ty (CounterAndHeap ty)
getHSCM  = HSCM State.get

setHSCM :: CounterAndHeap ty  -> HeapStepCounterM ty  ()
setHSCM v = HSCM $ State.put  v


unsafeHeapUpdate :: Ref -> HeapVal ty -> HeapStepCounterM ty ()
unsafeHeapUpdate rf val = do  cah <- getHSCM
                              x <- return $ heapRefUpdate rf val (_extractHeapCAH cah)
                              x `seq` setHSCM $ cah{_extractHeapCAH =x }

--- note, this should also decrement the counter!
heapAllocate :: HeapVal ty -> HeapStepCounterM ty  Ref
heapAllocate val = do   cah <-  getHSCM
                        (rf,hp) <- pure $ heapAllocateValue (_extractHeapCAH cah) val
                        cah' <- pure $ cah{_extractHeapCAH = hp}
                        setHSCM cah'
                        return rf

heapLookup :: Ref -> HeapStepCounterM ty (Maybe (HeapVal ty))
heapLookup rf =  (flip heapRefLookup rf . _extractHeapCAH) <$> getHSCM

--heapUpdate :: Ref -> Value ty ->
{-
need to think about possible cycles in references :(
or can i just assume that any refs must be strictly descending?
-}


runHSCM :: Natural -> HeapStepCounterM ty a -> (a,CounterAndHeap ty)
runHSCM cnt (HSCM m) = State.runState m (CounterAndHeap cnt $ Heap (Ref 1) Map.empty)

{-
need to add Partial App and multi arg lambdas to eval/apply later this week :)

-}


---- because we're not doing let normal form yet, we need to thunkify if needed
--argThunkify :: Exp ty (ValRec ty) -> HeapStepCounterM ty  Ref
--argThunkify (V (Pure ref)) = pure ref
--argThunkify (V (Free e)) = heapAllocate e
--argThunkify (Delay e) = heapAllocate $ ThunkF e  -- this shrinks expression slightly, maybe remove later
--argThunkify e = heapAllocate $ ThunkF e

