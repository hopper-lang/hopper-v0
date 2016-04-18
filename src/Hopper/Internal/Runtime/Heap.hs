{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE BangPatterns #-}

module Hopper.Internal.Runtime.Heap(
   CounterAndHeap(..)
  ,HeapError(..)
  ,_HeapError
  ,Heap(..)
  ,HeapStepCounterM  -- keeping HeapStepCounterM abstract for now, as long as theres NO TH hijinks
  ,unsafeHeapUpdate
  ,unsafeRunHSCM
  ,runHeap
  ,runEmptyHeap
  ,heapAllocate
  ,heapAllocateValue
  ,heapLookup
  ,checkedCounterIncrement
  ,checkedCounterCost
  ,throwHeapErrorWithStepInfoSTE
  ,TransitiveLookup(..)

  , getHSCM
  , setHSCM
  )

    where

import qualified Data.Map as Map
import GHC.Generics
import Numeric.Natural
import Data.Typeable
import Control.Lens.Prism
import Control.Monad.Trans.State.Strict as State
-- import Prelude.Extras
import Control.Monad.Trans.Class as MT
import Control.Monad.Primitive as  Prim
import Control.Monad.IO.Class as MIO
import Control.Monad.STE
import Data.Data
import Data.HopperException
import Hopper.Internal.Runtime.HeapRef
import Hopper.Utils.LocallyNameless (GlobalSymbol)



class TransitiveLookup valRep  where
  transitiveHeapLookup :: Ref -> HeapStepCounterM valRep (STE SomeHopperException s) (Natural, valRep)


throwHeapErrorWithStepInfoSTE :: forall s err val result. HopperException err
                              => (Natural -> err)
                              -> HeapStepCounterM val (STE SomeHopperException s) result
throwHeapErrorWithStepInfoSTE f = do
  cah <- getHSCM
  ct <- return $ _extractReductionStepCounterCAH cah
  lift $ throwSTE $! toHopperException $! f ct

data Heap val = Heap
  { _minMaxFreshRef :: !Ref
  , _symbolLookup :: !(Map.Map GlobalSymbol Ref)
  , _theHeap :: ! (Map.Map Ref val)
  } deriving (Typeable, Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Data)

-- | HeapError is currently flawed because we dont provide a stack trace
data HeapError
  = HeapStepCostCounterExceeded
  | InvalidHeapLookup
  | HeapLookupOutOfBounds
  deriving (Eq,Ord,Show,Read,Typeable)

instance HopperException HeapError where

_HeapError :: Prism' SomeHopperException HeapError
_HeapError = prism' toHopperException fromHopperException

heapRefUpdate :: forall s val. Ref -> val -> Heap val -> HeapStepCounterM val (STE SomeHopperException s) (Heap val)
heapRefUpdate ref val (Heap ct symTable mp)
        | ref < ct  && ref `Map.member` mp = return $ Heap ct symTable $ Map.insert ref val mp
        | ref >= ct = throwHeapErrorWithStepInfoSTE (\_ -> HeapLookupOutOfBounds) -- error $ "impossible heap ref greater than heap max, deep invariant failure" ++ show ref
        | otherwise {- invalid heap ref -} = throwHeapErrorWithStepInfoSTE (\_ -> InvalidHeapLookup)

heapAllocateValue :: Heap val   -> val   -> (Ref,Heap val)
heapAllocateValue (Heap minmax symTable theHeap) val = (minmax
                            , Heap (Ref $ refPointer minmax + 1) symTable newMap)
  where
      newMap = Map.insert minmax val theHeap

data CounterAndHeap val = CounterAndHeap
  { _extractReductionStepCounterCAH :: !Natural
  , _extractCostCounterCAH :: !Natural
  -- this should be a Natural, represents  number of steps l
  , _extractMaxCostCounter :: !Natural
  , _extractHeapCAH :: !(Heap val)
  } deriving (
    Typeable
    ,Eq,Ord,Show
    ,Foldable
    ,Traversable
    ,Functor
  )


newtype HeapStepCounterM val  m a = HSCM {_xtractHSCM :: State.StateT  (CounterAndHeap val ) m a}
   deriving (Typeable,Functor)

instance MonadIO m => MonadIO (HeapStepCounterM val m) where
  liftIO m = lift $ MIO.liftIO m

instance PrimMonad m => PrimMonad (HeapStepCounterM val m) where
  type PrimState (HeapStepCounterM val m) = Prim.PrimState m
  primitive stfun = lift $ Prim.primitive stfun
instance MT.MonadTrans (HeapStepCounterM val) where
    lift m =  HSCM $
                StateT $ \ s -> do
                                  a <- m
                                  return (a, s)
instance Monad  n=>Applicative (HeapStepCounterM val  n) where
    pure  = \v ->  HSCM $ pure v
    (<*>) = \ (HSCM f) (HSCM v) -> HSCM $ f <*> v
instance Monad m => Monad (HeapStepCounterM val m) where
    return = pure
    (>>=)= \ (HSCM mv) f -> HSCM (mv  >>= (_xtractHSCM. f))

getHSCM :: Monad m => HeapStepCounterM val  m (CounterAndHeap val )
getHSCM  = HSCM State.get

setHSCM :: Monad m =>  CounterAndHeap val   -> HeapStepCounterM  val  m  ()
setHSCM v = HSCM $ State.put  v


{- this is how we track number of reduction steps deterministically
may be a useful way of "addressing" a point in a programs execution
within a debugging tool at some future point -}
checkedCounterIncrement ::   HeapStepCounterM  val  (STE SomeHopperException s) ()
checkedCounterIncrement =  checkedCounterCost 0


-- | checkedCounterJump increments reduction step by one  plus the natural number argument
checkedCounterCost ::  Natural ->  HeapStepCounterM  val  (STE SomeHopperException s) ()
checkedCounterCost  jumpSize =
                          do  cah <- getHSCM
                              redct <- return $  _extractReductionStepCounterCAH cah
                              costct <- return $ _extractCostCounterCAH cah
                              if costct >= _extractMaxCostCounter cah -- lets try this

                               then
                                {-# SCC "heapABORT" #-}
                                do
                                 throwHeapErrorWithStepInfoSTE (\_ -> HeapStepCostCounterExceeded)-- error "allowed step count exceeded, aborting"
                               else setHSCM cah{
                                        _extractReductionStepCounterCAH = redct + 1
                                        ,_extractCostCounterCAH = costct +  1 +jumpSize}


unsafeHeapUpdate :: Ref -> val  -> HeapStepCounterM val (STE SomeHopperException s) ()
unsafeHeapUpdate rf val = do  cah <- getHSCM
                              x <-  heapRefUpdate rf val (_extractHeapCAH cah)
                              checkedCounterIncrement
                              x `seq` setHSCM $ cah{_extractHeapCAH =x }


heapAllocate :: val  -> HeapStepCounterM  val  (STE SomeHopperException s) Ref
heapAllocate val = do   cah <-  getHSCM
                        (rf,hp) <- pure $ heapAllocateValue (_extractHeapCAH cah) val
                        cah' <- pure $ cah{_extractHeapCAH = hp}
                        checkedCounterIncrement
                        setHSCM cah'
                        return rf

heapLookup :: Ref -> HeapStepCounterM val (STE SomeHopperException s) val
heapLookup ref = do
  checkedCounterIncrement
  heapHandle <- _extractHeapCAH <$> getHSCM
  !x <- heapRefLookup ref heapHandle
  return x
   where
     heapRefLookup :: Ref -> Heap val -> HeapStepCounterM val (STE SomeHopperException s) val
     heapRefLookup rf (Heap ct _symTable mp)
       | ref < ct && rf `Map.member` mp = return $ mp Map.! rf
       | ref >= ct = throwHeapErrorWithStepInfoSTE (\ _ -> HeapLookupOutOfBounds)
       | otherwise {- invalid heap ref -} = throwHeapErrorWithStepInfoSTE(\ _ -> InvalidHeapLookup)


--- this doesn't validate Heap and heap allocator correctness, VERY UNSAFE :)
unsafeRunHSCM :: Natural -> Heap val  -> HeapStepCounterM val m b -> m (b,CounterAndHeap val  )
unsafeRunHSCM cnt hp (HSCM m)  = State.runStateT m (CounterAndHeap 0 0 cnt hp)

-- run a program in an empty heap
runEmptyHeap :: Natural
  -> HeapStepCounterM val m b
  -> m (b, CounterAndHeap val)
runEmptyHeap = runHeap (Heap (Ref 1) Map.empty Map.empty)

runHeap :: Heap val
  -> Natural
  -> HeapStepCounterM val m b
  -> m (b, CounterAndHeap val)
runHeap heap cost (HSCM m)  =
      let counterAndHeap = CounterAndHeap 0 0 cost heap
          in State.runStateT m counterAndHeap
  -- | otherwise = error "runheap needs a nonzero total execution budget"


