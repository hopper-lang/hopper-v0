{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Hopper.Internal.Core.Heap

    where
--import Language.Hopper.Internal.Core.ANF
import Language.Hopper.Internal.Core.Value
import qualified Data.Map as Map
import GHC.Generics
import Numeric.Natural
import Data.Typeable
import Control.Monad.Trans.State.Strict as State

--import Bound

--import Data.Text (Text)

-- import  Control.Monad.Free
--import Control.Lens
--import qualified Data.Vector as V

--- This model implementation of the heap is kinda a hack --- Namely that
--- _minMaxFreshRef acts as a kinda heap pointer that is >= RefInMap + 1
data Heap ast ty =  Heap { _minMaxFreshRef :: !Ref,  _theHeap :: ! (Map.Map Ref (HeapVal ast ty ))   }
   deriving (  Typeable,Show  ,Generic  ,Eq ,Ord   )

heapRefLookup :: Heap ast ty  -> Ref -> Maybe (HeapVal ast ty )
heapRefLookup hp rf = Map.lookup rf (_theHeap hp)


-- this
heapRefUpdate :: Ref -> HeapVal ast ty -> Heap ast ty -> Heap ast ty
heapRefUpdate ref val (Heap ct mp)
        | ref < ct = Heap ct $ Map.insert ref val mp
        | otherwise = error $ "impossible heap ref greater than heap max " ++ show ref

heapAllocateValue :: Heap ast ty  -> HeapVal ast ty  -> (Ref,Heap ast ty )
heapAllocateValue hp val = (_minMaxFreshRef hp
                            , Heap (Ref $ (refPointer minmax) + 1) newMap)
  where
      minmax = _minMaxFreshRef hp
      newMap = Map.insert minmax  val (_theHeap hp)

data CounterAndHeap ast ty =  CounterAndHeap {
                                        _extractCounterCAH :: !Natural
                                        -- this should be a Natural, represents  number of
                                        -- steps left
                                        ,_extractHeapCAH :: !(Heap ast ty) }
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

extractHeapCAH :: Functor f => ((Heap ast ty ) ->  f (Heap ast ty' ))
                  -> CounterAndHeap ast  ty  -> f (CounterAndHeap ast ty' )
extractHeapCAH fun cnh = fmap (\mp' -> cnh{_extractHeapCAH=mp'}) $ fun $ _extractHeapCAH cnh

extractCounterCAH :: Functor f => (Natural -> f Natural )-> (CounterAndHeap ast ty  -> f (CounterAndHeap ast ty ))
extractCounterCAH  fun cnh = fmap (\i' -> cnh{_extractCounterCAH=i'}) $ fun $ _extractCounterCAH cnh

newtype HeapStepCounterM ast ty  a = HSCM {_xtractHSCM :: State.State (CounterAndHeap ast ty) a}
   deriving (Typeable,Functor,Generic)
instance Applicative (HeapStepCounterM ast ty ) where
    pure  = \v ->  HSCM $ pure v
    (<*>) = \ (HSCM f) (HSCM v) -> HSCM $ f <*> v
instance Monad (HeapStepCounterM ast ty ) where
    return = pure
    (>>=)= \ (HSCM mv) f -> HSCM (mv  >>= (_xtractHSCM. f))

getHSCM :: HeapStepCounterM ast ty (CounterAndHeap ast ty)
getHSCM  = HSCM State.get

setHSCM :: CounterAndHeap ast ty  -> HeapStepCounterM  ast ty  ()
setHSCM v = HSCM $ State.put  v

checkedCounterDecrement :: HeapStepCounterM  ast ty ()
checkedCounterDecrement = do  cah <- getHSCM
                              ct <- return $  _extractCounterCAH cah
                              if ct <= 0
                                then error "allowed step count exceeded, aborting"
                                else setHSCM cah{_extractCounterCAH = ct - 1}

unsafeHeapUpdate :: Ref -> HeapVal ast ty -> HeapStepCounterM ast ty ()
unsafeHeapUpdate rf val = do  cah <- getHSCM
                              x <- return $ heapRefUpdate rf val (_extractHeapCAH cah)
                              checkedCounterDecrement
                              x `seq` setHSCM $ cah{_extractHeapCAH =x }

--- note, this should also decrement the counter!
heapAllocate :: HeapVal  ast ty -> HeapStepCounterM  ast ty  Ref
heapAllocate val = do   cah <-  getHSCM
                        (rf,hp) <- pure $ heapAllocateValue (_extractHeapCAH cah) val
                        cah' <- pure $ cah{_extractHeapCAH = hp}
                        checkedCounterDecrement
                        setHSCM cah'
                        return rf

heapLookup :: Ref -> HeapStepCounterM ast  ty (Maybe (HeapVal ast ty))
heapLookup rf =  do  checkedCounterDecrement ; (flip heapRefLookup rf . _extractHeapCAH) <$> getHSCM

--heapUpdate :: Ref -> Value ty ->
{-
need to think about possible cycles in references :(
or can i just assume that any refs must be strictly descending?
-}

--- this doesn't validate Heap and heap allocator correctness, VERY UNSAFE :)
unsafeRunHSCM :: Natural -> Heap ast ty -> HeapStepCounterM ast ty b -> (b,CounterAndHeap ast  ty)
unsafeRunHSCM cnt hp (HSCM m)  = State.runState m (CounterAndHeap cnt $ hp)

-- run a program in an empty heap
runEmptyHeap :: Natural -> HeapStepCounterM ast ty b-> (b,CounterAndHeap ast ty)
runEmptyHeap ct (HSCM m) = State.runState m (CounterAndHeap ct $ Heap (Ref 1) Map.empty)
