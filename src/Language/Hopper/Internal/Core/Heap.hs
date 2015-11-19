{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Hopper.Internal.Core.Heap

    where
--import Language.Hopper.Internal.Core.ANF
import Language.Hopper.Internal.Core.Value
import qualified Data.Map as Map
import GHC.Generics
import Numeric.Natural
import Data.Typeable
import Control.Monad.Trans.State.Strict as State
import Prelude.Extras
--import Bound

--import Data.Text (Text)

-- import  Control.Monad.Free
--import Control.Lens
--import qualified Data.Vector as V

--- This model implementation of the heap is kinda a hack --- Namely that
--- _minMaxFreshRef acts as a kinda heap pointer that is >= RefInMap + 1
data Heap ast  =  Heap { _minMaxFreshRef :: !Ref,  _theHeap :: ! (Map.Map Ref (HeapVal ast  ))   }
   deriving (  Typeable ,Generic    )
deriving instance (Functor ast,Show1 ast, Show (ast Ref)) => Show (Heap ast)
deriving instance (Monad ast,Eq1 ast, Eq (ast Ref)) => Eq (Heap ast)
deriving instance (Monad ast, Ord1 ast, Ord (ast Ref)) => Ord (Heap ast)

heapRefLookup :: Heap ast   -> Ref -> Maybe (HeapVal ast  )
heapRefLookup hp rf = Map.lookup rf (_theHeap hp)


-- this
heapRefUpdate :: Ref -> HeapVal ast  -> Heap ast  -> Heap ast
heapRefUpdate ref val (Heap ct mp)
        | ref < ct = Heap ct $ Map.insert ref val mp
        | otherwise = error $ "impossible heap ref greater than heap max " ++ show ref

heapAllocateValue :: Heap ast   -> HeapVal ast   -> (Ref,Heap ast  )
heapAllocateValue hp val = (_minMaxFreshRef hp
                            , Heap (Ref $ (refPointer minmax) + 1) newMap)
  where
      minmax = _minMaxFreshRef hp
      newMap = Map.insert minmax  val (_theHeap hp)

data CounterAndHeap ast  =  CounterAndHeap {
                                        _extractCounterCAH :: !Natural
                                        -- this should be a Natural, represents  number of
                                        -- steps left
                                        ,_extractHeapCAH :: !(Heap ast ) }
                            deriving (

                                      Typeable

                                      ,Generic

                                      --,Foldable
                                      --,Traversable
                                      --,Functor
                                      )
deriving instance (Show (ast Ref),Functor ast , Show1 ast ) => Show (CounterAndHeap ast)
deriving instance (Eq (ast Ref),Monad ast,Eq1 ast ) => Eq (CounterAndHeap ast)
deriving instance (Ord (ast Ref), Monad ast, Ord1 ast) => Ord (CounterAndHeap ast)

extractHeapCAH :: Functor f => ((Heap ast  ) ->  f (Heap ast  ))
                  -> CounterAndHeap ast    -> f (CounterAndHeap ast  )
extractHeapCAH fun cnh = fmap (\mp' -> cnh{_extractHeapCAH=mp'}) $ fun $ _extractHeapCAH cnh

extractCounterCAH :: Functor f => (Natural -> f Natural )-> (CounterAndHeap ast   -> f (CounterAndHeap ast  ))
extractCounterCAH  fun cnh = fmap (\i' -> cnh{_extractCounterCAH=i'}) $ fun $ _extractCounterCAH cnh

newtype HeapStepCounterM ast   a = HSCM {_xtractHSCM :: State.State (CounterAndHeap ast ) a}
   deriving (Typeable,Functor,Generic)
instance Applicative (HeapStepCounterM ast  ) where
    pure  = \v ->  HSCM $ pure v
    (<*>) = \ (HSCM f) (HSCM v) -> HSCM $ f <*> v
instance Monad (HeapStepCounterM ast  ) where
    return = pure
    (>>=)= \ (HSCM mv) f -> HSCM (mv  >>= (_xtractHSCM. f))

getHSCM :: HeapStepCounterM ast  (CounterAndHeap ast )
getHSCM  = HSCM State.get

setHSCM :: CounterAndHeap ast   -> HeapStepCounterM  ast   ()
setHSCM v = HSCM $ State.put  v

checkedCounterDecrement :: HeapStepCounterM  ast  ()
checkedCounterDecrement = do  cah <- getHSCM
                              ct <- return $  _extractCounterCAH cah
                              if ct <= 0
                                then error "allowed step count exceeded, aborting"
                                else setHSCM cah{_extractCounterCAH = ct - 1}

unsafeHeapUpdate :: Ref -> HeapVal ast  -> HeapStepCounterM ast  ()
unsafeHeapUpdate rf val = do  cah <- getHSCM
                              x <- return $ heapRefUpdate rf val (_extractHeapCAH cah)
                              checkedCounterDecrement
                              x `seq` setHSCM $ cah{_extractHeapCAH =x }

--- note, this should also decrement the counter!
heapAllocate :: HeapVal  ast  -> HeapStepCounterM  ast   Ref
heapAllocate val = do   cah <-  getHSCM
                        (rf,hp) <- pure $ heapAllocateValue (_extractHeapCAH cah) val
                        cah' <- pure $ cah{_extractHeapCAH = hp}
                        checkedCounterDecrement
                        setHSCM cah'
                        return rf

heapLookup :: Ref -> HeapStepCounterM ast   (Maybe (HeapVal ast ))
heapLookup rf =  do  checkedCounterDecrement ; (flip heapRefLookup rf . _extractHeapCAH) <$> getHSCM

--heapUpdate :: Ref -> Value ty ->
{-
need to think about possible cycles in references :(
or can i just assume that any refs must be strictly descending?
-}

--- this doesn't validate Heap and heap allocator correctness, VERY UNSAFE :)
unsafeRunHSCM :: Natural -> Heap ast  -> HeapStepCounterM ast  b -> (b,CounterAndHeap ast  )
unsafeRunHSCM cnt hp (HSCM m)  = State.runState m (CounterAndHeap cnt $ hp)

-- run a program in an empty heap
runEmptyHeap :: Natural -> HeapStepCounterM ast  b-> (b,CounterAndHeap ast )
runEmptyHeap ct (HSCM m) = State.runState m (CounterAndHeap ct $ Heap (Ref 1) Map.empty)

heapRefLookupTransitive :: Ref -> HeapStepCounterM ast  (HeapVal ast , Ref)
heapRefLookupTransitive ref =
        do  next <- heapLookup ref
            case  next of
              Nothing -> error $ "bad heap ref in looup transitive" ++ show ref
              Just (BlackHoleF) -> error  $ "hit BlackHoleF in transitive lookup" ++ show ref
              (Just (IndirectionF nextRef)) -> heapRefLookupTransitive nextRef
              Just v -> return (v,ref)


