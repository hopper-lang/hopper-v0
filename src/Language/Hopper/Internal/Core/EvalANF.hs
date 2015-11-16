{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Hopper.Internal.Core.EvalANF
    -- (
    -- )
    where
import Language.Hopper.Internal.Core.ANF
import Language.Hopper.Internal.Core.Value
import qualified Data.Map as Map
import GHC.Generics
import Numeric.Natural
import Data.Typeable
import Control.Monad.Trans.State.Strict as State

import Bound

import Data.Text (Text)

import  Control.Monad.Free
import Control.Lens
import qualified Data.Vector as V

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
                            , Heap (Ref $ (refPointer minmax) + 1) newMap)
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

checkedCounterDecrement :: HeapStepCounterM  ty ()
checkedCounterDecrement = do  cah <- getHSCM
                              ct <- return $  _extractCounterCAH cah
                              if ct <= 0
                                then error "allowed step count exceeded, aborting"
                                else setHSCM cah{_extractCounterCAH = ct - 1}

unsafeHeapUpdate :: Ref -> HeapVal ty -> HeapStepCounterM ty ()
unsafeHeapUpdate rf val = do  cah <- getHSCM
                              x <- return $ heapRefUpdate rf val (_extractHeapCAH cah)
                              checkedCounterDecrement
                              x `seq` setHSCM $ cah{_extractHeapCAH =x }

--- note, this should also decrement the counter!
heapAllocate :: HeapVal ty -> HeapStepCounterM ty  Ref
heapAllocate val = do   cah <-  getHSCM
                        (rf,hp) <- pure $ heapAllocateValue (_extractHeapCAH cah) val
                        cah' <- pure $ cah{_extractHeapCAH = hp}
                        checkedCounterDecrement
                        setHSCM cah'
                        return rf

heapLookup :: Ref -> HeapStepCounterM ty (Maybe (HeapVal ty))
heapLookup rf =  do  checkedCounterDecrement ; (flip heapRefLookup rf . _extractHeapCAH) <$> getHSCM

--heapUpdate :: Ref -> Value ty ->
{-
need to think about possible cycles in references :(
or can i just assume that any refs must be strictly descending?
-}

--- this doesn't validate Heap and heap allocator correctness, VERY UNSAFE :)
unsafeRunHSCM :: Natural -> Heap ty -> HeapStepCounterM ty b -> (b,CounterAndHeap ty)
unsafeRunHSCM cnt hp (HSCM m)  = State.runState m (CounterAndHeap cnt $ hp)

-- run a program in an empty heap
runEmptyHeap :: Natural -> HeapStepCounterM ty b-> (b,CounterAndHeap ty)
runEmptyHeap ct (HSCM m) = State.runState m (CounterAndHeap ct $ Heap (Ref 1) Map.empty)


-- this is the stack in types are calling conventions paper
data StrictContext  ty a  = SCEmpty
                        | LetContext
                            (Scope (Maybe Text) (ANF ty) a)
                            (StrictContext ty a)
                        | ThunkUpdate !a (StrictContext ty a)
   deriving (Typeable
    --,Functor
    --,Foldable
    --,Traversable
    ,Generic
    -- ,Data
    ,Eq
    ,Ord
    ,Show)

heapRefLookupTransitive :: Ref -> HeapStepCounterM ty (HeapVal ty, Ref)
heapRefLookupTransitive ref =
        do  next <- heapLookup ref
            case  next of
              Nothing -> error $ "bad heap ref in looup transitive" ++ show ref
              Just (BlackHoleF) -> error  $ "hit BlackHoleF in transitive lookup" ++ show ref
              (Just (IndirectionF nextRef)) -> heapRefLookupTransitive nextRef
              Just v -> return (v,ref)

evalANF :: StrictContext ty Ref -> ANF ty Ref -> HeapStepCounterM ty (HeapVal ty)
evalANF stk (ReturnNF rf) = returnIntoStack stk rf
evalANF stk (TailCallANF app) = applyANF stk app
evalANF stk (LetNF _mname _mtype rhs scp) = evalRhsANF (LetContext  scp stk) rhs

evalRhsANF :: StrictContext ty Ref -> AnfRHS ty Ref -> HeapStepCounterM ty (HeapVal ty)
evalRhsANF  stk (NonTailCallApp app)  = applyANF stk app
evalRhsANF stk (SharedLiteral lit) = do  freshRef <- heapAllocate (VLitF lit ) ; returnIntoStack stk freshRef
evalRhsANF stk (AllocateThunk expr) = do freshRef <- heapAllocate (ThunkF expr) ; returnIntoStack stk freshRef
evalRhsANF stk (AllocateClosure argLs scp) =
      do  freshRef <- heapAllocate (DirectClosureF $ MkClosure ( map (ArityBoxed . view _1)  argLs) scp)
          returnIntoStack stk freshRef
evalRhsANF stk (ConstrApp _ constrid argsLS) =
        do  freshRef <- heapAllocate (ConstructorF (Tag $  unConstrId  constrid) $ WrappedVector $ V.fromList argsLS)
            returnIntoStack stk freshRef


applyANF :: StrictContext ty Ref -> AppANF ty Ref -> HeapStepCounterM ty (HeapVal ty)
applyANF stk  (EnterThunk thunkRef) =
              do  (thunkOrV,directRef) <- heapRefLookupTransitive thunkRef
                  case thunkOrV of
                    (ThunkF expr) -> do unsafeHeapUpdate directRef BlackHoleF
                                        evalANF (ThunkUpdate directRef stk) expr
                    (IndirectionF wat) ->
                        error "impossible reference, this is a failure of transitive lookup"
                    (BlackHoleF) -> error "impossible BlackHoleF in applyANF"
                    (ConstructorF _ _ ) -> returnIntoStack stk directRef
                    (DirectClosureF _) -> returnIntoStack stk directRef
                    (VLitF _) -> returnIntoStack stk directRef
applyANF stk (FunApp funRef lsArgsRef) =
      do  (closureOrDie,directRef) <- heapRefLookupTransitive funRef
          case closureOrDie of
              (DirectClosureF (MkClosure args scp))
                  | length args == length lsArgsRef ->
                    evalANF stk  $ flip instantiate  scp ((ReturnNF .) $ (Map.!) $ Map.fromList $ zip (map _extractArityInfo args) lsArgsRef)
                  | otherwise -> error $ "arity mismatch for closure in apply position"
              _ -> error "something thats not a closure was invoked in apply position, DIE"
applyANF stk (PrimApp nm args) = applyPrim stk nm args

applyPrim :: StrictContext ty Ref -> Text -> [Ref] ->  HeapStepCounterM ty (HeapVal ty)
applyPrim = error "this isn't defined yet applyPrim "

returnIntoStack :: StrictContext ty Ref -> Ref -> HeapStepCounterM ty  (HeapVal ty)
returnIntoStack SCEmpty ref =  maybe (error "invariant failure, die die die die") id <$>  heapLookup ref
returnIntoStack (ThunkUpdate target stk) ref = do  unsafeHeapUpdate target (IndirectionF ref) ; returnIntoStack stk ref
returnIntoStack (LetContext  scp stk) ref = evalANF stk (instantiate1 (ReturnNF ref) scp)
