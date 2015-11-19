{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
module Language.Hopper.Internal.Core.EvalTerm where

import Bound

import Language.Hopper.Internal.Core.Term
import Language.Hopper.Internal.Core.Value
import Language.Hopper.Internal.Core.Heap
import Language.Hopper.Internal.Core.Literal
-- import qualified Data.Map as Map
import GHC.Generics
-- import Numeric.Natural
import Data.Text (Text)
import Data.Typeable
import Data.Data


data ExpContext  ty a  = SCEmpty
                        | LetContext
                            (Scope (Maybe Text) (Exp ty) a)
                            (ExpContext ty a)
                        | ThunkUpdate !a (ExpContext ty a)
                        | FunAppCtxt  [Ref] [Exp ty a] (ExpContext  ty a)
                          -- lets just treat the ref list as having the function ref at the
                          -- "bottom of the stack", when [Exp] is empty, reverse ref list to resolve function and apply args
                        | PrimAppCtxt  PrimOpId [Ref] [Exp ty a] (ExpContext  ty a)

                        -- applications are their one hole contexts!
   deriving (Typeable
          ,Functor
          ,Foldable
          ,Traversable
          ,Generic
          ,Data
          ,Eq
          ,Ord
          ,Show)




-- should this be ref or value in the return position? lets revisit later
-- maybe it should be (Ref,HeapVal (Exp ty))  in return position?
evalExp :: (Ord ty,Show ty)=> ExpContext ty Ref -> Exp ty Ref -> HeapStepCounterM (Exp ty) ((HeapVal (Exp ty)), Ref)
evalExp stk (V rf) =  do  rp@(_hpval,_ref) <- heapRefLookupTransitive rf
                          applyStack stk rp -- does this need both heap location and value in general?
evalExp stk (Force e)= undefined


applyStack :: (Ord ty,Show ty)=>
    ExpContext ty Ref -> (HeapVal (Exp ty),Ref) -> HeapStepCounterM (Exp ty) ((HeapVal (Exp ty)), Ref)
applyStack = undefined

{-



evalANF :: StrictContext ty Ref -> ANF ty Ref -> HeapStepCounterM ty (HeapVal ty)
evalANF stk (ReturnNF rf) = returnIntoStack stk rf
evalANF stk (TailCallANF app) = applyANF stk app
evalANF stk (LetNF _mname _mtype rhs scp) = evalRhsANF (LetContext  scp stk) rhs




applyANF :: StrictContext ty Ref -> AppANF ty Ref -> HeapStepCounterM ty (HeapVal ty)
applyANF stk  (EnterThunk thunkRef) =
              do  (thunkOrV,directRef) <- heapRefLookupTransitive thunkRef
                  case thunkOrV of
                    (ThunkF expr) -> do unsafeHeapUpdate directRef BlackHoleF
                                        evalANF (ThunkUpdate directRef stk) expr
                    (IndirectionF _wat) ->
                        error "impossible reference, this is a failure of transitive lookup"
                    (BlackHoleF) -> error "impossible BlackHoleF in applyANF"
                    (ConstructorF _ _ ) -> returnIntoStack stk directRef
                    (DirectClosureF _) -> returnIntoStack stk directRef
                    (VLitF _) -> returnIntoStack stk directRef
applyANF stk (FunApp funRef lsArgsRef) =
      do  (closureOrDie,_directRef) <- heapRefLookupTransitive funRef
          case closureOrDie of
              (DirectClosureF (MkClosure args scp))
                  | length args == length lsArgsRef ->
                    evalANF stk  $ flip instantiate  scp ((ReturnNF .) $ (Map.!) $ Map.fromList $ zip (map _extractArityInfo args) lsArgsRef)
                  | otherwise -> error $ "arity mismatch for closure in apply position"
              _ -> error "something thats not a closure was invoked in apply position, DIE"
applyANF stk (PrimApp _  nm args) = applyPrim stk nm args

applyPrim :: StrictContext ty Ref -> Text -> [Ref] ->  HeapStepCounterM ty (HeapVal ty)
applyPrim = error "for demoware, we need partially applied prim vals on the heap "

returnIntoStack :: StrictContext ty Ref -> Ref -> HeapStepCounterM ty  (HeapVal ty)
returnIntoStack SCEmpty ref =  maybe (error "invariant failure, die die die die") id <$>  heapLookup ref
returnIntoStack (ThunkUpdate target stk) ref = do  unsafeHeapUpdate target (IndirectionF ref) ; returnIntoStack stk ref
returnIntoStack (LetContext  scp stk) ref = evalANF stk (Simple.instantiate1 (ReturnNF ref) scp)

-}
