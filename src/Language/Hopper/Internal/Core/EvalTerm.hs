{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric , TypeOperators#-}
module Language.Hopper.Internal.Core.EvalTerm where

import Bound

import Language.Hopper.Internal.Core.Term
import Language.Hopper.Internal.Core.Value
import Language.Hopper.Internal.Core.Heap
import Language.Hopper.Internal.Core.Literal
import qualified Data.Map as Map
import GHC.Generics
-- import Numeric.Natural
import Data.Text (Text)
import Data.Typeable
import Data.Data
import Control.Lens
import Control.Monad.STExcept
import Control.Monad.Trans
--import Bound.Scope (traverseBound)
import Control.Monad (join, void)
import  Data.Hop.Or
data ExpContext  ty a  = SCEmpty
                        | LetContext
                            (Maybe Text) -- we're not currently using / needing the variable name here
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


data InterpreterError
  = PrimopTypeMismatch
  | NonClosureInApplicationPosition
  | ArityMismatchFailure
  | HeapLookupFailure
  | MalformedClosure
  | MismatchedStackContext
  deriving (Eq,Ord,Show,Typeable,Data)

-- should this be ref or value in the return position? lets revisit later
-- maybe it should be (Ref,HeapVal (Exp ty))  in return position?
evalExp :: (Ord ty,Show ty)=>  ExpContext ty Ref -> Exp ty Ref
  -> HeapStepCounterM (Exp ty) (STE ((b :+ InterpreterError ) :+ HeapError) s)  ((HeapVal (Exp ty)), Ref)
evalExp stk (V rf) =  do  rp@(_hpval,_ref) <- heapRefLookupTransitive rf
                          applyStack stk rp -- does this need both heap location and value in general?
-- should Force reduce both Thunk e AND (Thunk (Thunk^+ e)) to e? for now I claim YES :)
evalExp stk (Force e)=  do  res <- evalExp stk e
                            forcingApply stk res -- forcing apply inits ref to thunk when evaluated to blackholeF
evalExp stk (Delay e) = do ref <- heapAllocate (ThunkF e) ; applyStack stk (ThunkF e,ref)
evalExp stk (funE :@ args) = evalClosureApp (FunAppCtxt [] (funE:args) stk )
evalExp stk (ELit l) =  do ref <- heapAllocate (VLitF l) ; applyStack stk (VLitF l, ref)
evalExp stk (PrimApp name args) = evalPrimApp (PrimAppCtxt name [] args stk )
evalExp stk (Lam ts bod) = do val <- return $ (DirectClosureF (MkClosure (map (ArityBoxed . view _1 )ts  ) bod))
                              ref <- heapAllocate val
                              applyStack stk (val,ref)
evalExp stk (Let mv _mty rhsExp scp) = evalExp (LetContext mv scp stk) rhsExp

noBlackholeArgs :: (Ord ty,Show ty) => [Ref] -> HeapStepCounterM (Exp ty)  (STE ((b :+ InterpreterError ) :+ HeapError) s) ()
noBlackholeArgs rls = void $ traverse heapRefLookupTransitive rls

throwInterpError :: MonadTrans t
                 => InterpreterError
                 -> t (STE ((a1 :+ InterpreterError) :+ b) s) a
throwInterpError e = lift $ throwSTE $ (InL . InR) e

evalClosureApp :: (Show ty, Ord ty)
               => ExpContext ty Ref
               -> HeapStepCounterM (Exp ty) (STE ((b :+ InterpreterError ) :+ HeapError) s) (HeapVal (Exp ty), Ref)
evalClosureApp (FunAppCtxt ls [] stk) = do
  (funRef:argsRef) <- return $ reverse ls
  (val,_ref) <- heapRefLookupTransitive funRef
  noBlackholeArgs argsRef
  case val of
    (DirectClosureF (MkClosure wrpNames scp))
      | length argsRef == length wrpNames
      -> let nmMap = Map.fromList $ zip (map _extractArityInfo wrpNames) argsRef
             sub var = case var of
               (B nm) -> maybe (throwInterpError MalformedClosure)
                               (\ rf -> return $ V rf)
                               (Map.lookup nm nmMap)
               (F term) -> return term
         in do
           nextExp <- traverse sub $ unscope scp
           evalExp stk $ join nextExp
      | otherwise -> throwInterpError ArityMismatchFailure -- error "closure arity vs argument application mismatch"
    _ -> throwInterpError NonClosureInApplicationPosition  -- error "cannot invoke non closure heap values in application position"
evalClosureApp (FunAppCtxt ls (h : t) stk) = evalExp (FunAppCtxt ls t stk) h
evalClosureApp (LetContext _ _ _ ) = throwInterpError MismatchedStackContext --error "letcontext appearing where there should be an closure app context"
evalClosureApp (ThunkUpdate _ _ ) = throwInterpError MismatchedStackContext --  error "thunkupdate context appearing where there should be a closure app context"
evalClosureApp (PrimAppCtxt _ _ _ _) = throwInterpError MismatchedStackContext -- error "prim app context appearing where there should be a closure app context"
evalClosureApp SCEmpty  = throwInterpError MismatchedStackContext -- error "empty stack where application context is expected"

evalPrimApp ::(Show ty, Ord ty) => ExpContext ty Ref -> HeapStepCounterM (Exp ty) (STE ((b :+ InterpreterError ) :+ HeapError) s) ((HeapVal (Exp ty)), Ref)
evalPrimApp (PrimAppCtxt nm args [] stk) = do noBlackholeArgs args ;applyPrim stk nm $ reverse args
evalPrimApp (PrimAppCtxt nm args (h:t) stk) = evalExp (PrimAppCtxt nm  args t stk) h
evalPrimApp (LetContext _ _ _ ) = throwInterpError MismatchedStackContext -- error "letcontext appearing where there should be an prim app context"
evalPrimApp (ThunkUpdate _ _ ) = throwInterpError MismatchedStackContext-- error "thunkupdate context appearing where there should be a prim app context"
evalPrimApp (FunAppCtxt _ _ _) = throwInterpError MismatchedStackContext -- error "fun app context appearing where there should be a prim app context"
evalPrimApp SCEmpty  = throwInterpError MismatchedStackContext --- error "empty stack where prim app context is expected"

forcingApply :: (Ord ty,Show ty)=>
    ExpContext ty Ref -> (HeapVal (Exp ty),Ref) -> HeapStepCounterM (Exp ty) (STE ((b :+ InterpreterError ) :+ HeapError) s) ((HeapVal (Exp ty)), Ref)
forcingApply = undefined

--- question: do we need to guard from blackholes in substitution points??????
applyStack :: (Ord ty,Show ty)=>
    ExpContext ty Ref -> (HeapVal (Exp ty),Ref)
      -> HeapStepCounterM (Exp ty) (STE ((b :+ InterpreterError ) :+ HeapError) s) ((HeapVal (Exp ty)), Ref)
applyStack SCEmpty p= return p
applyStack (LetContext _mv scp stk) (_v,ref)  = evalExp stk (instantiate1 (V ref) scp)
applyStack (FunAppCtxt ls [] stk) (_,ref) = evalClosureApp  (FunAppCtxt (ref : ls) [] stk)
applyStack (FunAppCtxt ls (h:t) stk) (_,ref) = evalExp (FunAppCtxt (ref:ls) t stk) h
applyStack (PrimAppCtxt nm revArgs [] stk) (_,ref) = evalPrimApp (PrimAppCtxt nm (ref:revArgs) [] stk)
applyStack (PrimAppCtxt nm revargs (h:t) stk) (_,ref) = evalExp (PrimAppCtxt nm (ref : revargs) t stk) h
applyStack (ThunkUpdate thunkRef stk) pr@(_val,ref) = do
  -- NOTE: under our current (deterministic, sequential) semantics, thunkRef
  --       *should* (transitively) lead to a blackhole before update.
  unsafeHeapUpdate thunkRef (IndirectionF ref)
  applyStack stk pr




applyPrim :: (Ord ty,Show ty)=> ExpContext ty Ref  -> PrimOpId -> [Ref]
  ->  HeapStepCounterM (Exp ty)  (STE ((b :+ InterpreterError ) :+ HeapError) s) ((HeapVal (Exp ty)), Ref)
applyPrim = error "we haven't defined any primops yet! "

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
