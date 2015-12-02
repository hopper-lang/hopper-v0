{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Hopper.Internal.Core.DemoEvalTerm where

-- import qualified  Language.Hopper.Internal.Core.TermDemoWare as TDW
import Language.Hopper.Internal.Core.Heap
import  Control.Monad.RWS.Class
import Control.Monad.RWS.Strict

-- import Control.Monad.Trans (lift)
import Data.Typeable
import Data.Data
import GHC.Generics
import qualified Data.Map.Strict as Map
import Numeric.Natural
import Data.Text (Text,pack,unpack )
import Bound
import Language.Hopper.Internal.Core.Value
import Language.Hopper.Internal.Core.Literal
import Language.Hopper.Internal.Core.Term
import Control.Lens (view,_1)
import Text.Read (readMaybe)
import Control.Monad.Trans.Except (ExceptT(..),runExceptT)
import Control.Monad.Error.Class (throwError)

import Control.Monad.STExcept

{-
reader holds the "snapshot" of the state of all accounts/balances before this program is run and thence committed
state holds BOTH an overlay map on top of the snapshot of any accounts whose balances have been adjusted
  so far
  AND a Natural number counter of # of (implicilty successful) commands written to proposed diff so far
writer holds the "log" of commands written so far, paired with an index that for now will be the #
  of commands previously written to the log in that execution (ie it defines the valid ordering for commiting those commands)

NOTE: does writer class allow disrupting the log??
-}

--  programs will just be [Cmd]
-- and we desugar those to nested lets whose names we ignore, and then we run it
{-
[transfer1 ... ]

let _ = transfer1
  in
    let _ = ...
        ...

-}

data DemoError = DERRRR
  deriving (Eq,Ord,Typeable,Show)

data Cmd = Cmd {from :: Text , to :: Text , posAmount :: Rational , fakeCryptoSig:: Text }
  deriving (Eq,Ord,Show,Read,Data,Typeable)
readCmdMaybe :: String -> Maybe Cmd
readCmdMaybe str =  (\ (fr,t,pos,fk) -> Cmd fr t pos fk)  <$> readMaybe str

readCmdListMaybe  :: String -> Maybe [Cmd]
readCmdListMaybe str = fmap (fmap (\ (fr,t,pos,fk) -> Cmd fr t pos fk) ) $ readMaybe str

type DemoWithLayers s  ast  a=  ExceptT  String
                            (RWST (Map.Map Text Rational)  [(Natural,Cmd)]  (Natural,(Map.Map Text Rational))
                              (HeapStepCounterM ast  (STE DemoError s) {- STE HopperDemoError  s -})) 
                              a

{-
newtype DemoWithLayers s ast a =   DWL  (RWST mp1 ops tupmp2 (HeapStepCounterM ast (STE demoerror s))   a)

-}


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


demoLift :: HeapStepCounterM   ast (STE DemoError s) a -> DemoWithLayers s  ast a
demoLift  = \m ->  lift $ lift m

-- should this be ref or value in the return position? lets revisit later
-- maybe it should be (Ref,HeapVal (Exp ty))  in return position?
evalExp :: (Ord ty,Show ty)=>  ExpContext ty Ref -> Exp ty Ref -> DemoWithLayers  s (Exp ty)  ((HeapVal (Exp ty)), Ref)
evalExp stk (V rf) =  do  rp@(_hpval,_ref) <-   demoLift $ heapRefLookupTransitive rf
                          applyStack stk rp -- does this need both heap location and value in general?
-- should Force reduce both Thunk e AND (Thunk (Thunk^+ e)) to e? for now I claim YES :)
evalExp stk (Force e)=  do  res <- evalExp stk e
                            forcingApply stk res -- forcing apply inits ref to thunk when evaluated to blackholeF
evalExp stk (Delay e) = do ref <- demoLift  $ heapAllocate (ThunkF e) ; applyStack stk (ThunkF e,ref)
evalExp stk (funE :@ args) = evalClosureApp (FunAppCtxt [] (funE:args) stk )
evalExp stk (ELit l) =  do ref <- demoLift $ heapAllocate (VLitF l) ; applyStack stk (VLitF l, ref)
evalExp stk (PrimApp name args) = evalPrimApp (PrimAppCtxt name [] args stk )
evalExp stk (Lam ts bod) = do val <- return $ (DirectClosureF (MkClosure (map (ArityBoxed . view _1 )ts  ) bod))
                              ref <- demoLift $ heapAllocate val
                              applyStack stk (val,ref)
evalExp stk (Let mv _mty rhsExp scp) = evalExp (LetContext mv scp stk) rhsExp

noBlackHoleRefs :: (Ord ty,Show ty) => [Ref] -> DemoWithLayers  s(Exp ty) ()
noBlackHoleRefs rls = do  vls <- demoLift $  mapM (fmap (view _1) . heapRefLookupTransitive) rls ;
                          if all (/= BlackHoleF) vls
                            then return ()
                            else error "heap reference to BlackHoleF in argument position in closure or prim application"




evalClosureApp :: (Show ty, Ord ty) => ExpContext ty Ref -> DemoWithLayers s (Exp ty) ((HeapVal (Exp ty)), Ref)
evalClosureApp (FunAppCtxt ls [] stk) =
    do  (funRef:argsRef) <- return $ reverse ls
        (val,_ref) <- demoLift $  heapRefLookupTransitive funRef
        noBlackHoleRefs argsRef
        case val of
          (DirectClosureF (MkClosure wrpNames scp))
                | length argsRef == length wrpNames ->
                      let nmMap = Map.fromList $ zip (map _extractArityInfo wrpNames) argsRef
                            in evalExp stk
                              (instantiate (\k -> V $ flip maybe id  (error "closure environment lookup failure ") $Map.lookup k nmMap) scp)
                | otherwise -> error "closure arity vs argument application mismatch"
          _ -> error "cannot invoke non closure heap values in application position"
evalClosureApp (FunAppCtxt ls (h : t) stk) = evalExp (FunAppCtxt ls t stk) h
evalClosureApp (LetContext _ _ _ ) = error "letcontext appearing where there should be an closure app context"
evalClosureApp (ThunkUpdate _ _ ) = error "thunkupdate context appearing where there should be a closure app context"
evalClosureApp (PrimAppCtxt _ _ _ _) = error "prim app context appearing where there should be a closure app context"
evalClosureApp SCEmpty  = error "empty stack where application context is expected"

evalPrimApp ::(Show ty, Ord ty) => ExpContext ty Ref -> DemoWithLayers s (Exp ty) ((HeapVal (Exp ty)), Ref)
evalPrimApp (PrimAppCtxt nm args [] stk) = do noBlackHoleRefs args ;  res <- applyPrim  nm $ reverse args ; applyStack stk res
evalPrimApp (PrimAppCtxt nm args (h:t) stk) = evalExp (PrimAppCtxt nm  args t stk) h
evalPrimApp (LetContext _ _ _ ) = error "letcontext appearing where there should be an prim app context"
evalPrimApp (ThunkUpdate _ _ ) = error "thunkupdate context appearing where there should be a prim app context"
evalPrimApp (FunAppCtxt _ _ _) = error "fun app context appearing where there should be a prim app context"
evalPrimApp SCEmpty  = error "empty stack where prim app context is expected"

forcingApply :: (Ord ty,Show ty)=>
    ExpContext ty Ref -> (HeapVal (Exp ty),Ref) -> DemoWithLayers  s (Exp ty) ((HeapVal (Exp ty)), Ref)
forcingApply = undefined

--- question: do we need to guard from blackholes in substitution points??????
applyStack :: (Ord ty,Show ty)=>
    ExpContext ty Ref -> (HeapVal (Exp ty),Ref) -> DemoWithLayers  s (Exp ty) ((HeapVal (Exp ty)), Ref)
applyStack SCEmpty p= return p
applyStack (LetContext _mv scp stk) (_v,ref)  = evalExp stk (instantiate1 (V ref) scp)
applyStack (FunAppCtxt ls [] stk) (_,ref) = evalClosureApp  (FunAppCtxt (ref : ls) [] stk)
applyStack (FunAppCtxt ls (h:t) stk) (_,ref) = evalExp (FunAppCtxt (ref:ls) t stk) h
applyStack (PrimAppCtxt nm revArgs [] stk) (_,ref) = evalPrimApp (PrimAppCtxt nm (ref:revArgs) [] stk)
applyStack (PrimAppCtxt nm revargs (h:t) stk) (_,ref) = evalExp (PrimAppCtxt nm (ref : revargs) t stk) h
applyStack (ThunkUpdate refTarget stk) pr@(_val,ref) =
                                      do   (targetVal,endRef)  <- demoLift $ heapRefLookupTransitive refTarget
                                           case targetVal of
                                                  -- should we do the indirection or direct contraction???
                                                  --- this semantics as is, can result in a chain of indirections
                                                 BlackHoleF -> do  demoLift $ unsafeHeapUpdate endRef (IndirectionF ref)  ; applyStack stk pr
                                                 _ -> error "tried to update a heap ref that isn't a blackholeF! ERRROR"

lookupPrimAccountBalance :: (Ord ty,Show ty)=> Text ->  DemoWithLayers  s (Exp ty) (Maybe Rational)
lookupPrimAccountBalance acctNam = do
      (_cnt,localizedMap) :: (Natural,Map.Map Text Rational) <-  get
      case Map.lookup  acctNam localizedMap of
          Just v |  v >= 0 -> return $ Just  v
                 | otherwise -> throwError $ "critical data invariant failure in underlying snapshot or localized map"
          Nothing -> do
              snapshotMap :: (Map.Map Text Rational ) <- ask
              case Map.lookup  acctNam snapshotMap of
                Just a | a >= 0 -> return $ Just  a
                       | otherwise -> throwError $ "critical data invariant in base snapshot of account balance data "
                Nothing ->  return Nothing  -- throwError $ "failure to find account balance for " ++ show acctNam

-- this may abort if target account doesn't exist
updatePrimAccountBalanceByAdding :: (Ord ty,Show ty)=> Text -> Rational ->  DemoWithLayers s (Exp ty) ()
updatePrimAccountBalanceByAdding nm amt = do
      currentBalance <- lookupPrimAccountBalance nm
      case currentBalance of
          Nothing   -> throwError "account doesn't exist "
          Just current |  current + amt < 0 -> throwError "cant debit an account more than its current balance"
                       |  otherwise -> do
                            (cnt,localizedMap) <- get
                            put (cnt, (Map.insert nm  $! (current + amt)) localizedMap)


applyPrim :: (Ord ty,Show ty)=> PrimOpId -> [Ref] ->  DemoWithLayers s  (Exp ty) ((HeapVal (Exp ty)), Ref)
applyPrim (PrimopId  trfer) [fromRef,toRef,posRatRef,fakeCryptoSigRef]
    | unpack trfer == "transfer" = do
        (fromVal,_reffrom) <- demoLift $ heapRefLookupTransitive fromRef
        (toVal,_refto) <- demoLift $ heapRefLookupTransitive toRef

        (posRatVal,_posRatRef) <- demoLift $ heapRefLookupTransitive posRatRef
        (fakeSigVal,_fakeSigRef) <- demoLift $ heapRefLookupTransitive fakeCryptoSigRef
        case (fromVal,toVal,posRatVal,fakeSigVal) of
            (VLitF (LText fromNm)
              ,VLitF (LText toNm)
              ,VLitF (LRational amt)
              ,VLitF (LText demoSig) )
                  | amt < 0 -> error "transfer command was invoked with a negative amount"
                  | otherwise ->  do
                      sourceBalanceM <- lookupPrimAccountBalance fromNm
                      targetBalanceM <- lookupPrimAccountBalance toNm
                      case (sourceBalanceM,targetBalanceM) of
                          (Just srcB,Just _targetB) ->
                              if srcB >= amt then
                                do
                                  updatePrimAccountBalanceByAdding fromNm (-amt)
                                  updatePrimAccountBalanceByAdding toNm amt
                                  (cnt, mp) <- get
                                  put (cnt+1,mp)
                                  tell [(cnt,Cmd fromNm toNm amt demoSig)]
                                  val <- return $ VLitF  $ LText $  pack "success"
                                  ref <- demoLift $ heapAllocate val  -- this shoudld be unit, but whatever
                                  return (val,ref)
                                else throwError "source balance is less than amount to be transfered"
                          bad -> throwError $ "accounts dont all exist " ++ show bad

            b -> error $ "deep invariant failure : bad args to transfer primop, the arguments were" ++ show b
applyPrim a b = error $ "called command  " ++ show  a ++ " with "  ++ show  (length b)   ++ " arguments"
