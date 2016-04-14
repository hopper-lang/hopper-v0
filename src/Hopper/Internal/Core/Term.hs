{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module  Hopper.Internal.Core.Term where

import Hopper.Internal.Core.Literal
-- import Hopper.Internal.Core.Type
import Data.Text  as T (Text)
import Data.Data
--import Bound
--import Data.Bifunctor
import Data.Word (Word32)
--import Prelude.Extras
import GHC.Generics (Generic)
import Hopper.Internal.Type.Relevance(Relevance)
import Hopper.Utils.LocallyNameless
--import Data.Traversable --  (fmapDefault,foldMapDefault)
import qualified Data.Map as Map -- FIXME, use IntMap or WordMap
import qualified Data.Vector as V


type Type = () -- TODO FIXME, wire in the real type info?, which will be "Term" :)

data BinderInfo =
      BinderInfoData
        {relevanceBI :: Relevance -- if zero, during evaluation we need not pass around
                                     --  BUT during NORMALIZATION, we probably do
                                     --  so the normalizer WILL thread around irrelevant values
                                     -- to properly support dependent type checking
                                     -- as is proper, because a runtime irrelevant value
                                     -- SHOULD be relevant during type checking, or
                                     -- it has no reason to exist
        , typeBICC :: Type -- at least for now, closure converted stuff may need a
          -- slightly different type system fragment than the Core layer Terms?
          -- NB: once we have existentials, should just be an "equivalent" subset
          -- of the full type theory?
        , sourceInfo :: Maybe Text --- this isn't quite right ...
        -- also should add
          } --- this needs to be fleshed out
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data Term =
    V Variable
  | BinderLevelShiftUP Word32 Term
  | ELit !Literal
  | Return !(V.Vector Term)  -- explicit multiple return values
                      -- should V x be replaced by Return [x] ?
                      --  once we lower to ANF
                      -- NOTE: for valid expressions,
  | EnterThunk !Term -- because we're in a strict IR rep,
                        -- we dont need to provide a seq like operation
                          -- seq a b === let _ := enterThunk a in b

  -- Delay is a Noop on Thunked values, otherwise creates a Thunked
  -- note: may need to change their semantics later?!
  -- Q: is it valid to thunk a thunked value? (no?)
  | Delay !Term
  | App !Term !(V.Vector Term)   --this is not curried :)
  | PrimApp  !PrimOpId --
             !(V.Vector Term) -- not sure if this is needed, but lets go with it for now

  | Lam !(V.Vector BinderInfo)
         !Term
  | Let !(V.Vector BinderInfo)
           Term --- RHS
           Term --- BODY
  -- case analysis:
  -- * the Word32 indicates the arity of the inspected constructor
  -- * invariant: length of the binders has to match arity
  -- TODO(joel) change this Word32 to an `Arity` when it exists.
  | Case Term Type (Map.Map (Term, Word32) (V.Vector BinderInfo, Term))
  -- Apply a constructor to arguments
  | ConstrApp !ConstrId !(V.Vector Term)
  deriving ({-Show1,Read1,Ord1,Eq1,-}Ord,Eq,Show,Read{-,Functor,Foldable-},Typeable{-,Traversable-})


--- NOTE: USE STE MONAD ONCE WE MIGRATE TO HSUM DESIGN
--- this is kinda only for "inlining" on debruijin variables for now
substitute :: Word32 -> (BinderSlot  -> Maybe Term) -> Term -> Either (String,Word32) Term
substitute baseLevel initMapper initTerm = goSub 0 initMapper initTerm
  where
    goSub :: Word32 -> (BinderSlot  -> Maybe Term) -> Term -> Either (String,Word32) Term
    goSub shift mapper  var@(V (LocalVar (LocalNamelessVar lnLvl bslt@(BinderSlot lnSlot))))
                |  lnLvl == (shift + baseLevel) =
                        maybe (Left ("bad slot", lnSlot))
                              (Right . BinderLevelShiftUP shift )
                             $ mapper bslt
                | otherwise =  Right var
    goSub _l _m var@(V (GlobalVarSym _ )) = Right var
    goSub shift mapper (Return ls) =  fmap Return $  mapM (goSub shift mapper ) ls
    goSub shift mapper (App fun args) =
          do   funNew <- goSub shift mapper fun
               argsNew <-  mapM (goSub shift mapper) args
               Right (App funNew argsNew)
    goSub shift mapper (Lam binders bod) =
          do   bodNew <- goSub (shift +1 )  mapper bod ; Right (Lam binders bodNew)
    goSub shift mapper (Let binders rhs bod) =
          do  rhsNew <- goSub shift mapper rhs ;
              bodNew <- goSub (shift +1 ) mapper bod ;
              Right (Let binders rhsNew bodNew)
    goSub shift mapper (PrimApp primop args) =
          do  argsNew <- mapM (goSub shift mapper) args
              Right (PrimApp primop argsNew)
    goSub shift mapper (BinderLevelShiftUP posAmt bod)
      | posAmt <= baseLevel + shift  = -- TODO AUDIT THIS TO TILL IT SCREAMS
          do  bodNew <- substitute (baseLevel + shift - posAmt) mapper bod
              Right (BinderLevelShiftUP posAmt bodNew)
      | otherwise = Left ("weird level shift appeared, you've been eaten by a grue", posAmt )
                --- OR WHATTTTTT??!?!?!?!
    goSub _shift _mapper lit@(ELit _)  = Right lit
    goSub shift mapper (EnterThunk bod ) =  fmap EnterThunk $ goSub shift mapper bod
    goSub shift mapper (Delay bod ) = fmap Delay $ goSub shift mapper bod
    goSub shift mapper (ConstrApp cId args) = do
      argsNew <- mapM (goSub shift mapper) args
      Right (ConstrApp cId argsNew)
    goSub shift mapper (Case tm () continuations) = do
      let transformCase
            :: ((Term, Word32), (V.Vector BinderInfo, Term))
            -> Either (String, Word32) ((Term, Word32), (V.Vector BinderInfo, Term))
          transformCase ((matchTm, arity), (binderInfos, matchCont)) = do
            -- substitute in the left-hand-side
            matchTm' <- goSub shift mapper matchTm
            -- ... as well as result continuations
            matchCont' <- goSub shift mapper matchCont
            return ((matchTm', arity), (binderInfos, matchCont'))

      tmNew <- goSub shift mapper tm
      let continuationsList = Map.toList continuations
      continuationsList' <- mapM transformCase continuationsList
      let continuations' = Map.fromList continuationsList'

      Right (Case tmNew () continuations')
