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

module Language.Hopper.Internal.Core.STLC where


import Bound
import Numeric.Natural
import Prelude.Extras
-- import Control.Applicative
import Control.Monad
import qualified  Data.Set as Set
import qualified  Data.Map.Strict as Map
import Data.Foldable (foldl')
import Data.Traversable
import Data.Text (Text)
import Data.Data
import qualified Data.Vector as V
import Data.Word
import Data.Int
import GHC.Generics (Generic)
import Control.Lens
-- import qualified  Data.Bits as Bits
-- import  Control.Monad.Trans.State.Strict (StateT(..))
import qualified Control.Monad.Trans.State.Strict as State

import  Control.Monad.Free

-- import Data.Bifunctor
-- import Data.Bitraversable
-- import Data.Bifoldable
-- import Data.Biapplicative

-- import qualified Data.Text as T

{- |  this iteration is essentially F_\omega, plus linear types,
plus inductive data types obeying the positivity condition, plus "crypto signed" values,
plus .... damnit, need dependent types to sanely treat crypto signed values

why?
because we dont know the commit id that a signed value in the result of a higher order transaction refers to until the parent computation is commited!


ok, so for now we're going to do F_omega, plus some singleton indexing
plus the kinda subtle "pubkey" "signed by"/"encrypted for" primitives that
-}


{-for now we're doing an STLC with a special pubkey type and some type level literals -}


data RigModel = Zero | One | Omega
 deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data Kind = Star | KArr Kind Kind | LiftedPubKey
  deriving (Eq,Ord,Read,Show,Data,Typeable,Generic)

data TCon {-a -}=  TInteger | TNatural | TRational  | TUnit | TArrow RigModel
                | EncryptedFor |  SignedBy
                | PubKey String {- this is not how it'll work :) -}
                -- | Linear
    deriving (Eq,Ord,Read,Show ,Data,Typeable,Generic)
data Type ty  {-a -}=  Tapp (Type ty) (Type ty) | TLit (TCon) | TVar ty
   deriving (Eq,Ord,Read,Show,Data,Typeable,Functor,Foldable,Traversable,Generic)


{-
a -> b

Tapp (Tapp (TLit TArrow) a) b


EncryptedFor Bob Boolean


SignedBy Alice Dollar

-}

deduceLitKind :: TCon ->  Kind
deduceLitKind tc = case tc of
          TUnit -> Star
          TInteger -> Star
          TNatural -> Star
          TRational -> Star
          -- Linear -> KArr Star Star
          TArrow _ -> KArr Star (KArr Star Star)
          PubKey _s -> LiftedPubKey
          EncryptedFor -> KArr LiftedPubKey (KArr Star Star)
          SignedBy -> KArr LiftedPubKey (KArr Star Star)



wellKindedType ::(Show  ty, Ord ty ) => Map.Map ty Kind -> Type ty -> Either String Kind
wellKindedType kenv tau = case tau of
  TLit tc -> Right $ deduceLitKind tc
  TVar tv -> maybe  (Left $ "free type variable " ++ show tv) Right $ Map.lookup  tv kenv
  Tapp tarr tinput ->
      do  (KArr a b) <- wellKindedType kenv tarr ; c <- wellKindedType kenv tinput ;
          if a == c  {- this part will get tricky later :) -}
              then Right b
              else Left $   "Woops, kind mismatch " ++ show (a,c)

collectFreeVars :: (Ord a, Traversable f) => f a -> Set.Set a
collectFreeVars =   Set.fromList . foldl' (flip (:)) []


{-
should term checking check the "price" of the expression
ie  -> (Rng, Type ty)
-}{-
checkTerm :: forall a ty . (Ord a,Show a,Eq ty,Show ty)=> Map.Map a (RigModel,Type ty)
              -> Exp ty a -> Either String (RigModel,Type ty)
checkTerm env term = do
                      missFVs <- Right $ collectFreeVars term `Set.difference` Map.keysSet env
                      if missFVs == Set.empty
                        then Right ()
                        else Left $ "error, there were unaccounted free variables: " ++  show missFVs
                      go env term

    where
      go :: Map.Map a (RigModel,Type ty) -> Exp ty a -> Either String (RigModel, Type ty)
                  --- need to check that expression obeys rigmodel constraints
                  --- on the free variables
      go mp tm = deduceType $ fmap (mp Map.!) tm
      deduceLitType :: Literal ->  Type ty
      deduceLitType (LRational _)  = TLit TRational
      deduceLitType (LNatural _) = TLit  TNatural
      deduceLitType (LInteger _) = TLit  TInteger

      {-
    NOTE, ignoring type level substitution for now,
    this is fine for STLC, but wrong :)

    also need to split this into  synthesize and check directions

    also need to add a nested??
      -}
      deduceType :: Exp ty (RigModel,Type ty) -> Either String (RigModel, Type ty)

      deduceType (ELit x ) = Right $  (Omega, deduceLitType x)
      deduceType (Let a b c) = undefined

      -- by induction we assume lineary/irrelevance is well behaved at this point
      deduceType (V t) = Right t
      -- deduceType (ELit x) = _typeOfLit
      -- deduceType (Let a b c ) = _elet
      --- need to check that linearity is obeyed
      deduceType (Lam t  scp)=
        let
          mp = undefined
          -- mp = _mp t
          -- linTys = _linTy t
          -- zeroTys= _zeroTy t
            in  deduceType $ instantiate (\x -> mp Map.! x) scp
      deduceType (fn :@ arg) =
          do   (argRig , argTyp) <- deduceType arg ;
               (_funRig ,fnTyp) <- deduceType fn
               case fnTyp of
                  (Tapp (Tapp (TLit (TArrow funArgRig)) from) to) ->
                    if from == argTyp
                      then      ---Right to
                        case (argRig,funArgRig) of
                              (Zero,Zero)  -> ()
                              (Zero,_) ->
                                  Left $ "Irelevant input supplied to relevant function type " ++ show fnTyp
                              (One,Omega) -> Left $ "Linear input applied to standard functiont type" ++ show fnTyp
                              (One,x) -> ()
                              (Omega,x)  -> ()
                      else Left $ "expected type " ++ show from
                            ++ " received " ++ show argTyp

                  _ -> Left $ "Expected Function type in application position, received :"
                        ++ show fnTyp

-}
      {-
        rough hacky(?) plan for now: change the types of Free variables from a to Type,
        that way

      -}
{-
checkLinearity ::

checkIrrelevance ::
-}

-- | 'Tag' is a constructor tag sum
newtype Tag = Tag { unTag :: Word64 } deriving (Eq, Show,Ord,Data,Typeable,Generic)

-- | current theres no pointer tagging in 'Ref' but eventually that will
-- probably change
newtype Ref = Ref {refPointer :: Word64} deriving  (Eq, Show,Ord,Data,Typeable,Generic)


instance Bounded Ref where
   minBound = Ref minBound
   maxBound = Ref maxBound

-- | interface for doing queries on bitwise representation and inspecting it
-- this could eg be used to query the upper 16 bits if we were to use a pointer
-- tagging scheme or the like. No such tagging scheme for now though :)
refRepLens :: Functor f =>(Word64 -> f a) -> Ref -> f a
refRepLens = \ f (Ref r) -> f r

-- | interface for doing bitwise transformations that yield a new ref
refTransform :: Functor f => (Word64 -> f Word64) -> Ref -> f Ref
refTransform = \ f (Ref r) -> Ref <$> f r

absoluteDistance  :: Ref -> Ref -> Word64
absoluteDistance = \(Ref a) (Ref b) -> if a > b then a - b else b - a

instance Enum Ref where
  succ rf@(Ref w) | rf < maxBound = Ref (1+ w)
                  | otherwise = error $ "succ: Ref overflow"
  pred rf@(Ref w) | rf > minBound = Ref (w - 1)
                  | otherwise = error $ "pred: Ref underflow"
  fromEnum (Ref w)
                | w < fromIntegral (maxBound :: Int) = fromIntegral w
                | otherwise =
                          error "fromEnum: any Ref that is larger than 2^63 -1  is unrepresentable as Int64"
  toEnum n | n >= 0 = Ref $ fromIntegral n
           | otherwise = error "toEnum: Cant represent negative locations in a Ref"


-- | this model of Values and Closures doens't do the standard
-- explicit environment model of substitution, but thats ok
-- also this is the "pre type erasure" representation
--  values at runtime will roughly look like  Val = Free  (Value ref ty)
-- because the underlying expressions will themselves have "values" in variable
-- positions?
-- or just make it polymorphic in ref/Ref
{-data Value ty = VLit !Literal
              | Constructor  !Tag  !(V.Vector (Value  ty  ))
              | Thunk !(Exp ty (Value ty ) )
              | PartialApp ![Arity] -- ^ args left to consume?
                           ![Value  ty  ]  -- ^  this will need to be reversed??
                           !(Closure  ty  (Value ty) {- (Value ty con v) -})
              | DirectClosure !(Closure ty (Value ty))
              | BlackHole
              | VRef !Ref --- refs are so we can have  exlpicit  sharing
                        --- in a manner thats parametric in the choice
                        -- of execution  semantics
                        --
   deriving
   (Typeable
    --,Functor
    --,Foldable
    --,Traversable
    ,Generic
    ,Data
    ,Eq
    ,Ord
    ,Show)
-}

type ValRec  ty  = Free (ValueF  ty) Ref


type HeapVal  ty = ValueF  ty (ValRec   ty)

data ValueF  ty v =    VLitF !Literal
              | ConstructorF  !Tag  !(V.Vector v)
              | ThunkF !(ANF ty v )
              | PartialAppF ![Arity] -- ^ args left to consume?
                           ![v  ]  -- ^  this will need to be reversed??
                           !(Closure  ty  v {- (Value ty con v) -})
              | DirectClosureF !(Closure  ty v)
              | BlackHoleF

              -- | VRefF !Ref --- refs are so we can have  exlpicit  sharing
                        --- in a manner thats parametric in the choice
                        -- of execution  semantics
   deriving
     (Typeable
      ,Functor
      ,Foldable
      ,Traversable
      ,Generic
      ,Data
      ,Eq
      ,Ord
      ,Show
      -- ,Eq1 -- ,Show1   -- ,Read1    -- ,Ord1   -- ,Eq2  -- ,Ord2  -- ,Read2   -- ,Show2
      )
{-
this is basically a definitional equality
-}
instance (Eq ty  ) => Eq1 (ValueF ty)
--where
--   (VLitF a) ==# (VLitF b) = a == b
--   (VLitF _) ==# _ = False
--   BlackHoleF ==# BlackHoleF = True
--   BlackHoleF ==# _ = False
--   (PartialAppF a1 b1 c1) ==# (PartialAppF a2 b2 c2) = a1 == a2 && b2 == b1 && c1 == c2
--   (PartialAppF _ _ _) ==# _  = False
--   (DirectClosureF a) ==# (DirectClosureF b) = a == b
--   (DirectClosureF _) ==# _ = False
--   (ConstructorF tg1 v1) ==# (ConstructorF tg2 v2) = tg1 == tg2 && v1 == v2
--   (ConstructorF _ _) ==# _ = False
--   (ThunkF e1) ==# (ThunkF e2) = e1 == e2
--   (ThunkF _) ==# _ = False

-- deriving instance(Eq1 con,Eq a,Eq ty) => Eq (Value ty con a)




data Arity = ArityBoxed {_extractArityInfo :: !Text} --- for now our model of arity is boring and simple
                              -- for now lets keep the variable names?
                              -- it'll keep the debugging simpler (maybe?)
 deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)

--- | 'Closure' may need some rethinking ... later
data Closure  ty a = MkClosure ![Arity] !(Scope Text (ANF ty) a)
  deriving (Eq,Ord,Show,Read,Ord1,Show1,Read1,Functor,Foldable,Traversable,Data,Generic)
deriving instance Eq ty => (Eq1 (Closure ty))

--- when we check closure arity, we're also gonna collaps indirected refernces
--- on the outside, also we're presuming
--- this may be the wrong name (maybe valueArity?),
--- either way, this sin't quite what we should have at the end, but
--- it'll work for now
closureArity :: forall m ty   .  Monad m => ValRec ty   -> (Ref -> m (HeapVal ty ))-> m  Word64
-- closureArity (Closure _ _)= 1
closureArity val resolve = go  5 val -- there really should only be like 1-2 refs indirection
    where
        go :: Int64 ->  ValRec ty  -> m  Word64
        go _ (Free (DirectClosureF (MkClosure arr _bdy))) = return $ fromIntegral  $ length arr
        go _ (Free (VLitF _)) = return 0
        go _ (Free (ConstructorF _ _)) = return 0
        go _ (Free (ThunkF _e)) = return 0
        go _ (Free (PartialAppF arr _accum _clos)) = return $ fromIntegral $ length arr
        go n (Pure r) | n  >= 0 =  do v <- resolve r ; go (n-1) v --- NB: this doesn't handle cycles currently!!!!
                      | otherwise = error $ "abort: deep ref cycle in application position " ++ show r


-- initHeap :: Ord a => Map a (Value ty a) -> Set a -> Map Ref (Value ty Ref)

-- evaluateWHNF ::
{-

-}

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

data StrictContext  ty  = SCEmpty
                        | SCArgEVal !(ValRec   ty) !() !(StrictContext ty )
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


-- because we're not doing let normal form yet, we need to thunkify if needed
argThunkify :: Exp ty (ValRec ty) -> HeapStepCounterM ty  Ref
argThunkify (V (Pure ref)) = pure ref
argThunkify (V (Free e)) = heapAllocate e
argThunkify (Delay e) = heapAllocate $ ThunkF e  -- this shrinks expression slightly, maybe remove later
argThunkify e = heapAllocate $ ThunkF e


-- evalLazyValue :: LazyContext ty -> ValRec ty -> HeapStepCounterM (ValRec ty)
-- evalLazyValue ctxt (Free )


{-
BURN WITH FIRE AFTER MOVING TO ANF for evaluation syntax


-}

-- evalLazy :: LazyContext ty -> Exp ty (ValRec ty) -> HeapStepCounterM ty (ValRec ty)
-- -- evalLazy (LCThunkUpdate tuRef rest) (V ())

-- evalLazy (LCThunkUpdate ref rest) (V (Pure ref))
-- evalLazy ctxt (V (Pure ref)) = do
--         mhv <- heapLookup ref
--         case mhv of
--           Nothing -> error $ "bad heap ref " ++ show ref
--           (Just (ThunkF e)) -> do
--               unsafeHeapUpdate ref BlackHoleF
--               evalLazy (LCThunkUpdate ref ctxt) e
--           (Just BlackHoleF) -> error  $"BOOOOOOM, halp i'm trapped in a black hole ref " ++ show ref
--           (Just val) -> applyLazy ctxt $ Free  val
-- evalLazy ctxt (V (Free (ThunkF e)))  --- note that with ANF assumption for values, can't really happen i think ...
--                                     -- this is somehow an unshared thunk
--                                     = evalLazy ctxt e
-- evalLazy (LCThunkUpdate ref rest) (V  (Free val)) = do unsafeHeapUpdate ref val ;
-- evalLazy ctxt (V  valf@(Free _)) = applyLazy ctxt valf
-- evalLazy ctxt (Force e)= evalLazy ctxt e
-- evalLazy ctxt (Delay e) = do rf <- heapAllocate (ThunkF e); applyLazy ctxt  (Pure rf)
-- evalLazy ctxt (ELit l ) = applyLazy ctxt ( Free $ VLitF l)
-- evalLazy ctxt (Let (_txt,_typ,_rig) lexp scp) =
--   -- could optimize substitution based on rig info
--         do rf <- heapAllocate (ThunkF lexp) ; evalLazy ctxt $ instantiate1 (V $ Pure  rf) scp
--                  -- | rig `elem` [Zero,One,Omega]  = undefined
-- evalLazy ctxt (fexp :@ argExp) = do aref <- argThunkify argExp ;  evalLazy (LCThunkEval ()  (Pure aref) $ ctxt) fexp
-- evalLazy ctxt (Lam ls scp) = applyLazy  ctxt  $ Free {- ??? -} $ DirectClosureF $ MkClosure (map (ArityBoxed . view  _1 ) ls) scp




-- | for 'applyLazy'  ctx  v,  v is the "function" and ctx carries the thunk evaluation context stack
-- -- so
-- applyLazy ::  LazyContext ty -> ValRec ty {- NEEDS TO BE A REF in naive semantics -} -> HeapStepCounterM ty (ValRec ty)
-- applyLazy LCEmpty v = return v -- undefined --return v
-- applyLazy (LCThunkUpdate ref rest) (Pure refVal) = do
--       hc <- heapLookup refVal


-- applyLazy ctxt@(LCThunkEval () expr rest) v =
--       case v of
--         (VRef ref) ->
--             do  (Just reValue) <-  heapLookup  ref
--                 case reValue of
--                   (VRef ref') -> error $ "double indirection in heap "++ show ref'
--                   val -> applyLazy ctxt val
--         (Thunk e)-> do unsafeHeapUpdate _ref BlackHole ;  evalLazy (LCThunkUpdate _ref ctxt) e  --- wait, do we need to push a "unblackhole the ref" operation?

{-evalLazy :: LazyContext ty -> HeapVal ty -> HeapStepCounterM ty (HeapVal ty)
evalLazy ctxt (V val) = applyLazy ctxt val
evalLazy ctxt (Force e)= evalLazy ctxt e
evalLazy ctxt (Delay e) = do rf <- heapAllocate (Thunk e); applyLazy ctxt  (VRef rf)
evalLazy ctxt (ELit l ) = applyLazy ctxt (VLit l)
evalLazy ctxt (Let (_txt,_typ,_rig) lexp scp) =
  -- could optimize substitution based on rig info
        do rf <- heapAllocate (Thunk lexp) ; evalLazy ctxt $ instantiate1 (V $ VRef rf) scp
                 -- | rig `elem` [Zero,One,Omega]  = undefined
evalLazy ctxt (fexp :@ argExp) = evalLazy (LCThunkEval ()  argExp $ ctxt) fexp
evalLazy ctxt (Lam ls scp) = applyLazy ctxt $ DirectClosure $ MkClosure (map (ArityBoxed . view  _1 ) ls) scp


-- | for 'applyLazy'  ctx  v,  v is the "function" and ctx carries the thunk evaluation context stack
-- so
applyLazy :: LazyContext ty -> Ref {- NEEDS TO BE A REF in naive semantics -} -> HeapStepCounterM ty (Value ty)
applyLazy LCEmpty v = return v
applyLazy ctxt@(LCThunkEval () expr rest) v =
      case v of
        (VRef ref) ->
            do  (Just reValue) <-  heapLookup  ref
                case reValue of
                  (VRef ref') -> error $ "double indirection in heap "++ show ref'
                  val -> applyLazy ctxt val
        (Thunk e)-> do unsafeHeapUpdate _ref BlackHole ;  evalLazy (LCThunkUpdate _ref ctxt) e  --- wait, do we need to push a "unblackhole the ref" operation?
-}


        -- (DirectClosure (Closure [x] scp) -> do ref <- heapAllocate (Thunk)
{-
need to finish the rest of the cases
-}

-- closureArity (VLit _) = error "what is lit arity?!"
                    {-   answer, its either a 0 arity value, or a prim op -}



data Atom ty  a = AtomVar !a
    | AtomicLit !Literal
    | AtomLam ![(Text,Type ty,RigModel)] -- do we want to allow arity == 0, or just >= 1?
                !(Scope Text (ANF ty) a)
  -- deriving(Eq,Ord,Functor,Foldable,Traversable,Eq,Ord)

data ANF ty a
    = ReturnNF !(Atom ty a)
    | ELitNF !Literal
    | ForceNF !a !a
    | !(Atom ty a) :@@ !(Atom ty a)
    | LetDerivedNF a a (Scope () (ANF ty) a)

    -- |
   deriving (
    Ord,
    Functor,
    Foldable,
    Traversable,
    Data,
    Eq,
    Show
    )


data Exp ty a
  = V  a
  | ELit Literal
  --  PrimApp a [Atomic a]
  | Force (Exp ty a)  --- Force is a Noop on evaluate values,
                      --- otherwise reduces expression to applicable normal form
                      -- should force be more like seq a b, cause pure

  | Delay (Exp ty a)  --- Delay is a Noop on Thunked values, otherwise creates a thunk
                      --- note: may need to change their semantics later?!
  | Exp ty a :@ Exp ty a
  | Lam [(Text,Type ty,RigModel)] -- do we want to allow arity == 0, or just >= 1?
        (Scope Text (Exp ty) a)
  | Let (Text,Type ty,RigModel)  (Exp ty a)  (Scope Text (Exp ty) a) --  [Scope Int Exp a] (Scope Int Exp a)
  deriving (Typeable,Data)
deriving instance (Read a, Read ty) => Read (Exp ty a)
deriving instance (Read ty) => Read1 (Exp ty)
deriving instance (Show a, Show ty) => Show (Exp ty a)
deriving instance (Show ty) => Show1 (Exp ty)
deriving instance (Ord ty) => Ord1 (Exp ty)
deriving instance (Ord ty,Ord a) => Ord (Exp ty a)
deriving instance (Eq ty) => Eq1 (Exp ty)
deriving instance (Eq a,Eq ty) => Eq (Exp ty a)

instance Functor (Exp ty)  where fmap       = fmapDefault

instance Foldable (Exp ty) where foldMap    = foldMapDefault

instance Applicative (Exp ty) where
  pure  = V
  (<*>) = ap

instance Traversable (Exp ty) where
  traverse f (V a)      = V <$> f a
  traverse _f (ELit e) = pure $ ELit e
  traverse f (Force e) = Force <$> traverse f e
  traverse f (Delay e) = Delay <$> traverse f e
  traverse f (x :@ y)   = (:@) <$> traverse f x <*> traverse f y
  traverse f (Lam t e)    = Lam  t <$> traverse f e
  traverse f (Let t bs b) = Let  t <$>  (traverse f) bs <*> traverse f b


instance Monad (Exp ty) where
  -- return = V
  V a         >>= f = f a
  Delay e     >>= f = Delay $ e >>= f
  Force e     >>= f = Force $ e >>= f
  ELit e      >>= _f = ELit e -- this could also safely be a coerce?
  (x :@ y)    >>= f = (x >>= f) :@ (y >>= f)
  Lam t  e    >>= f = Lam t (e >>>= f)
  Let t bs  b >>= f = Let t (  bs >>= f)  (b >>>= f)

