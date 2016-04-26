{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DataKinds, GADTs  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}

#if MIN_VERSION_GLASGOW_HASKELL(8,0,0,0)
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE DuplicateRecordFields #-}
#endif

{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE ScopedTypeVariables  #-}


--- all downstream clients of this module might need this plugin too?
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
--
-- {-# LANGUAGE TypeInType #-}

module Hopper.Internal.Reference.HOAS(
  Exp(..)
  ,evalB -- TODO: implement this, Carter
  ,Sort(..)
  ,PrimType(..)
  ,DataDesc --- this will be the data * DECL data type?
  ,Relevance(..)
  ,ValueNoThunk(..)
  ,Value(..)
  ,Neutral(..)
  ,Literal(..)
  --,ValFun(..)
  ,ThunkValue(..)
  --,ExpFun(..)
  ,SomeArityValFun(..)
  ,SomeArityExpFun(..)
  ,RawFunction(..)
  ,SizedList(..)
  ,PiTel(..)
  ,SigmaTel(..)
  ,ThunkValuation(..)
  --,TwoFlipF(..)
  -- these reexports are subject to change or delition
  ,MutVar
  ,Proxy(..)
  ,SomeNatF(..)
  ,SimpleValue
  --,SizedTelescope(..)
  ) where

import qualified GHC.TypeLits as GT
import Data.Primitive.MutVar
import Data.Map.Strict (Map)
--import qualified Data.Map.Strict as Map
--import Control.Monad.Primitive
import GHC.TypeLits (Nat,KnownNat)
#if MIN_VERSION_GLASGOW_HASKELL(8,0,0,0)
--import GHC.Exts (Constraint, Type )
import Data.Kind (type (*))
-- TypeInType forces this latter import
-- and * = Type as a magic synonym for compat
-- and Type = TYPE LiftedPointer rep
#elif MIN_VERSION_GLASGOW_HASKELL(7,10,3,0)
import GHC.Exts (Constraint)
#else
#error "unsupported GHC version thats less than 7.10.3"
#endif
import Data.Text (Text)
import Data.Void
import Data.Proxy
import Hopper.Internal.Type.Relevance
import Control.Monad.STE
import Numeric.Natural

{- A Higher Order  abstract syntax model of the term AST
There will be a few infelicities to simplify / leverage the use
of metalanguage (haskell) lambdas/binders

1) unboxed tuples/telescopes thereof

-}




data SomeArityValFun :: Nat -> * ->  * where
  SomeValFun :: GT.KnownNat n => Proxy n -> RawFunction n m a (Exp a) -> SomeArityValFun m a

-- for the underlying HOAS for terms, this is probably better
-- than
data RawFunction :: Nat -> Nat -> * -> (Nat ->  *) -> * where
  RawFunk :: (KnownNat domSize, KnownNat codSize ) =>
              Proxy domSize ->
              Proxy codSize ->
              (SizedList domSize domain ->  codomainF codSize) ->
              RawFunction domSize codSize domain codomainF
            -- ^ This has a nice profuntor / category / semigroupid instance!
            -- but does that matter?

{--}

data SomeArityExpFun :: Nat -> * -> * where
  SomeArityExpFun :: (GT.KnownNat n , GT.KnownNat m)=>
                     Proxy n ->
                     Proxy m  ->
                     (RawFunction n m a (Exp a)) ->
                     SomeArityExpFun m a

data Literal :: *  where --- this lives in a nother module, but leave empty for now
 LInteger :: Integer -> Literal


data DataDesc



-- This factorization is to require
data ValueCanCase :: * -> ( * -> * )  -> * where
  VLit :: Literal ->  ValueCanCase s neut


  --VFunction :: (SomeArityValFun resultArity (Value  s neut )) -> ValueNoThunk s neut
  VConstructor :: Text -> [Value s neut ] -> ValueCanCase s  neut

  --VPseudoUnboxedTuple :: [Value s neut] -> ValueNoThunk s neut
  -- unboxed tuples never exist as heap values, but may be the result of
 -- some computation

{-
TODO: add normalized types

-}

data Neutral :: *  -> * where
  NeutVariable :: Text {- this isn't quite right -} ->
                  --- ^ todo fix up this detail, Carter
                  Neutral s
  NeutCase :: (Neutral s ) ->
              --( Maybe (Value?)  ) ->
              Map Text (SomeArityExpFun n (Value s Neutral )) ->
              Neutral s
  NeutApp :: (KnownNat from, KnownNat to )=>
        Neutral s ->
        Proxy from ->
        Proxy to ->
        SizedList to (Value s Neutral)  ->
        Neutral s
  NeutForce :: KnownNat to =>
        Neutral s ->
        Proxy to ->
        Neutral s

--- Values are either in Normal form, or Neutral, or a Thunk
---
data Value :: * -> ( * -> * )  -> * where
    VNormal :: ValueCanCase s neut -> Value  s neut
    VThunk :: ThunkValue s neut -> Value s neut
    VFunk :: (RawFunction n m a (Exp (Value s neut))) -> Value s neut
    VNeutral :: neut s  -> Value s neut


data ThunkValuation :: * -> Nat -> ( * -> * ) -> * where
  ThunkValueResult :: SizedList n (Value s neut)  ->  ThunkValuation s  n neut
  ThunkComputation :: (Exp  (Value s neut) n ) -> ThunkValuation s n neut
  --- Q: should there be blackholes?

data ThunkValue :: * -> ( * -> * ) -> * where
  ThunkValue ::KnownNat n => Proxy n -> MutVar s (ThunkValuation s n neut ) -> ThunkValue s neut
--- figure this out, or maybe values need to be ST branded?

--- this isn't quite right yet
{-data NeutralTerm :: * -> * where
  NeutralFreeVariable :: gvar -> NeutralTerm gvar
  StuckCase :: NeutralTerm gv -> Maybe ()
            -> [(Text, SomeExpFun )]
            -> NuetralTerm gv
    -> -}

type SimpleValue = Value Void


data Sort :: *   where
  LubSort :: [Sort ] -> Sort  -- max of a list of sorts
  SuccSort :: Sort -> Sort -- 1 up the other sorts!
  BaseSort :: Natural  -> Sort

data PrimType :: * where
  PTInteger :: PrimType

--- this is in some sense
{-
--- revisit this to think about how this may or may not help
clarify
data Telescope :: (Nat -> * ->  * -> Type) -> * -> Nat -> * where
  TZ :: f 0 t  t -> Telescope f  t 0
  TSucc :: forall t f  (n :: Nat) (m :: Nat) . (m ~ (n GT.+ 1)) =>
              (f m  t (Telescope f t n)) -> Telescope f t m-}

{- is this a profunctor? or something nuts? or both :))
   its like some sort of categorical thingy
   point being, its meant to model dependent pi
   ie
   Pi {x_1 : }
 -}
data PiTel :: Nat -> * -> *  -> * -> * where
  PiZ :: forall domainV domTy codomainTy .
       codomainTy ->
       -- ^ a Zero arg function is logically just the bare expression,
       -- merely unevaluated. that is, PiZ (Exp a) is the same as
       -- a unit value argument function  @ ()-> codomain @
       PiTel 0 domainV domTy codomainTy

  PiSucc :: forall domainV domTy codomainTy m n . (m ~ (n GT.+ 1)) =>
          domTy ->
          -- ^ * of domain / current variable
          Relevance ->
          -- ^ variable usage annotation for the thusly typed function expression
          -- usage in * level expressions is deemed cost 0
          (domainV -> PiTel n domainV domTy codomainTy ) ->
          -- ^ rest of the telescope
          PiTel m domainV domTy codomainTy

-- | @SigmaTel n sort ty val@ can be thought of as eg
  -- SigmaSigma  (Ty1 :_rel1 Sort1) (f : (val1 : Ty1 )-> Ty2 val1)
  -- yiels a pair (x : Ty1 , y : f x )
data SigmaTel :: Nat -> * -> * -> * where
  SigmaZ :: forall {-domainExp-} domainV domTy . SigmaTel 0 {-domainExp-}  domainV domTy
  -- ^ an empty sigma telescope is basically just the unit value
  SigmaSucc :: forall domainTy domainV  {-domainSort-} m n . (m ~ (n GT.+ 1)) =>
            {-domainSort ->-}
            -- ^ the type/sort of the first element
            domainTy ->
            -- ^ sigmas are pairs! so we have the "value" / "expression"
            -- of the first element, which has type domSort.
            -- Which may or may not be evaluated yet!
            Relevance ->
            -- ^ the computational relevance for the associated value
            -- usage in * level expressions is deemed cost 0
            (domainV -> SigmaTel n {-domainSort-} domainV domainTy) ->
            -- ^ second/rest of the telescope
            -- (sigmas are, after a generalized pair), and in a CBV
            -- evaluation order, Expressions should be normalized
            -- (or at least neutral , before being supplied to the dependent term )
            SigmaTel m {-domainSort-} domainV domainTy

data SomeNatF :: (Nat -> * ) -> * where
  SomeNatF ::  forall n f . GT.KnownNat n => f n -> SomeNatF f

{-
indexed descriptions are a good strawman
datatype/type model

data IDesc {l : Level}(I : Set (suc l)) : Set (suc l) where
  var : I -> IDesc I
  const : Set l -> IDesc I
  prod : IDesc I -> IDesc I -> IDesc I
  sigma : (S : Set l) -> (S -> IDesc I) -> IDesc I
  pi : (S : Set l) -> (S -> IDesc I) -> IDesc I


-}



infixr 5 :*  -- this choice 5 is adhoc and subject to change



data SizedList ::  Nat -> * -> * where
  SLNil :: SizedList 0 a
  (:*) :: a -> SizedList n a -> SizedList (n GT.+ 1) a
sizedFmap :: forall n a b . (a -> b) -> SizedList n a -> SizedList n b
sizedFmap f SLNil = SLNil
sizedFmap f (a :* as) = f a :* (sizedFmap f as )

sizedMapM :: forall n a b m . Monad m  => (a -> m b) -> SizedList n a ->  m (SizedList n b)
sizedMapM f SLNil = return SLNil
sizedMapM f (a :* as) = do tl <- (sizedMapM f as ) ; hd <- f a ; return (hd :* tl)






--data HoasType ::  * -> * ) where
--   --FunctionSpace ::


{- | the @'Exp' a @ type!
Notice that @a@ appears in both positive and negative recursively within 'Exp',
and thus is not a Functor. The idea is

[ note on Function spaces ]
the notion of unboxed tuple telescopes,
i.e. @ pi{ x_1 :r_1 t_1 .. } -> Sigma{ y_1 :g_1 h_1..}@
(where x_i and y_i are variables, r_i and g_i are relevance, and t_i and h_i are types/sorts )
in both argument and result positions (surprisingly)
results in an interesting unification of dependent sums and products
which also lends itself to some pretty cool logical embeddings!
E.g. roughly @ Void === pi {a : Type}->sigma {res : a} @ which has zero
inhabitants,
and likewise something like  @ Unit === pi{ a : Type, v : a}-> Sigma{}@
or perhaps @  Unit == pi{}->sigma{} @, as either of those types
have only one inhabitant!

-}
data Exp :: * -> Nat  -> *  where

  {-
  our function * from unboxed tuples arity n>=0 to unboxed tuples arity m >=0
  should model the following coinductive / inductive type
  forall*{x_1 :r_1 t_1 ... x_n :t_n  } -> exist*{y_1 :h_1 q_1 .. y_m :h_m q_m}

  x_i,y_i are variables of * 'a'
  r_i,h_i are values of * Relevance
  t_i,q_i are expressions 'Exp a' that evaluate to valid sorts or types

  for all j such that j<i,  x_j is in the scope of t_i,

  all x_i are in scope for every q_1 .. q_m

  for all j < i, y_j is in the scope of q_i

  -}
  --- QUESTION: is this also the right binder rep
  -- for term level lambdas?! I think so ...
  -- on the flip side, that flies in the face of a bidirectional
  -- curry style presentation of the * theory
  FunctionSpaceTypeExp :: (KnownNat piSize, KnownNat sigSize) =>
      Proxy piSize ->
      -- ^ argument arity
      Proxy sigSize ->
      -- ^ result arity

      (PiTel piSize a (Exp  a 1)
        (SigmaTel sigSize {-(Exp  a 1) -}a (Exp  a 1))) ->
      -- ^ See note on Function spaces
      -- \pi x_1 ... \pi x_piSize -> Exists y_1 ... Exists y_sigmaSize
      --
      -- TODO: figure out better note convention, Carter
      Exp  a 1
      -- ^ Functions / Types  are a single value!
      --
  DelayType :: (KnownNat sigSize) =>
      Proxy sigSize ->
      SigmaTel sigSize {-(Exp  a 1) -} a (Exp  a 1) ->
      Exp a 1

  BaseType :: PrimType -> Exp  a 1
  --ExpType :: HoasType (Exp a) -> Exp a
  --FancyAbs ::
  Sorts :: Sort  -> Exp a 1
  Abs :: (RawFunction n m a (Exp a)) -> Exp a 1
  --Abs :: SomeArityExpFun m a -> Exp  a 1
  --App :: Exp 1 a -> Exp n a -> Exp a
  App :: (KnownNat from , KnownNat to) =>
    -- We always need to check
      Proxy from ->
      Proxy to  ->
      Exp a 1 {-  from -> to, always need to chek -} ->
      -- ^ the function position, it should evaluate to a function
      -- that has input arity @from@ and result arity @to@
      -- which needs to be checked by the evaluator
      Exp a from  ->
      Exp a to
  Pure :: a -> Exp a 1
  Return :: SizedList n (Exp a 1) -> Exp  a n
  HasType :: KnownNat n => Exp  a n-> Proxy n -> Exp  a 1 -> Exp  a n  --- aka CUT
  Delay :: KnownNat n => Proxy n -> Exp  a n -> Exp  a 1
  Force :: KnownNat n => Exp  a 1 -> Proxy n    -> Exp  a n
  -- ^ Not sure if `Force` and `Delay` should have this variable arity,
  -- But lets run with it for now
  LetExp :: Exp  a m -> (RawFunction m h a (Exp a)) -> Exp  a h
  --- ^ this is another strawman for arity of functions
  --- both LetExpExp and LetExp are essentially the same thing
  --- Let is also existential unpack for unboxed tuples, which
  -- can otherwise only be deconstructed  by calling a function
  --LetExp :: Exp  a m   -> (SizedList m a   -> Exp  a h) -> Exp   a h

  -- ^ Let IS monadic bind :)
   -- note that this doesn't quite line up the arities correctly... need to think about this more
   -- roughly Let {y_1 ..y_m} = evaluate a thing of * {}->{y_1 : t_1 .. y_m : t_m}
   --                  in  expression

  -- | 'CaseCon' is only
  CaseCon :: Exp  a 1 -- ^ the value being cased upon
        -> Maybe (Exp  a 1)  -- optional type annotation,
                          -- that should be a function from the
                          -- scrutinee to a generalization of the cases
        -> Map Text (SomeArityExpFun m a )
        -- ^ non-overlapping set of tags and continuations
        -- but all cases invoke the same continuation,
        -- and thus must have the same result arity

        -- TODO, look at sequent calc version
        -> Exp   a m

{-
queue

first order -> has feasibility sanity check
normal forms on types (values is bigger than we knew!)
BIDIRECTIONAL CHECKING (syntax) guillaume allais etc
make the Function space stuff not suck

-}


{-
-- it * checks!
>>> :t FunctionSpaceExp Proxy Proxy (PiZ (SigmaZ))
FunctionSpaceExp Proxy Proxy (PiZ (SigmaZ)) :: Exp a


>>> :t FunctionSpaceExp Proxy Proxy (PiSucc (Sorts (LubSort []) ) Omega  (\x -> PiZ (SigmaSucc (Sorts $ LubSort[]) (Var x)  Omega ((\ _y -> SigmaZ ) ) )))
FunctionSpaceExp Proxy Proxy
    (PiSucc (Sorts (LubSort []) ) Omega
    (\x -> PiZ
      (SigmaSucc (Sorts $ LubSort[]) (Var x)  Omega ((\ _y -> SigmaZ ) ) )))
  :: Exp a
-}

evalB ::   Exp  (Value s Neutral) n -> STE String  s (SizedList n (Value s Neutral))
evalB  (App parg pres funExp argExp) = undefined
evalB  (FunctionSpaceTypeExp _ _ _) = undefined
evalB (DelayType _ _) = undefined
evalB (BaseType _) = undefined
evalB (Sorts s) = undefined
evalB (Pure val) = return $ val :* SLNil
evalB (Abs f) = return $ (  VFunk f ) :* SLNil
evalB  (Return ls) = sizedMapM evalSingle ls
evalB (HasType x prox  _) = evalB x
evalB (Delay _resArity resExp ) =  undefined
evalB (Force _proxyRes _resExp ) = undefined
evalB (LetExp argExp (RawFunk parg pres funk)) = do args <- evalB argExp ; evalB (funk args)
evalB (CaseCon scrutinee _resTy casesMap) = do
  valScrutinee <- evalSingle scrutinee
  case valScrutinee of
    (VThunk _v) -> throwSTE "error :  case analysis of thunk/closures isn't allowed"
    (VFunk _v) -> throwSTE "error : case analysis of function values/closures isn't allowed"
    (VNeutral neut) -> return $ ( VNeutral $!  NeutCase neut {- _resTy here? -} casesMap) :* SLNil
                        ---- WOAH, this is a mismatch in arity wrt normalization ... gah




evalSingle ::   Exp  (Value s Neutral) 1 -> STE String  s  (Value s Neutral)
evalSingle  (App parg pres funExp argExp) = undefined
evalSingle  (FunctionSpaceTypeExp _ _ _) = undefined ---
evalSingle (DelayType _ _) = undefined --- see BaseType and FunctionSpace
evalSingle (BaseType _) = undefined --- need normalized type expressions
evalSingle (Sorts s) = undefined --- need normalized type expressions
evalSingle (Pure v) = return v
evalSingle (Abs f) = return $ (VNormal $! VFunk f )
evalSingle (Return (x :* SLNil)) = evalSingle x
evalSingle (Return (_ :* _ )) = throwSTE "error: impossible branch for evalSingle of Return"
                      ---  This second case shouldnt be needed
                      --- if the type nat solver also helped the coverage checker
--evalSingle  (Return ls) = sizedMapM (\ x -> do  (y :* SLNil) <- evalB (x :* SLNil); return y ) ls
evalSingle (HasType x prox ty)  =  do
        res <- evalB x
        case res of
            (v :* SLNil) -> return v
            (_ :* _) -> throwSTE "bad bad arity for HastypeExpr in evalSingle"
evalSingle (Delay resArity resExp ) =  undefined
evalSingle (Force proxyRes resExp ) = undefined
evalSingle (LetExp argExp bodyBind) = undefined
evalSingle (CaseCon scrutinee _resTy casesMap) = undefined
