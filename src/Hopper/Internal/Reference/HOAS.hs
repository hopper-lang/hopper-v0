{-# LANGUAGE DataKinds, GADTs  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
--
-- {-# LANGUAGE TypeInType #-}
-- {-# LANGUAGE DuplicateRecordFields #-}
module Hopper.Internal.Reference.HOAS where

import qualified GHC.TypeLits as GT
import Data.Primitive.MutVar
--import Control.Monad.Primitive
import GHC.TypeLits (Nat,KnownNat)
import GHC.Types (Type, Constraint) -- this isn't 7.10 compatible but its sooo nice :)
import Data.Text (Text)
import Data.Void
import Data.Proxy
import Hopper.Internal.Type.Relevance

{- A Higher Order  abstract syntax model of the term AST
There will be a few infelicities to simplify / leverage the use
of metalanguage (haskell) lambdas/binders

1) unboxed tuples/telescopes thereof

-}

data SizedTelescope :: Nat -> (Type ) ->(Nat -> Type -> Type ) -> (Nat -> Constraint) -> Type where
  STZ :: (constr 0)=> base  -> SizedTelescope 0 base induct constr
  STSucc :: (constr m , m~ (n GT.+ 1)) =>
          Proxy m -> induct m (SizedTelescope n base induct constr)
          -> SizedTelescope m base induct constr


data ValFun :: Nat -> Type ->  Type where
  ZeroVF :: (() -> a) -> ValFun 0 a
  SucVF :: {-GT.KnownNat n =>-} (a -> ValFun n a ) -> ValFun (n GT.+ 1) a

data SomeValFun :: Type ->  Type where
  SomeValFun :: GT.KnownNat n => Proxy n -> ValFun n a -> SomeValFun a


--data ValFun :: Nat  One (Value -> [Value ])


-- need to add relevance annotations to these
data ExpFun :: Nat -> Type ->  Type where
  Z :: (Exp a) -> ExpFun 0 a
  S :: (a -> ExpFun n a) -> ExpFun (n GT.+ 1) a

data SomeExpFun :: Type -> Type where
  SomeExpFun :: GT.KnownNat n => Proxy n -> ExpFun  n a -> SomeExpFun a

data Literal :: Type  where --- this lives in a nother module, but leave empty for now
 LInteger :: Integer -> Literal


data DataDesc


-- This factorization is to require
data ValueNoThunk :: Type -> (Type -> Type )  -> Type where
  VLit :: Literal ->  ValueNoThunk s neut
  VFunction :: (SomeValFun (Value s neut )) -> ValueNoThunk s neut
  VConstructor :: Text -> [Value s neut ] -> ValueNoThunk s  neut
  VNeutral :: neut s -> ValueNoThunk s neut

{-
TODO: add normalized types

-}

--- Values are either in Normal form, or Neutral, or a Thunk
data Value :: Type -> (Type -> Type )  -> Type where
    VNormal :: ValueNoThunk s neut -> Value  s neut
    VThunk :: Thunk s neut -> Value s neut


data ThunkValuation :: Type -> (Type -> Type ) -> Type where
  ThunkValueResult :: (ValueNoThunk s neut) ->  ThunkValuation s neut
  ThunkComputation :: (Exp (Value s neut)) -> ThunkValuation s neut
  --- Q: should there be blackholes?

data Thunk :: Type -> (Type -> Type ) -> Type where
  Thunk :: MutVar s (ThunkValuation s neut) -> Thunk s neut
--- figure this out, or maybe values need to be ST branded?

--- this isn't quite right yet
{-data NeutralTerm :: Type -> Type where
  NeutralFreeVariable :: gvar -> NeutralTerm gvar
  StuckCase :: NeutralTerm gv -> Maybe ()
            -> [(Text, SomeExpFun )]
            -> NuetralTerm gv
    -> -}

type SimpleValue = Value Void


data Sort :: Type   where
  LubSort :: [Sort ] -> Sort   -- following the agda convention,
                              --the base sort is modeled  as LubSort []
  LubSucc :: Sort  -> Sort

data PrimType :: Type where
  PTInteger :: PrimType

--- this is in some sense
data Telescope :: (Nat -> Type ->  Type -> Type) -> Type -> Nat -> Type where
  TZ :: f 0 t  t -> Telescope f  t 0
  TSucc :: forall t f  (n :: Nat) (m :: Nat) . (m ~ (n GT.+ 1)) =>
              (f m  t (Telescope f t n)) -> Telescope f t m

{- is this a profunctor? or something nuts? or both :))
   its like some sort of categorical thingy
   point being, its meant to model dependent pi
   ie
   Pi {x_1 : }
 -}
data PiTel :: Nat -> Type -> Type  -> Type -> Type where
  PiZ :: forall domainV domTy codomainTy .
       codomainTy ->
       -- ^ a Zero arg function is logically just the bare expression,
       -- merely unevaluated. that is, PiZ (Exp a) is the same as
       -- a unit value argument function  @ ()-> codomain @
       PiTel 0 domainV domTy codomainTy

  PiSucc :: forall domainV domTy codomainV m n . (m ~ (n GT.+ 1)) =>
          domTy ->
          -- ^ type of domain / current variable
          Relevance ->
          -- ^ variable usage annotation for the thusly typed function expression
          -- usage in type level expressions is deemed cost 0
          (domainV -> PiTel n domainV domTy codomainV ) ->
          -- ^ rest of the telescope
          PiTel m domainV domTy codomainV


data SigmaTel :: Nat -> Type -> Type -> Type where
  SigmaZ :: forall domainV domTy . SigmaTel 0 domainV domTy
  -- ^ an empty sigma telescope is basically just the unit value
  SigmaSucc :: forall domainV domTy m n . (m ~ (n GT.+ 1)) =>
            domTy ->
            -- ^ the type of the first element
            domainV ->
            -- ^ sigmas are pairs! so we have the "value" of the first element :)
            Relevance ->
            -- ^ the computational relevance for the associated value
            -- usage in type level expressions is deemed cost 0
            (domainV -> SigmaTel n domainV domTy) ->
            -- ^ second/rest of the telescope
            -- (sigmas are, after a generalized pair)
            SigmaTel m domainV domTy

data SomeNatF :: (Nat -> Type) -> Type where
  SomeNatF ::  forall n f . GT.KnownNat n => f n -> SomeNatF f


--data HoasType :: (Type -> Type ) where
--   --FunctionSpace ::


{- | the @'Exp' a @ type!
Notice that @a@ appears in both positive and negative recursively within 'Exp',
and thus is not a Functor. The idea is

[ note on Function spaces ]
the notion of unboxed tuple telescopes,
ie @ pi{ x_1 :r_1 t_1 .. } -> Sigma{ y_1 :g_1 h_1..}@
(where x_i and y_i are variables, r_i and g_i are relevance, and t_i and h_i are types/sorts )
in both argument and result positions (surprisingly)
results in an interesting unification of dependent sums and products
which also lends itself to some pretty cool logical embeddings!
Eg roughly @ Void === pi{a : Type}->sigma{res : a} @ which has zero
inhabitants,
and likewise something like  @ Unit === pi{ a : Type, v : a}-> Sigma{}@
or perhaps @  Unit == pi{}->sigma{} @, as either of those types
have only one inhabitant!

-}
data Exp :: Type -> Type  where

  {-
  our function type from unboxed tuples arity n>=0 to unboxed tuples arity m >=0
  should model the following coinductive / inductive type
  forall*{x_1 :r_1 t_1 ... x_n :t_n  } -> exist*{y_1 :h_1 q_1 .. y_m :h_m q_m}

  x_i,y_i are variables of type 'a'
  r_i,h_i are values of type Relevance
  t_i,q_i are expressions 'Exp a' that evaluate to valid sorts or types

  for all j such that j<i,  x_j is in the scope of t_i,

  all x_i are in scope for every q_1 .. q_m

  for all j < i, y_j is in the scope of q_i

  -}
  FunctionSpaceExp :: (KnownNat piSize, KnownNat sigSize) =>
      Proxy piSize ->
      -- ^ argument arity
      Proxy sigSize ->
      -- ^ result arity

      (PiTel piSize a (Exp a)
        (SigmaTel sigSize a (Exp a))) ->
      -- ^ See note on Function spaces
      --
      -- TODO: figure out better note convention, Carter
      Exp a
  BaseType :: PrimType -> Exp a
  --ExpType :: HoasType (Exp a) -> Exp a
  Sorts :: Sort  -> Exp a
  Abs :: SomeExpFun a -> Exp a
  App :: Exp a -> Exp a -> Exp a
  EReturn :: [Exp a] -> Exp a
  HasType :: Exp a -> Exp a -> Exp a  --- aka CUT
  {- TODO ADD LET -}
  Var :: a -> Exp a  --- values or names etc ???
  Case :: Exp a -- ^ the value being cased upon
        -> Maybe (Exp a)  -- optional type annotation,
                          -- also Joel thinks this is smelly, perhaps rightly
        -> [(Text, SomeExpFun a )] -- non-overlapping set of tags and continuations
        -> Exp a
{-
queue

first order -> hoas feasiblity sanity check
normal forms on types (values is bigger than we knew!)
BIDIRECTIONAL CHECKING (syntax) guillaume allais etc
make the Function space stuff not suck

-}


{-
-- it type checks!
>>> :t FunctionSpaceExp Proxy Proxy (PiZ (SigmaZ))
FunctionSpaceExp Proxy Proxy (PiZ (SigmaZ)) :: Exp a


>>> :t FunctionSpaceExp Proxy Proxy (PiSucc (Sorts (LubSort []) ) Omega  (\x -> PiZ (SigmaSucc (Sorts $ LubSort[]) x  Omega ((\ _y -> SigmaZ ) ) )))
FunctionSpaceExp Proxy Proxy
  (PiSucc (Sorts (LubSort []) ) Omega
      (\x -> PiZ
        (SigmaSucc (Sorts $ LubSort[]) x  Omega ((\ _y -> SigmaZ ) ) )))
  :: Exp a
-}

evalB :: Exp a -> a
evalB  _ = undefined


