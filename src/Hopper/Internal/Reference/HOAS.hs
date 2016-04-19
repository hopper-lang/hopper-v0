{-# LANGUAGE DataKinds, GADTs  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ConstraintKinds   #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
--
-- {-# LANGUAGE TypeInType #-}
-- {-# LANGUAGE DuplicateRecordFields #-}
module Hopper.Internal.Reference.HOAS where

import qualified GHC.TypeLits as GT
import GHC.TypeLits (Nat)
import GHC.Types (Type, Constraint) -- this isn't 7.10 compatible but its sooo nice :)
import Data.Text (Text)
import Data.Void
import Data.Proxy

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
  ZeroVF :: (() -> [Value neut]) -> ValFun 0 neut
  SucVF :: {-GT.KnownNat n =>-} (Value neut -> ValFun n neut ) -> ValFun (n GT.+ 1) neut

data SomeValFun :: Type ->  Type where
  SomeValFun :: GT.KnownNat n => Proxy n -> ValFun n neut -> SomeValFun neut


--data ValFun :: Nat  One (Value -> [Value ])


-- need to add relevance annotations to these
data ExpFun :: Nat -> Type ->  Type where
  Z :: ([Exp a]) -> ExpFun 0 a
  S :: (a -> ExpFun n a) -> ExpFun (n GT.+ 1) a

data SomeExpFun :: Type -> Type where
  SomeExpFun :: GT.KnownNat n => Proxy n -> ExpFun  n neut -> SomeExpFun neut

data Literal :: Type  where --- this lives in a nother module, but leave empty for now
 LInteger :: Integer -> Literal


data DataDesc


data Value :: Type  -> Type where
  VLit :: Literal -> Value neut
  VFunction :: GT.KnownNat n => ValFun n neut -> Value neut
  VConstructor :: Text -> [Value neut ] -> Value neut
  VNeutral :: neut -> Value neut
  VThunk :: Thunk neut -> Value neut

data Thunk :: Type -> Type where
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

data Exp a where

  -- this model of pi and sigma aren't quite right
  -- think about it more tomorrow
  Pi :: SomeExpFun a -> Exp a
  Sigma :: Exp a -> SomeExpFun a -> Exp a
  BaseType :: PrimType -> Exp a
  Sorts :: Sort  -> Exp a
  Abs :: SomeExpFun a -> Exp a
  App :: Exp a -> Exp a -> Exp a
  Val :: a -> Exp a  --- values or names etc ???
  Case :: Exp a -- ^ the value being cased upon
        -> Maybe (Exp a)  -- optional type annotation
        -> [(Text, SomeExpFun a )] -- non-overlapping set of tags and continuations
        -> Exp a

