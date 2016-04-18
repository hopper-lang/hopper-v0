{-# LANGUAGE DataKinds, GADTs  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE DuplicateRecordFields #-}
module Hopper.Internal.Core.HOAS where

import qualified GHC.TypeLits as GT
import GHC.TypeLits (Nat)
import GHC.Types (Type)

{- A Higher Order  abstract syntax model of the term AST
There will be a few infelicities to simplify / leverage the use
of metalanguage (haskell) lambdas/binders

1)

-}


data ValFun :: Nat -> Type where
  OneVF :: (Value -> [Value]) -> ValFun 1
  SomeVF :: GT.KnownNat n => (Value -> ValFun n) -> ValFun (n GT.+ 1)

--data ValFun :: Nat  One (Value -> [Value ])

data ExpFun :: Nat -> Type ->  Type where
  One :: (a -> [Exp a]) -> ExpFun 1 a
  Some :: GT.KnownNat n => (a -> ExpFun n a) -> ExpFun (n GT.+ 1) a

data Literal --- this lives in a nother module

data Value :: Type where
  VLit :: Literal -> Value
  VFunction :: GT.KnownNat n => ValFun n -> Value

data Exp a where
  Abs :: GT.KnownNat n =>  ExpFun n a -> Exp a
  App :: Exp a -> Exp a -> Exp a
