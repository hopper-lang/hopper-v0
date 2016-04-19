{-# LANGUAGE DataKinds, GADTs  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
--
-- {-# LANGUAGE TypeInType #-}
-- {-# LANGUAGE DuplicateRecordFields #-}
module Hopper.Internal.Reference.HOAS where

import qualified GHC.TypeLits as GT
import GHC.TypeLits (Nat)
import GHC.Types (Type) -- this isn't 7.10 compatible but its sooo nice :)

{- A Higher Order  abstract syntax model of the term AST
There will be a few infelicities to simplify / leverage the use
of metalanguage (haskell) lambdas/binders

1)

-}


data ValFun :: Nat -> Type where
  ZeroVF :: (() -> [Value]) -> ValFun 0
  SucVF :: GT.KnownNat n => (Value -> ValFun n) -> ValFun (n GT.+ 1)

--data ValFun :: Nat  One (Value -> [Value ])

data ExpFun :: Nat -> Type ->  Type where
  Z :: ([Exp a]) -> ExpFun 0 a
  S :: GT.KnownNat n => (a -> ExpFun n a) -> ExpFun (n GT.+ 1) a

data Literal --- this lives in a nother module

data Value :: Type where
  VLit :: Literal -> Value
  VFunction :: GT.KnownNat n => ValFun n -> Value

data Exp a where
  Abs :: GT.KnownNat n =>  ExpFun n a -> Exp a
  App :: Exp a -> Exp a -> Exp a
