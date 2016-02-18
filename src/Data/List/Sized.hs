{-# LANGUAGE DataKinds, PolyKinds, GADTs, TypeFamilies, TypeOperators,
             ConstraintKinds, ScopedTypeVariables, RankNTypes,DataKinds #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Data.List.Sized where

--import GHC.Exts
import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits

{-
this code is copied with permission from
https://github.com/wellposed/numerical/blob/master/src/Numerical/Array/ShapeAlternatives/SingletonShape.hs
subject to the license of that associated code repo

-}

--data Nat = Z | S Nat

--type family n1 + n2 where
--  Z + n2 = n2
--  (S n1') + n2 = S (n1' + n2)

-- singleton for Nat
data SNat :: Nat -> * where
  SZero :: SNat 0
  SSucc :: SNat n -> SNat (1+ n)

--gcoerce :: (a :~: b) -> ((a ~ b) => r) -> r
--gcoerce Refl x = x
--gcoerce = gcastWith

-- inductive proof of right-identity of +
plus_id_r :: SNat n -> ((n + 0) :~: n)
plus_id_r _ = Refl


-- inductive proof of simplification on the rhs of +
plus_succ_r :: SNat n1 -> Proxy n2 -> ((n1 + (1 + n2)) :~: (1+ (n1 + n2)))
plus_succ_r _snat  _Prox = Refl


data Shape :: Nat -> * -> * where
  Nil :: Shape 0 a
  (:*) :: a -> Shape n  a -> Shape ( 1 + n) a


infixr 7 :||

data TeleList :: Nat -> Nat -> (Nat  -> * -> * ) -> * ->  * where
  TNil :: KnownNat m => Proxy m -> TeleList m 0 f a
  (:||) :: f n a -> TeleList m n  f a -> TeleList m (1+ n) f a

newtype FF (n :: Nat) (a :: * ) = FFC a

example :: TeleList 7 2 FF Int
example = FFC  1 :|| FFC 2  :||  TNil Proxy


reverseShape :: Shape n a -> Shape n a
reverseShape Nil = Nil
reverseShape list = go SZero Nil list
  where
    go :: SNat n1 -> Shape n1  a-> Shape n2 a -> Shape (n1 + n2) a
    go snat acc Nil = gcastWith (plus_id_r snat) acc
    go snat acc (h :* (t :: Shape n3 a)) =
      gcastWith (plus_succ_r snat (Proxy :: Proxy n3))
              (go (SSucc snat) (h :* acc) t)
