
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}

module Hopper.Internal.Runtime.HeapRef(
      Ref(Ref)
      ,refRepLens
      ,refTransform
      ,refPointer
      ,absoluteDistance
      )
where

import Data.Word
import Data.Data
import GHC.Generics



-- | current theres no pointer tagging in 'Ref' but eventually that will
-- probably change
newtype Ref = Ref {refPointer :: Word64} deriving  (Eq,Read,Show,Ord,Typeable,Data,Generic)


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


