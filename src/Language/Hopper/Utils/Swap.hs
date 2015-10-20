{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
-- {-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}




module Language.Hopper.Utils.Swap where
import GHC.Generics (Generic)

import Data.Bifunctor
import Data.Bitraversable
import Data.Bifoldable
import Data.Biapplicative
import Data.Data

newtype Swap f a b = Swap { unSwap :: f b a }
    deriving (Eq, Show,Ord,Data,Typeable,Generic)

instance Bifunctor p => Bifunctor (Swap p) where
  first f = Swap . second f . unSwap
  {-# INLINE first #-}
  second f = Swap . first f . unSwap
  {-# INLINE second #-}
  bimap f g = Swap . bimap g f . unSwap
  {-# INLINE bimap #-}

instance Bifunctor p => Functor (Swap p a) where
  fmap f = Swap . first f . unSwap
  {-# INLINE fmap #-}

instance Biapplicative p => Biapplicative (Swap p) where
  bipure a b = Swap (bipure b a)
  {-# INLINE bipure #-}

  Swap fg <<*>> Swap xy = Swap (fg <<*>> xy)
  {-# INLINE (<<*>>) #-}

instance Bifoldable p => Bifoldable (Swap p) where
  bifoldMap f g = bifoldMap g f . unSwap
  {-# INLINE bifoldMap #-}

instance Bifoldable p => Foldable (Swap p a) where
  foldMap f = bifoldMap f (const mempty) . unSwap
  {-# INLINE foldMap #-}

instance Bitraversable p => Bitraversable (Swap p) where
  bitraverse f g = fmap Swap . bitraverse g f . unSwap
  {-# INLINE bitraverse #-}

instance Bitraversable p => Traversable (Swap p a) where
  traverse f = fmap Swap . bitraverse f pure . unSwap
  {-# INLINE traverse #-}
