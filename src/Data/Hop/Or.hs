{-# LANGUAGE TypeOperators#-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
-- {-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric, LambdaCase #-}
module Data.Hop.Or((:+)(..)) where
import Data.Typeable
import Data.Data
import GHC.Generics

infixr 7  :+

data a :+ b = InL a | InR b
  deriving (Eq,Ord,Show,Typeable,Data,Generic,Functor,Foldable,Traversable)

