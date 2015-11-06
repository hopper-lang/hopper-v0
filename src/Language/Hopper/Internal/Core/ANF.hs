{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Hopper.Internal.Core.ANF  where

import Language.Hopper.Internal.Core.Type
import Language.Hopper.Internal.Core.Literal
import Data.Text (Text)
import Data.Data

import Prelude.Extras
import Bound

data Atom  ty a = AtomVar !a
    | AtomicLit !Literal
    | AtomLam ![(Text,Type ty,RigModel)] -- do we want to allow arity == 0, or just >= 1?
                !(Scope Text (ANF ty)  a)
   deriving(Eq,Ord,Functor,Foldable,Traversable,Data,Show,Read)
instance Eq ty => Eq1 (Atom ty)
instance Show ty => Show1 (Atom ty)
instance Ord ty => Ord1 (Atom ty)
instance Read ty => Read1 (Atom ty)

data ANF ty a
    = ReturnNF !(Atom ty a)
    | ELitNF !Literal
    | ForceNF !a !a
    | !(Atom  ty a) :@@ !(Atom  ty a)
    | LetDerivedNF a a (Scope () (ANF ty) a)

    -- |
   deriving (
    Ord,
    Functor,
    Foldable,
    Traversable,
    Data,
    Eq,
    Read,
    Show)
instance Eq ty => Eq1 (ANF ty)
instance Show ty => Show1 (ANF ty)
instance Ord ty => Ord1 (ANF ty)
instance Read ty => Read1 (ANF ty)

instance Monad (ANF ty)

instance Applicative (ANF ty)
