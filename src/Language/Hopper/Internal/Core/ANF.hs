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

import  Control.Monad
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

instance Eq2 Atom
instance Show2 Atom
instance Ord2 Atom
instance Read2 Atom

--instance Applicative (Atom ty) where
--  pure = AtomVar
--  (<*>)= ap

--instance Monad (Atom ty) where
--  (AtomVar a) >>= f =  f a
--  (AtomicLit l) >>=  _f =AtomicLit l
--  (AtomLam bs bod) >>= f = AtomLam bs (bod >>>= f)

data ANF ty a
    = ReturnNF !(Atom ty a)
    -- | ELitNF !Literal
    | ForceNF !a !a
    | !(Atom  ty a) :@@ !(Atom  ty a)
    | LetApp (Atom ty a) (Atom ty a) (Scope () (ANF ty) a)

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

instance Eq2 ANF
instance Show2 ANF
instance Ord2 ANF
instance Read2 ANF


instance Applicative (ANF ty) where
  pure  = \x -> ReturnNF (AtomVar x)
  (<*>) = ap

instance Monad (ANF ty) where
  (ReturnNF (AtomVar a)) >>=f = f a

  -- return = V
  --V a         >>= f = f a
  --Delay e     >>= f = Delay $ e >>= f
  --Force e     >>= f = Force $ e >>= f
  --ELit e      >>= _f = ELit e -- this could also safely be a coerce?
  --(x :@ y)    >>= f = (x >>= f) :@ (y >>= f)
  --Lam t  e    >>= f = Lam t (e >>>= f)
  --Let t bs  b >>= f = Let t (  bs >>= f)  (b >>>= f)

