{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Hopper.Internal.Core.Term where

import Language.Hopper.Internal.Core.Literal
import Language.Hopper.Internal.Core.Type
import Data.Text (Text)
import Data.Data
import Bound
import Prelude.Extras
import Control.Monad
import GHC.Generics (Generic)
import Data.Traversable (fmapDefault,foldMapDefault)

data Exp ty a
  = V  a
  | ELit Literal
  -- | PrimApp Text [a]
  | Force (Exp ty a)  --- Force is a Noop on evaluate values,
                      --- otherwise reduces expression to applicable normal form
                      -- should force be more like seq a b, cause pure

  | Delay (Exp ty a)  --- Delay is a Noop on Thunked values, otherwise creates a thunk
                      --- note: may need to change their semantics later?!
  | Exp ty a :@ [Exp ty a]
  | Lam [(Text,Type ty,RigModel)]
        (Scope Text (Exp ty) a)
  | Let (Maybe Text) (Maybe (Type ty,RigModel))  (Exp ty a)  (Scope (Maybe Text) (Exp ty) a) --  [Scope Int Exp a] (Scope Int Exp a)
  deriving (Typeable,Data,Generic)
deriving instance (Read a, Read ty) => Read (Exp ty a)
deriving instance (Read ty) => Read1 (Exp ty)
deriving instance (Show a, Show ty) => Show (Exp ty a)
deriving instance (Show ty) => Show1 (Exp ty)
deriving instance (Ord ty) => Ord1 (Exp ty)
deriving instance (Ord ty,Ord a) => Ord (Exp ty a)
deriving instance (Eq ty) => Eq1 (Exp ty)
deriving instance (Eq a,Eq ty) => Eq (Exp ty a)

instance Functor (Exp ty)  where fmap       = fmapDefault

instance Foldable (Exp ty) where foldMap    = foldMapDefault

instance Applicative (Exp ty) where
  pure  = V
  (<*>) = ap

instance Traversable (Exp ty) where
  traverse f (V a)      = V <$> f a
  traverse _f (ELit e) = pure $ ELit e
  -- traverse f (PrimApp nm ls) = PrimApp nm <$> traverse f ls
  traverse f (Force e) = Force <$> traverse f e
  traverse f (Delay e) = Delay <$> traverse f e
  traverse f (x :@ ys)   = (:@) <$> traverse f x <*> traverse (traverse f) ys
  traverse f (Lam t e)    = Lam  t <$> traverse f e
  traverse f (Let mname mtype  bs b) = Let  mname mtype <$>  (traverse f) bs <*> traverse f b


instance Monad (Exp ty) where
  -- return = V
  V a         >>= f = f a
  -- PrimApp nm ls >>= f = PrimApp nm (map f ls)
  Delay e     >>= f = Delay $ e >>= f
  Force e     >>= f = Force $ e >>= f
  ELit e      >>= _f = ELit e -- this could also safely be a coerce?
  (x :@ y)    >>= f = (x >>= f) :@ (map (>>= f)  y )
  Lam t  e    >>= f = Lam t (e >>>= f)
  Let mname mtype bs  b >>= f = Let mname mtype (  bs >>= f)  (b >>>= f)
