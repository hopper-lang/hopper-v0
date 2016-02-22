{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Hopper.Internal.Core.Type where

import Data.Data
import qualified Data.Map as Map
import qualified  Data.Set as Set
import Data.Foldable (foldl')

import Prelude.Extras

data RigModel = Zero | One | Omega
 deriving (Eq,Ord,Show,Read,Typeable)

data Kind = Star | KArr Kind Kind | LiftedPubKey
  deriving (Eq,Ord,Read,Show,Typeable)

data TCon {-a -}=  TInteger | TNatural | TRational  | TUnit | TArrow RigModel
                | EncryptedFor |  SignedBy
                | PubKey String {- this is not how it'll work :) -}
                -- | Linear
    deriving (Eq,Ord,Read,Show ,Typeable)
data Type ty  {-a -}=  Tapp (Type ty) (Type ty) | TLit (TCon) | TVar ty
   deriving (Eq1,Ord1,Show1,Read1,Eq,Ord,Read,Show,Typeable,Functor,Foldable,Traversable)


{-
a -> b

Tapp (Tapp (TLit TArrow) a) b


EncryptedFor Bob Boolean


SignedBy Alice Dollar

-}

deduceLitKind :: TCon ->  Kind
deduceLitKind tc = case tc of
          TUnit -> Star
          TInteger -> Star
          TNatural -> Star
          TRational -> Star
          -- Linear -> KArr Star Star
          TArrow _ -> KArr Star (KArr Star Star)
          PubKey _s -> LiftedPubKey
          EncryptedFor -> KArr LiftedPubKey (KArr Star Star)
          SignedBy -> KArr LiftedPubKey (KArr Star Star)



wellKindedType ::(Show  ty, Ord ty ) => Map.Map ty Kind -> Type ty -> Either String Kind
wellKindedType kenv tau = case tau of
  TLit tc -> Right $ deduceLitKind tc
  TVar tv -> maybe  (Left $ "free type variable " ++ show tv) Right $ Map.lookup  tv kenv
  Tapp tarr tinput ->
      do  (KArr a b) <- wellKindedType kenv tarr ; c <- wellKindedType kenv tinput ;
          if a == c  {- this part will get tricky later :) -}
              then Right b
              else Left $   "Woops, kind mismatch " ++ show (a,c)

collectFreeVars :: (Ord a, Traversable f) => f a -> Set.Set a
collectFreeVars =   Set.fromList . foldl' (flip (:)) []
