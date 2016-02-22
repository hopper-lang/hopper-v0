{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures, PolyKinds, TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds, GADTs #-}

--{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Hopper.Internal.Core.AnfIndexed where

import Data.Data
import Data.Word
--import Prelude.Extras
--import Data.Proxy
--import GHC.Generics
import Data.List.Sized
import GHC.TypeLits
import Hopper.Internal.Core.Literal
       --Hopper.Internal.Core.ANF

{-
TODO : think about Debruijn rep for telescope binders

-}
newtype FinWord (n :: Nat) = MkFinWord { _unFinWord :: Word64 } deriving (Eq, Ord,Show)

data FullyQualifiedName = FQN --- STUB, FILL IN TODO

finWord :: KnownNat n => p n -> Word64 -> Maybe (FinWord n)
finWord p wd = if  natVal p == fromIntegral wd then Just (MkFinWord wd)  else Nothing

data AnfVariable :: Nat -> *   where
    AnfLocalVar :: KnownNat n => !(FinWord n) -> AnfVariable n
    AnfFullyQualifiedName :: KnownNat n => !(Proxy n) ->  !FullyQualifiedName -> AnfVariable n
  --deriving ({-Eq,Ord,Data,-}Typeable,Generic)

  --deriving (Data,Generic,Ord1,Eq1,Read1,Show1,Ord,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)

data AnfBinderInfo  {-(a :: k)-}  = AnfBI_Stub -- fill me in!
 --deriving (Data,Generic,Ord1,Eq1,Read1,Show1,Ord,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)


data AppAnf  a
    = EnterThunk !(AnfVariable a) -- if a is neutral term OR a free variable, this becomes neutral
    | FunApp !(AnfVariable a) ![AnfVariable a] --- if function position of FunApp is neutral, its neutral
    | PrimApp  {-!a -} !PrimOpId ![AnfVariable a] -- if any arg of a primop is neutral, its neutral
      --- case / eliminators will also be in this data type later
        --deriving ( Data,Generic,Ord,{-Functor,Ord1,Show1,Eq1,Read1,Foldable,Traversable,-}Typeable,Eq,Read,Show)



data AnfAlloc a where
    SharedLiteral :: !Literal -> AnfAlloc a--
    ConstrApp  :: {-a is this a resolved qname? -} {-!ty-}
        !ConstrId  -> {- this should be in the same name space as runtime values, sort of!  -}
        ![AnfVariable a] -> AnfAlloc a
    AllocateThunk ::
        !(Anf  a) -> AnfAlloc a -- Thunks share their evaluations
    AllocateClosure ::( KnownNat n, KnownNat m ) => Proxy n -> Proxy m
          -> !(Shape n AnfBinderInfo  {-,Type ty,RigModel-}) -- arity >=0
          -> !( (Anf (m+n)))   -- should we have global table of
          -> AnfAlloc m                                               -- "pointers" to lambdas? THINK ME + FIX ME
     --deriving (Data,Generic,Ord,{-Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,-}Typeable,Eq,Read,Show)



data AnfRHS  {-ty-} a
    = AnfAllocRHS !(AnfAlloc a) -- only heap allocates, no control flow
    | NonTailCallApp  !(AppAnf a) -- control stack allocation; possibly heap allocation

   --deriving (Data,Generic,Ord,
   -- {-Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,-}
   --       Typeable,Eq,Read,Show)


{-
name rep
    binder id :: Word64
    debrujin nesting :: Word64
    sourcename :: Maybe (Fully qualified name)
    sourcloc :: something something something


-}



data Anf (a :: Nat ) where
     ReturnNF::
          ![AnfVariable a]  -> Anf a -- !(Atom ty a)
     LetNF :: (KnownNat m, KnownNat n) => Proxy n -> Proxy m
              --  (Maybe Text) {-(Maybe(Type ty, RigModel)) -} (AnfRHS  a)
          -> !(Shape n AnfBinderInfo)   --  should track type, computational relevance, etc  of the
          -> !(AnfRHS m)  -- only ONE right hand side for now , which may have multiple return values
          -- this is NOT a let rec construct and doesn't provide mutual recursion
          -- this is provided as an artifact of simplifying the term 2 anf translation
          -> !(Anf  (n+m ))
          -> Anf m

          -- (Simple.Scope (Maybe Text) (ANF ) a)
    -- | LetNFMulti ![AnfRHS ty a] !(Scope Word64 (ANF ty) a)
     TailCallAnf ::
        !(AppAnf  a) -> Anf a
    -- future thing will have | LetNFRec maybe?
    --deriving (Data,Generic,Ord
    --        {-,Ord1,Eq1,Read1,Show1-}
    --          {-,Functor,Foldable,Traversable-},Typeable,Eq,Read,Show)
