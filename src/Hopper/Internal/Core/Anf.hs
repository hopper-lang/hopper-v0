{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}

module Hopper.Internal.Core.Anf where

import Data.Word
--import Numeric.Natural
import Data.Data
import Prelude.Extras
import GHC.Generics
import Hopper.Internal.Core.Literal
       --Hopper.Internal.Core.ANF

{-
TODO : think about Debruijn rep for telescope binders

-}

data AnfVariable a =
    AnfLocalVar !Word64
    | AnfFullyQualifiedName !a
  deriving (Data,Generic,Ord1,Eq1,Read1,Show1,Ord,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)

data AnfBinderInfo  a  = AnfBI_Stub -- fill me in!
 deriving (Data,Generic,Ord1,Eq1,Read1,Show1,Ord,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)
{-
  relevance = irrelevant, linear, general ( wild card/ignore binders should be marked irrev??)
  source name, if it exists
  type???
-}

type TypeAnf = ()

data AppAnf  a
    = EnterThunk !(AnfVariable a) -- if a is neutral term OR a free variable, this becomes neutral
    | FunApp !(AnfVariable a) ![AnfVariable a] --- if function position of FunApp is neutral, its neutral
    | PrimApp  {-!a -} !PrimOpId ![AnfVariable a] -- if any arg of a primop is neutral, its neutral
    -- For the Anf form we translate the Map (from variable and arity to
    -- right-hand-sides, how you should think of this thing) to a list, so we
    -- can get the functor instance.
    --
    -- On the other hand, lists have ordering, which might (or might not) be an
    -- important aspect of our semantics. Also on the other hand, Brian's PR
    -- removes the parameter, so the problematic instance goes away.
    --
    -- TODO(joel): revisit the List / Map decision
    -- TODO(joel): this is going to conflict with Brian's PR -- we need to
    -- un-paramaterize the subterms
    | Case
        -- | The variable to case on
        !(AnfVariable a)
        -- | Its type, so we can determine which constructors are admissible
        -- for converage checking
        TypeAnf
        -- | The cases
        --
        -- (constructor, arity, binding info, rhs)
        ![(ConstrId, Word32, [AnfBinderInfo a], AnfRHS a)]
        -- | Case !(AnfVariable a) !(Map.Map (AnfVariable a, Word32) ([AnfBinderInfo a], AnfRHS a))
        deriving ( Data,Generic,Ord,Functor,Ord1,Show1,Eq1,Read1,Foldable,Traversable,Typeable,Eq,Read,Show)



data AnfAlloc a
  = SharedLiteral !Literal -- we currently do not have any fixed size literal types
                            -- so for now all literals are heap allocated
                            -- this will change once we add support for stuff like
                            -- Double or Word64
   | ConstrApp {-a is this a resolved qname? -} {-!ty-}
        !ConstrId {- this should be in the same name space as runtime values, sort of!  -}
        ![AnfVariable a]
   | AllocateThunk
        !(Anf  a) -- Thunks share their evaluations
   | AllocateClosure
          ![(AnfBinderInfo a {-,Type ty,RigModel-})] -- arity >=0
          !( (Anf a))  -- should we have global table of
                                                              -- "pointers" to lambdas? THINK ME + FIX ME
     deriving (Data,Generic,Ord,Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)



data AnfRHS  {-ty-} a
    = AnfAllocRHS !(AnfAlloc a) -- only heap allocates, no control flow
    | NonTailCallApp  !(AppAnf a) -- control stack allocation; possibly heap allocation

   deriving (Data,Generic,Ord,Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)


{-
name rep
    binder id :: Word64
    debrujin nesting :: Word64
    sourcename :: Maybe (Fully qualified name)
    sourcloc :: something something something


-}



data Anf a
    = ReturnNF
          ![AnfVariable a] -- !(Atom ty a)
    | LetNF --  (Maybe Text) {-(Maybe(Type ty, RigModel)) -} (AnfRHS  a)
          ![AnfBinderInfo a]  --  should track type, computational relevance, etc  of the
          !(AnfRHS a) -- only ONE right hand side for now , which may have multiple return values
          -- this is NOT a let rec construct and doesn't provide mutual recursion
          -- this is provided as an artifact of simplifying the term 2 anf translation
          !(Anf  a)

          -- (Simple.Scope (Maybe Text) (ANF ) a)
    -- | LetNFMulti ![AnfRHS ty a] !(Scope Word64 (ANF ty) a)
    | TailCallAnf
        !(AppAnf  a)
    -- future thing will have | LetNFRec maybe?
    deriving (Data,Generic,Ord,Ord1,Eq1,Read1,Show1,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)
