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
-- {-# LANGUAGE TemplateHaskell #-}

module Hopper.Internal.Core.OldANF(
    OldAnf(..)
    ,OldAppAnf(..)
    ,OldAnfAlloc(..)
    ,OldAnfVariable
    ,OldAnfRHS(..)
    )
  where

-- import Hopper.Internal.Core.Type

import Hopper.Internal.Core.Literal
--import Data.Bifunctor
import Data.Text (Text)
import Data.Data
import GHC.Generics
-- import Data.Word (Word64)
--import Data.Bifunctor.TH
--import Data.Bitraversable
--import Data.Bifoldable
-- import GHC.Generics
-- import  Control.Monad
--import Data.Bifunctor.Wrapped
import Prelude.Extras

import Bound.Var
-- import Bound.Scope.Simple (Scope(..))
-- import Control.Lens (view,over,_1,_2)
import Numeric.Natural
--import Hopper.Internal.Core.Literal


type OldAnfVariable = (Either Natural Text)


data OldAppAnf  a
    = OldEnterThunk !a -- if a is neutral term OR a free variable, this becomes neutral
    | OldFunApp !a ![a] --- if function position of FunApp is neutral, its neutral
    | OldPrimApp  {-!a -} !PrimOpId ![a] -- if any arg of a primop is neutral, its neutral
      --- case / eliminators will also be in this data type later
        deriving ( Data,Generic,Ord,Functor,Ord1,Show1,Eq1,Read1,Foldable,Traversable,Typeable,Eq,Read,Show)


data OldAnfAlloc a
  = OldSharedLiteral !Literal -- we currently do not have any fixed size literal types
                            -- so for now all literals are heap allocated
                            -- this will change once we add support for stuff like
                            -- Double or Word64
   | OldConstrApp {-a is this a resolved qname? -} {-!ty-} !ConstrId [a]
   | OldAllocateThunk  (OldAnf  a) -- Thunks share their evaluations
  --  | EvaluateThunk !a       -- Thunk evaluation is a special
  --                           -- no arg lambda plus sharing
                              -- thunks and closure should
                              -- record their free variables???
   | OldAllocateClosure ![(OldAnfVariable {-,Type ty,RigModel-})] -- arity >=0
                             ({-Simple.Scope -} (OldAnf (Var (OldAnfVariable) a)))  -- should we have global table of
                                                              -- "pointers" to lambdas? THINK ME + FIX ME
     deriving (Data,Generic,Ord,Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)



data OldAnfRHS  {-ty-} a
    = OldAnfAllocRHS !(OldAnfAlloc a) -- only heap allocates, no control flow
    | OldNonTailCallApp  (OldAppAnf a) -- control stack allocation; possibly heap allocation

   deriving (Data,Generic,Ord,Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)


{-
name rep
    binder id :: Word64
    debrujin nexting :: Word64
    sourcename :: Maybe (Fully qualified name)
    sourcloc :: something something something


-}



data OldAnf a
    = OldReturnNF  ![a] -- !(Atom ty a)
    | OldLetNF --  (Maybe Text) {-(Maybe(Type ty, RigModel)) -} (AnfRHS  a)
          ![OldAnfVariable]  -- should be Either Count [Text] later
          !(OldAnfRHS a) -- only ONE right hand side for now , which may have multiple return values
          -- this list of "independent" simultaneous let bindings must always be nonempty
          -- this is NOT a let rec construct and doesn't provide mutual recursion
          -- this is provided as an artifact of simplifying the term 2 anf translation
          !(OldAnf (Var OldAnfVariable a))

          -- (Simple.Scope (Maybe Text) (ANF ) a)
    -- | LetNFMulti ![AnfRHS ty a] !(Scope Word64 (ANF ty) a)
    | OldTailCallAnf (OldAppAnf  a)
    -- future thing will have | LetNFRec maybe?
    deriving (Data,Generic,Ord,Ord1,Eq1,Read1,Show1,Functor,Foldable,Traversable,Typeable,Eq,Read,Show)

