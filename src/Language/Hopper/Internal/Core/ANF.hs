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

module Language.Hopper.Internal.Core.ANF  where

-- import Language.Hopper.Internal.Core.Type
import Language.Hopper.Internal.Core.Literal
import Data.Text (Text)
import Data.Data
-- import Data.Word (Word64)

-- import GHC.Generics
-- import  Control.Monad
import Prelude.Extras
-- import Bound hiding (Scope,unscope)
-- import Language.Hopper.Internal.Core.Term
-- import qualified   Bound.Scope.Simple as Simple
import Bound.Var
-- import Bound.Scope.Simple (Scope(..))
-- import Control.Lens (view,over,_1,_2)







data AppANF  a = EnterThunk a
                 | FunApp a ![a]
                 | PrimApp  a !Text ![a]
        deriving ( Ord,
         Functor,
         Ord1,Show1,Eq1,Read1,
         Foldable,
         Traversable,
         Typeable,
         Data,
         Eq,
         Read,
         Show)

data AnfRHS  {-ty-} a = SharedLiteral !Literal -- we currently do not have any fixed size literal types
                                          -- so for now all literals are heap allocated
                                          -- this will change once we add support for stuff like
                                          -- Double or Word64
                 | ConstrApp a {-!ty-} !ConstrId [a]
                 | AllocateThunk  (ANF   a) -- Thunks share their evaluations
                --  | EvaluateThunk !a       -- Thunk evaluation is a special
                --                           -- no arg lambda plus sharing
                                            -- thunks and closure should
                                            -- record their free variables???
                 | AllocateClosure ![(Text{-,Type ty,RigModel-})] -- arity >=0
                                   ({-Simple.Scope -} (ANF (Var Text a)))  -- should we have global table of
                                                              -- "pointers" to lambdas? THINK ME + FIX ME

                 | NonTailCallApp  (AppANF  a) -- control stack allocation; possibly heap allocation


   deriving (Ord,Ord1,Eq1,Show1,Read1,
    Functor,
    Foldable,
    Traversable,
    Typeable,
    Data,
    Eq,
    Read,
    Show)


data ANF  a
    = ReturnNF  !a -- !(Atom ty a)
    | LetNF (Maybe Text) {-(Maybe(Type ty, RigModel)) -} (AnfRHS  a)
          (ANF (Var (Maybe Text) a)) -- (Simple.Scope (Maybe Text) (ANF ) a)
    -- | LetNFMulti ![AnfRHS ty a] !(Scope Word64 (ANF ty) a)
    | TailCallANF (AppANF  a)
    -- future thing will have | LetNFRec maybe?
    deriving (Ord,Ord1,Eq1,Read1,Show1,
      Functor,
      Foldable,
      Traversable,
      Typeable,
      Data,
      Eq,
      Read,
      Show)

