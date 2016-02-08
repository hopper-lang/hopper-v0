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
import Numeric.Natural




--- data ExpContext  ty a  = SCEmpty
--                         | LetContext
--                             (Maybe Text) -- we're not currently using / needing the variable name here
--                             (Scope (Maybe Text) (Exp ) a)
--                             (ExpContext ty a)
--                         | ThunkUpdate !a (ExpContext ty a)
--                         | FunAppCtxt  [Ref] [Exp ty a] (ExpContext  ty a)
--                           -- lets just treat the ref list as having the function ref at the
--                           -- "bottom of the stack", when [Exp] is empty, reverse ref list to resolve function and apply args
--                         | PrimAppCtxt  PrimOpId [Ref] [Exp ty a] (ExpContext  ty a)

--                         -- applications are their one hole contexts!
--    deriving (Typeable,Functor,Foldable,Traversable,Generic,Data,Eq,Ord,Show)


-- data InterpreterError
--   = PrimopTypeMismatch
--   | NonClosureInApplicationPosition
--   | ArityMismatchFailure
--   | HeapLookupFailure
--   | MalformedClosure
--   | MismatchedStackContext
--   | PrimFailure String
--   | UnsupportedTermConstructFailure String
--   deriving (Eq,Ord,Show,Typeable,Data)


data AppANF  a
    = EnterThunk !a --
    | FunApp !a ![a]
    | PrimApp  !a !Text ![a]
        deriving ( Ord,Functor,Ord1,Show1,Eq1,Read1,Foldable,Traversable,Typeable,Data,Eq,Read,Show)

data AnfAlloc a
  = SharedLiteral !Literal -- we currently do not have any fixed size literal types
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
     deriving (Ord,Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,Typeable,Data,Eq,Read,Show)



data AnfRHS  {-ty-} a
    = AnfAllocRHS !(AnfAlloc a) -- only heap allocates, no control flow
    | NonTailCallApp  (AppANF  a) -- control stack allocation; possibly heap allocation

   deriving (Ord,Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,Typeable,Data,Eq,Read,Show)



data ANF  a
    = ReturnNF  !a -- !(Atom ty a)
    | LetNF --  (Maybe Text) {-(Maybe(Type ty, RigModel)) -} (AnfRHS  a)
          ![(Either Natural Text, AnfRHS a)]
          -- this list of "independent" simultaneous let bindings must always be nonempty
          -- this is NOT a let rec construct and doesn't provide mutual recursion
          -- this is provided as an artifact of simplifying the term 2 anf translation
          !(ANF (Var (Either Natural Text) a)) -- (Simple.Scope (Maybe Text) (ANF ) a)
    -- | LetNFMulti ![AnfRHS ty a] !(Scope Word64 (ANF ty) a)
    | TailCallANF (AppANF  a)
    -- future thing will have | LetNFRec maybe?
    deriving (Ord,Ord1,Eq1,Read1,Show1,Functor,Foldable,Traversable,Typeable,Data,Eq,Read,Show)

