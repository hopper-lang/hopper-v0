{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
module Language.Hopper.Internal.Core.EvalTerm where

import Bound

import Language.Hopper.Internal.Core.Term
import Language.Hopper.Internal.Core.Value
import Language.Hopper.Internal.Core.Literal
-- import qualified Data.Map as Map
import GHC.Generics
-- import Numeric.Natural
import Data.Text (Text)
import Data.Typeable
import Data.Data


data ExpContext  ty a  = SCEmpty
                        | LetContext
                            (Scope (Maybe Text) (Exp ty) a)
                            (ExpContext ty a)
                        | ThunkUpdate !a (ExpContext ty a)
                        | FunAppCtxt  [Ref] [Exp ty a] (ExpContext  ty a)
                          -- lets just treat the ref list as having the function ref at the
                          -- "bottom of the stack", when [Exp] is empty, reverse ref list to resolve function and apply args
                        | PrimAppCtxt  PrimOpId [Ref] [Exp ty a] (ExpContext  ty a)

                        -- applications are their one hole contexts!

   deriving (Typeable
          ,Functor
          ,Foldable
          ,Traversable
          ,Generic
          ,Data
          ,Eq
          ,Ord
          ,Show)
