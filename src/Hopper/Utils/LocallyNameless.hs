{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | An adaptation of the locally nameless representation (See Charguéraud's
-- "The Locally Nameless Representation" for more information) allowing bound
-- global variables in addition to bound 2D de Bruijn variables.

module Hopper.Utils.LocallyNameless
  ( Depth(..),depthLevel
  , Slot(..),slotIndex
  , GlobalSymbol(..),gsText
  , Bound(..),localDepth,localSlot,globalSymbol
  , Variable(..),boundVar,freeName
  , HasBound(..)
  )
  where

import Control.Lens
import Data.Word
import Data.Data
import GHC.Generics

import qualified Data.Text as T

-- NOTE: it could make sense to look into using bidirection pattern synonyms for
--       variables

-- TODO: add smart constructors, add least for creating a local var

--- | GlobalSymbol should correspond to the fully qualified name
--- of a reachable value that is induced UNIQUELY by a module's name and
--- set of dependencies and how it was built.
--- NB: this might be more subtle in the presence of linearity, but let's table
--- that for now
---
--- this may or may not actually need to just be a functory parameter in the
--- AST but let's keep it simple for now
newtype GlobalSymbol
  = GlobalSymbol { _gsText :: T.Text }
  deriving (Eq,Ord,Read,Show,Data,Typeable,Generic)

makeLenses ''GlobalSymbol

-- | The distance in binding levels between a variable and its binder. The
-- "first dimension" in our 2D de Bruijn scheme.
newtype Depth
  = Depth { _depthLevel :: Word32 }
  deriving (Eq,Show,Enum,Data,Ord,Read,Typeable,Generic)

makeLenses ''Depth

-- | A binder slot. The second dimension in our 2D de Bruijn scheme.
newtype Slot
  = Slot { _slotIndex :: Word32 }
  deriving (Eq,Show,Data,Ord,Read,Typeable,Generic)

makeLenses ''Slot

-- | 'Bound' is either a local env variable or a globally fixed symbol (think:
-- linkers and object code).
data Bound
  = Local  { _localDepth   :: {-# UNPACK #-} !Depth
           , _localSlot    :: {-# UNPACK #-} !Slot }
  | Global { _globalSymbol :: {-# UNPACK #-} !GlobalSymbol }
  deriving (Eq,Ord,Read,Show,Typeable,Data,Generic)

makeLenses ''Bound

-- | A locally nameless variable, which is either a bound variable, or a named
-- free variable.
data Variable
  = Bound { _boundVar :: Bound }
  | Atom  { _freeName :: T.Text }
  deriving (Eq,Ord,Show)

makeLenses ''Variable

class HasBound v where
  bound :: Traversal' v Bound

instance HasBound Bound    where bound = ($)
instance HasBound Variable where bound = boundVar
