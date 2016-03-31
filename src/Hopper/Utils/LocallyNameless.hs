{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}



module Hopper.Utils.LocallyNameless
  ( BinderSlot(..),slotIndex
  , GlobalSymbol(..),gsText
  , LocalNamelessVar(..),lnDepth,lnSlot
  , Variable(..),localNameless,globalSymbol
  ) where

import Control.Lens
import Data.Word
import Data.Data
import GHC.Generics
import qualified Data.Text as T (Text )

--- | GlobalSymbol should correspond to the fully qualified name
--- of a reachable value that is induced UNIQUELY by a module's name and
--- set of dependencies and how it was built.
--- NB: this might be more subtle in the presence of linearity, but let's table
--- that for now
---
--- this may or may not actually need to just be a functory parametery in the
--- AST but let's keep it simple for now
newtype GlobalSymbol
  = GlobalSymbol { _gsText :: T.Text }
  deriving (Eq,Ord,Read,Show,Data,Typeable,Generic)

makeLenses ''GlobalSymbol

newtype BinderSlot
  = BinderSlot { _slotIndex :: Word32 }
  deriving (Eq,Show,Data,Ord,Read,Typeable,Generic)

makeLenses ''BinderSlot

-- instance Enum BinderSlot where
--   toEnum = BinderSlot . toEnum
--   fromEnum = fromEnum . unBinderSlot

data LocalNamelessVar
  = LocalNamelessVar { _lnDepth :: {-# UNPACK #-} !Word32
                     , _lnSlot  :: {-# UNPACK #-} !BinderSlot }
  deriving (Eq,Ord,Read,Show,Typeable,Data,Generic)

makeLenses ''LocalNamelessVar

-- | VariableCC is either a local env variable or a globally fixed symbol (think like linkers and object code)
-- TODO: later lowering passes will induce register / stack placements and
-- veer into forcing specification of caller/callee saving conventions on code control tranfers
data Variable
  = LocalVar     { _localNameless :: {-# UNPACK #-} !LocalNamelessVar }
  | GlobalVarSym { _globalSymbol  :: {-# UNPACK #-} !GlobalSymbol }
  deriving (Eq,Ord,Read,Show,Typeable,Data,Generic)

makeLenses ''Variable
