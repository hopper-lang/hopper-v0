{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}



module Hopper.Utils.LocallyNameless(
  BinderSlot(..)
  ,GlobalSymbol(..)
  ,LocalNamelessVar(..)
  ,Variable(..)
  ) where


import Data.Word
import Data.Data
import GHC.Generics
import qualified Data.Text as T (Text )

--- | GlobalSymbol should correspond to the fully qualified name
--- of a reachable value that is induced UNIQUELY by a module's name and
--- set of dependencies and how it was built.
--- NB: this might be more subtle in the presence of linearity, but lets table that for now
---
--- this may or may not  actually need to just be a functory parametery in the AST
--- but lets keep it simple fo rnow
newtype GlobalSymbol = GlobalSymbol T.Text
  deriving (Eq,Ord,Read,Show,Data,Typeable,Generic)


newtype BinderSlot =
    BinderSlot { unBinderSlot :: Word32 }
  deriving (Eq, Show,Data,Ord,Read,Typeable,Generic)

data LocalNamelessVar =
   LocalNamelessVar
          {localBinderDepth :: {-# UNPACK #-}  !Word32
           ,localBinderArg :: {-# UNPACK #-}   !BinderSlot
         }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic )

-- | VariableCC is either a local env variable or a globally fixed symbol (think like linkers and object code)
-- TODO: later lowering passes will induce register / stack placements and
-- veer into forcing specification of caller/callee saving conventions on code control tranfers
data Variable  =
    LocalVar {-# UNPACK #-} !LocalNamelessVar
    | GlobalVarSym {-# UNPACK #-}  !GlobalSymbol
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic )

