{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Hopper.Internal.Type.BinderInfo
  ( BinderInfo(..), Type
  ) where

import Hopper.Internal.Type.Relevance (Relevance)

import Data.Aeson
import Data.Data (Data)
import Data.Text (Text)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

type Type = () -- FIXME: use real types

data BinderInfo =
  BinderInfoData { relevanceBI :: Relevance
                 -- ^ if zero, during evaluation we need not pass around
                 --  BUT during NORMALIZATION, we probably do
                 --  so the normalizer WILL thread around irrelevant values
                 -- to properly support dependent type checking
                 -- as is proper, because a runtime irrelevant value
                 -- SHOULD be relevant during type checking, or
                 -- it has no reason to exist
                 , typeBICC :: Type
                 -- ^ at least for now, closure converted stuff may need a
                 -- slightly different type system fragment than the Core layer
                 -- Terms? NB: once we have existentials, should just be an
                 -- "equivalent" subset of the full type theory?
                 , sourceInfo :: Maybe Text
                 -- ^ TODO: flesh this out
                 }
  deriving (Eq,Ord,Read,Show,Typeable,Data,Generic)

instance ToJSON BinderInfo where
