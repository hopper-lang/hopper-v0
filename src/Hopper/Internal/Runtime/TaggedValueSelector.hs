

module Hopper.Internal.Runtime.TaggedValueSelector where

{-
this module provides the semi high level heap value tag checker /extractors




a literal selector might look something like


class LiteralSelector hval  neut  ref | hval -> neut ref where
  literalSelect :: forall s . hval -> STE HeapError s (Maybe (Either neut (LitF ref) ))

or a similar prim monad esque  design
-}
