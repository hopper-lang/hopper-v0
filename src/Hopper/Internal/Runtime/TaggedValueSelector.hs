{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FunctionalDependencies, ScopedTypeVariables #-}

module Hopper.Internal.Runtime.TaggedValueSelector where


import  Hopper.Internal.Core.Literal (Literal,ConstrId)
import qualified Data.Vector as V

import Control.Lens.Prism(Prism')
import Control.Lens.Fold(preview)
import Control.Lens.Review(review,AReview)
import qualified Control.Lens.Getter
import qualified Data.Monoid
{-
not sure about this data model, but trying it out to see what happens
though will likely move away from this pretty quickly
-}
data LiteralF a = LitF Literal
data ConstructorF a = ConstructorF ConstrId (V.Vector (RefOf a))
data ClosureF a = ClosureF (V.Vector (RefOf a)) (ClosureCodeOf a)
data ThunkF a = ThunkF (V.Vector (RefOf a)) (ThunkCodeOf a)
data BlackHoleF a = BlackHoleF
data IndirectionF a = IndirectionF (RefOf a)
--type family EnvOf (closureLike :: *) :: *
type family NeutralOf v :: *
type family RefOf (a :: *) :: *

{-
should these perhaps be the same?
not sure. At some point thunks and no arg closures have the same runtime rep,
just different sharing/update machinery. should that leak into the code pointer model???
-}
type family ClosureCodeOf (a :: *) :: *
type family ThunkCodeOf ( a :: * ) :: *


{-# INLINE get #-}
get :: forall a s.
  Control.Lens.Getter.Getting (Data.Monoid.First a) s a
               -> s -> Maybe a
get s v = preview s v

set :: forall t b. AReview t b -> b -> t
set s v = review s v

class TaggedHeapValue v   where
  asLit :: Prism' v  (LiteralF v)
  asConstructor ::Prism'  v   (ConstructorF v)
  asClosure :: Prism' v    (ClosureF v)
  asThunk :: Prism'  v   (ConstructorF v)
  asBlackHole ::  Prism' v  (ConstructorF v)


