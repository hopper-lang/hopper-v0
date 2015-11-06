
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Hopper.Internal.Core.Value where

import Bound
--import Numeric.Natural
import Prelude.Extras
-- import Control.Applicative
--import Control.Monad
--import qualified  Data.Set as Set
--import qualified  Data.Map.Strict as Map
--import Data.Foldable (foldl')
--import Data.Traversable
import Data.Text (Text)
import Data.Data
import qualified Data.Vector as V
import Data.Word
--import Data.Int
import GHC.Generics (Generic)
--import Control.Lens
-- import qualified  Data.Bits as Bits
-- import  Control.Monad.Trans.State.Strict (StateT(..))
--import qualified Control.Monad.Trans.State.Strict as State

import  Control.Monad.Free

import Language.Hopper.Internal.Core.ANF
import Language.Hopper.Internal.Core.Literal



-- | current theres no pointer tagging in 'Ref' but eventually that will
-- probably change
newtype Ref = Ref {refPointer :: Word64} deriving  (Eq, Show,Ord,Data,Typeable,Generic)


instance Bounded Ref where
   minBound = Ref minBound
   maxBound = Ref maxBound

-- | interface for doing queries on bitwise representation and inspecting it
-- this could eg be used to query the upper 16 bits if we were to use a pointer
-- tagging scheme or the like. No such tagging scheme for now though :)
refRepLens :: Functor f =>(Word64 -> f a) -> Ref -> f a
refRepLens = \ f (Ref r) -> f r

-- | interface for doing bitwise transformations that yield a new ref
refTransform :: Functor f => (Word64 -> f Word64) -> Ref -> f Ref
refTransform = \ f (Ref r) -> Ref <$> f r

absoluteDistance  :: Ref -> Ref -> Word64
absoluteDistance = \(Ref a) (Ref b) -> if a > b then a - b else b - a

instance Enum Ref where
  succ rf@(Ref w) | rf < maxBound = Ref (1+ w)
                  | otherwise = error $ "succ: Ref overflow"
  pred rf@(Ref w) | rf > minBound = Ref (w - 1)
                  | otherwise = error $ "pred: Ref underflow"
  fromEnum (Ref w)
                | w < fromIntegral (maxBound :: Int) = fromIntegral w
                | otherwise =
                          error "fromEnum: any Ref that is larger than 2^63 -1  is unrepresentable as Int64"
  toEnum n | n >= 0 = Ref $ fromIntegral n
           | otherwise = error "toEnum: Cant represent negative locations in a Ref"




-- | 'Tag' is a constructor tag sum
newtype Tag = Tag { unTag :: Word64 } deriving (Eq,Read, Show,Ord,Data,Typeable,Generic)

type ValRec  ty   = Free (ValueF  ty) Ref


type HeapVal ty   = ValueF ty  (ValRec ty)

data ValueF ty  v =    VLitF !Literal
              | ConstructorF  !Tag  !(WrappedVector v)
              | ThunkF !(ANF  ty v )
              | PartialAppF ![Arity] -- ^ args left to consume?
                           ![v  ]  -- ^  this will need to be reversed??
                           !(Closure  ty  v {- (Value ty con v) -})
              | DirectClosureF !(Closure ty  v)
              | BlackHoleF

              -- | VRefF !Ref --- refs are so we can have  exlpicit  sharing
                        --- in a manner thats parametric in the choice
                        -- of execution  semantics
   deriving
     (Typeable
      ,Functor
      ,Foldable
      ,Traversable
      ,Generic
      ,Data
      ,Eq
      ,Ord
      ,Show
      ,Read
      ,Eq1
      ,Ord1
      ,Show1
      ,Read1
      )

newtype WrappedVector a = WrappedVector { unWrappedVector :: V.Vector a }
  deriving (Eq, Show,Ord,Read,Data,Typeable,Functor,Foldable,Traversable)
instance Show1 WrappedVector
instance Eq1 WrappedVector
instance Ord1 WrappedVector
instance Read1 WrappedVector

data Arity = ArityBoxed {_extractArityInfo :: !Text} --- for now our model of arity is boring and simple
                              -- for now lets keep the variable names?
                              -- it'll keep the debugging simpler (maybe?)
 deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)

--- | 'Closure' may need some rethinking ... later
data Closure  ty  a = MkClosure ![Arity] !(Scope Text (ANF ty) a)
  deriving (Eq,Ord,Show,Read,Ord1,Eq1,Show1,Read1,Functor,Foldable,Traversable,Data,Generic)

