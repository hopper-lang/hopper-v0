
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}

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

--import  Control.Monad.Free

--import Language.Hopper.Internal.Core.ANF
import Language.Hopper.Internal.Core.Literal



-- | current theres no pointer tagging in 'Ref' but eventually that will
-- probably change
newtype Ref = Ref {refPointer :: Word64} deriving  (Eq,Read,Show,Ord,Data,Typeable,Generic)


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
newtype Tag = Tag { unTag :: Text {-Word64-} } deriving (Eq,Read, Show,Ord,Data,Typeable,Generic)

-- type ValRec  ty   = Free (ValueF  ty Ref) Ref


type HeapVal ast     =  ValueF ast  Ref --  ValueF ty Ref (ValRec ty)

data ValueF ast   v =    VLitF !Literal
              | ConstructorF  !Tag  (WrappedVector v)
              | ThunkF (ast   v )
              --  should this be a heap ref to
              -- closure to have the right sharing ?
              | DirectClosureF (Closure ast  v) -- heap ref?
              | BlackHoleF
              | IndirectionF v
              --- in the types are calling conventions paper,
              --- indirections can point at pointer sized literals, or heap references (or tuples thereof???)

              -- | VRefF !Ref --- refs are so we can have  exlpicit  sharing
                        --- in a manner thats parametric in the choice
                        -- of execution  semantics
   deriving
     (Typeable
      ,Functor
      ,Foldable
      ,Traversable
      ,Generic
      --,Data
      ,Eq
      ,Ord
      ,Show
      ,Read
      --,Eq1
      --,Ord1
      --,Show1
      --,Read1
      )
deriving instance (Data a,Data (ast a),Monad ast,Data (ast (Var Text (ast a))),  Typeable ast,Typeable a)
  =>  Data (ValueF ast a )

instance (Eq1 ast,Monad ast) => Eq1 (ValueF ast) where
    (==#)  (VLitF a) (VLitF b) =  a == b
    (==#)  (VLitF _) _ =  False
    (==#)  (ConstructorF tga va) (ConstructorF tgb vb) =   tga == tgb && va == vb
    (==#)  (ConstructorF _ _) _ =  False
    (==#)  (ThunkF a) (ThunkF b) =  a ==# b
    (==#)  (ThunkF _) _ =  False
    (==#)  (DirectClosureF c1) (DirectClosureF c2) = c1 ==# c2
    (==#)  (DirectClosureF _ ) _ = False
    (==#)  BlackHoleF BlackHoleF = True
    (==#)  BlackHoleF _ =  False
    (==#) (IndirectionF v) (IndirectionF v2) = v == v2
    (==#) (IndirectionF _) _ = False

-- this is a trick to make defining the ord1 instance sane but total
codeValueF :: ValueF a b -> Int
codeValueF (VLitF _) = 1
codeValueF (ConstructorF _ _ ) = 2
codeValueF (ThunkF _) = 3
codeValueF (DirectClosureF _) = 4
codeValueF (BlackHoleF) = 5
codeValueF (IndirectionF _) = 6

instance (Ord1 ast,Monad ast) => Ord1 (ValueF ast) where
  compare1 (VLitF a) (VLitF b) = compare a b
  compare1 a@(VLitF _) b = compare  (codeValueF a) (codeValueF b)
  compare1 (ConstructorF ta va) (ConstructorF tb vb) =
        let tcomp = compare ta tb in  if tcomp == EQ then compare va vb else tcomp
  compare1 a@(ConstructorF _ _) b = compare (codeValueF a) (codeValueF b)
  compare1 (ThunkF e1) (ThunkF e2) = compare1 e1 e2
  compare1 a@(ThunkF _) b = compare (codeValueF a) (codeValueF b)
  compare1 (DirectClosureF a) (DirectClosureF b) = compare1 a b
  compare1 a@(DirectClosureF _) b = compare (codeValueF a) (codeValueF b)
  compare1 BlackHoleF BlackHoleF = EQ
  compare1 a@(BlackHoleF) b = compare (codeValueF a) (codeValueF b)
  compare1 (IndirectionF a) (IndirectionF b) = compare a b  --- this is spiritually evil :))))
  compare1 a@(IndirectionF _ ) b = compare (codeValueF a) (codeValueF b)

--- there will NOT be a read1 or show1 in this style


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
--- they're kinda the erasure of a lambda ... for now
data Closure ast   a = MkClosure ![Arity] !(Scope Text ast a)
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable,Generic,Typeable)
deriving instance (Typeable ast,Typeable a,Data (Scope Text ast  a))=> Data (Closure ast   a)
instance (Monad ast, Eq1 ast) => Eq1 (Closure ast)
instance (Monad ast, Ord1 ast) => Ord1 (Closure ast)
instance (Monad ast, Read1 ast) => Read1 (Closure ast)
instance (Monad ast, Show1 ast) => Show1 (Closure ast)
