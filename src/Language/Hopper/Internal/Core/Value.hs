
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
import Prelude.Extras
import Data.Text (Text)
import Data.Data
import GHC.Generics(Generic)
import qualified Data.Vector as V
import Language.Hopper.Internal.Core.Literal



-- | 'Tag' is a constructor tag sum
newtype Tag = Tag { unTag :: Text {-Word64-} } deriving (Data,Generic,Eq,Read, Show,Ord,Typeable)

-- type ValRec  ty   = Free (ValueF  ty Ref) Ref


--type HeapVal ast     =  ValueF ast  Ref --  ValueF ty Ref (ValRec ty)

data ValueF ast   v =    VLitF !Literal
              | ConstructorF  !Tag  !(WrappedVector v)
              | ThunkF !(ast   v )
              --  should this be a heap ref to
              -- closure to have the right sharing ?
              | DirectClosureF !(Closure ast  v) -- heap ref?
              | BlackHoleF
              | IndirectionF !v
              --- in the types are calling conventions paper,
              --- indirections can point at pointer sized literals, or heap references (or tuples thereof???)

              -- | VRefF !Ref --- refs are so we can have  exlpicit  sharing
                        --- in a manner thats parametric in the choice
                        -- of execution  semantics
   deriving
     (Generic,Typeable
      ,Functor
      ,Foldable
      ,Traversable

      --
      ,Eq
      ,Ord
      ,Show
      ,Read
      --,Eq1
      --,Ord1
      --,Show1
      --,Read1
      )


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
  deriving (Data,Generic,Eq, Show,Ord,Read,Typeable,Functor,Foldable,Traversable)
instance Show1 WrappedVector
instance Eq1 WrappedVector
instance Ord1 WrappedVector
instance Read1 WrappedVector

data Arity = ArityBoxed {_extractArityInfo :: !Text} --- for now our model of arity is boring and simple
                              -- for now lets keep the variable names?
                              -- it'll keep the debugging simpler (maybe?)
 deriving (Data,Generic,Eq,Ord,Show,Read,Typeable)

--- | 'Closure' may need some rethinking ... later
--- they're kinda the erasure of a lambda ... for now
data Closure ast   a = MkClosure ![Arity] !(Scope Text ast a)
  deriving (Generic,Eq,Ord,Show,Read,Functor,Foldable,Traversable,Typeable)
instance (Monad ast, Eq1 ast) => Eq1 (Closure ast)
instance (Monad ast, Ord1 ast) => Ord1 (Closure ast)
instance (Monad ast, Read1 ast) => Read1 (Closure ast)
instance (Monad ast, Show1 ast) => Show1 (Closure ast)
