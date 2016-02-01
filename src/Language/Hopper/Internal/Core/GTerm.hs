{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

{-# LANGUAGE TypeOperators #-}

module Language.Hopper.Internal.Core.GTerm where


import Data.Functor.Identity
import Data.Text
import qualified Bound.Scope as P
import Bound.Var
import GHC.Generics
import Data.Data

data PrimOpId = PID Int
  deriving(Read,Eq,Show,Ord,Data,Typeable,Generic)

data ConId = ConId !Text
  deriving(Read,Eq,Show,Ord,Data,Typeable,Generic)
data GLetHL rhsg bodf a = GLet (Maybe Text) (rhsg a) (P.Scope (Maybe Text) bodf a )
    deriving(Typeable,Functor,Foldable,Traversable)
  -- deriving(Read,Eq,Show,Ord,Data,Typeable,Generic)

data GLetANF rhsg bodf a = GLetANF (Maybe Text) (rhsg a) (bodf   (Var (Maybe Text) a) )
  deriving(Typeable,Functor,Foldable,Traversable)
-- deriving instance (Data (bodf a), Data (rhsg a)) => Data (GLetANF   rhsg bodf a )

data GCompHL f a = GApp (f a) [f a]
                | GPrimApp PrimOpId  [f a]
                | GReturn (f a) -- this maybe should move somewhere else?
                | GSeqThunk (f a) (f a)
  deriving(Read,Eq,Show,Ord,Data,Typeable,Generic,Functor,Foldable,Traversable)




data GAllocEnvCaptureHL f a = GHLLambdaHL [Text] !(P.Scope Text f a) | Delay !(f a)
  deriving(Typeable,Functor,Foldable,Traversable,Eq,Show,Ord,Typeable,Generic)
  -- deriving(Read,Eq,Show,Ord,Data,Typeable,Generic)


data GAllocEnvCaptureANF f a = GHLLambdaANF [Text] !(f  (Var Text  a)) | DelayANF !(f a)
    deriving(Typeable,Functor,Foldable,Traversable,Typeable,Generic)
  -- deriving(Read,Eq,Show,Ord,Data,Typeable,Generic)



data GAllocFirstOrder f a = ConstrApp !ConId ![f a] | GLitInt !Integer
  deriving(Read,Eq,Show,Ord,Data,Typeable,Generic,Functor,Foldable,Traversable)


data GValue f g a = GVFunc !(GAllocEnvCaptureHL f a) | GV !(GAllocFirstOrder g a)
    deriving(Typeable,Functor,Foldable,Traversable)
-- data Literal a = LitInt Int


data Exp a  = ExpLet (GLetHL Exp Exp a)
              | ExpComp (GCompHL Exp a) |  ExpLit (GValue Exp Exp a)
    deriving(Typeable,Functor,Foldable,Traversable)

data ANF a = ANFLetCall (GLetANF (GCompHL Identity) ANF a) | ANFLetAlloc !(GLetANF (GValue ANF Identity) ANF  a)
            |  ANFTailCall (GCompHL Identity a)
            deriving(Typeable,Functor,Foldable,Traversable)


-- exp2anfG :: Ord a => Exp a -> ANF a
-- exp2anfG (ExpLit (GV (GLitInt int))) = ANFLetAlloc (GLetANF Nothing (GV (GLitInt int)) (ANFTailCall (GReturn $ Identity $ (B Nothing))))
-- exp2anfG (ExpLit (GV ()
-- newtype ANF a = ANF (
--       ((GLet (GComp Identity `Coproduct` Literal)
--                   ANF) `Coproduct`
--       (GComp Identity)
--                    ) a
--     )
