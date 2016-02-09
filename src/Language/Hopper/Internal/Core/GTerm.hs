{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MagicHash, DataKinds, KindSignatures,GADTs, TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Language.Hopper.Internal.Core.GTerm where
{-
this module is for experiments in representation choices that are kept for retrospective
and learning value

approachs so

-}
import Numeric.Natural
import Data.Functor.Identity
import Data.Text
import qualified Bound.Scope as P
import Bound.Var
import GHC.Generics
import Data.Data
import GHC.TypeLits
--import GHC.Prim(Proxy#,proxy#)
import Data.Word (Word64)
--import Data.Proxy

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


data GExp a  = ExpLet (GLetHL GExp GExp a)
              | ExpComp (GCompHL GExp a) |  ExpLit (GValue GExp GExp a)
    deriving(Typeable,Functor,Foldable,Traversable)

data GANF a = ANFLetCall (GLetANF (GCompHL Identity) GANF a) | ANFLetAlloc !(GLetANF (GValue GANF Identity) GANF  a)
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

data SEither a b = SLeft !a | SRight !b
  deriving (Read,Eq,Show,Ord,Data,Typeable,Generic,Functor,Foldable,Traversable)
data HVar :: Nat  -> * -> * where
    FVar :: KnownNat depth => Proxy  depth -> a -> HVar depth a
    BVar :: KnownNat depth => Proxy  depth
        ->  !Natural {- natural should be at most Depth-} -> !(SEither Word64 Text)-> HVar depth a
    -- the BVars can be "half open"

data SExp :: Nat -> * -> * where
    SV :: HVar n a  -> SExp n a
    SLam ::  [(SEither Word64 Text)] -> (SExp (n+1) a) -> SExp n a
    SLet ::  [(SEither Word64 Text)] -> SExp n a -> (SExp (n+1) a) -> SExp n a
    --STreeSucc :: KnownNat m `=> Proxy m ->

--topLevel :: SExp 0 String
--topLevel = SLet [] (SV (FVar (Proxy   ) "lol")  )  (SV $ (BVar (Proxy   )  0   (SLeft 7))  )

