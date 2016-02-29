{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Hopper.Internal.Core.Term where

import Hopper.Internal.Core.Literal
-- import Hopper.Internal.Core.Type
import Data.Text (Text)
import Data.Data
--import Bound
import Data.Bifunctor
import Data.Word (Word64)
--import Prelude.Extras
import Control.Monad
import GHC.Generics (Generic)
--import Data.Traversable --  (fmapDefault,foldMapDefault)

newtype Scope b {-(f :: * -> *)-} a
  = Scope {unscope :: Term (Var b (Term a))}
  deriving ({-Show1,Read1,Ord1,Eq1,-}Ord,Eq,Generic,Show,Read,Functor,Foldable,Typeable,Traversable)
instance Bifunctor Scope  where
  bimap f g  (Scope tm) = Scope $ fmap (bimap f (fmap g)) tm


data Var b a = B b | F a
  deriving ({-Show1,Read1,Ord1,Eq1,-}Ord,Eq,Data,Generic,Show,Read,Functor,Foldable,Typeable,Traversable)
instance Bifunctor Var where
  {-# INLINE bimap #-}
  bimap = \ f g  v-> case v of B bv -> B $ f bv ; F fv -> F $ g fv

abstract ::  (a -> Maybe b) -> Term a -> Scope b  a
abstract f e = Scope (liftM k e) where
  k y = case f y of
    Just z  -> B z
    Nothing -> F (return y)
instantiate ::  (b -> Term a) -> Scope b  a -> Term a
instantiate k e = unscope e >>= \v -> case v of
  B b -> k b
  F a -> a


gbind ::  (a -> Term c) -> Scope b a  -> Scope b c
gbind f (Scope tm) = Scope $ fmap (fmap (>>= f))  tm

{-

class Bound (t :: (* -> *) -> * -> *) where
  (>>>=) :: Monad f => t f a -> (a -> f c) -> t f c
    Scope b a -> (a -> Term c) -> Scope b c
    uses bind :: Term a -> (a -> Term C) -> Term c
    so can do

-- >>> :m + Data.List
-- >>> abstract (`elemIndex` "bar") "barry"
-- Scope [B 0,B 1,B 2,B 2,F "y"]
abstract :: Monad f => (a -> Maybe b) -> f a -> Scope b f a
abstract f e = Scope (liftM k e) where
  k y = case f y of
    Just z  -> B z
    Nothing -> F (return y)
{-# INLINE abstract #-}



-- | Enter a scope, instantiating all bound variables
--
-- >>> :m + Data.List
-- >>> instantiate (\x -> [toEnum (97 + x)]) $ abstract (`elemIndex` "bar") "barry"
-- "abccy"
instantiate :: Monad f => (b -> f a) -> Scope b f a -> f a
instantiate k e = unscope e >>= \v -> case v of
  B b -> k b
  F a -> a
{-# INLINE instantiate #-}

-- | Enter a 'Scope' that binds one variable, instantiating it
--
-- >>> instantiate1 "x" $ Scope [B (),F "y",F "z"]
-- "xyz"
instantiate1 :: Monad f => f a -> Scope n f a -> f a
instantiate1 e = instantiate (const e)
{-# INLINE instantiate1 #-}


-}

data Term a
  = V  !a
  | ELit !Literal
  | Return ![ Term a ] -- explicit multiple return values
                      -- should V x be replaced by Return [x] ?
                      --  once we lower to ANF
                      -- NOTE: for valid expressions,
  | EnterThunk !(Term a) -- because we're in a strict IR rep,
                        -- we dont need to provide a seq like operation
                          -- seq a b === let _ := enterThunk a in b

  | Delay !(Term a)  --- Delay is a Noop on Thunked values, otherwise creates a Thunked
                    --- note: may need to change their semantics later?!
                    --- Q: is it valid to thunk a thunked value? (no?)
  | App !(Term  a)  ![Term  a]  --this is not curried :)
  | PrimApp  !PrimOpId --
             ![Term  a] -- not sure if this is needed, but lets go with it for now

  | Lam ![(Text{-,Type ty,RigModel-})]
        !(Scope Text  a)
  | Let !(Either Word64  [Text]) -- either the # of multiple RVs from the rhs,
                                  -- or the names for the values on the RHS
      --  this was the optional type annotation? (Maybe  () {-(Type ty,RigModel)-})
          !(Term  a)   -- rhs which may have multi verses
          (Scope (Either Word64 Text)   a) --  [Scope Int Term a] (Scope Int Term a)
  deriving ({-Show1,Read1,Ord1,Eq1,-}Ord,Eq,Show,Read,Functor,Foldable,Typeable,Traversable)


-- instance Functor (Term ty)  where fmap       = fmapDefault

-- instance Foldable (Term ty) where foldMap    = foldMapDefault

instance Applicative (Term ) where
  pure  = V
  (<*>) = ap

-- instance Traversable (Term ty) where
--   traverse f (V a)      = V <$> f a
--   traverse _f (ELit e) = pure $ ELit e
--   -- traverse f (PrimApp nm ls) = PrimApp nm <$> traverse f ls
--   traverse f (Force e) = Force <$> traverse f e
--   traverse f (Delay e) = Delay <$> traverse f e
--   traverse f (PrimApp nm args) = PrimApp nm <$> traverse (traverse f) args
--   traverse f (x :@ ys)   = (:@) <$> traverse f x <*> traverse (traverse f) ys
--   traverse f (Lam t e)    = Lam  t <$> traverse f e
--   traverse f (Let mname mtype  bs b) = Let  mname mtype <$>  (traverse f) bs <*> traverse f b


instance Monad (Term ) where
  return = V
  V a         >>= f = f a
  (Return ls) >>= f =    Return (map (>>= f) ls )
  -- PrimApp nm ls >>= f = PrimApp nm (map f ls)
  Delay e     >>= f = Delay $ e >>= f
  EnterThunk thnk     >>= f =  EnterThunk (thnk >>= f)
  ELit e      >>= _f = ELit e -- this could also safely be a coerce?
  (App x y)    >>= f = App (x >>= f)  (map (>>= f)  y )
  (PrimApp name args) >>= f = PrimApp name (map (>>= f) args )
  Lam t  e    >>= f =   Lam t (gbind f e)
  Let mname {-mtype-} bs  b >>= f = Let mname {-mtype-} (  bs >>= f)  (gbind f b)




callPrim :: (Either Text GmpMathOpId) -> [Term  a] -> Term  a
callPrim (Left name) = PrimApp  (PrimopIdGeneral name)
callPrim (Right gmpid) = PrimApp (TotalMapthOpGmp gmpid)

