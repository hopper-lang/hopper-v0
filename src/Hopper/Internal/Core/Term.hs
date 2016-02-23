{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}

module Hopper.Internal.Core.Term where

import Hopper.Internal.Core.Literal
-- import Hopper.Internal.Core.Type
import Data.Text (Text)
import Data.Data
import Bound
import Data.Word (Word64)
import Prelude.Extras
import Control.Monad
--import GHC.Generics (Generic)
-- import Data.Traversable --  (fmapDefault,foldMapDefault)

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
        !(Scope Text (Term) a)
  | Let !(Either Word64  [Text]) -- either the # of multiple RVs from the rhs,
                                  -- or the names for the values on the RHS
      --  this was the optional type annotation? (Maybe  () {-(Type ty,RigModel)-})
          !(Term  a)   -- rhs which may have multi verses
          (Scope (Either Word64 Text) Term  a) --  [Scope Int Term a] (Scope Int Term a)
  deriving (Show1,Read1,Ord1,Eq1,Ord,Eq,Show,Read,Functor,Foldable,Typeable,Traversable)


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
  Lam t  e    >>= f = Lam t (e >>>= f)
  Let mname {-mtype-} bs  b >>= f = Let mname {-mtype-} (  bs >>= f)  (b >>>= f)

-- Smart constructors

type DummyType = Int

abstract' :: (Eq b, Monad f) => [b] -> f b -> Scope b f b
abstract' vs b = abstract (\v' -> if v' `elem` vs
                                    then Just v'
                                    else Nothing)
                          b

lam :: [Text] -> Term  Text -> Term  Text
lam vs b = Lam (zipWith (\v _n -> (v{-, TVar n, Omega-})) vs [0 :: Word64 ..])
               (abstract' vs b)

-- | A smart constructor for Lam with one variable
--
-- >>> lam1 "y" (lam1 "x" (V "x" :@ [V "y"]))
-- Lam [("y",TVar 0,Omega)]
--     (Scope (Lam [("x",TVar 0,Omega)]
--            (Scope (V (B "x") :@ [V (F (V (B "y")))]))))
lam1 :: Text -> Term  Text -> Term  Text
lam1 v b = lam [v] b

let_ :: Text -> Term  Text -> Term  Text -> Term  Text
let_ v rhs bod = Let (Right [ v])
                     {-(Just (TVar 0, Omega))-}
                     rhs
                     (abstract (\var -> if var == v
                                        then Just (Right v)
                                        else Nothing)
                               bod)

callPrim :: (Either Text GmpMathOpId) -> [Term  a] -> Term  a
callPrim (Left name) = PrimApp  (PrimopIdGeneral name)
callPrim (Right gmpid) = PrimApp (TotalMapthOpGmp gmpid)

infixr 0 !
(!) :: Text -> Term  Text -> Term  Text
(!) = lam1

-- let_ "False" ("f" ! "t" ! V"f") (V "False")
-- let_ "True" ("f" ! "t" ! V"t") (V "True")
-- let_ "if" ("b" ! "t" ! "f" ! V"b" :@ [V"f"] :@ [V"t"]) (V "if")
-- let_ "Zero" ("z" ! "s" ! V"z") (V "Zero")
-- let_ "Succ" ("n" ! "z" ! "s" ! V"s" :@ [V"n"]) (V "Succ")
-- let_ "Zero" ("z" ! "s" ! V"z") $
--             let_ "Succ" ("n" ! "z" ! "s" ! V"s" :@ [V"n"]) $
--                         let_ "one" (V"Succ" :@ [V"Zero"]) $
--                                    V "one"
