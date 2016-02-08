{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}

module Language.Hopper.Internal.Core.Term where

import Language.Hopper.Internal.Core.Literal
-- import Language.Hopper.Internal.Core.Type
import Data.Text (Text)
import Data.Data
import Bound
import Data.Word (Word64)
import Prelude.Extras
import Control.Monad
import GHC.Generics (Generic)
-- import Data.Traversable --  (fmapDefault,foldMapDefault)

data Exp a
  = V  !a
  | ELit !Literal
  | Return ![Exp a ] -- explicit multiple return values
  | EnterThunk !(Exp a) -- because we're in a strict IR rep,
                        -- we dont need to provide a seq like operation
                          -- seq a b === let _ := enterThunk a in b

  | Delay !(Exp a)  --- Delay is a Noop on Thunked values, otherwise creates a thunk
  --                     --- note: may need to change their semantics later?!
  | App !(Exp  a)  ![Exp  a]
  | PrimApp  !PrimOpId ![Exp  a] -- not sure if this is needed, but lets go with it for now

  | Lam ![(Text{-,Type ty,RigModel-})]
        !(Scope Text (Exp) a)
  | Let !(Either Word64  [Text]) -- either the # of multiple RVs from the rhs,
                                  -- or the names for the values on the RHS
      --  this was the optional type annotation? (Maybe  () {-(Type ty,RigModel)-})
          !(Exp  a)   -- rhs which may have multi verses
          (Scope (Either Word64 Text) Exp  a) --  [Scope Int Exp a] (Scope Int Exp a)
  deriving (Show1,Read1,Ord1,Eq1,Ord,Eq,Show,Read,Functor,Foldable,Typeable,Data,Generic,Traversable)


-- instance Functor (Exp ty)  where fmap       = fmapDefault

-- instance Foldable (Exp ty) where foldMap    = foldMapDefault

instance Applicative (Exp ) where
  pure  = V
  (<*>) = ap

-- instance Traversable (Exp ty) where
--   traverse f (V a)      = V <$> f a
--   traverse _f (ELit e) = pure $ ELit e
--   -- traverse f (PrimApp nm ls) = PrimApp nm <$> traverse f ls
--   traverse f (Force e) = Force <$> traverse f e
--   traverse f (Delay e) = Delay <$> traverse f e
--   traverse f (PrimApp nm args) = PrimApp nm <$> traverse (traverse f) args
--   traverse f (x :@ ys)   = (:@) <$> traverse f x <*> traverse (traverse f) ys
--   traverse f (Lam t e)    = Lam  t <$> traverse f e
--   traverse f (Let mname mtype  bs b) = Let  mname mtype <$>  (traverse f) bs <*> traverse f b


instance Monad (Exp ) where
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

lam :: [Text] -> Exp  Text -> Exp  Text
lam vs b = Lam (zipWith (\v _n -> (v{-, TVar n, Omega-})) vs [0 :: Word64 ..])
               (abstract' vs b)

-- | A smart constructor for Lam with one variable
--
-- >>> lam1 "y" (lam1 "x" (V "x" :@ [V "y"]))
-- Lam [("y",TVar 0,Omega)]
--     (Scope (Lam [("x",TVar 0,Omega)]
--            (Scope (V (B "x") :@ [V (F (V (B "y")))]))))
lam1 :: Text -> Exp  Text -> Exp  Text
lam1 v b = lam [v] b

let_ :: Text -> Exp  Text -> Exp  Text -> Exp  Text
let_ v rhs bod = Let (Right [ v])
                     {-(Just (TVar 0, Omega))-}
                     rhs
                     (abstract (\var -> if var == v
                                        then Just (Right v)
                                        else Nothing)
                               bod)

callPrim :: Text -> [Exp  a] -> Exp  a
callPrim name = PrimApp (PrimopId name)

infixr 0 !
(!) :: Text -> Exp  Text -> Exp  Text
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
