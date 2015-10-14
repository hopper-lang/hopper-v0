{-# LANGUAGE GADTs, Rank2Types, KindSignatures, ScopedTypeVariables, TypeOperators, DataKinds, PolyKinds, MultiParamTypeClasses, FlexibleInstances, TypeFamilies, RecursiveDo, ExtendedDefaultRules #-}
{-
Higher order bound http://hpaste.org/73764 hpaste by kmett
-}

module Language.Hopper.HBound where

import Control.Applicative
import Control.Category
import Control.Comonad
import Control.Monad.Fix
import Control.Monad (ap)
import Data.Functor.Identity
import Data.Typeable
import Data.Monoid
import Data.Unique
import System.IO.Unsafe
import Unsafe.Coerce
import Prelude hiding ((.),id)

infixl 1 >>>-, >>-

type Nat f g = forall x. f x -> g x

class HFunctor t where
  hmap :: Nat f g -> Nat (t f) (t g)

class HFunctor t => HTraversable t where
  htraverse :: Applicative m => (forall x. f x -> m (g x)) -> t f a -> m (t g a)

class HFunctor t => HMonad t where
  hreturn :: Nat f (t f)
  (>>-)   :: t f a -> Nat f (t g) -> t g a

infixr 1 -<<
(-<<) :: HMonad t => Nat f (t g) -> Nat (t f) (t g)
f -<< m = m >>- f

class HBound s where
  (>>>-) :: HMonad t => s t f a -> Nat f (t g) -> s t g a

class HMonadTrans s where
  hlift :: HMonad t => Nat (t f) (s t f)

data Var b f a where
  B :: b a -> Var b f a
  F :: f a -> Var b f a

instance HFunctor (Var b) where
  hmap _ (B b) = B b
  hmap f (F a) = F (f a)

instance HTraversable (Var b) where
  htraverse _ (B b) = pure (B b)
  htraverse f (F a) = F <$> f a

instance HMonad (Var b) where
  hreturn   = F
  B b >>- _ = B b
  F a >>- f = f a

newtype Scope b t f a = Scope { unscope :: t (Var b (t f)) a }

instance HFunctor t => HFunctor (Scope b t) where
  hmap f (Scope b) = Scope (hmap (hmap (hmap f)) b)

instance HTraversable t => HTraversable (Scope b t) where
  htraverse f (Scope b) = Scope <$> htraverse (htraverse (htraverse f)) b

instance HMonad t => HMonad (Scope b t) where
  hreturn = Scope . hreturn . F . hreturn
  Scope e >>- f  = Scope $ e >>- \v -> case v of
    B b -> hreturn (B b)
    F ea -> ea >>- unscope . f

instance HMonadTrans (Scope b) where
  hlift = Scope . hreturn . F

instance HBound (Scope b) where
  Scope m >>>- f = Scope (hmap (hmap (>>- f)) m)

-- data Equal a b where
--    Refl :: Equal a a

-- instance Category Equal where
--   id = Refl
--   Refl . Refl = Refl

abstract :: HMonad t => (forall x. f x -> Maybe (b x)) -> Nat (t f) (Scope b t f)
abstract f = Scope . hmap (\y -> case f y of
  Just b -> B b
  Nothing -> F (hreturn y))

instantiate :: HMonad t => Nat b (t f) -> Nat (Scope b t f) (t f)
instantiate k (Scope e) = e >>- \v -> case v of
  B b -> k b
  F a -> a

data Ix :: [*] -> * -> * where
  Z :: Ix (a ': as) a
  S :: Ix as b -> Ix (a ': as) b

data Vec :: (* -> *) -> [*] -> * where
  HNil :: Vec f '[]
  (:::) :: f b -> Vec f bs -> Vec f (b ': bs)

infixr 5 :++, :::

type family (:++) (as :: [*]) (bs :: [*]) :: [*]
type instance '[] :++ bs = bs
type instance (a ': as) :++ bs = a ': (as :++ bs)

happend :: Vec f as -> Vec f bs -> Vec f (as :++ bs)
happend HNil bs = bs
happend (a ::: as) bs = a ::: happend as bs

hsingleton :: f a -> Vec f '[a]
hsingleton x = x ::: HNil

instance HFunctor Vec where
  hmap _ HNil = HNil
  hmap f (x ::: xs) = f x ::: hmap f xs

instance HTraversable Vec where
  htraverse _ HNil = pure HNil
  htraverse f (x ::: xs) = (:::) <$> f x <*> htraverse f xs

class EqF f where
  (==?) :: f a -> f b -> Maybe ( a :~: b)

data Lit t where
  Integer :: Integer -> Lit Integer
  Double  :: Double -> Lit Double
  String :: String -> Lit String

value :: Lit a -> a
value (Integer i) = i
value (Double d) = d
value (String s) = s

class Literal a where
  literal :: a -> Lit a

instance Literal Integer where
  literal = Integer

instance Literal String where
  literal = String

data Remote :: (* -> *) -> * -> * where
  Var :: f a -> Remote f a
  Lit :: Lit a -> Remote f a
  Lam :: Scope ( (:~:) b  ) Remote f a -> Remote f (b -> a)
  Let :: Vec (Scope (Ix bs) Remote f) bs -> Scope (Ix bs) Remote f a -> Remote f a
  Ap  :: Remote f (a -> b) -> Remote f a -> Remote f b

lam_ :: EqF f => f a -> Remote f b -> Remote f (a -> b)
lam_ v f = Lam (abstract (v ==?) f)

lit :: Literal a => a -> Remote f a
lit = Lit . literal

instance HFunctor Remote where
  hmap f (Var a)    = Var (f a)
  hmap _ (Lit t)    = Lit t
  hmap f (Lam b)    = Lam (hmap f b)
  hmap f (Let bs b) = Let (hmap (hmap f) bs) (hmap f b)
  hmap f (Ap x y)   = Ap (hmap f x) (hmap f y)

instance HTraversable Remote where
  htraverse f (Var a)    = Var <$> f a
  htraverse _ (Lit t)    = pure $ Lit t
  htraverse f (Lam b)    = Lam <$> htraverse f b
  htraverse f (Let bs b) = Let <$> htraverse (htraverse f) bs <*> htraverse f b
  htraverse f (Ap x y)   = Ap <$> htraverse f x <*> htraverse f y

instance HMonad Remote where
  hreturn        = Var
  Var a    >>- f = f a
  Lit t    >>- _ = Lit t
  Lam b    >>- f = Lam (b >>>- f)
  Let bs b >>- f = Let (hmap (>>>- f) bs) (b >>>- f)
  Ap x y   >>- f = Ap (x >>- f) (y >>- f)

(!) :: Vec f v -> Ix v a -> f a
(b ::: _)  ! Z   = b
(_ ::: bs) ! S n = bs ! n
_x ! _y = error "vec ! impossible badness "

eval :: Remote Identity a -> a
eval (Var w) = extract w
eval (Lit i) = value i
eval (Lam b) = \a -> eval (instantiate (\Refl -> Var (Identity a)) b)
eval (Let bs b) = eval (instantiate (vs !) b) where vs = hmap (instantiate (vs !)) bs
eval (Ap x y) = eval x (eval y)

closed :: HTraversable t => t f a -> Maybe (t g a)
closed = htraverse (const Nothing)

newtype V (a :: *) = V Unique

instance EqF V where
  V a ==? V b
    | a == b    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

lam :: (Remote V a -> Remote V b) -> Remote V (a -> b)
lam f = unsafePerformIO $ do
  x <- fmap V newUnique
  return $ Lam $ abstract (x ==?) $ f $ Var x

data Binding a = V a := Remote V a

rhs :: Binding a -> Remote V a
rhs (_ := a) = a

data Bindings = forall bs. Bindings (Vec Binding bs)

elemIndex :: Vec Binding bs -> V a -> Maybe (Ix bs a)
elemIndex HNil              _ = Nothing
elemIndex ((x := _r) ::: xs) y = case x ==? y of
  Just Refl -> Just Z
  Nothing   -> S <$> elemIndex xs y

instance Monoid Bindings where
  mempty = Bindings HNil
  Bindings xs `mappend` Bindings ys = Bindings (happend xs ys)

-- Allow the use of DoRec to define let statements

newtype Def a = Def { runDef :: IO (a, Bindings) }

instance Functor Def where
  fmap f (Def m) = Def $ do
    (a,w) <- m
    return (f a, w)

instance Applicative Def where
  pure = return
  (<*>) = ap

instance Monad Def where
  return a = Def $ return (a, mempty)
  Def m >>= f = Def $ do
    (a, xs) <- m
    (b, ys) <- runDef (f a)
    return (b, xs <> ys)

instance MonadFix Def where
  mfix m = Def $ mfix $ \ ~(a, _) -> runDef (m a)

def :: Remote V a -> Def (Remote V a)
def v@Var{} = Def $ return (v, mempty) -- this thing already has a name
def r = Def $ do
  v <- fmap V newUnique
  return (Var v, Bindings (hsingleton (v := r)))

let_ :: Def (Remote V a) -> Remote V a
let_ (Def m) = unsafePerformIO $ do
    (r, Bindings bs) <- m
    return $ Let (hmap (abstract (elemIndex bs) . rhs) bs)
                 (abstract (elemIndex bs) r)
