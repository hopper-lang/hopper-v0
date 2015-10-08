{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Lambomba.Internal.Core.STLC where


import Bound
import Numeric.Natural
import Prelude.Extras
-- import Control.Applicative
import Control.Monad
import qualified  Data.Set as Set
import qualified  Data.Map as Map
import Data.Foldable (foldl')
import Data.Traversable
import Data.Text (Text)
import Data.Data
-- import qualified Data.Text as T

{- |  this iteration is essentially F_\omega, plus linear types,
plus inductive data types obeying the positivity condition, plus "crypto signed" values,
plus .... damnit, need dependent types to sanely treat crypto signed values

why?
because we dont know the commit id that a signed value in the result of a higher order transaction refers to until the parent computation is commited!


ok, so for now we're going to do F_omega, plus some singleton indexing
plus the kinda subtle "pubkey" "signed by"/"encrypted for" primitives that
-}


{-for now we're doing an STLC with a special pubkey type and some type level literals -}


data RngModel = Zero | One | Omega
 deriving (Eq,Ord,Show,Read,Data,Typeable)

data Kind = Star | KArr Kind Kind | LiftedPubKey
  deriving (Eq,Ord,Read,Show,Data,Typeable)

data TCon {-a -}=  TInteger | TNatural | TRational  | TUnit | TArrow
                | EncryptedFor |  SignedBy
                | PubKey String {- this is not how it'll work :) -}
                | Linear
    deriving (Eq,Ord,Read,Show ,Data,Typeable)
data Type ty  {-a -}=  Tapp (Type ty) (Type ty) | TLit (TCon) | TVar ty
   deriving (Eq,Ord,Read,Show,Data,Typeable,Functor,Foldable,Traversable)


{-
a -> b

Tapp (Tapp (TLit TArrow) a) b

-}

deduceLitKind :: TCon ->  Kind
deduceLitKind tc = case tc of
          TUnit -> Star
          TInteger -> Star
          TNatural -> Star
          TRational -> Star
          Linear -> KArr Star Star
          TArrow -> KArr Star (KArr Star Star)
          PubKey _s -> LiftedPubKey
          EncryptedFor -> KArr LiftedPubKey (KArr Star Star)
          SignedBy -> KArr LiftedPubKey (KArr Star Star)



wellKindedType ::(Show  ty, Ord ty ) => Map.Map ty Kind -> Type ty -> Either String Kind
wellKindedType kenv tau = case tau of
  TLit tc -> Right $ deduceLitKind tc
  TVar tv -> maybe  (Left $ "free type variable " ++ show tv) Right $ Map.lookup  tv kenv
  Tapp tarr tinput ->
      do  (KArr a b) <- wellKindedType kenv tarr ; c <- wellKindedType kenv tinput ;
          if a == c  {- this part will get tricky later :) -}
              then Right b
              else Left $   "Woops, kind mismatch " ++ show (a,c)

collectFreeVars :: (Ord a, Traversable f) => f a -> Set.Set a
collectFreeVars =   Set.fromList . foldl' (flip (:)) []

checkTerm :: forall a ty . (Ord a,Show a,Eq ty,Show ty)=> Map.Map a (Type ty) -> Exp ty a -> Either String (Type ty)
checkTerm env term = do
                      missFVs <- Right $ collectFreeVars term `Set.difference` Map.keysSet env
                      if missFVs == Set.empty
                        then Right ()
                        else Left $ "error, there were unaccounted free variables: " ++  show missFVs
                      go env term

    where
      go :: Map.Map a (Type ty) -> Exp ty a -> Either String (Type ty)
      go mp tm = deduceType $ fmap (mp Map.!) tm
      deduceLitType :: Literal ->  Type ty
      deduceLitType (LRational _)  = TLit TRational
      deduceLitType (LNatural _) = TLit  TNatural
      deduceLitType (LInteger _) = TLit  TInteger
      deduceType :: Exp ty (Type ty) -> Either String (Type ty)

      -- deduceType (ELit x ) =
      -- deduceType (Let a b c) =
      deduceType (V t) = Right t
      deduceType (ELit x) = _typeOfLit
      deduceType (Let a b c ) = _elet
      deduceType (Lam t  scp)=
        let
          mp = _mp t
          linTys = _linTy t
          zeroTys= _zeroTy t
            in  deduceType $ instantiate (\x -> mp Map.! x) scp
      deduceType (fn :@ arg) =
          do   argTyp <- deduceType arg ;
               fnTyp <- deduceType fn
               case fnTyp of
                  (Tapp (Tapp (TLit TArrow) from) to) ->
                    if from == argTyp
                      then Right to
                      else Left $ "expected type " ++ show from
                            ++ " received " ++ show argTyp

                  _ -> Left $ "Expected Function type in application position, received :"
                        ++ show fnTyp

      {-
        rough hacky(?) plan for now: change the types of Free variables from a to Type,
        that way

      -}


-- | this model of Values and Closures doens't do the standard
-- explicit environment model of substitution, but thats ok
data Value  ty  =  VLit !Literal
              | Thunk !(Exp ty (Value ty)) -- i dont know if we need this
              | PartialApp [Arity]
                           [Value ty] !(Closure  ty (Value ty))
              | DirectClosure !(Closure ty (Value ty))

   deriving (Eq,Ord,Show)

data Arity = ArityBoxed --- for now our model of arity is boring and simple
 deriving (Eq,Ord,Show,Read)

data Closure ty a = MkClosure ![Arity] !(Scope [Text] (Exp ty) a)
  deriving (Eq,Ord,Show,Read,Eq1,Ord1,Show1,Read1)


closureArity :: Value ty -> Integer
-- closureArity (Closure _ _)= 1
closureArity (Thunk _) = 0
-- closureArity (VLit _) = error "what is lit arity?!"
                    {-   answer, its either a 0 arity value, or a prim op -}

data Literal = LInteger !Integer | LRational !Rational | LNatural !Natural
  deriving(Eq,Ord,Show,Read,Data,Typeable)


data Exp ty a
  = V  a
  | ELit Literal
  | Exp ty a :@ Exp ty a
  | Lam [(Text,Type ty,RngModel)] (Scope Text (Exp ty) a)
  | Let (Text,Type ty,RngModel)  (Exp ty a)  (Scope Text (Exp ty) a) --  [Scope Int Exp a] (Scope Int Exp a)
  deriving (Typeable,Data)
deriving instance (Read a, Read ty) => Read (Exp ty a)
deriving instance (Read ty) => Read1 (Exp ty)
deriving instance (Show a, Show ty) => Show (Exp ty a)
deriving instance (Show ty) => Show1 (Exp ty)
deriving instance (Ord ty) => Ord1 (Exp ty)
deriving instance (Ord ty,Ord a) => Ord (Exp ty a)
deriving instance (Eq ty) => Eq1 (Exp ty)
deriving instance (Eq a,Eq ty) => Eq (Exp ty a)

instance Functor (Exp ty)  where fmap       = fmapDefault
instance Foldable (Exp ty) where foldMap    = foldMapDefault

instance Applicative (Exp ty) where
  pure  = V
  (<*>) = ap

instance Traversable (Exp ty) where
  traverse f (V a)      = V <$> f a
  traverse f (x :@ y)   = (:@) <$> traverse f x <*> traverse f y
  traverse f (Lam t e)    = Lam  t <$> traverse f e
  traverse f (Let t bs b) = Let  t <$>  (traverse f) bs <*> traverse f b


instance Monad (Exp ty) where
  -- return = V
  V a      >>= f = f a
  (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
  Lam t  e    >>= f = Lam t (e >>>= f)
  Let t bs  b >>= f = Let t (  bs >>= f)  (b >>>= f)

