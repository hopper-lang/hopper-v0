{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}


module Language.Lambomba.Internal.Core where


import Bound
import Numeric.Natural
import Prelude.Extras
import Control.Applicative
import Control.Monad
import qualified  Data.Set as Set
import qualified  Data.Map as Map
import Data.Foldable (foldl')
import Data.Traversable

{- |  this iteration is essentially F_\omega, plus linear types,
plus inductive data types obeying the positivity condition, plus "crypto signed" values,
plus .... damnit, need dependent types to sanely treat crypto signed values

why?
because we dont know the commit id that a signed value in the result of a higher order transaction refers to until the parent computation is commited!


ok, so for now we're going to do F_omega, plus some singleton indexing
plus the kinda subtle "pubkey" "signed by"/"encrypted for" primitives that
-}


{-for now we're doing an STLC with a special pubkey type and some type level literals -}

data Kind = Star | KArr Kind Kind | LiftedPubKey
  deriving (Eq,Ord,Read,Show)

data TCon {-a -}=  TInt | TUnit | TArrow
                | EncryptedFor |  SignedBy
                | PubKey String {- this is not how it'll work :) -}
    deriving (Eq,Ord,Read,Show )
data Type  {-a -}=  Tapp (Type) (Type) | TLit (TCon)
   deriving (Eq,Ord,Read,Show)


deduceLitKind :: TCon ->  Kind
deduceLitKind tc = case tc of
          TUnit -> Star
          TInt -> Star
          TArrow -> KArr Star Star
          PubKey s -> LiftedPubKey
          EncryptedFor -> KArr LiftedPubKey Star
          SignedBy -> KArr LiftedPubKey Star


wellKindedType :: Type -> Either String Kind
wellKindedType tau = case tau of
  TLit tc -> Right $ deduceLitKind tc
  Tapp tarr tinput ->
      do  (KArr a b) <- wellKindedType tarr ; c <- wellKindedType tinput ;
          if a == c  {- this part will get tricky later :) -}
              then Right b
              else Left $   "Woops, kind mismatch " ++ show (a,c)

collectFreeVars :: (Ord a, Traversable f) => f a -> Set.Set a
collectFreeVars =   Set.fromList . foldl' (flip (:)) []

checkTerm :: forall a . (Ord a,Show a)=> Map.Map a Type -> Exp a -> Either String Type
checkTerm env term = do
                      missFVs <- Right $ collectFreeVars term `Set.difference` Map.keysSet env
                      if missFVs == Set.empty
                        then Right ()
                        else Left $ "error, there were unaccounted free variables: " ++  show missFVs
                      go env term

    where
      go :: Map.Map a Type -> Exp a -> Either String Type
      go mp tm = deduceType $ fmap (mp Map.!) tm
      deduceType :: Exp Type -> Either String Type
      deduceType (V t) = Right t
      deduceType (Lam t  scp)=  deduceType $ instantiate1 (V t) scp
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
data Value  =   Closure (Scope () Exp Value )
              | VLit Literal
   deriving (Eq,Ord,Show)


data Literal = Linteger Integer | LRational
  deriving(Eq,Ord,Show,Read)

data Exp a
  = V a
  | ELit Literal
  | Exp a :@ Exp a
  | Lam Type  (Scope () Exp a)
  | Let Type  (Exp a)  (Scope () Exp a) --  [Scope Int Exp a] (Scope Int Exp a)
  deriving (Eq,Ord,Show,Read,Eq1,Ord1,Show1,Read1)

instance Functor Exp  where fmap       = fmapDefault
instance Foldable Exp where foldMap    = foldMapDefault

instance Applicative Exp where
  pure  = V
  (<*>) = ap

instance Traversable Exp where
  traverse f (V a)      = V <$> f a
  traverse f (x :@ y)   = (:@) <$> traverse f x <*> traverse f y
  traverse f (Lam t e)    = Lam  t <$> traverse f e
  traverse f (Let t bs b) = Let  t <$>  (traverse f) bs <*> traverse f b


instance Monad Exp where
  return = V
  V a      >>= f = f a
  (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
  Lam t  e    >>= f = Lam t (e >>>= f)
  Let t bs  b >>= f = Let t (  bs >>= f)  (b >>>= f)

