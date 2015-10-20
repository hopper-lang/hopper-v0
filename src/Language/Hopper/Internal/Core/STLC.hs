{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}



module Language.Hopper.Internal.Core.STLC where


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
import qualified Data.Vector as V
import Data.Word
import GHC.Generics (Generic)

import Data.Bifunctor
import Data.Bitraversable
import Data.Bifoldable
import Data.Biapplicative

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


data RigModel = Zero | One | Omega
 deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data Kind = Star | KArr Kind Kind | LiftedPubKey
  deriving (Eq,Ord,Read,Show,Data,Typeable,Generic)

data TCon {-a -}=  TInteger | TNatural | TRational  | TUnit | TArrow RigModel
                | EncryptedFor |  SignedBy
                | PubKey String {- this is not how it'll work :) -}
                -- | Linear
    deriving (Eq,Ord,Read,Show ,Data,Typeable,Generic)
data Type ty  {-a -}=  Tapp (Type ty) (Type ty) | TLit (TCon) | TVar ty
   deriving (Eq,Ord,Read,Show,Data,Typeable,Functor,Foldable,Traversable,Generic)


{-
a -> b

Tapp (Tapp (TLit TArrow) a) b


EncryptedFor Bob Boolean


SignedBy Alice Dollar

-}

deduceLitKind :: TCon ->  Kind
deduceLitKind tc = case tc of
          TUnit -> Star
          TInteger -> Star
          TNatural -> Star
          TRational -> Star
          -- Linear -> KArr Star Star
          TArrow _ -> KArr Star (KArr Star Star)
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


{-
should term checking check the "price" of the expression
ie  -> (Rng, Type ty)
-}
checkTerm :: forall a ty . (Ord a,Show a,Eq ty,Show ty)=> Map.Map a (RigModel,Type ty)
              -> Exp ty a -> Either String (RigModel,Type ty)
checkTerm env term = do
                      missFVs <- Right $ collectFreeVars term `Set.difference` Map.keysSet env
                      if missFVs == Set.empty
                        then Right ()
                        else Left $ "error, there were unaccounted free variables: " ++  show missFVs
                      go env term

    where
      go :: Map.Map a (RigModel,Type ty) -> Exp ty a -> Either String (RigModel, Type ty)
                  --- need to check that expression obeys rigmodel constraints
                  --- on the free variables
      go mp tm = deduceType $ fmap (mp Map.!) tm
      deduceLitType :: Literal ->  Type ty
      deduceLitType (LRational _)  = TLit TRational
      deduceLitType (LNatural _) = TLit  TNatural
      deduceLitType (LInteger _) = TLit  TInteger

      {-
    NOTE, ignoring type level substitution for now,
    this is fine for STLC, but wrong :)

    also need to split this into  synthesize and check directions

    also need to add a nested??
      -}
      deduceType :: Exp ty (RigModel,Type ty) -> Either String (RigModel, Type ty)

      deduceType (ELit x ) = Right $  (Omega, deduceLitType x)
      deduceType (Let a b c) = undefined

      -- by induction we assume lineary/irrelevance is well behaved at this point
      deduceType (V t) = Right t
      -- deduceType (ELit x) = _typeOfLit
      -- deduceType (Let a b c ) = _elet
      --- need to check that linearity is obeyed
      deduceType (Lam t  scp)=
        let
          mp = undefined
          -- mp = _mp t
          -- linTys = _linTy t
          -- zeroTys= _zeroTy t
            in  deduceType $ instantiate (\x -> mp Map.! x) scp
      deduceType (fn :@ arg) =
          do   (argRig , argTyp) <- deduceType arg ;
               (_funRig ,fnTyp) <- deduceType fn
               case fnTyp of
                  (Tapp (Tapp (TLit (TArrow funArgRig)) from) to) ->
                    if from == argTyp
                      then      ---Right to
                        case (argRig,funArgRig) of
                              (Zero,Zero)  -> ()
                              (Zero,_) ->
                                  Left $ "Irelevant input supplied to relevant function type " ++ show fnTyp
                              (One,Omega) -> Left $ "Linear input applied to standard functiont type" ++ show fnTyp
                              (One,x) -> ()
                              (Omega,x)  -> ()
                      else Left $ "expected type " ++ show from
                            ++ " received " ++ show argTyp

                  _ -> Left $ "Expected Function type in application position, received :"
                        ++ show fnTyp


      {-
        rough hacky(?) plan for now: change the types of Free variables from a to Type,
        that way

      -}
{-
checkLinearity ::

checkIrrelevance ::
-}
newtype Tag = Tag { unTag :: Word64 } deriving (Eq, Show,Ord,Data,Typeable,Generic)


-- | this model of Values and Closures doens't do the standard
-- explicit environment model of substitution, but thats ok
-- also this is the "pre type erasure" representation
data Value  ty  v  =  VLit !Literal
              | Constructor  Tag  (V.Vector (Value ty  v))
              | Thunk !(Exp ty v {-(Value ty con v)-}) -- i dont know if we need this
              | PartialApp [Arity]
                           [Value ty  v] !(Closure  ty  v {- (Value ty con v) -})
              | DirectClosure !(Closure ty v {- Value ty con v -})

   deriving (Typeable,Functor,Foldable,Traversable,Generic)
-- deriving instance(Eq1 con,Eq a,Eq ty) => Eq (Value ty con a)




data Arity = ArityBoxed --- for now our model of arity is boring and simple
 deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)

data Closure ty a = MkClosure ![Arity] !(Scope [Text] (Exp ty) a)
  deriving (Eq,Ord,Show,Read,Ord1,Show1,Read1,Functor,Foldable,Traversable,Data,Generic)
deriving instance Eq ty => (Eq1 (Closure ty))

closureArity :: Value ty  v-> Integer
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
  | Lam [(Text,Type ty,RigModel)] (Scope Text (Exp ty) a)
  | Let (Text,Type ty,RigModel)  (Exp ty a)  (Scope Text (Exp ty) a) --  [Scope Int Exp a] (Scope Int Exp a)
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

