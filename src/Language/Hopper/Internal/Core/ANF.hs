{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
-- {-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE KindSignatures #-}
-- {-# LANGUAGE DeriveGeneric #-}

module Language.Hopper.Internal.Core.ANF  where

import Language.Hopper.Internal.Core.Type
import Language.Hopper.Internal.Core.Literal
import Data.Text (Text)
import Data.Data
import Data.Word (Word64)

import  Control.Monad
import Prelude.Extras
import Bound
-- import Language.Hopper.Internal.Core.Value (Tag)

-- newtype Atom  ty a = AtomVar {unVar :: a}
--
--     -- | AtomicLit !Literal
--   -- lambdas need a heap allocation to do the closure allocation in general
--   -- even if they are on the left hand side of an application, UNLESS they are fully applied at that use site
--   --  | AtomLam ![(Text,Type ty,RigModel)] -- do we want to allow arity == 0, or just >= 1?
--   --             !(Scope Text (ANF ty)  a)
--    deriving(Eq,Ord,Functor,Foldable,Traversable,Data,Show,Read,Typeable)
--
-- instance Eq ty => Eq1 (Atom ty)
-- instance Show ty => Show1 (Atom ty)
-- instance Ord ty => Ord1 (Atom ty)
-- instance Read ty => Read1 (Atom ty)
--
-- instance Eq2 Atom
-- instance Show2 Atom
-- instance Ord2 Atom
-- instance Read2 Atom


-- at runtime 'ConstrId' is mapped to a tag???
newtype ConstrId  = ConstrId { unConstrId :: Text } deriving (Eq, Show,Data,Typeable,Ord,Read)

-- | the right hand side of a let, aka 'AnfRHS' is the point where heap allocation of thunks happens
-- the only other
data AnfRHS ty a

--- SPLIT ANF RHS INTO ALLOCATING case and CALLING case sub data tyes  FIXMEEEEE

                 = SharedLiteral !Literal -- we currently do not have any fixed size literal types
                                          -- so for now all literals are heap allocated
                                          -- this will change once we add support for stuff like
                                          -- Double or Word64
                 | AllocateThunk !(ANF ty a) -- Thunks share their evaluations
                --  | EvaluateThunk !a       -- Thunk evaluation is a special
                --                           -- no arg lambda plus sharing
                                            -- thunks and closure should
                                            -- record their free variables???
                 | AllocateClosure ![(Text,Type ty,RigModel)] -- arity >=0
                                   !(Scope Text (ANF ty)  a)  -- should we have global table of
                                                              -- "pointers" to lambdas? THINK ME + FIX ME

                 | NonTailCallApp !(AppANF ty a) -- control stack allocation; possibly heap allocation

                  {- AllocateClosure {env :: [(Text,a)], codeBod :: CodeIdentifier } ???  -}

   deriving (Ord,
    Functor,
    Foldable,
    Traversable,
    Typeable,
    Data,
    Eq,
    Read,
    Show)
instance Eq ty => Eq1 (AnfRHS ty)
instance Show ty => Show1 (AnfRHS ty)
instance Ord ty => Ord1 (AnfRHS ty)
instance Read ty => Read1 (AnfRHS ty)

instance Eq2 AnfRHS
instance Show2 AnfRHS
instance Ord2 AnfRHS
instance Read2 AnfRHS
-- data ArgANF ty a = ArgVar a | ArgLit !Literal


data AppANF ty a = EnterThunk !a
                 | ConstrApp !ty !ConstrId ![a]
                 -- this isnt' doing a jump....  FIXMEEEEE
                 -- move into ALLOCATOR case of RHS ANF 
                 | FunApp !a ![a]
                 | PrimApp !Text ![a]
        deriving ( Ord,
         Functor,
         Foldable,
         Traversable,
         Typeable,
         Data,
         Eq,
         Read,
         Show)

instance Eq ty => Eq1 (AppANF ty)
instance Show ty => Show1 (AppANF ty)
instance Ord ty => Ord1 (AppANF ty)
instance Read ty => Read1 (AppANF ty)

instance Eq2 AppANF
instance Show2 AppANF
instance Ord2 AppANF
instance Read2 AppANF


data ANF ty a
    = ReturnNF  !a -- !(Atom ty a)
    | Let !(AnfRHS ty a) !(Scope () (ANF ty) a)
    -- | LetMulti ![AnfRHS ty a] !(Scope Word64 (ANF ty) a)
    | TailCallANF !(AppANF ty a)
    -- future thing will have | LetRec maybe?
    deriving (Ord,
      Functor,
      Foldable,
      Traversable,
      Typeable,
      Data,
      Eq,
      Read,
      Show)
instance Eq ty => Eq1 (ANF ty)
instance Show ty => Show1 (ANF ty)
instance Ord ty => Ord1 (ANF ty)
instance Read ty => Read1 (ANF ty)

instance Eq2 ANF
instance Show2 ANF
instance Ord2 ANF
instance Read2 ANF

-- l2rJoinANF :: forall ty a . (ANF ty (ANF ty a)) -> (ANF ty a)
-- l2rJoinANF (ReturnNF a) = a
-- l2rJoinANF (Let rhs bod) = l2rCanonicalRHS rhs (Scope $ fmap (fmap l2rJoinANF) $ unscope bod)
--
-- l2rCanonicalRHS :: AnfRHS ty (ANF ty a)
--                 -> ((Scope () (ANF ty) a)
--                 -> ANF ty a)
-- l2rCanonicalRHS (AllocateThunk e) scp = Let (AllocateThunk $ l2rJoinANF e) scp
-- l2rCanonicalRHS (SharedLiteral l) scp = Let (SharedLiteral l) scp
-- l2rCanonicalRHS (AllocateClosure ls bod) scp = Let (AllocateClosure ls $ Scope $ fmap (fmap l2rJoinANF) $ unscope bod) scp

{-
AUDIT: should we just be doing the too / from scope functions?

-}
flattenUnderScope :: Scope b (ANF ty) (ANF ty a) -> Scope b (ANF ty) a
flattenUnderScope = Scope . fmap (fmap danvyANF) . unscope



zoomToTailPosition :: forall a ty . (forall c . c -> ANF ty c) ->  ANF ty a -> ANF ty a
zoomToTailPosition f (ReturnNF a)  = f a
zoomToTailPosition f (TailCallANF app)  = Let (NonTailCallApp app)
                                           (Scope $ f (B () ))
zoomToTailPosition f (Let rhs bod)  =   Let rhs
                                          (Scope $ (fmap $ fmap $ zoomToTailPosition f) $ unscope bod)
-- zoomToTailPosition f (LetMulti rhss bod) = LetMulti rhss
--                     (Scope $ (fmap $ fmap $ zoomToTailPosition f) $ unscope bod)

danvyANF :: (ANF ty (ANF ty a)) -> ANF ty a
danvyANF (ReturnNF a) = a
danvyANF (TailCallANF app) = danvyTailCallANF app
danvyANF (Let rhs bod) = danvyRHS rhs (\r -> Let r $  flattenUnderScope bod)

danvyRHS :: (AnfRHS ty (ANF ty a)) ->(AnfRHS ty a -> ANF ty a) -> ANF ty a
danvyRHS (SharedLiteral l)  f =  f $ SharedLiteral l
danvyRHS (AllocateThunk expr) f = f $ AllocateThunk $ danvyANF expr
danvyRHS (AllocateClosure args scp) f = f $ AllocateClosure args (flattenUnderScope scp)
danvyRHS (NonTailCallApp app) f = danvyNotTailCallANF app  f


danvyExp2RhsANF :: (ANF ty a) -> ( a -> ANF ty a) -> ANF ty a
danvyExp2RhsANF = error "{ this is TERRRRIBLEEEEEEE }"
-- danvyExp2RhsANF (ReturnNF v) f = f v
-- danvyExp2RhsANF (TailCallANF app) f = danvyNotTailCallANF app (\ rhs -> Let rhs )


danvyTailCallANF :: (AppANF ty (ANF ty a)) {- } -> (AppANF ty a -> ANF ty a )-} -> ANF ty a
danvyTailCallANF (EnterThunk (ReturnNF x)) =  Let (NonTailCallApp (EnterThunk x))
                                                  (Scope  $ ReturnNF(B ()))
danvyTailCallANF (EnterThunk (TailCallANF app)) =
                                            Let
                                              (NonTailCallApp app)
                                              (Scope $ (
                                                ( Let (NonTailCallApp (EnterThunk (B ())))
                                                      (Scope $ ReturnNF (B () ))
                                                      )))
danvyTailCallANF (EnterThunk lt@(Let _ _))=
          zoomToTailPosition (\ x -> Let (NonTailCallApp $ EnterThunk x )
                                            (Scope $ ReturnNF (B()))
                                          )
                              lt

danvyNotTailCallANF :: (AppANF ty (ANF ty a)) -> ( AnfRHS ty a -> ANF ty a) -> ANF ty a
danvyNotTailCallANF (EnterThunk a) f = danvyExp2RhsANF a (\ var -> f $ NonTailCallApp
                                                                     $ EnterThunk var  )
{- traverse from right to left using Reverse or Backwards applicative
over State, accumulating continuations of the inner scopes that are the
later evaluation steps
  -}

instance Applicative (ANF ty) where
  pure  = \x -> ReturnNF  x
  (<*>) = ap

instance Monad (ANF ty) where
  (ReturnNF var) >>= f = f var


 {- (afun :@@ aargs) >>= f =
        let subst'dArgs :: forall a b .  (a -> ANF ty b) -> [Atom ty a]-> [ANF ty b]
            subst'dArgs  g  ls = fmap (unVar . fmap g) ls
            foldrList :: forall a b . (a -> b -> b) -> b -> [a] -> b
            foldrList = foldr
            cps'dArgs :: _sdfdsfdsf
            cps'dArgs = foldrList  cpsStacking id  (subst'dArgs f aargs)
            -- cpsStacking :: forall  a  . ( ) -> (a -> ANF ty a) -> (a -> ANF ty a)
            cpsStacking = _lalala
        in  (f $ unVar $ afun) `cpsStacking` cps'dArgs-}
  -- (Let aRHS aBod) >>= f = _dderp
  -- (ReturnNF (AtomicLit l)) >>= _f = ReturnNF $ AtomicLit l
  -- (ReturnNF (AtomLam bs bod)) >>= f = ReturnNF $ AtomLam bs (bod >>>= f)
  --( ( ) :@@ )

  -- return = V
  --V a         >>= f = f a
  --Delay e     >>= f = Delay $ e >>= f
  --Force e     >>= f = Force $ e >>= f
  --ELit e      >>= _f = ELit e -- this could also safely be a coerce?
  --(x :@ y)    >>= f = (x >>= f) :@ (y >>= f)
  --Lam t  e    >>= f = Lam t (e >>>= f)
  --Let t bs  b >>= f = Let t (  bs >>= f)  (b >>>= f)
