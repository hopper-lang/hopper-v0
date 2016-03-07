{-# LANGUAGE ScopedTypeVariables#-}
module Hopper.Internal.LoweredCore.ANF where

import Bound
import Data.Text (Text)
import Data.Word
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map

import Hopper.Internal.Core.Literal
import Hopper.Utils.Closed
import Hopper.Internal.Core.Term

-- a De Bruijn index
newtype LocalVar = LocalVar Word64 deriving (Eq,Ord,Read,Show)

newtype Arity    = Arity Word64    deriving (Eq,Ord,Read,Show)

type Relevance = () -- TODO
type Type = ()      -- TODO

data BinderInfo
  = BinderInfo { relevanceBICC :: Relevance
                 -- ^ if zero, during evaluation we need not pass around BUT
                 -- during NORMALIZATION, we probably do. so the normalizer WILL
                 -- thread around irrelevant values to properly support
                 -- dependent type checking as is proper, because a runtime
                 -- irrelevant value SHOULD be relevant during type checking, or
                 -- it has no reason to exist.
               , typeBICC :: Type
                 -- ^ at least for now, closure converted stuff may need a
                 -- slightly different type system fragment than the Core layer
                 -- terms? NB: once we have existentials, should just be an
                 -- "equivalent" subset of the full type theory?
               , sourceInfo :: Maybe String
                 -- ^ TODO: change this
               -- TODO: more?
               }

-- type Var = Either LocalVar Text

data Anf
  = AnfReturn !(V.Vector LocalVar) -- indices into the current env stack
  | AnfLet !Arity -- TODO: switch back to !(V.Vector BinderInfo)
           !Rhs
           !Anf
  | AnfTailCall !App
  deriving (Eq,Ord,Read,Show)

data App
  = AppFun !LocalVar !(V.Vector LocalVar)
  deriving (Eq,Ord,Read,Show)

data Alloc
  = AllocLit !Literal
  | AllocLam !Arity -- TODO: switch back to !(V.Vector BinderInfo)
             !Anf
  deriving (Eq,Ord,Read,Show)

data Rhs
  = RhsAlloc !Alloc
  | RhsApp !App
  deriving (Eq,Ord,Read,Show)

anfTail :: Closed Term -> Anf
anfTail (Closed x) = case x of
  -- Return ls -> _stuff
  ELit lit -> returnAllocated $ AllocLit lit
  -- App fun args -> _morestuff
  Lam args bod ->
    let varMap :: Map.Map Text LocalVar
        varMap = Map.fromList $ zip (reverse args) (LocalVar <$> [0,1..])
    in returnAllocated $
         AllocLam (Arity $ fromIntegral $ length args)
                  (anfLocalVarTop $ instantiate (V . (varMap Map.!)) bod)

  where
    returnAllocated :: Alloc -> Anf
    returnAllocated alloc = AnfLet (Arity 1)
                                   (RhsAlloc alloc)
                                   (AnfReturn $ V.singleton $ LocalVar 0)

    anfLocalVarTop :: Term LocalVar -> Anf
    anfLocalVarTop = undefined
