{-# LANGUAGE ScopedTypeVariables#-}
module Hopper.Internal.LoweredCore.ANF where

import Hopper.Utils.LocallyNameless
import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term


import Data.Word
import qualified Data.Vector as V


-- TODO: switch back away from this
newtype Arity    = Arity Word32    deriving (Eq,Ord,Read,Show)

data Anf
  = AnfReturn !(V.Vector Variable) -- indices into the current env stack
  | AnfLet !Arity -- TODO: switch back to !(V.Vector BinderInfo)
           !Rhs
           !Anf
  | AnfTailCall !App
  deriving (Eq,Ord,Read,Show)

data App
  = AppFun !Variable !(V.Vector Variable)
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

anfTail :: Term -> Anf
anfTail x = case x of
  -- Return ls -> _stuff
  ELit lit -> returnAllocated $ AllocLit lit
  -- App fun args -> _morestuff
  Lam args bod ->
    let varMap :: Map.Map BinderInfo Variable
        varMap = Map.fromList $ zip (V.toList $ V.reverse args) (fmap (LocalVar . LocalNamelessVar 0 . BinderSlot) [0,1..])
    in returnAllocated $
         AllocLam (Arity $ fromIntegral $ length args)
                  (anfLocalVarTop $ instantiate (V . (varMap Map.!)) bod)

  where
    returnAllocated :: Alloc -> Anf
    returnAllocated alloc = AnfLet (Arity 1)
                                   (RhsAlloc alloc)
                                   (AnfReturn $ V.singleton $ LocalVar $ LocalNamelessVar 0 $ BinderSlot 0)

    anfLocalVarTop :: Term -> Anf
    anfLocalVarTop = undefined

    instantiate = undefined
