{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric, LambdaCase,TypeOperators #-}


module Language.Hopper.Internal.Core.ClosureConvertedANF where

import Data.Word
import Data.Data
import qualified Data.Map as Map-- FIXME, use IntMap or WordMap

import Data.Text (Text)
import Language.Hopper.Internal.Core.Literal
import Language.Hopper.Internal.Core.Closed
import Language.Hopper.Internal.Core.Term
import GHC.Generics
--import Language.Hopper.Internal.Core.Heap
--import Language.Hopper.Internal.Core.HeapRef
--import Data.Hop.Or
--import Control.Monad.STE
{-
DESIGN
- this is the closure-converted let normal form (ANF) sibling of the types-as-calling-conventions language/abstract machine
- all variables are local vars
- all thunks and closures are replaced with symbolic IDs to the underlying code that will run when provided with the
  appropriate environment structure, and, if appropriate, the applicable function args
- consequences:
    - all code becomes first-order
    - all heap refs flow through a local env stack
    - (for now) all values held on the heap have a double indirection via env to heap
-}

{-
DESIGN NOTE:
once RTS is more mature, references to statically resolved / restricted values / functions
should be supported along with jumping through the local environment scope

may also want to think about some values only being listed in the local environment vs also being in the heap,
maybe
-}

-- | LocalVariableCC is a local variable that is operationally an offset in an environment structure
newtype LocalVariableCc = LocalVarCc Word64
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

newtype ThunkCodeId =
    ThunkCodeId { unThunkCodeId :: Word64 }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)
newtype ClosureCodeId =
    ClosureCodeId { unClosureCodeId :: Word64 }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)
newtype EnvSize =
    EnvSize { unEnvSize :: Word64 }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)
newtype CodeArity =
    CodeArity { getCodeArity :: Word64 }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)


data AnfBinderInfoCc =  BinderInfoCc {} --- this needs to be fleshed out
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data CcValueRep = FIXMEEEEEEANFCC --- TODO

data ThunkCodeRecord
  = ThunkCodeRecord !EnvSize      -- number of slots in the environment struct
                    ![Maybe Text] -- source names, if applicable, for the captured free vars in the orig source
                                  -- TODO, replace the sourcenames list field with V.Vector CcAnfBinderInfo
                    !AnfCc        -- the code
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)
{- |
for now we pass all function args as references to boxed heap values,
but in the future we can be clever about specialization / register-sized values
-}
data ClosureCodeRecord
  = ClosureCodeRecord !EnvSize
                      ![Maybe Text] -- source names, if applicable, for the captured free vars in the orig source
                                    --- TODO / FIXME replace with CcAnfBinderInfo
                      !CodeArity
                      -- ![CcAnfBinderInfo] -- info about the function args
                      -- how many explicit arguments the function takes
                      --- later we'll have [arg rep]
                      !AnfCc
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)


{- DESIGN QUESTION


-}

data AnfCc
    = CReturnCc ![LocalVariableCc]
    | LetNFCc
          {- TODO: src loc info -}
          ![(Bool,Maybe Text)]   -- TODO FIXME, replace with CcAnfBinderInfo
            -- the length == size of RHS multiple return value tuple
                 -- the True positions are the ones whose heap refs are copied into the
                 -- local environment stack
                 -- this is like a wimpy version of pattern matching on products
          !(RhsCc) -- right hand side of let binder, closure converted
          !(AnfCc) -- body of the let
    | TailCallCc !(AppCc)
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data AppCc
    = EnterThunkCc !LocalVariableCc -- if a is neutral term OR a free variable, this becomes neutral
    | FunAppCc !LocalVariableCc ![LocalVariableCc] --- if function position of FunApp is neutral, its neutral
    | CcPrimApp !PrimOpId ![LocalVariableCc] -- if any arg of a primop is neutral, its neutral
      --- case / eliminators will also be in this data type later
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data RhsCc
  = AllocRhsCc !AllocCc
  | NonTailCallAppCc !AppCc
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data AllocCc
  = SharedLiteralCc !Literal
  | ConstrAppCc !ConstrId
                ![LocalVariableCc]
  | AllocateThunkCc
        ![LocalVariableCc] -- the set of local variables captured in the thunk environment, in this order
        !ThunkCodeId -- thunk id for "code pointer" part of a closure
  | AllocateClosureCc
        ![LocalVariableCc] -- set of local variables captured in the thunk environment, in this order
        !Word64 --- arity of closure
        !ClosureCodeId -- the code id for the "code pointer" of a closure
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data CodeRegistry = CodeRegistry !(Map.Map ThunkCodeId ThunkCodeRecord)
                                 !(Map.Map ClosureCodeId ClosureCodeRecord)

-- TODO: implement this after ccAnf evaluator
--
closureConvert :: Closed Term {-  FIX -} -> (AnfCc, CodeRegistry)
closureConvert = error "_FINISHMEEEEEBRIANNNNN" -- TODO

