{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,GeneralizedNewtypeDeriving #-}
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
import Language.Hopper.Internal.Core.ANF
import Language.Hopper.Internal.Core.Heap
import Language.Hopper.Internal.Core.HeapRef
import Data.Hop.Or
import Control.Monad.STExcept
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
newtype CcLocalVariable = CcLV Word64
  deriving(Eq,Ord,Show,Enum,Typeable)

newtype ThunkCodeId = ThunkCodeId { unThunkCodeId :: Word64 } deriving (Eq,Ord, Show,Typeable)
newtype ClosureCodeId = ClosureCodeId { unClosureCodeId :: Word64 } deriving (Eq,Ord,Show,Typeable)
newtype EnvSize = EnvSize { unEnvSize :: Word64 } deriving (Eq, Ord,Show,Typeable)
newtype CodeArity = CodeArity { getCodeArity :: Word64 } deriving (Eq,Ord,Show,Typeable)


data CcValueRep = FIXMEEEEEEANFCC --- TODO

data ThunkCodeRecord
  = ThunkCodeRecord !EnvSize      -- number of slots in the environment struct
                    ![Maybe Text] -- source names, if applicable, for the captured free vars in the orig source
                    !CcAnf        -- the code
    deriving (Eq,Ord,Show,Typeable)
{- |
for now we pass all function args as references to boxed heap values,
but in the future we can be clever about specialization / register-sized values
-}
data ClosureCodeRecord
  = ClosureCodeRecord !EnvSize
                      ![Maybe Text]
                      !CodeArity -- how many explicit arguments the function takes
                      --- later we'll have [arg rep]
                      !CcAnf
  deriving (Eq,Ord,Show,Typeable)


data CcAnf
    = CcReturn ![CcLocalVariable]
    | CcLetNF
          {- TODO: src loc info -}
          ![(Bool,Maybe Text)] -- the length == size of RHS multiple return value tuple
                 -- the True positions are the ones whose heap refs are copied into the
                 -- local environment stack
                 -- this is like a wimpy version of pattern matching on products
          !(CcRhs) -- right hand side of let binder, closure converted
          !(CcAnf) -- body of the let
    | CcTailCall !(CcApp)
  deriving (Eq,Ord,Show,Typeable)

data CcApp
    = CcEnterThunk !CcLocalVariable -- if a is neutral term OR a free variable, this becomes neutral
    | CcFunApp !CcLocalVariable ![CcLocalVariable] --- if function position of FunApp is neutral, its neutral
    | CcPrimApp !PrimOpId ![CcLocalVariable] -- if any arg of a primop is neutral, its neutral
      --- case / eliminators will also be in this data type later
  deriving (Eq,Ord,Show,Typeable)

data CcRhs
  = CcAllocRhs !CcAlloc
  | CcNonTailCallApp !CcApp
 deriving (Eq,Ord,Show,Typeable)

data CcAlloc
  = CcSharedLiteral !Literal
  | CcConstrApp !ConstrId
                ![CcLocalVariable]
  | CcAllocateThunk
        ![CcLocalVariable] -- the set of local variables captured in the thunk environment, in this order
        !ThunkCodeId -- thunk id for "code pointer" part of a closure
  | CcAllocateClosure
        ![CcLocalVariable] -- set of local variables captured in the thunk environment, in this order
        !Word64 --- arity of closure
        !ClosureCodeId -- the code id for the "code pointer" of a closure
  deriving (Eq,Ord,Show,Typeable)

-- TODO: implement this after ccAnf evaluator
--
closureConvert :: Closed Anf -> (CcAnf, CodeRegistry)
closureConvert = error "_FINISHMEEEEEBRIANNNNN" -- TODO
data CodeRegistry = CodeRegistry !(Map.Map ThunkCodeId ThunkCodeRecord)
                                 !(Map.Map ClosureCodeId ClosureCodeRecord)

data CcAnfEnvStack
data CcAnfControlStack
data CcAnfEvalError

evalCcAnf :: CodeRegistry -> CcAnfEnvStack -> CcAnfControlStack -> CcAnf -> HeapStepCounterM CcValueRep (STE (c :+ CcAnfEvalError :+ HeapError ) s) Ref
evalCcAnf = error "finish this next week"

-- evalANF ::  Anf Ref -> ControlStackAnf -> HeapStepCounterM hepRep (STE (c :+ ErrorEvalAnf :+ HeapError ) s) Ref
