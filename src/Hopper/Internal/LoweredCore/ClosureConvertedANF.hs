{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric, LambdaCase,TypeOperators #-}


module Hopper.Internal.LoweredCore.ClosureConvertedANF where

import Data.Word
import Data.Data
import qualified Data.Map as Map-- FIXME, use IntMap or WordMap

--import Data.Text (Text)
import Hopper.Internal.Core.Literal
import Hopper.Utils.Closed
import Hopper.Internal.Core.Term
import GHC.Generics
import qualified  Data.Vector as V
import Hopper.Internal.Type.Relevance
--import Hopper.Internal.Core.Heap
--import Hopper.Internal.Core.HeapRef
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
newtype LocalVariableCC = LocalVarCC Word64
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

newtype ThunkCodeId =
    ThunkCodeId { unThunkCodeId :: Word64 }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)
newtype ClosureCodeId =
    ClosureCodeId { unClosureCodeId :: Word64 }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)
newtype EnvSize =
    EnvSize { getEnvSize :: Word64 }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)
newtype CodeArity =
    CodeArity { getCodeArity :: Word64 }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

{-
subtle issue with typed closure conversion:
all the fields of the


-}

-- whether the binder position is a variable, wild card,
-- live/dead, type/runtime rep info?

--- kill these stubs later
--type Relevance = ()
type TypeCC = () -- TODO FIXME, wire in the real type info?
data BinderInfoCC =
      BinderInfoDataCC
        { relevanceBICC :: Relevance -- if zero, during evaluation we need not pass around
                                     --  BUT during NORMALIZATION, we probably do
                                     --  so the normalizer WILL thread around irrelevant values
                                     -- to properly support dependent type checking
                                     -- as is proper, because a runtime irrelevant value
                                     -- SHOULD be relevant during type checking, or
                                     -- it has no reason to exist
        , typeBICC :: TypeCC  -- at least for now, closure converted stuff may need a
          -- slightly different type system fragment than the Core layer Terms?
          -- NB: once we have existentials, should just be an "equivalent" subset
          -- of the full type theory?
        , sourceInfo :: Maybe String --- this isn't quite right ...
        -- also should add
          } --- this needs to be fleshed out
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)


{-
forward looking design question:
how should the heap rep for Constructors, Thunks and Closures be related
-}

data ValueRepCC ref =
                ValueLitCC !Literal
              | ConstructorCC !ConstrId  !(V.Vector ref)
              | ThunkCC !(V.Vector ref)  !(ThunkCodeId)
              --  should this be a heap ref to
              -- closure to have the right sharing ?
              | ClosureCC !(V.Vector ref) !(ClosureCodeId)  -- heap ref?
              | BlackHoleCC
              | IndirectionCC ref
  deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)


data ThunkCodeRecordCC
  = ThunkCodeRecordCC !EnvSize      -- number of slots in the environment struct
                                  --
                    !(V.Vector BinderInfoCC) -- source names, if applicable, for the captured free vars in the orig source
                                  -- TODO, replace the sourcenames list field with V.Vector CCAnfBinderInfo
                    !AnfCC        -- the code
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)
{- |
for now we pass all function args as references to boxed heap values,
but in the future we can be clever about specialization / register-sized values.
Additionally

-}
data ClosureCodeRecordCC
  = ClosureCodeRecordCC !EnvSize -- is this redundant
                      !(V.Vector BinderInfoCC)
                      -- source names, if applicable, for the captured free vars in the orig source
                                    --- TODO / FIXME replace with CCAnfBinderInfo
                      !CodeArity  -- is this redundant?
                      !(V.Vector BinderInfoCC) -- explicit
                      -- ![CCAnfBinderInfo] -- info about the function args
                      -- how many explicit arguments the function takes
                      --- later we'll have [arg rep]
                      !AnfCC
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)


{- DESIGN QUESTION


-}

data AnfCC
    = ReturnCC !(V.Vector LocalVariableCC)
    | LetNFCC
          {- TODO: src loc info -}
          !(V.Vector BinderInfoCC)  -- TODO FIXME, replace with CCAnfBinderInfo
            -- the length == size of RHS multiple return value tuple
                 -- the True positions are the ones whose heap refs are copied into the
                 -- local environment stack
                 -- this is like a wimpy version of pattern matching on products
          !(RhsCC) -- right hand side of let binder, closure converted
          !(AnfCC) -- body of the let
    | TailCallCC !(AppCC)
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data AppCC
    = EnterThunkCC !LocalVariableCC -- if a is neutral term OR a free variable, this becomes neutral
    | FunAppCC !LocalVariableCC !(V.Vector LocalVariableCC) --- if function position of FunApp is neutral, its neutral
    | PrimAppCC !PrimOpId !(V.Vector LocalVariableCC) -- if any arg of a primop is neutral, its neutral
      --- case / eliminators will also be in this data type later
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data RhsCC
  = AllocRhsCC !AllocCC
  | NonTailCallAppCC !AppCC
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data AllocCC
  = SharedLiteralCC !Literal
  | ConstrAppCC !ConstrId
                !(V.Vector LocalVariableCC)
  | AllocateThunkCC
        !(V.Vector LocalVariableCC) -- the set of local variables captured in the thunk environment, in this order
        !ThunkCodeId -- thunk id for "code pointer" part of a closure
  | AllocateClosureCC
        !(V.Vector LocalVariableCC) -- set of local variables captured in the thunk environment, in this order
        !Word64 --- arity of closure (need that even be here?) TODO
        !ClosureCodeId -- the code id for the "code pointer" of a closure
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data CodeRegistryCC = CodeRegistry !(Map.Map ThunkCodeId ThunkCodeRecordCC)
                                 !(Map.Map ClosureCodeId ClosureCodeRecordCC)
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

-- TODO: implement this after ccAnf evaluator
--
closureConvert :: Closed Term {-  FIX -} -> (AnfCC, CodeRegistryCC)
closureConvert = error "_FINISHMEEEEEBRIANNNNN" -- TODO

