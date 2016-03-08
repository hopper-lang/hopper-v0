{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric, LambdaCase,TypeOperators #-}


module Hopper.Internal.LoweredCore.ClosureConvertedANF(
  AnfCC(..)
  ,LocalNamelessVar(..)
  ,Variable(..)
  ,BinderSlot(..)
  ,GlobalSymbol(..)
  ,AllocCC(..)
  ,AppCC(..)
  ,RhsCC(..)
  ,ClosureCodeId(..)
  ,ThunkCodeId(..)
  ,EnvSize(..) --- not sure if this is needed
  ,CodeArity(..) -- not sure if this is needed
   -- ,TypeCC(..) --- this shouldn't need to exist
  ,BinderInfoCC(..) --- not sure if there need be a lowered form of binders except to lower types?
  ,TransitiveLookup(..) -- this is a class reexport
  ,CodeRecord(..) -- this is an adhoc class that shouldn't be living here :)
  ,ValueRepCC(..)
  ,ClosureCodeRecordCC(..)
  ,ThunkCodeRecordCC(..)
  ,SymbolRegistryCC(..)
  ,lookupThunkCodeId
  ,lookupClosureCodeId
  ) where

import Data.Word
import Data.Data
import qualified Data.Map as Map-- FIXME, use IntMap or WordMap

import qualified Data.Text as T (Text)
import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term
import GHC.Generics
import qualified  Data.Vector as V
import Hopper.Internal.Type.Relevance(Relevance)
import Hopper.Internal.Runtime.Heap(TransitiveLookup(..),heapLookup)
import Hopper.Internal.Runtime.HeapRef(Ref)
import Hopper.Utils.LocallyNameless
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
type TypeCC = () -- TODO FIXME, wire in the real type info? This will be Term???!
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



instance TransitiveLookup (ValueRepCC Ref) where
  transitiveHeapLookup initref = go 1 initref
    where
      go !step !ref =
        do newval <- heapLookup ref
           case newval of
             (IndirectionCC newref) -> case length newref of
               1 -> go (step + 1) (V.head newref)
               _ -> return (step, newval)
             _ -> return (step, newval)


{-
forward looking design question:
how should the heap rep for Constructors, Thunks and Closures be related
-}

data ValueRepCC ref =
                ValueLitCC   !Literal
              | ConstructorCC !ConstrId  !(V.Vector ref)
              | ThunkCC !(V.Vector ref)  {-# UNPACK #-}  !(ThunkCodeId)
              --  should this be a heap ref to
              -- closure to have the right sharing ?
              | ClosureCC !(V.Vector ref)  {-# UNPACK #-}  !(ClosureCodeId)  -- heap ref?
              | BlackHoleCC
              | IndirectionCC !(V.Vector ref)
  deriving (Eq,Ord,Show,Read,Typeable,Data,Generic)

class CodeRecord a where
  envSize :: a -> Word64
  envBindersInfo :: a -> V.Vector BinderInfoCC

data ThunkCodeRecordCC =
  ThunkCodeRecordCC
    -- | number of slots in the environment struct
    {-# UNPACK #-} !EnvSize
    -- | source names, if applicable, for the captured free vars in the orig source
    -- TODO(carter): replace the sourcenames list field with V.Vector CCAnfBinderInfo
    !(V.Vector BinderInfoCC)
    -- | the code
    !AnfCC
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

instance CodeRecord ThunkCodeRecordCC where
  envSize (ThunkCodeRecordCC size _ _) = getEnvSize size
  {-# INLINE envSize #-}
  envBindersInfo (ThunkCodeRecordCC _ bs _) = bs
  {-# INLINE envBindersInfo #-}

{- |
for now we pass all function args as references to boxed heap values,
but in the future we can be clever about specialization / register-sized values.
Additionally

-}
data ClosureCodeRecordCC =
  ClosureCodeRecordCC  {-# UNPACK #-}  !EnvSize -- is this redundant
                      !(V.Vector BinderInfoCC)
                      -- source names, if applicable, for the captured free vars in the orig source
                                    --- TODO / FIXME replace with CCAnfBinderInfo
                      {-# UNPACK #-}  !CodeArity  -- is this redundant?
                      !(V.Vector BinderInfoCC) -- explicit
                      -- ![CCAnfBinderInfo] -- info about the function args
                      -- how many explicit arguments the function takes
                      --- later we'll have [arg rep]
                      !AnfCC
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

instance CodeRecord ClosureCodeRecordCC where
  envSize (ClosureCodeRecordCC size _ _ _ _) = getEnvSize size
  {-# INLINE envSize #-}
  envBindersInfo (ClosureCodeRecordCC _ bs _ _ _) = bs
  {-# INLINE envBindersInfo #-}

data AnfCC  =
    ReturnCC !(V.Vector Variable)
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


data AppCC  =
    EnterThunkCC !Variable -- if a is neutral term OR a free variable, this becomes neutral
    | FunAppCC !Variable !(V.Vector Variable) --- if function position of FunApp is neutral, its neutral
    | PrimAppCC !PrimOpId !(V.Vector Variable) -- if any arg of a primop is neutral, its neutral
      --- case / eliminators will also be in this data type later
     {- | CaseCc
        --- desugared case, not perfect, but good enough for sum data types,
        --- not sure about if it aligns with say... record projections and stuff
            VariableCC -- variable to case on
            TypeCC
            --- the type of the variable, because we need that to determine what constructors are admissible
            --- and do correct coverage checking
            [(ConstrId
              , V.Vector BinderInfoCC ---
              , AnfCC)] -- tag based dispatch??? kinda lame for Numbers and strings and stuff, only constructors
            Maybe AnfCc
                --- wild card case if applicable???
                ---  may correspond to either catch all cases or absurds??
                --- or would Case x typ [] Nothing , --- be the absurd case

        | RecordProjection   LocalVar   Type  Selector info
          --- for projecting out from nonlinear dependent or ordinary products?
          -- ghc and friends just use case for products, but that actually
          -- has known blowups in complexity  on large records
          -- TODO: look at how agda and idris and lean do this stuff


               -}
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data RhsCC
  = AllocRhsCC !AllocCC
  | NonTailCallAppCC !AppCC
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data AllocCC
  = SharedLiteralCC !Literal
  | ConstrAppCC {-# UNPACK #-}  !ConstrId
                !(V.Vector Variable)
  | AllocateThunkCC
        !(V.Vector Variable) -- the set of local variables captured in the thunk environment, in this order
        !ThunkCodeId -- thunk id for "code pointer" part of a closure
  | AllocateClosureCC
        !(V.Vector Variable) -- set of local variables captured in the thunk environment, in this order
        !Word64 --- arity of closure (need that even be here?) TODO
        !ClosureCodeId -- the code id for the "code pointer" of a closure
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

{- | SymbolRegistryCC is roughly a representatation of static read only data in _symRegValueMap
that is part of the "linkers" name space, though currently unused ... but that will change
and _symRegThunkMap and _symRegClosureMap are basically read only executable code pointers /
the regions of "memory" embodied by those codes


-}
data SymbolRegistryCC =
  SymbolRegistryCC { _symRegThunkMap :: !(Map.Map ThunkCodeId ThunkCodeRecordCC)
                    , _symRegClosureMap :: !(Map.Map ClosureCodeId ClosureCodeRecordCC)
                    , _symRegValueMap :: !(Map.Map GlobalSymbol (ValueRepCC GlobalSymbol))
                    --- value map is currently unused, but that will change
                                        }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)


lookupClosureCodeId :: SymbolRegistryCC -> ClosureCodeId-> Either String ClosureCodeRecordCC
lookupClosureCodeId (SymbolRegistryCC _thk closMap _vals) codeid =
      maybe  (Left $ "failed closure code lookup " ++ show codeid) (Right) $
        Map.lookup codeid closMap
lookupThunkCodeId :: SymbolRegistryCC -> ThunkCodeId-> Either String ThunkCodeRecordCC
lookupThunkCodeId (SymbolRegistryCC thkmap _closMap _vals) thud =
      maybe (Left $ "failed thunk code lookup " ++ show thud ) (Right) $
           Map.lookup thud thkmap
--lookupStaticValue :: this one is weird / we dont have it yet setup for this
-- because static values should roughly correspond to
