{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}


module  Hopper.Internal.Core.TermLocallyNameless where



import Hopper.Internal.Core.Literal
-- import Hopper.Internal.Core.Type
import Data.Text  as T (Text)
import Data.Data
--import Bound
--import Data.Bifunctor
import Data.Word (Word32)
--import Prelude.Extras
import Control.Monad
import GHC.Generics (Generic)
import Hopper.Internal.Type.Relevance(Relevance)
--import Data.Traversable --  (fmapDefault,foldMapDefault)



--- | GlobalSymbol should correspond to the fully qualified name
--- of a reachable value that is induced UNIQUELY by a module's name and
--- set of dependencies and how it was built.
--- NB: this might be more subtle in the presence of linearity, but lets table that for now
---
--- this may or may not  actually need to just be a functory parametery in the AST
--- but lets keep it simple fo rnow
newtype GlobalSymbol = GlobalSymbol T.Text
  deriving (Eq,Ord,Read,Show,Data,Typeable,Generic)


newtype BinderSlot =
    BinderSlot { unBinderSlot :: Word32 }
  deriving (Eq, Show,Data,Ord,Read,Typeable,Generic)

data LocalNamelessVar =
   LocalNamelessVar {localBinderDepth :: {-# UNPACK #-}  !Word32
           ,localBinderArg :: {-# UNPACK #-}   !BinderSlot
           -- ,  localDebruijnDepth :: {-# UNPACK #-}  !Word64
         }
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic )

-- | VariableCC is either a local env variable or a globally fixed symbol (think like linkers and object code)
-- TODO: later lowering passes will induce register / stack placements and
-- veer into forcing specification of caller/callee saving conventions on code control tranfers
data Variable  =
    LocalVar {-# UNPACK #-} !LocalNamelessVar
    | GlobalVarSym {-# UNPACK #-}  !GlobalSymbol
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic )
type Type = () -- TODO FIXME, wire in the real type info?, which will be TERM :)

data BinderInfo =
      BinderInfoData
        { relevanceBI :: Relevance -- if zero, during evaluation we need not pass around
                                     --  BUT during NORMALIZATION, we probably do
                                     --  so the normalizer WILL thread around irrelevant values
                                     -- to properly support dependent type checking
                                     -- as is proper, because a runtime irrelevant value
                                     -- SHOULD be relevant during type checking, or
                                     -- it has no reason to exist
        , typeBICC :: Type -- at least for now, closure converted stuff may need a
          -- slightly different type system fragment than the Core layer Terms?
          -- NB: once we have existentials, should just be an "equivalent" subset
          -- of the full type theory?
        , sourceInfo :: Maybe Text --- this isn't quite right ...
        -- also should add
          } --- this needs to be fleshed out
  deriving(Eq,Ord,Read,Show,Typeable,Data,Generic)

data Term =
    V  Variable
  | BinderLevelShiftUP Word32 Term  --
  | ELit !Literal
  | Return ![ Term  ] -- explicit multiple return values
                      -- should V x be replaced by Return [x] ?
                      --  once we lower to ANF
                      -- NOTE: for valid expressions,
  | EnterThunk !(Term) -- because we're in a strict IR rep,
                        -- we dont need to provide a seq like operation
                          -- seq a b === let _ := enterThunk a in b

  | Delay !(Term )  --- Delay is a Noop on Thunked values, otherwise creates a Thunked
                    --- note: may need to change their semantics later?!
                    --- Q: is it valid to thunk a thunked value? (no?)
  | App !(Term  )  ![Term  ]  --this is not curried :)
  | PrimApp  !PrimOpId --
             ![Term  ] -- not sure if this is needed, but lets go with it for now

  | Lam ![BinderInfo]
         !Term
  | Let ![BinderInfo]
           Term --- RHS
           Term --- BODY
  deriving ({-Show1,Read1,Ord1,Eq1,-}Ord,Eq,Show,Read{-,Functor,Foldable-},Typeable{-,Traversable-})


--- NOTE: USE STE MONAD ONCE WE MIGRATE TO HSUM DESIGN
--- this is kinda only for "inlining" on debruijin variables for now
substitute :: Word32 -> (BinderSlot  -> Maybe Term) -> Term -> Either (String,Word32) Term
substitute baseLevel initMapper initTerm = goSub 0 initMapper initTerm
  where
    goSub :: Word32 -> (BinderSlot  -> Maybe Term) -> Term -> Either (String,Word32) Term
    goSub shift mapper  var@(V (LocalVar (LocalNamelessVar lnLvl bslt@(BinderSlot lnSlot))))
                |  lnLvl == (shift + baseLevel) =
                        maybe (Left ("bad slot", lnSlot))
                              (Right . BinderLevelShiftUP shift )
                             $ mapper bslt
                | otherwise =  Right var
    goSub _l _m var@(V (GlobalVarSym _ )) = Right var
    goSub shift mapper (Return ls) =  fmap Return $  mapM (goSub shift mapper ) ls
    goSub shift mapper (App fun args) =
          do   funNew <- goSub shift mapper fun
               argsNew <-  mapM (goSub shift mapper) args
               Right (App funNew argsNew)
    goSub shift mapper (Lam binders bod) =
          do   bodNew <- goSub (shift +1 )  mapper bod ; Right (Lam binders bodNew)
    goSub shift mapper (Let binders rhs bod) =
          do  rhsNew <- goSub shift mapper rhs ;
              bodNew <- goSub (shift +1 ) mapper bod ;
              Right (Let binders rhsNew bodNew)
    goSub shift mapper (PrimApp primop args) =
          do  argsNew <- mapM (goSub shift mapper) args
              Right (PrimApp primop argsNew)
    goSub shift mapper (BinderLevelShiftUP posAmt bod)
      | posAmt <= baseLevel + shift  = -- TODO AUDIT THIS TO TILL IT SCREAMS
          do  bodNew <- substitute (baseLevel + shift - posAmt) mapper bod
              Right (BinderLevelShiftUP posAmt bodNew)
      | otherwise = Left ("weird level shift appeared, you've been eaten by a grue", posAmt )
                --- OR WHATTTTTT??!?!?!?!
    goSub shift mapper lit@(ELit _)  = Right lit
    goSub shift mapper (EnterThunk bod ) =  fmap EnterThunk $ goSub shift mapper bod
    goSub shift mapper (Delay bod ) = fmap Delay $ goSub shift mapper bod



{-
            _ _ (BinderLevelShiftUP _ _)
            _ _ (ELit _)
            _ _ (EnterThunk _)
            _ _ (Delay _)

-}
