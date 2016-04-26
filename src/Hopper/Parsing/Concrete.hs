{-# LANGUAGE OverloadedStrings #-}
module Hopper.Parsing.Concrete where

import Control.Lens (over)
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.Vector as V

import Hopper.Internal.Core.Literal
import qualified Hopper.Internal.Core.Term as Tm
import Hopper.Internal.Type.BinderInfo (BinderInfo(BinderInfoData))
import Hopper.Internal.Type.Relevance (Relevance(Omega))
import Hopper.Utils.LocallyNameless

data NumericType
  = IntTy
  -- | NatTy
  | RatTy
  deriving (Show, Eq, Ord, Read)

newtype ConcreteOpId = ConcreteOpId T.Text deriving (Show, Eq, Ord, Read)

data Concrete =
  Var !T.Text
  | StrLit !T.Text
  | NumericLit !(Either Integer Double)
  -- explicit multiple return values
  | Return !Concrete
  | EnterThunk !Concrete
  | Delay !Concrete
  | App !Concrete !(V.Vector Concrete)
  | PrimApp !ConcreteOpId !(V.Vector Concrete)
  | Lam !(V.Vector T.Text) !Concrete
  | Let !(V.Vector T.Text)
        -- | RHS
        !Concrete
        -- | Body
        !Concrete
  deriving (Show, Eq, Ord, Read)

toPrimOpId :: ConcreteOpId -> PrimOpId
toPrimOpId (ConcreteOpId opId) = TotalMathOpGmp $ case opId of
  "+" -> IntAddOpId
  "+." -> RatAddOpId
  "-" -> IntSubOpId
  "-." -> RatSubOpId
  "*" -> IntMultOpId
  "*." -> RatMultOpId
  _ -> error "primop not yet implemented"

toBinderInfo :: T.Text -> BinderInfo
toBinderInfo str = BinderInfoData Omega () (Just str)

-- Walk the concrete syntax tree, transforming it to our abstract syntax. This
-- transformation is straightforward, except for variable binding.
--
-- We walk the tree from top to bottom, maintaining a mapping from (Text)
-- variable names to their (LocallyNamelessVar) binders.
concreteToAbstract :: Concrete -> Tm.Term
concreteToAbstract = concreteToAbstract' Map.empty

goInsideBinder :: V.Vector T.Text
               -> Map.Map T.Text LocalNamelessVar
               -> Map.Map T.Text LocalNamelessVar
goInsideBinder newVars varLookup =
      -- bump the depth of all the existing binders
  let bumped = Map.map (over lnDepth (+1)) varLookup

      -- create a map from the variable name to its (bound) locally nameless
      -- var at depth 0
      lnVars = V.imap
        (\i v -> (v, LocalNamelessVar 0 (BinderSlot (fromIntegral i))))
        newVars
      lnVarMap = Map.fromList $ V.toList lnVars

  -- merge the bumped old map with the new variables we're binding
  in Map.union lnVarMap bumped

concreteToAbstract' :: Map.Map T.Text LocalNamelessVar -> Concrete -> Tm.Term
concreteToAbstract' varLookup tm = case tm of
  Var str -> case Map.lookup str varLookup of
    Nothing -> Tm.V $ GlobalVarSym $ GlobalSymbol $ str
    Just bound -> Tm.V $ LocalVar bound
  StrLit str -> Tm.ELit $ LText $ str
  NumericLit (Left i) -> Tm.ELit $ LInteger $ i
  NumericLit (Right d) -> Tm.ELit $ LRational $ toRational d
  -- TODO(joel) LNatural case?
  Return t -> Tm.Return $ V.singleton $ concreteToAbstract' varLookup t
  EnterThunk t -> Tm.EnterThunk $ concreteToAbstract' varLookup t
  Delay t -> Tm.Delay $ concreteToAbstract' varLookup t
  App f args -> Tm.App
    (concreteToAbstract' varLookup f)
    (V.map (concreteToAbstract' varLookup) args)
  PrimApp opId args ->
    Tm.PrimApp (toPrimOpId opId) (V.map (concreteToAbstract' varLookup) args)
  Lam binders t -> Tm.Lam
    (V.map toBinderInfo binders)
    (concreteToAbstract' (goInsideBinder binders varLookup) t)
  Let binders rhs body -> Tm.Let
    (V.map toBinderInfo binders)
    (concreteToAbstract' varLookup rhs)
    (concreteToAbstract' (goInsideBinder binders varLookup) body)
