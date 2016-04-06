{-# LANGUAGE TemplateHaskell #-}

----------------------------------------------------------------------------
-- |
-- This module defines an Administrative Normal Form (ANF) representation of a
-- Hopper abstract syntax tree, 'Anf'. In ANF, only simple allocations or
-- applications can occur on the right-hand side of a 'Let'. This is similar to
-- an SSA or CPS form.
--
-- The function 'toAnf' lowers a 'Term' AST to 'Anf'. This is achieved by an
-- adaptation of Olivier Danvy's algorithm from "A New One-Pass Transformation
-- into Monadic Normal Form" (2002) to our 2D De Bruijn 'Variable'
-- representation.
----------------------------------------------------------------------------

module Hopper.Internal.LoweredCore.ANF
  (
  -- * Data Types
    Arity(..)
  , Anf(..)
  , App(..)
  , Alloc(..)
  , Rhs(..)

  -- * Lowering to ANF
  , toAnf
  ) where

import Hopper.Utils.LocallyNameless
import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term

import Data.Foldable (foldr')
import Data.Maybe (fromMaybe, isJust)
import Data.Monoid (Sum(..), Last(..))
import Data.Word
import Control.Arrow ((&&&), (***))
import Control.Monad (replicateM, join)
import Control.Monad.Trans.Reader (ReaderT, runReaderT, ask, local, reader)
import Control.Monad.Trans.State.Strict (State, evalState)
import Control.Lens hiding (levels)

import qualified Data.Vector as V
import qualified Data.Map.Strict as Map

--------------------------
-- Data Types
--------------------------

-- TODO: possibly allow more "atomic" expression types (besides variables) once
--       we have some unboxed values

-- Eventually we might want to collapse lets elaborated from Core->ANF
-- translation into the same level as its containing source-side binder

-- TODO: switch back away from this
newtype Arity = Arity Word32 deriving (Eq,Ord,Read,Show)

data Anf
  = AnfReturn !(V.Vector Variable) -- indices into the current env stack
  | AnfLet !Arity -- TODO: switch back to !(V.Vector BinderInfo)
           -- !(Maybe SourcePos)
           !Rhs
           !Anf
  | AnfTailCall !App
  deriving (Eq,Ord,Read,Show)

data App
  = AppFun !Variable
           !(V.Vector Variable)
  | AppPrim !PrimOpId !(V.Vector Variable)
  | AppThunk !Variable
  deriving (Eq,Ord,Read,Show)

data Alloc
  = AllocLit !Literal
  | AllocLam !Arity -- TODO: switch back to !(V.Vector BinderInfo)
             !Anf
  | AllocThunk !Anf
  deriving (Eq,Ord,Read,Show)

data Rhs
  = RhsAlloc !Alloc
  | RhsApp !App
  deriving (Eq,Ord,Read,Show)

--------------------------
-- Lowering to ANF
--------------------------

-- | The first slot in the most recent binder
v0 :: Variable
v0 = LocalVar $ LocalNamelessVar 0 $ BinderSlot 0

-- | A temporary function to produce an 'Arity' for our ANF binding forms until
-- we switch to using 'BinderInfo's in 'Anf' as well.
arity :: V.Vector BinderInfo -> Arity
arity binderInfos = Arity $ fromIntegral $ V.length binderInfos

-- | A linear (single-use) reference to a(n existing/term or new/anf) binder. If
-- two source variables refer to the same binder, they are tracked via separate
-- 'AnfRef's.
newtype AnfRef
  = AnfRef { _refId :: Word64 }
  deriving (Eq, Show, Ord)

makeLenses ''AnfRef

instance Enum AnfRef where
  toEnum = AnfRef . toEnum
  fromEnum = fromEnum . _refId

-- | Bookkeeping structure that corresponds to a binder scope in the 'Term' AST.
data BindingLevel
  = BindingLevel { _levelRefs :: Map.Map AnfRef Variable
                 -- ^ Linear references (to both existing/term and new/anf
                 -- binders) to the 'Variable's they will be realized as when
                 -- used. These variables are bumped as new 'AnfLet's are
                 -- introduced.
                 , _levelIntros :: Word32
                 -- ^ Levels introduced since the last source binder. We keep
                 -- this in addition to _levelRefs because we remove refs from
                 -- the map once they've been used.
                 , _levelIndirections :: Maybe (V.Vector Variable)
                 -- ^ Set when the source binder(s) corresponding to this
                 -- 'BindingLevel' point to an earlier variable. e.g. in
                 -- translating 'Let's with 'V' or a 'Return' on the right-hand
                 -- side, which will not have corresponding 'AnfLet's.
                 }
  deriving (Eq, Show)

makeLenses ''BindingLevel

emptyLevel :: BindingLevel
emptyLevel = BindingLevel Map.empty 0 Nothing

emptyIndirectionLevel :: [Variable] -> BindingLevel
emptyIndirectionLevel vars = BindingLevel Map.empty 0 (Just $ V.fromList vars)

-- The bottom 'BindingLevel' of this stack does not necessarily correspond to a
-- 'Term' binding level (i.e. 'Let' or 'Lam') -- consider a toplevel 'Let' with
-- RHS global var applied to a global var. See 'toAnf'.
type BindingStack = [BindingLevel]

newtype LoweringState
  = LoweringState { _nextRef :: AnfRef
                  -- ^ The next 'AnfRef' to track an existing or new variable
                  -- usage.
                  }
  deriving (Eq, Show)

makeLenses ''LoweringState

-- | Monad transformer stack for lowering from 'Term' to 'Anf'.
type LoweringM = ReaderT BindingStack (State LoweringState)

-- | Dispenses an 'AnfRef' to track the usage of a 'Term' or newly-introduced
-- ("anf") variable to let-name a subexpression.
allocRef :: LoweringM AnfRef
allocRef = do
  curr <- use nextRef
  nextRef.refId %= succ
  return curr

-- | In converting a 'Term' to ANF, specifies whether the allocated value or
-- result of (prim/fun/thunk) application should be bound to an 'AnfLet'
-- corresponding to an existing ('Let') 'TermBinding' or a new 'AnfBinding'.
data Binding
  = TermBinding
  | AnfBinding [AnfRef] -- A list because we use unboxed tuples and 2D binders.
  deriving (Eq, Show)

-- | Bumps the provided source variable by the number of intermediate lets that
-- have been introduced since the source binder this variable points to.
translateTermVar :: Variable -> BindingStack -> Variable
translateTermVar var@(GlobalVarSym _) _ = var
translateTermVar var@(LocalVar lnv) stack =
  case mIndirections of
    Nothing ->
      adjust displacement var
    Just indirections ->
      adjust (displacement + depth) $ indirections V.! slot

  where
    depth = lnv ^. lnDepth
    slot  = lnv ^. lnSlot.slotIndex.to fromIntegral

    levels :: [BindingLevel]
    levels  = take (fromIntegral $ depth + 1) stack

    -- Calculate the displacement sum (from the number of let-introductions) and
    -- grab the last (possible) indirection in a single pass:
    (displacement, mIndirections) = (getSum *** join . getLast) . mconcat $
      (Sum . _levelIntros &&& Last . Just . view levelIndirections) <$> levels

    adjust :: Word32 -> Variable -> Variable
    adjust offset = localNameless.lnDepth +~ offset

-- | Updates the top of the 'BindingStack' to account for the existing
-- (pre-translated) 'Term' 'Variable's.
trackVariables :: Binding
               -> [Variable]
               -- ^ Existing source variables that've already been translated to
               -- point an appropriate number of binders up in ANF land.
               -> BindingStack
               -> BindingStack
trackVariables (AnfBinding refs) vars stack =
  stack & _head.levelRefs %~ addRefs
  where
    addRefs m = foldr' (uncurry Map.insert) m $ zip refs vars
trackVariables TermBinding vars stack =
  emptyIndirectionLevel vars : stack

-- | Updates the top of the 'BindingStack' to open a new 'AnfRef' for an
-- introduced 'AnfLet', or adds a new 'BindingLevel' for an existing 'Term'
-- 'Let'.
trackBinding :: Binding -> BindingStack -> BindingStack
trackBinding (AnfBinding refs) stack = stack & _head %~ updateLevel
  where
    updateLevel = (levelRefs                              %~ addRefs)
                . (levelRefs.mapped.localNameless.lnDepth +~ 1)
                . (levelIntros                            +~ 1)
    addRefs m = foldr' (uncurry Map.insert) m $ zip refs (repeat v0)
trackBinding TermBinding stack = emptyLevel:stack

-- | Stops tracking the provided 'AnfRef's in the top 'BindingLevel' of
-- 'BindingStack'.
dropRefs :: Foldable t => t AnfRef -> BindingStack -> BindingStack
dropRefs refs stack = stack & _head.levelRefs %~ deleteRefs
  where
    deleteRefs m = foldr' Map.delete m refs

-- | Resolves 'Variables' in 'BindingLevel' for the provided 'AnfRef's. Assumes
-- the refs are all present in the 'Map' of the 'BindingLevel'.
resolveRefs :: (Foldable t, Functor t)
            => t AnfRef
            -> BindingStack
            -> t Variable
resolveRefs refs stack = (varMap Map.!) <$> refs
  where
    varMap = fromMaybe (error "vars map must exist") $
      firstOf (_head.levelRefs) stack

-- | This is what we currently use to represent a deferred transformation to
-- 'BindingStack' (from the use of 'trackVariables' or 'trackBinding') for the
-- 'convertWithCont' callee to invoke. We typically call it immediately in the
-- continuation, except in the 'Let' case, where we need to roll back the stack
-- before applying the transform.
type StackTransform = BindingStack -> BindingStack

-- | Lowering a sequence of "sibling" 'Term's, and providing 'Variable's for the
-- lowering of the rest of the program.
convertToVars :: [Term]
              -- ^ A sequence of 'Terms' to lower in order, e.g. for prim or
              -- function or thunk application, or returning multiple values.
              -> ([Variable] -> StackTransform -> LoweringM Anf)
              -- ^ Continuation for synthesizing the lowering for the rest of
              -- the program from 'Variable's for each of the terms and a
              -- 'StackTransform' for cleaning up the 'AnfRef's that tracked the
              -- 'Variable's.
              -> LoweringM Anf
convertToVars terms synthesize = do
  refs <- replicateM (length terms) allocRef

  -- NOTE: To see how we could simplify this function, see notes on the 'Let'
  -- case of 'convertWithCont' regarding the possibility of using @ContT@. The
  -- fold in this function would become first-order.
  id &
    foldr (\(t, ref) nextK ->
            \track ->
              local track $ convertWithCont t (AnfBinding $ pure ref) nextK)
          (\track ->
            local track $ do
              vars <- reader $ resolveRefs refs
              let cleanup = dropRefs refs
              synthesize vars cleanup)
          (zip terms refs)

-- | A convenience function for placing a tail 'Alloc'ation on the RHS of a new
-- 'AnfLet' and 'AnfReturn'ing that value.
returnAllocated :: Alloc -> Anf
returnAllocated alloc = AnfLet (Arity 1)
                               (RhsAlloc alloc)
                               (AnfReturn $ V.singleton v0)

-- | A convenience function for converting a 'Lam'- or 'Delay'-guarded RHS of a
-- 'AnfLet'.
convertGuarded :: Term -> LoweringM Anf
convertGuarded t = local (emptyLevel:) $ convertTail t

-- | Converts a 'Term' in tail position to ANF. This function corresponds to
-- Danvy's function "E".
convertTail :: Term -> LoweringM Anf
convertTail term = case term of
  V v -> do
    translatedVar <- reader $ translateTermVar v
    return $ AnfReturn $ V.singleton translatedVar

  -- TODO: impl a pass to push shifts down to the leaves and off of the AST
  BinderLevelShiftUP _ _ ->
    error "unexpected binder shift during ANF conversion"

  ELit lit ->
    return $ returnAllocated $ AllocLit lit

  Return terms ->
    convertToVars (V.toList terms) $ \vars _cleanup ->
      return $ AnfReturn $ V.fromList vars

  EnterThunk t ->
    convertToVars [t] $ \[var] _cleanup ->
      return $ AnfTailCall $ AppThunk var

  Delay t -> do
    body <- convertGuarded t
    return $ returnAllocated $ AllocThunk body

  App ft ats -> do
    let terms = ft : V.toList ats
    convertToVars terms $ \vars _cleanup ->
      return $ AnfTailCall $ AppFun (head vars)
                                    (V.fromList $ tail vars)

  PrimApp primId terms ->
    convertToVars (V.toList terms) $ \vars _cleanup ->
      return $ AnfTailCall $ AppPrim primId $ V.fromList vars

  Lam binderInfos t -> do
    body <- convertGuarded t
    return $ returnAllocated $ AllocLam (arity binderInfos) body

  Let binderInfos rhs body ->
    -- TODO: use binderInfos
    convertWithCont rhs TermBinding $ \trackRhs ->
      local trackRhs $ convertTail body

-- | The total number of binders in the levels of the first stack not shared by
-- the second stack.
bindersAddedSince :: BindingStack -> BindingStack -> Word32
bindersAddedSince extended base = sum $ height <$> extended `levelsSince` base
  where
    height :: BindingLevel -> Word32
    height level | isJust (_levelIndirections level) = _levelIntros level
                 | otherwise                         = 1 + _levelIntros level

    levelsSince :: BindingStack -> BindingStack -> [BindingLevel]
    levelsSince new old | new == old = []
    levelsSince [] _old = error "first stack must be an extension of the second"
    levelsSince (level : newRest) old = level : (newRest `levelsSince` old)

-- | The former with open binders increased for each extra binder present
-- in the latter. Assumes that the latter is the former extended with extra top
-- 'BindingLevel's.
withBinderIncreasesPer :: BindingStack -> BindingStack -> BindingStack
withBinderIncreasesPer base extended =
  base & _head.levelIntros                            +~ numBinders
       & _head.levelRefs.mapped.localNameless.lnDepth +~ numBinders
  where
    numBinders = extended `bindersAddedSince` base

-- | Converts a 'Term' in nontail position to ANF. This function corresponds to
-- Danvy's function "E_c".
convertWithCont :: Term
                -- ^ The term to be lowered
                -> Binding
                -- ^ The binding to be used, with which future computation will
                -- refer to the result
                -> (StackTransform -> LoweringM Anf)
                -- ^ The continued lowering of the rest of the program, awaiting
                -- a transformation to update the 'BindingStack'.
                -> LoweringM Anf
                -- ^ The action which produces lowered ANF for this term
convertWithCont term binding k = case term of
  V v -> do
    translatedVar <- reader $ translateTermVar v
    k $ trackVariables binding [translatedVar]

  -- TODO: impl a pass to push shifts down to the leaves and off of the AST
  BinderLevelShiftUP _ _ ->
    error "unexpected binder shift during ANF conversion"

  ELit l -> do
    body <- k $ trackBinding binding
    return $ AnfLet (Arity 1)
                    (RhsAlloc $ AllocLit l)
                    body

  Return terms ->
    convertToVars (V.toList terms) $ \vars cleanupRefs ->
      case binding of
        TermBinding ->
          k $ trackVariables binding vars . cleanupRefs
        (AnfBinding _) ->
          -- TODO: expose this using proper error machinery
          error "unexpected non-tail Return outside of a Let RHS"

  EnterThunk t ->
    convertToVars [t] $ \[var] cleanupRef -> do
      body <- k $ trackBinding binding . cleanupRef
      return $ AnfLet (Arity 1) -- TODO: support tupled return
                      (RhsApp $ AppThunk var)
                      body

  Delay t -> do
    thunkBody <- convertGuarded t
    letBody <- k $ trackBinding binding
    return $ AnfLet (Arity 1)
                    (RhsAlloc $ AllocThunk thunkBody)
                    letBody

  App ft ats -> do
    let terms = ft : V.toList ats
    convertToVars terms $ \vars cleanupRefs -> do
      body <- k $ trackBinding binding . cleanupRefs
      return $ AnfLet (Arity 1) -- TODO: support tupled return
                      (RhsApp $ AppFun (head vars)
                                       (V.fromList $ tail vars))
                      body

  PrimApp primId terms ->
    convertToVars (V.toList terms) $ \vars cleanupRefs -> do
      body <- k $ trackBinding binding . cleanupRefs
      return $ AnfLet (Arity 1) -- TODO: support tupled return
                      (RhsApp $ AppPrim primId $ V.fromList vars)
                      body

  Lam binderInfos t -> do
    lamBody <- convertGuarded t
    letBody <- k $ trackBinding binding
    return $ AnfLet (Arity 1)
                    (RhsAlloc $ AllocLam (arity binderInfos)
                                         lamBody)
                    letBody

  -- NOTE: This is the one situation where we need to "roll-back" a
  --       'BindingStack' (and apply appropriate binder increases to an earlier
  --       stack) *before* invoking a "track" ('StackTransform') to update its
  --       bindings.
  --
  --       It's because of this single special case that we pass the
  --       'StackTransform' to the caller of 'convertWithCont' via a
  --       continuation (instead of having the callee simply update the bindings
  --       using 'local' when it invokes @k@).
  --
  --       We could perhaps improve this situation by:
  --       - Always saving the previous 'BindingStack' and the 'StackTransform'
  --       to update bindings before invoking @k@.
  --       - Move to using @ContT@ (which would have the nice side effect of
  --       un-CPS'ing our code) and roll back via @callCC@ or delimited
  --       continuation machinery (@shift@ and @reset@). It's natural to convert
  --       'convertWithCont' to @ContT@ but not as obvious how 'convertTail'
  --       should change. Should the functions continue to operate in the same
  --       @Monad@, with 'convertTail' taking a dummy continuation, or should
  --       all calls to 'convertWithCont' from 'convertTail' call @runCont@?
  --
  Let binderInfos rhs body -> do
    stackBefore <- ask
    convertWithCont rhs TermBinding $ \trackRhs ->
      local trackRhs $ convertWithCont body binding $ \trackBody ->
        local (stackBefore `withBinderIncreasesPer`) $ k trackBody

-- | Converts a 'Term' to Administrative Normal Form.
toAnf :: Term -> Anf
toAnf term = evalState (runReaderT (convertTail term) emptyStack) initialState
  where
    -- We provide a initial bottom level of the 'BindingStack' that doesn't
    -- correspond to a toplevel term 'Let' or 'Lam' so that e.g. a toplevel
    -- 'Let' with a non-trivial RHS has a level with which to introduce
    -- intermediary 'AnfLet's.
    emptyStack = [emptyLevel]
    initialState = LoweringState $ AnfRef 0

--------------------------
-- Some Earlier Notes
--------------------------

-- 3/18/16
-- no more shifts
-- we should distinguish between term and anf variables
--   either different types (e.g. newtype wrapping) or completely different handling (see ANF Variables, below)
-- when we're dealing with source variables, we bump by the number of lets introduced between source binding levels, and since the last source binding level
--   we can do this by maintaining a stack of # lets introduced per level
-- when dealing with anf variables, we bump by the number of lets introduced since its binder
--     some of these lets could actually be source lets -- consider nested/non-tail lets (add 1 (let x=2 in x) 3)
--   key insight here: each introduced let is only used once!
--   we could keep state for anf variables. succ each temp variable as we add successive temp vars
--     due to vars only used once, we know when to retire them (also everything will be retired upon next source binder)
--   if these temp/anf vars are tracked via state, we could generate these vars
--     a priori for use in n-ary application, but we need to care to not bump all of them the same amount.
--       we might want to allocate up-front, and then only start tracking once we are further along, in nested Ks
--   need to efficiently (1) bump all of the anf vars opened (and not yet used) in the current binding level (for this "spine"; i.e. don't bump anf vars for other nested lets)?
--                           - keep in mind that earlier ones will be bumped more often than later ones
--              and also (2) allow for efficient update and removal by some id?
--   - probably just use data.map/intmap for quick insert/read/delete, and eat the O(n*logn) for bumping all vars?
--   - it seems like we can use a separate intmap for temp/anf vars per binding level
--       and when we come back to a lower spine from e.g. a nested let, we can batch bump all anf vars in the
--       intmap by the number of levels that were introduced by this other nested/non-tail let.
--
-- 3/19/16
-- need to figure out how to unify representations for binding levels and and these nested/non-tail situations
--     that can contain multiple binding levels that need to be rolled back simultaneously
--   example:       let x=50 in add 10 (let f = lam... in f x) x
--   anf expansion: letT 50
--                  in   letA 10
--                       in   letT lam...                \ these two lines are for the nested
--                            in   letA (0) (2)          / let and affect our add's first arg
--                                 in   add (2) (0) (3)  - the x (3) here is translated from (0)
--                                                         and must not be thrown-off by the
--                                                         nested letT
--
-- 3/25/16
-- for non-tail/nested expressions (which can go arbitrarily deep), we need to
--     either bump the previous "level" when "rolling back", or be bumping these
--     outer scopes at all times, with no special behavior on "rollback".
--
-- we should consider cases like:
--     let
--     let
--          let
--          let
--               let
--                    lam <- this, wrapping a tail call, is a bump "firewall"
--                    let
--                         let
--                              let
--               let
--          let
--          let
--     let
--
-- in using ReaderT for our stack, we are using haskell's implicit control stack
--   how do things change with an explicit stack?
--     is it easier to calculate the extent to which the previous level should be bumped, on rollback?
--     or maybe our K could return a tuple around Anf with this bump info?
--         (or is *this* where it makes sense to wrap K with a newtype?)
--       and then we could stick with the reader (or cont?)!
--
-- we should probably start with a very simple model, and, once we have things
--     working, see how things like ContT can possibly fit into the mix.

--
-- add 10 (sub 30 5) 20
--
-- letA 10
-- in   letA 30
--      in   letA 5
--           in   letA sub (1) (0)
--                in   letA 20
--                     in   add (4) (1) (0)
--
-- 3/30/16
-- we should add support n-ary app before switching over to ReaderT
--
-- 3/31/16
-- Once we move to reader, our K becomes (() -> LoweringM Anf). At that point,
-- it seems we can just move to (using 'local' and) sequencing monadic actions.
--
-- 4/3/16
-- Reader could be over '(BindingStack, StackTransform)' instead of just
--     'BindingStack', and toplevel convertWithCont could be invoked from the outside
--     with 'id' for the transform
--   Though this might work against moving this to Cont -- where
--       'StackTransform' is the 'a' in the 'a -> r' K that 'convertWithCont' (a
--       suspended computation) takes
-- Consider always passing e.g. 'f1 s1', but then stash a pre-transformed (i.e.
--     with the use of 'f1') stack in a continuation (maybe using 'callCC') and
--     keep that in the state or reader env for the special rollback case.
--
-- Could be interesting to play with delimited continuation operators for
--     nontail let rollbacks.

-- the types seem to line-up to convert convertWithCont to ContT. can we get convertTail
-- to work in ContT as well, or would calls of convertWithCont from convertTail all
-- have to use 'evalContT'?
