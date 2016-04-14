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

import Data.Foldable (foldl')
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
-- Conversion to ANF begins with a single empty 'BindingLevel' (not an empty
-- 'BindingStack').
--
-- In converting the following (pseudo 'Term') program,
--
-- @
-- let f = λy. add 1 (sub y 20)
-- in f 10
-- @
--
-- we (start) run(ning) ANF conversion as follows:
-- 0. start converting the entire (tail position) 'Let', with the single empty
--    'BindingLevel'.
-- 1. start converting the (non-tail) lambda on the 'Let' RHS, with the single
--    empty 'BindingLevel'. as we pass into the lambda, we push a 'BindingLevel'
--    onto the stack because 'Lam' induces a new binding scope in the 'Term'
--    program.
-- 2. start converting the (tail) @add ...@ application with the stack of size
--    2, allocating (but not yet "tracking") an 'AnfRef' for each of the
--    variables we'll need when drop an 'AnfTailCall' for this app in the
--    future.
-- 3. start converting the (non-tail) @add@ global var; leave it as-is.
-- 4. upon encountering the (non-tail) literal @1@, we introduce an 'AnfLet'
--    which allocates the literal on the RHS. As we introduce this 'AnfLet',
--    (via 'trackBinding') we:
--    - increment @_levelIntros@ in our 'BindingLevel'. this will be useful when
--    we encounter the future variable @y@, because this let-introduction will
--    necessitate that this source variable be bumped.
--    - bump all references to "ANF variables" (from intro'd lets, as opposed to
--    existing 'Term' 'Variable's) that are "open", or being "tracked" in
--    @_levelRefs@.
--    - start tracking the 'AnfRef' for the future ANF variable that refers to
--    this allocated literal. we start "tracking" because any futher-introduced
--    'AnfLet's between here and our variable usage in the app will call for
--    bumps to the variable.
-- 5. start converting the (non-tail) @sub ...@ application with the stack of
--    size 2.
-- 6. upon encountering @y@ we see that it points 0 'Term' binding levels up, so
--    we will look at (0 + 1) binding levels (namely, only the top level) in our
--    stack, and increase @y@'s depth by the total number of @_levelIntros@
--    across these 'BindingLevel's.
-- ...
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
--
-- Instead of using Reader to thread 'BindingStack' state around, we could
-- pass around explicit stacks through @convert*@ and continuations; but by
-- using explicit /transformations/ (with `local`) we eliminate bugs pertaining
-- to the use of an incorrect stack variable. Additionally this current design
-- is more amenable to a move to the use of @Cont@, if we decide to go that
-- route.
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
    addRefs m = foldl' (flip $ uncurry Map.insert) m $ zip refs vars
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
    addRefs m = foldl' (\m' ref -> Map.insert ref v0 m') m refs
trackBinding TermBinding stack = emptyLevel:stack

-- | Stops tracking the provided 'AnfRef's in the top 'BindingLevel' of
-- 'BindingStack'.
dropRefs :: Foldable t => t AnfRef -> BindingStack -> BindingStack
dropRefs refs stack = stack & _head.levelRefs %~ deleteRefs
  where
    deleteRefs m = foldl' (flip Map.delete) m refs

-- | Resolves 'Variables' in 'BindingLevel' for the provided 'AnfRef's. Assumes
-- the refs are all present in the 'Map' of the 'BindingLevel'.
resolveRefs :: (Foldable t, Functor t)
            => t AnfRef
            -> BindingStack
            -> t Variable
resolveRefs refs stack = (varMap Map.!) <$> refs
  where
    varMap = fromMaybe (error "unexpected binding stack underrun") $
      firstOf (_head.levelRefs) stack

-- | This is what we currently use to represent a deferred transformation to
-- 'BindingStack' (from the use of 'trackVariables' or 'trackBinding') for the
-- 'convertWithCont' callee to invoke. We typically call it immediately in the
-- continuation, except in the 'Let' case, where we need to roll back the stack
-- before applying the transform.
type StackTransform = BindingStack -> BindingStack

-- | Lowering a sequence of "sibling" 'Term's, and providing 'Variable's for the
-- lowering of the rest of the program. This function helps remove boilerplate
-- from our two main functions, 'convertTail' and 'convertWithCont' in
-- situations where they need to convert multiple terms from left-to-right (e.g.
-- in the case of function application).
--
-- The expression 'convertToVars [fun, arg0, arg1] synthesize' will expand to
-- something like:
--
-- @
-- [funRef, arg0Ref, arg1Ref] <- replicateM 3 allocRef
--
-- local id $ convertWithCont fun (AnfBinding [funRef]) $ \trackFun ->
--   local trackFun $ convertWithCont arg0 (AnfBinding [arg0Ref]) $ \trackArg0 ->
--     local trackArg0 $ convertWithCont arg1 (AnfBinding [arg1Ref]) $ \trackArg1 ->
--       local trackArg1 $ do
--         vars <- reader resolveRefs [funRef, arg0Ref, arg1Ref]
--         let cleanup = dropRefs refs
--         synthesize vars cleanup
-- @
--
-- where 'synthesize' will provide the body of the inner-most continuation.
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

  BinderLevelShiftUP _ _ ->
    -- TODO: expose this using proper error machinery
    error "unexpected binder shift in convertTail during ANF conversion"

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

  Let _binderInfos rhs body ->
    -- TODO: use binderInfos when we moved to type-directed?
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

  BinderLevelShiftUP _ _ ->
    -- TODO: expose this using proper error machinery
    error "unexpected binder shift in convertWithCont during ANF conversion"

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
  Let _binderInfos rhs body -> do
    -- TODO: use binderInfos when we moved to type-directed?
    beforeStack <- ask
    convertWithCont rhs TermBinding $ \trackRhs ->
      local trackRhs $ convertWithCont body binding $ \trackBody ->
        let rollback letStack = beforeStack `withBinderIncreasesPer` letStack
        in local rollback $ k trackBody

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
