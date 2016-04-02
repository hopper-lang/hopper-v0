{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Hopper.Internal.LoweredCore.ANF where

import Hopper.Utils.LocallyNameless
import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term

import Data.Maybe (fromMaybe, isJust)
import Data.Monoid (Sum(..), Last(..))
import Data.Word
import Control.Arrow ((&&&), (***))
import Control.Monad (replicateM, join)
import Control.Monad.Trans.State.Strict as State
import Control.Lens hiding (levels)

import qualified Data.Vector as V
import qualified Data.Map.Strict as Map

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
  -- | AnfShift !Word32 !Anf
  deriving (Eq,Ord,Read,Show)

data App
  = AppFun !Variable
           !(V.Vector Variable)
  -- TODO: possibly use parametricity to enable guarantee that only fully-saturated apps exist
  -- | AppPartial Int        -- slots left
  --              -- TODO: add app type (fun vs prim)
  --              [Variable] -- slots filled. new ones are cons'd
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

-- Eventually we might want to collapse lets elaborated from Core->ANF
-- translation into the same level as its containing source-side binder

slot0 :: Word32 -> Variable
slot0 level = LocalVar $ LocalNamelessVar level $ BinderSlot 0

returnAllocated :: Alloc -> Anf
returnAllocated alloc = AnfLet (Arity 1)
                               (RhsAlloc alloc)
                               (AnfReturn $ V.singleton $ slot0 0)

arity :: V.Vector BinderInfo -> Arity
arity binders = Arity $ fromIntegral $ V.length binders

newtype AnfBinder
  = AnfBinder { _binderId :: Word64 }
  deriving (Eq, Show, Ord)
makeLenses ''AnfBinder

instance Enum AnfBinder where
  toEnum = AnfBinder . toEnum
  fromEnum = fromEnum . _binderId

data BindingLevel
  = BindingLevel { _levelRefs :: Map.Map AnfBinder Variable
                   -- ^ References to both existing (i.e. term) and new (i.e.
                   -- intermediate/anf) binders.
                 , _levelIntros :: Word32
                   -- ^ Levels introduced since the last source binder. separate
                   -- from map for now so we can remove items from the map once
                   -- used.
                 , _levelIndirection :: Maybe Variable
                   -- ^ Set when the source binder corresponding to this
                   -- 'BindingLevel' points to an earlier variable. e.g. in
                   -- translating 'Let's with 'V' on the right-hand side, which
                   -- will not have corresponding 'AnfLet's.
                 }
  deriving (Eq, Show)
makeLenses ''BindingLevel

-- The bottom 'BindingLevel' of this stack does not necessarily correspond to a
-- 'Term' binding level (i.e. 'Let' or 'Lam') -- consider a toplevel 'Let' with
-- RHS global var applied to a global var. See 'toAnf'.
type BindingStack = [BindingLevel]

newtype LoweringState
  = LoweringState { _nextBinder :: AnfBinder }
  deriving (Eq, Show)
makeLenses ''LoweringState

-- TODO: possibly wrap with (ReaderT BindingStack) after moving to n-ary apps
type LoweringM = State LoweringState

data Binding
  = TermBinding          -- or ImplicitLet / ExistingLet / ImplicitBinding
  | AnfBinding AnfBinder -- or IntroducedLet / ReifiedBinding / IntroducedBinding / ExplicitBinding
  deriving (Eq, Show)

emptyLevel :: BindingLevel
emptyLevel = BindingLevel (Map.fromList []) 0 Nothing

emptyIndirectionLevel :: Variable -> BindingLevel
emptyIndirectionLevel v = BindingLevel (Map.fromList []) 0 (Just v)

-- | Bumps the provided source variable by the number of intermediate lets that
-- have been introduced since the source binder this variable points to.
translateTermVar :: BindingStack -> Variable -> Variable
translateTermVar _ var@(GlobalVarSym _) = var
translateTermVar stack var@(LocalVar lnv) =
  case mIndirection of
    Nothing ->
      adjust displacement var
    Just indirection ->
      adjust (displacement + depth) indirection

  where
    depth = _lnDepth lnv

    levels :: [BindingLevel]
    levels  = take (fromIntegral $ depth + 1) stack

    -- Calculate the displacement sum (from the number of let-introductions) and
    -- grab the last (possible) indirection in a single pass:
    (displacement, mIndirection) = (getSum *** join . getLast) . mconcat $
      (Sum . _levelIntros &&& Last . Just . _levelIndirection) <$> levels

    adjust :: Word32 -> Variable -> Variable
    adjust offset = over (localNameless.lnDepth) (+ offset)

allocBinder :: LoweringM AnfBinder
allocBinder = do
  curr <- use nextBinder
  nextBinder.binderId %= succ
  return curr

trackVariable :: Binding -> Variable -> BindingStack -> BindingStack
trackVariable (AnfBinding binder) v stack =
  -- addRef binder (translateTermVar stack v) stack
  stack & (_head.levelRefs.at binder) ?~ translateTermVar stack v
trackVariable TermBinding v stack =
  emptyIndirectionLevel (translateTermVar stack v) : stack

-- | Updates the top of the 'BindingStack' to open a new binder for an
-- introduced 'AnfLet', or adds a new 'BindingLevel' for an existing 'Term'
-- 'Let'.
trackBinding :: Binding -> BindingStack -> BindingStack
trackBinding (AnfBinding binder) stack = stack & _head %~ updateLevel
  where
    updateLevel = (levelRefs.at binder                    ?~ slot0 0)
                . (levelRefs.mapped.localNameless.lnDepth +~ 1)
                . (levelIntros                            +~ 1)
trackBinding TermBinding stack = emptyLevel:stack

-- | Closes the provided 'AnfBinder's in 'BindingLevel'.
closeBinders :: [AnfBinder] -> BindingStack -> BindingStack
closeBinders binders stack = stack & _head.levelRefs %~ deleteRefs
  where
    -- TODO: should this be a strict or lazy fold?
    deleteRefs :: Map.Map AnfBinder Variable -> Map.Map AnfBinder Variable
    deleteRefs m = foldr Map.delete m binders

-- | Resolves 'Variables' in 'BindingLevel' for the provided 'AnfBinder's.
-- Assumes the binders are all present in the 'Map' of the 'BindingLevel'.
resolveRefs :: [AnfBinder] -> BindingStack -> [Variable]
resolveRefs binders stack = (varMap Map.!) <$> binders
  where
    varMap = fromMaybe (error "vars map must exist") $ firstOf (_head.levelRefs) stack

--

anfTail :: BindingStack
        -> Term
        -> LoweringM Anf
anfTail stack term = case term of
  V v ->
    return $ AnfReturn $ V.singleton $ translateTermVar stack v

  -- TODO: impl a pass to push shifts down to the leaves and off of the AST
  BinderLevelShiftUP _ _ ->
    error "unexpected binder shift during ANF conversion"

  ELit lit ->
    return $ returnAllocated $ AllocLit lit

  -- TODO: Return

  -- TODO: switch to support of n-ary application
  App ft ats
    | V.length ats == 1 -> do
        let at0 = V.head ats
        appBinders <- replicateM (succ $ V.length ats) allocBinder
        let [fBinder, argBinder0] = appBinders

        anfCont stack ft (AnfBinding fBinder) $ \s1 ->
          anfCont s1 at0 (AnfBinding argBinder0) $ \s2 -> do
            let vars = resolveRefs appBinders s2
            return $ AnfTailCall $ AppFun (head vars) (V.fromList $ tail vars)
    | otherwise ->
        error "TODO: add support for n-ary application in anfTail"

  Lam binderInfos t -> do
    body <- anfTail (emptyLevel : stack) t
    return $ returnAllocated $ AllocLam (arity binderInfos) body

  Let binderInfos rhs body -> do
    -- TODO: use binderInfos
    -- TODO: double-check this
    anfCont stack rhs TermBinding $ \stack' ->
      anfTail stack' body

  -- OLD n-ary attempt:
  --
  -- App fun args ->
  --   anfCont fun $ V.foldr (\term (K () k) ->
  --                           -- This Let we introduce in this K possibly retires
  --                           -- lower variables. TODO: stop tracking them.
  --                           K () $ \rhs ->
  --                             AnfLet (Arity 1)
  --                                    rhs
  --                                    -- If the following anfCont call does more
  --                                    -- than invoke k with a value, then we need
  --                                    -- to bump any binders to the args (and, of
  --                                    -- course, fn) before this one.
  --                                    (anfCont term $ K () k))
  --                         (K () $ \rhs -> -- maybe say this reaches upwards by N. or a stack with one level for each we reach
  --                           let n = V.length args
  --                               -- TODO: this falsely assumes that we
  --                               --       necessarily introduce a new binder for
  --                               --       each of our args
  --                               (fv:avs) = fmap slot0 [n, n-1..0]
  --                               body = AnfTailCall $ AppFun fv (V.fromList avs)
  --                           in AnfLet (Arity 1) rhs body)
  --                         args

-- | The total number of binders in the levels of the first stack not shared by
-- the second stack.
bindersAddedSince :: BindingStack -> BindingStack -> Word32
bindersAddedSince extended base = sum $ height <$> extended `levelsSince` base
  where
    height :: BindingLevel -> Word32
    height level | isJust (_levelIndirection level) = _levelIntros level
                 | otherwise                        = 1 + _levelIntros level

    levelsSince :: BindingStack -> BindingStack -> [BindingLevel]
    levelsSince new old | new == old = []
    levelsSince [] _old = error "first stack must be an extension of the second"
    levelsSince (level : newRest) old = level : (newRest `levelsSince` old)

-- | The former with open binders increased for each extra binder present
-- in the latter. Assumes that the latter is the former extended with extra top
-- 'BindingLevel's.
withIntrosFrom :: BindingStack -> BindingStack -> BindingStack
withIntrosFrom base extended =
  base & _head.levelIntros                            +~ numBinders
       & _head.levelRefs.mapped.localNameless.lnDepth +~ numBinders
  where
    numBinders = extended `bindersAddedSince` base

-- resetStack :: BindingStack -> Binding -> BindingStack -> BindingStack
-- resetStack base binding extended =
--   base & _head.levelIntros +~ (extended `bindersAddedSince` base)
--        & _head.levelRefs.at .... use binding not binder...

anfCont :: BindingStack
        -> Term                            -- ^ The term to be lowered
        -> Binding                         -- ^ The binding to be used, with which future computation will refer to the result
        -> (BindingStack -> LoweringM Anf) -- ^ The action lowering of the rest of the program, awaiting the next binding context
        -> LoweringM Anf                   -- ^ The action which produces lowered ANF for this term
anfCont stack term binding k = case term of
  V v ->
    k $ trackVariable binding v stack

  -- TODO: impl a pass to push shifts down to the leaves and off of the AST
  BinderLevelShiftUP _ _ ->
    error "unexpected binder shift during ANF conversion"

  ELit l -> do
    body <- k $ trackBinding binding stack
    return $ AnfLet (Arity 1)
                    (RhsAlloc $ AllocLit l)
                    body

  -- TODO: Return

  -- TODO: switch to support of n-ary application
  App ft ats
    | V.length ats == 1 -> do
        let at0 = V.head ats
        appBinders <- replicateM (succ $ V.length ats) allocBinder
        let [fBinder, argBinder0] = appBinders

        anfCont stack ft (AnfBinding fBinder) $ \s1 ->
          anfCont s1 at0 (AnfBinding argBinder0) $ \s2 -> do
            let vars = resolveRefs appBinders s2
                app  = AppFun (head vars)
                              (V.fromList $ tail vars)
                s3   = trackBinding binding . closeBinders appBinders $ s2
            body <- k s3
            return $ AnfLet (Arity 1) -- TODO: support tupled return
                            (RhsApp app)
                            body
    | otherwise ->
        error "TODO: support for n-ary application in anfCont"

  Lam binderInfos t -> do
    lamBody <- anfTail (emptyLevel : stack) t
    letBody <- k $ trackBinding binding stack
    return $ AnfLet (Arity 1)
                    (RhsAlloc $ AllocLam (arity binderInfos)
                                         lamBody)
                    letBody

  Let binderInfos rhs body -> do
    -- -- TODO: this is wrong. fix it. `withIntrosWith` should be used for K's work -- not for the let body yet.
    -- anfCont stack rhs TermBinding $ \stack' -> do
    --   anfCont (stack `withIntrosFrom` stack') body binding k
    --
    anfCont stack rhs TermBinding $ \s1 ->
      anfCont s1 body binding $ \s2 ->  -- FIXME: this is using binding, but then we throw the stack away
        k $ (stack `withIntrosFrom` s2) -- This util fn could replay use of
                                        -- binding... which might be gross. or
                                        -- we could introduce a new type of
                                        -- (Deferred?)Binding, which bottles-up
                                        -- a continuation and sticks it in a
                                        -- special field in the stack?
        -- TODO: how would replaying a binding (whether manually or with a cont)
        --       interact with # of intros we take from the levels differential?
        --
        -- TODO: perhaps if we go the DeferredBinding approach, we might want
        --       to calculate the number of intros at the same time that the deferred
        --       is constructed.
        --
        -- TODO: play with the idea of making modifications to the stack explicit,
        --       either as code (a cont) or data. and pass this modification to
        --       K instead of the new stack. and leave it up to the caller of
        --       anfCont to use this stack transformer as they please.
        --         It seems this would rule out the use of moving Reader into
        --         LoweringM.

toAnf :: Term -> Anf
toAnf t = evalState (anfTail emptyStack t) initialState
  where
    -- We provide a bottom level that doesn't correspond to a toplevel term
    -- 'Let' or 'Lam' so that e.g. a toplevel 'Let' with a non-trivial RHS has
    -- a level with which to introduce intermediary 'AnfLet's
    emptyStack = [emptyLevel]
    initialState = LoweringState $ AnfBinder 0

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

-- TODO: alloc (vs init) vars
-- TODO: track amount to bump outer level / and bump
-- TODO: make sure we are always removing things from the BindingLevel map (at usage sites)
--         or at least in the anfCont cases, where we pass the stack to k
--
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
