{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Hopper.Internal.LoweredCore.ANF where

import Hopper.Utils.LocallyNameless
import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term

import Data.Maybe (fromMaybe)
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

-- -- core
-- \x. sub 1 let y = 5
--           in mult y (add 10 x)
--
-- -- debruijn
--
-- lam
--    sub 1 letS 5
--          in mult (0) (add 10 (1))
--
--
-- anf (shifted):
--
-- lam
--    let alloc 1
--    in  SHIFT
--        letS alloc 5
--        in   let alloc 10
--             in  SHIFT
--                 let add (-1) (1)
--                 in  SHIFT
--                     let mult ...
--
-- anf (without shifts):
--
-- lam
--    let alloc 1              -- <-- naming
--    in let* alloc 5
--       in let alloc 10       -- <-- naming
--          in let add (0) (3) -- used to be add _ (1)
--             in let mult (2) (0)
--                in sub (4) (0)
--
--
--
-- -- core
-- let comp = lam ...
-- in let f = lam ...
--    in let abs = lam ...
--       in let g = lam ...
--          in  (comp f g) (abs 10) 5
--
-- -- anf
--
-- let lam ... -- comp
-- in  let lam ... -- f
--     in  let lam ... -- abs
--         in  let lam ... -- g
--             in  ---------------------------
--                 let (3) (2) (0) -- comp f g
--                 in  let alloc 10             -- <-- this sub-expr bumps compFG binding
--                     in  let abs (0)
--                         in  let alloc 5
--                             in  (3) (1) (0) -- (comp f g) (abs 10) 5
--
--
-- debruijn:
--
-- letX add 1 2
-- in   letY add (0) 20
--      in   letZ add 50 (add (2) (0))
--           in   (add (add (1) (2)) (0))
--
-- anf (debruijn):
--
-- let 1
-- in  let 2
--     in  letX add (1) (0)
--         in   let 20
--              in  letY add (1) (0)
--                  in   let 50
--                       in  let add (3) (1)
--                           in  letZ add (1) (0)
--                               in let add (3) (5)
--                                  in add (0) (1)

-- let 1
-- in  let 2
--     in  letX add (1) (0)
--         in   let 20
--              in  letY add (SHIFT 1 (0)) (0)
--                  in   let 50
--                       in  let SHIFT 1 $ add (2) (0)           OR: add (SHIFT 1 (2)) (SHIFT 1 (0))
--                           in  letZ add (1) (0)
--                               in   let SHIFT 2 $ add (1) (3)  OR: add (SHIFT 2 (1)) (SHIFT 3 (2))
--                                    in  add (0) (1)

-- OLD:
-- increase binders (or insert shifts) for between binder and use, for each scope introduced
-- without shifting variables using these new scopes
--   by using new binders immediately, and then inserting shifts?
-- shifts seem like they'd only really be useful in ANF if allowed around vars

-- Tagging continuations
--   maybe tuple them up with info about how far upward they reach, or with a stack with a level for each it reaches
--   as linearization of sub-exprs introduces extra lets, stretch pointers up a level
--   as we pass each binder, we can stop tracking binders that referred to this level

-- Maybe it's not a terrible idea to parameterize `Anf` with a functor for
-- contextualizing variables.
--   Before shipping off ANF ASTs downstream, we use f = Identity; but during
--   Core -> ANF translation, we use f = IORef or MVar, and mutate variables once
--   we let-name subexpressions between variables and their binders.
--
-- An alternative would be to give unique IDs to each variable and `tell` bumps
-- to uniquely-identified variables that we use to correct the AST afterwards.

-- data Accumulator
--   = K () -- TODO: info about contained vars which are pointing to higher binders
--       (Trivial -> Anf) -- (Rhs -> Anf)

-- newtype Trivial
--   = TrivVar Variable
--   -- | TrivRhs Rhs
--   -- TODO: add more trivial cases in the future once we have unboxed values

-- slot0 :: Integral a => a -> Variable
-- slot0 level = LocalVar $ LocalNamelessVar (fromIntegral level) $ BinderSlot 0

slot0 :: Word32 -> Variable
slot0 level = LocalVar $ LocalNamelessVar level $ BinderSlot 0

succVar :: Variable -> Variable
succVar (LocalVar (LocalNamelessVar lvl slot)) = LocalVar $ LocalNamelessVar (succ lvl) slot
succVar v@(GlobalVarSym _) = v

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
                   --   intermediate/anf) binders.
                 , _levelIntros :: Word32
                   -- ^ Levels introduced since the last source binder. separate
                   --   from map for now so we can remove items from the map
                   --   once used.
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

-- Let's probably just start with explicit thunks (K without taking vars), and then
-- see if we can covert it to just use laziness or monadic actions or something

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

addRef :: AnfBinder -> Variable -> BindingStack -> BindingStack
addRef binder termVar stack = stack & (_head.levelRefs.at binder) ?~ termVar

-- | Updates the top of the 'BindingStack' to open a new binder for an
-- introduced 'AnfLet', or adds a new 'BindingLevel' for an existing 'Term'
-- 'Let'.
trackBinding :: Binding -> BindingStack -> BindingStack
trackBinding (AnfBinding binder) stack = stack & _head %~ updateLevel
  where
    updateLevel = (levelRefs.at binder ?~ slot0 0)
                . (levelRefs.mapped    %~ succVar)
                . (levelIntros         %~ succ)
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

anfCont :: BindingStack
        -> Term
        -> Binding
        -> (BindingStack -> LoweringM Anf)
        -> LoweringM Anf
anfCont stack term binding k = case term of
  V v ->
    case binding of
      AnfBinding binder ->
        -- TODO: should translation occur outside? would this make helpers defined in terms of Level better now?
        k $ addRef binder (translateTermVar stack v) stack
      TermBinding ->
        -- TODO: double-check this:
        k $ emptyIndirectionLevel (translateTermVar stack v) : stack

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

  -- TODO: Let (handle rollback / bulk-succ'ing previous level)
  --         if we need to return more from anf{Tail,Cont}, think about how to
  --             work that into state, rather than returning a tuple


toAnf :: Term -> Anf
toAnf t = evalState (anfTail emptyStack t) initialState
  where
    -- We provide a bottom level that doesn't correspond to a toplevel term
    -- 'Let' or 'Lam' so that e.g. a toplevel 'Let' with a non-trivial RHS has
    -- a level with which to introduce intermediary 'AnfLet's
    emptyStack = [emptyLevel]
    initialState = LoweringState $ AnfBinder 0


-- 3/16/16 - trying danvy one-pass to ANF rep with Shift
--         - first just get things wired up with bad variables and 1-ary apps
--         - TODO: see whether we do need a (V -1) in the presence of shift
--         - then add shifts
--         - then get n-ary apps working
--         - switch from Arity rep back to (V.Vector BinderInfo)
--         - then make sure multiple retvals are working
--           - we need type information for this
--           - this might require our accumulator/K to take multiple trivial
--             values? not sure.

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
