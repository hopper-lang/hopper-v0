{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Hopper.Internal.LoweredCore.ANF where

import Hopper.Utils.LocallyNameless
import Hopper.Internal.Core.Literal
import Hopper.Internal.Core.Term

import Data.Word
import Control.Monad.Trans.State.Strict as State
import Control.Lens

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

newtype Trivial
  = TrivVar Variable
  -- | TrivRhs Rhs
  -- TODO: add more trivial cases in the future once we have unboxed values

slot0 :: Integral a => a -> Variable
slot0 level = LocalVar $ LocalNamelessVar (fromIntegral level) $ BinderSlot 0

returnAllocated :: Alloc -> Anf
returnAllocated alloc = AnfLet (Arity 1)
                               (RhsAlloc alloc)
                               (AnfReturn $ V.singleton $ slot0 (0 :: Word32))

arity :: V.Vector BinderInfo -> Arity
arity binders = Arity $ fromIntegral $ V.length binders

-- TODO: possibly rename?
newtype NewVar = NewVar { newVarId :: Word64 } deriving (Eq, Show, Ord)

instance Enum NewVar where
  toEnum = NewVar . toEnum
  fromEnum = fromEnum . newVarId

data BindingFrame
  = BindingFrame { _frameRefs :: Map.Map NewVar Variable
                   -- ^ references to both existing (i.e. term) and new (i.e.
                   --   intermediate) binders.
                 , _frameIntros :: Word32
                   -- ^ levels introduced since the last source binder. separate
                   --   from map for now so we can remove items from the map
                   --   once used.
                 }
  deriving (Eq, Show)
makeLenses ''BindingFrame

-- The bottom 'BindingFrame' of this stack does not necessarily correspond to a
-- 'Term' binding level (i.e. 'Let' or 'Lam') -- consider a toplevel 'Let' with
-- RHS global var applied to a global var. See 'toAnf'.
type BindingStack = [BindingFrame]

type LoweringM = {- TODO: wrap with: ReaderT BindingStack -} State NewVar

-- TODO: perhaps move from explicit stack passing to either tupling it update
--       into the state, or perhaps with a reader -- using e.g. mapReader
--       to apply a modified reader env for a certain sub-term

-- Let's probably just start with explicit thunks (K without taking vars), and then
-- see if we can covert it to just use laziness or monadic actions or something

frameSizes :: BindingStack -> [Word32]
frameSizes = fmap _frameIntros

-- | Bumps the provided source variable by the number of intermediate lets that
-- have been introduced since the source binder this variable points to.
translateTermVar :: BindingStack -> Variable -> Variable
translateTermVar _ v@(GlobalVarSym _) = v
translateTermVar stack (LocalVar (LocalNamelessVar depth slot)) =
  LocalVar $ LocalNamelessVar (depth + displacement) slot
  where
    displacement = sum $ take (fromIntegral $ depth + 1) (frameSizes stack)

-- updateTopFrame :: (BindingFrame -> BindingFrame) -> BindingStack -> BindingStack
-- updateTopFrame _ [] = error "unexpected binding stack underrun"
-- updateTopFrame f (frame : stack) = f frame : stack

-- | Initializes a NewVar pointing the correct number of binders up in the top
-- frame's map. As more levels are introduced, these initialized vars in the map
-- will be bumped.
initNewVar :: NewVar -> Maybe Variable -> BindingStack -> BindingStack
initNewVar newVar mTermVar stack = case mTermVar of
  Nothing -> setNewVar $ slot0 0
  Just termVar -> setNewVar $ translateTermVar stack termVar

  where
    setNewVar x = set (_head . frameRefs . at newVar) (Just x) stack

anfTail :: BindingStack -> Term -> LoweringM Anf
anfTail stack term = case term of
  V v -> return $ AnfReturn $ V.singleton $ translateTermVar stack v

  -- TODO: impl a pass to push shifts down to the leaves and off of the AST
  BinderLevelShiftUP _ _ -> error "unexpected binder shift during ANF conversion"

  ELit lit -> return $ returnAllocated $ AllocLit lit

  -- -- TODO: switch to support of n-ary application
  -- App ft ats
  --   | V.length ats == 1 -> anfCont ft $ \(TrivVar fv) ->         -- TODO: pass in stack
  --                            let at0 = V.head ats
  --                            in anfCont at0 $ \(TrivVar av) ->   -- TODO: pass in stack
  --                                 AnfTailCall $ AppFun fv $ V.singleton av
  --   | otherwise -> error "TODO: add support for n-ary application"

  -- App ft ats
  --   | V.length ats == 1 ->
  --     anfCont ft $ \_ -> do
  --       _todo
  --   | otherwise -> error "TODO: add support for n-ary application"

  Lam binders t -> do
    body <- anfTail stack t
    return $ returnAllocated $ AllocLam (arity binders) body

  -- OLD:
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

-- TODO: should K take the binding stack too?
-- anfCont :: BindingStack -> Term -> (Trivial -> LoweringM Anf) -> LoweringM Anf
anfCont :: BindingStack -> Term -> NewVar -> (BindingStack -> LoweringM Anf) -> LoweringM Anf
anfCont stack t var k = case t of
  V v -> do
    -- FIXME: this needs to update the stack frame... but that's not in the State.
    --        perhaps info should be passed to k, which might help us get away with no stack in the state?
    --        b/c if possible, no stack in the state is best: it'd be nice if that
    --        was implicitly done (correctly) by the haskell control stack
    --
    --        "info" could be (Maybe Variable) for the term var.. OR stack'
    --          if it's indeed stack', perhaps this is the time to put the stack in a ReaderT
    --          wrapping the state. Seems like yes
    --
    let stack' = initNewVar var (Just v) stack
    k stack'
--
--   -- TODO: is this right?
--   BinderLevelShiftUP n t -> AnfShift n $ anfCont t k
--
--   ELit l -> AnfLet (Arity 1)
--                    (RhsAlloc $ AllocLit l)
--                    (shift (k $ TrivVar $ slot0 0))
--
--   -- TODO: switch to support of n-ary application
--   App ft ats
--     | V.length ats == 1 ->
--         let at0 = V.head ats
--         in anfCont ft $ \(TrivVar fv) ->
--              anfCont at0 $ \(TrivVar av) ->
--                -- FIXME: this return arity is wrong. it needs to come from the
--                --        app. we can't actually assume 1 here.
--                AnfLet (Arity 1)
--                       (RhsApp $ AppFun fv $ V.singleton av)
--                       (shift $ k $ TrivVar $ slot0 0)
--
--     | otherwise -> error "TODO: add support for n-ary application"
--
--   Lam bs bod -> AnfLet (Arity 1)
--                        (RhsAlloc $ AllocLam (arity bs) $ anfTail bod)
--                        (shift (k $ TrivVar $ slot0 0))

toAnf :: Term -> Anf
toAnf t = evalState (anfTail emptyStack t) $ NewVar 0
  where
    -- We provide a bottom frame that doesn't correspond to a toplevel term
    -- 'Let' or 'Lam' so that e.g. a toplevel 'Let' with a non-trivial RHS has
    -- a frame with which to introduce intermediary 'AnfLet's
    emptyStack = [BindingFrame (Map.fromList []) 0]




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
--   example:       let x=50 in add 10 (let f = lam... in f x) 20
--   anf expansion: letT 50
--                  in   letA 10
--                       in   letT lam...        \   these two lines are for the nested
--                            in   letA (0) (2)  /   let and affect our add's first arg
--                                 in   letA 20
--                                      in   add (3) (1) (0)
