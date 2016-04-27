{-# LANGUAGE DeriveDataTypeable #-}

module  Hopper.Internal.Core.Term where

import Hopper.Internal.Core.Literal
import Hopper.Internal.Type.BinderInfo (BinderInfo)
import Hopper.Utils.LocallyNameless (Bound(..), Slot(..), Depth(..), localDepth,
                                     depthLevel, HasBound(..), Variable(..))

import Control.Lens ((+~), (%~), (^?), ix)
import Data.Data
import Data.Function ((&))
import Data.Tuple (swap)
import Data.Word (Word32)

import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Map.Strict as Map

data Term v =
  V v
  | BinderLevelShiftUP !Word32 !(Term v)  --
  | ELit !Literal
  | Return !(V.Vector (Term v))  -- explicit multiple return values
                      -- should V x be replaced by Return [x] ?
                      --  once we lower to ANF
                      -- NOTE: for valid expressions,
  | EnterThunk !(Term v) -- because we're in a strict IR rep,
                        -- we dont need to provide a seq like operation
                          -- seq a b === let _ := enterThunk a in b

  | Delay !(Term v)  --- Delay is a Noop on Thunked values, otherwise creates a Thunked
                    --- note: may need to change their semantics later?!
                    --- Q: is it valid to thunk a thunked value? (no?)
  | App !(Term v)  !(V.Vector (Term v))   --this is not curried :)
  | PrimApp  !PrimOpId --
             !(V.Vector (Term v)) -- not sure if this is needed, but lets go with it for now

  | Lam !(V.Vector BinderInfo)
        -- TODO: to properly translate to ANF, we need return arity info
        !(Term v)
  | Let !(V.Vector BinderInfo)
        !(Term v) --- RHS
        !(Term v) --- BODY
  deriving ({-Show1,Read1,Ord1,Eq1,-}Ord,Eq,Show,Read{-,Functor,Foldable-},Typeable{-,Traversable-})

-- | Removes binder shifts from a 'Term'
removeBinderShifts :: HasBound v => Term v -> Term v
removeBinderShifts = go $ repeat 0 -- NB: [] only works for well-formed ASTs,
                                   --     where no de Bruijn variables are free.
  where
    -- A bump amount @b@ at index @k@ in 'BinderShifts' means that we have @b@
    -- instances of @BinderLevelShiftUP k@ that we imagine we're tracking as we
    -- move down the AST.
    --
    -- When we enter a new scope, we @(0:)@ our list, effectively turning each
    -- tracked @BinderLevelShiftUP k@ to @BinderLevelShiftUP (k+1)@.
    --
    -- When we encounter a @BinderLevelShiftUP k@, we @(+1)@ the list at index
    -- @k@.
    --
    -- When we encounter a variable of depth @d@, we bump the variable by the
    -- sum of the @b@ amounts for all of the shifts the variable is affected by
    -- -- namely, the first @d+1@ @b@ values in the list of shifts.
    go :: HasBound v => [Word32] -> Term v -> Term v
    go shifts (V var) = case var ^? bound.localDepth.depthLevel of
      Just depth ->
        let adjustment = sum $ take (succ $ fromIntegral depth) shifts
        in V $ var & bound.localDepth.depthLevel +~ adjustment
      Nothing ->
        V var

    go shifts (BinderLevelShiftUP k t) =
      go (shifts & ix (fromIntegral k) %~ succ) t

    go _shifts lit@(ELit _) = lit

    go shifts (Return ts) = Return $ go shifts <$> ts

    go shifts (EnterThunk t) = EnterThunk $ go shifts t

    go shifts (Delay t) = Delay $ go shifts t

    go shifts (App ft ats) = App (go shifts ft) (go shifts <$> ats)

    go shifts (PrimApp primId ts) = PrimApp primId $ go shifts <$> ts

    -- In the 'Lam' and 'Let' cases, we enter a new scope:

    go shifts (Lam infos t) = Lam infos $ go (0 : shifts) t

    go shifts (Let infos rhs bod) = Let infos (go shifts rhs)
                                              (go (0 : shifts) bod)

-- | Open the term, using the name indexed at slot# in @names@ as the free
-- variable name when we come across a bound variable.
instantiate :: V.Vector T.Text -> Term Variable -> Term Variable
instantiate names = go $ Depth 0
  where
    go :: Depth -> Term Variable -> Term Variable
    go k t = case t of
      V (Bound (Local i (Slot idx)))
        | k == i
        -> V $ Atom $ names V.! fromIntegral idx
      V v -> V v
      BinderLevelShiftUP _ _ -> go k $ removeBinderShifts t
      ELit _ -> t
      Return ts -> Return $ V.map (go k) ts
      EnterThunk t' -> EnterThunk $ go k t'
      Delay t' -> Delay $ go k t'
      App ft ats -> App (go k ft) (go k <$> ats)
      PrimApp primId ts -> PrimApp primId $ go k <$> ts
      Lam infos body -> Lam infos $ go (succ k) body
      Let infos rhs body -> Let infos (go k rhs) $ go (succ k) body

-- | Close the term with respect to the provided free variable names, converting
-- free variables with those names to variables bound with the corresponding
-- slot indices.
abstract :: V.Vector T.Text -> Term Variable -> Term Variable
abstract names = go $ Depth 0
  where
    slots :: Map.Map T.Text Slot
    slots = Map.fromList $ fmap (fmap (Slot . fromIntegral) . swap) $
                                V.toList $ V.indexed names

    go :: Depth -> Term Variable -> Term Variable
    go k t = case t of
      V (Atom x)
        | Just slot <- Map.lookup x slots
        -> V $ Bound $ Local k slot
      V v -> V v
      BinderLevelShiftUP _ _ -> go k $ removeBinderShifts t
      ELit _ -> t
      Return ts -> Return $ V.map (go k) ts
      EnterThunk t' -> EnterThunk $ go k t'
      Delay t' -> Delay $ go k t'
      App ft ats -> App (go k ft) (go k <$> ats)
      PrimApp primId ts -> PrimApp primId $ go k <$> ts
      Lam infos body -> Lam infos $ go (succ k) body
      Let infos rhs body -> Let infos (go k rhs) $ go (succ k) body

-- | Converts a 'Term' from locally-nameless to (simply) bound variables.
-- Returns @Nothing@ if the term contains a free variable.
ensureClosed :: Term Variable -> Maybe (Term Bound)
ensureClosed t = case t of
  V (Atom _) -> Nothing
  V (Bound b) -> Just $ V b
  BinderLevelShiftUP _ _ -> ensureClosed $ removeBinderShifts t
  ELit lit -> Just $ ELit lit
  Return ts -> Return <$> V.mapM ensureClosed ts
  EnterThunk t' -> EnterThunk <$> ensureClosed t'
  Delay t' -> Delay <$> ensureClosed t'
  App ft ats -> App <$> ensureClosed ft <*> V.mapM ensureClosed ats
  PrimApp primId ats -> PrimApp primId <$> V.mapM ensureClosed ats
  Lam infos body -> Lam infos <$> ensureClosed body
  Let infos rhs body -> Let infos <$> ensureClosed rhs <*> ensureClosed body

--- NOTE: USE STE MONAD ONCE WE MIGRATE TO HSUM DESIGN
--- this is kinda only for "inlining" on debruijin variables for now
substitute :: Word32 -> (Slot  -> Maybe (Term Bound)) -> Term Bound -> Either (String,Word32) (Term Bound)
substitute baseLevel initMapper initTerm = goSub 0 initMapper initTerm
  where
    goSub :: Word32 -> (Slot  -> Maybe (Term Bound)) -> Term Bound -> Either (String,Word32) (Term Bound)
    goSub shift mapper  var@(V (Local (Depth level) bslt@(Slot slot)))
                | level == (shift + baseLevel) =
                        maybe (Left ("bad slot", slot))
                              (Right . BinderLevelShiftUP shift )
                             $ mapper bslt
                | otherwise =  Right var
    goSub _l _m var@(V (Global _)) = Right var
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
    goSub _shift _mapper lit@(ELit _)  = Right lit
    goSub shift mapper (EnterThunk bod ) =  fmap EnterThunk $ goSub shift mapper bod
    goSub shift mapper (Delay bod ) = fmap Delay $ goSub shift mapper bod
