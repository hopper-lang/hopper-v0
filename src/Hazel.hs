{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
module Hazel where

-- Significant features of this treatment include:
-- * n-tuples as a generalization of 2-tuples. This is an easy optimization
--   win for little extra work.
-- * bidirectional checking. we're following the treatment from Guillaume
--   Allais' "Typing with Leftovers" with modifications.
-- * linearity
--
-- * working towards:
--   - explicit usage annotations, so we can have variables that are used
--     multiple times (or not at all)
--   - dependency
--   - desugaring records, variants, etc
--
-- Idea for good error messages for linearity: instead of a boolean `Usage`,
-- keep track of the usage sites. Also, we don't need to track usage for
-- non-linear variables when they're introduced.

-- TODO things to check:
-- * arities line up in all places
-- * threading contexts specifies calling convention in a very real way
-- * what data structures are we using (list vs vector / ralist)

import Control.Lens hiding (Const)
import Control.Monad.Error.Class
import Control.Monad.State
import Data.Char (toUpper, toLower)
import Data.Vector (Vector)
import qualified Data.Vector as V


-- inferred terms / eliminations / neutral terms
data Computation
  = BVar Int
  | FVar String
  | App Computation Value
  -- questions arise re the eliminator for tuples
  -- * is it case, or was case just the eliminator for sums?
  -- * is let a suitable eliminator? but let's a checked term, not inferred
  -- * in a way, eliminating tuples is not computation! whereas functions and
  --   cases branch (justifying no inferred term for eliminating tuples).
  --
  -- ... actually we need case or there is no branching!
  | Case Computation     -- expression
         Type            -- type of the case expr
         (Vector Value)  -- expressions for each label
  | Annot Value Type
  deriving Show

-- checked terms / introductions / values
data Value
  = Lam Value
  | Primop Primop
  | Prd (Vector Value)
  | Let Pattern Computation Value
  | Index Int
  | Primitive Primitive
  | Neu Computation
  deriving Show

-- Match nested n-tuples.
--
-- Easy extension: `Underscore` doesn't bind any variables. Useful?
data Pattern
  = MatchTuple (Vector Pattern)
  | MatchVar Usage
  deriving Show

-- floating point numbers suck http://blog.plover.com/prog/#fp-sucks
-- (so do dates and times)
data Primitive
  = String String
  | Nat Int
  deriving Show

pattern NatV i = Primitive (Nat i)
pattern StrV s = Primitive (String s)

-- We should think about a more extensible way to add primops to the language
-- -- there will probably be a registry mapping from a name to its type and
-- evaluator at some point, but for now this will work.
data Primop
  = Add
  | PrintNat
  | ConcatString
  | ToUpper
  | ToLower
  deriving Show

data PrimTy
  = StringTy
  | NatTy
  deriving (Eq, Show)

data Type
  = PrimTy PrimTy
  | LabelsTy (Vector String)
  | LollyTy Type Type
  | TupleTy (Vector Type)
  deriving (Eq, Show)

data Usage = Inexhaustible | UseOnce | Exhausted
  deriving (Eq, Show)

useVar :: Usage -> Either String Usage
useVar Inexhaustible = Right Inexhaustible
useVar UseOnce = Right Exhausted
useVar Exhausted = Left "[useVar] used exhausted variable"

type Ctx = [(Type, Usage)]

-- I (Joel) made the explicit choice to not use the state monad to track
-- leftovers, since I want to take a little more care with tracking linearity.
-- We layer it on in some places where it's helpful.
--
-- TODO do we need to check all linear variables have been consumed here?
-- * we should just fix this so it passes in the empty context to the checker
runChecker :: Either String Ctx -> String
runChecker checker = either id (const "success!") checker

assert :: MonadError String m => Bool -> String -> m ()
assert True _ = return ()
assert False str = throwError str

inferVar :: Ctx -> Int -> Either String (Ctx, Type)
inferVar ctx k = do
  -- find the type, count this as a usage
  let (ty, usage) = ctx !! k
  usage' <- useVar usage
  -- TODO(joel) this is the only line that uses lens -- remove it?
  return (ctx & ix k . _2 .~ usage', ty)

-- Type inference for primops is entirely non-dependent on the environment.
inferPrimop :: Primop -> Type
inferPrimop p =
  let nat = PrimTy NatTy
      str = PrimTy StringTy
      tuple = TupleTy . V.fromList
  in case p of
       Add -> LollyTy (tuple [nat, nat]) nat
       PrintNat -> LollyTy nat str
       ConcatString -> LollyTy (tuple [str, str]) str
       ToUpper -> LollyTy str str
       ToLower -> LollyTy str str


allTheSame :: (Eq a) => [a] -> Bool
allTheSame [] = True
allTheSame (x:xs) = and $ map (== x) xs

infer :: Ctx -> Computation -> Either String (Ctx, Type)
infer ctx t = case t of
  BVar i -> inferVar ctx i
  FVar _name -> throwError "[infer FVar] found unexpected free variable"
  App cTm vTm -> do
    (leftovers, cTmTy) <- infer ctx cTm
    case cTmTy of
      LollyTy inTy outTy -> do
        leftovers2 <- check leftovers inTy vTm
        return (leftovers2, outTy)
      _ -> throwError "[infer App] inferred non LollyTy in LHS of application"
  Case cTm ty vTms -> do
    (leftovers1, cTmTy) <- infer ctx cTm

    -- TODO: check branches (labels) matches the right-hand-sides, cTm matches
    -- also

    leftovers2 <- flip execStateT leftovers1 $ forM vTms $ \vTm -> do
      let subCtx = (cTmTy, Inexhaustible):ctx
      (_, usage):newCtx <- lift $ check subCtx ty vTm
      assert (usage /= UseOnce)
        "[infer Case] must consume linear variable in case branch"
      return newCtx

    assert (allTheSame leftovers2)
      "[infer Case] all branches must consume the same linear variables"

--     case cTmTy of
--       LabelsTy _label -> assert (cTmTy == ty) "[infer Case] label mismatch"
--       _ -> throwError "[infer Case] can't case on non-labels"
--       -- PrimTy _prim -> assert (cTmTy == ty) "[infer Case] primitive mismatch"
--       -- TupleTy _values -> assert (cTmTy == ty) "[infer Case] tuple mismatch"
--       -- LollyTy _ _ -> throwError "[infer Case] can't case on function"

    return (leftovers2, ty)

  Annot vTm ty -> do
    leftovers <- check ctx ty vTm
    return (leftovers, ty)

check :: Ctx -> Type -> Value -> Either String Ctx
check ctx ty tm = case tm of
  Lam body -> case ty of
    LollyTy argTy tau -> do
      let bodyCtx = (argTy, UseOnce):ctx
      (_, usage):leftovers <- check bodyCtx tau body
      assert (usage /= UseOnce) "[check Lam] must consume linear bound variable"
      return leftovers
    _ -> throwError "[check Lam] checking lambda against non-lolly type"
  Primop p -> do
    let expectedTy = inferPrimop p
    assert (ty == expectedTy) $
      "[check Primop] primop (" ++ show p ++ ") type mismatch"
    return ctx
  Let pat letTm vTm -> do
    (leftovers, tmTy) <- infer ctx letTm
    patternTy <- typePattern pat tmTy
    -- XXX do we need to reverse these?
    let freshVars = map (, UseOnce) patternTy
        bodyCtx = freshVars ++ leftovers
        arity = length patternTy
    newCtx <- check bodyCtx ty vTm

    -- Check that the body consumed all the arguments
    let (bodyUsage, leftovers2) = splitAt arity newCtx
    forM_ bodyUsage $ \(_ty, usage) ->
      assert (usage /= UseOnce) "[check Let] must consume linear bound variables"
    return leftovers2
  Prd vTms -> case ty of
    -- Thread the leftover context through from left to right.
    TupleTy tys ->
      -- Layer on a state transformer for this bit, since we're passing
      -- leftovers from one term to the next
      let calc = forM (V.zip vTms tys) $ \(tm', ty') -> do
            leftovers <- get
            newLeftovers <- lift $ check leftovers ty' tm'
            put newLeftovers
      -- execState gives back the final state
      in execStateT calc ctx
    _ -> throwError "[check Prd] checking Prd agains non-product type"

  Primitive prim -> do
    case prim of
      String _ -> assert (ty == PrimTy StringTy)
        "[check Primitive] trying to match string against non-string type"
      Nat _ -> assert (ty == PrimTy NatTy)
        "[check Primitive] trying to match nat against non-nat type"
    return ctx

  -- XXX(joel) This doesn't make sense -- think about removing / replacing
  Index i -> case ty of
    LabelsTy names -> do
      assert (V.length names >= i)
        "[check Index] didn't find index in label vec"
      return ctx
    _ -> throwError "[check Index] checking Index against non-LabelsTy"

  Neu cTm -> do
    (leftovers, cTmTy) <- infer ctx cTm
    assert (cTmTy == ty) "[check Neu] checking inferred neutral type"
    return leftovers

evalC :: [Value] -> Computation -> Either String Value
evalC env tm = case tm of
  BVar i -> pure (env !! i)
  FVar name -> throwError ("unexpected free var in evaluation: " ++ name)
  App cTm vTm -> do
    cTm' <- evalC env cTm
    vTm' <- evalV env vTm
    case cTm' of
      Lam cBody -> evalV (vTm':env) cBody
      -- Note that we're passing in only the current heap value, not the
      -- context, since a primop must be atomic -- it can't capture
      Primop p -> evalPrimop p vTm'
      _ -> throwError "unexpected non lambda in lhs of function application"
  Case cTm _ty vTms -> do
    cTm' <- evalC env cTm
    case cTm' of
      Index branchIx ->
        case vTms V.!? branchIx of
          Just branch -> evalV (cTm':env) branch
          _ -> throwError "[evalC Case] couldn't find branch"
      Primitive _p -> undefined
      Prd _p -> undefined
      Neu _cTm -> undefined
      _ -> throwError "[evalC Case] unmatchable"
  Annot vTm _ty -> evalV env vTm

evalPrimop :: Primop -> Value -> Either String Value
evalPrimop Add (Prd args)
  | [NatV x, NatV y] <- V.toList args
  = pure (NatV (x + y))
evalPrimop PrintNat (NatV i) = pure (StrV (show i))
evalPrimop ConcatString (Prd args)
  | [StrV l, StrV r] <- V.toList args
  = pure (StrV (l ++ r))
evalPrimop ToUpper (StrV s) = pure (StrV (map toUpper s))
evalPrimop ToLower (StrV s) = pure (StrV (map toLower s))
evalPrimop _ _ = throwError "unexpected arguments to evalPrimop"

evalV :: [Value] -> Value -> Either String Value
evalV env tm = case tm of
  Prd vTms -> Prd <$> (mapM (evalV env) vTms)
  Let _pat cTm vTm -> do
    cTm' <- evalC env cTm
    evalV (cTm':env) vTm
  Primop _ -> pure tm
  Lam _ -> pure tm
  Primitive _ -> pure tm
  Index _ -> pure tm
  Neu _ -> pure tm

-- TODO we don't actually use the implementation of opening -- I had just
-- pre-emptively defined it thinking it would be used.
openC :: Int -> String -> Computation -> Computation
openC k x tm = case tm of
  BVar i -> if i == k then FVar x else tm
  FVar _ -> tm
  App cTm vTm -> App (openC k x cTm) (openV k x vTm)
  Case cTm ty vTms ->
    Case (openC k x cTm) ty (V.map (openV (k + 1) x) vTms)
  Annot vTm ty -> Annot (openV k x vTm) ty

openV :: Int -> String -> Value -> Value
openV k x tm = case tm of
  Lam vTm -> Lam (openV (k + 1) x vTm)
  Prd vTms -> Prd (V.map (openV k x) vTms)
  Let pat cTm vTm ->
    let bindingSize = patternSize pat
    in Let pat (openC k x cTm) (openV (k + bindingSize) x vTm)
  Index _ -> tm
  Primitive _ -> tm
  Primop _ -> tm
  Neu cTm -> Neu (openC k x cTm)

typePattern :: Pattern -> Type -> Either String [Type]
typePattern (MatchVar _) ty = Right [ty]
-- TODO check these line up (subPats / subTys)
--
-- example:
-- (MatchVar, MatchTuple (MatchVar, MatchVar))
--           v
-- [[ty0], [ty1, ty2]]
typePattern (MatchTuple subPats) (TupleTy subTys) = do
  let zipped = V.zip subPats subTys
  twoLevelTypes <- mapM (uncurry typePattern) zipped
  return (concat twoLevelTypes)
typePattern _ _ = throwError "[typePattern] misaligned pattern"

patternSize :: Pattern -> Int
patternSize (MatchVar _0) = 1
patternSize (MatchTuple subPats) = sum (V.map patternSize subPats)
