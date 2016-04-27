{-# LANGUAGE MagicHash, UnboxedTuples, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns,StandaloneDeriving #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs, TypeFamilies #-}


module Control.Monad.STE
(
  STE
  ,runSTE
  ,throwSTE
  ,handleSTE
  )

  where

#if MIN_VERSION_GLASGOW_HASKELL(8,0,0,0)
import GHC.Prim (State#, raiseIO#, catch#)
#else
import GHC.Prim (State#, raiseIO#, catch#, realWorld#)
#endif

import Control.Exception as Except
import Control.Monad (ap)
import Control.Monad.Primitive
import Data.Typeable
import Unsafe.Coerce (unsafeCoerce)
import GHC.IO(IO(..))

#if MIN_VERSION_GLASGOW_HASKELL(8,0,0,0)
import GHC.Magic(runRW#)
#endif


newtype STE e s a = STE  (STERep s a)

unSTE :: STE e s a -> STERep s a
unSTE = \(STE a) ->  a

type STERep s a = State# s -> (# State# s, a #)

instance Functor (STE e s) where
    fmap f (STE m) = STE $ \ s ->
      case (m s) of { (# new_s, r #) ->
      (# new_s, f r #) }

instance Applicative (STE e s) where
    {-# INLINE pure  #-}
    {-# INLINE (<*>) #-}
    pure = return
    (<*>) = ap

instance Monad (STE e s) where
    {-# INLINE return #-}
    {-# INLINE (>>)   #-}
    {-# INLINE (>>=)  #-}
    return x = STE (\ s -> (# s, x #))
    m >> k   = m >>= \ _ -> k

    (STE m) >>= k
      = STE (\ s ->
        case (m s) of { (# new_s, r #) ->
        case (k r) of { STE k2 ->
        (k2 new_s) }})

instance PrimMonad (STE e s) where
  type PrimState (STE e s) = s
  primitive = \ m ->  STE m
  {-# INLINE primitive #-}
instance PrimBase (STE e s) where
  internal (STE p) = \ s# -> case p s# of
                          y -> y
  {-# INLINE internal #-}



{-# INLINE runSTE #-} -- this may not be needed and may make code closer when its a small STE computation (though we're using it for small stuff )
runSTE ::  (forall s. STE e s a) -> (Either e a  -> b) -> b
runSTE = \ st  f -> f  $
            runBasicSTE (privateCatchSTE st)

{-# INLINE handleSTE #-}
handleSTE :: (Either e a -> b) -> (forall s. STE e s a)  -> b
handleSTE f st = runSTE st f

-- |  'throwSTE' needs the toException wrapper to play nice with
-- pure exceptions and async exceptions etc
throwSTE :: forall e s a .  e -> STE e s a
throwSTE err = unsafeIOToSTE  $
    IO (raiseIO# (toException $ STException $ ( Box $ unsafeCoerce err)))



-- | privateCatchSTE is NOT exported
-- we copy the machinery from
-- catchException so that pure errors aren't mishandled by
-- the catchSTE machinery when handling STE errors
privateCatchSTE:: forall e s b . STE e s b  -> STE e s (Either e b)
privateCatchSTE = \ steAct  ->
      unsafeIOToSTE $
        IO  (catch# (unsafeCoerce $ unSTE $ fmap Right steAct) handler')
  where
    --- need to handle pure exceptions too!
    handler' :: SomeException -> STERep RealWorld (Either e b)
    handler' e = case (fromException e) of
        Just (STException (Box val)) -> \ s -> (# s , Left $ unsafeCoerce val #)
        Nothing -> raiseIO# e

{-
catchAny :: IO a -> (forall e . Exception e => e -> IO a) -> IO a
catchAny (IO io) handler = IO $ catch# io handler'
    where handler' (SomeException e) = unIO (handler e)

catchException :: Exception e => IO a -> (e -> IO a) -> IO a
catchException (IO io) handler = IO $ catch# io handler'
    where handler' e = case fromException e of
                       Just e' -> unIO (handler e')
                       Nothing -> raiseIO# e


see https://phabricator.haskell.org/D1973 and
https://ghc.haskell.org/trac/ghc/ticket/11555
for information on tradeoffs in strictness

-}



unsafeIOToSTE :: IO a -> STE e s a
unsafeIOToSTE (IO io) = STE (unsafeCoerce io)



--- this results in WAY better perf when available
#if MIN_VERSION_GLASGOW_HASKELL(8,0,0,0)
runBasicSTE :: (forall s. STE e s a) -> a
runBasicSTE (STE st_rep) = case runRW# st_rep of (# _, a #) -> a
{-# INLINE runBasicSTE #-}
#else
runBasicSTE :: (forall s. STE e s a) -> a
runBasicSTE st = runSTERep (case st of { STE st_rep -> st_rep })
{-# INLINE runBasicSTE #-}

runSTERep :: (forall s. STERep  s a) -> a
runSTERep st_rep = case st_rep realWorld# of
                        (# _, r #) -> r
{-# NOINLINE runSTERep #-}
#endif



data Box a = Box {-# NOUNPACK #-} a

data STException where
   STException :: (Box ()) -> STException
  deriving Typeable
instance Show (STException ) where
  show (STException _) = "STException  OPAQUE BLOB, this should never happen, report a bug "
instance Exception (STException)
