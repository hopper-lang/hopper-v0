{-# LANGUAGE MagicHash, UnboxedTuples, GeneralizedNewtypeDeriving,RankNTypes, TypeFamilies, DeriveDataTypeable, GADTs,FlexibleContexts, Trustworthy,TypeOperators, ScopedTypeVariables, BangPatterns,StandaloneDeriving #-}
module Control.Monad.STE
(
  STE
  ,runSTE
  ,throwSTE
  ,handleSTE
  )

  where

--import qualified  GHC.ST as GST
import GHC.Prim (State#)
import Control.Exception as Except
import Control.Monad (ap)
import Control.Monad.Primitive
import Data.Typeable
import Unsafe.Coerce (unsafeCoerce)
import GHC.IO(IO(..))
import Control.Monad.ST
import GHC.ST



{-
---- stubb  while debugging new stuff
--newtype STE e s a = STE  { extractSTE  :: ExceptT e (ST s) a} deriving (Functor,Applicative,Monad)
instance PrimMonad (STE e s) where
    type PrimState (STE e s) = s
    primitive m = STE $! ExceptT $! (fmap Right (ST m))
    {-# INLINE primitive #-}

runSTE :: (forall s . STE e s a ) -> (Either e a -> b) -> b
runSTE (STE m)  f =  f  (runST  ((unsafeCoerce id) $! runExceptT m))

handleSTE :: (Either e a -> b) ->(forall s . STE e s a ) -> b
handleSTE f m =  runSTE m f

throwSTE :: e -> STE e s a
throwSTE err = STE (ExceptT $ return  $Left $  err )-}


-- maybe this constructor shouldn't be private?
newtype STE e s a = STE  (STERep s a)
type STERep s a = State# s -> (# State# s, a #)

instance Functor (STE e s) where
    fmap f (STE m) = STE $ \ s ->
      case (m s) of { (# new_s, r #) ->
      (# new_s, f r #) }

instance Applicative (STE e s) where
    pure = return
    (<*>) = ap

instance Monad (STE e s) where
    --{-# INLINE return #-}
    --{-# INLINE (>>)   #-}
    --{-# INLINE (>>=)  #-}
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
  --{-# INLINE primitive #-}
instance PrimBase (STE e s) where
  internal (STE p) = \ s# -> case p s# of
                          y -> y
 --  {-# INLINE internal #-}


{-# INLINE runSTE #-} -- this may not be needed and may make code closer when its a small STE computation (though we're using it for small stuff )
runSTE ::  (forall s. STE e s a) -> (Either e a  -> b) -> b
runSTE st  f = f $  runST $ privateCatch st


{-

{-# INLINE runST #-}
-- The INLINE prevents runSTRep getting inlined in *this* module
-- so that it is still visible when runST is inlined in an importing
-- module.  Regrettably delicate.  runST is behaving like a wrapper.

-- | Return the value computed by a state transformer computation.
-- The @forall@ ensures that the internal state used by the 'ST'
-- computation is inaccessible to the rest of the program.
runST :: (forall s. ST s a) -> a
runST st = runSTRep (case st of { ST st_rep -> st_rep })
-}

{-# NOINLINE privateCatch #-}
privateCatch :: forall (e :: *) (a :: * )  .  (forall s . STE e s a )  -> (forall s . ST s (Either e a))
privateCatch (STE steAction)  = ST $ unsafeCoerceIOAction2StateS $
        \s# ->
            case catch (fmap Right $ IO $ \ ps# -> steAction  ps# )  handler  of
               (IO ioAction) -> case ioAction s# of
                                  (# s'#, val #) -> (# s'#, val #)
   where
       handler :: STException -> IO (Either e a )
       handler = (\(STException (x) )->
                    case unbox $ unsafeCoerce x  of
                        !y -> return $ Left  y

                      )


--otherPrivateCatch

--catchException :: Exception e => IO a -> (e -> IO a) -> IO a
--catchException (IO io) handler = IO $ catch# io handler'
--    where handler' e = case fromException e of
--                       Just e' -> unIO (handler e')
--                       Nothing -> raiseIO# e


{-# INLINE handleSTE #-}
handleSTE :: (Either e a -> b) -> (forall s. STE e s a)  -> b
handleSTE f st = runSTE st f

{-

-- | A variant of 'throw' that can only be used within the 'IO' monad.
--
-- Although 'throwIO' has a type that is an instance of the type of 'throw', the
-- two functions are subtly different:
--
-- > throw e   `seq` x  ===> throw e
-- > throwIO e `seq` x  ===> x
--
-- The first example will cause the exception @e@ to be raised,
-- whereas the second one won\'t.  In fact, 'throwIO' will only cause
-- an exception to be raised when it is used within the 'IO' monad.
-- The 'throwIO' variant should be used in preference to 'throw' to
-- raise an exception within the 'IO' monad because it guarantees
-- ordering with respect to other 'IO' operations, whereas 'throw'
-- does not.
throwIO :: Exception e => e -> IO a
throwIO e = IO (raiseIO# (toException e))

-}

{-# INLINE unsafeCoerceIOAction2StateS #-}
unsafeCoerceIOAction2StateS :: (State# RealWorld -> (# State# RealWorld, a0 #)) -> forall s . STERep s a
unsafeCoerceIOAction2StateS = unsafeCoerce id


{-# INLINE throwSTE #-} -- again audit
throwSTE :: forall (e:: * ) s (a ::  * ) .  e -> STE e s a
throwSTE err = STE $ unsafeCoerceIOAction2StateS $ \s# ->
       case  throwIO (STException $ unsafeCoerce $! box err) of
          (IO act) -> case act s# of
                        (# s, res #) -> (# s , res #)

data Box a =
  Box {-# NOUNPACK #-} a
  -- question, should this have a dummy | Other
  --
box :: a -> Box a
box = Box
{-# INLINE box #-}

unbox :: Box a -> a
unbox = \(Box x) -> x
{-# INLINE unbox  #-}

data STException where
   STException :: {-# NOUNPACK #-} (Box ()) -> STException
  deriving Typeable
--deriving instance Typeable e => Typeable (STException e)

instance Show (STException ) where
  show (STException _) = "STException  OPAQUE BLOB "
instance Exception (STException)
