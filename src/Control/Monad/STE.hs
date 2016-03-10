{-# LANGUAGE MagicHash, UnboxedTuples, RankNTypes, TypeFamilies, DeriveDataTypeable, GADTs,FlexibleContexts, Trustworthy,TypeOperators, ScopedTypeVariables, BangPatterns #-}
module Control.Monad.STE
(
  STE
  ,runSTE
  ,throwSTE
  ,handleSTE
  ,extendError
  ,extendErrorTrans
  )

  where

-- import qualified  GHC.ST as GST
import GHC.Prim (State#,realWorld#,Any)
import Control.Exception as Except
import Control.Monad (ap)
import Control.Monad.Primitive
import Data.Typeable
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad.Trans.Class
import Data.Hop.Or
import Debug.Trace

-- {-# INLINE extendErrorTrans #-}
{-# NOINLINE extendErrorTrans #-}
extendErrorTrans
  :: forall s (h :: *) (tm :: (* -> *) -> * -> *) (a :: *). MonadTrans tm =>
     (forall b.
      tm (STE (b :+ h) s) a)
  -> forall c err.
     tm (STE (c :+ err :+ h ) s)  a
extendErrorTrans  x = (unsafeCoerce id ) $!  x


--  {-# INLINE extendError  #-}
{-# NOINLINE extendError  #-}
extendError
  :: forall s (h :: *) (a :: *).
     (forall b.  (STE (b :+ h) s) a)
  -> forall c err.  (STE (c :+ err :+ h ) s)  a
extendError  x = (unsafeCoerce id ) $! x

-- maybe this constructor shouldn't be private?
newtype STE e s a = STE {  extractSTE  ::  (STRep s a)}
type STRep s a = State# s -> (# State# s, a #)

instance Functor (STE e s) where
    fmap f (STE m) = STE $ \ s ->
      case (m s) of { (# new_s, r #) ->
      (# new_s, f r #) }

instance Applicative (STE e s) where
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
  internal (STE p) = p
 --  {-# INLINE internal #-}

unsafePrimToSTE :: forall m . PrimBase m =>(forall s e a . m a ->  STE e s a)
{-# NONLINE unsafePrimToSTE #-}
unsafePrimToSTE = unsafePrimToPrim

{-# NOINLINE runSTE #-} -- this may not be needed and may make code closer when its a small STE computation (though we're using it for small stuff )
runSTE :: (forall s. STE e s a) -> (Either e a  -> b) -> b
runSTE st  f = runSTRep (case
       do    -- traceM "about to runSTE"
            !res <-  unsafePrimToSTE $
              catch   (unsafePrimToPrim $ fmap Right  st)
                      (\(STException (Box err)) -> return (Left  $ unsafeCoerce err))
             -- traceM "caught STE "
            !resNew <-  return $! (f res)
             -- traceM "forced STE result "
            return $! resNew

    of { STE st_rep -> st_rep })

{-# NOINLINE  handleSTE #-}
handleSTE :: (Either e a -> b) -> (forall s. STE e s a)  -> b
handleSTE f st = runSTE st f

{-#  NOINLINE throwSTE #-} -- again audit
throwSTE :: forall (e:: * ) s (a ::  * ) .   e -> STE e s a
throwSTE err = STE $
       \s#  ->  (
           (extractSTE $
             unsafePrimToSTE $
                       (throwIO (STException  $! Box  $ (unsafeCoerce  $ err) ) ))
            s# )

-- I'm only letting runSTRep be inlined right at the end, in particular *after* full laziness
-- That's what the "INLINE [0]" says.
--              SLPJ Apr 99
-- {-# INLINE [0] runSTRep #-}

-- SDM: further to the above, inline phase 0 is run *before*
-- full-laziness at the moment, which means that the above comment is
-- invalid.  Inlining runSTRep doesn't make a huge amount of
-- difference, anyway.  Hence:

{-# NOINLINE runSTRep #-}
runSTRep :: forall a . (forall s. STRep s a) -> a
runSTRep st_rep = case st_rep realWorld# of
                        (# _, r #) -> r


data Box (a :: *) = Box a

data STException   where
   STException :: Box Any -> STException
  deriving(Typeable)
instance Show (STException) where
  show (STException _) = "(STException  <OPAQUE HEAP REFERENCE HERE>)"
instance  Exception STException

-- runSTFree :: Typeable e => (forall . STE (W e) s a) -> (Either e a -> b) -> b
