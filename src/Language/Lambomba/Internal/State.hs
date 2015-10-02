{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}


module Language.Lambomba.Internal.State where

import Data.Bound
import Data.Set
import Control.Monad.Trans.Free
{-

for our state triple rep, it looks roughly like

{P}C1..Cn{Q}, BUT

we actually want potentially
{P a} let x1 = c1 in .. let xn = cn in {Q}

because commands *could*
-}
-- data CommandSeqThenPostCond pred cmd a =
{-

this is basically a monadic ish sequence of commands followed by "returning"
the associated postcondition predicate set
PostCOndition (Set (Pred a))  |  CommandBind (Command a) (Scope () CommandSequence )

-}

data CommandMonad pred cmd a =
      CommandPostCondition (Set (pred a))
      | CommandBind !(cmd a) (Scope () (CommandMonad pred cmd) a)
    deriving (Eq,Ord,Functor,Show,Traversable,Foldable)

data Triple pred cmd a = Triple {
                                _pre :: Set (pred a)
                                _commandSequence :: CommandMonad pred cmd a
                                }
            deriving (Eq,Ord,Show,Functor,Show,Traversable,Foldable)
