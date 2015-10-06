{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}


module Language.Lambomba.Internal.State where

-- import Bound
-- import Data.Set
-- import Control.Monad.Trans.Free
-- import Prelude.Extras
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

{-data CommandMonad pred cmd a =
      CommandPostCondition  [(pred a)]
      | CommandBind !(cmd a) (Scope () (CommandMonad pred cmd) a)
    deriving (Eq,Ord,Eq1,Ord1,Show1,Read1,Functor,Show,Traversable,Foldable)

data Triple pred cmd a = Triple {
                                _pre :: [pred a]
                                , _commandSequence :: CommandMonad pred cmd a
                                }
            deriving (Eq,Ord,Show,Show,Traversable,Foldable)-}

{-



-}
