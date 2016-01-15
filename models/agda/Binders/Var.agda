module Binders.Var where

data Var  (a b : Set) :   Set where
     Free :  a -> Var a b
     Bound : b -> Var a b

