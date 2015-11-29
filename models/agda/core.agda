module core where

open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.String
open import Data.Rational
open import Data.Sum
open import Data.Unit


open import Binders.Var 




{-
module ABTLearning where
   data View {univ : Set} (f : univ -> Set) (a : univ) : list univ -> Set where
     Syn : f a -> View f a []
     Var : 
   record ABT {u : Set}
-}

module Term  where
    data Literal : Set where
        Nat : ℕ  -> Literal
        Rat : ℚ -> Literal
        Str : String -> Literal 
    data term (a : Set) : Set where
      v : a -> term a
      app : ∀  (n : ℕ ) ->   term a -> Vec (term a) n -> term a
      abs : ∀ (n : ℕ ) -> term (Var (Fin n) (term a))-> term a
      primcall : ∀ {n : ℕ } -> String -> Vec (term a) n -> term a
      lit :  Literal -> term a
      force : term a -> term a
      delay : term a -> term a 



module Types where

  
