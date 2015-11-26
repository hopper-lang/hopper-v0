module core where

open import Data.Nat
open import Data.Vec
open import Data.Fin

data Var  (a b : Set) :   Set where
     Free :  a -> Var a b
     Bound : b -> Var a b 
 
data term (a : Set) : Set where
  v : a -> term a
  app : ∀  (n : ℕ ) ->   term a -> Vec (term a) n -> term a 
  abs : ∀ (n : ℕ ) -> term (Var (Fin n) (term a))-> term a 
