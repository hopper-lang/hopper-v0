module core where

open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.String
open import Data.Rational

data Var  (a b : Set) :   Set where
     Free :  a -> Var a b
     Bound : b -> Var a b 

module ETerm  where
  data Literal : Set where
      Nat : ℕ  -> Literal
      Rat : ℚ -> Literal
      Str : String -> Literal 
  data term (a : Set) : Set where
    v : a -> term a
    app : ∀  (n : ℕ ) ->   term a -> Vec (term a) n -> term a
    --- 
    abs : ∀ (n : ℕ ) -> term (Var (Fin n) (term a))-> term a
    primcall : ∀ {n : ℕ } -> String -> Vec (term a) n -> term a
    lit :  Literal -> term a 

module ANF  where
 mutual 

  data term (a : Set ) : Set where
    v : a -> term a
    app : ∀ (n : ℕ ) ->  Callish a n   -> term a
    letCall : ∀ (n : ℕ ) -> Callish a n  -> term (Var (Fin n) a)  -> term a
    letAlloc : ∀ (n : ℕ ) -> Allocish a -> term (Var (Fin n) a) -> term a 

  data Allocish (a : Set) : Set  where 
    lam : ∀ (n : ℕ ) ->  term (Var (Fin n) (term a)) -> Allocish a
    delay : term a -> Allocish a
    
    
  data Callish  (a : Set) : ℕ ->  Set where
    force : a -> Callish a 0 
    call : ∀ {n } ->  a -> Vec a n -> Callish a n 
    primCall : ∀ {n } ->  String ->  Vec a n -> Callish a n 


--    abs
--   data anfNTC (a : Set) : Set where
  --  ntcApp : 
