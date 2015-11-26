module core where

open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.String 

data Var  (a b : Set) :   Set where
     Free :  a -> Var a b
     Bound : b -> Var a b 

module ETerm  where 
  data term (a : Set) : Set where
    v : a -> term a
    app : ∀  (n : ℕ ) ->   term a -> Vec (term a) n -> term a
    --- 
    abs : ∀ (n : ℕ ) -> term (Var (Fin n) (term a))-> term a 

module ANF  where
 mutual 

  data term (a : Set ) : Set where
    v : a -> term a
    app : ∀ (n : ℕ ) ->  Callish a n   -> term a
    letCall : ∀ (n : ℕ ) -> Callish a n  -> term (Var (Fin n) a)  -> term a

  data Callish  (a : Set) (n : ℕ ) : Set where
    call :  a -> Vec a n -> Callish a n 
    primCall : String ->  Vec a n -> Callish a n 
    lam :  term (Var (Fin n) (term a)) -> Callish a n 

--    abs
--   data anfNTC (a : Set) : Set where
  --  ntcApp : 
