

module ANF  where
open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.String
open import Data.Rational
open import Data.Sum
open import Data.Unit

open import Binders.Var 

record DataConApp (universe a : Set) : Set  where 
         constructor _#_◂_
         -- theres probably room for a better notation :))) 
         
         field
--            universe : Set
           arity : ℕ 
           schema : Vec universe arity
           app  : Vec a arity 


mutual        
    data term (a : Set ) : Set where
      v : a -> term a -- variables return only appears in "tail" position 
      app : ∀ (n : ℕ ) ->  Callish a n   -> term a
      letCall : ∀ (n : ℕ ) -> Callish a n    -> term (Var (Fin n) a)  -> term a
      letAlloc :  Allocish a 1 -> term (Var (Fin 1) a) -> term a
    -- for now we only model direct allocations have having a single return value ... 

    data Allocish (a : Set) : ℕ  -> Set  where 
      lam : ∀ (n : ℕ ) ->  term (Var (Fin n) (term a)) -> Allocish  a 1 
      delay : term a -> Allocish  a 1
      dataConstr : DataConApp ⊤ a -> Allocish a 1 
    
    
    data Callish  (a : Set) : ℕ ->  Set where
      force : a -> Callish a 0 
      call : ∀ {n } ->  a -> Vec a n -> Callish a n 
      primCall : ∀ {n } ->  String ->  Vec a n -> Callish a n 
