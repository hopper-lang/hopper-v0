

module HBound  where

import Relation.Unary.PredicateTransformer  as PT
open import Relation.Unary  
open import Level
open import Relation.Binary using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive)

--naturalTrans : ∀ {a ℓ₁ ℓ₂ : Level } (ix : Set a )   (f : RU.Pred {a} ix ℓ₁ ) (g : RU.Pred {a} ix ℓ₂) -> Set (suc (ℓ₁ ∪  ℓ₂ ∪ a)  )
-- naturalTrans ix f g = ∀ (x : ix) -> f x  -> g x 

-- indexed natural transformation as family predicates
-- note: this is not the most general notion of a natural transformation 
natTransI : ∀ {i j k : Level } (a : Set k) (f : Pred a i) (g : Pred a j) -> Set ( j ⊔  i ⊔ k)
natTransI   a  f g =  ∀ ( x : a  ) -> (f x -> g x )

-- this is a simplified module of a homogenuous natural transformation
natTrans : ∀ {i j }  -> ∀  { a : Set i} ->   Rel (Pred a j) (i ⊔ j ) 
natTrans f g = forall x -> (f x -> g x )

