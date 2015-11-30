

module HBound  where

import Relation.Unary.PredicateTransformer  as PT
open import Relation.Unary  
open import Level
open import Relation.Binary using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive)

open import  Category.Applicative 

--naturalTrans : ∀ {a ℓ₁ ℓ₂ : Level } (ix : Set a )   (f : RU.Pred {a} ix ℓ₁ ) (g : RU.Pred {a} ix ℓ₂) -> Set (suc (ℓ₁ ∪  ℓ₂ ∪ a)  )
-- naturalTrans ix f g = ∀ (x : ix) -> f x  -> g x 

-- indexed natural transformation as family predicates
-- note: this is not the most general notion of a natural transformation 
NatIx : ∀ {i j k : Level } (a : Set k) (f : Pred a i) (g : Pred a j) -> Set ( j ⊔  i ⊔ k)
NatIx   a  f g =  ∀ ( x : a  ) -> (f x -> g x )

-- this is a simplified model of a homogenuous natural transformation
Nat : ∀ {i j }  -> ∀  { a : Set i} ->   Rel (Pred a j) (i ⊔ j ) 
Nat f g = forall x -> (f x -> g x )



{-
question: is using a formal model of categorical arrows useful here
-}
record NatFunctor {i j } {a : Set i} (t : Pred a j -> Pred a j) : Set ( i ⊔ suc j)  where
  field 
       natMap : ∀ {f g} -> Nat f g -> Nat (t f) (t g )


-- record NatTraverseable 
