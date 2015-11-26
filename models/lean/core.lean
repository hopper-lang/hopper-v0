
import data.bool 
import data.nat
-- import data.list 

inductive List.{ℓ} (a : Type.{ℓ}) : Type.{imax (ℓ + 1) ℓ}
        | Nil : List a 
        | Cons : a -> List a -> List a 

set_option pp.all true 

check vector
inductive 
/-
debrujin representation 
-/
check succ

check Type.{imax 0 1}
check Type.{imax 1 2}
check Type.{imax 2 1}
check Type.{imax 1 0}

inductive Var : Type -> Type -> Type := 
  | Free : forall {a b} , a -> Var a b 
  | Bound : forall {a b} , b -> Var a b

check list
check Var.Free
-- this is the untyped ast 
inductive Term.{ℓ} (a : Type.{ℓ})   : Type.{max 1 ℓ} :=
   | V :  a -> Term a 
   | App : ∀ (n : nat), Term a -> (list (Term a) ) -> Term a 
