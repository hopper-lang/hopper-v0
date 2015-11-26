
import data.bool 
import data.nat
import data.list 
import data.examples.vector 
import data.fin

set_option pp.all true 

check vector
inductive 
/-
debrujin representation 
-/
check nat.succ

check Type.{imax 0 1}
check Type.{imax 1 2}
check Type.{imax 2 1}
check Type.{imax 1 0}

inductive Var ( a b : Type ) : Type := 
  | Free :   a -> Var a b 
  | Bound :  b -> Var a b
check fin
check list
check Var.Free
-- this is the untyped ast 

inductive term  (a : Type) : Type  :=
   | V : a -> term a 
   | App : term a -> list  (term a)   -> term a 
--   | Lam : ∀ {a }, forall {n : nat} , term (Var (fin n) (term a)) -> term a 

