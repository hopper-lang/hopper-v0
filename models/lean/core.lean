import data.bool 
import data.nat
open nat
check nat 

/-
debrujin representation 
-/
inductive HasImpred := | Impred : HasImpred | Pred : HasImpred 

set_option pp.all true 
open HasImpred 

definition meet : HasImpred -> HasImpred -> HasImpred
| meet Pred Pred := Pred 
| meet Impred Impred := Impred
| meet Pred Impred := Impred
| meet Impred Pred := Impred 
check ∀ (a b  : Type) , a -> b 
check Type.{imax  1 0}
check ∀ {t1} , ∀ {t2 : t1}, (t1 : Prop)
check ∀ {t1 f} , ∀ {t2 : t1}, f t2 
check ∀ {t1 f} , ∀ {t2 : t1}, t1 -> f t2
check Type.{1} -> Type.{2}

definition zeroOrPlusMax : nat -> nat -> nat 
|zeroOrPlusMax 0 0 := 0 
|zeroOrPlusMax n m :=  1 +  (max n m )

inductive type :  nat-> HasImpred  -> Type := 
  | lift : ∀ {n} , type  n Pred -> type  (succ n) Pred
  | var : ∀ {n hasimp} , nat -> type  n hasimp 
  | tyBool : ∀ {n} ,type n Pred 
  | tyInteger : ∀ {n}, type n Pred 
  | typString : ∀ {n}, type n Pred 
  | impredUniversal : ∀ { hasimpA hasimpB},type  0 hasimpA ->type 0 hasimpB  -> type  0 Impred
  | predUniversal : ∀ {n m},type  n Pred -> type m Pred -> type  (zeroOrPlusMax n m )  Pred 
 -- i do want impred, but will ignore for now

--   | predarr : ∀ {n m  hasImpA hasImpB}, type n Pred -> type m  Pred -> type n (meet hasImpA hasImpB)
/-  with term  : ∀ {n himp}, type n himp -> Type :=
  | tmBool : ∀ {n himp}, bool -> term (@tyBool n) 
 
-/
