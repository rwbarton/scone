import tactic.basic

/-
dependent equality / dependent path / "pathover" from HoTT/cubical type theory
-/

inductive deq {α : Sort*} {C : α → Sort*} :
  Π {a a' : α} (e : a = a') (x : C a) (x' : C a'), Prop
| refl {a : α} (x : C a) : deq (eq.refl a) x x

attribute [refl] deq.refl

notation x ` =[`:50 e:50 `] `:50 x':50 := deq e x x'

variables {α : Sort*} {C : α → Sort*}

@[symm] lemma deq.symm {a a' : α} (e : a = a') (x : C a) (x' : C a') :
  x =[e] x' → x' =[e.symm] x :=
begin
  rintro ⟨⟩,
  refl
end

@[trans] lemma deq.trans {a a' a'' : α} (e : a = a') (e' : a' = a'')
  (x : C a) (x' : C a') (x'' : C a'') :
  x =[e] x' → x' =[e'] x'' → x =[e.trans e'] x'' :=
begin
  rintros ⟨⟩ ⟨⟩,
  refl
end

/-
inductive ddeq {α : Sort*} {C : α → Sort*} {D : Π (a : α), C a → Sort*} :
  Π {a a' : α} {e : a = a'} {x : C a} {x' : C a'} (f : x =[e] x') (y : D a x) (y' : D a' x'), Prop
| refl {a : α} {x : C a} (y : D a x) : ddeq (deq.refl x) y y
-/
