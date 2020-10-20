import data.equiv.basic
import tactic.binder_matching
import scone.deq

namespace scone

universes v w u u'

/-
Packed contexts
~~~~~~~~~~~~~~~

In order to directly represent a context by a Lean type we would need induction-recursion:
simultaneously define contexts and type families in those contexts.
There might be a way to define these types in Lean anyways,
but for now we use the following mechanism of "packed contexts"
to represent a context as a single Lean type of a specific form
(which is visible only on the `meta` level).

A context `Γ` is represented as a type `⟦Γ⟧` which we call a "packed context":
* the empty context `•` is represented by the type `⟦•⟧ = unit`;
* the extended context `Γ, x : α` (where `Γ ⊢ α type`)
  is represented by the type `Σ (i : ⟦Γ⟧), α i`, where in turn
  the open type `α` is represented as a function from `⟦Γ⟧` to `Type`.
In the Lean code we write just `Γ` for the packed context `⟦Γ⟧`.
-/

/-- Extra data associated to the judgment `⊢ Γ ctx`. -/
structure edge_ctx (Γ : Sort u) :=
(v : Γ → Type v)
(e : Π {i₀ i₁ : Γ}, v i₀ → v i₁ → Type w)
(refl : Π {i} (a : v i), e a a)

/-- Extra data associated to the judgment `Γ ⊢ X type`.
Here the open type `X` is represented as a Type-valued function on
the packed context `⟦Γ⟧`, which in Lean we write as simply `Γ`,
as described above. -/
structure edge_ctx_ty {Γ : Sort*} (EΓ : edge_ctx Γ) (X : Γ → Sort u) :=
(v : Π {i : Γ}, EΓ.v i → X i → Type v)
(e : Π {i₀ i₁ : Γ} {γ₀ : EΓ.v i₀} {γ₁ : EΓ.v i₁}
       {x₀ : X i₀} {x₁ : X i₁}, EΓ.e γ₀ γ₁ → v γ₀ x₀ → v γ₁ x₁ → Type w)
(refl : Π {i : Γ} {γ : EΓ.v i} {x : X i} (a : v γ x), e (EΓ.refl γ) a a)

abbreviation edge_ctx_ty.v' {Γ : Sort*} {EΓ : edge_ctx Γ} {X : Γ → Sort*} (EX : edge_ctx_ty EΓ X)
  (i : Γ) (a : EΓ.v i) (x : X i) : Type* :=
EX.v a x

abbreviation edge_ctx_ty.e' {Γ : Sort*} {EΓ : edge_ctx Γ} {X : Γ → Sort*} (EX : edge_ctx_ty EΓ X)
  (i₀ i₁ : Γ) {γ₀ : EΓ.v i₀} {γ₁ : EΓ.v i₁} {x₀ : X i₀} {x₁ : X i₁} : EΓ.e γ₀ γ₁ → EX.v γ₀ x₀ → EX.v γ₁ x₁ → Type* :=
λ e, EX.e e

/-- Extra data associated to the judgment `Γ ⊢ t : X`.
Both `X` and `t` are represented as functions on the packed context `⟦Γ⟧`. -/
structure edge_ctx_tm {Γ : Sort*} (EΓ : edge_ctx Γ) {X : Γ → Sort*} (EX : edge_ctx_ty EΓ X)
  (t : Π i, X i) :=
(v : Π {i : Γ} (a : EΓ.v i), EX.v a (t i))
(e : Π {i₀ i₁ : Γ} {a₀ : EΓ.v i₀} {a₁ : EΓ.v i₁} (e : EΓ.e a₀ a₁), EX.e e (v a₀) (v a₁))
(refl : Π {i : Γ} (a : EΓ.v i), e (EΓ.refl a) = EX.refl (v a))

/-- Any context can be given the "discrete" `edge_ctx` structure. -/
def discrete_edge_ctx (Γ : Sort u) : edge_ctx Γ :=
{ v := λ _, unit,
  e := λ i₀ i₁ _ _, plift (i₀ = i₁),
  refl := λ i _, ⟨rfl⟩ }

/-- The extra data associated to the empty context. -/
def unit_edge_ctx : edge_ctx unit :=
discrete_edge_ctx unit

/-- Any type family can be given the "discrete" `edge_ctx_ty` structure
over the discrete `edge_ctx` structure on the index type.
This is appropriate for all types whose definition does not use `Type`. -/
def discrete_edge_ctx_ty {Γ : Sort*} (X : Γ → Sort u) :
  edge_ctx_ty (discrete_edge_ctx Γ) X :=
{ v := λ _ _ _, unit,
  e := λ i₀ i₁ _ _ x₀ x₁ r _ _, plift (x₀ =[r.down] x₁),
  refl := λ i _ x _, ⟨deq.refl x⟩ }

/-- Extra data corresponding to the "context extension" formation rule

  ⊢ Γ ctx   Γ ⊢ α type
 ----------------------
     ⊢ Γ, x : α ctx
-/
def edge_ctx.extend {Γ : Sort*} (EΓ : edge_ctx Γ) {A : Γ → Sort*} (EA : edge_ctx_ty EΓ A) :
  edge_ctx (Σ γ, A γ) :=
{ v := λ p, Σ (i : EΓ.v p.1), EA.v i p.2,
  e := λ p₀ p₁ q₀ q₁, Σ (j : EΓ.e q₀.1 q₁.1), EA.e j q₀.2 q₁.2,
  refl := λ p q, ⟨EΓ.refl q.1, EA.refl q.2⟩ }

/-- Extra data corresponding to the "weakening" structural rule

  ⊢ Γ ctx   Γ ⊢ α type   Γ ⊢ β type
 -----------------------------------
        Γ, x : α ⊢ β type
-/
def edge_ctx_ty.extend {Γ : Sort*} {EΓ : edge_ctx Γ} {A : Γ → Sort*} (EA : edge_ctx_ty EΓ A)
  {B : Γ → Sort*} (EB : edge_ctx_ty EΓ B) : edge_ctx_ty (EΓ.extend EA) (λ p, B p.1) :=
{ v := λ p q, EB.v q.1,
  e := λ p₀ p₁ q₀ q₁ x₀ x₁ j, EB.e j.1,
  refl := λ p q x a, EB.refl a }

/-- Implementation: A vertex of `Π A, B` over a value `f`
and above a vertex `x` of `Γ` over a value `i : Γ`. -/
structure pi_edge_v {Γ : Sort*} (EΓ : edge_ctx Γ)
  {A : Γ → Sort*} (EA : edge_ctx_ty EΓ A)
  {B : Π i, A i → Sort*}
  (EB : edge_ctx_ty (EΓ.extend EA) (λ p, B p.1 p.2))
  (i : Γ) (x : EΓ.v i) (f : Π (a : A i), B i a) :=
(fv : Π (a : A i) (w : EA.v x a), EB.v' ⟨i, a⟩ ⟨x, w⟩ (f a))
(fe : Π (a₀ a₁ : A i) (w₀ : EA.v x a₀) (w₁ : EA.v x a₁) (e : EA.e (EΓ.refl x) w₀ w₁),
  EB.e (by exact ⟨EΓ.refl x, e⟩) (fv a₀ w₀) (fv a₁ w₁))
-- TODO: refl

/-- Extra data corresponding to the Pi introduction rule

  ⊢ Γ ctx   Γ ⊢ α type   Γ, a : α ⊢ β type
 ------------------------------------------
           Γ ⊢ Π (a : α), β type

We represent the type family `β` as a function of two arguments:
the packed context `i : ⟦Γ⟧` and the bound variable `a : α`. -/
def pi_edge_ctx_ty {Γ : Sort*} (EΓ : edge_ctx Γ)
  {A : Γ → Sort*} (EA : edge_ctx_ty EΓ A)
  {B : Π i, A i → Sort*}
  (EB : edge_ctx_ty (EΓ.extend EA) (λ p, B p.1 p.2)) :
  edge_ctx_ty EΓ (λ i, Π a, B i a) :=
{ v := pi_edge_v EΓ EA EB,
  e := λ i₀ i₁ x₀ x₁ f₀ f₁ e F₀ F₁,
    Π (a₀ : A i₀) (a₁ : A i₁) (w₀ : EA.v x₀ a₀) (w₁ : EA.v x₁ a₁) (d : EA.e e w₀ w₁),
    EB.e' ⟨i₀, a₀⟩ ⟨i₁, a₁⟩ (by exact ⟨e, d⟩) (F₀.fv a₀ w₀) (F₁.fv a₁ w₁),
  refl := λ i a f F, F.fe }

/-- Extra data corresponding to the "var" structural rule

  ⊢ Γ ctx   Γ ⊢ α type
 ----------------------
    Γ, a : α ⊢ a : α
-/
def last_var_ctx_tm {Γ : Sort*} (EΓ : edge_ctx Γ) {A : Γ → Sort*} (EA : edge_ctx_ty EΓ A) :
  edge_ctx_tm (EΓ.extend EA) (EA.extend EA) (λ (p : Σ i, A i), p.2) :=
{ v := λ i p, p.2,
  e := λ i₀ i₁ p₀ p₁ e, e.2,
  refl := λ i p, rfl }

/-- Extra data corresponding to a type in an empty context: `• ⊢ α type`. -/
def edge_ty (A : Sort u) : Sort* := edge_ctx_ty unit_edge_ctx (λ _, A)

-- TODO: more concise constructor for `edge_ty`, not involving a zillion underscores?

def edge_ty.v_ {A : Sort*} (EA : edge_ty A) : A → Sort* := EA.v' () ()

def edge_ty.e_ {A : Sort*} (EA : edge_ty A) {a₀ a₁ : A} : EA.v_ a₀ → EA.v_ a₁ → Sort* := EA.e ⟨rfl⟩

-- TODO: similar `edge_tm` type for closed terms.

-- This definition classifies only *discrete* types!
def discrete_type_edge_ty : edge_ty Type :=
{ v := λ _ _ _, unit,
  e := λ _ _ _ _ X Y _ _ _, X ≃ Y,
  refl := λ _ _ X _, equiv.refl X }

structure edge_ty_iso {X Y : Sort*} (EX : edge_ty X) (EY : edge_ty Y) :=
(φ : X ≃ Y)
(φv : Π x, EX.v_ x ≃ EY.v_ (φ x))
(φe : Π x₀ x₁ (w₀ : EX.v_ x₀) (w₁ : EX.v_ x₁),
      EX.e_ w₀ w₁ ≃ EY.e_ (φv x₀ w₀) (φv x₁ w₁))
-- TODO: refl

/-- Extra data for `• ⊢ Type type`.
Object classifier, displayed over the object classifier `Type` of Set. -/
def type_edge_ty : edge_ty Type :=
{ v := λ _ _ X, edge_ty X,
  e := λ _ _ _ _ X Y _ EX EY, edge_ty_iso EX EY,
  refl := λ _ _ X EX,
  { φ := equiv.refl X,
    φv := λ x, equiv.refl _,
    φe := λ x₀ x₁ w₀ w₁, equiv.refl _ } }

def prop_edge_ty : edge_ty Prop :=
{ v := λ _ _ _, unit,
  e := λ _ _ _ _ p q _ _ _, plift (p ↔ q),
  refl := λ _ _ p _, ⟨iff.refl p⟩ }

/-- Weakening rule for constants:

  • ⊢ α type
 ------------
  Γ ⊢ α type
-/
def gen_edge_ty {A : Sort*} (EA : edge_ty A) {Γ : Sort*} {EΓ : edge_ctx Γ} : edge_ctx_ty EΓ (λ _, A) :=
{ v := λ i _ a, EA.v_ a,
  e := λ i₀ i₁ _ _ a₀ a₁ _ x₀ x₁, EA.e_ x₀ x₁,
  refl := λ i _ a x, EA.refl x }

/-- Extra data corresponding to Russell-style universes:

  ⊢ Γ ctx   Γ ⊢ α : Type
 ------------------------
        Γ ⊢ α type
-/
def univ_ctx_ty {Γ : Sort*} (EΓ : edge_ctx Γ) {A : Γ → Type} (EA : edge_ctx_tm EΓ (gen_edge_ty type_edge_ty) A) :
  edge_ctx_ty EΓ A :=
{ v := λ i x a, (EA.v x).v_ a,
  -- We make a choice of "transport direction" here; does it matter?
  e := λ i₀ i₁ x₀ x₁ a₀ a₁ e v₀ v₁, (EA.v x₁).e_ ((EA.e e).φv _ v₀) v₁,
  -- Note: This might not be a proof! Is that okay?
  -- Instead, we should transport `(EA.v x).refl _` along `EA.refl` somehow, I guess?
  refl := λ i x a v, by { rw EA.refl, exact (EA.v x).refl _ } }

end scone
