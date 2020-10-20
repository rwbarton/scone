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
(v : Γ → Sort v)
(e : Π {i₀ i₁ : Γ}, v i₀ → v i₁ → Sort w)
(refl : Π {i} (a : v i), e a a)

/-- Extra data associated to the judgment `Γ ⊢ X type`.
Here the open type `X` is represented as a Type-valued function on
the packed context `⟦Γ⟧`, which in Lean we write as simply `Γ`,
as described above. -/
structure edge_ctx_ty {Γ : Sort*} (EΓ : edge_ctx Γ) (X : Γ → Sort u) :=
(v : Π {i : Γ}, EΓ.v i → X i → Sort v)
(e : Π {i₀ i₁ : Γ} {γ₀ : EΓ.v i₀} {γ₁ : EΓ.v i₁}
       {x₀ : X i₀} {x₁ : X i₁}, EΓ.e γ₀ γ₁ → v γ₀ x₀ → v γ₁ x₁ → Sort w)
(refl : Π {i : Γ} {γ : EΓ.v i} {x : X i} (a : v γ x), e (EΓ.refl γ) a a)

/-- Extra data associated to the judgment `Γ ⊢ t : X`.
Both `X` and `t` are represented as functions on the packed context `⟦Γ⟧`. -/
structure edge_ctx_tm {Γ : Sort*} (EΓ : edge_ctx Γ) {X : Γ → Sort*} (EX : edge_ctx_ty EΓ X)
  (t : Π i, X i) :=
(v : Π {i : Γ} (a : EΓ.v i), EX.v a (t i))
(e : Π {i₀ i₁ : Γ} {a₀ : EΓ.v i₀} {a₁ : EΓ.v i₁} (e : EΓ.e a₀ a₁), EX.e e (v a₀) (v a₁))

/-- Any context can be given the "discrete" `edge_ctx` structure. -/
def discrete_edge_ctx (Γ : Sort u) : edge_ctx Γ :=
{ v := λ _, true,
  e := λ i₀ i₁ _ _, i₀ = i₁,
  refl := λ i _, rfl }

/-- The extra data associated to the empty context. -/
def unit_edge_ctx : edge_ctx unit :=
discrete_edge_ctx unit

/-- Any type family can be given the "discrete" `edge_ctx_ty` structure
over the discrete `edge_ctx` structure on the index type.
This is appropriate for all types whose definition does not use `Type`. -/
def discrete_edge_ctx_ty {Γ : Sort*} (X : Γ → Sort u) :
  edge_ctx_ty (discrete_edge_ctx Γ) X :=
{ v := λ _ _ _, true,
  e := λ i₀ i₁ _ _ x₀ x₁ r _ _, x₀ =[r] x₁,
  refl := λ i _ x _, deq.refl x }

/-- Extra data corresponding to the "context extension" formation rule

  ⊢ Γ ctx   Γ ⊢ α type
 ----------------------
     ⊢ Γ, x : α ctx
-/
def edge_ctx.extend {Γ : Sort*} (EΓ : edge_ctx Γ) {A : Γ → Sort*} (EA : edge_ctx_ty EΓ A) :
  edge_ctx (Σ γ, A γ) :=
sorry

/-- Extra data corresponding to the "weakening" structural rule

  ⊢ Γ ctx   Γ ⊢ α type   Γ ⊢ β type
 -----------------------------------
        Γ, x : α ⊢ β type
-/
def edge_ctx_ty.extend {Γ : Sort*} {EΓ : edge_ctx Γ} {A : Γ → Sort*} (EA : edge_ctx_ty EΓ A)
  {B : Γ → Sort*} (EB : edge_ctx_ty EΓ B) : edge_ctx_ty (EΓ.extend EA) (λ p, B p.1) :=
sorry

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
sorry

/-- Extra data corresponding to the "var" structural rule

  ⊢ Γ ctx   Γ ⊢ α type
 ----------------------
    Γ, a : α ⊢ a : α
-/
def last_var_ctx_tm {Γ : Sort*} (EΓ : edge_ctx Γ) {A : Γ → Sort*} (EA : edge_ctx_ty EΓ A) :
  edge_ctx_tm (EΓ.extend EA) (EA.extend EA) (λ (p : Σ i, A i), p.2) :=
sorry

/-- Extra data corresponding to a type in an empty context: `• ⊢ α type`. -/
def edge_ty (A : Sort u) := edge_ctx_ty unit_edge_ctx (λ _, A)

-- TODO: more concise constructor for `edge_ty`, not involving a zillion underscores?
def type_edge_ty : edge_ty Type :=
{ v := λ _ _ _, true,
  e := λ _ _ _ _ X Y _ _ _, X ≃ Y,
  refl := λ _ _ X _, equiv.refl X }

def prop_edge_ty : edge_ty Prop :=
{ v := λ _ _ _, true,
  e := λ _ _ _ _ p q _ _ _, p ↔ q,
  refl := λ _ _ p _, iff.refl p }

-- TODO: similar `edge_tm` type for closed terms.

/-- Weakening rule for constants:

  • ⊢ α type
 ------------
  Γ ⊢ α type
-/
def gen_edge_ty {A : Sort*} (EA : edge_ty A) {Γ : Sort*} {EΓ : edge_ctx Γ} : edge_ctx_ty EΓ (λ _, A) :=
sorry

/-- Extra data corresponding to Russell-style universes:

  ⊢ Γ ctx   Γ ⊢ α : Type
 ------------------------
        Γ ⊢ α type
-/
def univ_ctx_ty {Γ : Sort*} (EΓ : edge_ctx Γ) {A : Γ → Type} (EA : edge_ctx_tm EΓ (gen_edge_ty type_edge_ty) A) :
  edge_ctx_ty EΓ A :=
sorry

end scone
