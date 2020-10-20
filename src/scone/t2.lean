import scone.edge

-- Demo file.

open scone

/- The type of "Hausdorffness", or any other property of a topological space.
Here, to stick close to the primitives, we just represent a topology as
a collection of (open) sets, and omit the axioms. -/
def A : Type 1 := Π (X : Type), ((X → Prop) → Prop) → Prop

def edge_A : edge_ty A :=
begin
  unfold A,                     -- optional
  -- • ⊢ Π (X : Type), ((X → Prop) → Prop) → Prop) type
  refine pi_edge_ctx_ty _ type_edge_ty _,
  -- X : Type ⊢ ((X → Prop) → Prop) → Prop) type
  refine pi_edge_ctx_ty _ _ (gen_edge_ty prop_edge_ty),
  refine pi_edge_ctx_ty _ _ (gen_edge_ty prop_edge_ty),
  refine pi_edge_ctx_ty _ _ (gen_edge_ty prop_edge_ty),
  -- X : Type ⊢ X type
  -- For this we need Russell-style universes plus the variable rule.
  refine univ_ctx_ty _ _,
  -- X : Type ⊢ X : Type
  refine last_var_ctx_tm _ _,
  done
end

/- The property of being a Hausdorff space:
any two distinct points are separated by disjoint open sets. -/
def T₂ : A :=
λ X τ,
∀ (x y : X), (x = y → false) →
∃ (U V : X → Prop), τ U ∧ τ V ∧ U x ∧ V y ∧
∀ (z : X), U z → V z → false

-- TODO: By a similar process, prove
-- def edge_T₂ : edge_ctx_tm unit_edge_ctx edge_A (λ _, T₂) := sorry

variables {X Y : Type} (τX : (X → Prop) → Prop) (τY : (Y → Prop) → Prop)
variables (e : X ≃ Y) (he : ∀ (s : set X), τX s ↔ τY (e.symm ⁻¹' s))
variables {F : A} (hF : edge_ctx_tm unit_edge_ctx edge_A.{0 0} (λ _, F))
include he hF

lemma invariant : F X τX ↔ F Y τY :=
begin
  have := hF.e ⟨rfl⟩,
  swap, exact (), swap, exact (), swap, exact (),
  specialize this X Y (discrete_edge_ctx_ty _) (discrete_edge_ctx_ty _),
  specialize this ⟨e, λ x, equiv.refl _, _⟩,
  swap,
  { rintros x₀ x₁ ⟨⟩ ⟨⟩,
    -- need to check that the function `e` "preserves edges",
    -- which is automatic because `X` is discrete
    change plift (_ =[rfl] _) ≃ plift (_ =[rfl] _),
    sorry },
  specialize this τX τY,
  -- next we need a proof that τX "preserves edges",
  -- which is automatic because `X → Prop` is discrete,
  -- and the same for τY
  specialize this sorry sorry,
  -- now we need to use the compatibility of `e` and `τX`, `τY` somehow
  specialize this sorry,
  -- eliminate a `plift`
  cases this with h,
  exact h
end
