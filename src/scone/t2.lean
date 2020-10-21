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
    rw [deq_iff_eq, deq_iff_eq],
    refine equiv.plift.trans ((equiv.of_iff _).trans equiv.plift.symm),
    symmetry,
    apply equiv.apply_eq_iff_eq },
  specialize this τX τY,
  -- next we need a proof that τX "preserves edges",
  -- which is automatic because `X → Prop` is discrete,
  -- and the same for τY
  specialize this _, swap,
  { fsplit,
    { rintro (s : set X) hs,
      exact ⟨⟩ },
    { rintro (s₀ : set X) (s₁ : set X) hs₀ hs₁ h,
      suffices : s₀ = s₁,
      { constructor,
        rw this },
      ext x,
      specialize h x x () () ⟨deq.refl _⟩,
      exact h.down } },
  specialize this _, swap,
  { fsplit,
    { rintro (s : set Y) hs,
      exact ⟨⟩ },
    { rintro (s₀ : set Y) (s₁ : set Y) hs₀ hs₁ h,
      suffices : s₀ = s₁,
      { constructor,
        rw this },
      ext y,
      specialize h y y () () ⟨deq.refl _⟩,
      exact h.down } },
  -- now we need to use the compatibility of `e` and `τX`, `τY`
  specialize this _, swap,
  { rintros (s : set X) (t : set Y) _ _ h,
    suffices : t = e.symm ⁻¹' s,
    { change plift (τX s ↔ τY t),
      rw this,
      exact ⟨he s⟩ },
    ext y,
    specialize h (e.symm y) y () (),
    specialize h ⟨_⟩, swap,
    { conv { whnf },
      conv_lhs { change e (e.symm y) },
      rw e.apply_symm_apply },
    exact h.down.symm },
  exact this.down
end
