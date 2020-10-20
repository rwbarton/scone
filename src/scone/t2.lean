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
