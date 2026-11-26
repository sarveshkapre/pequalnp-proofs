import PEqualNP.ThreeGateGain.GainSelection

/-! Forced edges between centers, detected using only the two sets of leaf types. -/
namespace GainForced
open Finset TriangleOptimality GainSelection
open scoped Classical

variable {P L I J : Type*}

/-- Candidate partner sees the designated leaf and no other selected leaf. -/
def exclusive (H : I → J → Prop) (leaves : Finset I) (i : I) (j : J) : Prop :=
  H i j ∧ ∀ i' ∈ leaves, H i' j → i' = i

/-- Every possible assignment of centers to these leaves creates the crossing. -/
def forced (H : I → J → Prop) (RL : Finset I) (CL : Finset J) (i : I) (j : J) : Prop :=
  ∀ v, exclusive H RL i v → ∀ u, exclusive (fun j i => H i j) CL j u → H u v

noncomputable def forcedCount (H : I → J → Prop) (RL : Finset I) (CL : Finset J) : ℕ :=
  ((RL ×ˢ CL).filter fun e => forced H RL CL e.1 e.2).card

theorem count_edges (F : I → J → Prop) (X : Finset I) (Y : Finset J) :
    (((X ×ˢ Y).filter fun e => F e.1 e.2).card:ℤ) = edges F X Y := by
  classical
  rw [edges, ← sum_product']
  simp [hit]

theorem real_partner {H : I → J → Prop} {r : P → I} {c : L → J} {A : Finset P} {B : Finset L}
    (s : Side H r c A B) (p : {p // p ∈ s.centers}) :
    exclusive (fun j i => H i j) s.leafTypes (s.leaf p) (r p.val) := by
  refine ⟨s.attached p,?_⟩
  intro j hj h
  obtain ⟨q,rfl⟩ := s.leaf_mem_iff.mp hj
  apply congrArg s.leaf
  exact Subtype.ext (s.unique q p.val (s.active p.property) h).symm

theorem forced_bound {H : I → J → Prop} {r : P → I} {c : L → J} {A : Finset P} {B : Finset L}
    (s : Side H r c A B) (t : Side (fun j i => H i j) c r B A) :
    (forcedCount H t.leafTypes s.leafTypes:ℤ) ≤
      edges (fun p l => H (r p) (c l)) s.centers t.centers := by
  classical
  unfold forcedCount
  rw [count_edges, edges, edges, Side.leafTypes, Side.leafTypes,
      sum_image (fun _ _ _ _ e => t.leaf_injective e)]
  simp_rw [sum_image (fun _ _ _ _ e => s.leaf_injective e)]
  rw [sum_comm]
  conv_rhs => rw [← s.centers.sum_attach]; arg 2; ext p; rw [← t.centers.sum_attach]
  apply sum_le_sum; intro p _
  apply sum_le_sum; intro l _
  change hit (forced H t.leafTypes s.leafTypes) (t.leaf l) (s.leaf p) ≤ hit H (r p.val) (c l.val)
  by_cases h : forced H t.leafTypes s.leafTypes (t.leaf l) (s.leaf p)
  · have yes := h (c l.val) (real_partner t l) (r p.val) (real_partner s p)
    simp [hit,h,yes]
  · by_cases yes : H (r p.val) (c l.val) <;> simp [hit,h,yes]

#print axioms forced_bound
end GainForced
