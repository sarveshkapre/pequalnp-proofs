import Mathlib.Tactic

/-! Simulate a Boolean DAG in the edge-set model, retaining both polarities.
A gate is AND with available complemented wires. This is the usual AND-inverter
representation of an AND/OR/NOT circuit. Every available unary test has its
complement available, since arbitrary row and column subsets are allowed. -/
namespace PlaneSharing.Dual
open Set

private abbrev Family (α : Type) := Set (Set α)
private def free (s : Family α) : Family α := {z | ∃ t ⊆ s, ⋃₀ t = z}

private theorem keep {s : Family α} {a : Set α} (ha : a ∈ s) : a ∈ free s :=
  ⟨{a}, Set.singleton_subset_iff.mpr ha, Set.sUnion_singleton _⟩

private theorem merge {s : Family α} {a b : Set α} (ha : a ∈ s) (hb : b ∈ s) :
    a ∪ b ∈ free s := by
  refine ⟨{a,b},?_,by simp⟩
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact ha
  · obtain rfl := Set.mem_singleton_iff.mp hz
    exact hb

private def Paid (base : Family α) (k : Nat) (v : Family α) : Prop :=
  ∀ P : Nat → Family α → Prop, P 0 (free base) →
    (∀ i W a b, P i W → a ∈ W → b ∈ W → P (i+1) (free (insert (a ∩ b) W))) → P k v

private theorem step {base u v : Family α} {i : Nat} {a b : Set α}
    (inc : u ⊆ v) (legal : Paid base i v)
    (ha : a ∈ u) (hb : b ∈ u) (hna : aᶜ ∈ u) (hnb : bᶜ ∈ u) :
    ∃ w : Family α, insert (a ∩ b) (insert (a ∩ b)ᶜ u) ⊆ w ∧ Paid base (i+1) w := by
  refine ⟨free (insert (a ∩ b) v),?_,?_⟩
  · intro z hz
    rcases hz with rfl | rfl | hz
    · exact keep (Set.mem_insert ..)
    · rw [Set.compl_inter]
      exact merge (Set.mem_insert_of_mem _ (inc hna)) (Set.mem_insert_of_mem _ (inc hnb))
    · exact keep (Set.mem_insert_of_mem _ (inc hz))
  · intro P start extend
    exact extend _ _ _ _ (legal P start extend) (inc ha) (inc hb)
end PlaneSharing.Dual

open PlaneSharing.Dual in
theorem PEqualNP.PlaneSharing.DualRail :
    ∀ (m n k : Nat),
  let R := Set (Fin m × Fin n)
  let B : Set R := {z | (∃ a : Set (Fin m), z = Set.prod a Set.univ) ∨
                         (∃ b : Set (Fin n), z = Set.prod Set.univ b)}
  let free := fun (s : Set R) => {z : R | ∃ t ⊆ s, ⋃₀ t = z}
  ∀ U : Set R,
    (∀ P : Nat → Set R → Prop, P 0 B →
      (∀ i W (a b : R), P i W → a ∈ W → b ∈ W → aᶜ ∈ W → bᶜ ∈ W →
        P (i+1) (insert (a ∩ b) (insert (a ∩ b)ᶜ W))) → P k U) →
    ∃ V : Set R, U ⊆ V ∧
      ∀ P : Nat → Set R → Prop, P 0 (free B) →
        (∀ i W (a b : R), P i W → a ∈ W → b ∈ W →
          P (i+1) (free (insert (a ∩ b) W))) → P k V := by
  intro m n k
  dsimp only
  intro U h
  let base : Family (Fin m × Fin n) :=
    {z | (∃ a : Set (Fin m), z = Set.prod a Set.univ) ∨
         (∃ b : Set (Fin n), z = Set.prod Set.univ b)}
  apply h (fun i W => ∃ V, W ⊆ V ∧ Paid base i V)
  · exact ⟨free base, fun _ ha => keep ha, fun _ start _ => start⟩
  · rintro i W a b ⟨v,inc,legal⟩ ha hb hna hnb
    exact step inc legal ha hb hna hnb
