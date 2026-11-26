import PEqualNP.Atlas56.ThreeIntersectionsQuadrangle

/-!
# Partial rectangle-cover obstructions

The rectangles must cover the positive cells `P` and avoid the forbidden cells
`B`; their behavior on all other cells is unrestricted. A partial fooling set
contains positive cells with at least one forbidden cross-cell for every pair.
This is the usual rectangle fooling-set argument applied to `Bᶜ`.
-/

namespace QuadranglePartialFooling
open Set TwoIntersections ThreeIntersectionsQuadrangle

variable {ι κ β γ : Type*}

/-- Positive witness cells pairwise separated by a forbidden cross-cell. -/
def PartialFooling (P B : Set (ι × κ)) (f : β → ι × κ) : Prop :=
  (∀ i, f i ∈ P) ∧ ∀ i j, i ≠ j →
    ((f i).1, (f j).2) ∈ B ∨ ((f j).1, (f i).2) ∈ B

/-- A partial cover avoiding `B` requires one rectangle per witness cell. -/
theorem partial_fooling_cover_bound [Fintype β] [Fintype γ]
    {P B : Set (ι × κ)} {f : β → ι × κ} (hf : PartialFooling P B f)
    (r : γ → Set (ι × κ)) (hr : ∀ j, Rectangle (r j))
    (avoid : ∀ j, Disjoint (r j) B)
    (cover : ∀ p ∈ P, ∃ j, p ∈ r j) :
    Fintype.card β ≤ Fintype.card γ := by
  have hs : ∀ j, r j ⊆ Bᶜ := by
    intro j p hp hB
    exact Set.disjoint_left.mp (avoid j) hp hB
  have hc : ∀ i, ∃ j, f i ∈ r j := fun i => cover (f i) (hf.1 i)
  have hF : Fooling Bᶜ f := by
    constructor
    · intro i
      obtain ⟨j, hj⟩ := hc i
      exact hs j hj
    · intro i j hij
      rcases hf.2 i j hij with h | h
      · exact Or.inl (fun hnot => hnot h)
      · exact Or.inr (fun hnot => hnot h)
  exact fooling_cover_bound hF r hr hs hc

/-- Three partially fooling cells cannot be covered by two avoiding rectangles. -/
theorem no_union_two {P B : Set (ι × κ)} {f : Fin 3 → ι × κ}
    (hf : PartialFooling P B f) {a b : Set (ι × κ)}
    (ha : Rectangle a) (hb : Rectangle b)
    (cover : P ⊆ a ∪ b) (avoid : Disjoint (a ∪ b) B) : False := by
  let r : Fin 2 → Set (ι × κ) := ![a, b]
  have hr : ∀ j, Rectangle (r j) := by
    intro j
    fin_cases j <;> simpa [r] using (by assumption : Rectangle _)
  have hs : ∀ j, Disjoint (r j) B := by
    intro j
    apply Set.disjoint_left.mpr
    intro p hp hB
    apply Set.disjoint_left.mp avoid _ hB
    fin_cases j
    · exact Or.inl hp
    · exact Or.inr hp
  have hc : ∀ p ∈ P, ∃ j, p ∈ r j := by
    intro p hp
    rcases cover hp with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have impossible := partial_fooling_cover_bound hf r hr hs hc
  norm_num at impossible

/-- Four partially fooling cells cannot be covered by three avoiding rectangles. -/
theorem no_union_three {P B : Set (ι × κ)} {f : Fin 4 → ι × κ}
    (hf : PartialFooling P B f) {a b c : Set (ι × κ)}
    (ha : Rectangle a) (hb : Rectangle b) (hc : Rectangle c)
    (cover : P ⊆ (a ∪ b) ∪ c) (avoid : Disjoint ((a ∪ b) ∪ c) B) : False := by
  let r : Fin 3 → Set (ι × κ) := ![a, b, c]
  have hr : ∀ j, Rectangle (r j) := by
    intro j
    fin_cases j <;> simpa [r] using (by assumption : Rectangle _)
  have hs : ∀ j, Disjoint (r j) B := by
    intro j
    apply Set.disjoint_left.mpr
    intro p hp hB
    apply Set.disjoint_left.mp avoid _ hB
    fin_cases j
    · exact Or.inl (Or.inl hp)
    · exact Or.inl (Or.inr hp)
    · exact Or.inr hp
  have hcover : ∀ p ∈ P, ∃ j, p ∈ r j := by
    intro p hp
    rcases cover hp with (h | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have impossible := partial_fooling_cover_bound hf r hr hs hcover
  norm_num at impossible

#print axioms partial_fooling_cover_bound
#print axioms no_union_two
#print axioms no_union_three
end QuadranglePartialFooling
