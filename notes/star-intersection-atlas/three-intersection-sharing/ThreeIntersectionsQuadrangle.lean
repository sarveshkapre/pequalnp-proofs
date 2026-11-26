import TwoIntersections

/-!
A first structural exclusion for pjscruggs's quadrangle obstruction.

The general lemma is the rectangle fooling-set lower bound. The concrete
application excludes the union-of-four-rectangles branch of the three-gate
normal form. It does not exclude the other four branches.
-/
namespace ThreeIntersectionsQuadrangle
open Set TwoIntersections

variable {ι κ β γ : Type*}

/-- Every pair of selected zero cells has at least one nonzero cross-cell. -/
def Fooling (z : Set (ι × κ)) (f : β → ι × κ) : Prop :=
  (∀ i, f i ∈ z) ∧ ∀ i j, i ≠ j →
    ((f i).1, (f j).2) ∉ z ∨ ((f j).1, (f i).2) ∉ z

/-- Each zero rectangle can cover at most one cell of a fooling set. -/
theorem fooling_rectangle_unique {z : Set (ι × κ)} {f : β → ι × κ}
    (hf : Fooling z f) {r : Set (ι × κ)} (hr : Rectangle r)
    (hs : r ⊆ z) {i j : β} (hi : f i ∈ r) (hj : f j ∈ r) : i = j := by
  by_contra hne
  obtain ⟨rows, cols, rfl⟩ := hr
  change (f i).1 ∈ rows ∧ (f i).2 ∈ cols at hi
  change (f j).1 ∈ rows ∧ (f j).2 ∈ cols at hj
  rcases hf.2 i j hne with h | h
  · exact h (hs ⟨hi.1, hj.2⟩)
  · exact h (hs ⟨hj.1, hi.2⟩)

/-- A cover by `γ` zero rectangles needs at least as many members as a
fooling set indexed by `β`. -/
theorem fooling_cover_bound [Fintype β] [Fintype γ]
    {z : Set (ι × κ)} {f : β → ι × κ} (hf : Fooling z f)
    (r : γ → Set (ι × κ)) (hr : ∀ j, Rectangle (r j))
    (hs : ∀ j, r j ⊆ z) (cover : ∀ i, ∃ j, f i ∈ r j) :
    Fintype.card β ≤ Fintype.card γ := by
  classical
  choose g hg using cover
  apply Fintype.card_le_of_injective g
  intro i j hij
  apply fooling_rectangle_unique hf (hr (g i)) (hs (g i)) (hg i)
  simpa only [hij] using hg j

abbrev Cell := Fin 5 × Fin 6

/-- The unchanged five row masks from pjscruggs's 5×6 certificate. -/
def mask : Fin 5 → Nat := ![49, 42, 22, 13, 3]

def graph : Set Cell := {p : Cell | (mask p.1).testBit p.2.val = true}

def zero : Set Cell := graphᶜ

/-- `(A,BC), (B,AD), (C,BD), (D,AC), (X,CD)`. -/
def witness : Fin 5 → Cell := ![(0, 1), (1, 0), (2, 3), (3, 4), (4, 2)]

theorem witness_fooling : Fooling zero witness := by
  unfold Fooling zero graph witness mask
  decide +kernel

/-- The first branch of the three-intersection normal form is impossible. -/
theorem no_union_four_rectangles :
    ¬ ∃ a b c d : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
        zero = (a ∪ b) ∪ (c ∪ d) := by
  rintro ⟨a, b, c, d, ha, hb, hc, hd, hz⟩
  let r : Fin 4 → Set Cell := ![a, b, c, d]
  have hr : ∀ i, Rectangle (r i) := by
    intro i
    fin_cases i <;> simpa [r] using (by assumption : Rectangle _)
  have hs : ∀ i, r i ⊆ zero := by
    intro i x hx
    rw [hz]
    fin_cases i
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  have cover : ∀ i, ∃ j, witness i ∈ r j := by
    intro i
    have hi := witness_fooling.1 i
    rw [hz] at hi
    rcases hi with (h | h) | (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  have impossible := fooling_cover_bound witness_fooling r hr hs cover
  norm_num at impossible

#print axioms fooling_cover_bound
#print axioms witness_fooling
#print axioms no_union_four_rectangles
end ThreeIntersectionsQuadrangle
