import ThreeIntersections
import ThreeIntersectionsQuadrangle

/-!
The finite, kernel-checked portion of the 8×8 rectangle-sharing example.

This file checks a three-paid-union construction, the seven-cell fooling
set, and the impossibility of two paid unions. The stronger subcube
obstruction is proved in the subsequent `ThreeIntersectionsCubeGap` and
`ThreeIntersectionsBoxes` modules, which import this construction.
-/
namespace ThreeIntersectionsRectangleGap
open Set TwoIntersections ThreeIntersectionsQuadrangle

abbrev Cell := Fin 8 × Fin 8

def rowMasks : Fin 8 → Nat := ![129, 130, 4, 136, 16, 160, 64, 213]

def zero : Set Cell := {p : Cell | (rowMasks p.1).testBit p.2.val = true}

def rectRows : Fin 6 → Nat := ![42, 212, 153, 230, 135, 248]
def rectCols : Fin 6 → Nat := ![170, 84, 153, 230, 135, 248]

def rect (i : Fin 6) : Set Cell :=
  {r : Fin 8 | (rectRows i).testBit r.val = true} ×ˢ
    {c : Fin 8 | (rectCols i).testBit c.val = true}

theorem rect_rectangle (i : Fin 6) : Rectangle (rect i) := ⟨_, _, rfl⟩

theorem shared_diamond :
    zero = (rect 2 ∪ (rect 3 ∩ (rect 0 ∪ rect 1))) ∩
      (rect 4 ∪ (rect 5 ∩ (rect 0 ∪ rect 1))) := by
  ext p
  revert p
  unfold zero rowMasks rect rectRows rectCols
  decide +kernel

theorem three : ThreeIntersections.Three Rectangle zero := by
  apply (ThreeIntersections.rectangle_normal_iff zero).mpr
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rect 0, rect 1, rect 2, rect 3,
    rect 4, rect 5, rect_rectangle 0, rect_rectangle 1, rect_rectangle 2,
    rect_rectangle 3, rect_rectangle 4, rect_rectangle 5, shared_diamond⟩)))

def witness (i : Fin 7) : Cell := (i.castSucc, i.castSucc)

theorem witness_fooling : Fooling zero witness := by
  unfold Fooling zero rowMasks witness
  decide +kernel

theorem cover_bound {n : Nat} (r : Fin n → Set Cell)
    (hr : ∀ i, Rectangle (r i))
    (hc : ∀ p, p ∈ zero ↔ ∃ i, p ∈ r i) : 7 ≤ n := by
  have h := fooling_cover_bound witness_fooling r hr
    (fun i p hp => (hc p).mpr ⟨i, hp⟩)
    (fun i => (hc (witness i)).mp (witness_fooling.1 i))
  simpa only [Fintype.card_fin] using h

private theorem rect_inter {a b : Set Cell} (ha : Rectangle a)
    (hb : Rectangle b) : Rectangle (a ∩ b) := by
  obtain ⟨ar, ac, rfl⟩ := ha
  obtain ⟨br, bc, rfl⟩ := hb
  refine ⟨ar ∩ br, ac ∩ bc, ?_⟩
  ext p
  simp only [Set.mem_inter_iff, Set.mem_prod]
  tauto

/-- pjscruggs's two-gate theorem plus the seven-cell fooling set proves that
the displayed three-gate construction is optimal among circuits. -/
theorem not_two : ¬ Two Rectangle zero := by
  intro h
  have hn := (TwoIntersections.rectangle_normal_iff zero).mp h
  rcases hn with ⟨a, b, c, ha, hb, hc, hz⟩ | ⟨a, b, c, d, ha, hb, hc, hd, hz⟩
  · let r : Fin 4 → Set Cell := ![a, b, c, c]
    have hr : ∀ i, Rectangle (r i) := by
      intro i
      fin_cases i <;> simpa [r] using (by assumption : Rectangle _)
    have hh : ∀ p, p ∈ zero ↔ ∃ i, p ∈ r i := by
      intro p
      rw [hz]
      simp [r, Fin.exists_fin_succ]
      tauto
    have impossible := cover_bound r hr hh
    omega
  · let r : Fin 4 → Set Cell := ![a ∩ c, a ∩ d, b ∩ c, b ∩ d]
    have hr : ∀ i, Rectangle (r i) := by
      intro i
      fin_cases i
      · exact rect_inter ha hc
      · exact rect_inter ha hd
      · exact rect_inter hb hc
      · exact rect_inter hb hd
    have hh : ∀ p, p ∈ zero ↔ ∃ i, p ∈ r i := by
      intro p
      rw [hz]
      simp [r, Fin.exists_fin_succ]
      tauto
    have impossible := cover_bound r hr hh
    omega

theorem exact_three : ThreeIntersections.Three Rectangle zero ∧ ¬ Two Rectangle zero :=
  ⟨three, not_two⟩

/- The following statement, motivated by the subcube argument in
   audits/THREE_INTERSECTION_DERIVATION.md, is proved in the subsequent
   `ThreeIntersectionsBoxes` module to keep the imports acyclic:

theorem not_three_pair_products :
    ¬ ∃ a b c d e f : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      zero = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f)

The seven-cell fooling set excludes the other three formula forms after
expanding them into at most six rectangles. `ThreeIntersectionsFormula`
provides the separate costed-formula syntax and four-shape normalization;
the final separation combines these ingredients.
-/

#print axioms shared_diamond
#print axioms witness_fooling
#print axioms exact_three
end ThreeIntersectionsRectangleGap
