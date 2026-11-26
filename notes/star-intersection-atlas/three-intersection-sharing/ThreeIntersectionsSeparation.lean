import ThreeIntersectionsFormula
import ThreeIntersectionsRectangleGap
import ThreeIntersectionsBoxes

/-! Assemble the circuit/formula comparison for the 8×8 sharing example. -/
namespace ThreeIntersectionsSeparation
open Set TwoIntersections ThreeIntersectionsSharingGap
open ThreeIntersectionsRectangleGap ThreeIntersectionsFormula

private theorem rectangles_closed : Closed (@Rectangle (Fin 8) (Fin 8)) := by
  rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
  exact ⟨a ∩ c, b ∩ d, by ext p; simp; tauto⟩

theorem not_first_four_of_not_product
    (hproduct : ¬ ∃ a b c d e f : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧ zero = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f)) :
    ¬ FirstFour Rectangle zero := by
  rintro (⟨a, b, c, d, ha, hb, hc, hd, hz⟩ |
    ⟨a, b, c, d, e, ha, hb, hc, hd, he, hz⟩ |
    ⟨a, b, c, d, e, f, ha, hb, hc, hd, he, hf, hz⟩ |
    ⟨a, b, c, d, e, ha, hb, hc, hd, he, hz⟩)
  · let r : Fin 4 → Set Cell := ![a, b, c, d]
    have hr : ∀ i, Rectangle (r i) := by
      intro i
      fin_cases i <;> simpa [r] using (by assumption : Rectangle _)
    have hh : ∀ p, p ∈ zero ↔ ∃ i, p ∈ r i := by
      intro p
      rw [hz]
      simp [r, Fin.exists_fin_succ]
      tauto
    have h := cover_bound r hr hh
    omega
  · let r : Fin 6 → Set Cell := ![a ∩ d, a ∩ e, b ∩ d, b ∩ e, c ∩ d, c ∩ e]
    have hr : ∀ i, Rectangle (r i) := by
      intro i
      fin_cases i
      · exact rectangles_closed ha hd
      · exact rectangles_closed ha he
      · exact rectangles_closed hb hd
      · exact rectangles_closed hb he
      · exact rectangles_closed hc hd
      · exact rectangles_closed hc he
    have hh : ∀ p, p ∈ zero ↔ ∃ i, p ∈ r i := by
      intro p
      rw [hz]
      simp [r, Fin.exists_fin_succ]
      tauto
    have h := cover_bound r hr hh
    omega
  · exact hproduct ⟨a, b, c, d, e, f, ha, hb, hc, hd, he, hf, hz⟩
  · let r : Fin 5 → Set Cell := ![a, b ∩ d, b ∩ e, c ∩ d, c ∩ e]
    have hr : ∀ i, Rectangle (r i) := by
      intro i
      fin_cases i
      · exact ha
      · exact rectangles_closed hb hd
      · exact rectangles_closed hb he
      · exact rectangles_closed hc hd
      · exact rectangles_closed hc he
    have hh : ∀ p, p ∈ zero ↔ ∃ i, p ∈ r i := by
      intro p
      rw [hz]
      simp [r, Fin.exists_fin_succ]
      tauto
    have h := cover_bound r hr hh
    omega

theorem formula_four : Formula Rectangle 4 zero := by
  rw [shared_diamond]
  exact diamond_four_formula (rect_rectangle 0) (rect_rectangle 1)
    (rect_rectangle 2) (rect_rectangle 3) (rect_rectangle 4) (rect_rectangle 5)

/-- Every formula with at most three paid operations is excluded. -/
theorem formula_lower_bound {n : Nat} (hn : n < 4) :
    ¬ Formula Rectangle n zero := by
  intro h
  exact not_first_four_of_not_product ThreeIntersectionsBoxes.not_three_pair_products
    (formula_first_four rectangles_closed h (by omega))

/-- In this rectangle model, wire reuse saves one paid operation exactly:
circuits need three, while formulas need four. -/
theorem exact_circuit_formula_gap :
    ThreeIntersections.Three Rectangle zero ∧ ¬ Two Rectangle zero ∧
    Formula Rectangle 4 zero ∧ ∀ n, n < 4 → ¬ Formula Rectangle n zero :=
  ⟨three, not_two, formula_four, fun _ hn => formula_lower_bound hn⟩

#print axioms not_first_four_of_not_product
#print axioms formula_four
#print axioms formula_lower_bound
#print axioms exact_circuit_formula_gap
end ThreeIntersectionsSeparation
