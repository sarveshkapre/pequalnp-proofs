import QuadrangleSharedReduction
import PartialRectangleColoring

/-!
# Exact coloring criterion for a shared three-union diamond

Despite the filename, these results are independent of the quadrangle,
finiteness, and C4-freeness. They eliminate the two filtered arm rectangles
using least rectangular hulls, then replace the shared pair of rectangles by
an exact two-colorability condition on the residual positive cells.
-/
namespace QuadrangleSharedColoring
open Set TwoIntersections QuadrangleSharedReduction PartialRectangleColoring

variable {ι κ : Type*}

/-- For fixed unfiltered arms `c,e`, a shared diamond exists exactly when their
intersection is valid and the residual forbidden-cross relation is two-colorable.
The reverse implication constructs the filtered arms as the least hulls. -/
theorem fixed_diamond_iff_two_coloring (z c e : Set (ι × κ)) :
    (∃ a b d f : Set (ι × κ),
      Rectangle a ∧ Rectangle b ∧ Rectangle d ∧ Rectangle f ∧
      z = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b)))) ↔
    c ∩ e ⊆ z ∧
      ∃ color : ↥(z \ (c ∩ e)) → Fin 2,
        Compatible (z \ (c ∩ e)) (forbidden z c e) color := by
  constructor
  · rintro ⟨a,b,d,f,ha,hb,hd,hf,hz⟩
    obtain ⟨hi,hcover,havoid⟩ := diamond_partial_cover hd hf hz
    exact ⟨hi,(two_rectangles_iff_coloring _ _).mp ⟨a,b,ha,hb,hcover,havoid⟩⟩
  · rintro ⟨hi,hcolor⟩
    obtain ⟨a,b,ha,hb,hcover,havoid⟩ := (two_rectangles_iff_coloring _ _).mpr hcolor
    exact ⟨a,b,leftHull z c,leftHull z e,ha,hb,hull_rectangle _,hull_rectangle _,
      diamond_reconstruction hi hcover havoid⟩

/-- Complete semantic criterion for the genuine shared branch of the
three-union normal form. Only the two unfiltered rectangles remain to choose;
their residual cell-incompatibility graph must admit two colors. -/
theorem diamond_iff_two_coloring (z : Set (ι × κ)) :
    (∃ a b c d e f : Set (ι × κ),
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      z = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b)))) ↔
    ∃ c e : Set (ι × κ), Rectangle c ∧ Rectangle e ∧ c ∩ e ⊆ z ∧
      ∃ color : ↥(z \ (c ∩ e)) → Fin 2,
        Compatible (z \ (c ∩ e)) (forbidden z c e) color := by
  constructor
  · rintro ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz⟩
    exact ⟨c,e,hc,he,(fixed_diamond_iff_two_coloring z c e).mp
      ⟨a,b,d,f,ha,hb,hd,hf,hz⟩⟩
  · rintro ⟨c,e,hc,he,hi,hcolor⟩
    obtain ⟨a,b,d,f,ha,hb,hd,hf,hz⟩ :=
      (fixed_diamond_iff_two_coloring z c e).mpr ⟨hi,hcolor⟩
    exact ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz⟩

/-- A complete obstruction criterion. Unlike a fooling-set condition, it
retains every obstruction to two-colorability, including longer odd cycles. -/
theorem no_diamond_iff_no_two_coloring (z : Set (ι × κ)) :
    (¬ ∃ a b c d e f : Set (ι × κ),
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      z = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b)))) ↔
    ∀ c e : Set (ι × κ), Rectangle c → Rectangle e → c ∩ e ⊆ z →
      ¬ ∃ color : ↥(z \ (c ∩ e)) → Fin 2,
        Compatible (z \ (c ∩ e)) (forbidden z c e) color := by
  rw [diamond_iff_two_coloring]
  simp only [not_exists, not_and]

#print axioms fixed_diamond_iff_two_coloring
#print axioms diamond_iff_two_coloring
#print axioms no_diamond_iff_no_two_coloring
end QuadrangleSharedColoring
