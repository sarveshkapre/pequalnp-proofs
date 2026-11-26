import QuadrangleFormulaExclusions
import QuadrangleBaseUnion
import QuadrangleSharedReduction
import QuadrangleSharedFiniteData
import QuadranglePadding
import ThreeIntersectionsFormula
import ThreeIntersectionsRepresentation

/-!
Structural results for pjscruggs's quadrangle. The four formula shapes are
excluded geometrically. The shared diamond is excluded by a checked tree of
three-cell partial fooling obstructions. The representation bridge accounts
for arbitrary free unions, reuse, and the duplicated sixth row.
-/
namespace QuadrangleStructural
open Set TwoIntersections ThreeIntersectionsQuadrangle
open ThreeIntersectionsSharingGap ThreeIntersectionsFormula
open QuadrangleFormulaExclusions QuadrangleBaseUnion

theorem no_first_four : ¬ FirstFour Rectangle zero := by
  rintro (h | h | h | h)
  · exact no_union_four_rectangles h
  · exact no_three_by_two h
  · exact no_three_two_factors h
  · exact no_base_union_two_by_two h

/-- Free intersections remain unrestricted; paid union occurrences are counted
separately in every subtree of the zero-set formula. -/
theorem formula_lower_bound {n : Nat} (h : Formula Rectangle n zero) : 4 ≤ n := by
  by_contra hn
  have hsmall : n ≤ 3 := by omega
  apply no_first_four
  exact formula_first_four
    (fun ha hb => QuadrangleSquareObstruction.rectangle_inter ha hb) h hsmall

def zeroRow (i : Fin 5) : Set Cell := {i} ×ˢ {j | (i, j) ∈ zero}

theorem zeroRow_rectangle (i : Fin 5) : Rectangle (zeroRow i) := ⟨_, _, rfl⟩

/-- The row-by-row construction is the zero-set version of pjscruggs's
four-intersection upper bound. -/
theorem formula_four : Formula Rectangle 4 zero := by
  have hz : zero = (((zeroRow 0 ∪ zeroRow 1) ∪ zeroRow 2) ∪ zeroRow 3) ∪ zeroRow 4 := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> simp [zeroRow]
  rw [hz]
  exact .join (.join (.join (.join (.base (zeroRow_rectangle 0))
    (.base (zeroRow_rectangle 1))) (.base (zeroRow_rectangle 2)))
    (.base (zeroRow_rectangle 3))) (.base (zeroRow_rectangle 4))

theorem exact_formula_minimum :
    Formula Rectangle 4 zero ∧ ∀ n, Formula Rectangle n zero → 4 ≤ n :=
  ⟨formula_four, fun _ => formula_lower_bound⟩

/-- All other three-gate topologies have been excluded. -/
theorem three_requires_shared
    (h : QuadrangleHandoff.Represents 3 QuadrangleHandoff.graph) :
    ∃ a b c d e f : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      zero = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b))) := by
  have hn := ThreeIntersectionsRepresentation.quadrangle_three_normal h
  rcases hn with h | h | h | h | h
  · exact False.elim (no_union_four_rectangles h)
  · exact False.elim (no_three_by_two h)
  · exact False.elim (no_three_two_factors h)
  · exact False.elim (no_base_union_two_by_two h)
  · exact h

/-- Neither residual hull can contain the other in a surviving shared shape. -/
theorem three_requires_incomparable_hulls
    (h : QuadrangleHandoff.Represents 3 QuadrangleHandoff.graph) :
    ∃ a b c d e f : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      zero = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b))) ∧
      ¬ QuadrangleSharedReduction.leftHull zero c ⊆ QuadrangleSharedReduction.leftHull zero e ∧
      ¬ QuadrangleSharedReduction.leftHull zero e ⊆ QuadrangleSharedReduction.leftHull zero c := by
  obtain ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz⟩ := three_requires_shared h
  refine ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz,?_,?_⟩
  · intro hce
    exact no_base_union_two_by_two
      (QuadrangleSharedReduction.nested_residual_formula ha hb hc hd he hf hz hce)
  · intro hec
    apply no_base_union_two_by_two
    apply QuadrangleSharedReduction.nested_residual_formula ha hb he hf hc hd _ hec
    rw [Set.inter_comm]
    exact hz

/-- None of the five possible three-intersection shapes represents the zeros. -/
theorem no_normal : ¬ ThreeIntersections.Normal Rectangle zero := by
  rintro (h | h | h | h | h)
  · exact no_union_four_rectangles h
  · exact no_three_by_two h
  · exact no_three_two_factors h
  · exact no_base_union_two_by_two h
  · exact QuadrangleSharedFinite.no_shared_diamond h

theorem no_three_zero_circuit : ¬ ThreeIntersections.Three Rectangle zero :=
  fun h => no_normal ((ThreeIntersections.rectangle_normal_iff zero).mp h)

/-- The original handoff predicate, with arbitrary free unions and gate reuse,
cannot represent the graph using three paid intersections. -/
theorem lower_bound :
    ¬ QuadrangleHandoff.Represents 3 QuadrangleHandoff.graph := by
  intro h
  exact no_normal (ThreeIntersectionsRepresentation.quadrangle_three_normal h)

theorem four_suffices_three_impossible :
    QuadrangleHandoff.Represents 4 QuadrangleHandoff.graph ∧
      ¬ QuadrangleHandoff.Represents 3 QuadrangleHandoff.graph :=
  ⟨QuadrangleHandoff.four, lower_bound⟩

/-- The upper bound is pjscruggs's unchanged construction; padding excludes
every smaller budget, not merely the budget of exactly three. -/
theorem exact_minimum :
    QuadrangleHandoff.Represents 4 QuadrangleHandoff.graph ∧
      ∀ k, k < 4 → ¬ QuadrangleHandoff.Represents k QuadrangleHandoff.graph :=
  ⟨QuadrangleHandoff.four, QuadrangleHandoff.excludes_smaller lower_bound⟩

#print axioms no_first_four
#print axioms exact_formula_minimum
#print axioms three_requires_shared
#print axioms three_requires_incomparable_hulls
#print axioms no_normal
#print axioms no_three_zero_circuit
#print axioms lower_bound
#print axioms four_suffices_three_impossible
#print axioms exact_minimum
end QuadrangleStructural
