import FourEdges
import SourceBudget

open ResidualDegree PlaneFour
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

namespace PlaneBudget

/-- Four residual edges in a 63-gate candidate leave exactly twelve ordinary
tops, two dirty ANDs and two eligible ORs. -/
theorem four (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
    (small : C.size ≤ 63) (u : (Ustar plane C).card = 4) :
    (junk plane C).card = 2 ∧ centreless plane C = ∅ ∧
    (orN plane C \ lam plane C).card = 2 ∧ (tops plane C).card = 12 := by
  classical
  have edges : plane.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [plane_edges]; decide)
  have present : (Ustar plane C).Nonempty := Finset.card_pos.mp (by omega)
  have resid := Finset.card_sdiff_add_card_eq_card
    (show Ustar plane C ⊆ plane.edgeFinset from Finset.sdiff_subset)
  rw [plane_edges,u] at resid
  obtain ⟨count,cover⟩ := PEqualNP.Outside.L_meta_1491 26 plane C plane_four edges least top
  rw [plane_edges,u] at count
  obtain ⟨K,kc⟩ := min_cover_exists (plane.deleteEdges ↑(Ustar plane C))
  have cap := remaining_edges plane (Ustar plane C) K 4 plane_degree kc.1
  have ordinary := cover K kc
  have someDirty : (junk plane C).Nonempty := by
    obtain ⟨e,he⟩ := present
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨_,_,_,j,hj,_⟩ := PEqualNP.Outside.L_meta_8005.residualTrace least top he
      exact ⟨j,hj⟩
  have pos := Finset.card_pos.mpr someDirty
  have dirty : 2 ≤ (junk plane C).card := by
    by_contra! short
    obtain ⟨Q,covQ,paid⟩ := PEqualNP.Outside.L_meta_8103 26 plane C plane_four edges least top present (by omega)
    have full : (plane.deleteEdges ↑(∅ : Finset (Sym2 (Fin 26)))).IsVertexCover (Q : Set _) :=
      fun _ _ h => covQ _ _ (SimpleGraph.deleteEdges_adj.mp h).1
    have dc := remaining_edges plane ∅ Q 4 plane_degree full
    simp only [Finset.sdiff_empty, plane_edges] at dc
    omega
  have mult : 2 ≤ (centreless plane C).card + (orN plane C \ lam plane C).card := by
    by_contra! low
    have paid := ResidualSourceBudget.pays_with_one_source plane_four least top
      (by change 3 ≤ (Ustar plane C).card; omega) dirty (by
        change (centreless plane C).card + (orN plane C \ lam plane C).card ≤ 1; omega)
      (Ustar plane C) (Finset.Subset.refl _)
    change (Ustar plane C).card + (Ustar plane C).card ≤ (junk plane C).card +
      2*(centreless plane C).card + (orN plane C \ lam plane C).card at paid
    omega
  have emp : centreless plane C = ∅ := Finset.card_eq_zero.mp (by omega)
  have twelve : (tops plane C \ centreless plane C).card = 12 := by omega
  exact ⟨by omega,emp,by omega,by simpa [emp] using twelve⟩

#print axioms four
end PlaneBudget
