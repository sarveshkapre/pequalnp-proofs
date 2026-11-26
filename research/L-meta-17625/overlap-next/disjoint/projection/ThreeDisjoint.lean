import Realizability
import PathRemainder

namespace DisjointEdgeBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Once both earlier configurations are excluded, every two different
residual edges in a three-edge counterexample must be vertex-disjoint. -/
theorem failure_disjoint_of_exclusion (finite : FiniteExclusion)
    (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (failure : ¬GeneralThree.wireBound G C S)
    {p q : Sym2 (Fin n)} (hp : p ∈ Ustar G C) (hq : q ∈ Ustar G C) (ne : p ≠ q) :
    ∀ z : Fin n, z ∈ p → z ∉ q := by
  classical
  obtain ⟨r,hr,isolated⟩ := PathRemainder.isolated_edge four bip least top three S f inj partners failure
  intro b bp bq
  have pr : p ≠ r := by
    rintro rfl
    exact isolated q hq ne.symm b bp bq
  have qr : q ≠ r := by
    rintro rfl
    exact isolated p hp ne b bq bp
  have edges : G.edgeFinset.Nonempty := ⟨r,(Finset.mem_sdiff.mp hr).1⟩
  obtain ⟨a,rfl⟩ := Sym2.mem_iff_exists.mp bp
  obtain ⟨c,rfl⟩ := Sym2.mem_iff_exists.mp bq
  induction r using Sym2.ind with
  | h d e =>
    have ba := (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hp).1).ne
    have bc := (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hq).1).ne
    have de := (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hr).1).ne
    have ac : a ≠ c := fun h => ne (h ▸ rfl)
    have db := isolated _ hp pr d (Sym2.mem_mk_left d e)
    have eb := isolated _ hp pr e (Sym2.mem_mk_right d e)
    have dc := isolated _ hq qr d (Sym2.mem_mk_left d e)
    have ec := isolated _ hq qr e (Sym2.mem_mk_right d e)
    simp only [Sym2.mem_iff,not_or] at db eb dc ec
    let v : Fin 5 → Fin n := ![a,b,c,d,e]
    have distinct : Function.Injective v := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [v]
    have sub : PrivateMatching.shape (v 0) (v 1) (v 2) (v 3) (v 4) ⊆ Ustar G C := by
      intro x m
      simp only [PrivateMatching.shape,Finset.mem_insert,Finset.mem_singleton] at m
      rcases m with rfl|rfl|rfl
      · change s(a,b) ∈ _; rwa [Sym2.eq_swap]
      · exact hq
      · exact hr
    have sz : (PrivateMatching.shape (v 0) (v 1) (v 2) (v 3) (v 4)).card = 3 := by
      simp [PrivateMatching.shape,distinct.eq_iff]
    have shape := (Finset.eq_of_subset_of_card_le sub (le_of_eq (three.trans sz.symm))).symm
    exact failure (bound_of_exclusion finite four bip edges least top S f inj partners v distinct shape)

#print axioms failure_disjoint_of_exclusion
end DisjointEdgeBound
