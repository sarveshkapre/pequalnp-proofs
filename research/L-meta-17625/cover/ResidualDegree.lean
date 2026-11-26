import PEqualNP.Outside.L_meta_1491
import PEqualNP.Outside.L_meta_8005
import PEqualNP.Outside.L_meta_8103

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

namespace ResidualDegree

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- Edges outside the deleted set can use at most d slots per cover vertex. -/
theorem remaining_edges (U : Finset (Sym2 (Fin n))) (K : Finset (Fin n)) (d : ℕ)
    (degree : ∀ v, G.degree v ≤ d)
    (cover : (G.deleteEdges (U : Set _)).IsVertexCover (K : Set _)) :
    (G.edgeFinset \ U).card ≤ K.card * d := by
  classical
  have covered : G.edgeFinset \ U ⊆ K.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨member, kept⟩ := Finset.mem_sdiff.mp he
      have adj := SimpleGraph.mem_edgeFinset.mp member
      have dc : (G.deleteEdges (U : Set _)).Adj u v :=
        (SimpleGraph.deleteEdges_adj).mpr ⟨adj, kept⟩
      rcases cover dc with h | h
      · exact Finset.mem_biUnion.mpr ⟨u, h, by
          rw [G.incidenceFinset_eq_filter]; exact Finset.mem_filter.mpr ⟨member, Sym2.mem_mk_left _ _⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨v, h, by
          rw [G.incidenceFinset_eq_filter]; exact Finset.mem_filter.mpr ⟨member, Sym2.mem_mk_right _ _⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card covered
    _ ≤ ∑ v ∈ K, (G.incidenceFinset v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ K, d := Finset.sum_le_sum fun v _ => by simpa using degree v
    _ = _ := by simp

theorem min_cover_exists (G : SimpleGraph (Fin n)) :
    ∃ K : Finset (Fin n), IsMinCover G K := by
  classical
  let covers := Finset.univ.filter fun K : Finset (Fin n) => G.IsVertexCover (K : Set _)
  have huniv : Finset.univ ∈ covers := by simp [covers]
  obtain ⟨K, mem, least⟩ := covers.exists_min_image Finset.card ⟨_, huniv⟩
  exact ⟨K, (Finset.mem_filter.mp mem).2, fun T c => least T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c⟩)⟩

/-- A general sparsity test. It places no constraint on shared ORs or on the matching chosen. -/
theorem edge_capacity (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (d t : ℕ)
    (degree : ∀ v, G.degree v ≤ d)
    (short : (t - 1) * d < (G.edgeFinset \ Ustar G C).card)
    (budget : (Ustar G C).card ≤ (junk G C).card + 2*(centreless G C).card +
      (orN G C \ lam G C).card) :
    G.edgeFinset.card + t ≤ C.size + 1 := by
  classical
  obtain ⟨cnt, small⟩ := PEqualNP.Outside.L_meta_1491 n G C four edges least top
  obtain ⟨K, kc⟩ := min_cover_exists (G.deleteEdges (Ustar G C : Set _))
  have cap := remaining_edges G (Ustar G C) K d degree kc.1
  have lower : t ≤ K.card := by
    by_contra! h
    have hi : K.card ≤ t - 1 := by omega
    exact (Nat.not_le_of_lt short) (cap.trans (Nat.mul_le_mul_right d hi))
  have := small K kc
  omega

/-- For at most three residual edges, the surviving edge count gives a size
bound for every least top-form circuit, regardless of dirty gates or shared wires. -/
theorem three_small (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (d t : ℕ)
    (degree : ∀ v, G.degree v ≤ d) (three : (Ustar G C).card ≤ 3)
    (short : (t - 1) * d < (G.edgeFinset \ Ustar G C).card) :
    G.edgeFinset.card + t ≤ C.size + 1 := by
  classical
  by_cases u : (Ustar G C).Nonempty
  · by_cases singleton : (junk G C).card = 1
    · obtain ⟨K, cover, paid⟩ := PEqualNP.Outside.L_meta_8103 n G C four edges least top u singleton
      have deleted : (G.deleteEdges (Ustar G C : Set _)).IsVertexCover (K : Set _) := by
        intro a b h; exact cover _ _ (SimpleGraph.deleteEdges_adj.mp h).1
      have cap := remaining_edges G (Ustar G C) K d degree deleted
      have lower : t ≤ K.card := by
        by_contra! h
        exact (Nat.not_le_of_lt short) (cap.trans (Nat.mul_le_mul_right d (by omega)))
      have count := (PEqualNP.Outside.L_meta_1491 n G C four edges least top).1
      omega
    · apply edge_capacity G C four edges least top d t degree short
      have pos : (junk G C).Nonempty := by
        obtain ⟨e, he⟩ := u
        induction e using Sym2.ind with
        | h a b =>
          obtain ⟨_, _, _, j, member, _⟩ :=
            PEqualNP.Outside.L_meta_8005.residualTrace least top he
          exact ⟨j, member⟩
      have hp := Finset.card_pos.mpr pos
      rcases PEqualNP.Outside.L_meta_8005.residualConnection least top u with h | h
      all_goals have := Finset.card_pos.mpr h; omega
  · apply edge_capacity G C four edges least top d t degree short
    simp [Finset.not_nonempty_iff_eq_empty.mp u]

/-- The order-three incidence graph, with the same labels as R_meta_2600_17. -/
abbrev plane := edgeGraph 26 ((List.finRange 13).flatMap fun p =>
  ((List.finRange 13).filter fun l => decide (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)).map
    fun l => (p.val, 13 + l.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem plane_degree : ∀ v, plane.degree v ≤ 4 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem plane_edges : plane.edgeFinset.card = 52 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem plane_four : NoFourCycle plane := by decide

/-- Least top-form circuits on the whole plane with at most three residual edges need 64 gates. -/
theorem plane_three (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
    (three : (Ustar plane C).card ≤ 3) : 64 ≤ C.size := by
  classical
  have edges : plane.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [plane_edges]; decide)
  have residual := Finset.card_sdiff_add_card_eq_card (show Ustar plane C ⊆ plane.edgeFinset from Finset.sdiff_subset)
  rw [plane_edges] at residual
  have t := three_small plane C plane_four edges least top 4 13 plane_degree three (by omega)
  rw [plane_edges] at t
  omega

#print axioms ResidualDegree.plane_three

end ResidualDegree
