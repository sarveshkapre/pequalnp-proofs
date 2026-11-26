import MatchingTransfer

open PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace OneSpareCoverSlot

-- The graph has the six-vertex core and two six-cycles attached to its leaves.
abbrev G := edgeGraph 18 [(0,9),(1,10),(2,11),(0,10),(0,11),
  (3,12),(4,12),(4,13),(5,13),(5,14),(3,14),
  (6,15),(7,15),(7,16),(8,16),(8,17),(6,17),
  (1,12),(2,13),(6,9)]
abbrev U : Finset (Sym2 (Fin 18)) := {s(0,9),s(1,10),s(2,11)}
abbrev old := G.deleteEdges (U : Set _)
abbrev centres : Finset (Fin 18) := {0,12,13,14,6,7,8}
abbrev left : Finset (Fin 18) := Finset.Iio 9
abbrev oldLeft : Finset (Fin 18) := {0,3,4,5,6,7,8}
abbrev partner (v : Fin 18) : Fin 18 := v + 9
abbrev oldPartner (v : Fin 18) : Fin 18 := if v = 0 then 10 else partner v

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

theorem no4 : NoFourCycle G := by decide
theorem min_degree : ∀ v, 2 ≤ G.degree v := by decide
theorem crossing : ∀ u v, G.Adj u v → (u ∈ left) ≠ (v ∈ left) := by decide

theorem minimum_sizes :
    G.IsVertexCover (left : Set _) ∧ (∀ K : Finset (Fin 18), G.IsVertexCover (K : Set _) → 9 ≤ K.card) ∧
    old.IsVertexCover (centres : Set _) ∧ (∀ K : Finset (Fin 18), old.IsVertexCover (K : Set _) → 7 ≤ K.card) := by
  refine ⟨by unfold SimpleGraph.IsVertexCover; decide, ?_, by unfold SimpleGraph.IsVertexCover; decide, ?_⟩
  · intro K cover
    have le := ResidualDegree.matched_le_cover G left (fun v => partner v.val)
      (by decide) (by decide) K cover
    exact (show left.card = 9 by decide) ▸ le
  · intro K cover
    have le := ResidualDegree.matched_le_cover old oldLeft (fun v => oldPartner v.val)
      (by decide) (by decide) K cover
    exact (show oldLeft.card = 7 by decide) ▸ le

/-- The centre-free residual edges are precisely the last two matching edges.
The input selecting 1 and 2 has no independent extension hitting the leaves of centre 0. -/
theorem obstruction :
    (∀ e ∈ U, (∀ c ∈ centres, c ∉ e) ↔ (e = s(1,10) ∨ e = s(2,11))) ∧
    (∀ v, old.Adj 0 v ↔ v = 10 ∨ v = 11) ∧
    (∀ A : Finset (Fin 18), 1 ∈ A → 2 ∈ A → (∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v) →
        ∀ v ∈ A, ¬old.Adj 0 v) := by
  have leaves : ∀ v, old.Adj 0 v ↔ v = 10 ∨ v = 11 := by decide
  refine ⟨by decide, leaves, ?_⟩
  intro A h1 h2 independent v hv adj
  rcases (leaves v).1 adj with rfl | rfl
  · exact independent 1 h1 10 hv (by decide)
  · exact independent 2 h2 11 hv (by decide)

#print axioms OneSpareCoverSlot.obstruction

end OneSpareCoverSlot
