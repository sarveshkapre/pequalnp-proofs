import MatchingPorts

namespace CommonLiteral
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

set_option maxHeartbeats 1200000 in
/-- A common raw literal of all nonempty exceptional ORs forces every
residual edge to have an endpoint in its retained neighborhood. -/
theorem old_neighbor (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (w : Fin n) (common : ∀ h ∈ orN G C \ lam G C,
      (orIn n C (n+h)).Nonempty → w ∈ orIn n C (n+h))
    (u v : Fin n) (he : s(u,v) ∈ Ustar G C) :
    (G.deleteEdges ↑(Ustar G C)).Adj w u ∨ (G.deleteEdges ↑(Ustar G C)).Adj w v := by
  classical
  let old := G.deleteEdges ↑(Ustar G C)
  have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  obtain ⟨a,ma,fires⟩ := acceptedTop least adj
  obtain ⟨len,hand,_⟩ := topData ma
  have ne (p : Fin 2) : (side (n := n) C a p).Nonempty := by
    by_contra failed
    have zero := Finset.not_nonempty_iff_eq_empty.mp failed
    have cen : a ∈ centreless G C := by
      apply Finset.mem_filter.mpr
      refine ⟨ma,?_⟩
      fin_cases p
      · exact Or.inl zero
      · exact Or.inr zero
    rw [empty] at cen; exact Finset.notMem_empty _ cen
  have witnesses (p : Fin 2) : w ∈ side (n := n) C a p ∨ u ∈ side (n := n) C a p ∨ v ∈ side (n := n) C a p := by
    have bd := opndBound least.1 len p
    have on := (andValOperands least.1 len hand _).mp fires p
    rcases (nonemptyPortValue (G := G) least.1 _ _ (by omega) (ne p)).mp on with ⟨t,mt,bit⟩|⟨h,hm,_⟩
    · rcases (pairInput_true _ _ _).mp bit with rfl|rfl
      · exact Or.inr (Or.inl mt)
      · exact Or.inr (Or.inr mt)
    · change h ∈ (orN G C \ lam G C).filter _ at hm
      obtain ⟨m,raw,path⟩ := Finset.mem_filter.mp hm
      exact Or.inl (reach_mem_orIn w ((orReaches_reach h _ path).1.trans (mem_orIn_reach w (common _ m raw))))
  have cross {x y : Fin n} (hx : x ∈ side (n := n) C a 0) (hy : y ∈ side (n := n) C a 1) : old.Adj x y :=
    cleanAdj least.1 ma 0 hx hy
  have removed : ¬old.Adj u v := fun d => (SimpleGraph.deleteEdges_adj.mp d).2 he
  rcases witnesses 0 with wx|ux|vx <;> rcases witnesses 1 with wy|uy|vy
  · exact (old.irrefl (cross wx wy)).elim
  · exact Or.inl (cross wx uy)
  · exact Or.inr (cross wx vy)
  · exact Or.inl (cross ux wy).symm
  · exact (old.irrefl (cross ux uy)).elim
  · exact (removed (cross ux vy)).elim
  · exact Or.inr (cross vx wy).symm
  · exact (removed (cross vx uy).symm).elim
  · exact (old.irrefl (cross vx vy)).elim

/-- Every repeated vertex of the residual graph belongs to the retained
neighborhood of the common literal. Otherwise the two other endpoints and w
form a forbidden four-cycle. -/
theorem branch_vertex (four : NoFourCycle G) (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (w : Fin n) (common : ∀ h ∈ orN G C \ lam G C,
      (orIn n C (n+h)).Nonempty → w ∈ orIn n C (n+h))
    {v p q : Fin n} (distinct : p ≠ q) (vp : s(v,p) ∈ Ustar G C) (vq : s(v,q) ∈ Ustar G C) :
    (G.deleteEdges ↑(Ustar G C)).Adj w v := by
  by_contra no
  have wp := (old_neighbor least empty w common _ _ vp).resolve_left no
  have wq := (old_neighbor least empty w common _ _ vq).resolve_left no
  have vw : v ≠ w := by
    rintro rfl
    exact (SimpleGraph.deleteEdges_adj.mp wp).2 vp
  have ap := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp vp).1
  have aq := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp vq).1
  exact distinct (Finset.card_le_one.mp (four v w vw) p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ap, (SimpleGraph.deleteEdges_adj.mp wp).1⟩) q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, aq, (SimpleGraph.deleteEdges_adj.mp wq).1⟩))

/-- A path of three residual edges cannot occur in the common-literal case
for a bipartite graph with no four-cycle. The circuit can share arbitrary wires. -/
theorem no_three_edge_path (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (w : Fin n) (common : ∀ h ∈ orN G C \ lam G C,
      (orIn n C (n+h)).Nonempty → w ∈ orIn n C (n+h))
    {a b c d : Fin n} (ac : a ≠ c) (bd : b ≠ d) (ab : s(a,b) ∈ Ustar G C)
    (bc : s(b,c) ∈ Ustar G C) (cd : s(c,d) ∈ Ustar G C) : False := by
  have ba : s(b,a) ∈ Ustar G C := Sym2.eq_swap ▸ ab
  have cb : s(c,b) ∈ Ustar G C := Sym2.eq_swap ▸ bc
  have wb := (SimpleGraph.deleteEdges_adj.mp (branch_vertex four least empty w common ac ba bc)).1
  have wc := (SimpleGraph.deleteEdges_adj.mp (branch_vertex four least empty w common bd cb cd)).1
  have edge : G.Adj b c := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp bc).1
  obtain ⟨color⟩ := bip
  have left := color.valid wb
  have right := color.valid wc
  have diff := color.valid edge
  omega

#print axioms no_three_edge_path
end CommonLiteral
