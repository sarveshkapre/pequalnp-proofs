import FiveFacts

namespace NormalizeTips
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Relabeling the path preserves the chosen matching, star center, port,
leaf, and matched tip at every index. -/
private def swapTips {a b c d e : Fin n} (g : PrivateMatching.Guards G C a b c d e) :
    PrivateMatching.Guards G C c b a d e where
  port := g.port
  center := g.center
  leaf := g.leaf
  raw := g.raw
  member := g.member
  distinct := g.distinct
  distinctCenters := g.distinctCenters
  other := g.other
  serve := g.serve
  pathTip := g.pathTip
  pathTip_eq := g.pathTip_eq.symm
  avoid := g.avoid
  centerAvoid := g.centerAvoid

private def swapEdge {a b c d e : Fin n} (g : PrivateMatching.Guards G C a b c d e) :
    PrivateMatching.Guards G C a b c e d where
  port := g.port
  center := g.center
  leaf := g.leaf
  raw := g.raw
  member := g.member
  distinct := g.distinct
  distinctCenters := g.distinctCenters
  other := g.other
  serve := g.serve
  pathTip := g.pathTip
  pathTip_eq := g.pathTip_eq
  avoid t := by obtain ⟨x,y,z,w⟩ := g.avoid t; exact ⟨x,y,w,z⟩
  centerAvoid t := by obtain ⟨x,y,z,w⟩ := g.centerAvoid t; exact ⟨x,y,w,z⟩

private def pathMap : Fin 5 → Fin 5 := ![2,1,0,3,4]
private def edgeMap : Fin 5 → Fin 5 := ![0,1,2,4,3]

private theorem align (v : Fin 5 → Fin n) (inj : Function.Injective v)
    (g : PrivateMatching.Guards G C (v 0) (v 1) (v 2) (v 3) (v 4)) (matched : g.pathTip = v 0)
    (pattern : Ustar G C = PrivateMatching.shape (v 0) (v 1) (v 2) (v 3) (v 4))
    (color : G.Coloring (Fin 2)) : ∃ u : Fin 5 → Fin n, Nonempty (FiveFacts.Situation G C u) := by
  by_cases same : color (v 3) = color (v 0)
  · exact ⟨v,⟨⟨inj,g,matched,pattern,color,same⟩⟩⟩
  have sep : color (v 3) ≠ color (v 4) := by
    apply color.valid
    exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (show s(v 3,v 4) ∈ Ustar G C by
      rw [pattern]; simp [PrivateMatching.shape])).1
  have aligned : color (v 4) = color (v 0) := by omega
  have pattern' : Ustar G C = PrivateMatching.shape (v 0) (v 1) (v 2) (v 4) (v 3) := by
    rw [pattern]
    unfold PrivateMatching.shape
    rw [show s(v 4,v 3) = s(v 3,v 4) from Sym2.eq_swap]
  exact ⟨v ∘ edgeMap,⟨⟨inj.comp (show Function.Injective edgeMap by decide),
    swapEdge g,matched,pattern',color,aligned⟩⟩⟩

theorem normalize (bip : G.IsBipartite) (four : NoFourCycle G) (nonempty : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (injF : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (failure : ¬ GeneralThree.wireBound G C S)
    (v : Fin 5 → Fin n) (inj : Function.Injective v)
    (pattern : Ustar G C = PrivateMatching.shape (v 0) (v 1) (v 2) (v 3) (v 4)) :
    ∃ u : Fin 5 → Fin n, Nonempty (FiveFacts.Situation G C u) := by
  obtain ⟨color⟩ := bip
  obtain ⟨g⟩ := PrivateMatching.private_guards four nonempty least top three S f injF partners failure
    (v 0) (v 1) (v 2) (v 3) (v 4) pattern
  rcases g.pathTip_eq with l|r
  · exact align v inj g l pattern color
  · have pattern' : Ustar G C = PrivateMatching.shape (v 2) (v 1) (v 0) (v 3) (v 4) := by
      rw [pattern]
      unfold PrivateMatching.shape
      rw [show s(v 2,v 1) = s(v 1,v 2) from Sym2.eq_swap,
        show s(v 1,v 0) = s(v 0,v 1) from Sym2.eq_swap, Finset.insert_comm]
    exact align (v ∘ pathMap) (inj.comp (show Function.Injective pathMap by decide))
      (swapTips g) r pattern' color

#print axioms normalize
end NormalizeTips
