import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Outside.L_meta_5869

namespace ResidualRouting
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {U : Finset (Sym2 (Fin n))}

private abbrev R (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) := G.deleteEdges ↑U

private abbrev CoversAway (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U : Finset (Sym2 (Fin n))) (p : Fin n) :=
  ∀ t : Fin n → Bool, t p = true → graphFun G ∅ t = false →
    ∃ K : Finset (Fin n),
      (K.card ≤ 1 ∨ ∃ z, ∀ w ∈ K, (R G U).Adj w z) ∧
      (∀ a b, s(a,b) ∈ U → a ∈ K ∨ b ∈ K) ∧ ∀ w ∈ K, t w = false

private lemma common_neighbor_unique (h : NoFourCycle G) {u v a b : Fin n} (huv : u ≠ v)
    (hua : G.Adj u a) (hva : G.Adj v a) (hub : G.Adj u b) (hvb : G.Adj v b) : a = b :=
  Finset.card_le_one.mp (h u v huv) a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hua, hva⟩)
    b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hub, hvb⟩)

private lemma pair_negative {a b : Fin n} (hab : ¬G.Adj a b) :
    graphFun G ∅ (fun w => decide (w = a ∨ w = b)) = false := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_false_iff_not, decide_eq_true_eq]
  rintro ⟨u,v,huv,hu,hv⟩
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact G.loopless.irrefl _ huv
  · exact hab huv
  · exact hab huv.symm
  · exact G.loopless.irrefl _ huv

omit [DecidableRel G.Adj] in
private lemma common_color (c : G.Coloring (Fin 2)) {u v w : Fin n}
    (a : G.Adj u w) (b : G.Adj v w) : c u = c v := by
  have h1 := c.valid a
  have h2 := c.valid b
  omega

-- Orient both residual edges toward the neighbors of the vertex supplied by 5869.
private lemma oriented_equal (h4 : NoFourCycle G) (c : G.Coloring (Fin 2))
    {v p x q y : Fin n} (hvp : (R G U).Adj v p) (hvq : (R G U).Adj v q)
    (px : s(p,x) ∈ U) (qy : s(q,y) ∈ U) (ax : G.Adj p x) (ay : G.Adj q y)
    (routes : CoversAway G U p) : s(p,x) = s(q,y) := by
  classical
  have vp := (SimpleGraph.deleteEdges_adj.mp hvp).1
  have vq := (SimpleGraph.deleteEdges_adj.mp hvq).1
  have vy : v ≠ y := by
    rintro rfl
    exact (SimpleGraph.deleteEdges_adj.mp hvq.symm).2 qy
  by_cases same : p = q
  · subst q
    let bits := fun w : Fin n => decide (w = p ∨ w = p)
    obtain ⟨K,hK,cover,avoid⟩ := routes bits (by simp [bits]) (pair_negative (G.loopless.irrefl p))
    have np : p ∉ K := by intro hp; simpa [bits] using avoid p hp
    have hX := (cover p x px).resolve_left np
    have hY := (cover p y qy).resolve_left np
    by_cases hxy : x = y
    · rw [hxy]
    rcases hK with hK | ⟨z,hz⟩
    · exact False.elim (hxy (Finset.card_le_one.mp hK x hX y hY))
    have zx := hz x hX
    have zy := hz y hY
    have pz : p ≠ z := by
      rintro rfl
      exact (SimpleGraph.deleteEdges_adj.mp zx.symm).2 px
    exact False.elim (hxy (common_neighbor_unique h4 pz ax
      (SimpleGraph.deleteEdges_adj.mp zx.symm).1 ay (SimpleGraph.deleteEdges_adj.mp zy.symm).1))
  · have nonedge : ¬G.Adj p y := by
      intro hpy
      exact same (common_neighbor_unique h4 vy vp hpy.symm vq ay.symm)
    let bits := fun w : Fin n => decide (w = p ∨ w = y)
    obtain ⟨K,hK,cover,avoid⟩ := routes bits (by simp [bits]) (pair_negative nonedge)
    have np : p ∉ K := by intro hp; simpa [bits] using avoid p hp
    have ny : y ∉ K := by intro hy; simpa [bits] using avoid y hy
    have hX := (cover p x px).resolve_left np
    have hQ := (cover q y qy).resolve_right ny
    have pqcol := common_color c vp.symm vq.symm
    have neqcol : c x ≠ c q := by rw [← pqcol]; exact c.valid ax.symm
    rcases hK with hK | ⟨z,hz⟩
    · exact False.elim (neqcol (congrArg c (Finset.card_le_one.mp hK x hX q hQ)))
    · exact False.elim (neqcol (common_color c (SimpleGraph.deleteEdges_adj.mp (hz x hX)).1
                                        (SimpleGraph.deleteEdges_adj.mp (hz q hQ)).1))

theorem card_le_one_from_routes (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (sub : U ⊆ G.edgeFinset)
    (data : U.Nonempty → ∃ v : Fin n, ∀ k l : Fin n, s(k,l) ∈ U →
      ∃ w, (w = k ∨ w = l) ∧ (G.deleteEdges ↑U).Adj v w ∧
        ∀ t : Fin n → Bool, t w = true → graphFun G ∅ t = false →
          ∃ K : Finset (Fin n),
            (K.card ≤ 1 ∨ ∃ z, ∀ y ∈ K, (G.deleteEdges ↑U).Adj y z) ∧
            (∀ p q, s(p,q) ∈ U → p ∈ K ∨ q ∈ K) ∧ ∀ y ∈ K, t y = false) :
    U.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨v,routes⟩ := data ⟨e, he⟩
  induction e using Sym2.inductionOn with | _ a b =>
  induction f using Sym2.inductionOn with | _ d g =>
  obtain ⟨c⟩ := hb
  have orient (k l : Fin n) (kl : s(k,l) ∈ U) :
      ∃ p x, s(k,l) = s(p,x) ∧ (R G U).Adj v p ∧ G.Adj p x ∧ CoversAway G U p := by
    have adj : G.Adj k l := SimpleGraph.mem_edgeFinset.mp (sub kl)
    obtain ⟨w,hw,hvw,hroute⟩ := routes k l kl
    rcases hw with rfl | rfl
    · exact ⟨w,l,rfl,hvw,adj,hroute⟩
    · exact ⟨w,k,Sym2.eq_swap,hvw,adj.symm,hroute⟩
  obtain ⟨p,x,hex,hvp,hpx,hr⟩ := orient a b he
  obtain ⟨q,y,hfy,hvq,hqy,_⟩ := orient d g hf
  rw [hex] at he ⊢
  rw [hfy] at hf ⊢
  exact oriented_equal h4 c hvp hvq he hf hpx hqy hr

theorem small_budget_residual (C : Circuit) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (ne : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (top : TopForm G C)
    (dirty : 2 ≤ (junk G C).card)
    (small : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 3) :
    (Ustar G C).card ≤ 1 := by
  apply card_le_one_from_routes hb h4 Finset.sdiff_subset
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with | _ a b =>
  exact (PEqualNP.Outside.L_meta_5869 n G C h4 ne least top dirty small ⟨a,b,he⟩).2

theorem two_edges_require_four (C : Circuit) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (ne : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (top : TopForm G C)
    (dirty : 2 ≤ (junk G C).card) (two : 2 ≤ (Ustar G C).card) :
    4 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  by_contra! small
  have bound := small_budget_residual C hb h4 ne least top dirty (by omega)
  omega

#print axioms ResidualRouting.two_edges_require_four
end ResidualRouting
