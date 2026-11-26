import PEqualNP.Outside.L_meta_7465

namespace CentreSeparation
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux
open PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev Ordinary (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  ↥(tops G C \ centreless G C)

-- Regroup the possible output terms. Every residual pair must turn on a centreless
-- top or an exceptional OR feeding an ordinary centre. A protected negative turns
-- off every member of both groups.
theorem separate {I K : Type*} (least : IsLeastAO G C)
    (port : Ordinary G C → Fin 2) (center : Ordinary G C → Fin n)
    (single : ∀ a, side (n := n) C a.val (port a) = {center a})
    (pair : I → Fin n × Fin n) (pos : ∀ i, G.Adj (pair i).1 (pair i).2)
    (outside : ∀ i a, center a ≠ (pair i).1 ∧ center a ≠ (pair i).2)
    (neg : K → Fin n → Bool) (noEdge : ∀ k, graphFun G ∅ (neg k) = false)
    (leaves : ∀ a k, ∃ w ∈ side C a.val (1-port a), neg k w = true) :
    ∃ S : Finset ℕ,
      (∀ h ∈ S, h ∈ orN G C \ lam G C ∧ (orIn n C (n+h)).Nonempty ∧
        ∃ a : Ordinary G C, OrReaches n C (opnd C a.val (port a)) h) ∧
      (∀ i, ∃ h ∈ centreless G C ∪ S,
        gateVal n C h (pairInput (pair i).1 (pair i).2) = true) ∧
      ∀ k h, h ∈ centreless G C ∪ S → gateVal n C h (neg k) = false := by
  classical
  let atCentre (a : Ordinary G C) := (orN G C \ lam G C).filter fun h =>
    (orIn n C (n+h)).Nonempty ∧ OrReaches n C (opnd C a.val (port a)) h
  let S := Finset.univ.biUnion atCentre
  have source (h : ℕ) (mem : h ∈ S) :
      h ∈ orN G C \ lam G C ∧ (orIn n C (n+h)).Nonempty ∧
        ∃ a : Ordinary G C, OrReaches n C (opnd C a.val (port a)) h := by
    obtain ⟨a,_,member⟩ := Finset.mem_biUnion.mp mem
    obtain ⟨ex,support,path⟩ := Finset.mem_filter.mp member
    exact ⟨ex,support,a,path⟩
  refine ⟨S,source,?_,?_⟩
  · intro i
    obtain ⟨a,ha,fire⟩ := acceptedTop least (pos i)
    by_cases hc : a ∈ centreless G C
    · exact ⟨a,Finset.mem_union_left _ hc,fire⟩
    let t : Ordinary G C := ⟨a, Finset.mem_sdiff.mpr ⟨ha,hc⟩⟩
    have ht := topData ha
    have on := (andValOperands least.1 ht.1 ht.2.1 _).mp fire (port t)
    have bound := opndBound least.1 ht.1 (port t)
    have has : (orIn n C (opnd C a (port t))).Nonempty := by
      change (side (n := n) C t.val (port t)).Nonempty
      rw [single]
      exact Finset.singleton_nonempty _
    rcases (nonemptyPortValue (G := G) least.1 _ _ (by omega) has).mp on with
      ⟨v,hv,bit⟩ | ⟨h,hm,bit⟩
    · change v ∈ side C t.val (port t) at hv
      have same : v = center t := by simpa [single] using hv
      exact False.elim (((pairInput_true _ _ _).mp bit).elim
        (fun eq => (outside i t).1 (same.symm.trans eq)) (fun eq => (outside i t).2 (same.symm.trans eq)))
    · change h ∈ (orN G C \ lam G C).filter _ at hm
      exact ⟨h,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,hm⟩),bit⟩
  · intro k h hm
    apply Bool.eq_false_iff.mpr
    intro on
    have bad : graphFun G ∅ (neg k) = true := by
      rcases Finset.mem_union.mp hm with cent | promot
      · have ht := (Finset.mem_filter.mp cent).1
        exact (topData ht).2.2 _ on
      · obtain ⟨_,_,a,path⟩ := source h promot
        obtain ⟨w,hw,hx⟩ := leaves a k
        exact firingTop least.1 (Finset.mem_sdiff.mp a.2).1 (orReaches_reach h _ path).1 hw _ on hx
    exact Bool.false_ne_true ((noEdge k).symm.trans bad)

#print axioms separate
end CentreSeparation

namespace CentreSeparation
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The ordinary tops supply an indexed cover by stars even when other tops have
    an empty side. Every edge outside U belongs to an actual opposite port. -/
theorem ordinaryStars (four : NoFourCycle G) (ao : IsAO2 n C) :
    ∃ (b : Ordinary G C → Fin 2) (z : Ordinary G C → Fin n),
      (∀ a, side (n := n) C a.val (b a) = {z a}) ∧
      ∀ u v, (G.deleteEdges ↑(Ustar G C)).Adj u v → ∃ a : Ordinary G C,
        (u = z a ∧ v ∈ side C a.val (1-b a)) ∨ (v = z a ∧ u ∈ side C a.val (1-b a)) := by
  classical
  have chooseSide (a : Ordinary G C) : ∃ b : Fin 2, ∃ z : Fin n, side C a.val b = {z} := by
    obtain ⟨ha,hc⟩ := Finset.mem_sdiff.mp a.2
    have both : side (n := n) C a.val 0 ≠ ∅ ∧ side (n := n) C a.val 1 ≠ ∅ := by
      constructor <;> intro h <;> apply hc <;> apply Finset.mem_filter.mpr
      · exact ⟨ha,Or.inl h⟩
      · exact ⟨ha,Or.inr h⟩
    have thin : (side (n := n) C a.val 0).card ≤ 1 ∨ (side (n := n) C a.val 1).card ≤ 1 := by
      by_contra! large
      obtain ⟨p,hp,q,hq,pq⟩ := Finset.one_lt_card.mp large.1
      obtain ⟨s,hs,t,ht,st⟩ := Finset.one_lt_card.mp large.2
      have mem {w : Fin n} (hw : w ∈ side C a.val 1) :
          w ∈ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj q w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,topAdj ao ha hp hw,topAdj ao ha hq hw⟩
      exact st (Finset.card_le_one.mp (four p q pq) s (mem hs) t (mem ht))
    rcases thin with h | h
    · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr both.1)
      exact ⟨0,Finset.card_eq_one.mp (by omega)⟩
    · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr both.2)
      exact ⟨1,Finset.card_eq_one.mp (by omega)⟩
  choose b z singleton using chooseSide
  refine ⟨b,z,singleton,?_⟩
  intro u v adj
  obtain ⟨edge,kept⟩ := SimpleGraph.deleteEdges_adj.mp adj
  have cross : s(u,v) ∈ starEdges G C := by
    by_contra h
    exact kept (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr edge,h⟩)
  obtain ⟨a,ha,hit⟩ := Finset.mem_biUnion.mp cross
  obtain ⟨⟨p,q⟩,hit,eq⟩ := Finset.mem_image.mp hit
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hit
  have hc : a ∉ centreless G C := by
    intro h
    rcases (Finset.mem_filter.mp h).2 with emp | emp
    · simp [emp] at hp
    · simp [emp] at hq
  let k : Ordinary G C := ⟨a, Finset.mem_sdiff.mpr ⟨ha,hc⟩⟩
  have scalar (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have route : (p = z k ∧ q ∈ side C a (1-b k)) ∨ (q = z k ∧ p ∈ side C a (1-b k)) := by
    have one := singleton k
    rcases scalar (b k) with h | h
    · rw [h] at one
      change side (n := n) C a 0 = {z k} at one
      exact Or.inl ⟨by simpa [one] using hp,by simpa [h] using hq⟩
    · rw [h] at one
      change side (n := n) C a 1 = {z k} at one
      exact Or.inr ⟨by simpa [one] using hq,by simpa [h] using hp⟩
  refine ⟨k,?_⟩
  rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact route
  · exact route.symm

#print axioms ordinaryStars
end CentreSeparation
