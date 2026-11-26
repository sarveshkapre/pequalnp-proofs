import RawBudget

namespace PrivateLeaves
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem two_raw (ao : IsAO2 n C)
    (prod : ∀ h ∈ lam G C, ¬RawBudget.bypass n C h) {h : ℕ} (regular : h ∈ lam G C) :
    ∃ u ∈ orIn n C (n+h), ∃ v ∈ orIn n C (n+h), u ≠ v := by
  classical
  obtain ⟨nonTop,⟨u,hu⟩,_⟩ := Finset.mem_filter.mp regular
  obtain ⟨len,op,_⟩ := (show h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧ ¬BelowF G C h by
    simpa [orN,gatesWhere] using nonTop)
  have m : u ∈ orIn n C (n+h) := (PEqualNP.Outside.L_meta_1491.orIn_gate C h u).mpr
    ⟨len,op,_,opndMem ao len 0,opndBound ao len 0,hu⟩
  refine ⟨u,m,?_⟩
  by_contra! no
  have singleton : orIn n C (n+h) = {u} := by
    ext v
    constructor
    · exact fun hv => Finset.mem_singleton.mpr (no v hv).symm
    · rintro hv; exact (Finset.mem_singleton.mp hv) ▸ m
  rcases RawBudget.singleton_wire prod _ _ singleton with eq | ⟨k,excluded,eq⟩
  · have bound := u.isLt; omega
  · have same : h = k := by omega
    exact (Finset.mem_sdiff.mp excluded).2 (same ▸ regular)

private theorem neighbors (ao : IsAO2 n C) {a h : ℕ} (ta : a ∈ tops G C)
    (b p : Fin 2) (z : Fin n) (single : side (n := n) C a b = {z})
    (reaches : OrReaches n C (opnd C a p) h)
    {u v : Fin n} (mu : u ∈ orIn n C (n+h)) (mv : v ∈ orIn n C (n+h)) (ne : u ≠ v) :
    G.Adj z u ∧ G.Adj z v := by
  have incl (w : Fin n) (m : w ∈ orIn n C (n+h)) : w ∈ side (n := n) C a p :=
    reach_mem_orIn w ((orReaches_reach _ _ reaches).1.trans (mem_orIn_reach w m))
  have x := incl u mu
  have y := incl v mv
  rcases opposite b p with rfl | rfl
  · rw [single,Finset.mem_singleton] at x y; exact (ne (x.trans y.symm)).elim
  · have center : z ∈ side (n := n) C a b := by simp [single]
    exact ⟨(SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ta b center x)).1,
      (SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ta b center y)).1⟩

/-- In a tight circuit a productive ordinary OR cannot feed two different
star centers. Its support has two vertices, which would make a four-cycle. -/
theorem same_center (four : NoFourCycle G) (ao : IsAO2 n C)
    (prod : ∀ h ∈ lam G C, ¬RawBudget.bypass n C h) {h a c : ℕ} (hl : h ∈ lam G C)
    (ta : a ∈ tops G C) (tc : c ∈ tops G C) (b d i j : Fin 2) (z y : Fin n)
    (sz : side (n := n) C a b = {z}) (sy : side (n := n) C c d = {y})
    (ha : OrReaches n C (opnd C a i) h) (hc : OrReaches n C (opnd C c j) h) : z = y := by
  classical
  by_contra different
  obtain ⟨u,mu,v,mv,ne⟩ := two_raw ao prod hl
  have zu := neighbors ao ta b i z sz ha mu mv ne
  have yu := neighbors ao tc d j y sy hc mu mv ne
  exact ne (Finset.card_le_one.mp (four z y different) u (Finset.mem_filter.mpr ⟨Finset.mem_univ _,zu.1,yu.1⟩)
    v (Finset.mem_filter.mpr ⟨Finset.mem_univ _,zu.2,yu.2⟩))


/-- With distinct chosen centers, the ordinary edges of any two different
tops are disjoint. Thus those stars partition the ordinary edges. -/
theorem disjoint_stars (four : NoFourCycle G) (least : IsLeastAO G C)
    (prod : ∀ h ∈ lam G C, ¬RawBudget.bypass n C h)
    (sharp : (RawBudget.covered n C (tops G C)).card = (tops G C).card + (lam G C).card)
    (b : tops G C → Fin 2) (z : tops G C → Fin n) (inj : Function.Injective z)
    (single : ∀ a, side (n := n) C a.val (b a) = {z a}) {a c : tops G C} (ne : a ≠ c) :
    Disjoint (RawBudget.covered n C {a.val}) (RawBudget.covered n C {c.val}) := by
  classical
  let P : Finset ℕ := {a.val}
  let Q := (tops G C).erase a.val
  have parts : P ∪ Q = tops G C := by simp [P,Q,a.2]
  have sep : Disjoint P Q := by simp [P,Q]
  have rawSep : Disjoint (RawBudget.reachable G C P) (RawBudget.reachable G C Q) := by
    apply Finset.disjoint_left.mpr
    intro h hp hq
    obtain ⟨base,p,pm,i,pr⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,q,qm,j,qr⟩ := Finset.mem_filter.mp hq
    have pa : p = a.val := Finset.mem_singleton.mp pm
    subst p
    obtain ⟨diff,member⟩ := Finset.mem_erase.mp qm
    let t : tops G C := ⟨q,member⟩
    have eq := same_center four least.1 prod (Finset.mem_filter.mp base).1 a.2 t.2
      (b a) (b t) i j _ _ (single a) (single t) pr qr
    exact diff (congrArg Subtype.val (inj eq).symm)
  have count := RawBudget.overlap_count four least sharp P Q parts sep
  rw [Finset.disjoint_iff_inter_eq_empty.mp rawSep, Finset.card_empty] at count
  have esep : Disjoint (RawBudget.covered n C P) (RawBudget.covered n C Q) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero count))
  have cQ : c.val ∈ Q := Finset.mem_erase.mpr ⟨fun same => ne (Subtype.ext same.symm),c.2⟩
  apply Finset.disjoint_left.mpr
  intro uv ua uc
  apply Finset.disjoint_left.mp esep ua
  obtain ⟨r,m,edge⟩ := Finset.mem_biUnion.mp uc
  have rc : r = c.val := Finset.mem_singleton.mp m
  exact Finset.mem_biUnion.mpr ⟨r,rc ▸ cQ,edge⟩

#print axioms disjoint_stars

#print axioms same_center
end PrivateLeaves
