import PrivateMatching

namespace ProjectionGeometry
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {a b c d e : Fin n}

/-- These three sets have exactly nine distinct subsets, including the empty set. -/
def allowed (a b c d e : Fin n) (R : Finset (Fin n)) : Prop :=
  R ∩ {a,b,c,d,e} ⊆ {a,d} ∨ R ∩ {a,b,c,d,e} ⊆ {c,d} ∨ R ∩ {a,b,c,d,e} ⊆ {b,e}

omit [DecidableRel G.Adj] in
private theorem ordinary_side {R : Finset (Fin n)} (color : G.Coloring (Fin 2))
    (ab : G.Adj a b) (bc : G.Adj b c) (de : G.Adj d e) (align : color d = color a)
    (mono : ∀ x ∈ R, ∀ y ∈ R, color x = color y)
    (apart : ¬(a ∈ R ∧ c ∈ R)) : allowed a b c d e R := by
  classical
  have cab := color.valid ab
  have cbc := color.valid bc
  have cde := color.valid de
  have same : color a = color c := by omega
  have sepE : color a ≠ color e := by omega
  by_cases left : ∃ x ∈ R, color x = color a
  · obtain ⟨x,hx,col⟩ := left
    have nb : b ∉ R := fun hb => cab (col.symm.trans (mono _ hx _ hb))
    have ne : e ∉ R := fun he => sepE (col.symm.trans (mono _ hx _ he))
    unfold allowed
    by_cases hc : c ∈ R
    · right; left; intro v mv
      obtain ⟨hv,vs⟩ := Finset.mem_inter.mp mv
      simp only [Finset.mem_insert,Finset.mem_singleton] at vs ⊢
      grind
    · left; intro v mv
      obtain ⟨hv,vs⟩ := Finset.mem_inter.mp mv
      simp only [Finset.mem_insert,Finset.mem_singleton] at vs ⊢
      grind
  · right; right; intro v mv
    obtain ⟨hv,vs⟩ := Finset.mem_inter.mp mv
    simp only [Finset.mem_insert,Finset.mem_singleton] at vs ⊢
    rcases vs with rfl|rfl|rfl|rfl|rfl
    · exact (left ⟨_,hv,rfl⟩).elim
    · exact Or.inl rfl
    · exact (left ⟨_,hv,same.symm⟩).elim
    · exact (left ⟨_,hv,align⟩).elim
    · exact Or.inr rfl

theorem top_masks (g : PrivateMatching.Guards G C a b c d e)
    (ao : IsAO2 n C) (four : NoFourCycle G) (color : G.Coloring (Fin 2))
    (ab : G.Adj a b) (bc : G.Adj b c) (de : G.Adj d e) (align : color d = color a)
    (ac : a ≠ c) (t : tops G C) (p : Fin 2) : allowed a b c d e (side (n := n) C t p) := by
  rcases opposite (g.port t) p with rfl | rfl
  · apply ordinary_side color ab bc de align
    · simp only [g.raw,Finset.mem_singleton]; grind
    · simp only [g.raw,Finset.mem_singleton]; grind
  · have zmem : g.center t ∈ side (n := n) C t (g.port t) := by simp [g.raw]
    have adj (x) (m : x ∈ side (n := n) C t (1-g.port t)) : G.Adj (g.center t) x :=
      (SimpleGraph.deleteEdges_adj.mp (cleanAdj ao t.2 (g.port t) zmem m)).1
    apply ordinary_side color ab bc de align
    · intro x mx y my
      have := color.valid (adj x mx)
      have := color.valid (adj y my)
      omega
    · rintro ⟨ma,mc⟩
      have bound := Finset.card_le_one.mp (four _ _ (g.centerAvoid t).1)
      exact ac (bound a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,adj a ma,ab.symm⟩)
        c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,adj c mc,bc⟩))

theorem downward {X Y : Finset (Fin n)} (sub : X ⊆ Y)
    (h : allowed a b c d e Y) : allowed a b c d e X := by
  have small : X ∩ {a,b,c,d,e} ⊆ Y ∩ {a,b,c,d,e} := fun _ h =>
    Finset.mem_inter.mpr ⟨sub (Finset.mem_inter.mp h).1,(Finset.mem_inter.mp h).2⟩
  rcases h with p|p|p
  · exact Or.inl (small.trans p)
  · exact Or.inr (Or.inl (small.trans p))
  · exact Or.inr (Or.inr (small.trans p))

/-- Every uncharged OR is an ancestor through ORs of a physical top port. -/
theorem ordinary_masks (mask : ∀ t : tops G C, ∀ p : Fin 2, allowed a b c d e (side (n := n) C t p))
    {k : ℕ} (m : k ∈ lam G C) : allowed a b c d e (orIn n C (n+k)) := by
  obtain ⟨_,_,_,t,ht,p,_,reach⟩ := Finset.mem_filter.mp m
  apply downward _ (mask ⟨t,ht⟩ p)
  intro x hx
  exact reach_mem_orIn _ ((orReaches_reach _ _ reach).1.trans (mem_orIn_reach _ hx))

/-- Among the five vertices, all nonresidual edges are incident to the
unmatched tip. Its color allows only the opposite-color endpoint e of d-e
as a new neighbor: b-c is already residual. -/
theorem induced (g : PrivateMatching.Guards G C a b c d e) (matched : g.pathTip = a)
    (pattern : Ustar G C = PrivateMatching.shape a b c d e)
    (color : G.Coloring (Fin 2)) (ab : G.Adj a b) (bc : G.Adj b c)
    (align : color d = color a) {u v : Fin n}
    (hu : u ∈ ({a,b,c,d,e} : Finset (Fin n))) (hv : v ∈ ({a,b,c,d,e} : Finset (Fin n)))
    (edge : G.Adj u v) (retained : s(u,v) ∉ Ustar G C) :
    s(u,v) = s(c,e) ∧ ∃ t, g.center t = c := by
  classical
  have diff := color.valid edge
  have ac : color a = color c := by
    have := color.valid ab
    have := color.valid bc
    omega
  obtain ⟨t,ht⟩ := g.serve u v (SimpleGraph.deleteEdges_adj.mpr ⟨edge,retained⟩)
  have avoid := g.centerAvoid t
  rw [matched] at avoid
  have only {x : Fin n} (hx : x ∈ ({a,b,c,d,e} : Finset _)) (eq : x = g.center t) : x = c := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx; grind
  have right {y : Fin n} (hy : y ∈ ({a,b,c,d,e} : Finset _)) (ne : color c ≠ color y)
      (off : s(c,y) ∉ Ustar G C) : y = e := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    have cb : s(c,b) ∈ Ustar G C := by rw [pattern,Sym2.eq_swap]; simp [PrivateMatching.shape]
    grind
  rcases ht with ⟨z,_⟩|⟨z,_⟩
  · have eq := only hu z
    have h := right hv (eq ▸ diff) (eq ▸ retained)
    exact ⟨by rw [eq,h],⟨_,z.symm.trans eq⟩⟩
  · have eq := only hv z
    have off : s(c,u) ∉ Ustar G C := by rw [Sym2.eq_swap,←eq]; exact retained
    have h := right hu (eq ▸ Ne.symm diff) off
    exact ⟨by rw [eq,h,Sym2.eq_swap],⟨_,z.symm.trans eq⟩⟩

#print axioms top_masks
#print axioms ordinary_masks
#print axioms induced
end ProjectionGeometry
