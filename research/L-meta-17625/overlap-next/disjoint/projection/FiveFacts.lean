import FiveRows

namespace FiveFacts
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open DisjointProjected FiveRows

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {v : Fin 5 → Fin n}

/-- The matched path tip is a and d has the same color as a. -/
structure Situation (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (v : Fin 5 → Fin n) where
  inj : Function.Injective v
  guards : PrivateMatching.Guards G C (v 0) (v 1) (v 2) (v 3) (v 4)
  matched : guards.pathTip = v 0
  shape : Ustar G C = PrivateMatching.shape (v 0) (v 1) (v 2) (v 3) (v 4)
  color : G.Coloring (Fin 2)
  align : color (v 3) = color (v 0)

variable (D : Situation G C v)
noncomputable def inside : Bool := by classical exact decide (∃ t, D.guards.center t = v 2)
def cross (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin 5 → Fin n) : Bool :=
  decide (G.Adj (v 2) (v 4))
def negative (cross : Bool) : T := if cross then 880 else 1016
def positive (cross : Bool) : T := if cross then 15 else 7

include D in
theorem adjacent : G.Adj (v 0) (v 1) ∧ G.Adj (v 1) (v 2) ∧ G.Adj (v 3) (v 4) := by
  have edge {x y} (h : s(x,y) ∈ Ustar G C) := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp h).1
  exact ⟨edge (by rw [D.shape]; simp [PrivateMatching.shape]),edge (by rw [D.shape]; simp [PrivateMatching.shape]),
    edge (by rw [D.shape]; simp [PrivateMatching.shape])⟩

include D in
theorem top_allowed (four : NoFourCycle G) (ao : IsAO2 n C) (t : tops G C) (p : Fin 2) :
    ProjectionGeometry.allowed (v 0) (v 1) (v 2) (v 3) (v 4) (PEqualNP.TopForm.side (n := n) C t p) :=
  ProjectionGeometry.top_masks D.guards ao four D.color (adjacent D).1 (adjacent D).2.1
    (adjacent D).2.2 D.align (D.inj.ne (by decide)) t p

theorem off_vertex (t : tops G C) (out : ¬ (inside D = true ∧ D.guards.center t = v 2)) :
    ∀ i, v i ≠ D.guards.center t := by
  have hc : v 2 ≠ D.guards.center t := by
    intro eq
    exact out ⟨by classical simpa [inside] using (show ∃ u, D.guards.center u = v 2 from ⟨t,eq.symm⟩),eq.symm⟩
  have h := D.guards.centerAvoid t
  rw [D.matched] at h
  intro i; fin_cases i <;> first | exact hc | exact h.1.symm | exact h.2.1.symm | exact h.2.2.1.symm | exact h.2.2.2.symm

private theorem inside_five (u : Fin n) (r : Fin 10) (on : input v r u = true) :
    u ∈ ({v 0,v 1,v 2,v 3,v 4} : Finset _) := by
  obtain ⟨j,rfl,_⟩ := of_decide_eq_true on
  fin_cases j <;> simp

private def accepts (c : Bool) (r : Fin 10) : Bool :=
  let b (j : Fin 5) := (row r).getLsbD j
  (b 0 && b 1) || (b 1 && b 2) || (b 3 && b 4) || (c && b 2 && b 4)

include D in
theorem row_exact (r : Fin 10) : graphFun G ∅ (input v r) = accepts (cross G v) r := by
  apply Bool.eq_iff_iff.mpr
  have atv := at_vertex D.inj r
  change graphFun G ∅ (input v r) = true ↔ _
  simp only [accepts,Bool.or_eq_true,Bool.and_eq_true,cross,decide_eq_true_eq]
  constructor
  · intro yes
    simp [graphFun] at yes
    obtain ⟨u,w,edge,hu,hw⟩ := yes
    by_cases residual : s(u,w) ∈ Ustar G C
    · rw [D.shape] at residual
      simp only [PrivateMatching.shape,Finset.mem_insert,Finset.mem_singleton] at residual
      rcases residual with h|h|h <;> rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [atv] at hu hw <;> grind
    · have ce := (ProjectionGeometry.induced D.guards D.matched D.shape D.color (adjacent D).1 (adjacent D).2.1
        D.align (inside_five u r hu) (inside_five w r hw) edge residual).1
      rcases Sym2.eq_iff.mp ce with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [atv] at hu hw
      · exact Or.inr ⟨⟨edge,hu⟩,hw⟩
      · exact Or.inr ⟨⟨edge.symm,hw⟩,hu⟩
  · have got (i j : Fin 5) (adj : G.Adj (v i) (v j)) (l : (row r).getLsbD i = true)
        (h : (row r).getLsbD j = true) : graphFun G ∅ (input v r) = true := by
      simp [graphFun]
      exact ⟨v i,v j,adj,(atv i).trans l,(atv j).trans h⟩
    rintro (((h|h)|h)|⟨⟨adj,l⟩,r'⟩)
    · exact got 0 1 (adjacent D).1 h.1 h.2
    · exact got 1 2 (adjacent D).2.1 h.1 h.2
    · exact got 3 4 (adjacent D).2.2 h.1 h.2
    · exact got 2 4 adj l r'

private theorem rows : ∀ (x : Bool) (r : Fin 10),
    ((negative x).getLsbD r = true → accepts x r = false) ∧
    ((positive x).getLsbD r = true → accepts x r = true) ∧
    ((848 : T).getLsbD r = true → accepts x r = false ∧ (row r).getLsbD 2 = false) := by decide

include D in
theorem row_negative (r : Fin 10) (m : (negative (cross G v)).getLsbD r = true) :
    graphFun G ∅ (input v r) = false := (row_exact D r).trans ((rows _ r).1 m)

include D in
theorem row_positive (r : Fin 10) (m : (positive (cross G v)).getLsbD r = true) :
    graphFun G ∅ (input v r) = true := (row_exact D r).trans ((rows _ r).2.1 m)

theorem cross_inside (h : cross G v = true) : inside D = true := by
  classical
  have old : s(v 2,v 4) ∉ Ustar G C := by
    rw [D.shape]; simp only [PrivateMatching.shape,Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff,D.inj.eq_iff]; decide
  have mem (j : Fin 5) : v j ∈ ({v 0,v 1,v 2,v 3,v 4} : Finset _) := by fin_cases j <;> simp
  apply decide_eq_true
  exact (ProjectionGeometry.induced D.guards D.matched D.shape D.color (adjacent D).1 (adjacent D).2.1
    D.align (mem 2) (mem 4) (of_decide_eq_true h) old).2

theorem and_zero {x m : T} (off : ∀ r : Fin 10, m.getLsbD r = true → x.getLsbD r = false) :
    x &&& m = 0 := by
  apply PathBits.bit_ext; intro r
  rw [BitVec.getLsbD_and]
  cases h : m.getLsbD r
  · simp
  · rw [off r h]; simp

theorem inside_guard (ao : IsAO2 n C) (hi : inside D = true) (t : tops G C) :
    signal v C (opnd C t (D.guards.port t)) &&& 848 = 0 := by
  classical
  obtain ⟨u,eq⟩ := of_decide_eq_true hi
  apply and_zero; intro r m
  rw [signal_bit]
  have flags := (rows (cross G v) r).2.2 m
  apply D.guards.inside_four ao D.shape D.matched ⟨u,eq.symm⟩ _ _ ((row_exact D r).trans flags.1) t
  intro x hx
  obtain ⟨j,rfl,on⟩ := of_decide_eq_true hx
  fin_cases j <;> simp_all

theorem outside_guard (ao : IsAO2 n C) (four : NoFourCycle G) (ho : inside D = false) (t : tops G C) :
    (signal v C (opnd C t (D.guards.port t)) &&& negative (cross G v) = 0) ∨
    raw v (PEqualNP.TopForm.side (n := n) C t (1-D.guards.port t)) = 4 ∨
    raw v (PEqualNP.TopForm.side (n := n) C t (1-D.guards.port t)) = 12 := by
  classical
  let L := PEqualNP.TopForm.side (n := n) C t (1-D.guards.port t)
  by_cases hc : D.guards.leaf t = v 2
  · have mem : v 2 ∈ L := hc ▸ D.guards.member t
    have a := top_allowed D four ao t (1-D.guards.port t)
    have tag := allowed_tag v D.inj L a
    obtain ⟨m,hm⟩ := tag
    have bit : (raw v L).getLsbD 2 = true := by
      change (raw v L).getLsbD (2 : Fin 5).val = true
      simp only [raw,PathBits.get_pack]; exact decide_eq_true mem
    have check : ∀ i : BitVec 4, (rawMask i).getLsbD 2 = true → rawMask i = 4 ∨ rawMask i = 12 := by decide
    exact Or.inr (hm ▸ check m (hm.symm ▸ bit))
  · left
    apply and_zero; intro r m; rw [signal_bit]
    apply D.guards.rejects_guarded ao D.shape t _ (row_negative D r m)
    · intro j; apply Bool.eq_false_iff.mpr; intro on
      obtain ⟨i,eq,_⟩ := of_decide_eq_true on
      exact off_vertex D j (by simp [ho]) i eq
    · exact Or.inl ⟨fun h => (D.guards.avoid t).2.1 (h.trans D.matched.symm),hc⟩

theorem center_leaf (ao : IsAO2 n C) (t : tops G C) (z : D.guards.center t = v 2) :
    raw v (PEqualNP.TopForm.side (n := n) C t (1-D.guards.port t)) = 0 ∨
    (cross G v = true ∧ raw v (PEqualNP.TopForm.side (n := n) C t (1-D.guards.port t)) = 16) := by
  let L := PEqualNP.TopForm.side (n := n) C t (1-D.guards.port t)
  have center : v 2 ∈ PEqualNP.TopForm.side (n := n) C t (D.guards.port t) := by rw [D.guards.raw,z]; simp
  have one (i : Fin 5) (m : v i ∈ L) : v i = v 4 ∧ cross G v = true := by
    have edge := SimpleGraph.deleteEdges_adj.mp (cleanAdj ao t.2 (D.guards.port t) center m)
    have mem (j : Fin 5) : v j ∈ ({v 0,v 1,v 2,v 3,v 4} : Finset _) := by fin_cases j <;> simp
    have eq := (ProjectionGeometry.induced D.guards D.matched D.shape D.color (adjacent D).1 (adjacent D).2.1
      D.align (mem 2) (mem i) edge.1 edge.2).1
    have h := Sym2.eq_iff.mp eq
    have h24 := D.inj.ne (by decide : (2 : Fin 5) ≠ 4)
    have ve : v i = v 4 := by grind
    exact ⟨ve,decide_eq_true (ve ▸ edge.1)⟩
  by_cases on : v 4 ∈ L
  · right; refine ⟨(one 4 on).2,?_⟩
    apply PathBits.bit_ext; intro i
    change (raw v L).getLsbD i = _
    simp only [raw,PathBits.get_pack]
    have eq : v i ∈ L ↔ i = 4 := ⟨fun x => D.inj (one _ x).1,fun h => h ▸ on⟩
    simp only [eq]; fin_cases i <;> decide
  · left; apply PathBits.bit_ext; intro i
    change (raw v L).getLsbD i = _
    simp only [raw,PathBits.get_pack]
    have off : v i ∉ L := fun h => on ((one i h).1 ▸ h)
    simp [off]

end FiveFacts
