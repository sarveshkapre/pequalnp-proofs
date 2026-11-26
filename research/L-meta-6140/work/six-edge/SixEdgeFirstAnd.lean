import SixEdgePlane

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open ResidualDegree PlaneFour

variable {C : Circuit}

theorem first_port (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    {g : ℕ} (h : g ∈ junk plane C)
    (first : ∀ k ∈ charged plane C, ¬ k < g) (i : Fin 2) :
    ((∀ t ∈ side (n := 26) C g i, t.val < 13) ∨
      ∃ l : Fin 13, side (n := 26) C g i = {ln l}) ∧
    ∀ x, val C (List.ofFn x) (opnd C g i) = true ↔
      ∃ t ∈ side (n := 26) C g i, x t = true := by
  classical
  rcases matches_ports S least top (Finset.mem_union_left _ h) i with direct |
    ⟨nonempty, fit, sources, sem⟩
  · obtain ⟨k, hk, lt, _⟩ := direct
    exact (first k hk lt).elim
  constructor
  · rcases fit with ⟨v, subset⟩ | ⟨l, subset⟩
    · by_cases small : v.val < 13
      · exact Or.inl (fun t ht => (Finset.mem_singleton.mp (subset ht)).symm ▸ small)
      · right
        have large : 13 ≤ v.val := Nat.le_of_not_gt small
        let l : Fin 13 := ⟨v.val - 13, by have := v.isLt; omega⟩
        have eq : v = ln l := Fin.ext (by change v.val = 13 + (v.val - 13); omega)
        refine ⟨l, Finset.Subset.antisymm (eq ▸ subset) ?_⟩
        obtain ⟨t, ht⟩ := nonempty
        have e := Finset.mem_singleton.mp (subset ht)
        rw [← eq, ← e]
        exact Finset.singleton_subset_iff.mpr ht
    · left
      intro t ht
      obtain ⟨p, rfl⟩ := leaf_point S least.1 (subset ht)
      exact p.isLt
  · intro x
    rw [sem]
    constructor
    · rintro (raw | ⟨k, hk, _⟩)
      · exact raw
      · have source := sources k hk
        exact (first k (Finset.mem_union_right _ source.1) source.2.1).elim
    · exact Or.inl

private theorem points_or_line_and_clean_of_all_neighbors (least : IsLeastAO plane C)
    {g : ℕ} (h : g ∈ junk plane C)
    (sem : ∀ (i : Fin 2) (x : Fin 26 → Bool),
      val C (List.ofFn x) (opnd C g i) = true ↔ ∃ t ∈ side (n := 26) C g i, x t = true)
    (lineSide pointSide : Fin 2) (l : Fin 13)
    (lineEq : side (n := 26) C g lineSide = {ln l}) :
    ∃ t ∈ side (n := 26) C g pointSide, ¬ plane.Adj t (ln l) := by
  obtain ⟨bound, op, x, on, off⟩ := junkData h
  have both := (andValOperands least.1 bound op x).mp on
  obtain ⟨u, hu, xu⟩ := (sem lineSide x).mp (both lineSide)
  obtain ⟨t, ht, xt⟩ := (sem pointSide x).mp (both pointSide)
  rw [lineEq] at hu
  have xl : x (ln l) = true := Finset.mem_singleton.mp hu ▸ xu
  refine ⟨t, ht, fun adj => Bool.false_ne_true (off.symm.trans ?_)⟩
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨t, ln l, adj, xt, xl⟩

/-- A first charged gate that is a dirty AND and fires on an incidence uses
    two point ports or one line and a point port containing a non-neighbour. -/
theorem active_first_and (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    {g : ℕ} (h : g ∈ junk plane C) (first : ∀ k ∈ charged plane C, ¬ k < g)
    {p l : Fin 13} (on : gateVal 26 C g (pairInput (pt p) (ln l)) = true) :
    (∀ (i : Fin 2) (t : Fin 26), t ∈ side (n := 26) C g i → t.val < 13) ∨
    ∃ i : Fin 2, side (n := 26) C g i = {ln l} ∧
      (∀ t ∈ side (n := 26) C g (1-i), t.val < 13) ∧
      ∃ t ∈ side (n := 26) C g (1-i), ¬ plane.Adj t (ln l) := by
  have ports := first_port S least top h first
  obtain ⟨bound, op, _⟩ := junkData h
  have andOn := (andValOperands least.1 bound op _).mp on
  have line (i : Fin 2) {j : Fin 13} (eq : side (n := 26) C g i = {ln j}) :
      side (n := 26) C g i = {ln l} := by
    obtain ⟨t, ht, fired⟩ := ((ports i).2 _).mp (andOn i)
    rw [eq] at ht
    have teq := Finset.mem_singleton.mp ht
    have pair := (pairInput_true (pt p) (ln l) t).mp fired
    rcases pair with atPoint | atLine
    · have bad := congrArg Fin.val (teq.symm.trans atPoint)
      change 13 + j.val = p.val at bad
      have := p.isLt
      omega
    · exact eq.trans (congrArg (fun u : Fin 26 => ({u} : Finset (Fin 26))) (teq.symm.trans atLine))
  rcases (ports 0).1 with p0 | ⟨j, j0⟩ <;> rcases (ports 1).1 with p1 | ⟨k, k1⟩
  · exact Or.inl (fun i => by fin_cases i <;> assumption)
  · have k1' := line 1 k1
    exact Or.inr ⟨1, k1', p0,
      points_or_line_and_clean_of_all_neighbors least h (fun i => (ports i).2) 1 0 l k1'⟩
  · have j0' := line 0 j0
    exact Or.inr ⟨0, j0', p1,
      points_or_line_and_clean_of_all_neighbors least h (fun i => (ports i).2) 0 1 l j0'⟩
  · have j0' := line 0 j0
    have k1' := line 1 k1
    exfalso
    apply gate_not_copy least bound (w := (ln l).val) (by have := (ln l).isLt; omega)
    intro x
    rw [val_ofFn C x (ln l)]
    change gateVal 26 C g x = x (ln l)
    apply Bool.eq_iff_iff.mpr
    rw [andValBoth least.1 bound op x, (ports 0).2, (ports 1).2, j0', k1']
    simp

#print axioms active_first_and

end SixEdge.Plane
