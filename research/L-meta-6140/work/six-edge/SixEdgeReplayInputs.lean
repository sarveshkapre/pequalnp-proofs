import SixEdgeRefinement

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

def numberedMode (A : GateSchedule P) : PortChoice → Nat
  | .atom _ => 0
  | .direct j => (A.index j).val + 1

noncomputable def replayOperandScore (A : GateSchedule P) (p : PortChoice) : Nat := by
  classical
  exact 2*numberedMode A p + if ∃ v ∈ p.raw count, 13 ≤ v.val then 1 else 0

/-- The atom/direct selectors are sorted by the new gate order. If the two
    selectors tie, put a singleton line operand second. -/
noncomputable def replayOperandOrder (A : GateSchedule P) (i : Fin 5) : Fin 2 ≃ Fin 2 := by
  classical
  let p := P.port (A.index.symm i)
  let score (b : Fin 2) := replayOperandScore A (p b)
  exact swapPorts (decide (score 1 < score 0))

noncomputable def replayPort (A : GateSchedule P) (i : Fin 5) (b : Fin 2) : PortChoice :=
  P.port (A.index.symm i) (replayOperandOrder A i b)

theorem replay_operand_score_sorted (A : GateSchedule P) (i : Fin 5) :
    replayOperandScore A (replayPort A i 0) ≤ replayOperandScore A (replayPort A i 1) := by
  classical
  let p := P.port (A.index.symm i)
  let score (b : Fin 2) := replayOperandScore A (p b)
  change score (swapPorts (decide (score 1 < score 0)) 0) ≤
    score (swapPorts (decide (score 1 < score 0)) 1)
  by_cases flip : score 1 < score 0
  · simpa [swapPorts,flip] using flip.le
  · simpa [swapPorts,flip] using Nat.le_of_not_gt flip

theorem replay_port_sorted (A : GateSchedule P) (i : Fin 5) :
    numberedMode A (replayPort A i 0) ≤ numberedMode A (replayPort A i 1) := by
  have sorted := replay_operand_score_sorted A i
  unfold replayOperandScore at sorted
  split at sorted <;> split at sorted <;> omega

theorem replay_reads_earlier (A : GateSchedule P) (i j : Fin 5) (b : Fin 2)
    (read : (replayPort A i b).reads j) : A.index j < i := by
  have h := A.respects read
  simpa only [Equiv.apply_symm_apply] using h

def replayHost (r : Relabelling) : PortHost → Nat
  | .singleton v => (r.vertex v).val
  | .leaf l => 26+(r.line l).val

def replayRoute (A : GateSchedule P) (l : Fin 13) (b : Fin 2) (j : Fin 5) : Prop :=
  topRoute S count l b j ∧ A.afterDirty j

noncomputable def replayInputs (A : GateSchedule P) (r : Relabelling) : Input → Bool := by
  classical
  let sl := Fin.ofNat 5
  let port := fun i b => replayPort A (sl i) (Fin.ofNat 2 b)
  let line := fun l => r.inverse.line (Fin.ofNat 13 (l-13))
  exact fun tag => match tag with
    | .leaf _ _ => false
    | .atomMode i b => match port i b with | .atom _ => true | .direct _ => false
    | .direct i b j => match port i b with | .atom _ => false | .direct q => A.index q == sl j
    | .atom i b v => match port i b with
      | .atom a => decide (r.inverse.vertex (Fin.ofNat 26 v) ∈ a.raw)
      | .direct _ => false
    | .host i b h => match port i b with | .atom a => replayHost r a.host == h | .direct _ => false
    | .promotion i b j => match port i b with
      | .atom a => decide (A.index.symm (sl j) ∈ a.promoted)
      | .direct _ => false
    | .topCentre l j => decide (replayRoute A (line l) (S.center (S.index (line l))) (A.index.symm (sl j)))
    | .topLeaf l j => decide (replayRoute A (line l) (1-S.center (S.index (line l))) (A.index.symm (sl j)))

theorem replay_route_raw (A : GateSchedule P) {l : Fin 13} {b : Fin 2} {j : Fin 5}
    (use : replayRoute A l b j) :
    (gateOrder count j).val ∈ exceptional plane C ∧
      (wireRaw count j).Nonempty ∧ wireRaw count j ⊆ side (n := 26) C (S.index l).val b :=
  top_route_valid S count use.1

theorem mask_first_order : ∀ mask : BitVec 5, ∀ pos : Fin 5,
    mask.getLsbD pos = true → Formula.firstBit mask ≤ pos.val := by decide +kernel

theorem replay_after_first (A : GateSchedule P) (firstOn : A.masks.1.getLsbD (Formula.firstBit A.masks.1) = true)
    (j : Fin 5) : A.afterDirty j ↔ Formula.firstBit A.masks.1 < (A.index j).val := by
  constructor
  · rintro ⟨i,dirty,earlier⟩
    have bit : A.masks.1.getLsbD (A.index i) = true := by
      simpa only [GateSchedule.masks,ofSlots_bit,Equiv.symm_apply_apply] using dirty
    exact lt_of_le_of_lt (mask_first_order _ _ bit) earlier
  · intro earlier
    let i : Fin 5 := ⟨Formula.firstBit A.masks.1, lt_trans earlier (A.index j).isLt⟩
    refine ⟨A.index.symm i, ?_, ?_⟩
    · simpa only [GateSchedule.masks,ofSlots_bit] using (show A.masks.1.getLsbD i = true from firstOn)
    · rw [Equiv.apply_symm_apply]
      change Formula.firstBit A.masks.1 < (A.index j).val
      exact earlier

theorem replay_route_in_slots (A : GateSchedule P) (stages : Array Stage)
    (dirty : ∀ i : Fin 5, stages[i.val]!.dirty = dirtyAt count (A.index.symm i))
    (firstOn : A.masks.1.getLsbD (Formula.firstBit A.masks.1) = true)
    {l : Fin 13} {b : Fin 2} {j : Fin 5} (route : replayRoute A l b j) :
    (A.index j).val ∈ topSlots stages (Formula.firstBit A.masks.1) := by
  have exceptional := (replay_route_raw A route).1
  have notDirty : dirtyAt count j = false := decide_eq_false
    (fun h => Finset.disjoint_left.mp disjoint_charged h exceptional)
  have stageOr : stages[(A.index j).val]!.dirty = false := by
    rw [dirty, Equiv.symm_apply_apply, notDirty]
  exact List.mem_filter.mpr ⟨List.mem_range.mpr (A.index j).isLt,
    by simp [stageOr, (replay_after_first A firstOn j).mp route.2]⟩

noncomputable def replayPortBit (A : GateSchedule P) (i : Fin 5) (b : Fin 2)
    (x : Fin 26 → Bool) (past : Nat → Bool) : Bool := by
  classical
  exact decide ((replayPort A i b).value x (fun j => past (A.index j).val))

theorem replay_stage_combine (A : GateSchedule P) (i : Fin 5) (x : Fin 26 → Bool) (past : Nat → Bool) :
    A.stage x i.val past =
      if dirtyAt count (A.index.symm i) then replayPortBit A i 0 x past && replayPortBit A i 1 x past
      else replayPortBit A i 0 x past || replayPortBit A i 1 x past := by
  classical
  let q := A.index.symm i
  let order := replayOperandOrder A i
  let on := fun b => (P.port q b).value x (fun j => past (A.index j).val)
  have pair (b : Fin 2) : b = 0 ∨ b = 1 := by decide +revert
  have andPerm : (∀ b, on b) ↔ on (order 0) ∧ on (order 1) := by
    refine ⟨fun h => ⟨h _,h _⟩,?_⟩
    intro h b
    rcases pair (order.symm b) with left | right
    · rw [← Equiv.apply_symm_apply order b,left]
      exact h.1
    · rw [← Equiv.apply_symm_apply order b,right]
      exact h.2
  have orPerm : (∃ b, on b) ↔ on (order 0) ∨ on (order 1) := by
    refine ⟨?_, fun h => h.elim (fun h₀ => ⟨_,h₀⟩) (fun h₁ => ⟨_,h₁⟩)⟩
    rintro ⟨b,h⟩
    rcases pair (order.symm b) with left | right
    · left
      rwa [← left,Equiv.apply_symm_apply]
    · right
      rwa [← right,Equiv.apply_symm_apply]
  simp only [GateSchedule.stage, i.isLt, dite_true, OrderedPorts.onAt]
  apply Bool.eq_iff_iff.mpr
  split
  · change ((decide (∀ b, on b)) = true) ↔
      (replayPortBit A i 0 x past && replayPortBit A i 1 x past) = true
    rw [Bool.and_eq_true]
    change (decide (∀ b, on b) = true) ↔ (decide (on (order 0)) = true ∧ decide (on (order 1)) = true)
    simpa only [decide_eq_true_eq] using andPerm
  · change ((decide (∃ b, on b)) = true) ↔
      (replayPortBit A i 0 x past || replayPortBit A i 1 x past) = true
    rw [Bool.or_eq_true]
    change (decide (∃ b, on b) = true) ↔ (decide (on (order 0)) = true ∨ decide (on (order 1)) = true)
    simpa only [decide_eq_true_eq] using orPerm

theorem replay_dirty_has_reader (A : GateSchedule P) (r : Relabelling) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (j : Fin 5) (dirty : A.masks.1.getLsbD j = true) :
    ∃ i : Fin 5, j < i ∧ ∃ b : Fin 2, replayInputs A r (.direct i.val b.val j.val) = true := by
  have active : dirtyAt count (A.index.symm j) = true :=
    (ofSlots_bit (fun n => dirtyAt count (A.index.symm n)) j).symm ▸ dirty
  obtain ⟨q,_,c,choice⟩ := P.read_dirty least empty (A.index.symm j) active
  let i := A.index q
  let b := (replayOperandOrder A i).symm c
  have read : replayPort A i b = .direct (A.index.symm j) := by
    simp only [replayPort,i,Equiv.symm_apply_apply,b,Equiv.apply_symm_apply]
    exact choice
  have before := replay_reads_earlier A i (A.index.symm j) b (by rw [read]; rfl)
  refine ⟨i,by simpa only [Equiv.apply_symm_apply] using before,b,?_⟩
  simp [replayInputs,read]

#print axioms replay_port_sorted
#print axioms replay_reads_earlier
#print axioms replay_route_in_slots
#print axioms replay_stage_combine
#print axioms replay_dirty_has_reader

end SixEdge.Plane
