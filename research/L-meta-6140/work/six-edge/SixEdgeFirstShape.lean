import SixEdgeReplayPorts

namespace SixEdge.Formula

/-- The operands of a geometric first gate. With no named line, both
    operands contain points only. With a named line, the right operand
    supplies it and the left supplies a point not on it. -/
def FirstShapeValid (dirty : Bool) (i : Nat) (geometry : Int) (left right : Nat → Bool) : Prop :=
  dirty = true → i = 0 → 0 ≤ geometry →
    (∀ j, 13 ≤ j → j < 26 → left j = false) ∧
    if geometry = 0 then ∀ j, 13 ≤ j → j < 26 → right j = false
    else
      let line := (12+geometry).toNat
      line < 26 ∧ right line = true ∧ ∃ j < 13, j ∉ neighbours line ∧ left j = true

theorem audit_first_shape (p : Input → Bool) (v : Values)
    (dirty : Bool) (i : Nat) (geometry : Int) (a b : Array Lit) (left right : Nat → Bool) :
    Audited p v (FirstShapeValid dirty i geometry left right ∧
        ArrayDenotes v 26 left a ∧ ArrayDenotes v 26 right b)
      (checkFirstShape dirty i geometry a b) (fun _ => True) := by
  unfold checkFirstShape
  split
  · rename_i active
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at active
    have hd : dirty = true := by tauto
    have hi : i = 0 := by tauto
    have hg : 0 ≤ geometry := by tauto
    have lineBounds (j : Nat) (mem : j ∈ List.range' 13 13) : 13 ≤ j ∧ j < 26 := by
      obtain ⟨k,hk,eq⟩ := List.mem_range'.mp mem
      omega
    let pre := FirstShapeValid dirty i geometry left right ∧
      ArrayDenotes v 26 left a ∧ ArrayDenotes v 26 right b
    have leftOff (j : Nat) :
        Audited p v (pre ∧ j ∈ List.range' 13 13)
          (require .firstShape [-a[j]!]) (fun _ => True) := by
      refine (audit_require p v .firstShape _).mono ?_ (fun _ _ h => h)
      intro h
      obtain ⟨lo,hi'⟩ := lineBounds j h.2
      have bit := (h.1.1 hd hi hg).1 j lo hi'
      exact Denotes.unit (bit ▸ (h.1.2.1.2 j hi')).neg
    split
    · rename_i points
      have zero : geometry = 0 := beq_iff_eq.mp points
      apply Audited.forM
      intro j
      refine Audited.bind (leftOff j) ?_
      intro _
      refine (audit_require p v .firstShape _).mono ?_ (fun _ _ h => h)
      intro h
      obtain ⟨lo,hi'⟩ := lineBounds j h.1.2
      have off := (h.1.1.1 hd hi hg).2
      rw [ite_eq_left zero] at off
      exact Denotes.unit (off j lo hi' ▸ (h.1.1.2.2.2 j hi')).neg
    · rename_i named
      have nonzero : geometry ≠ 0 := fun eq => named (beq_iff_eq.mpr eq)
      let line := (12+geometry).toNat
      refine Audited.bind (Audited.forM (List.range' 13 13) leftOff) ?_
      intro _
      refine Audited.bind ((audit_require p v .firstShape [b[line]!]).mono ?_ (fun _ _ h => h)) ?_
      · intro h
        have on := (h.1.1 hd hi hg).2
        rw [ite_eq_right nonzero] at on
        exact Denotes.unit (on.2.1 ▸ (h.1.2.2.2 line on.1))
      intro _
      refine (audit_require p v .firstShape _).mono ?_ (fun _ _ h => h)
      intro h
      have hit := (h.1.1.1 hd hi hg).2
      rw [ite_eq_right nonzero] at hit
      obtain ⟨j,hj,miss,on⟩ := hit.2.2
      refine ⟨a[j]!,List.mem_filterMap.mpr ⟨j,List.mem_range.mpr hj,?_⟩,
        (h.1.1.2.1.2 j (by omega)).2.trans on⟩
      have notContains : (neighbours line).contains j ≠ true := by
        intro yes
        exact miss (List.contains_iff_mem.mp yes)
      exact ite_eq_right notContains
  · exact Audited.pure p v () (fun _ => trivial)

end SixEdge.Formula

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

set_option maxHeartbeats 2500000

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

private theorem first_port_mode (A : GateSchedule P) (b : Fin 2) :
    numberedMode A (replayPort A 0 b) = 0 := by
  cases h : replayPort A 0 b with
  | atom _ => rfl
  | direct j =>
    have earlier := replay_reads_earlier A 0 j b (by rw [h]; rfl)
    exact (Nat.not_lt_zero _ earlier).elim

private noncomputable def physicalPortOrder (A : GateSchedule P) (i : Fin 5) : Fin 2 ≃ Fin 2 :=
  (replayOperandOrder A i).trans (P.order (A.index.symm i))

private theorem replay_port_support (A : GateSchedule P) (i : Fin 5) (b : Fin 2) :
    (replayPort A i b).raw count =
      side (n := 26) C (gateOrder count (A.index.symm i)).val (physicalPortOrder A i b) :=
  P.raw (A.index.symm i) (replayOperandOrder A i b)

private theorem raw_at_vertex (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (b : Fin 2)
    (x : Fin 26) :
    scheduledPortRaw A r i b (r.vertex x).val = true ↔
      x ∈ side (n := 26) C (gateOrder count (A.index.symm i)).val (physicalPortOrder A i b) := by
  have fin : Fin.ofNat 26 (r.vertex x).val = r.vertex x :=
    Fin.ext (Nat.mod_eq_of_lt (r.vertex x).isLt)
  simp only [scheduledPortRaw,fin,r.vertex_left_inverse,decide_eq_true_eq,replay_port_support]

private theorem point_port_off (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (b : Fin 2)
    (points : ∀ x ∈ side (n := 26) C (gateOrder count (A.index.symm i)).val (physicalPortOrder A i b),
      x.val < 13) :
    ∀ j, 13 ≤ j → j < 26 → scheduledPortRaw A r i b j = false := by
  intro j lo hi
  apply Bool.eq_false_iff.mpr
  intro on
  let x := r.inverse.vertex ⟨j,hi⟩
  have slot : (r.vertex x).val = j := congrArg Fin.val (r.vertex_right_inverse ⟨j,hi⟩)
  have small := points x ((raw_at_vertex A r i b x).mp (slot.symm ▸ on))
  let point : Fin 13 := ⟨x.val,small⟩
  have eq : x = pt point := Fin.ext rfl
  have normalizedSmall : (r.vertex x).val < 13 := by
    rw [eq,point_vertex]
    exact (r.point point).isLt
  omega

private theorem other_port : ∀ a b : Fin 2, a ≠ b → a = 1-b := by decide

private theorem line_port_second (A : GateSchedule P) (b : Fin 2) (l : Fin 13)
    (lineSide : side (n := 26) C (gateOrder count (A.index.symm 0)).val b = {ln l})
    (pointSide : ∀ x ∈ side (n := 26) C (gateOrder count (A.index.symm 0)).val (1-b), x.val < 13) :
    physicalPortOrder A 0 1 = b := by
  classical
  let order := physicalPortOrder A 0
  by_contra wrong
  have other := other_port _ _ wrong
  have left : order 0 = b := by
    have different : order 0 ≠ order 1 := fun eq => (by decide : (0 : Fin 2) ≠ 1) (order.injective eq)
    calc
      order 0 = 1 - order 1 := other_port _ _ different
      _ = b := by rw [other]; exact (show ∀ b : Fin 2, 1-(1-b) = b by decide) b
  have wide : ∃ x ∈ (replayPort A 0 0).raw count, 13 ≤ x.val := by
    refine ⟨ln l,?_,?_⟩
    · rw [replay_port_support,left,lineSide]
      exact Finset.mem_singleton_self _
    · change 13 ≤ 13+l.val
      omega
  have narrow : ¬ ∃ x ∈ (replayPort A 0 1).raw count, 13 ≤ x.val := by
    rintro ⟨x,hx,lo⟩
    rw [replay_port_support,other] at hx
    exact (Nat.not_lt_of_ge lo) (pointSide x hx)
  have sorted := replay_operand_score_sorted A 0
  simp only [replayOperandScore,first_port_mode,wide,narrow,ite_true,ite_false] at sorted
  omega

private theorem named_line_ports (A : GateSchedule P) (r : Relabelling) (n : Fin 13)
    (shape : linePortShape C (gateOrder count (A.index.symm 0)).val r n) :
    (∀ j, 13 ≤ j → j < 26 → scheduledPortRaw A r 0 0 j = false) ∧
      13+n.val < 26 ∧ scheduledPortRaw A r 0 1 (13+n.val) = true ∧
      ∃ j < 13, j ∉ neighbours (13+n.val) ∧ scheduledPortRaw A r 0 0 j = true := by
  obtain ⟨b,l,label,lineSide,pointSide,w,hw,miss⟩ := shape
  have right := line_port_second A b l lineSide pointSide
  have left : physicalPortOrder A 0 0 = 1-b := other_port _ _ (fun eq =>
    (by decide : (0 : Fin 2) ≠ 1) ((physicalPortOrder A 0).injective (eq.trans right.symm)))
  refine ⟨point_port_off A r 0 0 (by rwa [left]),by have := n.isLt; omega,?_,?_⟩
  · have existsLine := (raw_at_vertex A r 0 1 (ln l)).mpr (by
      rw [right,lineSide]
      exact Finset.mem_singleton_self _)
    rw [line_vertex,label] at existsLine
    exact existsLine
  · let p : Fin 13 := ⟨w.val,pointSide w hw⟩
    have pointEq : w = pt p := Fin.ext rfl
    have pointOn := (raw_at_vertex A r 0 0 w).mpr (by rwa [left])
    refine ⟨(r.point p).val,(r.point p).isLt,?_,?_⟩
    · intro adj
      have inc := (in_neighbours (r.point p) n).mp adj
      rw [← label] at inc
      apply miss
      rw [pointEq]
      exact (adj_coordinates p l).mp ((r.incidence p l).mp inc)
    · rw [pointEq,point_vertex] at pointOn
      exact pointOn

theorem physical_first_shape (A : GateSchedule P) (first i : Fin 5) (centre : Option (Fin 13))
    (firstEq : first.val = firstBit A.masks.1)
    (choice : ReplayChoice S A.masks (gateOrder count (A.index.symm first)).val centre) :
    let r := choice.coordinates
    FirstShapeValid (A.masks.1.getLsbD i) i.val (mode choice.refinement).2.1
      (scheduledPortRaw A r i 0) (scheduledPortRaw A r i 1) := by
  dsimp only
  intro dirty zero enabled
  have iZero : i = 0 := Fin.ext zero
  subst i
  have firstZero : first = 0 := Fin.ext (by
    rw [firstEq]
    exact Nat.eq_zero_of_le_zero (mask_first_order A.masks.1 0 dirty))
  subst first
  rcases choice with ⟨refinement,r,_,_,_,_,shape⟩
  cases refinement with
  | base | inactive | canonicalInactive | active =>
    change (0 : Int) ≤ -1 at enabled
    omega
  | points =>
    exact ⟨point_port_off A r 0 0 (shape _),point_port_off A r 0 1 (shape _)⟩
  | centreLine =>
    exact named_line_ports A r 0 shape
  | otherLine =>
    exact named_line_ports A r 1 shape

#print axioms audit_first_shape
#print axioms physical_first_shape

end SixEdge.Plane
