import SixEdgeAncestorOrder
import SixEdgeReplayOutputs
import SixEdgeBuildPort

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

set_option maxHeartbeats 3000000

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

private theorem fin_slot {n j : Nat} [NeZero n] (bound : j < n) :
    Fin.ofNat n j = ⟨j,bound⟩ := Fin.ext (Nat.mod_eq_of_lt bound)

private theorem any_false (xs : List Nat) : xs.any (fun _ => false) = false := by
  induction xs <;> simp_all

private theorem selected_direct {n : Nat} (small : n ≤ 5) (q : Fin 5) (earlier : q.val < n)
    (bits : Nat → Bool) :
    (List.range n).any (fun j => (q == Fin.ofNat 5 j) && bits j) = bits q.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_range,Bool.and_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨j,hj,eq,on⟩
    have eq' : q.val = j := congrArg Fin.val (eq.trans (fin_slot (by omega)))
    rwa [eq']
  · intro on
    exact ⟨q.val,earlier, (fin_slot q.isLt).symm,on⟩

noncomputable def scheduledPortRaw (A : GateSchedule P) (r : Relabelling)
    (i : Fin 5) (b : Fin 2) (x : Nat) : Bool :=
  decide (r.inverse.vertex (Fin.ofNat 26 x) ∈ (replayPort A i b).raw count)

theorem operands_raw_eq (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (b : Fin 2)
    (n : Nat) (size : n = i.val) (x : Nat) :
    operandsRawBit (physicalLeaves S r (replayInputs A r)) n i.val b.val
      (fun j => scheduledRaw A r (Fin.ofNat 5 j)) x = scheduledPortRaw A r i b x := by
  classical
  have gi : Fin.ofNat 5 i.val = i := fin_slot i.isLt
  have bi : Fin.ofNat 2 b.val = b := fin_slot b.isLt
  cases h : replayPort A i b with
  | atom a =>
    simp [operandsRawBit,scheduledPortRaw,physicalLeaves,replayInputs,h,PortChoice.raw]
  | direct q =>
    have earlier : (A.index q).val < n := by
      rw [size]
      exact replay_reads_earlier A i q b (by rw [h]; rfl)
    simp only [operandsRawBit,scheduledPortRaw,physicalLeaves,replayInputs,gi,bi,h,PortChoice.raw,Bool.false_or]
    rw [selected_direct (by omega) (A.index q) earlier]
    have eq : Fin.ofNat 5 (A.index q).val = A.index q := fin_slot (A.index q).isLt
    simp only [scheduledRaw,eq,Equiv.symm_apply_apply]

private theorem atoms_sample (r : Relabelling) (a : AtomChoice) (k : Nat) (hk : k < samples.size) :
    (samples[k]!).any (fun x => decide (r.inverse.vertex (Fin.ofNat 26 x) ∈ a.raw)) = true ↔
      ∃ x ∈ a.raw, (sampleInput k ∘ r.vertex) x = true := by
  simp only [List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨x,hx,mem⟩
    let g : Fin 26 := ⟨x,sample_vertex hk hx⟩
    have eq : Fin.ofNat 26 x = g := fin_slot g.isLt
    refine ⟨r.inverse.vertex g,eq ▸ mem,?_⟩
    change samples[k]!.contains (r.vertex (r.inverse.vertex g)).val = true
    rw [r.vertex_right_inverse]
    exact List.contains_iff_mem.mpr hx
  · rintro ⟨x,hx,on⟩
    refine ⟨(r.vertex x).val,List.contains_iff_mem.mp on,?_⟩
    have eq : Fin.ofNat 26 (r.vertex x).val = r.vertex x := fin_slot (r.vertex x).isLt
    rwa [eq,r.vertex_left_inverse]

private theorem promoted_sample (A : GateSchedule P) (i : Fin 5) (b : Fin 2) (a : AtomChoice)
    (choice : replayPort A i b = .atom a) (stages : Array Stage) (size : stages.size = i.val)
    (dirty : ∀ j : Fin 5, j.val < stages.size → stages[j.val]!.dirty = dirtyAt count (A.index.symm j))
    (past : Nat → Bool) :
    (promotionSlots stages).any (fun j => decide (A.index.symm (Fin.ofNat 5 j) ∈ a.promoted) && past j) = true ↔
      ∃ q ∈ a.promoted, past (A.index q).val = true := by
  simp only [List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨j,has,chosen,on⟩
    have hj := List.mem_range.mp (List.mem_filter.mp has).1
    let t : Fin 5 := ⟨j,by have := i.isLt; omega⟩
    have coord : A.index (A.index.symm (Fin.ofNat 5 j)) = t := by
      rw [Equiv.apply_symm_apply]
      exact fin_slot t.isLt
    exact ⟨A.index.symm (Fin.ofNat 5 j),chosen,by rw [coord]; exact on⟩
  · rintro ⟨q,chosen,on⟩
    let j := A.index q
    have earlier : j.val < stages.size := by
      rw [size]
      exact replay_reads_earlier A i q b (by rw [choice]; exact chosen)
    have valid : (PortChoice.atom a).valid S count (A.index.symm i) :=
      choice ▸ P.valid (A.index.symm i) (replayOperandOrder A i b)
    have exceptional := (valid.2.2.2 q chosen).2.1
    have off : dirtyAt count q = false := decide_eq_false
      (fun h => Finset.disjoint_left.mp disjoint_charged h exceptional)
    have available : j.val ∈ promotionSlots stages := by
      unfold promotionSlots
      refine List.mem_filter.mpr ⟨List.mem_range.mpr earlier,?_⟩
      rw [dirty j earlier]
      simp only [j,Equiv.symm_apply_apply,off,Bool.not_false]
    have eq : Fin.ofNat 5 j.val = j := fin_slot j.isLt
    exact ⟨j.val,available,by simpa only [eq,j,Equiv.symm_apply_apply] using chosen,on⟩

theorem operands_sample_eq (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (b : Fin 2)
    (stages : Array Stage) (size : stages.size = i.val)
    (dirty : ∀ j : Fin 5, j.val < stages.size → stages[j.val]!.dirty = dirtyAt count (A.index.symm j))
    (prior : Nat → Nat → Bool) (k : Nat) (hk : k < samples.size) :
    operandsSampleBit (physicalLeaves S r (replayInputs A r)) stages i.val b.val prior k =
      replayPortBit A i b (sampleInput k ∘ r.vertex) (fun j => prior j k) := by
  classical
  have gi : Fin.ofNat 5 i.val = i := fin_slot i.isLt
  have bi : Fin.ofNat 2 b.val = b := fin_slot b.isLt
  cases h : replayPort A i b with
  | direct q =>
    have earlier : (A.index q).val < stages.size := by
      rw [size]
      exact replay_reads_earlier A i q b (by rw [h]; rfl)
    simp only [operandsSampleBit,physicalLeaves,replayInputs,gi,bi,h,replayPortBit,PortChoice.value]
    simp only [Bool.false_and,any_false,Bool.false_or]
    exact selected_direct (by omega) (A.index q) earlier (fun j => prior j k)
  | atom a =>
    apply Bool.eq_iff_iff.mpr
    simp only [operandsSampleBit,physicalLeaves,replayInputs,gi,bi,h,replayPortBit,PortChoice.value,
      Bool.false_and,any_false,Bool.or_false,Bool.or_eq_true,decide_eq_true_eq]
    exact or_congr (atoms_sample r a k hk) (promoted_sample A i b a h stages size dirty (fun j => prior j k))

theorem operand_ancestor_eq (A : GateSchedule P) (r : Relabelling) (ao : IsAO2 26 C)
    (i : Fin 5) (b : Fin 2) (stages : Array Stage) (size : stages.size = i.val)
    (dirty : ∀ j : Fin 5, j.val < stages.size → stages[j.val]!.dirty = dirtyAt count (A.index.symm j))
    (q : Nat) :
    operandAncestorBit (physicalLeaves S r (replayInputs A r)) stages i.val b.val
      (fun j => stageSource A (Fin.ofNat 5 j)) q = portSource A i b q := by
  classical
  let t := A.index.symm (Fin.ofNat 5 q)
  have source := port_dirty_source (P := P) ao (A.index.symm i) (replayOperandOrder A i b) t
  have gi : Fin.ofNat 5 i.val = i := fin_slot i.isLt
  have bi : Fin.ofNat 2 b.val = b := fin_slot b.isLt
  cases h : replayPort A i b with
  | direct j =>
    have earlier : (A.index j).val < stages.size := size.symm ▸ replay_reads_earlier A i j b (by rw [h]; rfl)
    simp only [operandAncestorBit,physicalLeaves,replayInputs,gi,bi,h,Bool.false_and,any_false,Bool.or_false]
    rw [selected_direct (by omega) (A.index j) earlier]
    apply Bool.eq_iff_iff.mpr
    simp only [portSource,stageSource,decide_eq_true_eq,Fin.ofNat_val_eq_self,Equiv.symm_apply_apply]
    change _ ↔ dirtySource count _ t
    rw [source]
    change _ ↔ ∃ k, (replayPort A i b).reads k ∧ _
    simp [h,PortChoice.reads,t]
  | atom a =>
    apply Bool.eq_iff_iff.mpr
    simp only [operandAncestorBit,physicalLeaves,replayInputs,gi,bi,h,Bool.false_and,any_false,Bool.false_or]
    rw [promoted_sample A i b a h stages size dirty]
    simp only [portSource,stageSource,decide_eq_true_eq,Fin.ofNat_val_eq_self,Equiv.symm_apply_apply]
    change _ ↔ dirtySource count _ t
    rw [source]
    change _ ↔ ∃ k, (replayPort A i b).reads k ∧ _
    simp [h,PortChoice.reads,t]

attribute [local irreducible] buildPort

/-- At any of the five positions, the exact port builder emits both the
    physical operand's support and its values on all the replay samples. -/
theorem buildPort_scheduled (A : GateSchedule P) (r : Relabelling) (v : Values)
    (i : Fin 5) (b : Fin 2) (stages : Array Stage) (hosts : Array Leaf) (canonical : Bool)
    (prior : Nat → Nat → Bool) :
    let p := physicalLeaves S r (replayInputs A r)
    BuildDefines p v
      (v 1 = true ∧ stages.size = i.val ∧
        (∀ j : Fin 5, j.val < stages.size → stages[j.val]!.dirty = dirtyAt count (A.index.symm j)) ∧
        (∀ j < stages.size, ArrayDenotes v 26 (scheduledRaw A r (Fin.ofNat 5 j)) stages[j]!.raw) ∧
        ∀ j < stages.size, ArrayDenotes v samples.size (prior j) stages[j]!.values)
      (buildPort stages hosts i.val b.val canonical) (fun port =>
        ArrayDenotes v 26 (scheduledPortRaw A r i b) port.raw ∧
        ArrayDenotes v samples.size (fun k =>
          replayPortBit A i b (sampleInput k ∘ r.vertex) (fun j => prior j k)) port.values) := by
  dsimp only
  refine (buildPort_defines (physicalLeaves S r (replayInputs A r)) v stages hosts i.val b.val canonical
    (fun j => scheduledRaw A r (Fin.ofNat 5 j)) prior).mono ?_ ?_
  · rintro ⟨one,_,_,raw,values⟩
    exact ⟨one,fun _ hk _ hx => sample_vertex hk hx,raw,values⟩
  · rintro ⟨_,size,dirty,_,_⟩ port ⟨raw,vals⟩
    refine ⟨⟨raw.1,?_⟩,⟨vals.1,?_⟩⟩
    · intro x hx
      exact ⟨(raw.2 x hx).1,(raw.2 x hx).2.trans (operands_raw_eq A r i b stages.size size x)⟩
    · intro k hk
      exact ⟨(vals.2 k hk).1,(vals.2 k hk).2.trans (operands_sample_eq A r i b stages size dirty prior k hk)⟩

theorem buildPort_with_sources (A : GateSchedule P) (r : Relabelling) (ao : IsAO2 26 C)
    (v : Values) (i : Fin 5) (b : Fin 2) (stages : Array Stage) (hosts : Array Leaf) (canonical : Bool)
    (prior : Nat → Nat → Bool) :
    let p := physicalLeaves S r (replayInputs A r)
    BuildDefines p v
      (v 1 = true ∧ stages.size = i.val ∧
        (∀ j : Fin 5, j.val < stages.size → stages[j.val]!.dirty = dirtyAt count (A.index.symm j)) ∧
        (∀ j < stages.size, ArrayDenotes v 26 (scheduledRaw A r (Fin.ofNat 5 j)) stages[j]!.raw) ∧
        (∀ j < stages.size, ArrayDenotes v samples.size (prior j) stages[j]!.values) ∧
        (canonical = true → ∀ j < stages.size,
          ArrayDenotes v 5 (stageSource A (Fin.ofNat 5 j)) stages[j]!.ancestors))
      (buildPort stages hosts i.val b.val canonical) (fun port =>
        ArrayDenotes v 26 (scheduledPortRaw A r i b) port.raw ∧
        ArrayDenotes v samples.size (fun k =>
          replayPortBit A i b (sampleInput k ∘ r.vertex) (fun j => prior j k)) port.values ∧
        (canonical = true → ArrayDenotes v 5 (portSource A i b) port.ancestors)) := by
  let p := physicalLeaves S r (replayInputs A r)
  refine (buildPort_tables p v stages hosts i.val b.val canonical
    (fun j => scheduledRaw A r (Fin.ofNat 5 j)) prior _ _
    (fun d ps => defines_port_ancestors p v stages i.val b.val d ps
      (fun j => stageSource A (Fin.ofNat 5 j)) canonical)).mono ?_ ?_
  · rintro ⟨one,_,_,raw,vals,anc⟩
    exact ⟨⟨one,fun _ hk _ hx => sample_vertex hk hx,raw,vals⟩,anc⟩
  · rintro ⟨_,size,dirty,_,_,_⟩ port ⟨raw,vals,anc⟩
    refine ⟨⟨raw.1,?_⟩,⟨vals.1,?_⟩,fun enabled => ⟨(anc enabled).1,?_⟩⟩
    · intro x hx
      exact ⟨(raw.2 x hx).1,(raw.2 x hx).2.trans (operands_raw_eq A r i b stages.size size x)⟩
    · intro k hk
      exact ⟨(vals.2 k hk).1,(vals.2 k hk).2.trans (operands_sample_eq A r i b stages size dirty prior k hk)⟩
    · intro q hq
      have lit := (anc enabled).2 q hq
      exact ⟨lit.1,lit.2.trans (operand_ancestor_eq A r ao i b stages size dirty q)⟩

#print axioms buildPort_scheduled

end SixEdge.Plane
