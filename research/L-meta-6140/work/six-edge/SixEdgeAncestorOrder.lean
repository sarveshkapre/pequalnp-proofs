import SixEdgeReplayInputs

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

attribute [local instance] gateOpDecEq

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

abbrev OrPath (C : Circuit) := Relation.ReflTransGen (OrStep 26 C)

/-- Follow a path towards this particular dirty AND. An ordinary OR has raw
    support on each operand, so the path must reach a selectable exceptional
    OR before it can reach the raw-empty AND. -/
private theorem promotion_on_path (ao : IsAO2 26 C) {g : Nat} (dirty : g ∈ junk plane C)
    {w : Nat} (raw : (orIn 26 C w).Nonempty) (route : OrPath C w (26+g)) :
    ∃ k ∈ portPromotions plane C w, OrPath C (26+k) (26+g) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases Relation.ReflTransGen.cases_head route with eq | ⟨v,step,rest⟩
    · rw [eq,andRawEmpty (junkData dirty).2.1] at raw
      simp at raw
    · obtain ⟨k,len,rfl,op,hv,lt⟩ := step
      by_cases ordinary : k ∈ lam plane C
      · obtain ⟨_,left,right,_⟩ := Finset.mem_filter.mp ordinary
        obtain ⟨b,hb⟩ := inputsAsOpnd ao len hv
        have rawV : (orIn 26 C v).Nonempty := by
          rw [hb]; fin_cases b
          · exact left
          · exact right
        obtain ⟨j,mem,path⟩ := ih v lt rawV rest
        obtain ⟨ex,rj,reaches⟩ := Finset.mem_filter.mp mem
        exact ⟨j,Finset.mem_filter.mpr ⟨ex,rj,
          (orReaches_iff 26 C k j).mpr ⟨len,Or.inr ⟨op,v,hv,lt,reaches⟩⟩⟩,path⟩
      · obtain ⟨_,_,x,on,off⟩ := junkData dirty
        have notBelow : ¬ BelowF plane C k := fun safe =>
          Bool.false_ne_true (off.symm.trans (safe x (orStep_up (by simp) route on)))
        have ex : k ∈ exceptional plane C := Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr len,op,notBelow⟩,ordinary⟩
        exact ⟨k,Finset.mem_filter.mpr ⟨ex,raw,
          (orReaches_iff 26 C k k).mpr ⟨len,Or.inl rfl⟩⟩,route⟩

def dirtySource (count : (charged plane C).card = 5) (w : Nat) (q : Fin 5) : Prop :=
  dirtyAt count q = true ∧ OrPath C w (26+(gateOrder count q).val)

/-- The stored direct read or promotion preserves the identity of the dirty
    source. This statement is structural and also holds in a muted replay. -/
theorem port_dirty_source (ao : IsAO2 26 C) (i : Fin 5) (b : Fin 2) (q : Fin 5) :
    dirtySource count (opnd C (gateOrder count i).val (P.order i b)) q ↔
      ∃ j, (P.port i b).reads j ∧ dirtySource count (26+(gateOrder count j).val) q := by
  constructor
  · rintro ⟨dirty,path⟩
    cases eq : P.port i b with
    | atom a =>
      have raw := (show (PortChoice.atom a).valid S count i from eq ▸ P.valid i b).1
      have phys := P.raw i b
      rw [eq] at phys
      change a.raw = _ at phys
      obtain ⟨k,mem,rest⟩ := promotion_on_path ao (of_decide_eq_true dirty) (show (side (n := 26) C _ _).Nonempty from phys ▸ raw) path
      have ex := (Finset.mem_filter.mp mem).1
      obtain ⟨j,hj⟩ := (gateOrder count).surjective ⟨k,Finset.mem_union_right _ ex⟩
      have e : (gateOrder count j).val = k := congrArg Subtype.val hj
      exact ⟨j,P.promotions i b a eq j (e.symm ▸ mem),dirty,e.symm ▸ rest⟩
    | direct j =>
      -- A direct choice is made exactly when the physical wire is charged.
      have same := P.direct_wire i b j eq
      exact ⟨j,rfl,dirty,same ▸ path⟩
  · rintro ⟨j,used,dirty,path⟩
    exact ⟨dirty,(P.reach i b j used).trans path⟩

theorem canonical_dirty_source (least : IsLeastAO plane C) {i : Fin 5}
    (later : (GateSchedule.rawFirst P least).afterDirty i) :
    ∃ q, dirtySource count (26+(gateOrder count i).val) q := by
  classical
  obtain ⟨j,hj,lt⟩ := later
  by_contra! missing
  have raw : rawOnly plane C (26+(gateOrder count i).val) := by
    rintro ⟨g,hg,path⟩
    obtain ⟨q,hq⟩ := (gateOrder count).surjective ⟨g,Finset.mem_union_left _ hg⟩
    have e : (gateOrder count q).val = g := congrArg Subtype.val hq
    exact missing q ⟨decide_eq_true (e.symm ▸ hg),e.symm ▸ path⟩
  have reverse := reordered_puts_raw_first (rawSlots count) (decide_eq_true raw)
    (decide_eq_false (dirty_not_rawOnly (of_decide_eq_true hj)))
  exact (not_lt_of_ge reverse.le) lt

noncomputable section

def stageSource (A : GateSchedule P) (i : Fin 5) (q : Nat) : Bool := by
  classical
  exact decide (dirtySource count (26+(gateOrder count (A.index.symm i)).val)
    (A.index.symm (Fin.ofNat 5 q)))

def portSource (A : GateSchedule P) (i : Fin 5) (b : Fin 2) (q : Nat) : Bool := by
  classical
  let j := A.index.symm i
  exact decide (dirtySource count (opnd C (gateOrder count j).val (P.order j (replayOperandOrder A i b)))
    (A.index.symm (Fin.ofNat 5 q)))

theorem stage_source_combine (A : GateSchedule P) (ao : IsAO2 26 C) (i : Fin 5) (q : Nat) (bound : q < 5) :
    (if A.masks.1.getLsbD i then q == i.val else portSource A i 0 q || portSource A i 1 q) =
      stageSource A i q := by
  classical
  let j := A.index.symm i
  let t := A.index.symm (Fin.ofNat 5 q)
  let g := (gateOrder count j).val
  let k := (gateOrder count t).val
  let perm := (replayOperandOrder A i).trans (P.order j)
  have bit : A.masks.1.getLsbD i = dirtyAt count j := ofSlots_bit (fun h => dirtyAt count (A.index.symm h)) i
  by_cases dirty : dirtyAt count j = true
  · rw [bit,ite_eq_left dirty]
    apply Bool.eq_iff_iff.mpr
    change (q == i.val) = true ↔ decide (dirtySource count (26+g) t) = true
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · rintro rfl
      have eq : t = j := by simp [t,j]
      exact ⟨eq.symm ▸ dirty,eq.symm ▸ (Relation.ReflTransGen.refl : OrPath C (26+g) (26+g))⟩
    · rintro ⟨_,path⟩
      rcases Relation.ReflTransGen.cases_head path with eq | ⟨_,⟨h,_,hw,op,_⟩,_⟩
      · have same : j = t := (gateOrder count).injective (Subtype.ext (Nat.add_left_cancel eq))
        have indexEq := congrArg A.index same
        simp only [j,t,Equiv.apply_symm_apply] at indexEq
        have coord := congrArg Fin.val indexEq
        simpa [Fin.ofNat,Nat.mod_eq_of_lt bound] using coord.symm
      · have gh : g = h := Nat.add_left_cancel hw
        have atG : (gateAt C g).op = GateOp.or := gh.symm ▸ op
        have contradiction : GateOp.and = GateOp.or := (junkData (of_decide_eq_true dirty)).2.1.symm.trans atG
        cases contradiction
  · rw [bit,ite_eq_right dirty]
    have ex : g ∈ exceptional plane C := (Finset.mem_union.mp (gateOrder count j).property).resolve_left
      (fun h => dirty (decide_eq_true h))
    obtain ⟨len,op,_⟩ := orData ex
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,portSource,stageSource,decide_eq_true_eq]
    change dirtySource count (opnd C g (perm 0)) t ∨ dirtySource count (opnd C g (perm 1)) t ↔
      dirtySource count (26+g) t
    have lift (b : Fin 2) (z : dirtySource count (opnd C g (perm b)) t) : dirtySource count (26+g) t :=
      ⟨z.1,.head ⟨g,len,rfl,op,opndMem ao len _,opndBound ao len _⟩ z.2⟩
    constructor
    · exact fun h => h.elim (lift 0) (lift 1)
    · rintro ⟨dt,path⟩
      rcases Relation.ReflTransGen.cases_head path with eq | ⟨w,⟨h,_,eq,_,member,_⟩,rest⟩
      · have eq' : g = k := Nat.add_left_cancel eq
        exact (Finset.disjoint_left.mp disjoint_charged (eq' ▸ of_decide_eq_true dt) ex).elim
      · have same : g = h := Nat.add_left_cancel eq
        obtain ⟨b,hb⟩ := inputsAsOpnd ao len (same ▸ member)
        have dz : dirtySource count (opnd C g (perm (perm.symm b))) t :=
          ⟨dt,by rw [Equiv.apply_symm_apply,← hb]; exact rest⟩
        generalize perm.symm b = slot at dz
        fin_cases slot
        · exact Or.inl dz
        · exact Or.inr dz

/-- In the canonical order an exceptional OR after the first dirty AND has
    a strictly earlier dirty source. Its index names a true SAT ancestor bit. -/
theorem canonical_order_witness (least : IsLeastAO plane C) (i : Fin 5)
    (firstOn : (GateSchedule.rawFirst P least).masks.1.getLsbD
      (firstBit (GateSchedule.rawFirst P least).masks.1) = true)
    (isOr : (GateSchedule.rawFirst P least).masks.1.getLsbD i = false)
    (later : firstBit (GateSchedule.rawFirst P least).masks.1 < i.val) :
    ∃ q : Fin 5, q < i ∧ (GateSchedule.rawFirst P least).masks.1.getLsbD q = true ∧
      stageSource (GateSchedule.rawFirst P least) i q.val = true := by
  classical
  let A := GateSchedule.rawFirst P least
  let j := A.index.symm i
  have after : A.afterDirty j := (replay_after_first A firstOn _).mpr (by simpa [j] using later)
  obtain ⟨k,dirty,path⟩ := canonical_dirty_source least after
  have bit (t : Fin 5) : A.masks.1.getLsbD t = dirtyAt count (A.index.symm t) :=
    ofSlots_bit (fun h => dirtyAt count (A.index.symm h)) t
  have off : dirtyAt count j = false := (bit i).symm.trans isOr
  have ne : k ≠ j := fun eq => Bool.false_ne_true (off.symm.trans (eq ▸ dirty))
  have original : k < j := by
    apply lt_of_le_of_ne _ ne
    apply (gateOrder count).le_iff_le.mp
    have h := orStep_le path
    change (gateOrder count k).val ≤ (gateOrder count j).val
    omega
  have rawJ : rawSlots count j = false :=
    decide_eq_false (fun no => no ⟨_,of_decide_eq_true dirty,path⟩)
  have earlier : A.index k < A.index j := reordered_keeps_reads _ original (by simp [rawJ])
  refine ⟨A.index k,by simpa [j] using earlier,?_,?_⟩
  · rw [show (GateSchedule.rawFirst P least).masks.1.getLsbD (A.index k) = _ from bit (A.index k),
      Equiv.symm_apply_apply]
    exact dirty
  · change stageSource A i (A.index k).val = true
    apply decide_eq_true
    rw [Fin.ofNat_val_eq_self,Equiv.symm_apply_apply]
    exact ⟨dirty,path⟩

#print axioms canonical_order_witness

end
end SixEdge.Plane
