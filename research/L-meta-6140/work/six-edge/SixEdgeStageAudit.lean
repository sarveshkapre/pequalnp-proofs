import SixEdgePortClauseAudit

namespace SixEdge.Formula

set_option maxHeartbeats 2500000

/-- Like the local clause audit, but the interpretation includes the prefix.
    This lets a continuation reuse semantic proofs of earlier emitted wires. -/
def StageAudit (p : Input → Bool) (v : Values) {α : Type} (pre : Prop)
    (m : Build α) (post : α → Prop) : Prop :=
  ∀ s, let (a,t) := m.run s
    ∃ es, t.events.toList = s.events.toList ++ es ∧
      ((∀ e ∈ t.events.toList, Interprets p v e) → pre →
        (∀ e ∈ es, Meets v e) ∧ post a)

namespace StageAudit

theorem pure (p : Input → Bool) (v : Values) {α : Type} {pre : Prop} {post : α → Prop}
    (a : α) (h : pre → post a) : StageAudit p v pre (Pure.pure a) post :=
  fun _ => ⟨[],by simp,fun _ hp => ⟨by simp,h hp⟩⟩

theorem mono {p : Input → Bool} {v : Values} {α : Type}
    {pre ready : Prop} {m : Build α} {u w : α → Prop}
    (audit : StageAudit p v pre m u) (before : ready → pre)
    (after : ready → ∀ a, u a → w a) : StageAudit p v ready m w := by
  intro s
  obtain ⟨es,append,ok⟩ := audit s
  refine ⟨es,append,?_⟩
  intro defs h
  have done := ok defs (before h)
  exact ⟨done.1,after h _ done.2⟩

theorem bind {p : Input → Bool} {v : Values} {α β : Type}
    {pre : Prop} {m : Build α} {f : α → Build β} {u : α → Prop} {w : β → Prop}
    (first : StageAudit p v pre m u) (next : ∀ a, StageAudit p v (pre ∧ u a) (f a) w) :
    StageAudit p v pre (m >>= f) w := by
  intro s
  obtain ⟨es,appended,checked⟩ := first s
  obtain ⟨fs,more,after⟩ := next (m s).1 (m s).2
  refine ⟨es ++ fs,?_,?_⟩
  · rw [more,appended,List.append_assoc]
  · intro defs pre
    have done := checked (fun e he => defs e (more ▸ List.mem_append_left _ he)) pre
    have later := after defs ⟨pre,done.2⟩
    refine ⟨fun e he => ?_,later.2⟩
    rcases List.mem_append.mp he with h | h
    · exact done.1 e h
    · exact later.1 e h

theorem thenKeep {p : Input → Bool} {v : Values} {α β : Type}
    {pre : Prop} {m : Build α} {f : α → Build β} {post : β → Prop}
    (action : StageAudit p v pre m (fun _ => True))
    (next : ∀ x, StageAudit p v pre (f x) post) : StageAudit p v pre (m >>= f) post :=
  bind action (fun a => (next a).mono And.left (fun _ _ h => h))

theorem of_audited {p : Input → Bool} {v : Values} {α : Type}
    {pre : Prop} {m : Build α} {post : α → Prop} (audit : Audited p v pre m post) :
    StageAudit p v pre m post := by
  intro s
  obtain ⟨es,append,ok⟩ := audit s
  refine ⟨es,append,?_⟩
  intro defs pre
  have h := ok (fun e he => defs e (append ▸ List.mem_append_right _ he)) pre
  exact ⟨h.1,h.2⟩

theorem with_defines {p : Input → Bool} {v : Values} {α : Type}
    {pre : Prop} {m : Build α} {u w : α → Prop}
    (audit : Audited p v pre m u) (value : BuildDefines p v pre m w) :
    StageAudit p v pre m (fun a => u a ∧ w a) := by
  intro s
  obtain ⟨es,append,ok⟩ := of_audited audit s
  refine ⟨es,append,?_⟩
  intro defs pre
  have h := ok defs pre
  exact ⟨h.1,h.2,(value s).2 defs pre⟩

end StageAudit

private theorem audit_ancestor_bits (p : Input → Bool) (v : Values) (dirty : Bool) (i : Nat)
    (a b : Port) (x y bit : Nat → Bool)
    (combine : ∀ q < 5, (if dirty then q == i else x q || y q) = bit q) :
    Audited p v (v 1 = true ∧ ArrayDenotes v 5 x a.ancestors ∧ ArrayDenotes v 5 y b.ancestors)
      (stageAncestors dirty i a b) (ArrayDenotes v 5 bit) := by
  let pre := v 1 = true ∧ ArrayDenotes v 5 x a.ancestors ∧ ArrayDenotes v 5 y b.ancestors
  have each q : Audited p v (pre ∧ q ∈ List.range 5)
      (if dirty then pure (if q == i then 1 else -1) else makeOr [a.ancestors[q]!,b.ancestors[q]!])
      (Denotes v (bit q)) := by
    cases dirty with
    | false =>
      exact (denote_or_pair v _ _ _ _).mono
        (fun h => ⟨h.1.1,h.1.2.1.2 q (List.mem_range.mp h.2),h.1.2.2.2 q (List.mem_range.mp h.2)⟩)
        (fun h _ z => (combine q (List.mem_range.mp h.2)) ▸ z)
    | true =>
      exact Audited.pure p v _ (fun h => (combine q (List.mem_range.mp h.2)) ▸ Denotes.constant v h.1.1 (q == i))
  unfold stageAncestors buildLitArray
  refine Audited.bind (Audited.mapM (List.range 5) each) (fun arr => ?_)
  exact Audited.pure _ _ _ (fun h => list_to_array_denotes h.2)

/-- The order clause literally contains the five ancestor literals. A single
    dirty source in the returned table supplies its satisfying literal. -/
theorem audit_stage_ancestor_order (p : Input → Bool) (v : Values) (key : CertificateKey)
    (i : Nat) (a b : Port) (x y bit : Nat → Bool)
    (combine : ∀ q < 5, (if key.1.1.getLsbD i then q == i else x q || y q) = bit q)
    (witness : (mode key.2).2.2 = true → key.1.1.getLsbD i = false →
      firstBit key.1.1 < i → ∃ q < 5, bit q = true)
    (centreOff : (mode key.2).2.1 = 0 → key.1.2.getLsbD i = true → bit 0 = false) :
    let canonical := (mode key.2).2.2
    StageAudit p v (v 1 = true ∧ (canonical = true → ArrayDenotes v 5 x a.ancestors) ∧
      (canonical = true → ArrayDenotes v 5 y b.ancestors))
      (checkStageAncestors key i a b) (fun arr => canonical = true → ArrayDenotes v 5 bit arr) := by
  dsimp only
  unfold checkStageAncestors
  split
  · rename_i enabled
    refine StageAudit.bind ((StageAudit.of_audited (audit_ancestor_bits p v _ i a b x y bit combine)).mono
      (fun h => ⟨h.1,h.2.1 enabled,h.2.2 enabled⟩) (fun _ _ z => z)) ?_
    intro anc
    unfold checkAncestorRules
    have order : StageAudit p v (ArrayDenotes v 5 bit anc)
        (requireWhen (!(key.1.1.getLsbD i) && decide (i > firstBit key.1.1)) .canonicalOrder anc.toList)
        (fun _ => True) := by
      unfold requireWhen
      split
      · rename_i active
        simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at active
        obtain ⟨q,hq,on⟩ := witness enabled active.1 active.2
        refine (StageAudit.of_audited (audit_require p v .canonicalOrder anc.toList)).mono ?_ (fun _ _ z => z)
        intro ok
        have atQ : q < anc.size := ok.1.symm ▸ hq
        exact ⟨anc[q]!,by rw [getElem!_pos anc q atQ]; exact Array.getElem_mem_toList atQ,
          (ok.2 q hq).2.trans on⟩
      · exact StageAudit.pure p v () (fun _ => trivial)
    have centre : StageAudit p v (ArrayDenotes v 5 bit anc)
        (requireWhen (!(key.1.1.getLsbD i) && ((mode key.2).2.1 == 0 && key.1.2.getLsbD i))
          .centreExclusion [-anc[0]!]) (fun _ => True) := by
      unfold requireWhen
      split
      · rename_i active
        simp only [Bool.and_eq_true,beq_iff_eq] at active
        refine (StageAudit.of_audited (audit_require p v _ _)).mono ?_ (fun _ _ z => z)
        intro ok
        have zero := (ok.2 0 (by decide)).neg
        rw [centreOff active.2.1 active.2.2] at zero
        exact zero.unit
      · exact StageAudit.pure p v () (fun _ => trivial)
    refine StageAudit.thenKeep ((StageAudit.thenKeep (order.mono And.right (fun _ _ z => z))
      (fun _ => centre.mono And.right (fun _ _ z => z)))) ?_
    exact fun _ => StageAudit.pure p v anc (fun h _ => h.2)
  · rename_i disabled
    exact StageAudit.pure p v #[] (fun _ h => (disabled h).elim)

end SixEdge.Formula
