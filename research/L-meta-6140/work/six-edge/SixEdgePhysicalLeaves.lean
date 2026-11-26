import SixEdgeLeafProof
import SixEdgeRefinement

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PlaneFour ResidualDegree Formula

variable {C : Circuit}

attribute [local irreducible] emitStages

-- Other primary variables may use the subsequently selected schedule.
noncomputable def physicalLeaves (S : Stars C) (r : Relabelling) (other : Input → Bool) : Input → Bool := by
  classical
  exact fun tag => match tag with
    | .leaf l p => decide (pt (r.inverse.point (Fin.ofNat 13 p)) ∈
        leaf S (r.inverse.line (Fin.ofNat 13 (l-13))))
    | tag => other tag

private theorem line_embed (r : Relabelling) (l : Fin 13) : r.line (r.inverse.line l) = l :=
  r.inverse.lineInjective (by rw [line_inverse])

theorem physicalLeaves_bit (S : Stars C) (r : Relabelling) (other : Input → Bool) (p l : Fin 13) :
    physicalLeaves S r other (.leaf (13+l.val) p.val) = true ↔
      pt (r.inverse.point p) ∈ leaf S (r.inverse.line l) := by
  classical
  simp [physicalLeaves]

theorem in_neighbours : ∀ p l : Fin 13,
    p.val ∈ neighbours (13+l.val) ↔ incident p l := by decide +kernel

private theorem coordinate_rows :
    edgeRows.toList.map (fun (p,l) => (Fin.ofNat 13 p, Fin.ofNat 13 (l-13))) = edgePairs := by
  decide +kernel

private theorem relabelled_count (S : Stars C) (r : Relabelling) (other : Input → Bool) :
    (MissingFlags (physicalLeaves S r other)).count true = (residualPairs S).card := by
  classical
  let missing (e : Fin 13 × Fin 13) := decide (pt (r.inverse.point e.1) ∉ leaf S (r.inverse.line e.2))
  have countEquiv : MissingFlags (physicalLeaves S r other) = edgePairs.map missing := by
    rw [← coordinate_rows, List.map_map]
    apply List.map_congr_left
    rintro ⟨p,l⟩ _
    simp [physicalLeaves, missing, decide_not]
  rw [countEquiv, List.count_eq_length_filter, List.filter_map]
  simp only [List.length_map, Function.comp_def, beq_true]
  have distinct := edge_pairs_exact.2.filter missing
  rw [← List.toFinset_card_of_nodup distinct]
  apply Finset.card_bij (fun e _ => (r.inverse.point e.1, r.inverse.line e.2))
  · rintro ⟨p,l⟩ he
    have h : (p,l) ∈ positives ∧ missing (p,l) = true := by simpa [edge_pairs_exact.1] using he
    have spot : incident p l := (Finset.mem_filter.mp h.1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(r.inverse.incidence _ _).mpr spot⟩,
      of_decide_eq_true h.2⟩
  · intro a _ b _ eq
    exact Prod.ext (r.inverse.pointInjective (congrArg Prod.fst eq)) (r.inverse.lineInjective (congrArg Prod.snd eq))
  · rintro ⟨p,l⟩ he
    obtain ⟨inc,absent⟩ := Finset.mem_filter.mp he
    have hInc : incident (r.point p) (r.line l) := (r.incidence p l).mpr (Finset.mem_filter.mp inc).2
    refine ⟨(r.point p,r.line l), ?_, by simp [point_inverse, line_inverse]⟩
    have member : (r.point p,r.line l) ∈ positives := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hInc⟩
    have absent' : missing (r.point p,r.line l) = true := by simp [missing,point_inverse,line_inverse,absent]
    simpa [edge_pairs_exact.1] using And.intro member absent'

private theorem all_leaves_live (S : Stars C) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (r : Relabelling) (other : Input → Bool) :
    ∀ l ∈ List.range' 13 13, ∃ p ∈ neighbours l, physicalLeaves S r other (.leaf l p) = true := by
  intro l mem
  have bounds := List.mem_range'.mp mem
  let c : Fin 13 := ⟨l-13,by omega⟩
  have label : 13+c.val = l := by change 13+(l-13) = l; omega
  obtain ⟨v,hv⟩ := leaf_nonempty S empty (r.inverse.line c)
  obtain ⟨p,rfl⟩ := leaf_point S least.1 hv
  have edge := (adj_coordinates p (r.inverse.line c)).mpr (leaf_neighbor S least.1 hv)
  have inc := (r.incidence p (r.inverse.line c)).mpr edge
  rw [line_embed] at inc
  refine ⟨(r.point p).val, ?_, ?_⟩
  · rw [← label]
    exact in_neighbours _ _ |>.mpr inc
  · rw [← label]
    apply (physicalLeaves_bit S r other _ _).mpr
    rwa [point_inverse]

/-- A real circuit supplies all the leaf and count inputs, with the required
    anchor whenever the selected mask has no centre routes. -/
theorem audit_physical_prepare (S : Stars C) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (six : (Ustar plane C).card = 6)
    (r : Relabelling) (extra : BitVec 5) (other : Input → Bool)
    (anchor : extra = 0 → pt (r.inverse.point 0) ∉ leaf S (r.inverse.line 0))
    (v : Values) : Audited (physicalLeaves S r other) v (v 1 = true)
      (prepare extra) (fun leaves => LeafBank (physicalLeaves S r other) v leaves.toList) := by
  refine (audit_prepare _ _ _).mono (fun one => ⟨one,all_leaves_live S least empty r other,?_,?_⟩)
    (fun _ _ h => h)
  · rw [relabelled_count, residual_card S least.1, six]
  · intro eq
    apply Bool.eq_false_iff.mpr
    exact fun fire => anchor eq ((physicalLeaves_bit S r other 0 0).mp fire)

/-- Discharge the preparation clauses with the actual circuit for any final
    interpretation whose trace contains the encoder's preparation prefix. -/
theorem physical_preparation_clauses (S : Stars C) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (six : (Ustar plane C).card = 6)
    (r : Relabelling) (extra : BitVec 5) (other : Input → Bool)
    (anchor : extra = 0 → pt (r.inverse.point 0) ∉ leaf S (r.inverse.line 0))
    (final : BuildState) (wf : TraceValid 1 final.events.toList)
    (contains : ∀ e ∈ ((prepare extra).run {}).2.events.toList, e ∈ final.events.toList) :
    let v := assignment (physicalLeaves S r other) initial final.events.toList
    ∀ e ∈ ((prepare extra).run {}).2.events.toList, Meets v e := by
  let v := assignment (physicalLeaves S r other) initial final.events.toList
  have one : v 1 = true := (assignment_keeps _ _ _ _ wf 1 (by decide)).trans rfl
  obtain ⟨es, appended, audited⟩ := audit_physical_prepare S least empty six r extra other anchor v {}
  have eq : ((prepare extra).run {}).2.events.toList = es := appended
  have defs e (he : e ∈ es) : Interprets (physicalLeaves S r other) v e :=
    assignment_interprets _ _ wf e (contains e (eq.symm ▸ he))
  exact eq.symm ▸ (audited defs one).1

set_option maxHeartbeats 2500000 in
/-- Only the clauses emitted after preparation are needed from the caller.
    The physical leaf data supplies the first part of the actual replay trace. -/
theorem exact_assignment_from_stages (S : Stars C) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (six : (Ustar plane C).card = 6)
    (key : CertificateKey) (r : Relabelling) (other : Input → Bool)
    (anchor : key.1.2 = 0 → pt (r.inverse.point 0) ∉ leaf S (r.inverse.line 0))
    (wf : TraceValid 1 (build key).events.toList)
    (remaining : ∀ (v : Values) (leaves : Array Leaf),
      Audited (physicalLeaves S r other) v (v 1 = true ∧ LeafBank (physicalLeaves S r other) v leaves.toList)
        (emitStages key leaves) (fun _ => True)) :
    ∃ v : Values, (exactCNF (build key)).Sat v := by
  let primary := physicalLeaves S r other
  have programAudit (v : Values) : Audited primary v (v 1 = true) (program key) (fun _ => True) := by
    exact Audited.bind (primary := primary) (v := v) (m := prepare key.1.2) (f := emitStages key)
      (p := fun a => LeafBank primary v a.toList)
      (audit_physical_prepare S least empty six r key.1.2 other anchor v) (remaining v)
  let values := fun i => assignment primary initial (build key).events.toList (i+1)
  refine ⟨values, assignment_satisfies primary _ wf ?_⟩
  exact audit_program (program key)
    (fun v one => (programAudit v).mono (fun _ : True => one) (fun _ _ h => h)) trivial wf

/-- Each physical circuit in scope selects a recorded key and discharges the
    complete initial portion of that key's exact encoder. -/
theorem circuit_prepares_recorded_key (S : Stars C) (least : IsLeastAO plane C)
    (top : TopForm plane C) (empty : centreless plane C = ∅)
    (two : (junk plane C).card = 2) (three : (exceptional plane C).card = 3)
    (six : (Ustar plane C).card = 6) (other : Input → Bool) :
    ∃ (key : CertificateKey), key ∈ keys ∧ ∃ r : Relabelling,
      ∀ v : Values, Audited (physicalLeaves S r other) v (v 1 = true) (prepare key.1.2)
        (fun leaves => LeafBank (physicalLeaves S r other) v leaves.toList) := by
  let count := charged_card two three
  obtain ⟨P⟩ := ordered_ports S least top count
  let A : GateSchedule P := GateSchedule.rawFirst P least
  obtain ⟨_,_,centre,noneMask,_,⟨choice⟩⟩ := schedule_replay_choice S least top empty two count six P A rfl
  refine ⟨(A.masks,choice.refinement),choice.member,choice.coordinates,?_⟩
  have anchor : A.masks.2 = 0 → pt (choice.coordinates.inverse.point 0) ∉ leaf S (choice.coordinates.inverse.line 0) := by
    intro noCentre
    have eq := noneMask.mpr noCentre
    subst centre
    exact choice.anchor
  exact audit_physical_prepare S least empty six choice.coordinates A.masks.2 other anchor

theorem circuit_satisfies_preparation (S : Stars C) (least : IsLeastAO plane C)
    (top : TopForm plane C) (empty : centreless plane C = ∅)
    (two : (junk plane C).card = 2) (three : (exceptional plane C).card = 3)
    (six : (Ustar plane C).card = 6) (other : Input → Bool) :
    ∃ (key : CertificateKey), key ∈ keys ∧ ∃ r : Relabelling,
      Requirements (physicalLeaves S r other) initial ((prepare key.1.2).run {}).2.events.toList := by
  obtain ⟨key,known,r,verified⟩ := circuit_prepares_recorded_key S least top empty two three six other
  refine ⟨key,known,r,?_⟩
  exact audit_program (p := fun _ : Array Leaf => True) (prepare key.1.2)
    (fun v one => (verified v).mono (fun _ : True => one) (fun _ _ _ => trivial)) trivial (preparation_trace_valid _)

#print axioms audit_physical_prepare
#print axioms physical_preparation_clauses
#print axioms exact_assignment_from_stages
#print axioms circuit_prepares_recorded_key
#print axioms circuit_satisfies_preparation

end SixEdge.Plane
