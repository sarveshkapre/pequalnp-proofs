import SixEdgeStageInduction
import SixEdgeConclusion
import SixEdgeJointReplay

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PlaneFour ResidualDegree Formula
open Std.Sat Std.Tactic.BVDecide

set_option maxHeartbeats 3500000
noncomputable section
variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

private theorem dirty_use_clause (A : GateSchedule P) (r : Relabelling) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (v : Values) {mute : Option Nat} {canonical : Bool}
    {stages : Array Stage} (pref : StagePrefix A r mute v canonical 5 stages)
    (j : Fin 5) (dirty : A.masks.1.getLsbD j = true) : ClauseTrue v (dirtyTerms stages j.val) := by
  obtain ⟨i,earlier,b,chosen⟩ := replay_dirty_has_reader A r least empty j dirty
  have mode : numberedMode A (replayPort A i b) = j.val+1 := by
    cases eq : replayPort A i b with
    | atom a => simp [replayInputs,eq] at chosen
    | direct t =>
      have coord : A.index t = j := by simpa [replayInputs,eq] using chosen
      simp [numberedMode,coord]
  let ms := stages[i.val]!.operandModes b
  have lit := (pref.modes i i.isLt b).2 (j.val+1) (by omega)
  have on : literalValue v (ms[j.val+1]!) = true := by
    simpa only [mode,beq_self_eq_true,List.getElem!_toArray,ms] using lit.2
  refine ⟨ms[j.val+1]!,List.mem_flatMap.mpr ⟨i.val,List.mem_filter.mpr
    ⟨List.mem_range.mpr (pref.size.symm ▸ i.isLt),decide_eq_true earlier⟩,?_⟩,on⟩
  fin_cases b <;> simp [ms]

private theorem audit_finish_slot (p : Input → Bool) (v : Values) (key : CertificateKey)
    (stages : Array Stage) (rows : List (List TopSelector × List Lit)) (j : Nat) :
    Audited p v ((key.1.1.getLsbD j = true → ClauseTrue v (dirtyTerms stages j)) ∧
      (key.1.2.getLsbD j = true → ClauseTrue v (centreTerms rows j)))
      (finishSlot key stages rows j) (fun _ => True) := by
  let D := key.1.1.getLsbD j
  let E := key.1.2.getLsbD j
  let pre := (D = true → ClauseTrue v (dirtyTerms stages j)) ∧
    (E = true → ClauseTrue v (centreTerms rows j))
  have check (condition : Bool) (rule : Rule) (ts : List Lit) (holds : pre → condition = true → ClauseTrue v ts) :
      Audited p v pre (if condition then require rule ts else pure ()) (fun _ => True) := by
    split
    · rename_i on
      exact (audit_require p v _ _).mono (fun h => holds h on) (fun _ _ z => z)
    · exact Audited.pure p v () (fun _ => trivial)
  have left := check D .dirtyUsed (dirtyTerms stages j) And.left
  have right := check E .centreMask (centreTerms rows j) And.right
  by_cases d : D = true
  · rw [ite_eq_left d] at left
    change key.1.1.getLsbD j = true at d
    simpa only [pre,D,E,finishSlot,d,ite_true] using
      (Audited.bind left (fun _ => right.mono And.left (fun _ _ z => z)))
  · change ¬key.1.1.getLsbD j = true at d
    simpa only [pre,D,E,finishSlot,ite_eq_right d] using right

attribute [local irreducible] StageAudit Audited buildStages collectOutputTests prepare program Formula.build
  stageSource physicalLeaves LeafBank replayInputs

private theorem audit_emit_physical (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (first : Fin 5) (centre : Option (Fin 13))
    (choice : ReplayChoice S (GateSchedule.rawFirst P least).masks
      (gateOrder count ((GateSchedule.rawFirst P least).index.symm first)).val centre)
    (v : Values) (leaves : Array Leaf)
    (firstEq : first.val = firstBit (GateSchedule.rawFirst P least).masks.1)
    (noneMask : centre = none ↔ (GateSchedule.rawFirst P least).masks.2 = 0)
    (firstRoute : ∀ l, centre = some l → ∃ j : Fin 5, j.val = firstBit (GateSchedule.rawFirst P least).masks.2 ∧
      replayRoute (GateSchedule.rawFirst P least) l (S.center (S.index l)) ((GateSchedule.rawFirst P least).index.symm j)) :
    let A := GateSchedule.rawFirst P least
    let p := physicalLeaves S choice.coordinates (replayInputs A choice.coordinates)
    StageAudit p v (v 1 = true ∧ LeafBank p v leaves.toList)
      (emitStages (A.masks,choice.refinement) leaves) (fun _ => True) := by
  let A := GateSchedule.rawFirst P least
  let r := choice.coordinates
  let p := physicalLeaves S r (replayInputs A r)
  unfold emitStages
  refine StageAudit.bind (audit_stages_for_output A least rfl top empty v first centre leaves firstEq noneMask choice firstRoute) ?_
  intro stages
  unfold finishOutputs
  refine StageAudit.bind ((StageAudit.of_audited (audit_physical_output_tests (P := P)
    least top empty first centre choice v leaves stages)).mono (fun h => h.2.1) (fun _ _ z => z)) ?_
  intro rows
  apply StageAudit.of_audited
  apply Audited.forM
  intro j
  refine (audit_finish_slot p v (A.masks,choice.refinement) stages rows j).mono ?_ (fun _ _ z => z)
  rintro ⟨⟨⟨_,out,pref⟩,routed⟩,mem⟩
  let i : Fin 5 := ⟨j,List.mem_range.mp mem⟩
  exact ⟨dirty_use_clause A r least empty v pref i,
    physical_centre_presence A r v stages out.firstOn out.dirty _ rows routed i⟩

/-- All kinds of requirements of a recorded formula hold for the real
    circuit. Only the mechanical validity of that formula's numbering is
    needed to assign the auxiliary variables. -/
theorem circuit_to_exact_assignment (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (two : (junk plane C).card = 2)
    (three : (exceptional plane C).card = 3) (six : (Ustar plane C).card = 6) :
    ∃ key ∈ keys, TraceValid 1 (build key).events.toList →
      ∃ assignment : Nat → Bool, (exactCNF (build key)).Sat assignment := by
  let count := charged_card two three
  obtain ⟨P⟩ := ordered_ports S least top count
  let A := GateSchedule.rawFirst P least
  obtain ⟨first,eq,centre,noneMask,firstRoute,⟨choice⟩⟩ :=
    schedule_replay_choice S least top empty two count six P A rfl
  let key : CertificateKey := (A.masks,choice.refinement)
  let r := choice.coordinates
  let p := physicalLeaves S r (replayInputs A r)
  have anchor : A.masks.2 = 0 → pt (r.inverse.point 0) ∉ leaf S (r.inverse.line 0) := by
    intro mask
    have no := noneMask.mpr mask
    subst centre
    exact choice.anchor
  refine ⟨key,choice.member,?_⟩
  intro wf
  let events := (build key).events.toList
  let v := Formula.assignment p initial events
  have one : v 1 = true := (assignment_keeps _ _ _ _ wf 1 (by decide)).trans rfl
  have audit : StageAudit p v (v 1 = true) (program key) (fun _ => True) := by
    unfold program
    exact StageAudit.bind (StageAudit.of_audited (audit_physical_prepare S least empty six r key.1.2 (replayInputs A r) anchor v))
      (fun leaves => audit_emit_physical least top empty first centre choice v leaves eq noneMask (fun l hl => by
        obtain ⟨j,hj,past,route⟩ := firstRoute l hl
        exact ⟨j,hj,route,past⟩))
  unfold StageAudit at audit
  obtain ⟨es,append,ok⟩ := audit {}
  change ((program key).run {}).2.events.toList = [] ++ es at append
  rw [List.nil_append] at append
  have same : events = es := by unfold events Formula.build; exact append
  have defs : ∀ e ∈ events, Interprets p v e := assignment_interprets p _ wf
  refine ⟨_,assignment_satisfies p _ wf ((requirements_iff_final p _ _ _ wf).mpr ?_)⟩
  intro rule terms mem
  unfold events Formula.build at defs
  have all := ok defs one
  exact all.1 (.require rule terms) (same ▸ mem)

/-- The two finite checks here are run against the same Lean-generated key:
    valid trace numbering and the LRAT contradiction of its exact CNF. -/
theorem exclude_six_edges (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (two : (junk plane C).card = 2)
    (three : (exceptional plane C).card = 3) (six : (Ustar plane C).card = 6)
    (replays : ∀ key ∈ keys, ∃ proof, caseChecks key proof = true) : False := by
  obtain ⟨key,mem,translation⟩ := circuit_to_exact_assignment S least top empty two three six
  obtain ⟨proof,passed⟩ := replays key mem
  obtain ⟨valid,checked⟩ := (caseChecks_spec key proof).mp passed
  obtain ⟨assignment,sat⟩ := translation ((traceValidBool_spec _ _).mp valid)
  exact certificate_contradicts _ proof checked assignment sat

#print axioms circuit_to_exact_assignment
#print axioms exclude_six_edges

end
end SixEdge.Plane
