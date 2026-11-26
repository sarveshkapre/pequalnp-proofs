import SixEdgeStageAudit
import SixEdgeStageSemantics
import SixEdgeFirstShape
import SixEdgeCentreExclusion

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

set_option maxHeartbeats 3500000
noncomputable section

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

attribute [local irreducible] StageAudit Audited BuildDefines buildPort portHosts
  buildStagePorts applyStageActivity appendStage buildStages combineSampleValues combineRawSupport

structure StagePrefix (A : GateSchedule P) (r : Relabelling) (mute : Option Nat)
    (v : Values) (canonical : Bool) (n : Nat) (stages : Array Stage) : Prop where
  size : stages.size = n
  dirty : ∀ j : Fin 5, j.val < n → stages[j.val]!.dirty = dirtyAt count (A.index.symm j)
  raw : ∀ j : Fin 5, j.val < n → ArrayDenotes v 26 (scheduledRaw A r j) stages[j.val]!.raw
  values : ∀ j : Fin 5, j.val < n →
    ArrayDenotes v samples.size (stageValues A r mute n j.val) stages[j.val]!.values
  ancestors : canonical = true → ∀ j : Fin 5, j.val < n →
    ArrayDenotes v 5 (stageSource A j) stages[j.val]!.ancestors
  modes : ∀ j : Fin 5, j.val < n → ∀ b : Fin 2,
    ArrayDenotes v (j.val+1) (fun k => k == numberedMode A (replayPort A j b))
      (stages[j.val]!.operandModes b).toArray

private theorem rawAtPrior {A : GateSchedule P} {r : Relabelling} {mute : Option Nat}
    {v : Values} {canonical : Bool} {i : Fin 5} {stages : Array Stage}
    (prefixOK : StagePrefix A r mute v canonical i.val stages) (j : Nat) (bound : j < stages.size) :
    ArrayDenotes v 26 (scheduledRaw A r (Fin.ofNat 5 j)) stages[j]!.raw := by
  have lt : j < i.val := prefixOK.size ▸ bound
  let t : Fin 5 := ⟨j,lt.trans i.isLt⟩
  have eq : Fin.ofNat 5 j = t := Fin.ext (Nat.mod_eq_of_lt t.isLt)
  rw [eq]
  exact prefixOK.raw t lt

private theorem prefix_push (A : GateSchedule P) (r : Relabelling) (mute : Option Nat)
    (v : Values) (i : Fin 5) (stages : Array Stage) (s : Stage)
    {canonical : Bool} (old : StagePrefix A r mute v canonical i.val stages)
    (kind : s.dirty = dirtyAt count (A.index.symm i))
    (raw : ArrayDenotes v 26 (scheduledRaw A r i) s.raw)
    (value : ArrayDenotes v samples.size
      (fun k => if mute = some i.val then false else beforeStageActivity A r mute i k) s.values)
    (anc : canonical = true → ArrayDenotes v 5 (stageSource A i) s.ancestors)
    (modes : ∀ b : Fin 2, ArrayDenotes v (i.val+1) (fun k => k == numberedMode A (replayPort A i b))
      (s.operandModes b).toArray) :
    StagePrefix A r mute v canonical (i.val+1) (stages.push s) := by
  have len : (stages.push s).size = i.val+1 := by rw [Array.size_push,old.size]
  have earlier (j : Nat) (lt : j < i.val) : (stages.push s)[j]! = stages[j]! := by
    have b : j < stages.size := old.size.symm ▸ lt
    rw [getElem!_pos (stages.push s) j (len.symm ▸ Nat.lt_succ_of_lt lt),
      getElem!_pos stages j b, Array.getElem_push_lt b]
  have atLast : (stages.push s)[i.val]! = s := by
    rw [← old.size]
    simp
  have splitIndex (j : Fin 5) (lt : j.val < i.val+1) : j.val < i.val ∨ j = i := by
    by_cases less : j.val < i.val
    · exact Or.inl less
    · exact Or.inr (Fin.ext (by omega))
  have oldValue (j : Fin 5) (lt : j.val < i.val) :
      stageValues A r mute (i.val+1) j.val = stageValues A r mute i.val j.val := by
    funext k
    unfold stageValues
    rw [evalSchedule,Function.update_of_ne (Nat.ne_of_lt lt)]
  have newValue : stageValues A r mute (i.val+1) i.val =
      (fun k => if mute = some i.val then false else beforeStageActivity A r mute i k) := by
    funext k
    unfold stageValues
    rw [evalSchedule,Function.update_self]; rfl
  refine ⟨len,?_,?_,?_,?_,?_⟩
  · intro j lt
    rcases splitIndex j lt with less | rfl
    · rw [earlier _ less]
      exact old.dirty j less
    · rwa [atLast]
  · intro j lt
    rcases splitIndex j lt with less | rfl
    · rw [earlier _ less]
      exact old.raw j less
    · rwa [atLast]
  · intro j lt
    rcases splitIndex j lt with less | eq
    · rw [earlier _ less,oldValue j less]
      exact old.values j less
    · subst j
      rwa [atLast,newValue]

  · intro enabled j lt
    rcases splitIndex j lt with less | rfl
    · rw [earlier _ less]; exact old.ancestors enabled j less
    · rw [atLast]; exact anc enabled
  · intro j lt
    rcases splitIndex j lt with less | rfl
    · rw [earlier _ less]; exact old.modes j less
    · rw [atLast]; exact modes

private def portValues (A : GateSchedule P) (r : Relabelling) (mute : Option Nat) (i : Fin 5)
    (b : Fin 2) (k : Nat) : Bool :=
  replayPortBit A i b (sampleInput k ∘ r.vertex) (fun j => stageValues A r mute i.val j k)

private def operandReady (A : GateSchedule P) (r : Relabelling) (mute : Option Nat)
    (v : Values) (canonical : Bool) (i : Fin 5) (b : Fin 2) (port : Port) : Prop :=
  ArrayDenotes v (i.val+1) (fun j => j == numberedMode A (replayPort A i b)) port.modes.toArray ∧
  ArrayDenotes v 26 (scheduledPortRaw A r i b) port.raw ∧
  ArrayDenotes v samples.size (portValues A r mute i b) port.values ∧
  (canonical = true → ArrayDenotes v 5 (portSource A i b) port.ancestors)

private def stageReady (A : GateSchedule P) (r : Relabelling) (mute : Option Nat) (v : Values)
    (canonical : Bool) (i : Fin 5) (leaves : Array Leaf) (stages : Array Stage) : Prop :=
  v 1 = true ∧ LeafBank (physicalLeaves S r (replayInputs A r)) v leaves.toList ∧
    StagePrefix A r mute v canonical i.val stages

private theorem audit_stage_ports (A : GateSchedule P) (r : Relabelling) (ao : IsAO2 26 C)
    (mute : Option Nat) (v : Values) (i : Fin 5) (stages : Array Stage) (leaves : Array Leaf)
    (canonical : Bool) :
    StageAudit (physicalLeaves S r (replayInputs A r)) v (stageReady A r mute v canonical i leaves stages)
      (buildStagePorts stages (portHosts leaves) i.val canonical)
      (fun ab => operandReady A r mute v canonical i 0 ab.1 ∧ operandReady A r mute v canonical i 1 ab.2) := by
  let p := physicalLeaves S r (replayInputs A r)
  let ready := stageReady A r mute v canonical i leaves stages
  have operand (b : Fin 2) : StageAudit p v ready
      (buildPort stages (portHosts leaves) i.val b.val canonical) (operandReady A r mute v canonical i b) := by
    refine StageAudit.with_defines ((audit_scheduled_buildPort A r ao v i b stages leaves canonical).mono
      (fun h : ready => ⟨h.1,h.2.2.size,h.2.1,rawAtPrior h.2.2⟩) (fun _ _ z => z)) ?_
    refine (buildPort_with_sources A r ao v i b stages (portHosts leaves) canonical
      (stageValues A r mute i.val)).mono ?_ (fun _ _ z => z)
    intro h
    refine ⟨h.1,h.2.2.size,fun j hj => h.2.2.dirty j (h.2.2.size ▸ hj),rawAtPrior h.2.2,?_,?_⟩
    · intro j hj
      have lt : j < i.val := h.2.2.size ▸ hj
      exact h.2.2.values ⟨j,lt.trans i.isLt⟩ lt
    · intro enabled j hj
      have lt : j < i.val := h.2.2.size ▸ hj
      let t : Fin 5 := ⟨j,lt.trans i.isLt⟩
      have eq : Fin.ofNat 5 j = t := Fin.ext (Nat.mod_eq_of_lt t.isLt)
      rw [eq]; exact h.2.2.ancestors enabled t lt
  unfold buildStagePorts
  refine StageAudit.bind (operand 0) ?_
  intro a
  refine StageAudit.bind ((operand 1).mono And.left (fun _ _ z => z)) ?_
  intro b
  have reads {ls : List Lit} {bit : Nat → Bool} (ok : ArrayDenotes v (i.val+1) bit ls.toArray)
      (j : Nat) (bound : j < ls.length) : Denotes v (bit j) ls[j]! := by
    have len : ls.length = i.val+1 := ok.1
    simpa only [List.getElem!_toArray] using ok.2 j (len ▸ bound)
  refine StageAudit.thenKeep ((StageAudit.of_audited (audit_port_order p v a.modes b.modes
    (numberedMode A (replayPort A i 0)) (numberedMode A (replayPort A i 1)))).mono
      (fun h => ⟨replay_port_sorted A i,reads h.1.2.1,reads h.2.1⟩) (fun _ _ z => z)) ?_
  intro _
  exact StageAudit.pure p v (a,b) (fun h => ⟨h.1.2,h.2⟩)

private theorem audit_stage_activity (A : GateSchedule P) (r : Relabelling) (v : Values)
    (refinement : Refinement) (first i : Fin 5) (leaves : Array Leaf) (values : Array Lit)
    (firstEq : first.val = firstBit A.masks.1) (firstOn : A.masks.1.getLsbD first = true)
    (activity : ∀ active, (mode refinement).1 = some active →
      FirstActivity active A.masks.2 (keptInput (physicalLeaves S r (replayInputs A r)))
        (beforeStageActivity A r (replayMute refinement first) first)) :
    let p := physicalLeaves S r (replayInputs A r)
    let mute := replayMute refinement first
    let awake := beforeStageActivity A r mute i
    StageAudit p v (v 1 = true ∧ LeafBank p v leaves.toList ∧ ArrayDenotes v samples.size awake values)
      (applyStageActivity (A.masks,refinement) leaves i.val values)
      (ArrayDenotes v samples.size (fun k => if mute = some i.val then false else awake k)) := by
  let p := physicalLeaves S r (replayInputs A r)
  let mute := replayMute refinement first
  let awake := beforeStageActivity A r mute i
  have atStage : activityAt (A.masks,refinement) i.val =
      if i = first then (mode refinement).1 else none := by
    by_cases hi : i = first
    · subst i
      simp [activityAt,← firstEq,firstOn]
    · have ne : i.val ≠ first.val := fun h => hi (Fin.ext h)
      simp [activityAt,← firstEq,ne,hi]
  dsimp only
  unfold applyStageActivity
  rw [atStage]
  by_cases here : i = first
  · subst i
    rw [ite_eq_left rfl]
    cases selected : (mode refinement).1 with
    | none =>
      have noMute : mute = none := by simp [mute,replayMute,selected]
      refine StageAudit.pure p v values (fun h => ?_)
      change ArrayDenotes v samples.size
        (fun k => if mute = some first.val then false else awake k) values
      simpa only [noMute,reduceCtorEq,ite_false] using h.2.2
    | some active =>
      refine (StageAudit.of_audited (audit_first_activity p v A.masks.2 active
        (retainedInputs leaves) values (keptInput p) awake)).mono ?_ ?_
      · intro h
        exact ⟨h.1,retained_inputs_denote p v h.1 leaves h.2.1,h.2.2,activity active selected⟩
      · intro _ out checked
        cases active <;> simpa [replayMute,selected,awake,mute] using checked
  · rw [ite_eq_right here]
    have ne : mute ≠ some i.val := by
      unfold mute replayMute
      split
      · intro eq
        exact here (Fin.ext (Option.some.inj eq).symm)
      · simp
    refine StageAudit.pure p v values (fun h => ?_)
    change ArrayDenotes v samples.size (fun k => if mute = some i.val then false else awake k) values
    simpa only [ne,ite_false] using h.2.2

private theorem audit_push_uses (p : Input → Bool) (v : Values) :
    StageAudit p v True (modify fun s : BuildState => {s with uses := s.uses.push #[]})
      (fun _ => True) := by
  unfold StageAudit
  exact fun _ => ⟨[],by simp,fun _ _ => ⟨by simp,trivial⟩⟩

private theorem audit_append_stage (A : GateSchedule P) (r : Relabelling) (ao : IsAO2 26 C)
    (v : Values) (refinement : Refinement) (first i : Fin 5) (leaves : Array Leaf) (stages : Array Stage)
    (firstEq : first.val = firstBit A.masks.1) (firstOn : A.masks.1.getLsbD first = true)
    (sources : ∀ j : Fin 5, A.masks.1.getLsbD j = false → firstBit A.masks.1 < j.val → ∃ q < 5, stageSource A j q = true)
    (centreOff : ∀ j : Fin 5, (mode refinement).2.1 = 0 → A.masks.2.getLsbD j = true → stageSource A j 0 = false)
    (shape : FirstShapeValid (A.masks.1.getLsbD i) i.val (mode refinement).2.1
      (scheduledPortRaw A r i 0) (scheduledPortRaw A r i 1))
    (activity : ∀ active, (mode refinement).1 = some active →
      FirstActivity active A.masks.2 (keptInput (physicalLeaves S r (replayInputs A r)))
        (beforeStageActivity A r (replayMute refinement first) first)) :
    StageAudit (physicalLeaves S r (replayInputs A r)) v
      (stageReady A r (replayMute refinement first) v (mode refinement).2.2 i leaves stages)
      (appendStage (A.masks,refinement) leaves stages i.val)
      (StagePrefix A r (replayMute refinement first) v (mode refinement).2.2 (i.val+1)) := by
  let p := physicalLeaves S r (replayInputs A r)
  let mute := replayMute refinement first
  let dirty := A.masks.1.getLsbD i
  let awake := beforeStageActivity A r mute i
  unfold appendStage
  refine StageAudit.bind (audit_stage_ports A r ao mute v i stages leaves _) ?_
  intro ports
  let a := ports.1
  let b := ports.2
  have gate := audit_scheduled_gate A r v i a.values b.values (fun k j => stageValues A r mute i.val j k)
  refine StageAudit.bind ((StageAudit.of_audited gate).mono
    (fun h => ⟨h.1.1,fun k hk => ⟨h.2.1.2.2.1.2 k hk,h.2.2.2.2.1.2 k hk⟩⟩)
    (fun _ _ z => z)) ?_
  intro values
  have raw := audit_combine_raw p v dirty a.raw b.raw (scheduledPortRaw A r i 0) (scheduledPortRaw A r i 1)
  refine StageAudit.bind ((StageAudit.of_audited raw).mono (w := ArrayDenotes v 26 (scheduledRaw A r i))
    (fun h => ⟨h.1.1.1,fun j hj => ⟨h.1.2.1.2.1.2 j hj,h.1.2.2.2.1.2 j hj⟩⟩) ?_) ?_
  · intro _ lits h
    exact (show ArrayDenotes v 26 (scheduledRaw A r i) lits from
      ⟨h.1,fun j hj => ⟨(h.2 j hj).1,(h.2 j hj).2.trans (scheduled_raw_combine A ao r i j)⟩⟩)
  intro support
  have firstShape := audit_first_shape p v dirty i.val (mode refinement).2.1
    a.raw b.raw (scheduledPortRaw A r i 0) (scheduledPortRaw A r i 1)
  refine StageAudit.thenKeep ((StageAudit.of_audited firstShape).mono
    (fun h => ⟨shape,h.1.1.2.1.2.1,h.1.1.2.2.2.1⟩) (fun _ _ z => z)) ?_
  intro _
  refine StageAudit.bind ((audit_stage_activity A r v refinement first i leaves values firstEq firstOn activity).mono
    (fun h => ⟨h.1.1.1.1,h.1.1.1.2.1,h.1.2⟩) (fun _ _ z => z)) ?_
  intro after
  have orderAudit := audit_stage_ancestor_order p v (A.masks,refinement) i.val a b
    (portSource A i 0) (portSource A i 1) (stageSource A i) (stage_source_combine A ao i)
    (fun _ off later => sources i off later) (centreOff i)
  refine StageAudit.bind (orderAudit.mono
    (fun h => ⟨h.1.1.1.1.1,h.1.1.1.2.1.2.2.2,h.1.1.1.2.2.2.2.2⟩) (fun _ _ z => z)) ?_
  intro anc
  refine StageAudit.thenKeep ((audit_push_uses p v).mono (fun _ => trivial) (fun _ _ z => z)) ?_
  intro _
  refine StageAudit.pure p v (stages.push ⟨dirty,support,after,anc,fun k => if k = 0 then a.modes else b.modes⟩) ?_
  intro h
  apply prefix_push A r mute v i stages _ h.1.1.1.1.1.2.2 (scheduled_dirty_bit A i) h.1.1.2 h.1.2 h.2
  intro k
  fin_cases k
  · exact h.1.1.1.1.2.1.1
  · exact h.1.1.1.1.2.2.1

private theorem audit_stage_range (A : GateSchedule P) (r : Relabelling) (ao : IsAO2 26 C)
    (v : Values) (refinement : Refinement) (first : Fin 5) (leaves : Array Leaf)
    (firstEq : first.val = firstBit A.masks.1) (firstOn : A.masks.1.getLsbD first = true)
    (sources : ∀ j : Fin 5, A.masks.1.getLsbD j = false → firstBit A.masks.1 < j.val → ∃ q < 5, stageSource A j q = true)
    (centreOff : ∀ j : Fin 5, (mode refinement).2.1 = 0 → A.masks.2.getLsbD j = true → stageSource A j 0 = false)
    (shape : ∀ i : Fin 5, FirstShapeValid (A.masks.1.getLsbD i) i.val (mode refinement).2.1
      (scheduledPortRaw A r i 0) (scheduledPortRaw A r i 1))
    (activity : ∀ active, (mode refinement).1 = some active →
      FirstActivity active A.masks.2 (keptInput (physicalLeaves S r (replayInputs A r)))
        (beforeStageActivity A r (replayMute refinement first) first))
    (start n : Nat) (bound : start+n ≤ 5) (stages : Array Stage) :
    let p := physicalLeaves S r (replayInputs A r)
    let mute := replayMute refinement first
    StageAudit p v (v 1 = true ∧ LeafBank p v leaves.toList ∧ StagePrefix A r mute v (mode refinement).2.2 start stages)
      ((List.range' start n).foldlM (appendStage (A.masks,refinement) leaves) stages)
      (StagePrefix A r mute v (mode refinement).2.2 (start+n)) := by
  let p := physicalLeaves S r (replayInputs A r)
  let mute := replayMute refinement first
  induction n generalizing start stages with
  | zero =>
    exact StageAudit.pure p v stages (fun h => h.2.2)
  | succ n ih =>
    rw [List.range'_succ,List.foldlM_cons]
    let i : Fin 5 := ⟨start,by omega⟩
    refine StageAudit.bind (audit_append_stage A r ao v refinement first i leaves stages
      firstEq firstOn sources centreOff (shape i) activity) ?_
    intro next
    have eq : start+1+n = start+(n+1) := by omega
    exact (ih (start+1) (by omega) next).mono (fun h => ⟨h.1.1,h.1.2.1,h.2⟩)
      (fun _ _ z => eq ▸ z)

private theorem recorded_first_dirty (A : GateSchedule P) (refinement : Refinement)
    (mem : (A.masks,refinement) ∈ keys) :
    A.masks.1.getLsbD (firstBit A.masks.1) = true := by
  apply fun h => (first_dirty_facts A.masks h).2.1
  obtain ⟨key,hk,inside⟩ := List.mem_flatMap.mp mem
  obtain ⟨_,_,eq⟩ := List.mem_map.mp inside
  have same : key = A.masks := congrArg Prod.fst eq
  rwa [← same]

/-- The exact five-stage builder checks its port, gate, geometry, activity and ancestor-order clauses
    and returns the schedule's raw support and sample values after stage five. -/
theorem audit_buildStages (A : GateSchedule P) (least : IsLeastAO plane C)
    (order : A = GateSchedule.rawFirst P least) (top : TopForm plane C) (empty : centreless plane C = ∅) (v : Values)
    (first : Fin 5) (centre : Option (Fin 13)) (leaves : Array Leaf)
    (firstEq : first.val = firstBit A.masks.1) (noneMask : centre = none ↔ A.masks.2 = 0)
    (choice : ReplayChoice S A.masks (gateOrder count (A.index.symm first)).val centre) :
    let r := choice.coordinates
    let p := physicalLeaves S r (replayInputs A r)
    StageAudit p v (v 1 = true ∧ LeafBank p v leaves.toList)
      (buildStages (A.masks,choice.refinement) leaves)
      (StagePrefix A r (replayMute choice.refinement first) v (mode choice.refinement).2.2 5) := by
  let r := choice.coordinates
  have on : A.masks.1.getLsbD first = true := by
    rw [firstEq]
    exact recorded_first_dirty A choice.refinement choice.member
  unfold buildStages
  apply (audit_stage_range A r least.1 v choice.refinement first leaves firstEq on
    (fun i off later => by
      subst A
      obtain ⟨q,_,_,bit⟩ := canonical_order_witness least i (firstEq ▸ on) off later
      exact ⟨q.val,q.isLt,bit⟩)
    (fun i geo used => by subst A; exact physical_centre_exclusion least top empty first i centre choice firstEq geo used)
    (fun i => physical_first_shape A first i centre firstEq choice)
    (physical_first_activity A least.1 first centre noneMask choice) 0 5 (by decide) #[]).mono
  · intro h
    refine ⟨h.1,h.2,rfl,?_,?_,?_,?_,?_⟩ <;> intros <;> omega
  · exact fun _ _ z => z

theorem audit_stages_for_output (A : GateSchedule P) (least : IsLeastAO plane C)
    (order : A = GateSchedule.rawFirst P least) (top : TopForm plane C) (empty : centreless plane C = ∅) (v : Values)
    (first : Fin 5) (centre : Option (Fin 13)) (leaves : Array Leaf)
    (firstEq : first.val = firstBit A.masks.1) (noneMask : centre = none ↔ A.masks.2 = 0)
    (choice : ReplayChoice S A.masks (gateOrder count (A.index.symm first)).val centre)
    (firstRoute : ∀ l, centre = some l → ∃ j : Fin 5, j.val = firstBit A.masks.2 ∧
      replayRoute A l (S.center (S.index l)) (A.index.symm j)) :
    let r := choice.coordinates
    let p := physicalLeaves S r (replayInputs A r)
    StageAudit p v (v 1 = true ∧ LeafBank p v leaves.toList)
      (buildStages (A.masks,choice.refinement) leaves)
      (fun stages => ScheduledOutput A r (replayMute choice.refinement first) v leaves stages ∧
        StagePrefix A r (replayMute choice.refinement first) v (mode choice.refinement).2.2 5 stages) := by
  refine (audit_buildStages A least order top empty v first centre leaves firstEq noneMask choice).mono id ?_
  rintro ⟨one,bank⟩ stages checked
  refine ⟨?_,checked⟩
  exact ⟨one,bank,recorded_first_dirty A choice.refinement choice.member,
    fun j => checked.dirty j j.isLt, fun j k hk => (checked.values j j.isLt).2 k hk,
    fun j => checked.raw j j.isLt, physical_centre_anchor A choice.coordinates centre
      choice.anchor noneMask firstRoute⟩

/-- A circuit in the six-edge family selects one of the replayed keys. With
    its physical selectors, every order clause in preparation and all five
    stages is true for any valuation interpreting the emitted definitions. -/
theorem circuit_ancestor_order (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (two : (junk plane C).card = 2)
    (three : (exceptional plane C).card = 3) (six : (Ustar plane C).card = 6) :
    ∃ key ∈ keys, ∃ p : Input → Bool, ∀ v : Values,
      let events := (((prepare key.1.2 >>= buildStages key).run {}).2.events).toList
      v 1 = true → (∀ e ∈ events, Interprets p v e) →
        ∀ ts, Event.require .canonicalOrder ts ∈ events → ClauseTrue v ts := by
  let count := charged_card two three
  obtain ⟨P⟩ := ordered_ports S least top count
  let A := GateSchedule.rawFirst P least
  obtain ⟨first,hfirst,centre,noneMask,_,⟨choice⟩⟩ :=
    schedule_replay_choice S least top empty two count six P A rfl
  let r := choice.coordinates
  let key : CertificateKey := (A.masks,choice.refinement)
  let p := physicalLeaves S r (replayInputs A r)
  have anchor : A.masks.2 = 0 → pt (r.inverse.point 0) ∉ leaf S (r.inverse.line 0) := by
    intro mask
    have eq := noneMask.mpr mask
    subst centre
    exact choice.anchor
  refine ⟨key,choice.member,p,?_⟩
  intro v
  let pre := audit_physical_prepare S least empty six r key.1.2 (replayInputs A r) anchor v
  have checked : StageAudit p v (v 1 = true) (prepare key.1.2 >>= buildStages key) (fun _ => True) :=
    StageAudit.bind (StageAudit.of_audited pre) (fun leaves =>
      (audit_buildStages A least rfl top empty v first centre leaves hfirst noneMask choice).mono id (fun _ _ _ => trivial))
  intro events one interprets ts member
  unfold StageAudit at checked
  obtain ⟨es,append,ok⟩ := checked {}
  change events = [] ++ es at append
  rw [List.nil_append] at append
  exact (ok interprets one).1 (.require .canonicalOrder ts) (append ▸ member)

#print axioms circuit_ancestor_order
#print axioms audit_buildStages
#print axioms audit_stages_for_output

end
end SixEdge.Plane
