import SixEdgeReplayTests
import SixEdgePhysicalLeaves
import SixEdgeOutputProof

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

set_option maxHeartbeats 2500000

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

theorem mode_assignment (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (b : Fin 2)
    (j : Nat) (bound : j ≤ i.val) :
    replayInputs A r (modeInput i.val b.val j) = (j == numberedMode A (replayPort A i b)) := by
  have gi : Fin.ofNat 5 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have bi : Fin.ofNat 2 b.val = b := Fin.ext (Nat.mod_eq_of_lt b.isLt)
  cases j with
  | zero => cases h : replayPort A i b <;> simp [modeInput,replayInputs,h,numberedMode]
  | succ j =>
    have hj : j < 5 := by have := i.isLt; omega
    cases h : replayPort A i b with
    | atom a => simp [modeInput,replayInputs,h,numberedMode]
    | direct q =>
      simp only [modeInput,replayInputs,gi,bi,h,numberedMode]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,Nat.succ.injEq]
      constructor
      · intro eq
        have val := congrArg Fin.val eq
        change (A.index q).val = j % 5 at val
        rw [Nat.mod_eq_of_lt hj] at val
        exact val.symm
      · intro eq
        apply Fin.ext
        change (A.index q).val = j % 5
        rw [Nat.mod_eq_of_lt hj, eq]

theorem audit_scheduled_port_order (A : GateSchedule P) (r : Relabelling) (v : Values) (i : Fin 5)
    (a b : List Lit) :
    let primary := physicalLeaves S r (replayInputs A r)
    Audited primary v
      (a.length = i.val+1 ∧ b.length = i.val+1 ∧
        (∀ j < a.length, Denotes v (primary (modeInput i.val 0 j)) a[j]!) ∧
        (∀ j < b.length, Denotes v (primary (modeInput i.val 1 j)) b[j]!))
      (orderPortModes a b) (fun _ => True) := by
  dsimp only
  apply (audit_port_order _ v a b (numberedMode A (replayPort A i 0)) (numberedMode A (replayPort A i 1))).mono
    ?_ (fun _ _ h => h)
  rintro ⟨la,lb,ma,mb⟩
  refine ⟨replay_port_sorted A i, ?_, ?_⟩
  · intro j bound
    have e : Denotes v (replayInputs A r (modeInput i.val 0 j)) a[j]! := by cases j <;> exact ma _ bound
    exact ⟨e.1,e.2.trans (mode_assignment A r i 0 j (by omega))⟩
  · intro j bound
    have e : Denotes v (replayInputs A r (modeInput i.val 1 j)) b[j]! := by cases j <;> exact mb _ bound
    exact ⟨e.1,e.2.trans (mode_assignment A r i 1 j (by omega))⟩

theorem audit_scheduled_gate (A : GateSchedule P) (r : Relabelling) (v : Values) (i : Fin 5)
    (a b : Array Lit) (past : Nat → Nat → Bool) :
    let primary := physicalLeaves S r (replayInputs A r)
    let x := fun k => sampleInput k ∘ r.vertex
    Audited primary v (v 1 = true ∧ ∀ k < samples.size,
        Denotes v (replayPortBit A i 0 (x k) (past k)) a[k]! ∧
        Denotes v (replayPortBit A i 1 (x k) (past k)) b[k]!)
      (combineSampleValues (A.masks.1.getLsbD i) a b)
      (ArrayDenotes v samples.size (fun k => A.stage (x k) i.val (past k))) := by
  dsimp only
  have kind : A.masks.1.getLsbD i = dirtyAt count (A.index.symm i) := by
    unfold GateSchedule.masks
    exact ofSlots_bit (fun j => dirtyAt count (A.index.symm j)) i
  refine (audit_combine_samples (physicalLeaves S r (replayInputs A r)) v (A.masks.1.getLsbD i) a b
    (fun k => replayPortBit A i 0 (sampleInput k ∘ r.vertex) (past k))
    (fun k => replayPortBit A i 1 (sampleInput k ∘ r.vertex) (past k))).mono id ?_
  rintro _ vs ⟨size,values⟩
  refine ⟨size,?_⟩
  intro k bound
  change Denotes v (A.stage (sampleInput k ∘ r.vertex) i.val (past k)) vs[k]!
  rw [replay_stage_combine, ← kind]
  exact values k bound

private theorem sample_bounds : ∀ k : Fin 132, (samples[k.val]!).all (fun j => decide (j < 26)) = true := by
  decide +kernel

theorem sample_vertex {k j : Nat} (bound : k < samples.size) (mem : j ∈ samples[k]!) : j < 26 := by
  rw [sample_count] at bound
  exact of_decide_eq_true (List.all_eq_true.mp (sample_bounds ⟨k,bound⟩) _ mem)

theorem physical_raw_leaf (S : Stars C) (ao : IsAO2 26 C) (r : Relabelling) (other : Input → Bool)
    (v : Values) (one : v 1 = true) (l : Fin 13) (bank : Leaf)
    (matched : LeafMatches (physicalLeaves S r other) v (13+l.val) bank) (w : Fin 26) :
    literalValue v (rawAt bank w.val) = true ↔ r.inverse.vertex w ∈ leaf S (r.inverse.line l) := by
  have lookup := (leaf_lookup matched one w.val).2
  rw [lookup]
  constructor
  · split
    · rename_i adj
      have h : w.val < 13 := List.mem_range.mp (List.mem_filter.mp adj).1
      let p : Fin 13 := ⟨w.val,h⟩
      have wp : w = pt p := Fin.ext rfl
      rw [wp, point_vertex]
      exact (physicalLeaves_bit S r other p l).mp
    · simp
  · intro mem
    obtain ⟨p,hp⟩ := leaf_point S ao mem
    have wEq : w = pt (r.point p) := by
      have e := congrArg r.vertex hp
      simpa only [r.vertex_right_inverse,point_vertex] using e
    rw [wEq]
    have adj := (adj_coordinates p (r.inverse.line l)).mpr (leaf_neighbor S ao (hp ▸ mem))
    have adj' := (r.incidence p (r.inverse.line l)).mpr adj
    have lnEq : r.line (r.inverse.line l) = l := r.inverse.lineInjective (by rw [line_inverse])
    rw [lnEq] at adj'
    have neigh := (in_neighbours (r.point p) l).mpr adj'
    have hit : physicalLeaves S r other (.leaf (13+l.val) (r.point p).val) = true := by
      apply (physicalLeaves_bit S r other _ _).mpr
      simpa only [point_inverse] using (hp ▸ mem)
    exact (ite_eq_left neigh).trans hit

private theorem slot_bound {stages : Array Stage} {first i : Nat} (mem : i ∈ topSlots stages first) : i < 5 :=
  List.mem_range.mp (List.mem_filter.mp mem).1

private theorem physical_choice_route (A : GateSchedule P) (r : Relabelling) (l : Fin 13) (i : Fin 5) :
    let q := r.inverse.line l
    let primary := physicalLeaves S r (replayInputs A r)
    (primary (.topCentre (13+l.val) i.val) = true ↔ replayRoute A q (S.center (S.index q)) (A.index.symm i)) ∧
      (primary (.topLeaf (13+l.val) i.val) = true ↔ replayRoute A q (1-S.center (S.index q)) (A.index.symm i)) := by
  classical
  have line : 13+l.val-13 = l.val := by omega
  simp [physicalLeaves,replayInputs,line]

noncomputable def scheduledRaw (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (j : Nat) : Bool :=
  decide (r.inverse.vertex (Fin.ofNat 26 j) ∈ wireRaw count (A.index.symm i))

theorem physical_top_allowed (A : GateSchedule P) (ao : IsAO2 26 C) (r : Relabelling) (v : Values)
    (one : v 1 = true) (l : Fin 13) (i : Fin 5) (stages : Array Stage) (bank : Leaf)
    (matched : LeafMatches (physicalLeaves S r (replayInputs A r)) v (13+l.val) bank)
    (raw : ArrayDenotes v 26 (scheduledRaw A r i) stages[i.val]!.raw)
    (anchor : i.val = Formula.firstBit A.masks.2 → l = 0 →
      A.masks.2.getLsbD i = true → replayRoute A (r.inverse.line l) (S.center (S.index (r.inverse.line l))) (A.index.symm i)) :
    TopAllowed (physicalLeaves S r (replayInputs A r)) v A.masks.2 (13+l.val) bank stages i.val := by
  classical
  let q := r.inverse.line l
  let j := A.index.symm i
  let ln' := 13+l.val
  have coord : r.line q = l := r.inverse.lineInjective (by rw [line_inverse])
  have centre : ArrayDenotes v 26 (fun n => n == ln') (topCentreRaw ln') := by
    refine ⟨by simp [topCentreRaw],?_⟩
    intro n hn
    have valid : n < (topCentreRaw ln').size := by simpa [topCentreRaw] using hn
    rw [getElem!_pos (topCentreRaw ln') n valid]
    simp only [topCentreRaw, Array.getElem_map, Array.getElem_range]
    exact Denotes.constant v one _
  have leafArray : ArrayDenotes v 26
      (fun n => decide (r.inverse.vertex (Fin.ofNat 26 n) ∈ leaf S q)) (topLeafRaw bank) := by
    refine ⟨by simp [topLeafRaw],?_⟩
    intro n hn
    have valid : n < (topLeafRaw bank).size := by simpa [topLeafRaw] using hn
    rw [getElem!_pos (topLeafRaw bank) n valid]
    simp only [topLeafRaw, Array.getElem_map, Array.getElem_range]
    let w : Fin 26 := ⟨n,hn⟩
    have eq : Fin.ofNat 26 n = w := Fin.ext (Nat.mod_eq_of_lt hn)
    rw [eq]
    refine ⟨(leaf_lookup matched one n).1,Bool.eq_iff_iff.mpr ?_⟩
    simp only [decide_eq_true_eq]
    exact physical_raw_leaf S ao r _ v one l bank matched w
  have nonempty (ne : (wireRaw count j).Nonempty) : ∃ n < 26, scheduledRaw A r i n = true := by
    obtain ⟨u,hu⟩ := ne
    refine ⟨(r.vertex u).val,(r.vertex u).isLt,?_⟩
    unfold scheduledRaw
    have eq : Fin.ofNat 26 (r.vertex u).val = r.vertex u := Fin.ext (Nat.mod_eq_of_lt (r.vertex u).isLt)
    simp only [eq,r.vertex_left_inverse,decide_eq_true_eq]
    exact hu
  refine ⟨raw.nonzero, ?_, ?_, ?_⟩
  · intro on
    have route := (physical_choice_route A r l i).1.mp on
    obtain ⟨_,ne,sub⟩ := replay_route_raw A route
    apply raw_subset_of_denotes raw centre (nonempty ne)
    intro n hn member
    have w := sub (of_decide_eq_true member)
    rw [S.singleton,Finset.mem_singleton] at w
    have image := congrArg r.vertex w
    rw [r.vertex_right_inverse,line_vertex,coord] at image
    have e := congrArg Fin.val image
    change n % 26 = 13+l.val at e
    exact beq_iff_eq.mpr (by rwa [Nat.mod_eq_of_lt hn] at e)
  · intro on
    have route := (physical_choice_route A r l i).2.mp on
    obtain ⟨_,ne,sub⟩ := replay_route_raw A route
    apply raw_subset_of_denotes raw leafArray (nonempty ne)
    intro n _ member
    exact decide_eq_true (sub (of_decide_eq_true member))
  · constructor
    · intro off
      apply Bool.eq_false_iff.mpr
      intro on
      have route := (physical_choice_route A r l i).1.mp on
      have bit : A.masks.2.getLsbD i = true := by
        simp only [GateSchedule.masks,ofSlots_bit]
        exact decide_eq_true ⟨route.2,q,route.1⟩
      exact Bool.false_ne_true (off.symm.trans bit)
    · intro on pos line
      exact (physical_choice_route A r l i).1.mpr (anchor pos (Fin.ext (by omega)) on)

private theorem physical_selected_bits (A : GateSchedule P) (r : Relabelling) (v : Values) (l : Fin 13)
    (stages : Array Stage) (firstOn : A.masks.1.getLsbD (Formula.firstBit A.masks.1) = true)
    (dirty : ∀ i : Fin 5, stages[i.val]!.dirty = dirtyAt count (A.index.symm i))
    (past : Nat → Bool) (read : Nat → Lit)
    (bank : ∀ i ∈ topSlots stages (Formula.firstBit A.masks.1), Denotes v (past i) (read i))
    (selectors : List TopSelector)
    (rel : TopChoices (physicalLeaves S r (replayInputs A r)) v (13+l.val)
      (topSlots stages (Formula.firstBit A.masks.1)) selectors) :
    let q := r.inverse.line l
    ((selectedBits v read (·.2.1) selectors).any id = true ↔
      ∃ j, replayRoute A q (S.center (S.index q)) j ∧ past (A.index j).val = true) ∧
    ((selectedBits v read (·.2.2) selectors).any id = true ↔
      ∃ j, replayRoute A q (1-S.center (S.index q)) j ∧ past (A.index j).val = true) := by
  let q := r.inverse.line l
  let slots := topSlots stages (Formula.firstBit A.masks.1)
  let primary := physicalLeaves S r (replayInputs A r)
  have transport (tag : Nat → Input) (b : Fin 2) (matching : ∀ i : Fin 5,
      primary (tag i.val) = true ↔ replayRoute A q b (A.index.symm i)) :
      (∃ i ∈ slots, primary (tag i) = true ∧ past i = true) ↔
        ∃ j, replayRoute A q b j ∧ past (A.index j).val = true := by
    constructor
    · rintro ⟨i,mem,yes,on⟩
      let p : Fin 5 := ⟨i,slot_bound mem⟩
      exact ⟨A.index.symm p,(matching p).mp yes,by simpa only [Equiv.apply_symm_apply] using on⟩
    · rintro ⟨j,route,on⟩
      refine ⟨_,replay_route_in_slots A stages dirty firstOn route,(matching (A.index j)).mpr ?_,on⟩
      rwa [Equiv.symm_apply_apply]
  exact ⟨(selectedBits_on rel read past bank (tag := .topCentre (13+l.val)) (fun _ _ h => h.2.1)).trans
    (transport _ _ (fun i => (physical_choice_route A r l i).1)),
    (selectedBits_on rel read past bank (tag := .topLeaf (13+l.val)) (fun _ _ h => h.2.2)).trans
    (transport _ _ (fun i => (physical_choice_route A r l i).2))⟩

theorem physical_decoded_hit (A : GateSchedule P) (ao : IsAO2 26 C) (r : Relabelling) (v : Values)
    (one : v 1 = true) (l : Fin 13) (stages : Array Stage) (bank : Leaf)
    (firstOn : A.masks.1.getLsbD (Formula.firstBit A.masks.1) = true)
    (dirty : ∀ i : Fin 5, stages[i.val]!.dirty = dirtyAt count (A.index.symm i))
    (matched : LeafMatches (physicalLeaves S r (replayInputs A r)) v (13+l.val) bank)
    (k : Nat) (bound : k < samples.size) (past : Nat → Bool) (selectors : List TopSelector)
    (rel : TopChoices (physicalLeaves S r (replayInputs A r)) v (13+l.val)
      (topSlots stages (Formula.firstBit A.masks.1)) selectors)
    (known : ∀ i ∈ topSlots stages (Formula.firstBit A.masks.1), Denotes v (past i) stages[i]!.values[k]!) :
    let read := fun i : Nat => stages[i]!.values[k]!
    let x := sampleInput k ∘ r.vertex
    HitInputs v read bank selectors samples[k]! ∧
      (decodedHit v (13+l.val) bank selectors read samples[k]! = true ↔ replayTopOn A (r.inverse.line l) x past) := by
  let read := fun i : Nat => stages[i]!.values[k]!
  let x := sampleInput k ∘ r.vertex
  let q := r.inverse.line l
  have centre : samples[k]!.contains (13+l.val) = x (ln q) := by
    change samples[k]!.contains _ = samples[k]!.contains (r.vertex (ln q)).val
    rw [line_vertex]
    have eq : r.line q = l := r.inverse.lineInjective (by rw [line_inverse])
    rw [eq]
    rfl
  have leafBit : (samples[k]!.filterMap fun n => bank.lookup n).any (literalValue v) = true ↔
      ∃ w ∈ leaf S q, x w = true := by
    rw [leaf_terms_value v one, List.any_eq_true]
    constructor
    · rintro ⟨j,mem,on⟩
      let w : Fin 26 := ⟨j,sample_vertex bound mem⟩
      refine ⟨r.inverse.vertex w,(physical_raw_leaf S ao r _ v one l bank matched w).mp on,?_⟩
      change samples[k]!.contains (r.vertex (r.inverse.vertex w)).val = true
      rw [r.vertex_right_inverse]
      exact List.contains_iff_mem.mpr mem
    · rintro ⟨w,mem,on⟩
      refine ⟨(r.vertex w).val,List.contains_iff_mem.mp on,?_⟩
      apply (physical_raw_leaf S ao r _ v one l bank matched (r.vertex w)).mpr
      rwa [r.vertex_left_inverse]
  refine ⟨⟨one,?_,?_⟩,?_⟩
  · intro s hs
    obtain ⟨mem,meaning⟩ := rel.mem s hs
    exact ⟨meaning.2.1.1,meaning.2.2.1,(known _ mem).1⟩
  · intro t ht
    obtain ⟨j,_,found⟩ := List.mem_filterMap.mp ht
    have h := (leaf_lookup matched one j).1
    simpa only [rawAt,found,Option.getD_some] using h
  · obtain ⟨centreRoutes,leafRoutes⟩ := physical_selected_bits A r v l stages firstOn dirty past read known selectors rel
    simp only [read] at centreRoutes leafRoutes
    unfold decodedHit replayTopOn
    simp only [Bool.and_eq_true,Bool.or_eq_true,centre,leafBit,centreRoutes,leafRoutes]
    rfl

noncomputable def physicalHit (A : GateSchedule P) (r : Relabelling) (mute : Option Nat) (line k : Nat) : Bool := by
  classical
  let x := sampleInput k ∘ r.vertex
  exact decide (replayTopOn A (r.inverse.line (Fin.ofNat 13 (line-13))) x (evalSchedule (A.stage x) mute 5))

structure ScheduledOutput (A : GateSchedule P) (r : Relabelling) (mute : Option Nat) (v : Values)
    (leaves : Array Leaf) (stages : Array Stage) : Prop where
  one : v 1 = true
  bank : LeafBank (physicalLeaves S r (replayInputs A r)) v leaves.toList
  firstOn : A.masks.1.getLsbD (Formula.firstBit A.masks.1) = true
  dirty : ∀ j : Fin 5, stages[j.val]!.dirty = dirtyAt count (A.index.symm j)
  reads : ∀ j : Fin 5, ∀ k < samples.size, let x := sampleInput k ∘ r.vertex
    Denotes v (evalSchedule (A.stage x) mute 5 j.val) stages[j.val]!.values[k]!
  raw : ∀ j : Fin 5, ArrayDenotes v 26 (scheduledRaw A r j) stages[j.val]!.raw
  anchor : ∀ j : Fin 5, j.val = Formula.firstBit A.masks.2 → A.masks.2.getLsbD j = true →
    let l := r.inverse.line 0
    replayRoute A l (S.center (S.index l)) (A.index.symm j)

private theorem physical_output_ready (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (i : Fin 5) (centre : Option (Fin 13))
    (choice : ReplayChoice S (GateSchedule.rawFirst P least).masks
      (gateOrder count ((GateSchedule.rawFirst P least).index.symm i)).val centre)
    (v : Values) (leaves : Array Leaf) (stages : Array Stage) :
    let A := GateSchedule.rawFirst P least
    let r := choice.coordinates
    let mute := replayMute choice.refinement i
    let primary := physicalLeaves S r (replayInputs A r)
    ScheduledOutput A r mute v leaves stages →
      OutputTestsReady primary v A.masks.1 A.masks.2 leaves stages (physicalHit A r mute) := by
  classical
  dsimp only
  let A := GateSchedule.rawFirst P least
  let r := choice.coordinates
  let mute := replayMute choice.refinement i
  let primary := physicalLeaves S r (replayInputs A r)
  have tests := replay_sample_tests (P := P) least top empty i centre choice
  rintro ⟨one,bank,firstOn,dirty,reads,raw,anchor⟩
  have lineBank (line : Nat) (lo : 13 ≤ line) (hi : line < 26) :
      LeafMatches primary v line leaves[line-13]! := by
    simpa only [Array.toArray_toList] using leaf_bank_index bank line lo hi
  have bounds (line : Nat) (mem : line ∈ List.range' 13 13) : 13 ≤ line ∧ line < 26 := by
    obtain ⟨n,hn,eq⟩ := List.mem_range'.mp mem
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro line hm j hj
    have hx := bounds line hm
    let l : Fin 13 := ⟨line-13, by omega⟩
    let g : Fin 5 := ⟨j,slot_bound hj⟩
    have tag : 13+l.val = line := by change 13+(line-13) = line; omega
    have leafMatch : LeafMatches primary v (13+l.val) leaves[line-13]! := by
      rw [tag]
      exact lineBank line hx.1 hx.2
    have verified := physical_top_allowed A least.1 r v one l g stages leaves[line-13]! leafMatch (raw g)
      (by intro hp eq on; rw [eq]; exact anchor g hp on)
    rwa [tag] at verified
  · intro line hm sels rel k hk
    have hx := bounds line hm
    have lo : 13 ≤ line := hx.1
    have hi : line < 26 := hx.2
    let l : Fin 13 := ⟨line-13, by omega⟩
    have tag : 13+l.val = line := by change 13+(line-13) = line; omega
    have slot : Fin.ofNat 13 (line-13) = l := Fin.ext (Nat.mod_eq_of_lt l.isLt)
    let x := sampleInput k ∘ r.vertex
    let past := evalSchedule (A.stage x) mute 5
    have matched : LeafMatches primary v (13+l.val) leaves[line-13]! := by
      rw [tag]
      exact lineBank line lo hi
    have found := physical_decoded_hit A least.1 r v one l stages leaves[line-13]! firstOn dirty matched
      k hk past sels (tag.symm ▸ rel) (fun j bound => reads ⟨j,slot_bound bound⟩ k hk)
    refine ⟨found.1, ?_, ?_⟩
    · apply Bool.eq_iff_iff.mpr
      simp only [physicalHit,slot,decide_eq_true_eq]
      have transport := found.2
      rw [tag] at transport
      exact transport
    · intro negative
      have off := tests.2 k negative hk (r.inverse.line l)
      simp only [physicalHit,slot,decide_eq_false_iff_not]
      exact off
  · intro k hk
    obtain ⟨l,on⟩ := tests.1 k hk
    let line := r.line l
    refine ⟨13+line.val, List.mem_range'.mpr ⟨line.val,line.isLt,by simp⟩,?_⟩
    have hn : 13+line.val-13 = line.val := by omega
    have coord : Fin.ofNat 13 line.val = line := Fin.ext (Nat.mod_eq_of_lt line.isLt)
    change physicalHit A r mute (13+line.val) k = true
    simp only [physicalHit,hn,coord,line,line_inverse,decide_eq_true_eq]
    exact on

attribute [local irreducible] collectOutputTests

/-- The emitted output block checks the physical routes and all sample tests
    once the stage table supplies their raw support and sample values. -/
theorem audit_physical_output_tests (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (i : Fin 5) (centre : Option (Fin 13))
    (choice : ReplayChoice S (GateSchedule.rawFirst P least).masks
      (gateOrder count ((GateSchedule.rawFirst P least).index.symm i)).val centre)
    (v : Values) (leaves : Array Leaf) (stages : Array Stage) :
    let A := GateSchedule.rawFirst P least
    let r := choice.coordinates
    let mute := replayMute choice.refinement i
    let primary := physicalLeaves S r (replayInputs A r)
    Audited primary v (ScheduledOutput A r mute v leaves stages)
      (collectOutputTests A.masks.1 A.masks.2 leaves stages)
      (List.Forall₂ (OutputRow primary v A.masks.1 stages (physicalHit A r mute)) (List.range' 13 13)) := by
  dsimp only
  let A := GateSchedule.rawFirst P least
  let r := choice.coordinates
  let mute := replayMute choice.refinement i
  let primary := physicalLeaves S r (replayInputs A r)
  exact (audit_collect_output_tests primary v A.masks.1 A.masks.2 leaves stages (physicalHit A r mute)).mono
    (physical_output_ready (P := P) least top empty i centre choice v leaves stages) (fun _ _ h => h)

theorem physical_centre_presence (A : GateSchedule P) (r : Relabelling) (v : Values) (stages : Array Stage)
    (firstOn : A.masks.1.getLsbD (Formula.firstBit A.masks.1) = true)
    (dirty : ∀ i : Fin 5, stages[i.val]!.dirty = dirtyAt count (A.index.symm i))
    (answer : Nat → Nat → Bool) (rows : List (List TopSelector × List Lit))
    (rel : List.Forall₂ (OutputRow (physicalLeaves S r (replayInputs A r)) v A.masks.1 stages answer)
      (List.range' 13 13) rows) (i : Fin 5) (on : A.masks.2.getLsbD i = true) :
    ClauseTrue v (centreTerms rows i.val) := by
  classical
  simp only [GateSchedule.masks,ofSlots_bit,decide_eq_true_eq] at on
  obtain ⟨after,l,uses⟩ := on
  let normalized := r.line l
  have lineRange : 13+normalized.val ∈ List.range' 13 13 :=
    List.mem_range'.mpr ⟨normalized.val,normalized.isLt,by simp⟩
  have route : replayRoute A l (S.center (S.index l)) (A.index.symm i) := ⟨uses,after⟩
  have slot : i.val ∈ topSlots stages (Formula.firstBit A.masks.1) := by
    simpa only [Equiv.apply_symm_apply] using replay_route_in_slots A stages dirty firstOn route
  apply centre_terms_on rel lineRange slot
  apply (physical_choice_route A r normalized i).1.mpr
  simpa only [normalized,line_inverse] using route

theorem physical_centre_anchor (A : GateSchedule P) (r : Relabelling) (centre : Option (Fin 13))
    (coordinates : CoordinateAnchor S centre r) (noneMask : centre = none ↔ A.masks.2 = 0)
    (firstRoute : ∀ l, centre = some l → ∃ j : Fin 5, j.val = Formula.firstBit A.masks.2 ∧
      replayRoute A l (S.center (S.index l)) (A.index.symm j))
    (i : Fin 5) (first : i.val = Formula.firstBit A.masks.2) (on : A.masks.2.getLsbD i = true) :
    let l := r.inverse.line 0
    replayRoute A l (S.center (S.index l)) (A.index.symm i) := by
  cases centre with
  | none => simp [noneMask.mp rfl] at on
  | some l =>
    obtain ⟨j,pos,route⟩ := firstRoute l rfl
    have eq : j = i := Fin.ext (pos.trans first.symm)
    subst j
    change r.line l = 0 at coordinates
    have normalized : r.inverse.line 0 = l := by rw [← coordinates,line_inverse]
    simpa only [normalized] using route

#print axioms physical_decoded_hit
#print axioms audit_scheduled_port_order
#print axioms audit_scheduled_gate
#print axioms audit_physical_output_tests
#print axioms physical_centre_presence
#print axioms physical_centre_anchor

end SixEdge.Plane
