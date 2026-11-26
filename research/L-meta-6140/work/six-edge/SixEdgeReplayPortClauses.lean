import SixEdgeReplayPorts
import SixEdgePortClauseAudit

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

set_option maxHeartbeats 3000000

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

private theorem fin_ofNat_eq {n k : Nat} [NeZero n] (bound : k < n) :
    Fin.ofNat n k = ⟨k,bound⟩ := Fin.ext (Nat.mod_eq_of_lt bound)

private theorem leaf_size {p : Input → Bool} {v : Values} {leaves : Array Leaf}
    (checked : LeafBank p v leaves.toList) : leaves.size = 13 := by
  simpa using checked.length_eq.symm

private theorem host_size (leaves : Array Leaf) : (portHosts leaves).size = 26 + leaves.size := by
  simp [portHosts]

private theorem singleton_bank (leaves : Array Leaf) (j : Nat) (bound : j < 26) :
    (portHosts leaves)[j]! = [(j,1)] := by
  have left : j < ((List.range 26).map (fun x => [(x,(1 : Lit))])).toArray.size := by simpa using bound
  have all : j < (portHosts leaves).size := by rw [host_size]; omega
  rw [getElem!_pos (portHosts leaves) j all]
  simp [portHosts,Array.getElem_append_left left]

private theorem line_bank (leaves : Array Leaf) (l : Fin 13) (size : leaves.size = 13) :
    (portHosts leaves)[26+l.val]! = leaves[l.val]! := by
  have bound : l.val < leaves.size := size.symm ▸ l.isLt
  have all : 26+l.val < (portHosts leaves).size := by rw [host_size]; omega
  have right : ((List.range 26).map (fun x => [(x,(1 : Lit))])).toArray.size ≤ 26+l.val := by simp
  rw [getElem!_pos (portHosts leaves) _ all,getElem!_pos leaves _ bound]
  simp [portHosts,Array.getElem_append_right right]

private theorem leaf_vertices {p : Input → Bool} {v : Values} {l : Nat} {bank : Leaf}
    (checked : LeafMatches p v l bank) : bank.map Prod.fst = neighbours l := by
  unfold LeafMatches at checked
  generalize neighbourList : neighbours l = points at checked ⊢
  clear neighbourList
  induction checked with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons,head.1,ih]

private theorem host_vertices {p : Input → Bool} {v : Values} {leaves : Array Leaf}
    (checked : LeafBank p v leaves.toList) (j : Nat) (bound : j < (portHosts leaves).size) :
    ∀ x ∈ (portHosts leaves)[j]!.map Prod.fst, x < 26 := by
  by_cases raw : j < 26
  · rw [singleton_bank leaves j raw]
    intro x hx
    simpa using (List.mem_singleton.mp hx ▸ raw : x < 26)
  · have size := leaf_size checked
    rw [host_size,size] at bound
    let l : Fin 13 := ⟨j-26,by omega⟩
    have eq : 26+l.val = j := by change 26+(j-26) = j; omega
    have lchecked : LeafMatches p v (13+l.val) leaves[l.val]! := by
      simpa using leaf_bank_index checked (13+l.val) (by omega) (by have := l.isLt; omega)
    rw [← eq,line_bank leaves l size,leaf_vertices lchecked]
    intro x mem
    have hx : x < 13 := List.mem_range.mp (List.mem_filter.mp mem).1
    omega

private theorem host_supplies (r : Relabelling) (ao : IsAO2 26 C) (other : Input → Bool)
    (v : Values) (one : v 1 = true) (leaves : Array Leaf)
    (checked : LeafBank (physicalLeaves S r other) v leaves.toList)
    (host : PortHost) (x : Fin 26) (mem : x ∈ host.support S) :
    literalValue v (rawAt (portHosts leaves)[replayHost r host]! (r.vertex x).val) = true := by
  cases host with
  | singleton u =>
    have e : x = u := Finset.mem_singleton.mp mem
    subst x
    rw [replayHost,singleton_bank leaves _ (r.vertex u).isLt]
    simp [rawAt,List.lookup,literalValue,one]
  | leaf l =>
    let q := r.line l
    have lchecked : LeafMatches (physicalLeaves S r other) v (13+q.val) leaves[q.val]! := by
      simpa using leaf_bank_index checked (13+q.val) (by omega) (by have := q.isLt; omega)
    rw [replayHost,line_bank leaves q (leaf_size checked)]
    apply (physical_raw_leaf S ao r other v one q _ lchecked (r.vertex x)).mpr
    simpa only [q,r.vertex_left_inverse,line_inverse,PortHost.support] using mem

private theorem rawAt_on_mem (v : Values) (one : v 1 = true) (bank : Leaf) (n : Nat)
    (on : literalValue v (rawAt bank n) = true) : n ∈ bank.map Prod.fst := by
  induction bank with
  | nil => simp [rawAt,literalValue,one] at on
  | cons h t ih =>
    by_cases eq : n = h.1
    · exact List.mem_cons.mpr (Or.inl eq)
    · have ne : (n == h.1) = false := Bool.eq_false_iff.mpr (fun h => eq (beq_iff_eq.mp h))
      exact List.mem_cons_of_mem _ (ih (by simpa [rawAt,List.lookup,ne] using on))

private theorem physical_host_checks (A : GateSchedule P) (r : Relabelling) (ao : IsAO2 26 C)
    (v : Values) (one : v 1 = true) (i : Fin 5) (b : Fin 2) (leaves : Array Leaf)
    (checked : LeafBank (physicalLeaves S r (replayInputs A r)) v leaves.toList) :
    HostChecks (physicalLeaves S r (replayInputs A r)) v (portHosts leaves) i.val b.val := by
  classical
  let hosts := portHosts leaves
  let p := physicalLeaves S r (replayInputs A r)
  have hostCount : hosts.size = 39 := by rw [host_size,leaf_size checked]
  have gi : Fin.ofNat 5 i.val = i := fin_ofNat_eq i.isLt
  have bi : Fin.ofNat 2 b.val = b := fin_ofNat_eq b.isLt
  cases cur : replayPort A i b with
  | direct q =>
    have mode : p (.atomMode i.val b.val) = false := by
      simp only [p,physicalLeaves,replayInputs,gi,bi,cur]
    have atom (x : Nat) : p (.atom i.val b.val x) = false := by
      simp only [p,physicalLeaves,replayInputs,gi,bi,cur]
    have host (j : Nat) : p (.host i.val b.val j) = false := by
      simp only [p,physicalLeaves,replayInputs,gi,bi,cur]
    refine ⟨fun h => (Bool.false_ne_true (mode.symm.trans h)).elim,
      fun x _ h => (Bool.false_ne_true ((atom x).symm.trans h)).elim, ?_,?_⟩
    · refine ⟨0,by rw [hostCount]; decide,?_⟩
      intro j _
      change p (.host i.val b.val j) = (p (.atomMode i.val b.val) && (j == 0))
      rw [host j,mode,Bool.false_and]
    · intro j jb
      refine ⟨host_vertices checked j jb,?_,?_⟩
      · exact fun h => (Bool.false_ne_true ((host j).symm.trans h)).elim
      · exact fun _ h => (Bool.false_ne_true ((host j).symm.trans h)).elim
  | atom a =>
    have mode : p (.atomMode i.val b.val) = true := by
      simp only [p,physicalLeaves,replayInputs,gi,bi,cur]
    have atom (x : Nat) : p (.atom i.val b.val x) = decide (r.inverse.vertex (Fin.ofNat 26 x) ∈ a.raw) := by
      simp only [p,physicalLeaves,replayInputs,gi,bi,cur]
    have host (j : Nat) : p (.host i.val b.val j) = (replayHost r a.host == j) := by
      simp only [p,physicalLeaves,replayInputs,gi,bi,cur]
    have valid : (PortChoice.atom a).valid S count (A.index.symm i) :=
      cur ▸ P.valid (A.index.symm i) (replayOperandOrder A i b)
    have atomOn (x : Fin 26) (inRaw : x ∈ a.raw) : p (.atom i.val b.val (r.vertex x).val) = true := by
      rw [atom,fin_ofNat_eq (r.vertex x).isLt]
      change decide (r.inverse.vertex (r.vertex x) ∈ a.raw) = true
      rw [r.vertex_left_inverse]
      exact decide_eq_true inRaw
    refine ⟨?_,fun _ _ _ => mode,?_,?_⟩
    · intro _
      obtain ⟨x,hx⟩ := valid.1
      exact ⟨(r.vertex x).val,(r.vertex x).isLt,atomOn x hx⟩
    · refine ⟨replayHost r a.host, ?_,?_⟩
      · rw [hostCount]
        cases a.host with
        | singleton u => exact lt_trans (r.vertex u).isLt (by decide)
        | leaf l =>
          have bound := (r.line l).isLt
          change 26+(r.line l).val < 39
          omega
      · intro j _
        change p (.host i.val b.val j) = (p (.atomMode i.val b.val) && (j == replayHost r a.host))
        rw [host j,mode,Bool.true_and]
        exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)
    · intro j jb
      refine ⟨host_vertices checked j jb,?_,?_⟩
      · intro enabled x xb on
        have eq : replayHost r a.host = j := beq_iff_eq.mp ((host j).symm.trans enabled)
        rw [← eq]
        have hit : r.inverse.vertex (Fin.ofNat 26 x) ∈ a.raw := of_decide_eq_true ((atom x).symm.trans on)
        have supplied := host_supplies r ao (replayInputs A r) v one leaves checked a.host
          (r.inverse.vertex (Fin.ofNat 26 x)) (valid.2.1 hit)
        rw [r.vertex_right_inverse,fin_ofNat_eq xb] at supplied
        exact supplied
      · intro large enabled
        have eq : replayHost r a.host = j := beq_iff_eq.mp ((host j).symm.trans enabled)
        have many : 2 ≤ a.raw.card := by
          have card := valid.2.2.1
          cases hh : a.host with
          | leaf l => simpa only [hh] using card
          | singleton u =>
            rw [hh] at eq
            have small := (r.vertex u).isLt
            change (r.vertex u).val = j at eq
            omega
        obtain ⟨x,hx,y,hy,diff⟩ := Finset.one_lt_card.mp many
        have contains (u : Fin 26) (hu : u ∈ a.raw) : (r.vertex u).val ∈ hosts[j]!.map Prod.fst := by
          rw [← eq]
          exact rawAt_on_mem v one _ _ (host_supplies r ao (replayInputs A r) v one leaves checked _ _ (valid.2.1 hu))
        have names : (r.vertex x).val ≠ (r.vertex y).val :=
          fun e => diff (r.vertex_injective (Fin.ext e))
        rcases pairs_distinct _ (contains x hx) (contains y hy) names with forward | reverse
        · exact ⟨_,forward,Bool.and_eq_true_iff.mpr ⟨atomOn x hx,atomOn y hy⟩⟩
        · exact ⟨_,reverse,Bool.and_eq_true_iff.mpr ⟨atomOn y hy,atomOn x hx⟩⟩


private theorem scheduled_mode_bit (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (b : Fin 2)
    (j : Nat) (bound : j ≤ i.val) :
    physicalLeaves S r (replayInputs A r) (modeInput i.val b.val j) =
      (j == numberedMode A (replayPort A i b)) := by
  cases j <;> exact mode_assignment A r i b _ bound

private theorem scheduled_mode_selects (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (b : Fin 2) :
    Selects (i.val+1) true (fun j => physicalLeaves S r (replayInputs A r) (modeInput i.val b.val j)) := by
  refine ⟨numberedMode A (replayPort A i b),?_,?_⟩
  · cases h : replayPort A i b with
    | atom a => simp [numberedMode]
    | direct q =>
      have earlier := replay_reads_earlier A i q b (by rw [h]; rfl)
      exact Nat.succ_lt_succ earlier
  · intro j bound
    simpa only [Bool.true_and] using scheduled_mode_bit A r i b j (by omega)

private theorem physical_promotion (A : GateSchedule P) (r : Relabelling) (i : Fin 5) (b : Fin 2)
    (v : Values) (stages : Array Stage) (j : Nat)
    (prior : ArrayDenotes v 26 (scheduledRaw A r (Fin.ofNat 5 j)) stages[j]!.raw) :
    PromotionChecks (physicalLeaves S r (replayInputs A r)) v stages i.val b.val j
      (scheduledRaw A r (Fin.ofNat 5 j)) := by
  classical
  let p := physicalLeaves S r (replayInputs A r)
  let q := A.index.symm (Fin.ofNat 5 j)
  have gi : Fin.ofNat 5 i.val = i := fin_ofNat_eq i.isLt
  have bi : Fin.ofNat 2 b.val = b := fin_ofNat_eq b.isLt
  cases cur : replayPort A i b with
  | direct k =>
    have off : p (.promotion i.val b.val j) = false := by
      simp only [p,physicalLeaves,replayInputs,gi,bi,cur]
    refine ⟨prior,?_,?_,?_⟩ <;> exact fun yes => (Bool.false_ne_true (off.symm.trans yes)).elim
  | atom a =>
    have mode : p (.atomMode i.val b.val) = true := by
      simp only [p,physicalLeaves,replayInputs,gi,bi,cur]
    have selected (yes : p (.promotion i.val b.val j) = true) : q ∈ a.promoted := by
      simpa only [p,physicalLeaves,replayInputs,gi,bi,cur,decide_eq_true_eq,q] using yes
    have valid : (PortChoice.atom a).valid S count (A.index.symm i) :=
      cur ▸ P.valid (A.index.symm i) (replayOperandOrder A i b)
    refine ⟨prior,fun _ => mode,?_,?_⟩
    · intro yes
      obtain ⟨x,hx⟩ := (valid.2.2.2 q (selected yes)).2.2.1
      refine ⟨(r.vertex x).val,(r.vertex x).isLt,?_⟩
      unfold scheduledRaw
      rw [fin_ofNat_eq (r.vertex x).isLt]
      change decide (r.inverse.vertex (r.vertex x) ∈ wireRaw count q) = true
      rw [r.vertex_left_inverse]
      exact decide_eq_true hx
    · intro yes x _ on
      have member : r.inverse.vertex (Fin.ofNat 26 x) ∈ wireRaw count q := of_decide_eq_true on
      have subset := (valid.2.2.2 q (selected yes)).2.2.2
      simpa only [p,physicalLeaves,replayInputs,gi,bi,cur,decide_eq_true_eq] using subset member

attribute [local irreducible] buildPort portHosts

/-- The scheduled physical operand satisfies every required clause of the
    actual builder. The returned mode literals are ready for the order check. -/
theorem audit_scheduled_buildPort (A : GateSchedule P) (r : Relabelling) (ao : IsAO2 26 C)
    (v : Values) (i : Fin 5) (b : Fin 2) (stages : Array Stage) (leaves : Array Leaf)
    (canonical : Bool) :
    let p := physicalLeaves S r (replayInputs A r)
    Audited p v
      (v 1 = true ∧ stages.size = i.val ∧ LeafBank p v leaves.toList ∧
        ∀ j < stages.size, ArrayDenotes v 26 (scheduledRaw A r (Fin.ofNat 5 j)) stages[j]!.raw)
      (buildPort stages (portHosts leaves) i.val b.val canonical)
      (fun port => ArrayDenotes v (i.val+1) (fun j => j == numberedMode A (replayPort A i b)) port.modes.toArray) := by
  let p := physicalLeaves S r (replayInputs A r)
  let raw := fun j => scheduledRaw A r (Fin.ofNat 5 j)
  dsimp only
  refine (audit_buildPort p v stages (portHosts leaves) i.val b.val canonical raw).mono ?_ ?_
  · rintro ⟨one,size,bank,past⟩
    refine ⟨one,?_,physical_host_checks A r ao v one i b leaves bank,?_⟩
    · rw [size]
      exact scheduled_mode_selects A r i b
    · intro j mem
      exact physical_promotion A r i b v stages j (past j (List.mem_range.mp (List.mem_filter.mp mem).1))
  · rintro ⟨_,size,_,_⟩ port modes
    refine ⟨modes.1.trans (by rw [size]),?_⟩
    intro j bnd
    have hb : j < stages.size+1 := by rwa [size]
    have hj := modes.2 j hb
    exact ⟨hj.1,hj.2.trans (scheduled_mode_bit A r i b j (by omega))⟩


theorem audit_scheduled_stage_ports (A : GateSchedule P) (r : Relabelling) (ao : IsAO2 26 C)
    (v : Values) (i : Fin 5) (stages : Array Stage) (leaves : Array Leaf) (canonical : Bool) :
    let p := physicalLeaves S r (replayInputs A r)
    Audited p v
      (v 1 = true ∧ stages.size = i.val ∧ LeafBank p v leaves.toList ∧
        ∀ j < stages.size, ArrayDenotes v 26 (scheduledRaw A r (Fin.ofNat 5 j)) stages[j]!.raw)
      (buildStagePorts stages (portHosts leaves) i.val canonical)
      (fun ⟨a,b⟩ =>
        ArrayDenotes v (i.val+1) (fun j => j == numberedMode A (replayPort A i 0)) a.modes.toArray ∧
        ArrayDenotes v (i.val+1) (fun j => j == numberedMode A (replayPort A i 1)) b.modes.toArray) := by
  dsimp only
  unfold buildStagePorts
  refine Audited.bind (audit_scheduled_buildPort A r ao v i 0 stages leaves canonical) ?_
  intro a
  refine Audited.bind ((audit_scheduled_buildPort A r ao v i 1 stages leaves canonical).mono
    And.left (fun _ _ z => z)) ?_
  intro b
  have reads {ls : List Lit} {bit : Nat → Bool} (ok : ArrayDenotes v (i.val+1) bit ls.toArray)
      (j : Nat) (bound : j < ls.length) : Denotes v (bit j) ls[j]! := by
    have len : ls.length = i.val+1 := ok.1
    simpa only [List.getElem!_toArray] using ok.2 j (len ▸ bound)
  refine Audited.bind ((audit_port_order (physicalLeaves S r (replayInputs A r)) v a.modes b.modes
    (numberedMode A (replayPort A i 0)) (numberedMode A (replayPort A i 1))).mono
      (fun h => ⟨replay_port_sorted A i,reads h.1.2,reads h.2⟩) (fun _ _ z => z)) ?_
  intro _
  exact Audited.pure _ _ (a,b) (fun h => ⟨h.1.1.2,h.1.2⟩)

#print axioms audit_scheduled_buildPort
#print axioms audit_scheduled_stage_ports

end SixEdge.Plane
