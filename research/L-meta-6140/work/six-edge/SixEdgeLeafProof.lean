import SixEdgeCountProof

namespace SixEdge.Formula

set_option maxHeartbeats 3000000

def LeafMatches (primary : Input → Bool) (v : Values) (line : Nat) (leaf : Leaf) : Prop :=
  List.Forall₂ (fun p (entry : Nat × Lit) =>
    entry.1 = p ∧ entry.2 ≠ 0 ∧ literalValue v entry.2 = primary (.leaf line p))
    (neighbours line) leaf

theorem audit_declare_leaf (primary : Input → Bool) (v : Values) (line : Nat) :
    Audited primary v True (declareLeaf line) (LeafMatches primary v line) := by
  unfold declareLeaf LeafMatches
  apply Audited.mapM
  intro p
  apply Audited.bind ((audit_choose primary v (.leaf line p)).mono (fun _ => trivial) (fun _ _ h => h))
  intro t
  exact Audited.pure _ _ _ (fun h => ⟨rfl,h.2⟩)

private theorem matching_lookup {v : Values} {f : Nat → Bool} {pts : List Nat} {leaf : Leaf}
    (same : List.Forall₂ (fun p (e : Nat × Lit) => e.1 = p ∧ e.2 ≠ 0 ∧ literalValue v e.2 = f p) pts leaf)
    (p : Nat) (one : v 1 = true) :
    rawAt leaf p ≠ 0 ∧ literalValue v (rawAt leaf p) = (if p ∈ pts then f p else false) := by
  induction same with
  | nil => simp [rawAt, literalValue, one]
  | @cons q entry qs es matchHead _ ih =>
    obtain ⟨fromHead,nz,value⟩ := matchHead
    by_cases eq : p = q
    · simp [rawAt,List.lookup,eq,fromHead,nz,value]
    · have test : (p == entry.1) = false := Bool.eq_false_iff.mpr (fun h => eq ((beq_iff_eq.mp h).trans fromHead))
      simpa [rawAt, List.lookup, test, eq] using ih

theorem leaf_lookup {primary : Input → Bool} {v : Values} {line : Nat} {leaf : Leaf}
    (same : LeafMatches primary v line leaf) (one : v 1 = true) (point : Nat) :
    rawAt leaf point ≠ 0 ∧ literalValue v (rawAt leaf point) =
      (if point ∈ neighbours line then primary (.leaf line point) else false) :=
  matching_lookup same point one

private theorem some_active_term {v : Values} {f : Nat → Bool} {pts : List Nat} {leaf : Leaf}
    (same : List.Forall₂ (fun p (e : Nat × Lit) => e.1 = p ∧ e.2 ≠ 0 ∧ literalValue v e.2 = f p) pts leaf)
    {p : Nat} (hp : p ∈ pts) (active : f p = true) : ClauseTrue v (leaf.map Prod.snd) := by
  induction same with
  | nil => simp at hp
  | @cons q entry qs es relation _ ih =>
    rcases List.mem_cons.mp hp with rfl | later
    · exact ⟨entry.2, by simp, relation.2.2.trans active⟩
    · obtain ⟨t,ht,on⟩ := ih later
      exact ⟨t,List.mem_cons_of_mem _ ht,on⟩

private theorem audit_check_leaves (primary : Input → Bool) (v : Values) (bank : List Leaf) :
    Audited primary v (∀ leaf ∈ bank, ClauseTrue v (leaf.map Prod.snd)) (checkLeaves bank) (fun _ => True) := by
  induction bank with
  | nil => exact Audited.pure _ _ _ (fun _ => trivial)
  | cons leaf bank ih =>
    change Audited primary v _ (require .nonemptyLeaf (leaf.map Prod.snd) >>= fun _ => checkLeaves bank) _
    apply Audited.bind ((audit_require primary v .nonemptyLeaf (leaf.map Prod.snd)).mono
      (fun h => h _ List.mem_cons_self) (fun _ _ h => h))
    intro _
    apply ih.mono (fun h l hl => h.1 l (List.mem_cons_of_mem _ hl)) (fun _ _ h => h)

def LeafBank (primary : Input → Bool) (v : Values) (bank : List Leaf) : Prop :=
  List.Forall₂ (LeafMatches primary v) (List.range' 13 13) bank

theorem leaf_bank_index {primary : Input → Bool} {v : Values} {bank : List Leaf}
    (checked : LeafBank primary v bank) (line : Nat) (low : 13 ≤ line) (high : line < 26) :
    LeafMatches primary v line (bank.toArray[line-13]!) := by
  have size : bank.length = 13 := by simpa using checked.length_eq.symm
  have chunk : line - 13 < 13 := by omega
  have rel := checked.get (i := line-13) (by simpa) (by simpa [size])
  have labelEq : 13 + (line - 13) = line := by omega
  have bound : line - 13 < bank.toArray.size := by simpa [size]
  rw [getElem!_pos bank.toArray (line-13) bound]
  simpa [labelEq] using rel

private theorem bank_has_live {primary : Input → Bool} {v : Values} {bank : List Leaf}
    (checked : LeafBank primary v bank)
    (live : ∀ l ∈ List.range' 13 13, ∃ p ∈ neighbours l, primary (.leaf l p) = true) :
    ∀ leaf ∈ bank, ClauseTrue v (leaf.map Prod.snd) := by
  intro leaf mem
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp mem
  have il : i < (List.range' 13 13).length := by rw [checked.length_eq]; exact hi
  have matchLeaf := checked.get (i := i) il hi
  obtain ⟨p,hp,on⟩ := live _ (List.getElem_mem il)
  exact some_active_term matchLeaf hp on

private theorem indexed_edgeRows (e : Nat × Nat) (he : e ∈ edgeRows.toList) :
    13 ≤ e.2 ∧ e.2 < 26 ∧ e.1 ∈ neighbours e.2 := by
  have valid : edgeRows.toList.all (fun e => decide (13 ≤ e.2 ∧ e.2 < 26 ∧ e.1 ∈ neighbours e.2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp valid e he)

theorem bank_retained {primary : Input → Bool} {v : Values} {bank : List Leaf}
    (checked : LeafBank primary v bank) (one : v 1 = true)
    (e : Nat × Nat) (he : e ∈ edgeRows.toList) :
    rawAt (bank.toArray[e.2-13]!) e.1 ≠ 0 ∧
      literalValue v (rawAt (bank.toArray[e.2-13]!) e.1) = primary (.leaf e.2 e.1) := by
  obtain ⟨low,high,inc⟩ := indexed_edgeRows e he
  simpa [inc] using leaf_lookup (leaf_bank_index checked e.2 low high) one e.1

def MissingFlags (primary : Input → Bool) : List Bool :=
  edgeRows.toList.map fun (p,l) => !(primary (.leaf l p))

theorem audit_prepare (primary : Input → Bool) (v : Values) (extra : BitVec 5) :
    Audited primary v
      (v 1 = true ∧
        (∀ l ∈ List.range' 13 13, ∃ p ∈ neighbours l, primary (.leaf l p) = true) ∧
        (MissingFlags primary).count true = 6 ∧ (extra = 0 → primary (.leaf 13 0) = false))
      (prepare extra) (fun leaves => LeafBank primary v leaves.toList) := by
  unfold prepare
  apply Audited.bind (p := LeafBank primary v)
  · exact (Audited.mapM _ (fun l => (audit_declare_leaf primary v l).mono
      (fun _ => trivial) (fun _ _ h => h)))
  · intro bank
    apply Audited.bind ((audit_check_leaves primary v bank).mono
      (fun h => bank_has_live h.2 h.1.2.1) (fun _ _ h => h))
    intro _
    let retained := edgeRows.map fun (p,l) => rawAt bank.toArray[l-13]! p
    let negs := (retained.map Neg.neg).toList
    apply Audited.bind ((audit_exact_six primary v negs).mono ?_ (fun _ _ h => h))
    · intro _
      split
      · rename_i noCentre
        apply Audited.bind ((audit_require primary v .anchorResidual [-retained[0]!]).mono ?_ (fun _ _ h => h))
        · intro _
          apply Audited.pure
          exact fun h => by simpa using h.1.1.1.2
        · intro h
          have single := bank_retained h.1.1.2 h.1.1.1.1 (0,13) (by decide +kernel)
          refine ⟨_,List.mem_cons_self,?_⟩
          have eq : retained[0]! = rawAt bank.toArray[0]! 0 := by
            have edgeBound : 0 < edgeRows.size := by decide +kernel
            have bounded : 0 < retained.size := by simpa [retained] using edgeBound
            rw [getElem!_pos retained 0 bounded]
            have first : edgeRows[0]'edgeBound = (0,13) := by decide +kernel +revert
            simp only [retained, Array.getElem_map, first]
          rw [eq, literal_neg_of_ne _ (by simpa using single.1), show literalValue v (rawAt bank.toArray[0]! 0) = _ from single.2,
            h.1.1.1.2.2.2 noCentre]
          rfl
      · apply Audited.pure
        exact fun h => by simpa using h.1.1.2
    · rintro ⟨⟨⟨one,_,cnt,_⟩,covered⟩,_⟩
      have expanded : negs = edgeRows.toList.map (fun (p,l) => -rawAt bank.toArray[l-13]! p) := by
        simp [negs, retained, Function.comp_def]
      refine ⟨one,?_,?_⟩
      · rw [expanded]
        intro t ht
        obtain ⟨⟨p,l⟩,he,rfl⟩ := List.mem_map.mp ht
        exact neg_ne_zero.mpr (bank_retained covered one (p,l) he).1
      · rw [expanded,List.map_map, ← cnt]
        congr 1
        apply List.map_congr_left
        rintro ⟨p,l⟩ he
        obtain ⟨nz,value⟩ := bank_retained covered one (p,l) he
        change literalValue v (-rawAt bank.toArray[l-13]! p) = !(primary (.leaf l p))
        rw [literal_neg_of_ne _ nz,value]

set_option maxRecDepth 50000 in
private theorem preparation_trace_zero :
    TraceValid 1 ((prepare (0 : BitVec 5)).run {}).2.events.toList := by
  exact (traceValidBool_spec _ _).mp (by decide +kernel)

set_option maxRecDepth 50000 in
private theorem preparation_trace_nonzero :
    TraceValid 1 ((prepare (1 : BitVec 5)).run {}).2.events.toList := by
  exact (traceValidBool_spec _ _).mp (by decide +kernel)

theorem preparation_trace_valid (extra : BitVec 5) :
    TraceValid 1 ((prepare extra).run {}).2.events.toList := by
  by_cases none : extra = 0
  · subst extra
    exact preparation_trace_zero
  · have same : prepare extra = prepare 1 := by
      have one : (1 : BitVec 5) ≠ 0 := by decide
      simp only [prepare, ite_eq_right none, ite_eq_right one]
    rw [same]
    exact preparation_trace_nonzero

#print axioms audit_prepare
#print axioms preparation_trace_valid

end SixEdge.Formula
