import SixEdgeLayout
import SixEdgeEvaluation

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open ResidualDegree PlaneFour

variable {C : Circuit}

theorem PortChoice.value_congr (p : PortChoice) (x : Fin 26 → Bool) {f g : Fin 5 → Bool}
    (eq : ∀ j, p.reads j → f j = g j) : p.value x f ↔ p.value x g := by
  cases p with
  | direct j => simp [PortChoice.value, eq j rfl]
  | atom a =>
    apply or_congr Iff.rfl
    exact ⟨fun ⟨j, hj, on⟩ => ⟨j,hj,(eq j hj).symm ▸ on⟩,
      fun ⟨j, hj, on⟩ => ⟨j,hj,eq j hj ▸ on⟩⟩

theorem PortChoice.value_mono (p : PortChoice) (x : Fin 26 → Bool) {f g : Fin 5 → Bool}
    (hle : f ≤ g) : p.value x f → p.value x g := by
  have pushTrue j (h : f j = true) : g j = true := by
    cases h' : g j
    · exact False.elim ((by decide : ¬ true ≤ false) (h ▸ h' ▸ hle j))
    · rfl
  cases p with
  | direct j => exact pushTrue j
  | atom a =>
    rintro (raw | ⟨j,hj,on⟩)
    · exact Or.inl raw
    · exact Or.inr ⟨j,hj,pushTrue j on⟩

private theorem orValOperands (ao : IsAO2 26 C) {a : Nat} (len : a < C.gates.length)
    (op : (gateAt C a).op = GateOp.or) (x : Fin 26 → Bool) :
    gateVal 26 C a x = true ↔ ∃ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [gateVal_eq_val, val_or (n := 26) (by simp) len op]
  constructor
  · rintro ⟨w,hw,_,on⟩
    obtain ⟨b,hb⟩ := inputsAsOpnd ao len hw
    exact ⟨b,hb ▸ on⟩
  · rintro ⟨b,on⟩
    exact ⟨_,opndMem ao len b,opndBound ao len b,on⟩

def OrderedPorts.onAt {S : Stars C} {count : (charged plane C).card = 5}
    (P : OrderedPorts S count) (x : Fin 26 → Bool) (i : Fin 5) (past : Fin 5 → Bool) : Prop :=
  if dirtyAt count i then ∀ b, (P.port i b).value x past else ∃ b, (P.port i b).value x past

theorem OrderedPorts.onAt_actual {S : Stars C} {count : (charged plane C).card = 5}
    (P : OrderedPorts S count) (ao : IsAO2 26 C) (x : Fin 26 → Bool) (i : Fin 5) :
    P.onAt x i (fun j => gateVal 26 C (gateOrder count j).val x) ↔
      gateVal 26 C (gateOrder count i).val x = true := by
  classical
  have perms (Q : Fin 2 → Prop) : (∀ b, Q (P.order i b)) ↔ ∀ b, Q b :=
    ⟨fun h b => by simpa using h ((P.order i).symm b), fun h b => h _⟩
  have somePerm (Q : Fin 2 → Prop) : (∃ b, Q (P.order i b)) ↔ ∃ b, Q b :=
    ⟨fun ⟨b,hb⟩ => ⟨_,hb⟩, fun ⟨b,hb⟩ => ⟨(P.order i).symm b,by simpa⟩⟩
  rcases Finset.mem_union.mp (gateOrder count i).property with dirty | other
  · have has : dirtyAt count i = true := decide_eq_true dirty
    rw [OrderedPorts.onAt, ite_eq_left has, andValOperands ao (junkData dirty).1 (junkData dirty).2.1]
    simp only [← P.value]
    exact perms (fun b => val C (List.ofFn x) (opnd C (gateOrder count i).val b) = true)
  · have not : (gateOrder count i).val ∉ junk plane C :=
      fun hd => Finset.disjoint_left.mp disjoint_charged hd other
    have has : dirtyAt count i = false := decide_eq_false not
    have hne : ¬ dirtyAt count i = true := by simp [has]
    rw [OrderedPorts.onAt, ite_eq_right hne, orValOperands ao (orData other).1 (orData other).2.1]
    simp only [← P.value]
    exact somePerm (fun b => val C (List.ofFn x) (opnd C (gateOrder count i).val b) = true)

structure GateSchedule {S : Stars C} {count : (charged plane C).card = 5}
    (P : OrderedPorts S count) where
  index : Fin 5 ≃ Fin 5
  respects : ∀ {i j b}, (P.port i b).reads j → index j < index i

def GateSchedule.original {S : Stars C} {count : (charged plane C).card = 5}
    (P : OrderedPorts S count) : GateSchedule P :=
  ⟨Equiv.refl _, fun {_ _ b} h => PortChoice.reads_earlier (P.valid _ b) h⟩

noncomputable def GateSchedule.rawFirst {S : Stars C} {count : (charged plane C).card = 5}
    (P : OrderedPorts S count) (least : IsLeastAO plane C) : GateSchedule P :=
  ⟨reordered (rawSlots count), P.reorder_preserves_read least⟩

def GateSchedule.afterDirty {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (j : Fin 5) : Prop :=
  ∃ i : Fin 5, dirtyAt count i = true ∧ A.index i < A.index j

noncomputable def GateSchedule.masks {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) : Case := by
  classical
  exact (ofSlots (fun i => dirtyAt count (A.index.symm i)), ofSlots (fun i =>
    let j := A.index.symm i
    decide (A.afterDirty j ∧ ∃ l, topRoute S count l (S.center (S.index l)) j)))

/-- Reordering preserves coverage by the 34 base cases. A selected centre
    route must belong to an exceptional OR after some dirty AND. -/
theorem GateSchedule.masks_covered {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (two : (junk plane C).card = 2) : A.masks ∈ cases := by
  classical
  apply covers
  · have card := dirty_slots_card count two
    rw [← card]
    apply Finset.card_bij' (fun i _ => A.index.symm i) (fun j _ => A.index j)
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    · intro j hj
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] using hj
    · intros
      exact A.index.apply_symm_apply _
    · intros
      exact A.index.symm_apply_apply _
  · apply Bool.eq_false_iff.mpr
    intro on
    obtain ⟨i,_,b,use⟩ := P.read_dirty least empty _ on
    have h : (P.port i b).reads (A.index.symm 4) := by simp [use,PortChoice.reads]
    have before := A.respects h
    rw [Equiv.apply_symm_apply] at before
    omega
  · intro i on
    obtain ⟨⟨j,hj,lt⟩,l,route⟩ : A.afterDirty (A.index.symm i) ∧
      ∃ l, topRoute S count l (S.center (S.index l)) (A.index.symm i) := of_decide_eq_true on
    have ex := (top_route_valid S count route).1
    refine ⟨decide_eq_false (fun h => Finset.disjoint_left.mp disjoint_charged h ex), A.index j, ?_, ?_⟩
    · simpa using lt
    · simpa using hj

theorem GateSchedule.dirty_at_head_is_first {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (least : IsLeastAO plane C) {i : Fin 5}
    (zero : (GateSchedule.rawFirst P least).index i = 0) (dirty : dirtyAt count i = true) :
    ∀ k ∈ charged plane C, ¬ k < (gateOrder count i).val := by
  classical
  intro k hk earlier
  obtain ⟨j,hj⟩ := (gateOrder count).surjective ⟨k,hk⟩
  have kj : (gateOrder count j).val = k := congrArg Subtype.val hj
  have jEarlier : j < i := (gateOrder count).lt_iff_lt.mp (by
    change (gateOrder count j).val < (gateOrder count i).val
    simpa only [kj] using earlier)
  have iRaw : rawSlots count i = false := decide_eq_false (dirty_not_rawOnly (of_decide_eq_true dirty))
  have rank : (GateSchedule.rawFirst P least).index j < (GateSchedule.rawFirst P least).index i :=
    reordered_keeps_reads _ jEarlier (by simp [iRaw])
  rw [zero] at rank
  omega

theorem GateSchedule.raw_before_dirty {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} {j : Fin 5} (least : IsLeastAO plane C)
    (noEarlier : ¬ (GateSchedule.rawFirst P least).afterDirty j) :
    rawOnly plane C (26+(gateOrder count j).val) ∨ dirtyAt count j = true := by
  classical
  by_cases raw : rawOnly plane C (26+(gateOrder count j).val)
  · exact Or.inl raw
  by_cases dirty : dirtyAt count j = true
  · exact Or.inr dirty
  exfalso
  apply noEarlier
  have reachesDirty := raw
  unfold rawOnly at reachesDirty
  push Not at reachesDirty
  obtain ⟨g,hg,path⟩ := reachesDirty
  let chargedG : ↥(charged plane C) := ⟨g,Finset.mem_union_left _ hg⟩
  obtain ⟨i,hi⟩ := (gateOrder count).surjective chargedG
  have eq : (gateOrder count i).val = g := congrArg Subtype.val hi
  have isDirty : (gateOrder count i).val ∈ junk plane C := eq.symm ▸ hg
  refine ⟨i,decide_eq_true isDirty,?_⟩
  have le := orStep_le path
  have neq : (gateOrder count j).val ≠ g := fun e => dirty (decide_eq_true (e.symm ▸ hg))
  have earlier : i < j := (gateOrder count).lt_iff_lt.mp (by
    change (gateOrder count i).val < (gateOrder count j).val
    rw [eq]
    omega)
  have iRaw : rawSlots count i = false := decide_eq_false (dirty_not_rawOnly isDirty)
  have jRaw : rawSlots count j = false := decide_eq_false raw
  change reordered (rawSlots count) i < reordered (rawSlots count) j
  exact reordered_keeps_reads _ earlier (by simp [jRaw,iRaw])

theorem GateSchedule.rawFirst_top_port {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (l : Fin 13) (b : Fin 2) (x : Fin 26 → Bool) :
    val C (List.ofFn x) (opnd C (S.index l).val b) = true ↔
      (∃ v ∈ side (n := 26) C (S.index l).val b, x v = true) ∨
      ∃ j : Fin 5, topRoute S count l b j ∧ (GateSchedule.rawFirst P least).afterDirty j ∧
        gateVal 26 C (gateOrder count j).val x = true := by
  classical
  rw [top_route_value S least top empty count l b x]
  constructor
  · rintro (raw | ⟨j, route, fire⟩)
    · exact Or.inl raw
    · by_cases eligible : (GateSchedule.rawFirst P least).afterDirty j
      · exact Or.inr ⟨j,route,eligible,fire⟩
      have info := top_route_valid S count route
      rcases GateSchedule.raw_before_dirty (P := P) least eligible with raw | dirty
      · obtain ⟨_,_,reach⟩ := Finset.mem_filter.mp route.1
        exact Or.inl (rawOnly_port_redundant least.1 top (S.index l).property b raw
          (orReaches_reach _ _ reach).1 fire)
      · exact (Finset.disjoint_left.mp disjoint_charged (of_decide_eq_true dirty) info.1).elim
  · rintro (raw | ⟨j,route,_,fire⟩)
    · exact Or.inl raw
    · exact Or.inr ⟨j,route,fire⟩

noncomputable def GateSchedule.stage {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (x : Fin 26 → Bool)
    (i : Nat) (past : Nat → Bool) : Bool := by
  classical
  exact if hi : i < 5 then decide (P.onAt x (A.index.symm ⟨i,hi⟩) (fun j => past (A.index j).val)) else false

theorem GateSchedule.stage_monotone {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (x : Fin 26 → Bool) (i : Nat) :
    Monotone (A.stage x i) := by
  classical
  intro f g fg
  unfold stage
  split
  · rename_i hi
    let j := A.index.symm ⟨i,hi⟩
    change decide (P.onAt x j (fun k => f (A.index k).val)) ≤ decide (P.onAt x j (fun k => g (A.index k).val))
    apply Bool.le_iff_imp.mpr
    simp only [decide_eq_true_eq]
    unfold OrderedPorts.onAt
    split
    · intro h b
      exact (P.port j b).value_mono x (fun k => fg (A.index k).val) (h b)
    · rintro ⟨b,hb⟩
      exact ⟨b,(P.port j b).value_mono x (fun k => fg (A.index k).val) hb⟩
  · exact le_rfl

theorem GateSchedule.evaluation {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (ao : IsAO2 26 C) (x : Fin 26 → Bool) :
    ∀ (k : Nat) (i : Fin 5), (A.index i).val < k →
      evalSchedule (A.stage x) none k (A.index i).val = gateVal 26 C (gateOrder count i).val x := by
  classical
  intro k
  induction k with
  | zero => intro i impossible; omega
  | succ k ih =>
    intro i hi
    rw [evalSchedule]
    simp only [reduceCtorEq, ite_false]
    by_cases now : (A.index i).val = k
    · rw [now, Function.update_self]
      have bound : k < 5 := now ▸ (A.index i).isLt
      have indexEq : A.index.symm ⟨k,bound⟩ = i := by
        apply A.index.injective
        rw [Equiv.apply_symm_apply]
        exact Fin.ext now.symm
      rw [stage, dite_eq_left bound, indexEq]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, ← P.onAt_actual ao x i]
      have agree b : (P.port i b).value x (fun j => evalSchedule (A.stage x) none k (A.index j).val) ↔
          (P.port i b).value x (fun j => gateVal 26 C (gateOrder count j).val x) := by
        apply PortChoice.value_congr
        intro j read
        apply ih
        exact now ▸ A.respects read
      unfold OrderedPorts.onAt
      split
      · exact forall_congr' agree
      · exact exists_congr agree
    · rw [Function.update_of_ne now]
      exact ih i (by omega)

def topOn {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (l : Fin 13) (x : Fin 26 → Bool)
    (past : Nat → Bool) : Prop :=
  (x (ln l) = true ∨ ∃ j, topRoute S count l (S.center (S.index l)) j ∧ past (A.index j).val = true) ∧
  ((∃ v ∈ leaf S l, x v = true) ∨
    ∃ j, topRoute S count l (1-S.center (S.index l)) j ∧ past (A.index j).val = true)

noncomputable def GateSchedule.output {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (x : Fin 26 → Bool) (past : Nat → Bool) : Bool := by
  classical
  exact decide (∃ l, topOn A l x past)

theorem GateSchedule.output_mono {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (x : Fin 26 → Bool) : Monotone (A.output x) := by
  classical
  intro f g le
  apply Bool.le_iff_imp.mpr
  simp only [output, decide_eq_true_eq]
  have lift (a : Prop) (q : Fin 5 → Prop) :
      (a ∨ ∃ j, q j ∧ f (A.index j).val = true) → a ∨ ∃ j, q j ∧ g (A.index j).val = true := by
    rintro (raw | ⟨j,promote,h⟩)
    · exact Or.inl raw
    · refine Or.inr ⟨j,promote,?_⟩
      have enough := le (A.index j).val
      rw [h] at enough
      exact Bool.le_iff_imp.mp enough rfl
  rintro ⟨l,a,b⟩
  exact ⟨l,lift _ _ a,lift _ _ b⟩

private theorem graphFun_iff_edge (x : Fin 26 → Bool) : graphFun plane ∅ x = true ↔
    ∃ p l : Fin 13, plane.Adj (pt p) (ln l) ∧ x (pt p) = true ∧ x (ln l) = true := by
  have colors : ∀ u v, plane.Adj u v → (u.val < 13 ↔ ¬ v.val < 13) := by decide
  have point v (h : v.val < 13) : ∃ p : Fin 13, v = pt p := ⟨⟨v.val,h⟩,Fin.ext rfl⟩
  have line v (h : ¬ v.val < 13) : ∃ l : Fin 13, v = ln l := by
    refine ⟨⟨v.val-13,by have := v.isLt; omega⟩, Fin.ext ?_⟩
    change v.val = 13+(v.val-13)
    omega
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
  constructor
  · intro ⟨u,v,adj,onU,onV⟩
    by_cases up : u.val < 13
    · obtain ⟨p,rfl⟩ := point u up
      obtain ⟨l,rfl⟩ := line v ((colors _ _ adj).mp up)
      exact ⟨p,l,adj,onU,onV⟩
    · obtain ⟨l,rfl⟩ := line u up
      obtain ⟨p,rfl⟩ := point v (by by_contra h; exact up ((colors _ _ adj).mpr h))
      exact ⟨p,l,adj.symm,onV,onU⟩
  · rintro ⟨p,l,adj,onP,onL⟩
    exact ⟨_,_,adj,onP,onL⟩

theorem GateSchedule.output_edge_free {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (x : Fin 26 → Bool) (off : graphFun plane ∅ x = false) :
    A.output x (evalSchedule (A.stage x) none 5) = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro wrong
  rw [output, decide_eq_true_eq] at wrong
  obtain ⟨l,h⟩ := wrong
  unfold topOn at h
  simp only [A.evaluation least.1 x 5 _ (Fin.isLt _)] at h
  exact Bool.false_ne_true (off.symm.trans ((topData (S.index l).property).2.2 x
    ((top_value S least top empty count l x).mpr h)))

theorem GateSchedule.output_incidence {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) {p l : Fin 13} (adj : plane.Adj (pt p) (ln l)) :
    let x := pairInput (pt p) (ln l)
    A.output x (evalSchedule (A.stage x) none 5) = true := by
  classical
  dsimp only
  rw [output, decide_eq_true_eq]
  obtain ⟨j,on⟩ := (test_obligations S least).1 p l adj
  refine ⟨j,?_⟩
  unfold topOn
  simp only [A.evaluation least.1 _ 5 _ (Fin.isLt _)]
  exact (top_value S least top empty count j _).mp on

theorem GateSchedule.retained_accept {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) {p l : Fin 13} (kept : pt p ∈ leaf S l) :
    A.output (pairInput (pt p) (ln l)) (fun _ => false) = true := by
  classical
  rw [output, decide_eq_true_eq]
  exact ⟨l,Or.inl (pairInput_right _ _), Or.inl ⟨pt p,kept,pairInput_left _ _⟩⟩

theorem GateSchedule.muted_tests {S : Stars C} {count : (charged plane C).card = 5}
    {P : OrderedPorts S count} (A : GateSchedule P) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (m : Nat)
    (quiet : ∀ p l : Fin 13, plane.Adj (pt p) (ln l) → pt p ∉ leaf S l →
      let x := pairInput (pt p) (ln l)
      A.stage x m (evalSchedule (A.stage x) none m) = false) :
    (∀ p l : Fin 13, plane.Adj (pt p) (ln l) →
      let x := pairInput (pt p) (ln l)
      A.output x (evalSchedule (A.stage x) (some m) 5) = true) ∧
    (∀ x : Fin 26 → Bool, graphFun plane ∅ x = false →
      A.output x (evalSchedule (A.stage x) (some m) 5) = false) := by
  constructor
  · intro p l adj
    dsimp only
    let x := pairInput (pt p) (ln l)
    by_cases h : pt p ∈ leaf S l
    · have monotone := A.output_mono x
        (show (fun _ : Nat => false) ≤ evalSchedule (A.stage x) (some m) 5 from fun _ => Bool.false_le _)
      exact Bool.le_iff_imp.mp monotone (A.retained_accept h)
    · rw [mute_when_off _ (quiet p l adj h)]
      exact A.output_incidence least top empty adj
  · intro x off
    have le := A.output_mono x (mute_monotone _ (A.stage_monotone x) m 5)
    have h := A.output_edge_free least top empty x off
    apply Bool.eq_false_iff.mpr
    intro on
    exact Bool.false_ne_true (h.symm.trans (Bool.le_iff_imp.mp le on))

def sampleInput (index : Nat) (v : Fin 26) : Bool := (Formula.samples[index]!).contains v.val

def edgePairAt (k : Nat) : Fin 13 × Fin 13 :=
  let (p,l) := Formula.edgeRows[k]!
  (Fin.ofNat 13 p, Fin.ofNat 13 (l-13))

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 20000 in
theorem positive_sample_exact : ∀ k : Fin 52,
    let (p,l) := edgePairAt k.val
    incident p l ∧ ∀ v : Fin 26, sampleInput k.val v = pairInput (pt p) (ln l) v := by
  decide +kernel

def edgePairs : List (Fin 13 × Fin 13) := (List.range 52).map edgePairAt

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 20000 in
theorem edge_pairs_exact : edgePairs.toFinset = positives ∧ edgePairs.Nodup := by
  decide +kernel

/-- The Boolean flags the counter receives have the same cardinality as the
    uncovered incidences of the real circuit. -/
theorem residual_flags_count (S : Stars C) (ao : IsAO2 26 C) :
    (edgePairs.filter fun (p,l) => decide (pt p ∉ leaf S l)).length = (Ustar plane C).card := by
  classical
  let missing (e : Fin 13 × Fin 13) := decide (pt e.1 ∉ leaf S e.2)
  change (edgePairs.filter missing).length = _
  have nodup := edge_pairs_exact.2.filter missing
  rw [← List.toFinset_card_of_nodup nodup, ← residual_card S ao]
  congr 1
  ext e
  simp [residualPairs, edge_pairs_exact.1, missing]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 20000 in
private theorem negative_sample_test : ∀ k : Fin 80, ∀ p l : Fin 13,
    incident p l → (sampleInput (k.val+52) (pt p) && sampleInput (k.val+52) (ln l)) = false := by
  decide +kernel

theorem negative_sample_edge_free (k : Fin 80) : graphFun plane ∅ (sampleInput (k.val+52)) = false := by
  apply Bool.eq_false_iff.mpr
  intro on
  obtain ⟨p,l,adj,hp,hl⟩ := (graphFun_iff_edge _).mp on
  have off := negative_sample_test k p l ((adj_coordinates p l).mpr adj)
  rw [hp,hl] at off
  cases off

#print axioms GateSchedule.evaluation
#print axioms GateSchedule.rawFirst_top_port
#print axioms GateSchedule.masks_covered
#print axioms GateSchedule.output_incidence
#print axioms GateSchedule.output_edge_free
#print axioms GateSchedule.muted_tests
#print axioms negative_sample_edge_free
#print axioms positive_sample_exact
#print axioms residual_flags_count

end SixEdge.Plane
