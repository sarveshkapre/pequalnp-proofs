import SixEdgeCases
import PEqualNP.Outside.L_meta_7465
import PEqualNP.MetaComplexity.Helpers.LiveSize

/-! The two case masks of an actual circuit. The circuit remains in its
original gate order. ORs before its first dirty AND need no centre route. -/
namespace SixEdge

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.LiveSize
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev exceptional (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  orN G C \ lam G C

abbrev charged (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  junk G C ∪ exceptional G C

theorem disjoint_charged : Disjoint (junk G C) (exceptional G C) := by
  apply Finset.disjoint_left.mpr
  intro g hj ho
  exact GateOp.noConfusion ((junkData hj).2.1.symm.trans (orData ho).2.1)

theorem charged_card (two : (junk G C).card = 2) (three : (exceptional G C).card = 3) :
    (charged G C).card = 5 := by
  rw [Finset.card_union_of_disjoint disjoint_charged, two, three]

theorem gate_live (least : IsLeastAO G C) {j : ℕ} (bound : j < C.gates.length) :
    j ∈ PEqualNP.FactorSubst.liveGates n C := by
  obtain ⟨D, ao, size, correct⟩ := live_main n C.gates.length C rfl least.1
  have same : circuitFun n D = graphFun G ∅ := by
    rw [← least.2.1]
    funext x
    exact correct x
  have lower := least.2.2 D ao same
  rw [size] at lower
  by_contra missing
  have sub : PEqualNP.FactorSubst.liveGates n C ⊂ Finset.range C.gates.length := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun i hi => Finset.mem_range.mpr ((mem_live n C i).mp hi).1, ?_⟩
    intro eq
    exact missing (eq ▸ Finset.mem_range.mpr bound)
  have strict := Finset.card_lt_card sub
  simp only [Finset.card_range] at strict
  exact (Nat.not_lt_of_ge lower) strict

/-- If a charged wire always has the value of an earlier wire, removing its
    gate preserves fan-in two as well as the circuit function. -/
theorem gate_not_copy (least : IsLeastAO G C) {j w : ℕ} (bound : j < C.gates.length)
    (earlier : w < n+j)
    (same : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+j) = val C (List.ofFn x) w) :
    False := by
  let D := LiftFix.del n j w C
  have valid : IsAO2 n D := LiftFix.del_AO n j w C least.1 earlier
  have correct : circuitFun n D = graphFun G ∅ := by
    rw [← least.2.1]
    exact LiftFix.del_fun n j w C bound earlier
      (LiftFix.readsBack_take n C least.1.2.1 j) same
  have ge := least.2.2 D valid correct
  have smaller := LiftFix.del_length n j w C bound
  change C.gates.length ≤ D.gates.length at ge
  change D.gates.length + 1 = C.gates.length at smaller
  omega

theorem reader_of_not_below (least : IsLeastAO G C) {j : ℕ} (bound : j < C.gates.length)
    (dirty : ¬ BelowF G C j) : ∃ k, RR n C j k := by
  rcases (mem_live n C j).mp (gate_live least bound) with ⟨_, out, same | path⟩
  · exfalso
    apply dirty
    have eq : C.output = n+j := by omega
    intro x on
    change val C (List.ofFn x) (n+j) = true at on
    rw [← eq] at on
    change circuitFun n C x = true at on
    rw [least.2.1] at on
    exact on
  · obtain ⟨k, read, _⟩ := Relation.TransGen.head'_iff.mp path
    exact ⟨k, read⟩

theorem lies_under_and (least : IsLeastAO G C) {g : ℕ} (bound : g < C.gates.length)
    (notBelow : ¬ BelowF G C g) :
    ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
      ∃ b : Fin 2, Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+g) := by
  let remaining := C.gates.length - g
  have h : remaining = C.gates.length - g := rfl
  clear_value remaining
  induction remaining using Nat.strong_induction_on generalizing g with
  | ind remaining ih =>
    obtain ⟨k, kl, lt, reads⟩ := reader_of_not_below least bound notBelow
    rcases least.1.1 _ (gateAt_mem kl) with hand | hor
    · obtain ⟨i, eq⟩ := inputsAsOpnd least.1 kl reads
      exact ⟨k, kl, hand, i, by rw [← eq]⟩
    · have step : OrStep n C (n+k) (n+g) := ⟨k, kl, rfl, hor, reads, by omega⟩
      have kNotBelow : ¬ BelowF G C k := by
        intro safe
        apply notBelow
        intro x on
        exact safe x (orStep_up (n := n) (by simp) (.single step) on)
      obtain ⟨a, al, aop, b, path⟩ :=
        ih (C.gates.length - k) (by omega) kl kNotBelow rfl
      exact ⟨a, al, aop, b, path.tail step⟩

/-- Reading a dirty AND must use another charged gate. An AND reader has an
    empty raw operand, so it cannot be a centred top. An OR reader fails the
    two-nonempty-operands requirement for Lambda. -/
theorem dirty_reader_is_charged (ao : IsAO2 n C) (empty : centreless G C = ∅)
    {j k : ℕ} (dirty : j ∈ junk G C) (read : RR n C j k) : k ∈ charged G C := by
  classical
  obtain ⟨jl, ja, x, on, off⟩ := junkData dirty
  obtain ⟨kl, lt, uses⟩ := read
  obtain ⟨i, eq⟩ := inputsAsOpnd ao kl uses
  have zero : side (n := n) C k i = ∅ := by
    change orIn n C (opnd C k i) = ∅
    rw [← eq, andRawEmpty ja]
  rcases ao.1 _ (gateAt_mem kl) with hand | hor
  · apply Finset.mem_union_left
    have notBelow : ¬ BelowF G C k := by
      intro below
      have ht : k ∈ tops G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr kl, hand, below⟩
      have cl : k ∈ centreless G C := Finset.mem_filter.mpr
        ⟨ht, by fin_cases i; exact Or.inl zero; exact Or.inr zero⟩
      simp [empty] at cl
    unfold BelowF at notBelow
    push Not at notBelow
    obtain ⟨y, on', off'⟩ := notBelow
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr kl, hand, kl, y, on',
      Bool.eq_false_iff.mpr off'⟩
  · apply Finset.mem_union_right
    have notBelow : ¬ BelowF G C k := by
      intro below
      have on' : gateVal n C k x = true :=
        (val_or (n := n) (by simp) kl hor).mpr ⟨n+j, uses, by omega, on⟩
      exact Bool.false_ne_true (off.symm.trans (below x on'))
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr kl, hor, notBelow⟩
    · intro lamMem
      obtain ⟨_, l, r, _⟩ := Finset.mem_filter.mp lamMem
      fin_cases i
      · exact l.ne_empty zero
      · exact r.ne_empty zero

noncomputable def gateOrder (count : (charged G C).card = 5) :
    Fin 5 ≃o ↥(charged G C) :=
  (charged G C).orderIsoOfFin count

noncomputable def dirtyAt (count : (charged G C).card = 5) (i : Fin 5) : Bool := by
  classical
  exact decide ((gateOrder count i).val ∈ junk G C)

theorem dirty_slots_card (count : (charged G C).card = 5) (two : (junk G C).card = 2) :
    (Finset.univ.filter fun i => dirtyAt count i = true).card = 2 := by
  classical
  rw [← two]
  apply Finset.card_bij (fun i _ => (gateOrder count i).val)
  · intro i hi
    exact of_decide_eq_true (Finset.mem_filter.mp hi).2
  · intro i _ j _ eq
    exact (gateOrder count).injective (Subtype.ext eq)
  · intro j hj
    let x : ↥(charged G C) := ⟨j,Finset.mem_union_left _ hj⟩
    let i := (gateOrder count).symm x
    have eq : gateOrder count i = x := (gateOrder count).apply_symm_apply x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true (eq ▸ hj)⟩,
      congrArg Subtype.val eq⟩

theorem last_is_or (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (count : (charged G C).card = 5) : dirtyAt count 4 = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro isDirty
  have hj : (gateOrder count 4).val ∈ junk G C := of_decide_eq_true isDirty
  obtain ⟨k, read⟩ := reader_of_not_below least (junkData hj).1
    (fun safe => by
      obtain ⟨_, _, x, on, off⟩ := junkData hj
      exact Bool.false_ne_true (off.symm.trans (safe x on)))
  let r : ↥(charged G C) := ⟨k,dirty_reader_is_charged least.1 empty hj read⟩
  let later := (gateOrder count).symm r
  have eq : gateOrder count later = r := (gateOrder count).apply_symm_apply r
  have greater : (4 : Fin 5) < later := by
    apply (gateOrder count).lt_iff_lt.mp
    change (gateOrder count 4).val < (gateOrder count later).val
    rw [eq]
    exact read.2.1
  omega

/-- A non-raw contribution to a port has an earlier dirty AND in its OR cone. -/
theorem earlier_dirty_of_promotion (ao : IsAO2 n C) (top : TopForm G C)
    {a g : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (b : Fin 2) {x : Fin n → Bool}
    (ex : g ∈ exceptional G C)
    (reach : OrReaches n C (opnd C a b) g) (on : gateVal n C g x = true)
    (noRaw : ¬ ∃ t ∈ side (n := n) C a b, x t = true) :
    ∃ j ∈ junk G C, j < g := by
  have sub := (orReaches_reach g (opnd C a b) reach).1
  obtain ⟨w, path, fires, input | ⟨j, jl, eq, notOr⟩⟩ :=
    or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) (n+g) on
  · let t : Fin n := ⟨w, input⟩
    exact (noRaw ⟨t, reach_mem_orIn t (sub.trans path),
      (val_ofFn C x t).symm.trans fires⟩).elim
  · rw [eq] at path
    have aj : (gateAt C j).op = GateOp.and := by
      rcases ao.1 _ (gateAt_mem jl) with and | or
      · exact and
      · exact (notOr or).elim
    have safety := operandOrAndJunk ao top ha hand (reach_orReaches (sub.trans path) j rfl jl) aj
    have le := orStep_le path
    have ne : j ≠ g := fun eq => notOr (eq ▸ (orData ex).2.1)
    exact ⟨j, safety, by omega⟩

noncomputable def portPromotions (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact (exceptional G C).filter fun h => (orIn n C (n+h)).Nonempty ∧ OrReaches n C w h

theorem port_value (ao : IsAO2 n C) {a : ℕ} (bound : a < C.gates.length) (b : Fin 2)
    (raw : (side (n := n) C a b).Nonempty) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C a b) = true ↔
      (∃ t ∈ side (n := n) C a b, x t = true) ∨
      ∃ g ∈ portPromotions G C (opnd C a b), gateVal n C g x = true :=
  nonemptyPortValue (G := G) ao x _ (by have := opndBound ao bound b; omega) raw

/-- The exact top-port function. Promotions before the first dirty AND are
    already accounted for by the raw literals on the port. -/
theorem top_port_value (ao : IsAO2 n C) (top : TopForm G C) (empty : centreless G C = ∅)
    {a : ℕ} (ht : a ∈ tops G C) (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C a b) = true ↔
      (∃ t ∈ side (n := n) C a b, x t = true) ∨
      ∃ g ∈ portPromotions G C (opnd C a b),
        (∃ j ∈ junk G C, j < g) ∧ gateVal n C g x = true := by
  classical
  obtain ⟨bound, hand, _⟩ := topData ht
  rw [port_value (G := G) ao bound b (topSides empty ht b) x]
  constructor
  · rintro (raw | ⟨g, mem, on⟩)
    · exact Or.inl raw
    · by_cases raw : ∃ t ∈ side (n := n) C a b, x t = true
      · exact Or.inl raw
      · obtain ⟨ex, _, reach⟩ := Finset.mem_filter.mp mem
        exact Or.inr ⟨g, mem, earlier_dirty_of_promotion ao top bound hand b ex reach on raw, on⟩
  · rintro (raw | ⟨g, mem, _, on⟩)
    · exact Or.inl raw
    · exact Or.inr ⟨g, mem, on⟩

/-- The raw literals of a port either fit in a singleton or sit inside the
    leaf side of a centred top. These are the two families used by the encoder. -/
def FitsAtom (center : ↥(tops G C) → Fin 2) (r : Finset (Fin n)) : Prop :=
  (∃ t : Fin n, r ⊆ {t}) ∨
    ∃ a : ↥(tops G C), r ⊆ side (n := n) C a.val (1-center a)

theorem lambda_atom (center : ↥(tops G C) → Fin 2)
    (singleton : ∀ a, ∃ t : Fin n, side (n := n) C a.val (center a) = {t})
    {k : ℕ} (h : k ∈ lam G C) : FitsAtom center (orIn n C (n+k)) := by
  classical
  obtain ⟨_, _, _, a, ha, b, _, reach⟩ := Finset.mem_filter.mp h
  let t : ↥(tops G C) := ⟨a,ha⟩
  have sub : orIn n C (n+k) ⊆ side (n := n) C a b := by
    intro u hu
    exact reach_mem_orIn u ((orReaches_reach k _ reach).1.trans (mem_orIn_reach u hu))
  by_cases hb : b = center t
  · obtain ⟨v, hv⟩ := singleton t
    change orIn n C (n+k) ⊆ side C t.val b at sub
    exact Or.inl ⟨v, by simpa only [hb, hv] using sub⟩
  · exact Or.inr ⟨t, by
      have eq : b = 1-center t := by revert hb; generalize center t = i; fin_cases i <;> fin_cases b <;> decide
      exact eq ▸ sub⟩

/-- Every operand of a charged gate has a literal-and-promotions description
    or is exactly the output of an earlier charged gate. -/
theorem charged_port (least : IsLeastAO G C) (top : TopForm G C)
    (center : ↥(tops G C) → Fin 2)
    (singleton : ∀ a, ∃ t : Fin n, side (n := n) C a.val (center a) = {t})
    {g : ℕ} (hg : g ∈ charged G C) (i : Fin 2) :
    (∃ k ∈ charged G C, k < g ∧ opnd C g i = n+k) ∨
    ((side (n := n) C g i).Nonempty ∧ FitsAtom center (side (n := n) C g i) ∧
      (∀ k ∈ portPromotions G C (opnd C g i), k ∈ exceptional G C ∧ k < g ∧
        (orIn n C (n+k)).Nonempty ∧ orIn n C (n+k) ⊆ side C g i) ∧
      ∀ x, val C (List.ofFn x) (opnd C g i) = true ↔
        (∃ u ∈ side (n := n) C g i, x u = true) ∨
        ∃ k ∈ portPromotions G C (opnd C g i), gateVal n C k x = true) := by
  classical
  let w := opnd C g i
  have gl : g < C.gates.length := by
    rcases Finset.mem_union.mp hg with j | ex
    · exact (junkData j).1
    · exact (orData ex).1
  have wb : w < n+g := opndBound least.1 gl i
  by_cases direct : ∃ k ∈ charged G C, k < g ∧ w = n+k
  · exact Or.inl direct
  obtain ⟨a, al, hand, b, context⟩ : ∃ a < C.gates.length,
      (gateAt C a).op = GateOp.and ∧
      ∃ b : Fin 2, Relation.ReflTransGen (OrStep n C) (opnd C a b) w := by
    rcases Finset.mem_union.mp hg with j | ex
    · exact ⟨g, gl, (junkData j).2.1, i, .refl⟩
    · obtain ⟨a, al, hand, b, path⟩ :=
        lies_under_and least gl (Finset.mem_filter.mp (Finset.mem_sdiff.mp ex).1).2.2
      exact ⟨a, al, hand, b, path.tail ⟨g, gl, rfl, (orData ex).2.1,
        opndMem least.1 gl i, wb⟩⟩
  have raw : (orIn n C w).Nonempty := by
    by_contra empty
    obtain ⟨k, eq, dirty | ex⟩ := emptyPortSource least.1 top al hand context
      (Finset.not_nonempty_iff_eq_empty.mp empty)
    · exact direct ⟨k, Finset.mem_union_left _ dirty, by omega, eq⟩
    · exact direct ⟨k, Finset.mem_union_right _ ex, by omega, eq⟩
  have atom : FitsAtom center (orIn n C w) := by
    by_cases input : w < n
    · let t : Fin n := ⟨w,input⟩
      refine Or.inl ⟨t, fun v hv => Finset.mem_singleton.mpr (Fin.ext ?_)⟩
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with eq | ⟨_, step, _⟩
      · exact eq.symm
      · obtain ⟨j, _, eq, _, _, _⟩ := step
        omega
    · obtain ⟨k, eq⟩ : ∃ k, w = n+k := ⟨w-n, by omega⟩
      have kl : k < C.gates.length := by omega
      have regular : k ∈ lam G C := by
        by_contra notLam
        have raw' : (orIn n C (n+k)).Nonempty := eq ▸ raw
        obtain ⟨u, hu⟩ := raw'
        have hor : (gateAt C k).op = GateOp.or := by
          rcases least.1.1 _ (gateAt_mem kl) with ha | ho
          · rw [andRawEmpty ha] at hu
            exact (Finset.notMem_empty _ hu).elim
          · exact ho
        have notSafe : ¬ BelowF G C k := by
          intro safe
          have vu := reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
          exact G.irrefl ((graphFun_pair G u u).mp (safe _ vu))
        have ex : k ∈ exceptional G C := Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr kl, hor, notSafe⟩, notLam⟩
        exact direct ⟨k, Finset.mem_union_right _ ex, by omega, eq⟩
      rw [eq]
      exact lambda_atom center singleton regular
  refine Or.inr ⟨raw, atom, ?_, port_value least.1 gl i raw⟩
  intro k hk
  obtain ⟨ex, present, reach⟩ := Finset.mem_filter.mp hk
  have path := (orReaches_reach k w reach).1
  have bound := orStep_le path
  exact ⟨ex, by omega, present, fun u hu => reach_mem_orIn u (path.trans (mem_orIn_reach u hu))⟩

noncomputable def centerAt (count : (charged G C).card = 5)
    (center : ↥(tops G C) → Fin 2) (i : Fin 5) : Bool := by
  classical
  let g := (gateOrder count i).val
  exact decide ((∃ j ∈ junk G C, j < g) ∧
    ∃ a : ↥(tops G C), g ∈ portPromotions G C (opnd C a.val (center a)))

theorem center_route (count : (charged G C).card = 5)
    (center : ↥(tops G C) → Fin 2) (i : Fin 5) (on : centerAt count center i = true) :
    dirtyAt count i = false ∧ ∃ j, j < i ∧ dirtyAt count j = true := by
  classical
  obtain ⟨⟨j, hj, lt⟩, a, route⟩ := of_decide_eq_true on
  have ex : (gateOrder count i).val ∈ exceptional G C := (Finset.mem_filter.mp route).1
  have notDirty := fun h => (Finset.disjoint_left.mp disjoint_charged) h ex
  let r : ↥(charged G C) := ⟨j, Finset.mem_union_left _ hj⟩
  let earlier := (gateOrder count).symm r
  have eq : gateOrder count earlier = r := (gateOrder count).apply_symm_apply r
  refine ⟨decide_eq_false notDirty, earlier, ?_, ?_⟩
  · apply (gateOrder count).lt_iff_lt.mp
    change (gateOrder count earlier).val < (gateOrder count i).val
    rwa [eq]
  · exact decide_eq_true (eq ▸ hj)

theorem circuit_case (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (two : (junk G C).card = 2) (three : (exceptional G C).card = 3)
    (center : ↥(tops G C) → Fin 2) :
    let count := charged_card two three
    (ofSlots (dirtyAt count), ofSlots (centerAt count center)) ∈ cases :=
  covers _ _ (dirty_slots_card _ two) (last_is_or least empty _) (center_route _ center)

#print axioms circuit_case

end SixEdge
