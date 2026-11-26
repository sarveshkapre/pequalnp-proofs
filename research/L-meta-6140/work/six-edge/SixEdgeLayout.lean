import SixEdgePortChoices
import SixEdgeFormula
import SixEdgeFirstAnd
import SixEdgeOrder
import SixEdgeSymmetry

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open ResidualDegree PlaneFour

variable {C : Circuit}

def PortHost.index : PortHost → Nat
  | .singleton v => v.val
  | .leaf l => 26+l.val

/-- The centre and leaf selectors omit a promotion that precedes every dirty
    AND, since its raw contribution is already present. -/
def topRoute (S : Stars C) (count : (charged plane C).card = 5)
    (l : Fin 13) (b : Fin 2) (j : Fin 5) : Prop :=
  let g := (gateOrder count j).val
  g ∈ portPromotions plane C (opnd C (S.index l).val b) ∧ ∃ k ∈ junk plane C, k < g

theorem top_route_valid (S : Stars C) (count : (charged plane C).card = 5)
    {l : Fin 13} {b : Fin 2} {j : Fin 5} (h : topRoute S count l b j) :
    (gateOrder count j).val ∈ exceptional plane C ∧
      (wireRaw count j).Nonempty ∧ wireRaw count j ⊆ side (n := 26) C (S.index l).val b := by
  classical
  obtain ⟨ex, someRaw, reach⟩ := Finset.mem_filter.mp h.1
  exact ⟨ex, someRaw, fun v hv => reach_mem_orIn v
    ((orReaches_reach _ _ reach).1.trans (mem_orIn_reach v hv))⟩

theorem top_route_value (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (count : (charged plane C).card = 5)
    (l : Fin 13) (b : Fin 2) (x : Fin 26 → Bool) :
    val C (List.ofFn x) (opnd C (S.index l).val b) = true ↔
      (∃ v ∈ side (n := 26) C (S.index l).val b, x v = true) ∨
      ∃ j : Fin 5, topRoute S count l b j ∧ gateVal 26 C (gateOrder count j).val x = true := by
  classical
  rw [top_port_value least.1 top empty (S.index l).property b x]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨g, mem, earlier, fire⟩
    have ex : g ∈ exceptional plane C := (Finset.mem_filter.mp mem).1
    let k : ↥(charged plane C) := ⟨g, Finset.mem_union_right _ ex⟩
    obtain ⟨j, eq⟩ := (gateOrder count).surjective k
    have e : (gateOrder count j).val = g := congrArg Subtype.val eq
    exact ⟨j, ⟨e.symm ▸ mem, e.symm ▸ earlier⟩, e.symm ▸ fire⟩
  · rintro ⟨j, ⟨mem, earlier⟩, fire⟩
    exact ⟨_, mem, earlier, fire⟩

/-- Evaluate the top in terms of the raw star and its two selector sets. -/
theorem top_value (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (count : (charged plane C).card = 5)
    (l : Fin 13) (x : Fin 26 → Bool) :
    gateVal 26 C (S.index l).val x = true ↔
      (x (ln l) = true ∨ ∃ j : Fin 5, topRoute S count l (S.center (S.index l)) j ∧
        gateVal 26 C (gateOrder count j).val x = true) ∧
      ((∃ v ∈ leaf S l, x v = true) ∨ ∃ j : Fin 5, topRoute S count l (1-S.center (S.index l)) j ∧
        gateVal 26 C (gateOrder count j).val x = true) := by
  have data := topData (S.index l).property
  have pair : ∀ t c : Fin 2, c = t ∨ c = 1-t := by decide
  let b := S.center (S.index l)
  have swap : (∀ c : Fin 2, val C (List.ofFn x) (opnd C (S.index l).val c) = true) ↔
      (val C (List.ofFn x) (opnd C (S.index l).val b) = true ∧
       val C (List.ofFn x) (opnd C (S.index l).val (1-b)) = true) := by
    constructor
    · exact fun h => ⟨h _, h _⟩
    · intro h c
      rcases pair b c with rfl | rfl
      · exact h.1
      · exact h.2
  rw [andValOperands least.1 data.1 data.2.1, swap,
    top_route_value S least top empty count l b x,
    top_route_value S least top empty count l (1-b) x]
  change (_ ∨ _) ∧ (_ ∨ _) ↔ _
  simp only [b, S.singleton, Finset.mem_singleton, exists_eq_left, leaf]

private def allPoints : Fin 26 → Bool := fun v => decide (v.val < 13)

private theorem allPoints_edge_free : graphFun plane ∅ allPoints = false := by decide

/-- If the first dirty AND uses only points, propagating it through OR gates to
    a centre would fire a top on the all-points input. -/
theorem first_points_avoid_centre (S : Stars C) (least : IsLeastAO plane C)
    (top : TopForm plane C) (empty : centreless plane C = ∅)
    {g : Nat} (dirty : g ∈ junk plane C)
    (first : ∀ k ∈ charged plane C, ¬ k < g)
    (points : ∀ (b : Fin 2) v, v ∈ side (n := 26) C g b → v.val < 13)
    (l : Fin 13) : ¬ Relation.ReflTransGen (OrStep 26 C)
      (opnd C (S.index l).val (S.center (S.index l))) (26+g) := by
  intro path
  have data := junkData dirty
  have firstOn : gateVal 26 C g allPoints = true := by
    apply (andValOperands least.1 data.1 data.2.1 _).mpr
    intro b
    apply ((first_port S least top dirty first b).2 allPoints).mpr
    rcases matches_ports S least top (Finset.mem_union_left _ dirty) b with ⟨k,hk,hlt,_⟩ | ⟨nonempty, _⟩
    · exact (first k hk hlt).elim
    · obtain ⟨v,hv⟩ := nonempty
      exact ⟨v,hv,decide_eq_true (points b v hv)⟩
  have centreOn : val C (List.ofFn allPoints) (opnd C (S.index l).val (S.center (S.index l))) = true :=
    orStep_up (n := 26) (by simp) path firstOn
  obtain ⟨v, vLeaf⟩ := leaf_nonempty S empty l
  obtain ⟨p, rfl⟩ := leaf_point S least.1 vLeaf
  have leafOn : val C (List.ofFn allPoints) (opnd C (S.index l).val (1-S.center (S.index l))) = true :=
    reach_var_val allPoints _ _ (mem_orIn_reach _ vLeaf) (decide_eq_true p.isLt)
  have topData := topData (S.index l).property
  have topOn : gateVal 26 C (S.index l).val allPoints = true := by
    apply (andValOperands least.1 topData.1 topData.2.1 _).mpr
    intro b
    have pair : ∀ t c : Fin 2, c = t ∨ c = 1-t := by decide
    rcases pair (S.center (S.index l)) b with rfl | rfl
    · exact centreOn
    · exact leafOn
  exact Bool.false_ne_true (allPoints_edge_free.symm.trans (topData.2.2 allPoints topOn))

/-- Normalise the coordinates used by the active first-AND refinements. With
    a centre route fixed, the AND's line becomes line zero or line one. With
    no centre route, put its chosen residual incidence at row zero. -/
theorem active_first_coordinates (S : Stars C) (least : IsLeastAO plane C)
    (top : TopForm plane C) {g : Nat} (dirty : g ∈ junk plane C)
    (first : ∀ k ∈ charged plane C, ¬ k < g) {p l : Fin 13} (edge : incident p l)
    (on : gateVal 26 C g (pairInput (pt p) (ln l)) = true) (centre : Option (Fin 13)) :
    ∃ r : Relabelling,
      (match centre with | none => r.point p = 0 ∧ r.line l = 0 | some c => r.line c = 0) ∧
      ((∀ (b : Fin 2) v, v ∈ side (n := 26) C g b → v.val < 13) ∨
        ∃ b : Fin 2, side (n := 26) C g b = {ln l} ∧
          (∀ v ∈ side (n := 26) C g (1-b), v.val < 13) ∧
          (∃ v ∈ side (n := 26) C g (1-b), ¬ plane.Adj v (ln l)) ∧
          (r.line l = 0 ∨ r.line l = 1)) := by
  have shape := active_first_and S least top dirty first on
  cases centre with
  | none =>
    obtain ⟨r, hp, hl⟩ := anchor_incidence p l edge
    refine ⟨r, ⟨hp,hl⟩, ?_⟩
    rcases shape with points | ⟨b,ls,ps,witness⟩
    · exact Or.inl points
    · exact Or.inr ⟨b,ls,ps,witness,Or.inl hl⟩
  | some c =>
    rcases shape with points | ⟨b,ls,ps,witness⟩
    · exact ⟨translate (-c), by simp [translate], Or.inl points⟩
    · by_cases eq : l = c
      · subst c
        have zero : (translate (-l)).line l = 0 := by simp [translate]
        exact ⟨translate (-l), zero, Or.inr ⟨b,ls,ps,witness,Or.inl zero⟩⟩
      · obtain ⟨r,hc,hl⟩ := anchor_lines c l eq
        exact ⟨r, hc, Or.inr ⟨b,ls,ps,witness,Or.inr hl⟩⟩

theorem centre_mask (S : Stars C) (count : (charged plane C).card = 5) (j : Fin 5) :
    centerAt count S.center j = true ↔ ∃ l : Fin 13, topRoute S count l (S.center (S.index l)) j := by
  classical
  constructor
  · intro route
    obtain ⟨past, a, reaches⟩ := of_decide_eq_true route
    obtain ⟨l,rfl⟩ := S.index.surjective a
    exact ⟨l, reaches, past⟩
  · rintro ⟨l, reaches, past⟩
    exact decide_eq_true ⟨past, S.index l, reaches⟩

def swapPorts (flip : Bool) : Fin 2 ≃ Fin 2 :=
  if flip then Equiv.swap 0 1 else Equiv.refl _

structure OrderedPorts (S : Stars C) (count : (charged plane C).card = 5) where
  port : Fin 5 → Fin 2 → PortChoice
  order : Fin 5 → Fin 2 ≃ Fin 2
  ascending : ∀ i, (port i 0).mode ≤ (port i 1).mode
  valid : ∀ i b, (port i b).valid S count i
  raw : ∀ i b, (port i b).raw count = side (n := 26) C (gateOrder count i).val (order i b)
  direct : ∀ i b j, opnd C (gateOrder count i).val (order i b) = 26+(gateOrder count j).val →
    port i b = .direct j
  reach : ∀ i b j, (port i b).reads j → Relation.ReflTransGen (OrStep 26 C)
    (opnd C (gateOrder count i).val (order i b)) (26+(gateOrder count j).val)
  direct_wire : ∀ i b j, port i b = .direct j →
    opnd C (gateOrder count i).val (order i b) = 26+(gateOrder count j).val
  promotions : ∀ i b a, port i b = .atom a → ∀ j, (gateOrder count j).val ∈
    portPromotions plane C (opnd C (gateOrder count i).val (order i b)) → j ∈ a.promoted
  value : ∀ i b x, val C (List.ofFn x) (opnd C (gateOrder count i).val (order i b)) = true ↔
    (port i b).value x (fun j => gateVal 26 C (gateOrder count j).val x)

theorem ordered_ports (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (count : (charged plane C).card = 5) : Nonempty (OrderedPorts S count) := by
  classical
  choose choices valid raw direct reach direct_wire promotions value using (select_port S least top count)
  let order (i : Fin 5) : Fin 2 ≃ Fin 2 := swapPorts (decide ((choices i 1).mode < (choices i 0).mode))
  refine ⟨⟨fun i b => choices i (order i b), order, ?_, fun i b => valid i (order i b),
    fun i b => raw i (order i b), fun i b => direct i (order i b),
    fun i b => reach i (order i b), fun i b => direct_wire i (order i b),
    fun i b => promotions i (order i b), fun i b => value i (order i b)⟩⟩
  intro i
  by_cases swap : (choices i 1).mode < (choices i 0).mode
  · simpa [order, swapPorts, swap] using swap.le
  · simpa [order, swapPorts, swap] using Nat.le_of_not_gt swap

theorem OrderedPorts.read_dirty {S : Stars C} {count : (charged plane C).card = 5}
    (P : OrderedPorts S count) (least : IsLeastAO plane C) (empty : centreless plane C = ∅)
    (j : Fin 5) (dirty : dirtyAt count j = true) :
    ∃ i : Fin 5, j < i ∧ ∃ b : Fin 2, P.port i b = .direct j := by
  classical
  have hj : (gateOrder count j).val ∈ junk plane C := of_decide_eq_true dirty
  obtain ⟨bound, _, x, fire, off⟩ := junkData hj
  obtain ⟨k, reads⟩ := reader_of_not_below least bound
    (fun below => Bool.false_ne_true (off.symm.trans (below x fire)))
  let r : ↥(charged plane C) := ⟨k, dirty_reader_is_charged least.1 empty hj reads⟩
  obtain ⟨i, hi⟩ := (gateOrder count).surjective r
  have eq : (gateOrder count i).val = k := congrArg Subtype.val hi
  obtain ⟨b, hb⟩ := inputsAsOpnd least.1 reads.1 reads.2.2
  have earlier : j < i := (gateOrder count).lt_iff_lt.mp (by
    change (gateOrder count j).val < (gateOrder count i).val
    rw [eq]
    exact reads.2.1)
  refine ⟨i, earlier, (P.order i).symm b, P.direct _ _ _ ?_⟩
  rw [Equiv.apply_symm_apply, eq]
  exact hb.symm

noncomputable def rawSlots (count : (charged plane C).card = 5) (i : Fin 5) : Bool := by
  classical
  exact decide (rawOnly plane C (26+(gateOrder count i).val))

/-- Moving raw-only ORs before the dirty gates preserves every selected
    direct use and promotion. -/
theorem OrderedPorts.reorder_preserves_read {S : Stars C} {count : (charged plane C).card = 5}
    (P : OrderedPorts S count) (least : IsLeastAO plane C) {i j : Fin 5} {b : Fin 2}
    (used : (P.port i b).reads j) : reordered (rawSlots count) j < reordered (rawSlots count) i := by
  classical
  apply reordered_keeps_reads _ (PortChoice.reads_earlier (P.valid i b) used)
  intro pure
  have iRaw : rawOnly plane C (26+(gateOrder count i).val) := of_decide_eq_true pure
  rcases Finset.mem_union.mp (gateOrder count i).property with dirty | other
  · exact (dirty_not_rawOnly dirty iRaw).elim
  · obtain ⟨len, hop⟩ := orData other
    let gate := (gateOrder count i).val
    have step : OrStep 26 C (26+gate) (opnd C gate (P.order i b)) :=
      ⟨gate,len,rfl,hop.1,opndMem least.1 len _,opndBound least.1 len _⟩
    exact decide_eq_true (rawOnly_reaches iRaw (.head step (P.reach i b j used)))

/-- All primary variables given their physical meaning for the original ordering.
    Natural-number arguments occur only at the bounded indices allocated by the encoder. -/
noncomputable def OrderedPorts.primary {S : Stars C} {count : (charged plane C).card = 5}
    (P : OrderedPorts S count) : Formula.Input → Bool := by
  classical
  let slot (i : Nat) : Fin 5 := Fin.ofNat 5 i
  let port (i b : Nat) : PortChoice := P.port (slot i) (Fin.ofNat 2 b)
  let line (l : Nat) : Fin 13 := Fin.ofNat 13 (l-13)
  exact fun input => match input with
    | .leaf l p => decide ((Fin.ofNat 26 p) ∈ leaf S (line l))
    | .direct i b j => match port i b with
      | .direct k => k == slot j
      | .atom _ => false
    | .atomMode i b => match port i b with
      | .direct _ => false
      | .atom _ => true
    | .atom i b v => match port i b with
      | .direct _ => false
      | .atom a => decide ((Fin.ofNat 26 v) ∈ a.raw)
    | .host i b h => match port i b with
      | .direct _ => false
      | .atom a => a.host.index == h
    | .promotion i b j => match port i b with
      | .direct _ => false
      | .atom a => decide (slot j ∈ a.promoted)
    | .topCentre l j => decide (topRoute S count (line l) (S.center (S.index (line l))) (slot j))
    | .topLeaf l j => decide (topRoute S count (line l) (1-S.center (S.index (line l))) (slot j))

#print axioms top_route_value
#print axioms first_points_avoid_centre
#print axioms active_first_coordinates
#print axioms ordered_ports
#print axioms OrderedPorts.read_dirty
#print axioms OrderedPorts.reorder_preserves_read

end SixEdge.Plane
