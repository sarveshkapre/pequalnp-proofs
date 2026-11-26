import SixEdgePlane

/-! Principal variables for a charged gate's two operands. These choices are
made from physical wires before any symmetry relabelling or gate muting. -/
namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open ResidualDegree

inductive PortHost where
  | singleton (v : Fin 26)
  | leaf (l : Fin 13)

variable {C : Circuit}

def PortHost.support (S : Stars C) : PortHost → Finset (Fin 26)
  | .singleton v => {v}
  | .leaf l => SixEdge.Plane.leaf S l

structure AtomChoice where
  raw : Finset (Fin 26)
  host : PortHost
  promoted : Finset (Fin 5)

inductive PortChoice where
  | direct (j : Fin 5)
  | atom (a : AtomChoice)

def PortChoice.mode : PortChoice → Nat
  | .atom _ => 0
  | .direct j => j.val + 1

def PortChoice.value (p : PortChoice) (x : Fin 26 → Bool) (past : Fin 5 → Bool) : Prop :=
  match p with
  | .direct j => past j = true
  | .atom a => (∃ v ∈ a.raw, x v = true) ∨ ∃ j ∈ a.promoted, past j = true

def PortChoice.reads (p : PortChoice) (j : Fin 5) : Prop :=
  match p with
  | .direct k => j = k
  | .atom a => j ∈ a.promoted

noncomputable def wireRaw (count : (charged plane C).card = 5) (j : Fin 5) : Finset (Fin 26) :=
  orIn 26 C (26+(gateOrder count j).val)

noncomputable def PortChoice.raw (count : (charged plane C).card = 5) : PortChoice → Finset (Fin 26)
  | .direct j => wireRaw count j
  | .atom a => a.raw

def PortChoice.valid (S : Stars C) (count : (charged plane C).card = 5) (i : Fin 5) :
    PortChoice → Prop
  | .direct j => j < i
  | .atom a => a.raw.Nonempty ∧ a.raw ⊆ a.host.support S ∧
      (match a.host with | .singleton _ => True | .leaf _ => 2 ≤ a.raw.card) ∧
      ∀ j ∈ a.promoted, j < i ∧ (gateOrder count j).val ∈ exceptional plane C ∧
        (wireRaw count j).Nonempty ∧ wireRaw count j ⊆ a.raw

theorem PortChoice.reads_earlier {S : Stars C} {count : (charged plane C).card = 5}
    {p : PortChoice} {i j : Fin 5} (valid : p.valid S count i) (read : p.reads j) : j < i := by
  cases p with
  | direct k => exact (show j = k from read).symm ▸ valid
  | atom a => exact (valid.2.2.2 j read).1

/-- If the raw set has one element, use its singleton host. If it has at least
    two, a fitting host must be a leaf. This is the encoder's host restriction. -/
theorem select_host (S : Stars C) {R : Finset (Fin 26)} (nonempty : R.Nonempty)
    (fits : (∃ v : Fin 26, R ⊆ {v}) ∨ ∃ l : Fin 13, R ⊆ leaf S l) :
    ∃ h : PortHost, R ⊆ h.support S ∧
      (match h with | .singleton _ => True | .leaf _ => 2 ≤ R.card) := by
  by_cases small : R.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp small
    exact ⟨.singleton v, Finset.Subset.rfl, trivial⟩
  · have size : 2 ≤ R.card := by
      have h := Finset.card_pos.mpr nonempty
      omega
    rcases fits with ⟨v, sub⟩ | ⟨l, sub⟩
    · have bound := Finset.card_le_card sub
      rw [Finset.card_singleton] at bound
      omega
    · exact ⟨.leaf l, sub, size⟩

/-- Each physical operand has a valid primary choice. If the wire is charged,
    the choice reads it directly, even if another description is possible. -/
theorem select_port (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (count : (charged plane C).card = 5) (i : Fin 5) (b : Fin 2) :
    let g := (gateOrder count i).val
    ∃ p : PortChoice, p.valid S count i ∧ p.raw count = side (n := 26) C g b ∧
      (∀ j : Fin 5, opnd C g b = 26+(gateOrder count j).val → p = .direct j) ∧
      (∀ j : Fin 5, p.reads j → Relation.ReflTransGen (OrStep 26 C)
        (opnd C g b) (26+(gateOrder count j).val)) ∧
      (∀ j, p = .direct j → opnd C g b = 26+(gateOrder count j).val) ∧
      (∀ a, p = .atom a → ∀ j, (gateOrder count j).val ∈
        portPromotions plane C (opnd C g b) → j ∈ a.promoted) ∧
      ∀ x, val C (List.ofFn x) (opnd C g b) = true ↔
        p.value x (fun j => gateVal 26 C (gateOrder count j).val x) := by
  classical
  let g := (gateOrder count i).val
  have chargedG : g ∈ charged plane C := (gateOrder count i).property
  have bound : g < C.gates.length := by
    rcases Finset.mem_union.mp chargedG with d | r
    · exact (junkData d).1
    · exact (orData r).1
  have earlier j (h : (gateOrder count j).val < g) : j < i :=
    (gateOrder count).lt_iff_lt.mp h
  by_cases isDirect : ∃ j : Fin 5, opnd C g b = 26+(gateOrder count j).val
  · obtain ⟨j, read⟩ := isDirect
    have before := opndBound least.1 bound b
    rw [read] at before
    use PortChoice.direct j
    refine ⟨earlier _ (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change orIn 26 C (26+(gateOrder count j).val) = orIn 26 C (opnd C g b)
      rw [read]
    · intro k hr
      have equal : (gateOrder count j).val = (gateOrder count k).val :=
        Nat.add_left_cancel (read.symm.trans hr)
      congr 1
      exact (gateOrder count).injective (Subtype.ext equal)
    · intro k hk
      change k = j at hk
      subst k
      rw [read]
    · rintro k eq; cases eq; exact read
    · rintro a impossible; cases impossible
    · intro x
      rw [read]
      rfl
  · rcases matches_ports S least top chargedG b with ⟨k, hk, _, eq⟩ | ⟨raw, fits, compat, value⟩
    · obtain ⟨j, hj⟩ := (gateOrder count).surjective ⟨k,hk⟩
      exact (isDirect ⟨j, (congrArg (fun r : ↥(charged plane C) => 26+r.val) hj).symm ▸ eq⟩).elim
    · let promotions := portPromotions plane C (opnd C g b)
      let selected := Finset.univ.filter fun j : Fin 5 => (gateOrder count j).val ∈ promotions
      have selected_iff (j : Fin 5) : j ∈ selected ↔ (gateOrder count j).val ∈ promotions := by
        simp [selected]
      obtain ⟨host, supports, size⟩ := select_host S raw fits
      refine ⟨.atom ⟨_,host,selected⟩, ⟨raw,supports,size,?_⟩, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        obtain ⟨ex, before, nonempty, sub⟩ := compat _ ((selected_iff j).mp hj)
        exact ⟨earlier _ before, ex, nonempty, sub⟩
      · intro j read
        exact (isDirect ⟨j,read⟩).elim
      · intro j hj
        obtain ⟨_,_,promote⟩ := Finset.mem_filter.mp ((selected_iff j).mp hj)
        exact (orReaches_reach _ _ promote).1
      · rintro k impossible; cases impossible
      · rintro a eq j mem
        cases eq
        exact (selected_iff j).mpr mem
      · intro x
        change _ ↔ (∃ v ∈ side (n := 26) C g b, x v = true) ∨
          ∃ j ∈ selected, gateVal 26 C (gateOrder count j).val x = true
        rw [value x]
        apply or_congr Iff.rfl
        constructor
        · rintro ⟨k, hk, on⟩
          let prior : ↥(charged plane C) := ⟨k, Finset.mem_union_right _ (compat k hk).1⟩
          obtain ⟨j,hj⟩ := (gateOrder count).surjective prior
          have eq : (gateOrder count j).val = k := congrArg Subtype.val hj
          exact ⟨j, (selected_iff j).mpr (eq.symm ▸ hk), eq.symm ▸ on⟩
        · rintro ⟨j, hj, on⟩
          exact ⟨_,(selected_iff j).mp hj,on⟩

#print axioms select_port

end SixEdge.Plane
