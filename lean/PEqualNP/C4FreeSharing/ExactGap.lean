import PEqualNP.C4FreeSharing.C4Gap

/-! Express the circuit and formula predicates using only the pinned library.
A set belongs to a generated family exactly when every family closed under
the same constructors contains it. This lets the independent verifier read
the model and the entire seven-row matrix directly from the recorded statement. -/
namespace C4Gap.Audit
open TwoIntersections ThreeIntersectionsFormula
abbrev Region := Set (Fin 7 × Fin 7)

def free (F : Region → Prop) (s : Region) : Prop :=
  ∀ P : Region → Prop, (∀ t, F t → P t) →
    (∀ a b, P a → P b → P (a ∩ b)) → P s

def formula (n : Nat) (s : Region) : Prop :=
  ∀ P : Nat → Region → Prop, (∀ t, Rectangle t → P 0 t) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
    (∀ i j a b, P i a → P j b → P (i+j+1) (a ∪ b)) → P n s

theorem free_eq : free = @Free (Fin 7 × Fin 7) := by
  funext F s
  apply propext
  constructor
  · exact fun h => h (Free F) (fun _ => .input) (fun _ _ => .meet)
  · intro h P base meet
    induction h with
    | input h => exact base _ h
    | meet _ _ ih jh => exact meet _ _ ih jh

theorem formula_eq : formula = Formula (@Rectangle (Fin 7) (Fin 7)) := by
  funext n s
  apply propext
  constructor
  · exact fun h => h (Formula Rectangle) (fun _ => .base)
      (fun _ _ _ _ => .meet) (fun _ _ _ _ => .join)
  · intro h P base meet join
    induction h with
    | base h => exact base _ h
    | meet _ _ ih jh => exact meet _ _ _ _ ih jh
    | join _ _ ih jh => exact join _ _ _ _ ih jh
end C4Gap.Audit

theorem PEqualNP.C4FreeSharing.ExactGap :
    let Cell := Fin 7 × Fin 7
    let Region := Set Cell
    let masks : Fin 7 → BitVec 7 := ![113, 109, 125, 106, 62, 126, 79]
    let z : Region := {p | (masks p.1).getLsbD p.2.val = true}
    let edge := fun (r c : Fin 7) => !(masks r).getLsbD c.val
    let rect := fun (s : Region) => ∃ r c : Set (Fin 7), s = Set.prod r c
    let free := fun (F : Region → Prop) (s : Region) =>
      ∀ P : Region → Prop, (∀ t, F t → P t) →
        (∀ a b, P a → P b → P (a ∩ b)) → P s
    let addWire := fun (F : Region → Prop) (w t : Region) => F t ∨ t = w
    let two := fun (F : Region → Prop) (s : Region) =>
      ∃ a b, free F a ∧ free F b ∧
        ∃ c d, free (addWire F (a ∪ b)) c ∧ free (addWire F (a ∪ b)) d ∧
          free (addWire (addWire F (a ∪ b)) (c ∪ d)) s
    let three := fun (F : Region → Prop) (s : Region) =>
      ∃ a b, free F a ∧ free F b ∧ two (addWire F (a ∪ b)) s
    let formula := fun (n : Nat) (s : Region) =>
      ∀ P : Nat → Region → Prop, (∀ t, rect t → P 0 t) →
        (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
        (∀ i j a b, P i a → P j b → P (i+j+1) (a ∪ b)) → P n s
    (∀ r s c d : Fin 7, r ≠ s → c ≠ d →
      ¬ (edge r c = true ∧ edge r d = true ∧ edge s c = true ∧ edge s d = true)) ∧
    three rect z ∧ ¬ two rect z ∧ formula 4 z ∧ ∀ n, n < 4 → ¬ formula n z := by
  constructor
  · exact C4Gap.four_cycle_free
  change
    let addWire := fun (F : C4Gap.Audit.Region → Prop) (w t : C4Gap.Audit.Region) => F t ∨ t = w
    let two := fun (F : C4Gap.Audit.Region → Prop) (s : C4Gap.Audit.Region) =>
      ∃ a b, C4Gap.Audit.free F a ∧ C4Gap.Audit.free F b ∧
        ∃ c d, C4Gap.Audit.free (addWire F (a ∪ b)) c ∧ C4Gap.Audit.free (addWire F (a ∪ b)) d ∧
          C4Gap.Audit.free (addWire (addWire F (a ∪ b)) (c ∪ d)) s
    let three := fun (F : C4Gap.Audit.Region → Prop) (s : C4Gap.Audit.Region) =>
      ∃ a b, C4Gap.Audit.free F a ∧ C4Gap.Audit.free F b ∧ two (addWire F (a ∪ b)) s
    three TwoIntersections.Rectangle C4Gap.zero ∧
      ¬ two TwoIntersections.Rectangle C4Gap.zero ∧
      C4Gap.Audit.formula 4 C4Gap.zero ∧
      ∀ n, n < 4 → ¬ C4Gap.Audit.formula n C4Gap.zero
  rw [C4Gap.Audit.free_eq, C4Gap.Audit.formula_eq]
  exact C4Gap.exact_circuit_formula_gap
