import PEqualNP.SixSharing.SixSharing

/-! Express the circuit and formula predicates using only the pinned library.
A set belongs to a generated family exactly when every family closed under
the same constructors contains it. This lets the independent verifier read
the model and the entire six-row matrix directly from the recorded statement. -/
namespace SixSharing.Audit
open TwoIntersections ThreeIntersectionsFormula
abbrev Region := Set (Fin 6 × Fin 6)

def free (F : Region → Prop) (s : Region) : Prop :=
  ∀ P : Region → Prop, (∀ t, F t → P t) →
    (∀ a b, P a → P b → P (a ∩ b)) → P s

def formula (n : Nat) (s : Region) : Prop :=
  ∀ P : Nat → Region → Prop, (∀ t, Rectangle t → P 0 t) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
    (∀ i j a b, P i a → P j b → P (i+j+1) (a ∪ b)) → P n s

theorem free_eq : free = @Free (Fin 6 × Fin 6) := by
  funext F s
  apply propext
  constructor
  · exact fun h => h (Free F) (fun _ => .input) (fun _ _ => .meet)
  · intro h P base meet
    induction h with
    | input h => exact base _ h
    | meet _ _ ih jh => exact meet _ _ ih jh

theorem formula_eq : formula = Formula (@Rectangle (Fin 6) (Fin 6)) := by
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
end SixSharing.Audit

theorem PEqualNP.SixSharing.ExactGap :
    let Cell := Fin 6 × Fin 6
    let Region := Set Cell
    let masks : Fin 6 → BitVec 6 := ![44, 22, 29, 62, 32, 56]
    let z : Region := {p | (masks p.1).getLsbD p.2.val = true}
    let rect := fun (s : Region) => ∃ r c : Set (Fin 6), s = Set.prod r c
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
    three rect z ∧ ¬ two rect z ∧ formula 4 z ∧ ∀ n, n < 4 → ¬ formula n z := by
  change
    let addWire := fun (F : SixSharing.Audit.Region → Prop) (w t : SixSharing.Audit.Region) => F t ∨ t = w
    let two := fun (F : SixSharing.Audit.Region → Prop) (s : SixSharing.Audit.Region) =>
      ∃ a b, SixSharing.Audit.free F a ∧ SixSharing.Audit.free F b ∧
        ∃ c d, SixSharing.Audit.free (addWire F (a ∪ b)) c ∧ SixSharing.Audit.free (addWire F (a ∪ b)) d ∧
          SixSharing.Audit.free (addWire (addWire F (a ∪ b)) (c ∪ d)) s
    let three := fun (F : SixSharing.Audit.Region → Prop) (s : SixSharing.Audit.Region) =>
      ∃ a b, SixSharing.Audit.free F a ∧ SixSharing.Audit.free F b ∧ two (addWire F (a ∪ b)) s
    three TwoIntersections.Rectangle SixSharing.zero ∧
      ¬ two TwoIntersections.Rectangle SixSharing.zero ∧
      SixSharing.Audit.formula 4 SixSharing.zero ∧
      ∀ n, n < 4 → ¬ SixSharing.Audit.formula n SixSharing.zero
  rw [SixSharing.Audit.free_eq, SixSharing.Audit.formula_eq]
  exact SixSharing.exact_circuit_formula_gap
