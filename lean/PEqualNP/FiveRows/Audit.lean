import PEqualNP.Atlas56.FullClassification

/-! Express the two recorded statements entirely in the pinned library. -/
namespace FiveRowsAudit
open Set TwoIntersections ThreeIntersectionsFormula
abbrev Region (n : Nat) := Set (Fin 5 × Fin n)

def closure {n} (F : Region n → Prop) (s : Region n) : Prop :=
  ∀ P : Region n → Prop, (∀ t, F t → P t) →
    (∀ a b, P a → P b → P (a ∩ b)) → P s

theorem closure_eq {n} : @closure n = @Free (Fin 5 × Fin n) := by
  funext F s
  apply propext
  constructor
  · exact fun h => h (Free F) (fun _ => .input) (fun _ _ => .meet)
  · intro h P base meet
    induction h with
    | input h => exact base _ h
    | meet _ _ ih jh => exact meet _ _ ih jh

def two {n} (F : Region n → Prop) (s : Region n) : Prop :=
  ∃ a b, closure F a ∧ closure F b ∧
    ∃ c d, closure (With F (a ∪ b)) c ∧ closure (With F (a ∪ b)) d ∧
      closure (With (With F (a ∪ b)) (c ∪ d)) s

def three {n} (F : Region n → Prop) (s : Region n) : Prop :=
  ∃ a b, closure F a ∧ closure F b ∧ two (With F (a ∪ b)) s

theorem two_eq {n} : @two n = @Two (Fin 5 × Fin n) := by
  unfold two Two
  rw [closure_eq]

theorem three_eq {n} : @three n = @ThreeIntersections.Three (Fin 5 × Fin n) := by
  unfold three ThreeIntersections.Three
  rw [closure_eq, two_eq]

def tree {n} (k : Nat) (s : Region n) : Prop :=
  ∀ P : Nat → Region n → Prop, (∀ t, Rectangle t → P 0 t) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
    (∀ i j a b, P i a → P j b → P (i+j+1) (a ∪ b)) → P k s

theorem tree_eq {n} : @tree n = Formula (@Rectangle (Fin 5) (Fin n)) := by
  funext k s
  apply propext
  constructor
  · exact fun h => h (Formula Rectangle) (fun _ => .base)
      (fun _ _ _ _ => .meet) (fun _ _ _ _ => .join)
  · intro h P base meet join
    induction h with
    | base h => exact base _ h
    | meet _ _ ih jh => exact meet _ _ _ _ ih jh
    | join _ _ ih jh => exact join _ _ _ _ ih jh
end FiveRowsAudit
