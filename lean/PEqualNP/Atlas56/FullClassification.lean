import PEqualNP.Atlas56.Finite
import PEqualNP.Atlas56.Classification

namespace Atlas56
open Set TwoIntersections
def four (F : Family Cell) (z : Set Cell) : Prop :=
  ∃ a b, Free F a ∧ Free F b ∧ ThreeIntersections.Three (With F (a ∪ b)) z

theorem four_circuit (z : Set Cell) : four Rectangle z := by
  let row (i : Row) : Set Cell := {i} ×ˢ {j | (i,j) ∈ z}
  have hr (i : Row) : Rectangle (row i) := ⟨_,_,rfl⟩
  have hz : z = (((row 0 ∪ row 1) ∪ row 2) ∪ row 3) ∪ row 4 := by
    ext ⟨i,j⟩
    fin_cases i <;> simp [row]
  refine ⟨row 0,row 1,.input (hr 0),.input (hr 1),
    row 0 ∪ row 1,row 2,.input (Or.inr rfl),.input (Or.inl (hr 2)),
    (row 0 ∪ row 1) ∪ row 2,row 3,.input (Or.inr rfl),.input (Or.inl (Or.inl (hr 3))),
    ((row 0 ∪ row 1) ∪ row 2) ∪ row 3,row 4,.input (Or.inr rfl),
    .input (Or.inl (Or.inl (Or.inl (hr 4)))),.input (Or.inr hz)⟩

theorem full_cover (z : Set Cell) : cube z ∨ orbit z := by
  obtain ⟨cols,rfl⟩ := encode z
  exact alternative patterns patterns_nodup patterns_full complete_check cols
end Atlas56

namespace Atlas56.Audit
open TwoIntersections ThreeIntersectionsFormula
abbrev Region := Set (Fin 5 × Fin 6)

def free (F : Region → Prop) (s : Region) : Prop :=
  ∀ P : Region → Prop, (∀ t, F t → P t) →
    (∀ a b, P a → P b → P (a ∩ b)) → P s

def formula (n : Nat) (s : Region) : Prop :=
  ∀ P : Nat → Region → Prop, (∀ t, Rectangle t → P 0 t) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
    (∀ i j a b, P i a → P j b → P (i+j+1) (a ∪ b)) → P n s

theorem free_eq : free = @Free (Fin 5 × Fin 6) := by
  funext F s
  apply propext
  constructor
  · exact fun h => h (Free F) (fun _ => .input) (fun _ _ => .meet)
  · intro h P base meet
    induction h with
    | input h => exact base _ h
    | meet _ _ ih jh => exact meet _ _ ih jh

theorem formula_eq : formula = Formula (@Rectangle (Fin 5) (Fin 6)) := by
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
end Atlas56.Audit

theorem PEqualNP.Atlas56.FullClassification :
    let Cell := Fin 5 × Fin 6
    let Region := Set Cell
    let masks : Fin 5 → Nat := ![49, 42, 22, 13, 3]
    let q : Region := {p | ¬ (masks p.1).testBit p.2.val = true}
    let iso := fun (z : Region) =>
      ∃ (r : Equiv.Perm (Fin 5)) (c : Equiv.Perm (Fin 6)),
        z = (fun p : Cell => (r p.1,c p.2)) ⁻¹' q
    let rect := fun (s : Region) => ∃ r : Set (Fin 5), ∃ c : Set (Fin 6), s = Set.prod r c
    let cube := fun (z : Region) => ∃ a b c d e f : Region,
      rect a ∧ rect b ∧ rect c ∧ rect d ∧ rect e ∧ rect f ∧
      z = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f)
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
    let four := fun (F : Region → Prop) (s : Region) =>
      ∃ a b, free F a ∧ free F b ∧ three (addWire F (a ∪ b)) s
    let formula := fun (n : Nat) (s : Region) =>
      ∀ P : Nat → Region → Prop, (∀ t, rect t → P 0 t) →
        (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
        (∀ i j a b, P i a → P j b → P (i+j+1) (a ∪ b)) → P n s
    ∀ z : Region, (iso z ↔ ¬ three rect z) ∧
      (iso z ↔ ¬ ∃ n < 4, formula n z) ∧ (¬ iso z → cube z) ∧
      formula 4 z ∧ four rect z := by
  change
    let addWire := fun (F : Atlas56.Audit.Region → Prop) (w t : Atlas56.Audit.Region) => F t ∨ t = w
    let two := fun (F : Atlas56.Audit.Region → Prop) (s : Atlas56.Audit.Region) =>
      ∃ a b, Atlas56.Audit.free F a ∧ Atlas56.Audit.free F b ∧
        ∃ c d, Atlas56.Audit.free (addWire F (a ∪ b)) c ∧ Atlas56.Audit.free (addWire F (a ∪ b)) d ∧
          Atlas56.Audit.free (addWire (addWire F (a ∪ b)) (c ∪ d)) s
    let three := fun (F : Atlas56.Audit.Region → Prop) (s : Atlas56.Audit.Region) =>
      ∃ a b, Atlas56.Audit.free F a ∧ Atlas56.Audit.free F b ∧ two (addWire F (a ∪ b)) s
    let four := fun (F : Atlas56.Audit.Region → Prop) (s : Atlas56.Audit.Region) =>
      ∃ a b, Atlas56.Audit.free F a ∧ Atlas56.Audit.free F b ∧ three (addWire F (a ∪ b)) s
    ∀ z : Atlas56.Audit.Region, (Atlas56.orbit z ↔ ¬ three TwoIntersections.Rectangle z) ∧
      (Atlas56.orbit z ↔ ¬ ∃ n < 4, Atlas56.Audit.formula n z) ∧
      (¬ Atlas56.orbit z → Atlas56.cube z) ∧
      Atlas56.Audit.formula 4 z ∧ four TwoIntersections.Rectangle z
  rw [Atlas56.Audit.free_eq, Atlas56.Audit.formula_eq]
  change ∀ z : Atlas56.Audit.Region,
    (Atlas56.orbit z ↔ ¬ ThreeIntersections.Three TwoIntersections.Rectangle z) ∧
    (Atlas56.orbit z ↔ ¬ ∃ n < 4, ThreeIntersectionsFormula.Formula TwoIntersections.Rectangle n z) ∧
    (¬ Atlas56.orbit z → Atlas56.cube z) ∧
    ThreeIntersectionsFormula.Formula TwoIntersections.Rectangle 4 z ∧ Atlas56.four TwoIntersections.Rectangle z
  intro z
  obtain ⟨circ,form,cube,upper⟩ := Atlas56.classify Atlas56.full_cover z
  exact ⟨circ,form,cube,upper,Atlas56.four_circuit z⟩
