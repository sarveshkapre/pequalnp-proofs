import PEqualNP.SparseSharing.ForestSimulation

open Set TwoIntersections ThreeIntersectionsFormula SparseSharing

/-- Standalone verifier target. Both cost measures are given by their induction
principles in the statement; the only graph hypothesis is mathlib acyclicity. -/
theorem PEqualNP.SparseSharing.Arboricity :
∀ (m n k : Nat) (fs : List (SimpleGraph (Fin m ⊕ Fin n))),
(∀ G ∈ fs, G.IsAcyclic) →
let Region := Set (Fin m × Fin n)
let z : Region := {p | ∀ G ∈ fs, ¬ G.Adj (.inl p.1) (.inr p.2)}
let rect := fun s : Region => ∃ (r : Set (Fin m)) (c : Set (Fin n)), s = Set.prod r c
let free := fun (F : Region → Prop) (s : Region) =>
  ∀ P : Region → Prop, (∀ t, F t → P t) →
    (∀ a b, P a → P b → P (a ∩ b)) → P s
let circ := fun (F : Region → Prop) (i : Nat) (s : Region) =>
  ∀ P : (Region → Prop) → Nat → Region → Prop,
    (∀ B t, free B t → P B 0 t) →
    (∀ B j a b t, free B a → free B b →
      P (fun u => B u ∨ u = a ∪ b) j t → P B (j+1) t) → P F i s
let formula := fun (i : Nat) (s : Region) =>
  ∀ Q : Nat → Region → Prop, (∀ a, rect a → Q 0 a) →
    (∀ i j a b, Q i a → Q j b → Q (i+j) (a ∩ b)) →
    (∀ i j a b, Q i a → Q j b → Q (i+j+1) (a ∪ b)) → Q i s
circ rect k z → formula (2 * fs.length * (4*k+1)) z := by
  intro m n k fs acyclic
  dsimp only
  intro circuit Q base meet join
  have decode {B : Family (Fin m × Fin n)} {s : Set (Fin m × Fin n)}
      (h : ∀ P : Set (Fin m × Fin n) → Prop, (∀ t, B t → P t) →
        (∀ a b, P a → P b → P (a ∩ b)) → P s) : Free B s :=
    h (Free B) (fun _ ht => .input ht) (fun _ _ ha hb => .meet ha hb)
  have hc : Circuit Rectangle k (forestZeros fs) :=
    circuit Circuit (fun _ _ h => .output (decode h))
      (fun _ _ _ _ _ ha hb rest => .gate (decode ha) (decode hb) rest)
  have emit {j : Nat} {s : Set (Fin m × Fin n)} (f : Formula Rectangle j s) : Q j s := by
    induction f with
    | base h => exact base _ h
    | meet _ _ ha hb => exact meet _ _ _ _ ha hb
    | join _ _ ha hb => exact join _ _ _ _ ha hb
  exact emit (arboricity_simulation fs acyclic hc)
