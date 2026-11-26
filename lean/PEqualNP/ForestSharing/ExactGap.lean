import PEqualNP.C4FreeSharing.ExactGap
import PEqualNP.ForestSharing.ForestCounterexample

/-- The bipartite graph specified by all 49 cells is a tree. In the dual
zero-set model its circuit requires three paid unions, and its formula four. -/
theorem PEqualNP.ForestSharing.ExactGap :
    let Cell := Fin 7 × Fin 7
    let Region := Set Cell
    let masks : Fin 7 → BitVec 7 := ![117, 109, 106, 62, 126, 79, 119]
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
    (∃ G : SimpleGraph (Fin 7 ⊕ Fin 7),
      (∀ r c : Fin 7, G.Adj (.inl r) (.inr c) ↔ edge r c = true) ∧
      (∀ r s : Fin 7, ¬ G.Adj (.inl r) (.inl s)) ∧
      (∀ c d : Fin 7, ¬ G.Adj (.inr c) (.inr d)) ∧ G.IsTree) ∧
    three rect z ∧ ¬ two rect z ∧ formula 4 z ∧ ∀ n, n < 4 → ¬ formula n z := by
  constructor
  · refine ⟨ForestTree.graphOf ForestGap.edge, ?_, ?_, ?_, ForestGap.tree_exact_gap.1⟩
    · intro r c
      rfl
    · intro r s
      change false ≠ true
      decide
    · intro c d
      change false ≠ true
      decide
  change
    let addWire := fun (F : C4Gap.Audit.Region → Prop) (w t : C4Gap.Audit.Region) => F t ∨ t = w
    let two := fun (F : C4Gap.Audit.Region → Prop) (s : C4Gap.Audit.Region) =>
      ∃ a b, C4Gap.Audit.free F a ∧ C4Gap.Audit.free F b ∧
        ∃ c d, C4Gap.Audit.free (addWire F (a ∪ b)) c ∧ C4Gap.Audit.free (addWire F (a ∪ b)) d ∧
          C4Gap.Audit.free (addWire (addWire F (a ∪ b)) (c ∪ d)) s
    let three := fun (F : C4Gap.Audit.Region → Prop) (s : C4Gap.Audit.Region) =>
      ∃ a b, C4Gap.Audit.free F a ∧ C4Gap.Audit.free F b ∧ two (addWire F (a ∪ b)) s
    three TwoIntersections.Rectangle ForestGap.zero ∧
      ¬ two TwoIntersections.Rectangle ForestGap.zero ∧
      C4Gap.Audit.formula 4 ForestGap.zero ∧
      ∀ n, n < 4 → ¬ C4Gap.Audit.formula n ForestGap.zero
  rw [C4Gap.Audit.free_eq, C4Gap.Audit.formula_eq]
  exact ForestGap.tree_exact_gap.2
