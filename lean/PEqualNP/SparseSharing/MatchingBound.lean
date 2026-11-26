import PEqualNP.SparseSharing.ForestMatching

/-- Standalone replay statement for the matching-number formula bound on forests. -/
theorem PEqualNP.SparseSharing.MatchingBound :
∀ (rows cols m d h : Nat) (G : SimpleGraph (Fin rows ⊕ Fin cols)),
G.IsAcyclic →
(∀ (q : Nat) (r : Fin q → Fin rows) (c : Fin q → Fin cols),
  Function.Injective r → Function.Injective c →
  (∀ j, G.Adj (.inl (r j)) (.inr (c j))) → q ≤ m) →
0 < h → h < d → m ≤ d.choose h →
let Region := Set (Fin rows × Fin cols)
let rect := fun s : Region => ∃ (r : Set (Fin rows)) (c : Set (Fin cols)), s = Set.prod r c
∀ Q : Nat → Region → Prop, (∀ a, rect a → Q 0 a) →
  (∀ i j a b, Q i a → Q j b → Q (i+j) (a ∩ b)) →
  (∀ i j a b, Q i a → Q j b → Q (i+j+1) (a ∪ b)) →
  Q (2*(d-1)) {p | ¬ G.Adj (.inl p.1) (.inr p.2)} := by
  intro rows cols m d h G tree bound positive proper capacity
  dsimp only
  intro Q base meet join
  have emit {j : Nat} {s : Set (Fin rows × Fin cols)}
      (f : ThreeIntersectionsFormula.Formula TwoIntersections.Rectangle j s) : Q j s := by
    induction f with
    | base h => exact base _ h
    | meet _ _ left right => exact meet _ _ _ _ left right
    | join _ _ left right => exact join _ _ _ _ left right
  exact emit (ForestMatching.forest_formula G tree bound positive proper capacity)
