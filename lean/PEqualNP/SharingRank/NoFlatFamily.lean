import PEqualNP.SharingRank.Witness

theorem PEqualNP.SharingRank.NoFlatFamily :
    ∀ (t : Nat),
  let W := BitVec 6 × (Fin t → Bool × Bool)
  let shared := fun (v : BitVec 6) => v.getLsbD 0 || v.getLsbD 1
  let base := fun (v : BitVec 6) => (v.getLsbD 2 || (v.getLsbD 3 && shared v)) &&
    (v.getLsbD 4 || (v.getLsbD 5 && shared v))
  let zero := fun (x y : W) => base (x.1 &&& y.1) = true ∧ ∀ i,
    ((x.2 i).1 && (y.2 i).1) = true ∨
      (((x.2 i).2 && (y.2 i).2) = true ∧ shared (x.1 &&& y.1) = true)
  ∀ (clipR clipC : Set W) (a b s u : Fin (t+3) → Set W),
    ¬ (∀ x y, zero x y ↔ x ∈ clipR ∧ y ∈ clipC ∧
      ∀ j, (x ∈ a j ∧ y ∈ s j) ∨ (x ∈ b j ∧ y ∈ u j)) := by
  intro t
  dsimp only
  exact SharingRank.Witness.no_flat
