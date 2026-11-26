import PEqualNP.SharingRank.Upper

namespace SharingRank
private theorem fold_wires (p : Program m n) :
    p.foldr (fun (g : Port m n × Port m n) (w : Nat → Region m n) (i : Nat) =>
      Nat.casesOn i (run w g.1 ∪ run w g.2) w) (fun _ => Set.univ) = wires p := by
  induction p with
  | nil => rfl
  | cons g p ih => obtain ⟨a,b⟩ := g; simp only [List.foldr_cons,ih]; rfl

private theorem fold_flat (p : Program m n) :
    p.foldr (fun (g : Port m n × Port m n) (z : Region m n) =>
      (raw g.1 ∪ raw g.2) ∩ z) Set.univ = flat p := by
  induction p with
  | nil => rfl
  | cons g p ih => obtain ⟨a,b⟩ := g; simp only [List.foldr_cons,ih]; rfl
end SharingRank

open SharingRank in
theorem PEqualNP.SharingRank.Rigidity :
    ∀ (m n : Nat),
      let R := Set (Fin m × Fin n)
      let B := Set (Fin m) × Set (Fin n)
      let T := B × Set Nat
      let raw := fun (q : T) => Set.prod q.1.1 q.1.2
      let run := fun (w : Nat → R) (q : T) => raw q ∩ {x | ∀ i, i ∈ q.2 → x ∈ w i}
      let cons := fun (g : T × T) (w : Nat → R) (i : Nat) =>
        Nat.casesOn i (run w g.1 ∪ run w g.2) w
      let stage := fun (g : T × T) (z : R) => (raw g.1 ∪ raw g.2) ∩ z
      ∀ (p : List (T × T)) (q : T),
        let z := run (p.foldr cons (fun _ => Set.univ)) q
        let h : Matrix (Fin m) (Fin n) ℝ := fun i j =>
          @ite ℝ ((i,j) ∈ z) (Classical.propDecidable _) 1 0
        h.rank ≤ 3 ^ p.length ∧
          (z ≠ raw q ∩ p.foldr stage Set.univ → h.rank + 2 ≤ 3 ^ p.length) := by
  intro m n
  dsimp only
  intro p q
  have bound := rigidity p q
  rw [← fold_wires p, ← fold_flat p] at bound
  exact bound
