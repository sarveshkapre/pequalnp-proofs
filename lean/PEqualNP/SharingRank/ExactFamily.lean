import PEqualNP.SharingRank.Ceiling

namespace SharingRank
private theorem record_wires (p : Program m n) :
    p.foldr (fun (g : Port m n × Port m n) (w : Nat → Region m n) (i : Nat) =>
      Nat.casesOn i (run w g.1 ∪ run w g.2) w) (fun _ => Set.univ) = wires p := by
  induction p with
  | nil => rfl
  | cons g p ih => obtain ⟨a,b⟩ := g; simp only [List.foldr_cons,ih]; rfl

end SharingRank

open SharingRank in
theorem PEqualNP.SharingRank.ExactFamily :
    ∀ (t : Nat), ∃ n : Nat,
  let R := Set (Fin n × Fin n)
  let B := Set (Fin n) × Set (Fin n)
  let T := B × Set Nat
  let raw := fun (q : T) => Set.prod q.1.1 q.1.2
  let run := fun (w : Nat → R) (q : T) => raw q ∩ {x | ∀ i, i ∈ q.2 → x ∈ w i}
  let cons := fun (g : T × T) (w : Nat → R) (i : Nat) =>
    Nat.casesOn i (run w g.1 ∪ run w g.2) w
  let circuit := fun (j : Nat) (z : R) => ∃ (p : List (T × T)) (q : T),
    p.length = j ∧ run (p.foldr cons (fun _ => Set.univ)) q = z
  let formula := fun (j : Nat) (z : R) => ∀ P : Nat → R → Prop,
    (∀ (r c : Set (Fin n)), P 0 (Set.prod r c)) →
    (∀ i h a b, P i a → P h b → P (i+h) (a ∩ b)) →
    (∀ i h a b, P i a → P h b → P (i+h+1) (a ∪ b)) → P j z
  ∃ z : R,
    let h : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      @ite ℝ ((i,j) ∈ z) (Classical.propDecidable _) 1 0
    h.rank + 2 = 3^(t+3) ∧
    circuit (t+3) z ∧ (∀ j < t+3, ¬ circuit j z) ∧
    formula (t+4) z ∧ (∀ j < t+4, ¬ formula j z) := by
  intro t
  obtain ⟨n,z,r,upper,lower,f,g⟩ := Family.records t
  refine ⟨n,z,r,?_,?_,f,g⟩
  · obtain ⟨p,q,len,eq⟩ := upper
    rw [← record_wires] at eq
    exact ⟨p,q,len,eq⟩
  · rintro j cheap ⟨p,q,len,eq⟩
    apply lower j cheap
    refine ⟨p,q,len,?_⟩
    rw [← record_wires]
    exact eq
