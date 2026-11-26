import Mathlib.Tactic

namespace PEqualNP.PaidDepth
open scoped BigOperators

private def fitsSuffix (m : Nat) : List Nat → Prop
  | [] => True
  | w :: ws => 0 < w ∧ m * (w-1) < w + ws.sum ∧ fitsSuffix m ws

private theorem packSuffix {m : Nat} (items : List Nat) (cap : Fin m → Nat)
    (fits : fitsSuffix m items) (total : items.sum ≤ ∑ b, cap b) :
    ∃ placement : List (Fin m × Nat),
      placement.map Prod.snd = items ∧
      ∀ b, (placement.map fun slot => if slot.1 = b then slot.2 else 0).sum ≤ cap b := by
  induction items generalizing cap with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons w ws ih =>
    obtain ⟨hw, need, tails⟩ := fits
    have enough : ∃ b, w ≤ cap b := by
      by_contra! small
      have bound : (∑ b, cap b) ≤ ∑ _b : Fin m, (w-1) :=
        Finset.sum_le_sum fun b _ => by have := small b; omega
      simp at bound
      simp only [List.sum_cons] at total
      omega
    obtain ⟨b, hb⟩ := enough
    let remain (j : Fin m) := if b = j then cap j - w else cap j
    have restore : (∑ j, remain j) + w = ∑ j, cap j := by
      calc
        _ = ∑ j, (remain j + if b = j then w else 0) := by
          rw [Finset.sum_add_distrib]
          simp
        _ = _ := Finset.sum_congr rfl fun j _ => by
          by_cases same : b = j
          · subst j
            simp [remain, hb]
          · simp [remain, same]
    have room : ws.sum ≤ ∑ j, remain j := by
      simp only [List.sum_cons] at total
      omega
    obtain ⟨placement, order, loads⟩ := ih remain tails room
    refine ⟨(b,w)::placement, by simpa using order, ?_⟩
    intro j
    have load := loads j
    by_cases same : b = j
    · subst j
      simp [remain] at load
      simpa using (show w + _ ≤ cap b by omega)
    · simpa [same] using (show _ ≤ cap j from by simpa [remain, same] using load)

theorem ReservePacking :
∀ (m L q : Nat) (cap : Fin m → Nat) (items : List Nat),
  (∀ w ∈ items, 0 < w ∧ w ≤ L) → m * (L-1) ≤ q →
  items.sum + q ≤ ∑ b, cap b →
  ∃ placement : List (Fin m × Nat),
    placement.map Prod.snd = items ++ List.replicate q 1 ∧
    ∀ b, (placement.map fun slot => if slot.1 = b then slot.2 else 0).sum ≤ cap b
 := by
  intro m L q cap items sizes reserved total
  have ones (n : Nat) : fitsSuffix m (List.replicate n 1) := by
    induction n with
    | zero => trivial
    | succ n ih => simp [List.replicate_succ, fitsSuffix, ih]
  have fits : fitsSuffix m (items ++ List.replicate q 1) := by
    induction items with
    | nil => exact ones q
    | cons w ws ih =>
      obtain ⟨pos, bound⟩ := sizes w (by simp)
      have smaller : m*(w-1) ≤ m*(L-1) := Nat.mul_le_mul_left _ (by omega)
      refine ⟨pos, ?_, ih (fun i hi => sizes i (by simp [hi])) ?_⟩
      · simp
        omega
      · simp only [List.sum_cons] at total
        omega
  exact packSuffix _ cap fits (by simpa using total)

end PEqualNP.PaidDepth
