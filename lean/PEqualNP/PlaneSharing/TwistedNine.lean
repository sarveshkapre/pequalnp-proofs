import Mathlib.Tactic

/-! In GF(9) = GF(3)[i] with i² = -1, the two trits encode a + bi.
The norm selects one of two conjugations. The first two finite assertions give
additive slope maps with disjoint graphs away from zero. The remaining
assertions exhibit two perspective triangles violating Desargues' conclusion. -/
theorem PEqualNP.PlaneSharing.TwistedNine :
    let add := fun (x y : Nat) => (x%3 + y%3)%3 + 3*((x/3 + y/3)%3)
  let mul := fun (x y : Nat) => ((x%3)*(y%3) + 2*(x/3)*(y/3))%3 +
    3*(((x%3)*(y/3) + (x/3)*(y%3))%3)
  let conj := fun (x : Nat) => x%3 + 3*((2*(x/3))%3)
  let slope := fun (m x : Nat) => mul m (if mul m (conj m) = 2 then conj x else x)
  let inc := fun (p l : Nat) =>
    if 81 ≤ p then l == 90 || p-81 == l/9
    else if l = 90 then false
    else if l/9 = 9 then p/9 == l%9
    else p%9 == add (slope (l/9) (p/9)) (l%9)
  let col := fun (a b c : Nat) => ∃ l : Fin 91, inc a l.val ∧ inc b l.val ∧ inc c l.val
  (∀ m x y : Fin 9, slope m (add x y) = add (slope m x) (slope m y)) ∧
  (∀ m n x : Fin 9, m ≠ n → x ≠ 0 → slope m x ≠ slope n x) ∧
  col 0 9 18 ∧ col 0 10 20 ∧ col 0 1 3 ∧
  ¬ col 9 10 1 ∧ ¬ col 18 20 3 ∧
  col 9 10 90 ∧ col 18 20 90 ∧
  col 9 1 58 ∧ col 18 3 58 ∧
  col 10 1 28 ∧ col 20 3 28 ∧ ¬ col 90 58 28 := by
  set_option maxRecDepth 65536 in
  set_option maxHeartbeats 12000000 in
  decide +kernel
