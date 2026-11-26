import PEqualNP.SharingRank.Records
namespace SharingRank
open Set

private theorem flat_has_formula (p : Program n n) : FormulaAt p.length (flat p) := by
  intro P box meet join
  induction p with
  | nil =>
    have h := box (Set.univ : Set (Fin n)) (Set.univ : Set (Fin n))
    simpa [flat] using h
  | cons g l ih =>
    obtain ⟨a,b⟩ := g
    have pair := join 0 0 _ _ (box a.1.1 a.1.2) (box b.1.1 b.1.2)
    simpa only [raw,flat,List.length_cons,Nat.zero_add,Nat.one_add,Nat.succ_eq_add_one] using meet 1 l.length _ _ pair ih

theorem ceiling {z : Region n n} (c : CircuitAt k z) (f : ¬ FormulaAt k z) :
    (indicator z).rank + 2 ≤ 3^k := by
  obtain ⟨p,q,rfl,rfl⟩ := c
  apply (rigidity p q).2
  intro eq
  apply f
  rw [eq]
  intro P box meet join
  simpa only [raw,Nat.zero_add] using
    meet 0 p.length _ _ (box q.1.1 q.1.2) (flat_has_formula p P box meet join)
end SharingRank
