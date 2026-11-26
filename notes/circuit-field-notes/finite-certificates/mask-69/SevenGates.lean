import PEqualNP.Defs.MetaComplexity

namespace FivePointMask69
open PEqualNP.CircuitLowerBounds

/-- The seven-gate control supplied with desk unit L-meta-23714. -/
def circuit : Circuit :=
  ⟨[⟨.not, [0]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [3, 6]⟩,
    ⟨.or, [4, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.not, [10]⟩], 11⟩

theorem seven_suffice :
    ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        (69 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, circuit]
  · decide

#print axioms seven_suffice
end FivePointMask69
