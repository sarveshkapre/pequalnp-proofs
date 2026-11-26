import Refutation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace SixPointMask133

def lit {n : Nat} (i j : Fin n) (k : Fin n) : Bool := decide (k = i ∨ k = j)

def answer {n : Nat} (mask : Nat) (i j : Fin n) : Bool :=
  mask.testBit (n * min i.val j.val + max i.val j.val)

-- Point 5 has no positive singleton or pair. Restricting it to false leaves mask 69.
theorem no_seven : ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧
    ∀ i j : Fin 6, C.eval (List.ofFn (lit i j)) = answer 133 i j := by
  rintro ⟨C, fan, size, values⟩
  let f (x : Fin 6 → Bool) := C.eval (List.ofFn x)
  let g (x : Fin 5 → Bool) := f (Fin.snoc x false)
  have obs (i j : Fin 6) : f (lit i j) = answer 133 i j := values i j
  have restricts (i j : Fin 5) : g (lit i j) = answer 69 i j := by
    have embed : ∀ a b : Fin 5, Fin.snoc (lit a b) false = lit a.castSucc b.castSucc := by decide
    have same : ∀ a b : Fin 5, answer 133 a.castSucc b.castSucc = answer 69 a b := by decide
    change f (Fin.snoc (lit i j) false) = _
    rw [embed, obs, same]
  have dependent : ∃ x : Fin 6 → Bool,
      f (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ f x := by
    refine ⟨lit 0 0, ?_⟩
    have flip : Function.update (lit (0 : Fin 6) 0) (Fin.last 5)
        (!(lit (0 : Fin 6) 0 (Fin.last 5))) = lit 0 5 := by decide
    rw [flip, obs, obs]
    decide
  have varies : ∃ y y' : Fin 5 → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y' false) := by
    refine ⟨lit 0 0, lit 2 2, ?_⟩
    change g (lit 0 0) ≠ g (lit 2 2)
    rw [restricts, restricts]
    decide
  have orig : HasCircuitSize 6 f 7 := ⟨C, fan, size, fun _ => rfl⟩
  obtain ⟨D, fanD, sizeD, evD⟩ := Mask69.gate_elim 5 f false 6 dependent varies orig
  exact Mask69.no_six ⟨D, fanD, sizeD, fun i j => (evD (lit i j)).trans (restricts i j)⟩

-- The desk supplied these eight gates. The finite check covers all 36 ordered tests.
def deskCircuit : Circuit :=
  ⟨[⟨.not, [0]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.not, [12]⟩], 13⟩

theorem eight_suffice : ∃ C : Circuit, FanInTwo C ∧ C.size = 8 ∧
    ∀ i j : Fin 6, C.eval (List.ofFn (lit i j)) = answer 133 i j := by
  refine ⟨deskCircuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, deskCircuit]
  · decide

end SixPointMask133
