import PEqualNP.Defs

namespace MatchingThree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
  (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
  (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def expansion : Circuit where
  gates := [
    ⟨.and, [4, 8]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [0, 11]⟩,
    ⟨.and, [3, 8]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [1, 15]⟩,
    ⟨.and, [3, 7]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [2, 19]⟩,
    ⟨.or, [12, 16]⟩, ⟨.or, [21, 20]⟩]
  output := 22

theorem expansion_mono : Monotone2 expansion := by
  intro g hg
  simp [expansion] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst g <;> simp

theorem known_upper :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 14 ∧
      ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x := by
  refine ⟨expansion, expansion_mono, rfl, ?_⟩
  intro x
  simp [expansion, Circuit.eval, Circuit.wires, GateOp.eval, target, List.ofFn_succ,
        List.getD, List.getElem?_cons, Bool.or_assoc, Bool.and_or_distrib_left,
        Bool.and_assoc]

end MatchingThree

theorem PEqualNP.Outside.Upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 14 ∧
  ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
    ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
     (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
     (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)) := MatchingThree.known_upper
