import PEqualNP.Quadrangle.Encoding
import PEqualNP.Quadrangle.Certificate
import PEqualNP.Quadrangle.Padding

/-!
# The missing lower half of pjscruggs's quadrangle handoff

The graph, four-intersection witness, CNF, and LRAT certificate are pjscruggs's
published artifacts at commit 7da7d81614b93ea808c11ac27f27136942fec385.
This addition connects the original `Represents` predicate to that exact CNF
and replays the existing certificate with the project's kernel LRAT checker.
-/

/-- No three-intersection representation of the original duplicated-row graph
exists, even with arbitrary free unions and reuse of all earlier gates. -/
theorem PEqualNP.Quadrangle.LowerBound :
    ¬ QuadrangleHandoff.Represents 3 QuadrangleHandoff.graph := by
  intro h
  exact PEqualNP.Quadrangle.Certificate.unsat
    (PEqualNP.Quadrangle.Encoding.represents_satisfies h)

/-- The handoff's four-gate upper bound together with the missing lower bound. -/
theorem PEqualNP.Quadrangle.FourSufficesThreeImpossible :
    QuadrangleHandoff.Represents 4 QuadrangleHandoff.graph ∧
      ¬ QuadrangleHandoff.Represents 3 QuadrangleHandoff.graph :=
  ⟨QuadrangleHandoff.four, PEqualNP.Quadrangle.LowerBound⟩

/-- Four is the exact minimum, including exclusion of every smaller budget. -/
theorem PEqualNP.Quadrangle.ExactMinimum :
    QuadrangleHandoff.Represents 4 QuadrangleHandoff.graph ∧
      ∀ k, k < 4 → ¬ QuadrangleHandoff.Represents k QuadrangleHandoff.graph :=
  ⟨QuadrangleHandoff.four,
    QuadrangleHandoff.excludes_smaller PEqualNP.Quadrangle.LowerBound⟩

#print axioms PEqualNP.Quadrangle.LowerBound
#print axioms PEqualNP.Quadrangle.FourSufficesThreeImpossible
#print axioms PEqualNP.Quadrangle.ExactMinimum
