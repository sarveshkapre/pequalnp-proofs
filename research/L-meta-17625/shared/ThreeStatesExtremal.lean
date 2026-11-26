import ThreeStates
import OrdinaryExtremal

namespace ThreeStates
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- An excess of residual pairs over the three-state capacity guarantees a
smaller vertex cover, without constraints on the numbers of other gates. -/
theorem smaller_cover (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (many : 3^(junk G C).card < 2^(Ustar G C).card) :
    ∃ K : Finset (Fin n), G.IsVertexCover (K : Set _) ∧
      K.card < (tops G C \ centreless G C).card + (Ustar G C).card := by
  by_contra! lower
  obtain ⟨e,neg,S,_,contains,under,yes,no⟩ := CentreSeparation.extremal four least lower
  exact (Nat.not_le_of_lt many) (capacity least.1 top e neg S under contains yes no)

#print axioms smaller_cover
end ThreeStates
