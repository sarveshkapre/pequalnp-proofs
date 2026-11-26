import ProjectionOutsideAAOO
import ProjectionOutsideAOAO
import ProjectionOutsideAOOA
import ProjectionOutsideOAAO
import ProjectionOutsideOAOA
import ProjectionOutsideOOAA
import ProjectionInsideAAOO
import ProjectionInsideAOAO
import ProjectionInsideAOOA
import ProjectionInsideOAAO
import ProjectionInsideOAOA
import ProjectionInsideOOAA
import ProjectionCrossAAOO
import ProjectionCrossAOAO
import ProjectionCrossAOOA
import ProjectionCrossOAAO
import ProjectionCrossOAOA
import ProjectionCrossOOAA
namespace DisjointProjected
/-- The four charged positions contain exactly two exceptional ORs. When a cross edge is
present the path tip c is a centre. Every selector trial fails on the ten specified rows. -/
theorem no_four_selectors (inside cross o₀ o₁ o₂ o₃ : Bool)
    (cross_ok : cross = true → inside = true)
    (budget : [o₀,o₁,o₂,o₃].count true = 2)
    (p q r s t u v w : P) (a b : BitVec 12) (c : BitVec 9) :
    realizes inside cross o₀ o₁ o₂ o₃ p q r s t u v w a b c = false := by
  cases inside <;> cases cross <;> cases o₀ <;> cases o₁ <;> cases o₂ <;> cases o₃
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exact outside_AAOO p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exact outside_AOAO p q r s t u v w a b c
  · exact outside_AOOA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exact outside_OAAO p q r s t u v w a b c
  · exact outside_OAOA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exact outside_OOAA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exact False.elim (Bool.noConfusion (cross_ok rfl))
  · exfalso; revert budget; decide
  · exact False.elim (Bool.noConfusion (cross_ok rfl))
  · exact False.elim (Bool.noConfusion (cross_ok rfl))
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exact False.elim (Bool.noConfusion (cross_ok rfl))
  · exact False.elim (Bool.noConfusion (cross_ok rfl))
  · exfalso; revert budget; decide
  · exact False.elim (Bool.noConfusion (cross_ok rfl))
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exact inside_AAOO p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exact inside_AOAO p q r s t u v w a b c
  · exact inside_AOOA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exact inside_OAAO p q r s t u v w a b c
  · exact inside_OAOA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exact inside_OOAA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exact cross_AAOO p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exact cross_AOAO p q r s t u v w a b c
  · exact cross_AOOA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exact cross_OAAO p q r s t u v w a b c
  · exact cross_OAOA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exact cross_OOAA p q r s t u v w a b c
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide
  · exfalso; revert budget; decide

#print axioms no_four_selectors
end DisjointProjected
