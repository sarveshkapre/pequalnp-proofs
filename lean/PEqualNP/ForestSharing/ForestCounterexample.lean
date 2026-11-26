import PEqualNP.ForestSharing.ForestGraph
import PEqualNP.ForestSharing.ForestGap

namespace ForestGap

/-- The graph tested as a circuit is the same bipartite graph proved to be a tree. -/
theorem tree_exact_gap :
    (ForestTree.graphOf edge).IsTree ∧
    ThreeIntersections.Three TwoIntersections.Rectangle zero ∧
    ¬ TwoIntersections.Two TwoIntersections.Rectangle zero ∧
    ThreeIntersectionsFormula.Formula TwoIntersections.Rectangle 4 zero ∧
    ∀ n, n < 4 → ¬ ThreeIntersectionsFormula.Formula TwoIntersections.Rectangle n zero :=
  ⟨ForestTree.isTree, exact_circuit_formula_gap⟩

end ForestGap
