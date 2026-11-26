import ThreeMatchingReduction
import MatchExclusion
import TwoTouching

namespace ThreeMatchingBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Every matching satisfies the repeated-read bound with three pairwise disjoint residual edges. -/
theorem pairwise_disjoint (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (disjoint : PairwiseDisjoint (Ustar G C)) (S : Finset (Fin n)) (f : S → Fin n)
    (inj : Function.Injective f) (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) :
    GeneralThree.wireBound G C S := by
  by_contra failure
  obtain ⟨_, _, _, _, _, realized⟩ :=
    failure_realizes four bip least top three disjoint S f inj partners failure
  exact MatchProjected.no_realizes realized

/-- Amritpal's repeated-read inequality for all shapes of exactly three residual edges. -/
theorem all_three (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n)
    (inj : Function.Injective f) (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) :
    GeneralThree.wireBound G C S := by
  by_contra failure
  apply failure (pairwise_disjoint four bip least top three ?_ S f inj partners)
  intro p q hp hq ne
  exact DisjointEdgeBound.failure_requires_three_disjoint four bip least top three
    S f inj partners failure hp hq ne

#print axioms pairwise_disjoint
#print axioms all_three
end ThreeMatchingBound
