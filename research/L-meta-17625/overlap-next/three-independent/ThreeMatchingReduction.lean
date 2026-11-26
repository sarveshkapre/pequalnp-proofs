import MatchingPhysical
import MatchingBridge
import MatchingTerminals

namespace ThreeMatchingBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev PairwiseDisjoint (U : Finset (Sym2 (Fin n))) :=
  ∀ {e f}, e ∈ U → f ∈ U → e ≠ f → ∀ x : Fin n, x ∈ e → x ∉ f

/-- A failing physical circuit with three disjoint residual edges gives
one set of fixed selectors accepting all three diagonal pairs. Every witness
top rejects every independent input on the six distinguished vertices. -/
theorem failure_realizes (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (disjoint : PairwiseDisjoint (Ustar G C)) (S : Finset (Fin n)) (f : S → Fin n)
    (inj : Function.Injective f) (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i))
    (failure : ¬ GeneralThree.wireBound G C S) :
    ∃ c o s t selected, MatchProjected.Realizes c o s t selected := by
  classical
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < (Ustar G C).card by omega)
  have edges : G.edgeFinset.Nonempty := ⟨e,(Finset.mem_sdiff.mp he).1⟩
  obtain ⟨D⟩ := MatchingLabels.of_failure four bip edges least top three disjoint S f inj partners failure
  obtain ⟨twoAnd,empty,twoOr,_⟩ := GeneralThree.remaining G C four edges least top three S f inj partners failure
  have empty' := Finset.card_eq_zero.mp empty
  have active := ActiveOr.three_need_both bip four least top empty' twoAnd twoOr (Ustar G C)
    Finset.Subset.rfl three.ge (fun _ he _ hf => disjoint he hf)
  have b := MatchingBridge.facts D four least.1
  obtain ⟨o,s,t,ops,l,r,ports⟩ := MatchingPhysical.encode (MatchingBridge.v D) (MatchingBridge.code D)
    least.1 top twoAnd twoOr active b.literal b.ordinary
  obtain ⟨sel,yes⟩ := MatchingTerminals.assemble D least empty' _ _ b.graph b.leaf b.center
    b.positive b.negative o s t ops l r ports
  exact ⟨_,o,s,t,sel,yes⟩

#print axioms failure_realizes
end ThreeMatchingBound
