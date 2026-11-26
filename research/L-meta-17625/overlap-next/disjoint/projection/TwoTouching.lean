import ThreeDisjoint
import ProjectionExclusion

namespace DisjointEdgeBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem finite_exclusion : FiniteExclusion := by
  intro i x cross_ok op two p l r c
  have counted : ∀ a b c d : Bool,
      (Finset.univ.filter fun j : Fin 4 => (![a,b,c,d] : Fin 4 → Bool) j = true).card =
        [a,b,c,d].count true := by decide
  have repr : op = ![op 0,op 1,op 2,op 3] := by
    funext j; fin_cases j <;> rfl
  have budget : [op 0,op 1,op 2,op 3].count true = 2 := by
    rw [← counted, ← repr]; exact two
  exact DisjointProjected.no_four_selectors i x _ _ _ _ cross_ok budget
    (p 0 0) (p 0 1) (p 1 0) (p 1 1) (p 2 0) (p 2 1) (p 3 0) (p 3 1) l r c

/-- Amritpal's repeated-read inequality for residual edges ab, bc, de
on five distinct vertices, for every choice of matching. -/
theorem two_touching_and_one_separate (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i))
    (v : Fin 5 → Fin n) (distinct : Function.Injective v)
    (shape : Ustar G C = PrivateMatching.shape (v 0) (v 1) (v 2) (v 3) (v 4)) :
    GeneralThree.wireBound G C S := by
  have edge : s(v 0,v 1) ∈ Ustar G C := by rw [shape]; simp [PrivateMatching.shape]
  exact bound_of_exclusion finite_exclusion four bip ⟨_, (Finset.mem_sdiff.mp edge).1⟩
    least top S f inj partners v distinct shape

/-- Every pair of different residual edges in any three-edge failure is disjoint. -/
theorem failure_requires_three_disjoint (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (failure : ¬GeneralThree.wireBound G C S)
    {p q : Sym2 (Fin n)} (hp : p ∈ Ustar G C) (hq : q ∈ Ustar G C) (ne : p ≠ q) :
    ∀ z : Fin n, z ∈ p → z ∉ q :=
  failure_disjoint_of_exclusion finite_exclusion four bip least top three S f inj partners
    failure hp hq ne

#print axioms two_touching_and_one_separate
#print axioms failure_requires_three_disjoint
end DisjointEdgeBound
