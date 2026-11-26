import ProtectedTriple
import ExtremalCover

namespace ProtectedResiduals
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- When every ordinary top and every residual edge must contribute separately
to a vertex cover, the residual edges are simultaneously protected.
Their number is bounded by the total number of dirty ANDs. -/
theorem extremal_limits (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅)
    (lower : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set _) →
      (tops G C).card + (Ustar G C).card ≤ K.card) :
    (Ustar G C).card ≤ (junk G C).card ∧
      ((junk G C).card ≤ 3 → (orN G C \ lam G C).card ≤ 2 → (Ustar G C).card ≤ 2) := by
  classical
  let U := Ustar G C
  let lookup : U ≃ Fin U.card := Fintype.equivFinOfCardEq (by simp)
  have endpoint (q : U) : ∃ a b : Fin n, q.val = s(a,b) := by
    induction q.val using Sym2.ind with | _ u v => exact ⟨u,v,rfl⟩
  choose l r decomp using endpoint
  let ends (i : Fin U.card) (b : Bool) := if b then r (lookup.symm i) else l (lookup.symm i)
  have rep (i : Fin U.card) : (lookup.symm i).val = s(ends i false,ends i true) := by
    simpa [ends] using decomp (lookup.symm i)
  have pos (i : Fin U.card) : G.Adj (ends i false) (ends i true) := by
    have m : s(ends i false,ends i true) ∈ G.edgeFinset := by
      rw [←rep]
      exact (Finset.mem_sdiff.mp (lookup.symm i).2).1
    exact SimpleGraph.mem_edgeFinset.mp m
  obtain ⟨port,z,one,serve⟩ := topIndexedStars four least.1 empty
  let leaves (a : tops G C) := side (n := n) C a (1-port a)
  have routes (u v : Fin n) (uv : G.Adj u v) :
      (∃ a, (u=z a ∧ v∈leaves a) ∨ (v=z a ∧ u∈leaves a)) ∨
        ∃ i, s(u,v) = s(ends i false,ends i true) := by
    by_cases h : s(u,v) ∈ U
    · let q : U := ⟨s(u,v),h⟩
      exact Or.inr ⟨lookup q,by simpa [q] using rep (lookup q)⟩
    · exact Or.inl (serve u v (SimpleGraph.deleteEdges_adj.mpr ⟨uv,h⟩))
  obtain ⟨outside,neg,noEdge,contains,leaf⟩ := ExtremalCover.transversals G z leaves ends pos routes
    (by simpa [U] using lower)
  exact limits least top port z one ends pos outside neg noEdge contains leaf

/-- The strict improvement over adding one cover vertex per residual edge. -/
theorem cover_saves_one (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅)
    (threshold : (junk G C).card < (Ustar G C).card ∨
      (2 < (Ustar G C).card ∧ (junk G C).card ≤ 3 ∧ (orN G C \ lam G C).card ≤ 2)) :
    ∃ K : Finset (Fin n), G.IsVertexCover (K : Set _) ∧ K.card < (tops G C).card + (Ustar G C).card := by
  by_contra! none
  have bounds := extremal_limits four least top empty none
  rcases threshold with few | ⟨three,small,ors⟩
  · omega
  · have two := bounds.2 small ors
    omega

#print axioms extremal_limits
#print axioms cover_saves_one
end ProtectedResiduals
