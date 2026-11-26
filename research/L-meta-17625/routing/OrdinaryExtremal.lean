import CentreSeparation
import ExtremalCover
import SharedSwitch

namespace CentreSeparation
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- If the naive cover size is optimal, all residual edges are simultaneously
separated from all endpoint transversals by centreless tops and promotions
reaching the singleton sides of ordinary tops. -/
theorem extremal (four : NoFourCycle G) (least : IsLeastAO G C)
    (lower : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set _) →
      (tops G C \ centreless G C).card + (Ustar G C).card ≤ K.card) :
    ∃ (e : Fin (Ustar G C).card → Bool → Fin n)
        (neg : (Fin (Ustar G C).card → Bool) → Fin n → Bool) (S : Finset ℕ),
      (∀ b, graphFun G ∅ (neg b) = false) ∧
      (∀ b i, neg b (e i (b i)) = true) ∧
      (∀ h ∈ S, SharedSwitch.belowAnd n C (n+h)) ∧
      (∀ i, ∃ h ∈ centreless G C ∪ S, gateVal n C h (pairInput (e i false) (e i true)) = true) ∧
      ∀ b h, h ∈ centreless G C ∪ S → gateVal n C h (neg b) = false := by
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
  obtain ⟨port,z,one,serve⟩ := ordinaryStars four least.1
  let leaves (a : Ordinary G C) := side (n := n) C a.val (1-port a)
  have routes (u v : Fin n) (uv : G.Adj u v) :
      (∃ a, (u=z a ∧ v∈leaves a) ∨ (v=z a ∧ u∈leaves a)) ∨
        ∃ i, s(u,v) = s(ends i false,ends i true) := by
    by_cases h : s(u,v) ∈ U
    · let q : U := ⟨s(u,v),h⟩
      exact Or.inr ⟨lookup q,by simpa [q] using rep (lookup q)⟩
    · exact Or.inl (serve u v (SimpleGraph.deleteEdges_adj.mpr ⟨uv,h⟩))
  obtain ⟨outside,neg,noEdge,contains,leaf⟩ := ExtremalCover.transversals G z leaves ends pos routes
    (by simpa [U, Ordinary] using lower)
  obtain ⟨S, form, yes, no⟩ := separate least port z one (fun i => (ends i false, ends i true))
    pos outside neg noEdge leaf
  refine ⟨ends,neg,S,noEdge,contains,?_,yes,no⟩
  intro h mem
  obtain ⟨_,_,a,path⟩ := form h mem
  have data := topData (Finset.mem_sdiff.mp a.2).1
  exact ⟨a.val,data.1,data.2.1,port a,(orReaches_reach h _ path).1⟩

#print axioms extremal
end CentreSeparation
