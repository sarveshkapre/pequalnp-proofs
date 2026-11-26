import MatchProjected
import MatchingRows
import MatchingLabels

namespace MatchingTerminals
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
abbrev mask (v : Fin 6 → Fin n) (a : tops G C) (p : Fin 2) :=
  MatchingRows.raw v (side (n := n) C a p)

private theorem top_eval (ao : IsAO2 n C) (a : tops G C) (p : Fin 2) (x : Fin n → Bool) :
    (val C (List.ofFn x) (opnd C a p) && val C (List.ofFn x) (opnd C a (1-p))) =
      gateVal n C a x := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true,andValOperands ao (topData a.2).1 (topData a.2).2.1]
  constructor
  · rintro ⟨yes,other⟩ j
    rcases opposite p j with rfl | rfl
    · exact yes
    · exact other
  · intro h; exact ⟨h _,h _⟩

/-- Use one actual accepting top per diagonal. Each chosen top is clean on
every graph-independent row. They may coincide, use earlier gates repeatedly,
or share either side with other tops. -/
theorem assemble (D : MatchingLabels.Labels G C) (least : IsLeastAO G C)
    (empty : centreless G C = ∅) (v : Fin 6 → Fin n) (c : MatchProjected.Cross)
    (graph : MatchProjected.graphOK c = true)
    (leaf : ∀ a : tops G C, MatchProjected.allowed c (mask v a (1-D.port a)) = true)
    (center : ∀ a : tops G C, MatchProjected.leafOK c (mask v a (D.port a))
      (mask v a (1-D.port a)) = true)
    (pos : ∀ i, MatchingRows.input v (MatchProjected.positive i) = pairInput (D.left i) (D.right i))
    (neg : ∀ r, MatchProjected.independent c r = true → graphFun G ∅ (MatchingRows.input v r) = false)
    (o : Fin 4 → Bool) (s t : Fin 4 → MatchProjected.Selector)
    (budget : (List.ofFn o).count true = 2)
    (left : ∀ i, (s i).direct = false → MatchProjected.allowed c (s i).raw = true)
    (right : ∀ i, (t i).direct = false → MatchProjected.allowed c (t i).raw = true)
    (sides : ∀ a : tops G C, ∀ p : Fin 2, (side (n := n) C a p).Nonempty →
      ∃ take : BitVec 4, ∀ r, MatchProjected.side (mask v a p) take (MatchProjected.schedule o s t) r =
        val C (List.ofFn (MatchingRows.input v r)) (opnd C a p)) :
    ∃ selected, MatchProjected.Realizes c o s t selected := by
  classical
  have edges (i : Fin 3) : G.Adj (D.left i) (D.right i) :=
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (D.diagonal i)).1
  choose gate member fires using fun i => acceptedTop least (edges i)
  let a (i : Fin 3) : tops G C := ⟨gate i, member i⟩
  choose use proof using fun (g : tops G C) p => sides g p (topSides empty g.2 p)
  let code (g : tops G C) : MatchProjected.TopSel :=
    ⟨mask v g (D.port g), mask v g (1-D.port g), use g (D.port g), use g (1-D.port g)⟩
  have eval (g : tops G C) (r : MatchProjected.Raw) :
      MatchProjected.topVal (code g) (MatchProjected.schedule o s t) r =
        gateVal n C g (MatchingRows.input v r) := by
    unfold MatchProjected.topVal code
    dsimp only
    rw [proof,proof,top_eval least.1]
  refine ⟨fun i => code (a i), ⟨graph,budget,left,right,fun i => leaf (a i),
    fun i => center (a i),?_,?_⟩⟩
  · intro i; rw [eval,pos]; exact fires i
  · intro i r h
    rw [eval]
    apply Bool.eq_false_iff.mpr
    intro on
    exact Bool.false_ne_true ((neg r h).symm.trans ((topData (a i).2).2.2 _ on))

#print axioms assemble
end MatchingTerminals
