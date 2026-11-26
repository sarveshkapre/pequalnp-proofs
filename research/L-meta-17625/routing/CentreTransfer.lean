import OrdinaryExtremal
import CentreSwitch
import MatchingTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace CentreSeparation

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- If a centreless top occurs, a circuit with as many residual edges as dirty
ANDs and centreless tops must save at least one vertex in a graph cover. -/
theorem cover_saves_one (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (cent : (centreless G C).Nonempty)
    (many : (junk G C).card + (centreless G C).card ≤ (Ustar G C).card) :
    ∃ K : Finset (Fin n), G.IsVertexCover (K : Set _) ∧
      K.card < (tops G C \ centreless G C).card + (Ustar G C).card := by
  by_contra! lower
  obtain ⟨e,neg,S,_,contains,under,yes,no⟩ := extremal four least lower
  have strict := CentreSwitch.strict_bound least.1 top cent e neg S under contains yes no
  omega

/-- The exact repeat-charge inequality of L-meta-17625 in the (2,1,1) branch.
The same proof applies whenever one saved cover vertex absorbs the gate deficit. -/
theorem repeat_charge {S : Finset (Fin n)} {f : S → Fin n}
    (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (cent : (centreless G C).Nonempty)
    (many : (junk G C).card + (centreless G C).card ≤ (Ustar G C).card)
    (budget : 2 * (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card + 1)
    (inj : Function.Injective f) (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) :
    let uses := C.gates.flatMap Gate.inputs
    let inputs := uses.toFinset.filter fun w => w < n
    G.edgeFinset.card + S.card - inputs.card ≤ uses.length - uses.toFinset.card := by
  classical
  obtain ⟨K,covers,saves⟩ := cover_saves_one four least top cent many
  have card := ResidualDegree.matched_le_cover G S f inj partners K covers
  have gate := (PEqualNP.Outside.L_meta_1491 n G C four edges least top).1
  obtain ⟨h,member⟩ := cent
  have inside : h < C.size :=
    (PEqualNP.Outside.L_meta_7465_aux.Routing.topData (Finset.mem_filter.mp member).1).1
  exact ResidualDegree.repeat_of_size G C least.1 (by omega) _ (by omega)

#print axioms cover_saves_one
#print axioms repeat_charge
end CentreSeparation
