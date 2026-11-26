import MatchingTransfer
import ExtremalRouting

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

namespace ResidualDegree

theorem repeated_reads_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (noCentreless : centreless G C = ∅)
    (three : (Ustar G C).card = 3)
    (cases : ((junk G C).card = 2 ∧ (orN G C \ lam G C).card = 3) ∨
      ((junk G C).card = 3 ∧ (orN G C \ lam G C).card = 2))
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) :
    let uses := C.gates.flatMap Gate.inputs
    let inputs := uses.toFinset.filter fun w => w < n
    G.edgeFinset.card + S.card - inputs.card ≤ uses.length - uses.toFinset.card := by
  exact transfer_three G C four edges least top noCentreless three cases
    (ProtectedResiduals.extremal_limits four least top noCentreless) S f inj partners

#print axioms ResidualDegree.repeated_reads_three

end ResidualDegree
