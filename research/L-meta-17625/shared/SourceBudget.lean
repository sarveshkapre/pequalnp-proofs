import PEqualNP.Outside.L_meta_7465

/-! Resource patterns left by the three-residual-edge matching question. -/

namespace ResidualSourceBudget
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_7465_aux
open PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev residualCount (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) := (Ustar G C).card
abbrev dirtyCount (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) := (junk G C).card
abbrev centreCount (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) := (centreless G C).card
abbrev extraORCount (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) := (orN G C \ lam G C).card

/-- With residual edges and no centreless top, some AND output reaches a top
through an OR outside Lambda. Both routing facts are upstream. -/
theorem extraOR_of_no_centre (least : IsLeastAO G C) (top : TopForm G C)
    (hu : 0 < residualCount G C) (hc : centreCount G C = 0) : 0 < extraORCount G C := by
  classical
  have emp : centreless G C = ∅ := Finset.card_eq_zero.mp hc
  obtain ⟨e, he⟩ := Finset.card_pos.mp hu
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨a,ha,b,j,hj,_,path,_⟩ := residualTrace least top he
    obtain ⟨m,hm,_,_⟩ := residualPath least.1 emp ha hj path
    exact Finset.card_pos.mpr ⟨m,hm⟩

/-- Compilation of the general, reusable one-source results hidden inside the
11-vertex proof. Any selected subset of residual edges can be used here. -/
theorem pays_with_one_source (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (hu : 3 ≤ residualCount G C) (hj : 2 ≤ dirtyCount G C)
    (sources : centreCount G C + extraORCount G C ≤ 1)
    (M : Finset (Sym2 (Fin n))) (sub : M ⊆ Ustar G C) :
    residualCount G C + M.card ≤ dirtyCount G C + 2 * centreCount G C + extraORCount G C := by
  have m : M.card ≤ residualCount G C := Finset.card_le_card sub
  by_cases zero : centreCount G C = 0
  · have pos := extraOR_of_no_centre least top (by omega) zero
    have enough := oneMixingPays (h₄ := four) least top hu (Finset.card_eq_zero.mp zero)
      (show extraORCount G C = 1 by omega)
    change 2 * residualCount G C ≤ 2 * centreCount G C + dirtyCount G C + extraORCount G C at enough
    omega
  · have h := oneCentrePays four least top (Finset.card_pos.mp (show 0 < residualCount G C by omega))
      hj (show centreCount G C = 1 by omega)
      (Finset.card_eq_zero.mp (show extraORCount G C = 0 by omega))
    change 2 * residualCount G C ≤ 2 * centreCount G C + dirtyCount G C + extraORCount G C at h
    omega

/-- Failure of the sufficient inequality at three residual edges requires
one of these four resource patterns, regardless of the graph or where OR gates overlap.
The first pattern can obstruct a two-edge matching; the others need all three. -/
theorem possible_obstructions (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (hu : residualCount G C = 3) (hj : 2 ≤ dirtyCount G C)
    (M : Finset (Sym2 (Fin n))) (sub : M ⊆ Ustar G C)
    (unpaid : dirtyCount G C + 2 * centreCount G C + extraORCount G C < residualCount G C + M.card) :
    (dirtyCount G C = 2 ∧ centreCount G C = 0 ∧ extraORCount G C = 2 ∧ 2 ≤ M.card) ∨
    (M.card = 3 ∧ ((dirtyCount G C = 2 ∧ centreCount G C = 0 ∧ extraORCount G C = 3) ∨
      (dirtyCount G C = 3 ∧ centreCount G C = 0 ∧ extraORCount G C = 2) ∨
      (dirtyCount G C = 2 ∧ centreCount G C = 1 ∧ extraORCount G C = 1))) := by
  have m : M.card ≤ residualCount G C := Finset.card_le_card sub
  have sources : 2 ≤ centreCount G C + extraORCount G C := by
    by_contra! h
    have paid := pays_with_one_source four least top (by omega) hj (by omega) M sub
    omega
  omega

#print axioms pays_with_one_source
#print axioms possible_obstructions
end ResidualSourceBudget
