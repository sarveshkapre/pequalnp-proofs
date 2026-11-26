import FiveFacts
import PhysicalSchedule

namespace FiveSchedule
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {v : Fin 5 → Fin n}

/-- The physical ten test rows meet every raw-mask assumption of the
four-stage adapter. -/
def projection (D : FiveFacts.Situation G C v) (four : NoFourCycle G) (ao : IsAO2 n C) :
    PhysicalSchedule.Projection G C where
  rows := FiveRows.input v
  mask := FiveRows.raw v
  literal_spec := FiveRows.literal_spec v
  raw_sub := FiveRows.raw_sub v
  raw_union := FiveRows.raw_union v
  raw_empty := FiveRows.raw_empty v
  tag_lit := fun u => FiveRows.raw_single v u D.inj
  tag_lam := fun _ h => FiveRows.allowed_tag v D.inj _
    (ProjectionGeometry.ordinary_masks (FiveFacts.top_allowed D four ao) h)

@[simp] theorem physical (D : FiveFacts.Situation G C v) (four : NoFourCycle G)
    (ao : IsAO2 n C) (w : ℕ) :
    (projection D four ao).physical w = FiveRows.physical v C w := rfl

theorem exists_schedule (D : FiveFacts.Situation G C v) (four : NoFourCycle G)
    (ao : IsAO2 n C) (top : TopForm G C) (twoAnd : (junk G C).card = 2)
    (twoOr : (orN G C \ lam G C).card = 2) :
    Nonempty (PhysicalSchedule.Schedule (projection D four ao)) :=
  PhysicalSchedule.encode _ ao top twoAnd twoOr

#print axioms exists_schedule
end FiveSchedule
