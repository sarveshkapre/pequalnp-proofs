import SixEdgeAncestorOrder

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

private theorem points_first_zero {k : Case} (mem : (k,.points) ∈ keys) : firstBit k.1 = 0 := by
  have ok : keys.all (fun key => decide (key.2 = .points → firstBit key.1.1 = 0)) = true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp ok _ mem)) rfl

/-- If the first AND uses points alone, any OR carrying it to a centre
    would make an ordinary top fire on the edge-free all-points input. -/
theorem physical_centre_exclusion (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (first j : Fin 5) (centre : Option (Fin 13))
    (choice : ReplayChoice S (GateSchedule.rawFirst P least).masks
      (gateOrder count ((GateSchedule.rawFirst P least).index.symm first)).val centre)
    (firstEq : first.val = firstBit (GateSchedule.rawFirst P least).masks.1)
    (geometry : (mode choice.refinement).2.1 = 0)
    (used : (GateSchedule.rawFirst P least).masks.2.getLsbD j = true) :
    stageSource (GateSchedule.rawFirst P least) j 0 = false := by
  classical
  let A := GateSchedule.rawFirst P least
  have points : choice.refinement = .points := by
    cases h : choice.refinement <;> simp_all [mode]
  have key := choice.member
  rw [points] at key
  have zero : first = 0 := Fin.ext (firstEq.trans (points_first_zero key))
  subst first
  rcases choice with ⟨refinement,r,member,anchor,active,quiet,shape⟩
  change refinement = .points at points
  subst refinement
  apply Bool.eq_false_iff.mpr
  intro on
  obtain ⟨dirty,path⟩ : dirtySource count (26+(gateOrder count (A.index.symm j)).val) (A.index.symm 0) :=
    of_decide_eq_true on
  simp only [GateSchedule.masks,ofSlots_bit,decide_eq_true_eq] at used
  obtain ⟨_,l,route⟩ := used
  obtain ⟨_,_,reach⟩ := Finset.mem_filter.mp route.1
  apply first_points_avoid_centre S least top empty (of_decide_eq_true dirty)
    (GateSchedule.dirty_at_head_is_first least (A.index.apply_symm_apply 0) dirty) shape l
  exact (orReaches_reach _ _ reach).1.trans path

end SixEdge.Plane
