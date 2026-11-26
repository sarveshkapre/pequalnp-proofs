import ActiveOr
import PathPhysical
import PhysicalPortMasks

namespace MatchingGateOrder
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem plain {x y : ℕ} (p : Relation.ReflTransGen (ActiveOr.ordinaryStep G C) x y) :
    Relation.ReflTransGen (OrStep n C) x y := by
  induction p with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.1

/-- All four charged gates are in the active set in the residual-matching case. -/
theorem all_active (firsts : ActiveOr.atTops G C = orN G C \ lam G C)
    (h : ℕ) (m : h ∈ orN G C \ lam G C) : h ∈ P4Ports.active G C := by
  classical
  have hp : h ∈ ActiveOr.atTops G C := firsts ▸ m
  obtain ⟨_,_,a,ha,b,p⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨m,a,(topData ha).1,(topData ha).2.1,b,plain p⟩)

structure Ordered (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) where
  ids : Fin 4 ↪o ℕ
  active : ∀ i, ids i ∈ P4Ports.active G C
  cover : ∀ j ∈ P4Ports.active G C, ∃ i, ids i = j
  twoOr : (Finset.univ.filter (fun i => PathPhysical.kind C (ids i) = true)).card = 2

theorem ordered (twoAnd : (junk G C).card = 2) (twoOr : (orN G C \ lam G C).card = 2)
    (atTops : ActiveOr.atTops G C = orN G C \ lam G C) : Nonempty (Ordered G C) := by
  classical
  let A := junk G C
  let O := orN G C \ lam G C
  let allG := A ∪ O
  have separate : Disjoint A O := by
    apply Finset.disjoint_left.mpr
    intro j ha ho
    have left := (junkData ha).2.1
    have right := (orData ho).2.1
    rw [left] at right
    contradiction
  have size : allG.card = 4 := by
    change (A ∪ O).card = 4
    rw [Finset.card_union_of_disjoint separate,twoAnd,twoOr]
  let ids := allG.orderEmbOfFin size
  have inside (i : Fin 4) : ids i ∈ allG := allG.orderEmbOfFin_mem size i
  have rangeIds : ∀ k ∈ allG, ∃ i, ids i = k := fun k m =>
    (allG.range_orderEmbOfFin size).ge m
  have kind (i : Fin 4) : PathPhysical.kind C (ids i) = true ↔ ids i ∈ O := by
    rcases Finset.mem_union.mp (inside i) with a|o
    · have k := (junkData a).2.1
      exact ⟨fun y => by simp [PathPhysical.kind,k] at y,
        fun mo => (Finset.disjoint_left.mp separate a mo).elim⟩
    · exact ⟨fun _ => o,fun _ => by simp [PathPhysical.kind,(orData o).2.1]⟩
  refine ⟨⟨ids,?_,?_,?_⟩⟩
  · intro i
    rcases Finset.mem_union.mp (inside i) with a|o
    · exact Finset.mem_union_left _ a
    · exact all_active atTops _ o
  · intro j hj
    apply rangeIds
    rcases Finset.mem_union.mp hj with a|o
    · exact Finset.mem_union_left _ a
    · exact Finset.mem_union_right _ (Finset.mem_filter.mp o).1
  · let F := Finset.univ.filter (fun i : Fin 4 => PathPhysical.kind C (ids i) = true)
    have eq : F.image ids = O := by
      ext j
      constructor
      · rintro m
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp m
        exact (kind i).mp (Finset.mem_filter.mp hi).2
      · intro m
        obtain ⟨i,rfl⟩ := rangeIds j (Finset.mem_union_right _ m)
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(kind i).mpr m⟩,rfl⟩
    have cnt := congrArg Finset.card eq
    rwa [Finset.card_image_of_injective _ ids.injective,twoOr] at cnt

#print axioms ordered
end MatchingGateOrder
