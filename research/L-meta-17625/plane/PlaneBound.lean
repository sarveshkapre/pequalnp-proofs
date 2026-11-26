import StarGeometry
import StarGrowth
import StarPromotions
import PlaneBudget

namespace PlaneBound
open ResidualDegree PlaneFour PlaneStar PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

/-- A saturated set of twelve ordinary stars cannot recover the four incidences
of the missing vertex with two dirty ANDs and two exceptional ORs. -/
theorem star_needs_more (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
    (v : Fin 26) (removed : Ustar plane C = plane.incidenceFinset v)
    (ordinary : centreless plane C = ∅) (twelve : (tops plane C).card = 12)
    (budget : (orN plane C \ lam plane C).card ≤ 2) : 4 ≤ (junk plane C).card := by
  classical
  let L := plane.neighborFinset v
  have card : L.card = 4 := four_neighbors v
  have adj (l : Fin 26) (hl : l ∈ L) : plane.Adj v l := (plane.mem_neighborFinset _ _).mp hl
  obtain ⟨b,z,raw,inject,image,leaf⟩ := centers_and_leaves C least.1 ordinary twelve v removed
  have good (a : tops plane C) : z a ∈ other_side v := by
    rw [← image]; exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have away (a : tops plane C) : z a ≠ v ∧ z a ∉ L := by
    exact ⟨(Finset.mem_filter.mp (good a)).2.1,fun m => other_nonadjacent v _ (good a) (adj _ m).symm⟩
  have leafsize (a : tops plane C) : (side (n := 26) C a (1-b a)).card = 4 := by
    rw [leaf, four_neighbors]
  have common (a : tops plane C) : ((side (n := 26) C a (1-b a)) ∩ L).card = 1 := by
    rw [leaf]; exact one_common_neighbor v _ (good a)
  have thin (a : tops plane C) := (common a).le
  have leafAway (a : tops plane C) :
      v ∉ side (n := 26) C a (1-b a) ∧ z a ∉ side (n := 26) C a (1-b a) := by
    rw [leaf]
    exact ⟨fun m => other_nonadjacent v _ (good a) ((plane.mem_neighborFinset _ _).mp m),
      fun m => ((plane.mem_neighborFinset _ _).mp m).ne rfl⟩
  have guard (a : tops plane C) : ∃ w ∈ side (n := 26) C a (1-b a), ¬ plane.Adj v w := by
    by_contra! all
    have sub : side (n := 26) C a (1-b a) ⊆ L := fun w m => (plane.mem_neighborFinset _ _).mpr (all w m)
    have eq := Finset.inter_eq_left.mpr sub
    have many := leafsize a
    have one := common a
    rw [eq] at one; omega
  have ex := StarPromotions.raw_neighbors_le_one least budget v L (by omega) adj b z inject raw
    (fun a => Finset.card_pos.mp (by rw [leafsize]; decide)) away leafAway thin
  have ports (a : ℕ) (ha : a ∈ tops plane C) (p : Fin 2) :
      ((side (n := 26) C a p) ∩ L).card ≤ 1 := by
    let A : tops plane C := ⟨a,ha⟩
    rcases opposite (b A) p with rfl | rfl
    · change ((side (n := 26) C A (b A)) ∩ L).card ≤ 1
      rw [raw]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (Finset.card_singleton _).le
    · exact thin A
  have sparse (j : ℕ) (hj : j ∈ junk plane C) (p : Fin 2) :
      ((side (n := 26) C j p) ∩ L).card ≤ 1 := by
    have len := (junkData hj).1
    have bd := opndBound least.1 len p
    exact StarGrowth.all_raw_sparse least.1 L ports ex (opnd C j p) (by omega)
  have changes := StarGrowth.centre_changes least top v L adj b z raw away guard
  simpa [card] using StarGrowth.first_changes least.1 top v L sparse changes

#print axioms star_needs_more

/-- The whole 52-incidence plane needs at least 64 gates in this entire class.
No upper bound on wire reuse or on the number of dirty gates is assumed. -/
theorem four_size (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
    (small : (Ustar plane C).card ≤ 4) : 64 ≤ C.size := by
  classical
  by_contra! short
  have bound : C.size ≤ 63 := by omega
  by_cases three : (Ustar plane C).card ≤ 3
  · have := plane_three C least top three; omega
  have four : (Ustar plane C).card = 4 := by omega
  by_cases star : ∃ v : Fin 26, ∀ e ∈ Ustar plane C, v ∈ e
  · obtain ⟨v,h⟩ := star
    have removed := full_star v (show Ustar plane C ⊆ plane.edgeFinset from Finset.sdiff_subset) four h
    obtain ⟨j,empty,o,t⟩ := PlaneBudget.four C least top bound four
    have := star_needs_more C least top v removed empty t o.le
    omega
  · have := four_nonstar_size C least top four star; omega

/-- Starting from any exact fan-in-two AND/OR circuit for this plane, any
saving over 64 gates requires at least five residual incidences in a least top form. -/
theorem five_required (C : Circuit) (ao : IsAO2 26 C)
    (computes : circuitFun 26 C = graphFun plane ∅) (small : C.size ≤ 63) :
    ∃ D, IsLeastAO plane D ∧ TopForm plane D ∧ D.size ≤ C.size ∧
      5 ≤ (Ustar plane D).card := by
  classical
  have edges : plane.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [plane_edges]; decide)
  obtain ⟨D,least,top,bound⟩ := PEqualNP.Outside.L_meta_8567 26 plane C edges ao computes
  refine ⟨D,least,top,bound,?_⟩
  by_contra! h
  have := four_size D least top (by omega)
  omega

/-- L-meta-17625's read count holds for every matching on this plane throughout
the four-residual-edge class. -/
theorem repeat_four (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
    (small : (Ustar plane C).card ≤ 4) (S : Finset (Fin 26)) (f : S → Fin 26)
    (inj : Function.Injective f) (partners : ∀ v, f v ∉ S ∧ plane.Adj v.val (f v)) :
    let uses := C.gates.flatMap Gate.inputs
    let inputs := uses.toFinset.filter fun w => w < 26
    plane.edgeFinset.card + S.card - inputs.card ≤ uses.length - uses.toFinset.card := by
  have size := four_size C least top small
  have matching := matching_card S f inj (fun v => (partners v).1)
  apply repeat_of_size plane C least.1 (by omega)
  rw [plane_edges]; omega

#print axioms four_size
#print axioms five_required
#print axioms repeat_four
end PlaneBound
