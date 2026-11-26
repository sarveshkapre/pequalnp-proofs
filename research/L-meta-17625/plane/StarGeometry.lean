import FourEdges
import PEqualNP.Outside.L_meta_7465

open ResidualDegree PlaneFour
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux

namespace PlaneStar

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

/-- The twelve vertices on the side of v other than v itself. -/
def other_side (v : Fin 26) := Finset.univ.filter fun x : Fin 26 => x ≠ v ∧ (x.val < 13 ↔ v.val < 13)

theorem other_card : ∀ v, (other_side v).card = 12 := by decide
theorem four_neighbors : ∀ v, (plane.neighborFinset v).card = 4 := by decide
theorem other_nonadjacent : ∀ v, ∀ x ∈ other_side v, ¬ plane.Adj x v := by decide
theorem other_independent : ∀ v, ∀ x ∈ other_side v, ∀ y ∈ other_side v, ¬plane.Adj x y := by decide
theorem one_common_neighbor : ∀ v, ∀ x ∈ other_side v,
    ((plane.neighborFinset x) ∩ plane.neighborFinset v).card = 1 := by decide
theorem center_not_other : ∀ v, v ∉ other_side v := by decide
theorem incident_four : ∀ v, (plane.incidenceFinset v).card = 4 := by
  simpa using four_neighbors

theorem full_star {U : Finset (Sym2 (Fin 26))} (v : Fin 26)
    (sub : U ⊆ plane.edgeFinset) (four : U.card = 4) (star : ∀ e ∈ U, v ∈ e) :
    U = plane.incidenceFinset v := by
  apply Finset.eq_of_subset_of_card_le _ (by rw [four,incident_four])
  intro e he
  rw [plane.incidenceFinset_eq_filter]
  exact Finset.mem_filter.mpr ⟨sub he,star e he⟩

/-- Twelve vertices cover 48 retained incidences only if none covers a removed incidence. -/
private theorem disjoint_from_removed {U : Finset (Sym2 (Fin 26))}
    {K : Finset (Fin 26)} (sub : U ⊆ plane.edgeFinset) (four : U.card = 4)
    (cov : (plane.deleteEdges ↑U).IsVertexCover (K : Set _)) (small : K.card ≤ 12) :
    ∀ x ∈ K, ∀ e ∈ U, x ∉ e := by
  classical
  intro x hx e he contains
  have cov' : (plane.deleteEdges ↑(U.erase e)).IsVertexCover (K : Set _) := by
    intro u w h
    obtain ⟨adj,old⟩ := SimpleGraph.deleteEdges_adj.mp h
    by_cases eq : s(u,w) = e
    · rw [← eq] at contains
      rcases Sym2.mem_iff.mp contains with h | h
      · exact Or.inl (h ▸ hx)
      · exact Or.inr (h ▸ hx)
    · exact cov (SimpleGraph.deleteEdges_adj.mpr ⟨adj,fun mem => old (Finset.mem_erase.mpr ⟨eq,mem⟩)⟩)
  have cap := remaining_edges plane (U.erase e) K 4 plane_degree cov'
  have count := Finset.card_sdiff_add_card_eq_card
    (show U.erase e ⊆ plane.edgeFinset from (Finset.erase_subset _ _).trans sub)
  rw [Finset.card_erase_of_mem he, four, plane_edges] at count
  omega

/-- The twelve-cover of the order-three plane after deleting a full star is unique. -/
theorem unique_cover (v : Fin 26) (K : Finset (Fin 26))
    (cov : (plane.deleteEdges ↑(plane.incidenceFinset v)).IsVertexCover (K : Set _))
    (small : K.card ≤ 12) : K = other_side v := by
  classical
  have sub : plane.incidenceFinset v ⊆ plane.edgeFinset := by
    rw [plane.incidenceFinset_eq_filter]; exact Finset.filter_subset _ _
  have dis := disjoint_from_removed sub (incident_four v) cov small
  symm
  apply Finset.eq_of_subset_of_card_le _ (by simpa [other_card] using small)
  intro x hx
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < ((plane.neighborFinset x) ∩ plane.neighborFinset v).card by rw [one_common_neighbor v x hx]; decide)
  obtain ⟨xw,vw⟩ := Finset.mem_inter.mp hw
  have adj := (plane.mem_neighborFinset _ _).mp vw
  have e_mem : s(v,w) ∈ plane.incidenceFinset v := by
    rw [plane.incidenceFinset_eq_filter]
    exact Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr adj, Sym2.mem_mk_left _ _⟩
  have keep : s(x,w) ∉ plane.incidenceFinset v := by
    rw [plane.incidenceFinset_eq_filter]
    intro mem
    rcases Sym2.mem_iff.mp (Finset.mem_filter.mp mem).2 with a|b
    · exact (Finset.mem_filter.mp hx).2.1 a.symm
    · exact adj.ne b
  exact (cov (SimpleGraph.deleteEdges_adj.mpr ⟨(plane.mem_neighborFinset _ _).mp xw,keep⟩)).resolve_right
    (fun hw => dis w hw _ e_mem (Sym2.mem_mk_right _ _))

/-- Every one of the twelve top ANDs has its own center, and its opposite raw
port contains all four neighbors. -/
theorem centers_and_leaves (C : Circuit) (ao : IsAO2 26 C)
    (empty : centreless plane C = ∅) (size : (tops plane C).card = 12)
    (v : Fin 26) (removed : Ustar plane C = plane.incidenceFinset v) :
    ∃ (b : tops plane C → Fin 2) (z : tops plane C → Fin 26),
      (∀ a : tops plane C, side (n := 26) C a (b a) = {z a}) ∧ Function.Injective z ∧
      Finset.univ.image z = other_side v ∧
      ∀ a : tops plane C, side C a (1-b a) = plane.neighborFinset (z a) := by
  classical
  obtain ⟨b,z,single,route⟩ := topIndexedStars plane_four ao empty
  let K := Finset.univ.image z
  have mem (a : tops plane C) : z a ∈ K := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have cov : (plane.deleteEdges ↑(Ustar plane C)).IsVertexCover (K : Set _) := by
    intro u w h
    obtain ⟨a,⟨rfl,_⟩|⟨rfl,_⟩⟩ := route u w h
    · exact Or.inl (mem a)
    · exact Or.inr (mem a)
  rw [removed] at cov
  have card : K.card ≤ 12 := Finset.card_image_le.trans (by simp [size])
  have eq := unique_cover v K cov card
  have zGood (a : tops plane C) : z a ∈ other_side v := eq ▸ mem a
  have count : (Finset.univ.image z).card = (Finset.univ : Finset (tops plane C)).card := by
    change K.card = _; rw [eq,other_card]; simp [size]
  have inj : Function.Injective z := fun a d => (Finset.injOn_of_card_image_eq count) (Finset.mem_univ a) (Finset.mem_univ d)
  refine ⟨b,z,single,inj,eq,?_⟩
  intro a
  apply Finset.Subset.antisymm
  · intro w hw
    apply (plane.mem_neighborFinset _ _).mpr
    have hz : z a ∈ side C a (b a) := by simp [single]
    rcases (show b a = 0 ∨ b a = 1 by have := (b a).isLt; omega) with val | val
    · simp only [val] at hz hw
      exact PEqualNP.Outside.L_meta_7465_aux.Routing.topAdj ao a.2 hz hw
    · simp only [val] at hz hw
      exact (PEqualNP.Outside.L_meta_7465_aux.Routing.topAdj ao a.2 hw hz).symm
  · intro w hw
    have adj := (plane.mem_neighborFinset _ _).mp hw
    have old : s(z a,w) ∉ Ustar plane C := by
      rw [removed,plane.incidenceFinset_eq_filter]
      intro h
      rcases Sym2.mem_iff.mp (Finset.mem_filter.mp h).2 with h|h
      · exact (Finset.mem_filter.mp (zGood a)).2.1 h.symm
      · exact other_nonadjacent v _ (zGood a) (h ▸ adj)
    obtain ⟨d,⟨h,leaf⟩|⟨h,_⟩⟩ := route (z a) w (SimpleGraph.deleteEdges_adj.mpr ⟨adj,old⟩)
    · simpa [inj h] using leaf
    · exact (other_independent v _ (zGood a) w (h ▸ zGood d) adj).elim

#print axioms unique_cover
#print axioms centers_and_leaves
end PlaneStar
