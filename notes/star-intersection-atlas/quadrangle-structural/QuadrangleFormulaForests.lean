import ThreeIntersectionsQuadrangle

/-!
The complement of a two-rectangle superset is a pair of disjoint stars.

The geometric lemma is independent of the quadrangle and its dimensions.  A
finite C4-free graph with no full row or column forces each of the two cross
rectangles to be a star.  The finite quadrangle certificates below use only
these small subgraphs; they do not enumerate circuits or invoke a SAT solver.
-/
namespace QuadrangleFormulaForests
open Set TwoIntersections ThreeIntersectionsQuadrangle

variable {ι κ : Type*}

/-- The two pieces use disjoint row supports and disjoint column supports. -/
def Separate (s t : Set (ι × κ)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ t, x.1 ≠ y.1 ∧ x.2 ≠ y.2

/-- The complement of two rectangles is two cross rectangles when every row
and every column has a point in their union. -/
theorem complement_two_rectangles {a b : Set (ι × κ)}
    (ha : Rectangle a) (hb : Rectangle b)
    (hrow : ∀ i, ∃ j, (i,j) ∈ a ∪ b)
    (hcol : ∀ j, ∃ i, (i,j) ∈ a ∪ b) :
    ∃ s t, Rectangle s ∧ Rectangle t ∧ Separate s t ∧ (a ∪ b)ᶜ = s ∪ t := by
  classical
  obtain ⟨ar, ac, rfl⟩ := ha
  obtain ⟨br, bc, rfl⟩ := hb
  have hr : ∀ i, i ∈ ar ∨ i ∈ br := by
    intro i
    obtain ⟨j,hj⟩ := hrow i
    exact hj.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hc : ∀ j, j ∈ ac ∨ j ∈ bc := by
    intro j
    obtain ⟨i,hi⟩ := hcol j
    exact hi.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  refine ⟨arᶜ ×ˢ bcᶜ, brᶜ ×ˢ acᶜ, ⟨_,_,rfl⟩, ⟨_,_,rfl⟩, ?_, ?_⟩
  · intro x hx y hy
    constructor
    · intro heq
      exact (hr x.1).elim hx.1 (fun h => hy.1 (heq ▸ h))
    · intro heq
      exact (hc x.2).elim (fun h => hy.2 (heq ▸ h)) hx.2
  · ext x
    have h₁ := hr x.1
    have h₂ := hc x.2
    simp only [mem_compl_iff, mem_union, mem_prod]
    tauto

/-- A C4-free incidence relation contains no rectangle with two rows and two
columns. -/
def C4Free (g : Set (ι × κ)) : Prop :=
  ∀ i i' j j', (i,j) ∈ g → (i,j') ∈ g → (i',j) ∈ g → (i',j') ∈ g →
    i = i' ∨ j = j'

theorem rectangle_is_star {g s : Set (ι × κ)} (hg : C4Free g)
    (hs : Rectangle s) (hsub : s ⊆ g) (hne : s.Nonempty) :
    (∃ i, ∀ p ∈ s, p.1 = i) ∨ (∃ j, ∀ p ∈ s, p.2 = j) := by
  classical
  obtain ⟨r,c,rfl⟩ := hs
  obtain ⟨x,hx⟩ := hne
  by_cases hr : ∀ p ∈ r ×ˢ c, p.1 = x.1
  · exact Or.inl ⟨x.1,hr⟩
  · push Not at hr
    obtain ⟨y,hy,hxy⟩ := hr
    refine Or.inr ⟨x.2,?_⟩
    intro p hp
    have h := hg y.1 x.1 p.2 x.2
      (hsub ⟨hy.1,hp.2⟩) (hsub ⟨hy.1,hx.2⟩)
      (hsub ⟨hx.1,hp.2⟩) (hsub ⟨hx.1,hx.2⟩)
    exact h.resolve_left hxy

theorem graph_c4free : C4Free graph := by
  unfold C4Free graph mask
  simp only [mem_ofPred_eq]
  decide +kernel

theorem graph_has_zero_in_every_row : ∀ i : Fin 5, ∃ j : Fin 6, (i,j) ∈ zero := by
  unfold zero graph mask
  decide +kernel

theorem graph_has_zero_in_every_column : ∀ j : Fin 6, ∃ i : Fin 5, (i,j) ∈ zero := by
  unfold zero graph mask
  decide +kernel

theorem quadrangle_complement_two_rectangles {a b : Set Cell}
    (ha : Rectangle a) (hb : Rectangle b) (hz : zero ⊆ a ∪ b) :
    ∃ s t, Rectangle s ∧ Rectangle t ∧ s ⊆ graph ∧ t ⊆ graph ∧
      Separate s t ∧ (a ∪ b)ᶜ = s ∪ t := by
  classical
  obtain ⟨s,t,hs,ht,hsep,heq⟩ := complement_two_rectangles ha hb
    (fun i => (graph_has_zero_in_every_row i).imp fun _ h => hz h)
    (fun j => (graph_has_zero_in_every_column j).imp fun _ h => hz h)
  have hsub : s ∪ t ⊆ graph := by
    intro p hp
    by_contra hn
    have hzero : p ∈ zero := hn
    have hout : p ∈ (a ∪ b)ᶜ := heq.symm ▸ hp
    exact hout (hz hzero)
  exact ⟨s,t,hs,ht,fun _ h => hsub (Or.inl h), fun _ h => hsub (Or.inr h),hsep,heq⟩

/-- Select an arbitrary subset of three listed points. Repeated points are
allowed, so this also codes stars of degree less than three. -/
def selectThree {α : Type*} (v : Fin 3 → α) (b : Fin 8) : Set α :=
  {p | ∃ k : Fin 3, b.val.testBit k.val = true ∧ p = v k}

theorem subset_three_code {α : Type*} (v : Fin 3 → α) (s : Set α)
    (hs : ∀ p ∈ s, p = v 0 ∨ p = v 1 ∨ p = v 2) :
    ∃ b : Fin 8, s = selectThree v b := by
  classical
  have represent : ∀ b : Fin 8, (∀ k : Fin 3, b.val.testBit k.val = true ↔ v k ∈ s) →
      s = selectThree v b := by
    intro b hb
    ext p
    constructor
    · intro hp
      rcases hs p hp with h | h | h
      · exact ⟨0, (hb 0).mpr (h ▸ hp), h⟩
      · exact ⟨1, (hb 1).mpr (h ▸ hp), h⟩
      · exact ⟨2, (hb 2).mpr (h ▸ hp), h⟩
    · rintro ⟨k,hk,rfl⟩
      exact (hb k).mp hk
  by_cases h₀ : v 0 ∈ s <;> by_cases h₁ : v 1 ∈ s <;> by_cases h₂ : v 2 ∈ s
  · refine ⟨7,represent 7 ?_⟩
    intro k; fin_cases k <;> simp_all [Nat.testBit]
  · refine ⟨3,represent 3 ?_⟩
    intro k; fin_cases k <;> simp_all [Nat.testBit]
  · refine ⟨5,represent 5 ?_⟩
    intro k; fin_cases k <;> simp_all [Nat.testBit]
  · refine ⟨1,represent 1 ?_⟩
    intro k; fin_cases k <;> simp_all [Nat.testBit]
  · refine ⟨6,represent 6 ?_⟩
    intro k; fin_cases k <;> simp_all [Nat.testBit]
  · refine ⟨2,represent 2 ?_⟩
    intro k; fin_cases k <;> simp_all [Nat.testBit]
  · refine ⟨4,represent 4 ?_⟩
    intro k; fin_cases k <;> simp_all [Nat.testBit]
  · refine ⟨0,represent 0 ?_⟩
    intro k; fin_cases k <;> simp_all [Nat.testBit]

def starPoints : Fin 11 → Fin 3 → Cell := ![
  ![(0,0),(0,4),(0,5)], ![(1,1),(1,3),(1,5)],
  ![(2,1),(2,2),(2,4)], ![(3,0),(3,2),(3,3)],
  ![(4,0),(4,1),(4,1)],
  ![(0,0),(3,0),(4,0)], ![(1,1),(2,1),(4,1)],
  ![(2,2),(3,2),(3,2)], ![(1,3),(3,3),(3,3)],
  ![(0,4),(2,4),(2,4)], ![(0,5),(1,5),(1,5)]]

private theorem row_star_points : ∀ (i : Fin 5) (p : Cell), p ∈ graph → p.1 = i →
    p = starPoints ⟨i.val, by omega⟩ 0 ∨
    p = starPoints ⟨i.val, by omega⟩ 1 ∨
    p = starPoints ⟨i.val, by omega⟩ 2 := by
  unfold graph mask starPoints
  simp only [mem_ofPred_eq]
  decide +kernel

private theorem column_star_points : ∀ (j : Fin 6) (p : Cell), p ∈ graph → p.2 = j →
    p = starPoints ⟨5+j.val, by omega⟩ 0 ∨
    p = starPoints ⟨5+j.val, by omega⟩ 1 ∨
    p = starPoints ⟨5+j.val, by omega⟩ 2 := by
  unfold graph mask starPoints
  simp only [mem_ofPred_eq]
  decide +kernel

theorem rectangle_star_code {s : Set Cell} (hs : Rectangle s) (hg : s ⊆ graph) :
    ∃ i : Fin 11, ∃ b : Fin 8, s = selectThree (starPoints i) b := by
  classical
  by_cases he : s = ∅
  · exact ⟨0,0,he.trans (by ext p; simp [selectThree])⟩
  · rcases rectangle_is_star graph_c4free hs hg (Set.nonempty_iff_ne_empty.mpr he) with
      ⟨i,hi⟩ | ⟨j,hj⟩
    · obtain ⟨b,hb⟩ := subset_three_code (starPoints ⟨i.val,by omega⟩) s
        (fun p hp => row_star_points i p (hg hp) (hi p hp))
      exact ⟨⟨i.val,by omega⟩,b,hb⟩
    · obtain ⟨b,hb⟩ := subset_three_code (starPoints ⟨5+j.val,by omega⟩) s
        (fun p hp => column_star_points j p (hg hp) (hj p hp))
      exact ⟨⟨5+j.val,by omega⟩,b,hb⟩

#print axioms complement_two_rectangles
#print axioms rectangle_is_star
#print axioms quadrangle_complement_two_rectangles
end QuadrangleFormulaForests
