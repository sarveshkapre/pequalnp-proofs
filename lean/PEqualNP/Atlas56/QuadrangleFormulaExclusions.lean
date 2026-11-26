import PEqualNP.Atlas56.QuadrangleFormulaCatalog

/-!
Two structural exclusions for the quadrangle.  The `U3 ∩ U2` exclusion is a
relative fooling-set argument.  The three-factor exclusion says that three
pairs of projection-disjoint stars cannot cover the 14 incidence edges.
-/
namespace QuadrangleFormulaExclusions
open Set TwoIntersections ThreeIntersectionsQuadrangle QuadrangleFormulaForests
open QuadrangleFormulaCatalog QuadranglePartialFooling
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem no_three_by_two :
    ¬ ∃ a b c d e : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧ Rectangle e ∧
        zero = ((a ∪ b) ∪ c) ∩ (d ∪ e) := by
  classical
  rintro ⟨a,b,c,d,e,ha,hb,hc,hd,he,hz⟩
  have h₂ : zero ⊆ d ∪ e := by
    intro p hp
    rw [hz] at hp
    exact hp.2
  obtain ⟨i,hi⟩ := complement_catalog hd he h₂
  apply no_union_three (forest_fooling i) ha hb hc
  · intro p hp
    rw [hz] at hp
    exact hp.1
  · apply Set.disjoint_left.mpr
    intro p hp hbad
    have hde : p ∈ d ∪ e := by
      by_contra hn
      exact hbad.2 (hi hn)
    have hzero : p ∈ zero := by
      rw [hz]
      exact ⟨hp,hde⟩
    exact hzero hbad.1

/-- The 14 actual edges, indexed independently of their 30 grid positions. -/
def edge : Fin 14 → Cell := ![(0,0), (0,4), (0,5), (1,1), (1,3), (1,5), (2,1), (2,2), (2,4), (3,0), (3,2), (3,3), (4,0), (4,1)]

/-- Each two-star forest as a subset of the 14 graph edges. -/
def compactForest : Fin 48 → BitVec 14 := ![5057, 8271, 11848, 4665, 1159, 3079, 3842, 3008, 4681, 3620, 3590, 2071, 3904, 314, 59, 31, 3624, 8777, 453, 484, 199, 1592, 2512, 496, 1208, 440, 7169, 4866, 12546, 4644, 8292, 4614, 12294, 8584, 8458, 12324, 6161, 13440, 5249, 2322, 14352, 12336, 12672, 1188, 10320, 8304, 15360, 9352]

theorem edge_in_graph : ∀ l : Fin 14, edge l ∈ graph := by
  unfold edge graph mask
  simp only [mem_ofPred_eq]
  decide +kernel

theorem compact_correct : ∀ (i : Fin 48) (l : Fin 14),
    edge l ∈ codeSet (forestCode i) ↔ (compactForest i).getLsbD l.val = true := by
  unfold edge codeSet forestCode compactForest
  simp only [mem_ofPred_eq]
  decide +kernel

private theorem ones_bits : ∀ l : Fin 14, (16383 : BitVec 14).getLsbD l.val = true := by
  decide +kernel

private theorem missing_bit {n : BitVec 14} (hn : n ≠ 16383) :
    ∃ l : Fin 14, n.getLsbD l.val = false := by
  classical
  by_contra h
  apply hn
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have hfalse : n.getLsbD i ≠ false := fun he => h ⟨⟨i,hi⟩,he⟩
  have htrue : n.getLsbD i = true := by
    cases hb : n.getLsbD i <;> simp_all
  exact htrue.trans (ones_bits ⟨i,hi⟩).symm

/-- Kernel checks are split into 48 small independent declarations to bound
replay memory. They check a finite graph covering statement, not circuits. -/
private theorem forest_triple_0 : ∀ j k : Fin 48,
    (compactForest 0 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_1 : ∀ j k : Fin 48,
    (compactForest 1 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_2 : ∀ j k : Fin 48,
    (compactForest 2 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_3 : ∀ j k : Fin 48,
    (compactForest 3 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_4 : ∀ j k : Fin 48,
    (compactForest 4 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_5 : ∀ j k : Fin 48,
    (compactForest 5 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_6 : ∀ j k : Fin 48,
    (compactForest 6 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_7 : ∀ j k : Fin 48,
    (compactForest 7 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_8 : ∀ j k : Fin 48,
    (compactForest 8 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_9 : ∀ j k : Fin 48,
    (compactForest 9 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_10 : ∀ j k : Fin 48,
    (compactForest 10 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_11 : ∀ j k : Fin 48,
    (compactForest 11 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_12 : ∀ j k : Fin 48,
    (compactForest 12 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_13 : ∀ j k : Fin 48,
    (compactForest 13 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_14 : ∀ j k : Fin 48,
    (compactForest 14 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_15 : ∀ j k : Fin 48,
    (compactForest 15 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_16 : ∀ j k : Fin 48,
    (compactForest 16 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_17 : ∀ j k : Fin 48,
    (compactForest 17 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_18 : ∀ j k : Fin 48,
    (compactForest 18 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_19 : ∀ j k : Fin 48,
    (compactForest 19 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_20 : ∀ j k : Fin 48,
    (compactForest 20 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_21 : ∀ j k : Fin 48,
    (compactForest 21 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_22 : ∀ j k : Fin 48,
    (compactForest 22 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_23 : ∀ j k : Fin 48,
    (compactForest 23 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_24 : ∀ j k : Fin 48,
    (compactForest 24 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_25 : ∀ j k : Fin 48,
    (compactForest 25 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_26 : ∀ j k : Fin 48,
    (compactForest 26 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_27 : ∀ j k : Fin 48,
    (compactForest 27 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_28 : ∀ j k : Fin 48,
    (compactForest 28 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_29 : ∀ j k : Fin 48,
    (compactForest 29 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_30 : ∀ j k : Fin 48,
    (compactForest 30 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_31 : ∀ j k : Fin 48,
    (compactForest 31 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_32 : ∀ j k : Fin 48,
    (compactForest 32 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_33 : ∀ j k : Fin 48,
    (compactForest 33 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_34 : ∀ j k : Fin 48,
    (compactForest 34 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_35 : ∀ j k : Fin 48,
    (compactForest 35 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_36 : ∀ j k : Fin 48,
    (compactForest 36 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_37 : ∀ j k : Fin 48,
    (compactForest 37 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_38 : ∀ j k : Fin 48,
    (compactForest 38 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_39 : ∀ j k : Fin 48,
    (compactForest 39 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_40 : ∀ j k : Fin 48,
    (compactForest 40 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_41 : ∀ j k : Fin 48,
    (compactForest 41 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_42 : ∀ j k : Fin 48,
    (compactForest 42 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_43 : ∀ j k : Fin 48,
    (compactForest 43 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_44 : ∀ j k : Fin 48,
    (compactForest 44 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_45 : ∀ j k : Fin 48,
    (compactForest 45 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_46 : ∀ j k : Fin 48,
    (compactForest 46 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

private theorem forest_triple_47 : ∀ j k : Fin 48,
    (compactForest 47 ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  unfold compactForest
  decide +kernel

theorem three_forests_not_full : ∀ i j k : Fin 48,
    (compactForest i ||| compactForest j) ||| compactForest k ≠ (16383 : BitVec 14) := by
  intro i
  fin_cases i
  · exact forest_triple_0
  · exact forest_triple_1
  · exact forest_triple_2
  · exact forest_triple_3
  · exact forest_triple_4
  · exact forest_triple_5
  · exact forest_triple_6
  · exact forest_triple_7
  · exact forest_triple_8
  · exact forest_triple_9
  · exact forest_triple_10
  · exact forest_triple_11
  · exact forest_triple_12
  · exact forest_triple_13
  · exact forest_triple_14
  · exact forest_triple_15
  · exact forest_triple_16
  · exact forest_triple_17
  · exact forest_triple_18
  · exact forest_triple_19
  · exact forest_triple_20
  · exact forest_triple_21
  · exact forest_triple_22
  · exact forest_triple_23
  · exact forest_triple_24
  · exact forest_triple_25
  · exact forest_triple_26
  · exact forest_triple_27
  · exact forest_triple_28
  · exact forest_triple_29
  · exact forest_triple_30
  · exact forest_triple_31
  · exact forest_triple_32
  · exact forest_triple_33
  · exact forest_triple_34
  · exact forest_triple_35
  · exact forest_triple_36
  · exact forest_triple_37
  · exact forest_triple_38
  · exact forest_triple_39
  · exact forest_triple_40
  · exact forest_triple_41
  · exact forest_triple_42
  · exact forest_triple_43
  · exact forest_triple_44
  · exact forest_triple_45
  · exact forest_triple_46
  · exact forest_triple_47

/-- Every triple from the complete catalog of 48 maximal two-star forests
misses an incidence edge. -/
theorem three_forests_do_not_cover (i j k : Fin 48) :
    ∃ p : Cell, p ∈ graph ∧
      p ∉ (codeSet (forestCode i) ∪ codeSet (forestCode j)) ∪ codeSet (forestCode k) := by
  obtain ⟨l,hl⟩ := missing_bit (three_forests_not_full i j k)
  refine ⟨edge l,edge_in_graph l,?_⟩
  intro h
  have htrue : ((compactForest i ||| compactForest j) ||| compactForest k).getLsbD l.val = true := by
    simp only [BitVec.getLsbD_or, Bool.or_eq_true]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl ((compact_correct i l).mp h))
    · exact Or.inl (Or.inr ((compact_correct j l).mp h))
    · exact Or.inr ((compact_correct k l).mp h)
  rw [hl] at htrue
  contradiction

theorem no_three_two_factors :
    ¬ ∃ a b c d e f : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧ Rectangle e ∧ Rectangle f ∧
        zero = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f) := by
  classical
  rintro ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz⟩
  have h₁ : zero ⊆ a ∪ b := by
    intro p hp
    rw [hz] at hp
    exact hp.1.1
  have h₂ : zero ⊆ c ∪ d := by
    intro p hp
    rw [hz] at hp
    exact hp.1.2
  have h₃ : zero ⊆ e ∪ f := by
    intro p hp
    rw [hz] at hp
    exact hp.2
  obtain ⟨i,hi⟩ := complement_catalog ha hb h₁
  obtain ⟨j,hj⟩ := complement_catalog hc hd h₂
  obtain ⟨k,hk⟩ := complement_catalog he hf h₃
  obtain ⟨p,hg,hout⟩ := three_forests_do_not_cover i j k
  have hab : p ∈ a ∪ b := by
    by_contra hn
    exact hout (Or.inl (Or.inl (hi hn)))
  have hcd : p ∈ c ∪ d := by
    by_contra hn
    exact hout (Or.inl (Or.inr (hj hn)))
  have hef : p ∈ e ∪ f := by
    by_contra hn
    exact hout (Or.inr (hk hn))
  have hzero : p ∈ zero := by
    rw [hz]
    exact ⟨⟨hab,hcd⟩,hef⟩
  exact hzero hg

#print axioms no_three_by_two
#print axioms three_forests_do_not_cover
#print axioms no_three_two_factors
end QuadrangleFormulaExclusions
