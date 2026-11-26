import GeneralThree

namespace MatchingPorts

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

/-- At most one disjoint matching edge can use each member of a set of centers. -/
theorem count_untouched {n : ℕ} (S Z : Finset (Fin n)) (f : S → Fin n)
    (inj : Function.Injective f) (outside : ∀ v, f v ∉ S) :
    S.card ≤ Z.card + (Finset.univ.filter fun i : S => i.val ∉ Z ∧ f i ∉ Z).card := by
  classical
  let hit := Finset.univ.filter fun i : S => i.val ∈ Z ∨ f i ∈ Z
  let pick (i : S) : Fin n := if i.val ∈ Z then i.val else f i
  have unique : Function.Injective pick := by
    intro i j eq
    dsimp [pick] at eq
    split_ifs at eq with a b b
    · exact Subtype.ext eq
    · exact (outside j (eq ▸ i.2)).elim
    · exact (outside i (eq.symm ▸ j.2)).elim
    · exact inj eq
  have sub : hit.image pick ⊆ Z := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [pick]
    split_ifs with yes
    · exact yes
    · exact (Finset.mem_filter.mp hi).2.resolve_left yes
  have upper := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ unique] at upper
  have parts := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
    (p := fun i : S => i.val ∈ Z ∨ f i ∈ Z)
  simp only [not_or, Finset.card_univ, Fintype.card_coe] at parts
  change (Finset.univ.filter fun i : S => i.val ∈ Z ∨ f i ∈ Z).card ≤ Z.card at upper
  omega

/-- Every top that fires on a matched pair avoiding its center receives a
live exceptional OR with exactly that center as its raw input support. -/
theorem active_source {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (u v : Fin n) (a : tops G C) (b : Fin 2) (z : Fin n)
    (one : side (n := n) C a b = {z}) (free : z ≠ u ∧ z ≠ v)
    (fires : gateVal n C a (pairInput u v) = true) :
    ∃ h ∈ orN G C \ lam G C, orIn n C (n+h) = {z} ∧
      OrReaches n C (opnd C a b) h ∧ gateVal n C h (pairInput u v) = true := by
  classical
  obtain ⟨len,hand,_⟩ := topData a.2
  have on := (andValOperands ao len hand _).mp fires b
  have bd := opndBound ao len b
  have ne : (orIn n C (opnd C a b)).Nonempty := by change (side C a b).Nonempty; rw [one]; simp
  rcases (nonemptyPortValue (G := G) ao _ _ (by omega) ne).mp on with ⟨x,mem,yes⟩ | ⟨h,m,yes⟩
  · change x ∈ side (n := n) C a b at mem
    rw [one,Finset.mem_singleton] at mem
    subst x
    rcases (pairInput_true _ _ _).mp yes with eq|eq
    · exact (free.1 eq).elim
    · exact (free.2 eq).elim
  · change h ∈ (orN G C \ lam G C).filter _ at m
    obtain ⟨hm,raw,path⟩ := Finset.mem_filter.mp m
    have sub : orIn n C (n+h) ⊆ {z} := by
      rw [← one]
      exact fun x hx => reach_mem_orIn x ((orReaches_reach h _ path).1.trans (mem_orIn_reach x hx))
    exact ⟨h,hm,Finset.eq_of_subset_of_card_le sub (by
      simp only [Finset.card_singleton]; exact Finset.card_pos.mpr raw),path,yes⟩

/-- In a failure there are at least two disjoint matched residual edges outside
every chosen ordinary center. On each, all firing tops must use a live
exceptional OR with singleton raw support. -/
theorem two_promoted {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (failure : ¬ GeneralThree.wireBound G C S)
    (b : tops G C → Fin 2) (z : tops G C → Fin n)
    (one : ∀ a : tops G C, side (n := n) C a (b a) = {z a})
    (centers : ∀ u v, (G.deleteEdges ↑(Ustar G C)).Adj u v → ∃ a, u = z a ∨ v = z a) :
    ∃ T : Finset S, 2 ≤ T.card ∧ ∀ i ∈ T,
      s(i.val, f i) ∈ Ustar G C ∧ (∀ a, z a ≠ i.val ∧ z a ≠ f i) ∧
      (∀ a : tops G C, gateVal n C a (pairInput i.val (f i)) = true →
        ∃ h ∈ orN G C \ lam G C, orIn n C (n+h) = {z a} ∧
          OrReaches n C (opnd C a (b a)) h ∧ gateVal n C h (pairInput i.val (f i)) = true) := by
  classical
  let Z := Finset.univ.image z
  let T := Finset.univ.filter fun i : S => i.val ∉ Z ∧ f i ∉ Z
  have tight := (GeneralThree.tight_if_failed G C four edges least top three S f inj partners failure).1
  have bound : Z.card ≤ (tops G C).card :=
    Finset.card_image_le.trans_eq (by simp)
  have many := count_untouched S Z f inj (fun v => (partners v).1)
  change S.card ≤ Z.card + T.card at many
  refine ⟨T,by omega,?_⟩
  intro i hi
  have avoids : i.val ∉ Z ∧ f i ∉ Z := (Finset.mem_filter.mp hi).2
  have zmem (a : tops G C) : z a ∈ Z := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have free (a : tops G C) : z a ≠ i.val ∧ z a ≠ f i :=
    ⟨fun eq => avoids.1 (eq ▸ zmem a),fun eq => avoids.2 (eq ▸ zmem a)⟩
  refine ⟨?_,free,fun a fired => active_source least.1 _ _ a _ _ (one a) (free a) fired⟩
  by_contra miss
  obtain ⟨a,eq|eq⟩ := centers _ _ (SimpleGraph.deleteEdges_adj.mpr ⟨(partners i).2,miss⟩)
  · exact (free a).1 eq.symm
  · exact (free a).2 eq.symm

#print axioms two_promoted
end MatchingPorts
