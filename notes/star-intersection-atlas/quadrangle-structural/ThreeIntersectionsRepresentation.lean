import ThreeIntersections
import QuadrangleHandoff
import ThreeIntersectionsQuadrangle

/-! Connect the five-shape theorem to pjscruggs's unchanged `Represents`
definition, including free unions and reuse of all earlier paid gates. -/
namespace ThreeIntersectionsRepresentation
open Set TwoIntersections ThreeIntersections QuadrangleHandoff

private def clause {τ : Type*} (I : τ → Finset Cell)
    (A B : Finset (Fin 6)) (S : Finset τ) : Set Cell :=
  {p | ¬ (p.1 ∈ A ∨ p.2 ∈ B ∨ ∃ r ∈ S, p ∈ I r)}

private theorem free_clause {τ : Type*} [DecidableEq τ] {F : Family Cell}
    (I : τ → Finset Cell) (A B : Finset (Fin 6)) (S : Finset τ)
    (hbase : F {p | p.1 ∉ A ∧ p.2 ∉ B})
    (hprev : ∀ r ∈ S, Free F {p | p ∉ I r}) : Free F (clause I A B S) := by
  induction S using Finset.induction_on with
  | empty =>
    have h : clause I A B ∅ = {p | p.1 ∉ A ∧ p.2 ∉ B} := by
      ext p; simp [clause]
    rw [h]
    exact Free.input hbase
  | @insert r S hr ih =>
    have h : clause I A B (insert r S) = clause I A B S ∩ {p | p ∉ I r} := by
      ext p; simp [clause]; tauto
    rw [h]
    exact Free.meet (ih (fun t ht => hprev t (Finset.mem_insert_of_mem ht)))
      (hprev r (Finset.mem_insert_self r S))

private theorem rectangle_base (A B : Finset (Fin 6)) :
    Rectangle {p : Cell | p.1 ∉ A ∧ p.2 ∉ B} :=
  ⟨{i | i ∉ A}, {j | j ∉ B}, rfl⟩

/-- Every original three-intersection representation yields a three-union
zero-set circuit. No input selection or earlier-gate reuse is discarded. -/
theorem represents_three {G : Finset Cell} (hG : Represents 3 G) :
    Three Rectangle {p | p ∉ G} := by
  rcases hG with ⟨I, A, B, S, horder, hpaid, hout, hG⟩
  let Z (t : Fin 4) : Set Cell := {p | p ∉ I t}
  let C (t : Fin 4) (e : Fin 2) : Set Cell := clause I (A t e) (B t e) (S t e)
  have paid (t : Fin 4) (ht : t ≠ Fin.last 3) : Z t = C t 0 ∪ C t 1 := by
    ext p
    change (¬ p ∈ I t) ↔ _
    rw [hpaid t ht p]
    simp only [C, clause, Fin.forall_fin_two, Set.mem_union, Set.mem_ofPred_eq]
    exact not_and_or
  have final : Z (Fin.last 3) = C (Fin.last 3) 0 := by
    ext p
    change (¬ p ∈ I (Fin.last 3)) ↔ _
    rw [hout p]
    rfl
  have c0 (e : Fin 2) : Free Rectangle (C 0 e) := by
    apply free_clause I (A 0 e) (B 0 e) (S 0 e) (rectangle_base _ _)
    intro r hr
    have h := horder 0 e r hr
    exact (Fin.not_lt_zero r h).elim
  have c1 (e : Fin 2) : Free (With Rectangle (Z 0)) (C 1 e) := by
    apply free_clause I (A 1 e) (B 1 e) (S 1 e) (Or.inl (rectangle_base _ _))
    intro r hr
    have h := horder 1 e r hr
    have er : r = 0 := by apply Fin.ext; change r.val = 0; change r.val < 1 at h; omega
    subst r
    exact Free.input (Or.inr rfl)
  have c2 (e : Fin 2) : Free (With (With Rectangle (Z 0)) (Z 1)) (C 2 e) := by
    apply free_clause I (A 2 e) (B 2 e) (S 2 e) (Or.inl (Or.inl (rectangle_base _ _)))
    intro r hr
    have h := horder 2 e r hr
    have er : r = 0 ∨ r = 1 := by
      change r.val < 2 at h
      have : r.val = 0 ∨ r.val = 1 := by omega
      rcases this with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases er with rfl | rfl
    · exact Free.input (Or.inl (Or.inr rfl))
    · exact Free.input (Or.inr rfl)
  have c3 : Free (With (With (With Rectangle (Z 0)) (Z 1)) (Z 2))
      (C (Fin.last 3) 0) := by
    apply free_clause I (A (Fin.last 3) 0) (B (Fin.last 3) 0) (S (Fin.last 3) 0)
      (Or.inl (Or.inl (Or.inl (rectangle_base _ _))))
    intro r hr
    have h := horder (Fin.last 3) 0 r hr
    have er : r = 0 ∨ r = 1 ∨ r = 2 := by
      change r.val < 3 at h
      have : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
      rcases this with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases er with rfl | rfl | rfl
    · exact Free.input (Or.inl (Or.inl (Or.inr rfl)))
    · exact Free.input (Or.inl (Or.inr rfl))
    · exact Free.input (Or.inr rfl)
  have hz : Three Rectangle (Z (Fin.last 3)) := by
    refine ⟨C 0 0, C 0 1, c0 0, c0 1, ?_⟩
    rw [← paid 0 (by decide)]
    refine ⟨C 1 0, C 1 1, c1 0, c1 1, ?_⟩
    rw [← paid 1 (by decide)]
    refine ⟨C 2 0, C 2 1, c2 0, c2 1, ?_⟩
    rw [← paid 2 (by decide), final]
    exact c3
  simpa only [Z, hG] using hz

/-- The normal-form reduction on exactly the contributor's graph model. -/
theorem represents_three_normal {G : Finset Cell} (hG : Represents 3 G) :
    ThreeIntersections.Normal Rectangle {p | p ∉ G} :=
  (ThreeIntersections.rectangle_normal_iff _).mp (represents_three hG)

private def rowEmbedding (i : Fin 5) : Fin 6 := ⟨i.val, by omega⟩

/-- Deleting the duplicated sixth row yields precisely the original 5×6
zero-cell matrix, with no identification or alteration of selected gates. -/
theorem quadrangle_three_normal (hG : Represents 3 QuadrangleHandoff.graph) :
    ThreeIntersections.Normal Rectangle ThreeIntersectionsQuadrangle.zero := by
  have hz := ThreeIntersections.rectangle_normal_preimage rowEmbedding id
    (represents_three_normal hG)
  have hzero : (fun p : Fin 5 × Fin 6 => (rowEmbedding p.1, p.2)) ⁻¹'
      {p | p ∉ QuadrangleHandoff.graph} = ThreeIntersectionsQuadrangle.zero := by
    have hcells : ∀ p : Fin 5 × Fin 6,
        (rowEmbedding p.1, p.2) ∉ QuadrangleHandoff.graph ↔
          p ∈ ThreeIntersectionsQuadrangle.zero := by
      unfold rowEmbedding QuadrangleHandoff.graph QuadrangleHandoff.mask
        ThreeIntersectionsQuadrangle.zero ThreeIntersectionsQuadrangle.graph
        ThreeIntersectionsQuadrangle.mask
      decide +kernel
    ext p
    exact hcells p
  change ThreeIntersections.Normal Rectangle
    ((fun p : Fin 5 × Fin 6 => (rowEmbedding p.1, p.2)) ⁻¹'
      {p | p ∉ QuadrangleHandoff.graph}) at hz
  rwa [hzero] at hz

#print axioms represents_three
#print axioms represents_three_normal
#print axioms quadrangle_three_normal
end ThreeIntersectionsRepresentation
