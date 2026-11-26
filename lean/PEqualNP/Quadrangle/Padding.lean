import PEqualNP.Quadrangle.Handoff

namespace QuadrangleHandoff

/-- Prepend an empty intersection; shift every original gate and every
reference by one. The output stays the same. -/
private theorem shiftRefs {n : Nat} (I : Fin n → Finset Cell)
    (s : Finset (Fin n)) (p : Cell) :
    (∃ r ∈ s.image Fin.succ, p ∈ (Fin.cases ∅ I r : Finset Cell)) ↔
      ∃ r ∈ s, p ∈ I r := by
  constructor
  · rintro ⟨r, hr, hp⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨u, hu, hp⟩
  · rintro ⟨u, hu, hp⟩
    exact ⟨u.succ, Finset.mem_image_of_mem _ hu, hp⟩

theorem pad_one {k : Nat} {G : Finset Cell} (h : Represents k G) : Represents (k+1) G := by
  obtain ⟨I,A,B,S,earlier,gate,output,correct⟩ := h
  refine ⟨Fin.cases ∅ I, Fin.cases (fun _ => ∅) A, Fin.cases (fun _ => ∅) B,
    Fin.cases (fun _ => ∅) (fun t e => (S t e).image Fin.succ), ?_, ?_, ?_, ?_⟩
  · intro t
    refine Fin.cases ?_ (fun t => ?_) t
    · simp
    · intro e r hr
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
      exact Fin.succ_lt_succ_iff.mpr (earlier t e u hu)
  · intro t
    refine Fin.cases ?_ (fun t => ?_) t
    · intro _ p
      simp
    · intro ht p
      have hne : t ≠ Fin.last k := fun h => ht (by rw [h]; rfl)
      simp only [Fin.cases_succ, shiftRefs]
      exact gate t hne p
  · intro p
    change p ∈ I (Fin.last k) ↔ _ ∨ _ ∨ ∃ r ∈ (S (Fin.last k) 0).image Fin.succ,
      p ∈ (Fin.cases ∅ I r : Finset Cell)
    rw [shiftRefs]
    exact output p
  · exact correct

theorem excludes_smaller {G : Finset Cell} (h : ¬Represents 3 G) :
    ∀ k, k < 4 → ¬Represents k G := by
  intro k hk rep
  have hle : k ≤ 3 := by omega
  apply h
  exact Nat.le_induction rep (fun _ _ r => pad_one r) 3 hle

end QuadrangleHandoff
