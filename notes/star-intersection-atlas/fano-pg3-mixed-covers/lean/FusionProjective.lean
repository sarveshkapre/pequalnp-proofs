import FusionCanonical

namespace FusionCanonical

variable {R C T : Type*}

theorem exists_not_of_card_lt [Fintype T] [DecidableEq T]
    (p : T → Prop) [DecidablePred p] (s : Finset T)
    (h : Fintype.card {x // p x} < s.card) : ∃ x ∈ s, ¬ p x := by
  classical
  by_contra hn
  push Not at hn
  have hs : s ⊆ Finset.univ.filter p := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn x hx⟩
  have hc := Finset.card_le_card hs
  rw [← Fintype.card_subtype p] at hc
  omega

/- This uses only sparsity, not projective geometry or C4-freeness. -/
theorem split_of_sparse [Fintype R] [Fintype C]
    (G : R → C → Prop) [DecidableRel G] (d : ℕ)
    (sizeR : 2 * d + 2 ≤ Fintype.card R)
    (sizeC : 2 * d + 2 ≤ Fintype.card C)
    (degreeR : ∀ r, Fintype.card {c // G r c} ≤ d)
    (degreeC : ∀ c, Fintype.card {r // G r c} ≤ d) :
    ∃ A : Set R, ∃ B : Set C, SplitZeros G A B := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset R)) (n := d + 1) (by simpa using (show d+1 ≤ Fintype.card R by omega))
  obtain ⟨b, _, hb⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset C)) (n := d + 1) (by simpa using (show d+1 ≤ Fintype.card C by omega))
  have hac : d < aᶜ.card := by rw [Finset.card_compl, ha]; omega
  have hbc : d < bᶜ.card := by rw [Finset.card_compl, hb]; omega
  refine ⟨(a : Set R), (b : Set C), ?_⟩
  constructor
  · intro r
    obtain ⟨c,hc,hn⟩ := exists_not_of_card_lt (G r) b (by rw [hb]; exact Nat.lt_succ_of_le (degreeR r))
    exact ⟨c,hn,hc⟩
  · intro r
    obtain ⟨c,hc,hn⟩ := exists_not_of_card_lt (G r) bᶜ (lt_of_le_of_lt (degreeR r) hbc)
    exact ⟨c,hn,by simpa using hc⟩
  · intro c
    obtain ⟨r,hr,hn⟩ := exists_not_of_card_lt (fun r => G r c) a
      (by rw [ha]; exact Nat.lt_succ_of_le (degreeC c))
    exact ⟨r,hn,hr⟩
  · intro c
    obtain ⟨r,hr,hn⟩ := exists_not_of_card_lt (fun r => G r c) aᶜ
      (lt_of_le_of_lt (degreeC c) hac)
    exact ⟨r,hn,by simpa using hr⟩

theorem sparse_canonical_two [Fintype R] [Fintype C]
    (G : R → C → Prop) [DecidableRel G] (d : ℕ)
    (sizeR : 2 * d + 2 ≤ Fintype.card R)
    (sizeC : 2 * d + 2 ≤ Fintype.card C)
    (degreeR : ∀ r, Fintype.card {c // G r c} ≤ d)
    (degreeC : ∀ c, Fintype.card {r // G r c} ≤ d) : CanonicalCover G 2 := by
  obtain ⟨A,B,h⟩ := split_of_sparse G d sizeR sizeC degreeR degreeC
  exact canonical_two_of_split h

/- Stated directly in finite incidence data, matching the project's plane data.
   Unique joining lines are more than needed: existence suffices here. -/
theorem projective_canonical_exact_two
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 3 ≤ q) (hN : N = q ^ 2 + q + 1)
    (linesThrough : ∀ p, Fintype.card {l // I p l} = q + 1)
    (pointsOn : ∀ l, Fintype.card {p // I p l} = q + 1)
    (joining : ∀ p p', p ≠ p' → ∃ l, I p l ∧ I p' l) :
    CanonicalCover I 2 ∧ ¬ CanonicalCover I 1 := by
  have hsize : 2 * (q + 1) + 2 ≤ Fintype.card (Fin N) := by
    simp only [Fintype.card_fin]
    rw [hN]
    nlinarith
  obtain ⟨A,B,h⟩ := split_of_sparse I (q+1) hsize hsize
    (fun p => (linesThrough p).le) (fun l => (pointsOn l).le)
  have row_nonempty (p : Fin N) : ∃ l, I p l := by
    have hc : 0 < Fintype.card {l // I p l} := by rw [linesThrough p]; omega
    obtain ⟨l⟩ := Fintype.card_pos_iff.mp hc
    exact ⟨l.val,l.property⟩
  apply canonical_exact_two_of_split h
  · intro p p'
    by_cases he : p = p'
    · subst p'
      obtain ⟨l,hl⟩ := row_nonempty p
      exact ⟨l,hl,hl⟩
    · exact joining p p' he
  · have hpos : 0 < N := by rw [hN]; omega
    obtain ⟨l,hl⟩ := row_nonempty ⟨0,hpos⟩
    exact ⟨⟨0,hpos⟩,l,hl⟩

#print axioms sparse_canonical_two
#print axioms projective_canonical_exact_two

end FusionCanonical
