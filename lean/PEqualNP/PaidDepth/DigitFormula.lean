import Mathlib.Tactic

/-! A balanced intersection tree of equality tests on blocks of labels.
Each equality test is a free union of intersections of two one-sided inputs. -/
theorem PEqualNP.PaidDepth.DigitFormula :
    ∀ (r c b h : Nat) (A : Nat → Nat → Set (Fin r)) (B : Nat → Nat → Set (Fin c))
      (P : Nat → Nat → Set (Fin r × Fin c) → Prop),
    (∀ d (U : Set (Fin r)), P 0 d {x | x.1 ∈ U}) → (∀ d (V : Set (Fin c)), P 0 d {x | x.2 ∈ V}) →
    (∀ i j d U V, P i d U → P j d V → P (i+j) d (U ∪ V)) →
    (∀ i j d U V, P i d U → P j d V → P (i+j+1) (d+1) (U ∩ V)) →
    ∃ k, k+1 = (b+1)*2^h ∧ P k (h+1)
      {x | ∀ t < 2^h, ∃ z < b, x.1 ∈ A t z ∧ x.2 ∈ B t z} := by
  intro r c b h A B P row col join gate
  let digit (t n : Nat) : Set (Fin r × Fin c) :=
    {x | ∃ z < n, x.1 ∈ A t z ∧ x.2 ∈ B t z}
  have each (t n : Nat) : P n 1 (digit t n) := by
    induction n with
    | zero =>
      convert row 1 (∅ : Set (Fin r)) using 1
      ext x
      simp [digit]
    | succ n ih =>
      have single := gate 0 0 0 _ _ (row 0 (A t n)) (col 0 (B t n))
      have split : digit t (n+1) = digit t n ∪
          ({x | x.1 ∈ A t n} ∩ {x | x.2 ∈ B t n}) := by
        ext x
        change (∃ z < n+1, x.1 ∈ A t z ∧ x.2 ∈ B t z) ↔
          (∃ z < n, x.1 ∈ A t z ∧ x.2 ∈ B t z) ∨ (x.1 ∈ A t n ∧ x.2 ∈ B t n)
        constructor
        · rintro ⟨z,hz,hp⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hz) with lt|rfl
          · exact Or.inl ⟨z,lt,hp⟩
          · exact Or.inr hp
        · rintro (⟨z,hz,hp⟩|hp)
          · exact ⟨z,by omega,hp⟩
          · exact ⟨n,by omega,hp⟩
      rw [split]
      exact join _ _ 1 _ _ ih single
  let block (t n : Nat) : Set (Fin r × Fin c) :=
    {x | ∀ j < n, x ∈ digit (t+j) b}
  have build (u : Nat) : ∀ t, ∃ k, k+1 = (b+1)*2^u ∧ P k (u+1) (block t (2^u)) := by
    induction u with
    | zero =>
      intro t
      refine ⟨b,by simp,?_⟩
      have eq : block t (2^0) = digit t b := by
        ext x
        simp [block]
      rw [eq]
      exact each t b
    | succ u ih =>
      intro t
      obtain ⟨i,hi,pi⟩ := ih t
      obtain ⟨j,hj,pj⟩ := ih (t+2^u)
      refine ⟨i+j+1,?_,?_⟩
      · rw [pow_succ,← Nat.mul_assoc,Nat.mul_two]
        omega
      · have split : block t (2^(u+1)) = block t (2^u) ∩ block (t+2^u) (2^u) := by
          ext x
          simp only [block,Set.mem_ofPred_eq,Set.mem_inter_iff,pow_succ,Nat.mul_two]
          constructor
          · intro all
            refine ⟨fun v hv => all v (by omega),?_⟩
            intro v hv
            simpa [Nat.add_assoc] using all (2^u+v) (by omega)
          · rintro ⟨left,right⟩ v hv
            by_cases small : v < 2^u
            · exact left v small
            · have tail := right (v-2^u) (by omega)
              have back : t+2^u+(v-2^u) = t+v := by omega
              simpa only [back] using tail
        rw [split]
        exact gate _ _ _ _ _ pi pj
  simpa [block,digit] using build h 0
