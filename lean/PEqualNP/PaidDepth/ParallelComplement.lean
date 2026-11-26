import PEqualNP.PaidDepth.DigitFormula

/-! Complement a single parallel layer with a balanced formula.
One block label chooses a rejecting operand for each intersection in the block. -/
theorem PEqualNP.PaidDepth.ParallelComplement :
    ∀ (r c g h : Nat) (A : Nat → Fin g → Bool → Set (Fin r))
      (B : Nat → Fin g → Bool → Set (Fin c)) (row : Set (Fin r)) (col : Set (Fin c))
      (P : Nat → Nat → Set (Fin r × Fin c) → Prop),
    (∀ d (U : Set (Fin r)), P 0 d {x | x.1 ∈ U}) →
    (∀ d (V : Set (Fin c)), P 0 d {x | x.2 ∈ V}) →
    (∀ i j d U V, P i d U → P j d V → P (i+j) d (U ∪ V)) →
    (∀ i j d U V, P i d U → P j d V → P (i+j+1) (d+1) (U ∩ V)) →
    ∃ k, k+1 = (2^g+1)*2^h ∧ P k (h+1)
      {x | ¬ (x.1 ∈ row ∨ x.2 ∈ col ∨ ∃ t < 2^h, ∃ i : Fin g,
        ∀ e : Bool, x.1 ∈ A t i e ∨ x.2 ∈ B t i e)} := by
  classical
  intro r c g h A B row col P rawRow rawCol join gate
  let code : (Fin g → Bool) ≃ Fin (2^g) := Fintype.equivFinOfCardEq (by simp)
  let decode (z : Nat) : Fin g → Bool :=
    if hz : z < 2^g then code.symm ⟨z,hz⟩ else fun _ => false
  let left (t z : Nat) : Set (Fin r) := {x | x ∉ row ∧ ∀ i, x ∉ A t i (decode z i)}
  let right (t z : Nat) : Set (Fin c) := {y | y ∉ col ∧ ∀ i, y ∉ B t i (decode z i)}
  obtain ⟨k,hk,proof⟩ := PEqualNP.PaidDepth.DigitFormula r c (2^g) h left right P
    rawRow rawCol join gate
  refine ⟨k,hk,?_⟩
  convert proof using 2
  ext x
  constructor
  · intro no t ht
    have rejected (i : Fin g) : ∃ e, x.1 ∉ A t i e ∧ x.2 ∉ B t i e := by
      by_contra! all
      exact no (Or.inr (Or.inr ⟨t,ht,i,fun e => by
        by_cases mem : x.1 ∈ A t i e
        · exact Or.inl mem
        · exact Or.inr (all e mem)⟩))
    choose chooseArm misses using rejected
    let v := code chooseArm
    have back : decode v.val = chooseArm := by
      simp [decode,v]
    refine ⟨v.val,v.isLt,⟨fun hr => no (Or.inl hr),?_⟩,⟨fun hc => no (Or.inr (Or.inl hc)),?_⟩⟩
    · intro i
      rw [back]
      exact (misses i).1
    · intro i
      rw [back]
      exact (misses i).2
  · intro covered bad
    obtain ⟨z,_,lr,rc⟩ := covered 0 (by positivity)
    rcases bad with hr|hc|⟨t,ht,i,both⟩
    · exact lr.1 hr
    · exact rc.1 hc
    · obtain ⟨v,_,L,R⟩ := covered t ht
      exact (both (decode v i)).elim (L.2 i) (R.2 i)
