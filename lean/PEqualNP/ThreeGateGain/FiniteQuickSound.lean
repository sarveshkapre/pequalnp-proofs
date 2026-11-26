import PEqualNP.ThreeGateGain.FiniteQuick
import PEqualNP.ThreeGateGain.GainFrameResidual

namespace GainFinite
open Finset GainFrameBridge

private theorem active_iff (h : Host) (i : WordType) :
    (activeMask h).testBit i.val = true ↔ rowMask h i ≠ 0 := by
  have checked : ∀ (h : Host) (i : WordType), (activeMask h).testBit i.val = true ↔ rowMask h i ≠ 0 := by
    decide +kernel
  exact checked h i

private def avail (h : Host) (b : Leaves) : Finset WordType :=
  (positions (activeMask h &&& ((2^27-1) ^^^ unionMask h b))).toFinset

private theorem amem (h : Host) (b : Leaves) (i : WordType) :
    i ∈ avail h b ↔ rowMask h i ≠ 0 ∧ (unionMask h b).testBit i.val = false := by
  simp only [avail,List.mem_toFinset,positions_mem,Nat.testBit_and,Nat.testBit_xor,
    Nat.testBit_two_pow_sub_one,i.isLt,decide_true,Bool.true_xor,Bool.and_eq_true,
    Bool.not_eq_true',active_iff]

private theorem rough_score (h : Host) (rl cl : Leaves) :
    (liveRows h rl cl).length + size27 ((liveRows h rl cl).foldr (· ||| ·) 0) ≤
      remaining h cl + remaining h rl := by
  have left : (indices h rl cl).toFinset ⊆ avail h cl := by
    intro i hi
    obtain ⟨h₁,h₂⟩ := List.mem_filter.mp (List.mem_toFinset.mp hi)
    obtain ⟨_,h₀⟩ := List.mem_filter.mp h₁
    apply (amem h cl i).mpr
    refine ⟨?_,by simpa only [Bool.not_eq_true'] using h₀⟩
    have nz : word h rl i ≠ 0 := bne_iff_ne.mp h₂
    intro zero
    exact nz (by simp [word,zero])
  have right : C h rl cl ⊆ avail h rl := by
    intro j hj
    obtain ⟨i,_,bit⟩ := (col_mem h rl cl j).mp hj
    obtain ⟨edge,free⟩ := (word_bit _ _ _ _).mp bit
    apply (amem h rl j).mpr
    refine ⟨witness_nonzero _ i ?_,?_⟩
    · exact (row_bit _ _ _).trans ((edge_symm h j i).trans edge)
    · apply Bool.eq_false_iff.mpr; intro b
      obtain ⟨k,hk,ek⟩ := (union_bit h rl j).mp b
      simp [free k hk] at ek
  have cleft := card_le_card left
  have cright := card_le_card right
  rw [List.toFinset_card_of_nodup (indices_nodup h rl cl)] at cleft
  rw [show (avail h cl).card = remaining h cl from positions_count _] at cleft
  rw [show (avail h rl).card = remaining h rl from positions_count _] at cright
  rw [show (C h rl cl).card = size27 ((liveRows h rl cl).foldr (· ||| ·) 0) from positions_count _] at cright
  have length : (liveRows h rl cl).length = (indices h rl cl).length := by rw [live_map,List.length_map]
  omega

theorem quickFrame_sound (h : Host) (rl cl : Leaves) :
    quickFrame h rl cl = true → testFrame h rl cl = true := by
  intro yes
  simp only [quickFrame,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at yes
  obtain ⟨ht,cheap|done⟩ := yes
  · have compress := rough_score h rl cl
    have detail := Nat.min_le_right ((liveRows h rl cl).map size27).sum
      ((liveRows h rl cl).length + size27 ((liveRows h rl cl).foldr (· ||| ·) 0))
    simp only [testFrame,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,GainFinite.residual]
    refine ⟨ht,Or.inl ?_⟩
    have bound : 17*(rl.length+cl.length) + 3*((liveRows h rl cl).length +
        size27 ((liveRows h rl cl).foldr (· ||| ·) 0)) ≤ 158 := by
      rcases cheap with rough|mid
      · exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 3 compress) _) rough
      · exact mid
    exact decide_eq_true (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 3 detail) _) bound)
  · exact done

theorem visit_imp {α : Type*} (ok f g : List α → Bool)
    (imp : ∀ xs, f xs = true → g xs = true) (s xs : List α) :
    visit ok f s xs = true → visit ok g s xs = true := by
  induction xs generalizing s with
  | nil => exact imp s
  | cons i is ih =>
    simp only [visit,Bool.and_eq_true,Bool.or_eq_true]
    rintro ⟨base,skip|inc⟩
    · exact ⟨ih _ base,Or.inl skip⟩
    · exact ⟨ih _ base,Or.inr (ih _ inc)⟩

theorem quickCols_sound (h : Host) (rl : Leaves) : quickCols h rl = true → checkCols h rl = true :=
  visit_imp _ _ _ (quickFrame_sound h rl) _ _

theorem quickHost_sound (h : Host) : quickHost h = true → checkHost h = true :=
  visit_imp _ _ _ (quickCols_sound h) _ _

end GainFinite
