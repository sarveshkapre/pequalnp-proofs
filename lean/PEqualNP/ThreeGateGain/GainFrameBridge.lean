import PEqualNP.ThreeGateGain.FiniteFrame
import PEqualNP.ThreeGateGain.GainSelection

namespace GainFrameBridge
open Finset GainFinite

@[simp] theorem row_bit (h : Host) (i j : WordType) :
    (rowMask h i).testBit j.val = hostEdge h i j := by
  simp only [rowMask,hostEdge,Nat.testBit_mod_two_pow,j.isLt,decide_true,Bool.true_and,Nat.testBit_shiftRight]

@[simp] theorem union_bit (h : Host) (xs : List WordType) (j : WordType) :
    (unionMask h xs).testBit j.val = true ↔ ∃ i ∈ xs, hostEdge h i j = true := by
  induction xs with
  | nil => simp [unionMask]
  | cons i is ih =>
    simp only [unionMask,List.foldr_cons,Nat.testBit_or,Bool.or_eq_true,row_bit] at *
    rw [ih]
    simp

@[simp] theorem private_bit (h : Host) (xs : List WordType) (i j : WordType) :
    (privateMask h xs i).testBit j.val = true ↔
    hostEdge h i j = true ∧ ∀ k ∈ xs, hostEdge h k j = true → k = i := by
  simp only [privateMask,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,
    j.isLt, decide_true, Bool.true_xor, Bool.and_eq_true, Bool.not_eq_true',row_bit]
  simp only [Bool.eq_false_iff, ne_eq, union_bit,List.mem_filter,bne_iff_ne]
  grind

@[simp] theorem positions_mem (m : Nat) (i : WordType) :
    i ∈ positions m ↔ m.testBit i.val = true := by simp [positions]

theorem positions_nodup (m : Nat) : (positions m).Nodup :=
  (List.nodup_finRange _).filter _

theorem positions_count (m : Nat) : (positions m).toFinset.card = size27 m :=
  List.toFinset_card_of_nodup (positions_nodup m)

theorem witness_nonzero (m : Nat) (i : WordType) (h : m.testBit i.val = true) : m ≠ 0 := by
  rintro rfl; simp at h

theorem edge_symm (h : Host) (i j : WordType) : hostEdge h i j = hostEdge h j i := by
  have all : ∀ (g : Host) (x y : WordType), hostEdge g x y = hostEdge g y x := by
    decide +kernel
  exact all h i j

noncomputable def fromSet (s : Finset WordType) := selected (fun i => decide (i ∈ s))

@[simp] theorem fromSet_mem (s : Finset WordType) (i : WordType) : i ∈ fromSet s ↔ i ∈ s := by
  simp [fromSet,selected,allTypes]

theorem fromSet_nodup (s : Finset WordType) : (fromSet s).Nodup :=
  List.nodup_reverse.mpr ((List.nodup_finRange _).filter _)

@[simp] theorem fromSet_toFinset (s : Finset WordType) : (fromSet s).toFinset = s := by
  ext i; simp

@[simp] theorem fromSet_length (s : Finset WordType) : (fromSet s).length = s.card := by
  simpa only [fromSet_toFinset] using (List.toFinset_card_of_nodup (fromSet_nodup s)).symm

end GainFrameBridge
