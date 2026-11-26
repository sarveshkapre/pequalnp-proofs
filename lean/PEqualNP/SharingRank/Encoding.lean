import PEqualNP.SharingRank.FamilyRank
import PEqualNP.SharingRank.Witness

namespace SharingRank.Family
private def digit : Bool → Bool → Four
  | false,false => 0
  | true,false => 1
  | false,true => 2
  | true,true => 3

@[simp] private theorem first_digit (a b c d : Bool) :
    firstBit (digit a b) (digit c d) = (a && c) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] private theorem other_digit (a b c d : Bool) :
    otherBit (digit a b) (digit c d) = (b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private def tailWord : (t : Nat) → Witness.Tail t → Words t
  | 0, _ => ()
  | n+1, f => (digit (f 0).1 (f 0).2,tailWord n (fun i => f i.succ))

private theorem tail_test (test : Four → Four → Bool) (t : Nat) (x y : Witness.Tail t) :
    allPairs test t (tailWord t x) (tailWord t y) = true ↔
      ∀ i, test (digit (x i).1 (x i).2) (digit (y i).1 (y i).2) = true := by
  induction t with
  | zero => simp [allPairs,tailWord]
  | succ n ih =>
    rw [Fin.forall_fin_succ]
    simp only [tailWord,allPairs,Bool.and_eq_true,ih]

def encode {t : Nat} (x : Witness.Word t) : Four × Words (t+2) :=
  (digit (x.1.getLsbD 0) (x.1.getLsbD 1),
    digit (x.1.getLsbD 2) (x.1.getLsbD 3),
    digit (x.1.getLsbD 4) (x.1.getLsbD 5),tailWord t x.2)

theorem encode_cell {t : Nat} (x y : Witness.Word t) :
    cell (t+2) (encode x) (encode y) = true ↔ Witness.zero x y := by
  let key := Witness.common (x.1 &&& y.1)
  by_cases h : key = true
  · have eq : someBit (encode x).1 (encode y).1 = true := by
      simpa [encode,someBit,key,Witness.common,BitVec.getLsbD_and] using h
    rw [cell,eq,Bool.true_and]
    simp only [encode,allPairs,Bool.or_eq_true,Bool.and_eq_true]
    simp only [tail_test,someBit,first_digit,other_digit,Bool.or_eq_true,Bool.and_eq_true]
    simp only [Witness.zero,Witness.core,show Witness.common (x.1 &&& y.1) = true from h,
      Bool.and_true,BitVec.getLsbD_and,Bool.or_eq_true,Bool.and_eq_true,and_true]
    constructor
    · rintro (⟨h2,h4,tail⟩|⟨h2,h4,tail⟩)
      · exact ⟨⟨Or.inl h2,Or.inl h4⟩,fun i => Or.inl (tail i)⟩
      · exact ⟨⟨h2,h4⟩,tail⟩
    · rintro ⟨⟨h2,h4⟩,tail⟩
      exact Or.inr ⟨h2,h4,tail⟩
  · have hf : key = false := Bool.eq_false_iff.mpr h
    have eq : someBit (encode x).1 (encode y).1 = false := by
      simpa [encode,someBit,key,Witness.common,BitVec.getLsbD_and] using hf
    rw [cell,eq,Bool.false_and,Bool.or_false]
    simp [encode,allPairs,tail_test,Witness.zero,Witness.core,
      show Witness.common (x.1 &&& y.1) = false from hf,BitVec.getLsbD_and,and_assoc]
end SharingRank.Family
