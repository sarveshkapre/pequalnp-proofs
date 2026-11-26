import PEqualNP.ThreeGateGain.FanoFiveUpper
import PEqualNP.ThreeGateGain.FiniteValue
import Mathlib.Tactic

namespace GainCircuit
open FanoFiveUpper GainFinite

private def used (xs : List (Fin n)) (i : Fin n) := decide (i ∈ xs)

private theorem read₀ (xs : List (Fin 0)) (f : Fin 0 → Bool) : xs.any f = false := by
  cases xs with
  | nil => rfl
  | cons hd _ => exact hd.elim0

private theorem read₁ (xs : List (Fin 1)) (f : Fin 1 → Bool) :
    xs.any f = (used xs 0 && f 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, used, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,hf⟩; fin_cases i; exact ⟨hi,hf⟩
  · rintro ⟨hi,hf⟩; exact ⟨0,hi,hf⟩

private theorem read₂ (xs : List (Fin 2)) (f : Fin 2 → Bool) :
    xs.any f = ((used xs 0 && f 0) || (used xs 1 && f 1)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, used, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,hf⟩; fin_cases i <;> tauto
  · rintro (⟨hi,hf⟩|⟨hi,hf⟩)
    · exact ⟨0,hi,hf⟩
    · exact ⟨1,hi,hf⟩

private theorem read₃ (xs : List (Fin 3)) (f : Fin 3 → Bool) :
    xs.any f = ((used xs 0 && f 0) || (used xs 1 && f 1) || (used xs 2 && f 2)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, used, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,hf⟩; fin_cases i <;> tauto
  · rintro ((⟨hi,hf⟩|⟨hi,hf⟩)|⟨hi,hf⟩)
    · exact ⟨0,hi,hf⟩
    · exact ⟨1,hi,hf⟩
    · exact ⟨2,hi,hf⟩

/-- Every ordinary paid circuit, including its free output arm, has raw words
and a wiring independent of the evaluated inputs. -/
theorem circuit_words {R C : Nat} (program : Circuit 3) (out : Arm 3) :
    ∃ (w : BitVec 9) (r : Fin R → BitVec 6) (c : Fin C → BitVec 6),
      ∀ p l, out.eval p l (program.eval p l) =
        (out.pointMask.testBit p.val || out.lineMask.testBit l.val || threeValue w (r p ||| c l)) := by
  cases program
  rename_i prev a₂ b₂
  cases prev
  rename_i prev a₁ b₁
  cases prev
  rename_i prev a₀ b₀
  cases prev
  let w : BitVec 9 := BitVec.ofBoolListLE
    [used a₁.earlier 0,used b₁.earlier 0,used a₂.earlier 0,used a₂.earlier 1,
     used b₂.earlier 0,used b₂.earlier 1,used out.earlier 0,used out.earlier 1,used out.earlier 2]
  let r (p : Fin R) : BitVec 6 := BitVec.ofBoolListLE
    [a₀.pointMask.testBit p.val,b₀.pointMask.testBit p.val,a₁.pointMask.testBit p.val,
     b₁.pointMask.testBit p.val,a₂.pointMask.testBit p.val,b₂.pointMask.testBit p.val]
  let c (l : Fin C) : BitVec 6 := BitVec.ofBoolListLE
    [a₀.lineMask.testBit l.val,b₀.lineMask.testBit l.val,a₁.lineMask.testBit l.val,
     b₁.lineMask.testBit l.val,a₂.lineMask.testBit l.val,b₂.lineMask.testBit l.val]
  refine ⟨w,r,c,?_⟩
  intro p l
  let raw {n : Nat} (a : Arm n) := a.pointMask.testBit p.val || a.lineMask.testBit l.val
  let g₀ := raw a₀ && raw b₀
  let g₁ := (raw a₁ || (used a₁.earlier 0 && g₀)) &&
    (raw b₁ || (used b₁.earlier 0 && g₀))
  let g₂ := (raw a₂ || (used a₂.earlier 0 && g₀) || (used a₂.earlier 1 && g₁)) &&
    (raw b₂ || (used b₂.earlier 0 && g₀) || (used b₂.earlier 1 && g₁))
  let c₁ := Circuit.empty.gate a₀ b₀
  let c₂ := c₁.gate a₁ b₁
  let c₃ := c₂.gate a₂ b₂
  have e₀ : c₁.eval p l 0 = g₀ := by
    change ((raw a₀ || a₀.earlier.any _) && (raw b₀ || b₀.earlier.any _)) = _
    simp [read₀,g₀]
  have e₁ : c₂.eval p l 1 = g₁ := by
    change ((raw a₁ || a₁.earlier.any (c₁.eval p l)) &&
      (raw b₁ || b₁.earlier.any (c₁.eval p l))) = _
    rw [read₁,read₁,e₀]
  have e₀' : c₂.eval p l 0 = g₀ := e₀
  have e₂ : c₃.eval p l 2 = g₂ := by
    change ((raw a₂ || a₂.earlier.any (c₂.eval p l)) &&
      (raw b₂ || b₂.earlier.any (c₂.eval p l))) = _
    rw [read₂,read₂,e₀',e₁]
    simp only [g₂,Bool.or_assoc]
  have e₀'' : c₃.eval p l 0 = g₀ := e₀
  have e₁' : c₃.eval p l 1 = g₁ := e₁
  change (raw out || out.earlier.any (c₃.eval p l)) = _
  rw [read₃,e₀'',e₁',e₂]
  simp only [threeValue,w,r,c,BitVec.getLsbD_or,BitVec.getLsbD_ofBoolListLE]
  rfl

/-- Unused paid gates can be appended, and old gates remain available. -/
theorem pad {R C n m : Nat} (h : n ≤ m) (program : Circuit n) (out : Arm n) :
    ∃ (next : Circuit m) (o : Arm m), ∀ (p : Fin R) (l : Fin C),
      out.eval p l (program.eval p l) = o.eval p l (next.eval p l) := by
  induction h with
  | refl => exact ⟨program,out,fun _ _ => rfl⟩
  | step _ ih =>
    obtain ⟨c,o,ho⟩ := ih
    refine ⟨c.gate ⟨0,0,[]⟩ ⟨0,0,[]⟩,
      ⟨o.pointMask,o.lineMask,o.earlier.map Fin.castSucc⟩,?_⟩
    intro p l
    rw [ho]
    simp [Arm.eval,Circuit.eval,List.any_map,Function.comp_def]

#print axioms circuit_words
#print axioms pad
end GainCircuit
