import PEqualNP.ThreeGateGain.GainCircuit
import PEqualNP.ThreeGateGain.GainAttainment

namespace GainRealize
open FanoFiveUpper GainFinite GainGeometry TriangleOptimality Finset Configuration
open scoped Classical

private def mask {n : Nat} (f : Fin n → Bool) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn f)).toNat

private theorem mask_bit {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (mask f).testBit i.val = f i := by
  change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = _
  rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

private def choose {n : Nat} (b : Bool) (i : Fin n) := if b then [i] else []

private theorem choose_any {n : Nat} (b : Bool) (i : Fin n) (old : Fin n → Bool) :
    (choose b i).any old = (b && old i) := by cases b <;> simp [choose]

/-- Conversely, any assignment of words describes a genuine sequence of three
paid intersections. This includes arbitrary raw stars in the output union. -/
theorem program {R C : Nat} (w : BitVec 9) (r : Fin R → BitVec 6)
    (c : Fin C → BitVec 6) (rawP : Fin R → Bool) (rawL : Fin C → Bool) :
    ∃ (s : Circuit 3) (o : Arm 3), ∀ p l, o.eval p l (s.eval p l) =
      (rawP p || rawL l || threeValue w (r p ||| c l)) := by
  let arm {n : Nat} (i : Nat) (earlier : List (Fin n)) : Arm n :=
    ⟨mask (fun p => (r p).getLsbD i), mask (fun l => (c l).getLsbD i), earlier⟩
  let s₁ := Circuit.empty.gate (arm 0 []) (arm 1 [])
  let s₂ := s₁.gate (arm 2 (choose (w.getLsbD 0) 0)) (arm 3 (choose (w.getLsbD 1) 0))
  let s₃ := s₂.gate (arm 4 (choose (w.getLsbD 2) 0 ++ choose (w.getLsbD 3) 1))
                    (arm 5 (choose (w.getLsbD 4) 0 ++ choose (w.getLsbD 5) 1))
  let o : Arm 3 := ⟨mask rawP, mask rawL,
    choose (w.getLsbD 6) 0 ++ choose (w.getLsbD 7) 1 ++ choose (w.getLsbD 8) 2⟩
  refine ⟨s₃,o,?_⟩
  intro p l
  let x := r p ||| c l
  let a := x.getLsbD 0 && x.getLsbD 1
  let b := (x.getLsbD 2 || (w.getLsbD 0 && a)) && (x.getLsbD 3 || (w.getLsbD 1 && a))
  have atArm {n : Nat} (i : Nat) (es : List (Fin n)) (old : Fin n → Bool) :
      (arm i es).eval p l old = (x.getLsbD i || es.any old) := by
    simp [arm,Arm.eval,mask_bit,x,BitVec.getLsbD_or]
  have ha : s₁.eval p l 0 = a := by
    change ((arm 0 []).eval p l (Circuit.empty.eval p l) &&
            (arm 1 []).eval p l (Circuit.empty.eval p l)) = _
    simp [atArm,a]
  have ha₂ : s₂.eval p l 0 = a := ha
  have hb : s₂.eval p l 1 = b := by
    change ((arm 2 _).eval p l (s₁.eval p l) && (arm 3 _).eval p l (s₁.eval p l)) = b
    simp [atArm,choose_any,ha,b]
  have ha₃ : s₃.eval p l 0 = a := ha
  have hb₃ : s₃.eval p l 1 = b := hb
  have hc : s₃.eval p l 2 =
      ((x.getLsbD 4 || (w.getLsbD 2 && a) || (w.getLsbD 3 && b)) &&
       (x.getLsbD 5 || (w.getLsbD 4 && a) || (w.getLsbD 5 && b))) := by
    change ((arm 4 _).eval p l (s₂.eval p l) && (arm 5 _).eval p l (s₂.eval p l)) = _
    simp [atArm,List.any_append,choose_any,ha₂,hb,Bool.or_assoc]
  simp only [o,Arm.eval,mask_bit,List.any_append,choose_any,ha₃,hb₃,hc,threeValue,x,a,b,
    Bool.or_assoc]

/-- The extremizer is also a circuit in the list-of-gates model. -/
theorem attained {P L : Type*} [Fintype P] [Fintype L] [Membership P L] [ProjectivePlane P L]
    (hq : 3 ≤ ProjectivePlane.order P L) :
    ∃ (s : Circuit 3) (o : Arm 3),
      let accepts (p : P) (l : L) := o.eval (Fintype.equivFin P p) (Fintype.equivFin L l)
        (s.eval (Fintype.equivFin P p) (Fintype.equivFin L l))
      score (fun p l => p ∈ l) (fun p l => accepts p l = true) univ univ =
        10 * (ProjectivePlane.order P L : ℤ) - 2 ∧ ∀ p l, accepts p l = true → p ∈ l := by
  classical
  obtain ⟨w,r,c,e,h⟩ := GainAttainment.attained hq
  obtain ⟨s,o,ev⟩ := program w (fun i => r ((Fintype.equivFin P).symm i))
    (fun j => c ((Fintype.equivFin L).symm j)) (fun _ => false) (fun _ => false)
  refine ⟨s,o,?_⟩
  simpa only [ev,Equiv.symm_apply_apply,Bool.false_or] using And.intro e h

end GainRealize
