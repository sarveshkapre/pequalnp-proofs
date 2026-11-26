import PEqualNP.ThreeGateGain.GainAdmissible
import PEqualNP.ThreeGateGain.GainFrameResidual
import PEqualNP.ThreeGateGain.GainForcedBridge

namespace GainFrameBridge
open Finset TriangleOptimality GainGeometry GainFinite GainSelection GainForcedBridge

/-- The finite host certificate bounds every positive core, with arbitrary
multiplicities of active row and column types and either orientation of a center. -/
theorem physical_upper {P L : Type*} (G : P → L → Prop) (sq : NoSquare G)
    (h : Host) (r : P → WordType) (c : L → WordType) (A : Finset P) (B : Finset L)
    (d : ℤ) (degree : 17 ≤ d)
    (row : ∀ p ∈ A, ∑ l ∈ B, hit G p l ≤ d)
    (col : ∀ l ∈ B, ∑ p ∈ A, hit G p l ≤ d)
    (rpos : ∀ p ∈ A, 0 < ∑ l ∈ B, weight G (fun p l => hostEdge h (r p) (c l) = true) p l)
    (cpos : ∀ l ∈ B, 0 < ∑ p ∈ A, weight G (fun p l => hostEdge h (r p) (c l) = true) p l)
    (checked : checkHost h = true) :
    score G (fun p l => hostEdge h (r p) (c l) = true) A B ≤ 10*d-12 := by
  classical
  let H := fun i j => hostEdge h i j = true
  let s := GainSelection.select G sq H r c A B cpos
  have trans : NoSquare (fun l p => G p l) :=
    fun l m p q a b e f => (sq p q l m a e b f).symm
  let t := GainSelection.select (fun l p => G p l) trans (fun j i => H i j) c r B A rpos
  let rl := fromSet t.leafTypes
  let cl := fromSet s.leafTypes
  have cover (i j : WordType) (h₁ : ∀ k ∈ s.leafTypes, ¬ H i k)
      (h₂ : ∀ k ∈ t.leafTypes, ¬ H k j) (e : H i j) :
      i ∈ R h rl cl ∧ j ∈ C h rl cl :=
    cover_live h rl cl i j (fun v hv => h₁ v ((fromSet_mem _ _).mp hv))
      (fun u hu => h₂ u ((fromSet_mem _ _).mp hu)) e
  have lim : (R h rl cl).card ≤ 28 := by
    have le := Finset.card_le_univ (R h rl cl)
    simpa only [Fintype.card_fin] using le.trans (show Fintype.card WordType ≤ 28 by decide)
  have actual := host_score G sq s t _ _ cover lim d row col
  have bound := residual_score h rl cl
  have forced := crossings_physical h s t rl cl (fromSet_nodup _) (fromSet_nodup _)
    (fromSet_toFinset _) (fromSet_toFinset _) (edge_symm h)
  rw [← s.center_edges t] at forced
  have frame := physical_frame h s t checked
  change testFrame h rl cl = true at frame
  simp only [testFrame,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at frame
  have tr : rl.length = t.leafTypes.card := fromSet_length _
  have tc : cl.length = s.leafTypes.card := fromSet_length _
  let w := (s.leafTypes.card:ℤ) + t.leafTypes.card
  let corr := (GainFinite.residual h rl cl:ℤ) - crossings h rl cl
  apply stretch (t:=w) (rem:=corr) _ degree _ _
  · dsimp [w]; omega
  · dsimp [w,corr]; omega
  · dsimp [w,corr]
    linarith

#print axioms physical_upper
end GainFrameBridge
