import PEqualNP.ThreeGateGain.GainFrameBridge
import PEqualNP.ThreeGateGain.GainForced

namespace GainForcedBridge
open Finset TriangleOptimality GainSelection GainForced GainFinite GainFrameBridge
open scoped Classical

/-- A positive bit test says every pair of actual partners crosses. -/
theorem forces_sound (h : Host) (rl cl : Leaves) (i j : WordType)
    (symm : ∀ u v, hostEdge h u v = hostEdge h v u)
    (hf : forces h rl cl i j = true) :
    forced (fun u v => hostEdge h u v = true) rl.toFinset cl.toFinset i j := by
  intro v hv u hu
  have hv' : (privateMask h rl i).testBit v.val = true := by
    apply (private_bit ..).mpr
    exact ⟨hv.1,fun k hk e => hv.2 k (by simpa using hk) e⟩
  have hu' : (privateMask h cl j).testBit u.val = true := by
    apply (private_bit ..).mpr
    refine ⟨(symm j u).trans hu.1,?_⟩
    intro k hk e
    exact hu.2 k (by simpa using hk) ((symm u k).trans e)
  have test := (List.all_eq_true.mp hf) u ((positions_mem ..).mpr hu')
  have he : rowMask h u &&& privateMask h rl i = privateMask h rl i := by simpa using test
  have e := congrArg (fun n : Nat => n.testBit v.val) he
  simpa [Nat.testBit_and,hv'] using e

theorem crossings_le_forced (h : Host) (rl cl : Leaves) (rnodup : rl.Nodup) (cnodup : cl.Nodup)
    (symm : ∀ u v, hostEdge h u v = hostEdge h v u) :
    (crossings h rl cl : ℤ) ≤ (forcedCount (fun u v => hostEdge h u v = true) rl.toFinset cl.toFinset : ℤ) := by
  classical
  unfold forcedCount
  rw [count_edges, edges]
  unfold crossings
  rw [← List.sum_toFinset _ rnodup, Nat.cast_sum]
  apply sum_le_sum; intro i _
  rw [← List.toFinset_card_of_nodup (cnodup.filter _)]
  have le : (cl.filter (forces h rl cl i)).toFinset ⊆
      cl.toFinset.filter (forced (fun u v => hostEdge h u v = true) rl.toFinset cl.toFinset i) := by
    intro j hj
    simp only [List.mem_toFinset,List.mem_filter] at hj
    exact mem_filter.mpr ⟨by simpa using hj.1,forces_sound h rl cl i j symm hj.2⟩
  simpa [hit,Finset.sum_boole] using (show ((cl.filter (forces h rl cl i)).toFinset.card:ℤ) ≤ _ from
    Int.ofNat_le.mpr (card_le_card le))

theorem crossings_physical {P L : Type*} (h : Host) {r : P → WordType} {c : L → WordType}
    {A : Finset P} {B : Finset L}
    (s : Side (fun i j => hostEdge h i j = true) r c A B)
    (t : Side (fun j i => hostEdge h i j = true) c r B A)
    (rl cl : Leaves) (rnodup : rl.Nodup) (cnodup : cl.Nodup)
    (eqr : rl.toFinset = t.leafTypes) (eqc : cl.toFinset = s.leafTypes)
    (symm : ∀ u v, hostEdge h u v = hostEdge h v u) :
    (crossings h rl cl : ℤ) ≤ edges (fun p l => hostEdge h (r p) (c l) = true) s.centers t.centers := by
  have h₁ := crossings_le_forced h rl cl rnodup cnodup symm
  rw [eqr,eqc] at h₁
  exact h₁.trans (forced_bound s t)

#print axioms crossings_physical
end GainForcedBridge
