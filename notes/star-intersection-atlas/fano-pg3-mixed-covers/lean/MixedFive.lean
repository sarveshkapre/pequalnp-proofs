import FusionMixed
import FusionExamples

/- Five explicit pairs cover both singleton witness families on the actual
   order-three plane in Pro session 007. The operands are subsets of its
   nonincidences. The row and column labels are five-bit cube vertices. -/
namespace Plane3MixedFive
open FusionCanonical FusionMixed

abbrev G := FusionExamples.plane3
instance : DecidableRel G := fun r c =>
  inferInstanceAs (Decidable (FusionExamples.plane3 r c))

def pointWord (r : Fin 13) : Nat :=
  [6,18,24,17,15,9,30,10,0,23,29,3,5].getD r.val 0
def lineWord (c : Fin 13) : Nat :=
  [4,16,28,19,13,8,31,26,11,2,25,21,22].getD c.val 0
def arm (b : Bool) (i : Fin 5) : Set (Zero G) :=
  {z | (pointWord z.val.1).testBit i.val = b ∨ (lineWord z.val.2).testBit i.val = b}

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 1024

theorem canonical_cases : ∀ (r c : Fin 13), G r c →
    ∃ i : Fin 5, Covers (canonical G r c) (arm false i) (arm true i) := by
  simp only [covers_iff, Set.subset_def, arm, row, col, Set.mem_ofPred_eq]
  unfold G FusionExamples.plane3
  decide +kernel

theorem row_cases : ∀ (r c : Fin 13) (z : Zero G), G r c → z.val.2 = c →
    ∃ i : Fin 5, Covers (upTwo (row G r) {z}) (arm false i) (arm true i) := by
  simp only [covers_upTwo_iff, Set.subset_def, arm, row, Set.mem_ofPred_eq]
  unfold G FusionExamples.plane3
  decide +kernel

theorem column_cases : ∀ (r c : Fin 13) (z : Zero G), G r c → z.val.1 = r →
    ∃ i : Fin 5, Covers (upTwo (col G c) {z}) (arm false i) (arm true i) := by
  simp only [covers_upTwo_iff, Set.subset_def, arm, col, Set.mem_ofPred_eq]
  unfold G FusionExamples.plane3
  decide +kernel

theorem five_pairs : MixedCover FusionExamples.plane3 5 := by
  refine ⟨arm false, arm true, ?_⟩
  intro F hw
  rcases hw with ⟨r,c,h,rfl⟩ | ⟨r,c,z,h,hz,rfl⟩ | ⟨r,c,z,h,hz,rfl⟩
  · exact canonical_cases r c h
  · exact row_cases r c z h hz
  · exact column_cases r c z h hz

#print axioms five_pairs
end Plane3MixedFive
