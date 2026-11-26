import FusionMixed
import FusionExamples

/- Four actual operand pairs cover the two mixed witness families on Fano. -/
namespace FanoMixedFour
open FusionCanonical FusionMixed

abbrev G := FusionExamples.fano
instance : DecidableRel G := fun r c =>
  inferInstanceAs (Decidable (FusionExamples.fano r c))

def pointWord (r : Fin 7) : Nat :=
  [12,11,10,0,15,7,5].getD r.val 0
def lineWord (c : Fin 7) : Nat :=
  [12,3,15,5,6,10,9].getD c.val 0
def arm (b : Bool) (i : Fin 4) : Set (Zero G) :=
  {z | (pointWord z.val.1).testBit i.val = b ∨ (lineWord z.val.2).testBit i.val = b}

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 1024

theorem canonical_cases : ∀ (r c : Fin 7), G r c →
    ∃ i : Fin 4, Covers (canonical G r c) (arm false i) (arm true i) := by
  simp only [covers_iff, Set.subset_def, arm, row, col, Set.mem_ofPred_eq]
  unfold G FusionExamples.fano
  decide +kernel

theorem row_cases : ∀ (r c : Fin 7) (z : Zero G), G r c → z.val.2 = c →
    ∃ i : Fin 4, Covers (upTwo (row G r) {z}) (arm false i) (arm true i) := by
  simp only [covers_upTwo_iff, Set.subset_def, arm, row, Set.mem_ofPred_eq]
  unfold G FusionExamples.fano
  decide +kernel

theorem column_cases : ∀ (r c : Fin 7) (z : Zero G), G r c → z.val.1 = r →
    ∃ i : Fin 4, Covers (upTwo (col G c) {z}) (arm false i) (arm true i) := by
  simp only [covers_upTwo_iff, Set.subset_def, arm, col, Set.mem_ofPred_eq]
  unfold G FusionExamples.fano
  decide +kernel

theorem four_pairs : MixedCover FusionExamples.fano 4 := by
  refine ⟨arm false, arm true, ?_⟩
  intro F hw
  rcases hw with ⟨r,c,h,rfl⟩ | ⟨r,c,z,h,hz,rfl⟩ | ⟨r,c,z,h,hz,rfl⟩
  · exact canonical_cases r c h
  · exact row_cases r c z h hz
  · exact column_cases r c z h hz

#print axioms four_pairs
end FanoMixedFour
