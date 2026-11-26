import FusionLocalCounterexample
import FusionRowMixed

/-! Actual operands realize a four-pair cover of the one-sided PG(2,3) witness
family. A specified dual witness is not covered. This is not a full cover. -/
namespace FusionRowMixedCounterexample

open FusionCanonical FusionMixed FusionProfiles FusionRowMixed
open FusionLocalCounterexample

abbrev G := FusionExamples.plane3

instance : DecidableRel G := fun r c =>
  inferInstanceAs (Decidable (FusionExamples.plane3 r c))

def operandE (i : Fin 4) : Set (Zero G) :=
  {z | rowWords z.val.1 i = 1 ∨ columnWords z.val.2 i = 1}

def operandH (i : Fin 4) : Set (Zero G) :=
  {z | rowWords z.val.1 i = 2 ∨ columnWords z.val.2 i = 2}

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 1024

theorem checked_canonical_cover : ∀ r c : Fin 13, G r c →
    ∃ i : Fin 4, Covers (canonical G r c) (operandE i) (operandH i) := by
  simp only [covers_iff]
  simp only [Set.subset_def, operandE, operandH, row, col, Set.mem_ofPred_eq]
  unfold G FusionExamples.plane3
  decide +kernel

theorem checked_row_cover : ∀ (r c : Fin 13) (z : Zero G),
    G r c → z.val.2 = c →
    ∃ i : Fin 4, Covers (upTwo (row G r) {z}) (operandE i) (operandH i) := by
  simp only [covers_upTwo_iff, Set.singleton_subset_iff]
  simp only [Set.subset_def, operandE, operandH, row, Set.mem_ofPred_eq]
  unfold G FusionExamples.plane3
  decide +kernel

theorem plane3_row_mixed_four : RowMixedCover G 4 := by
  refine ⟨operandE, operandH, ?_⟩
  intro F hF
  rcases hF with ⟨r,c,hrc,rfl⟩ | ⟨r,c,z,hrc,hz,rfl⟩
  · exact checked_canonical_cover r c hrc
  · exact checked_row_cover r c z hrc hz

def zero00 : Zero G := ⟨(0,0), by decide⟩

theorem dual_witness_not_covered : ∀ i : Fin 4,
    ¬ Covers (upTwo (col G 1) {zero00}) (operandE i) (operandH i) := by
  simp only [covers_upTwo_iff, Set.singleton_subset_iff]
  simp only [Set.subset_def, operandE, operandH, col, Set.mem_ofPred_eq]
  decide +kernel

theorem explicit_missing_mixed_witness : ∃ F : Set (Set (Zero G)),
    MixedWitness G F ∧ ∀ i : Fin 4, ¬ Covers F (operandE i) (operandH i) := by
  refine ⟨upTwo (col G 1) {zero00}, ?_, dual_witness_not_covered⟩
  exact Or.inr (Or.inr ⟨0,1,zero00,by decide,rfl,rfl⟩)

/-- The first two column profiles are identical in the local model. -/
theorem equal_selected_column_words : columnWords 0 = columnWords 1 := rfl

/-- Equality of these two column profiles obstructs the dual witness for any
actual operands, not just the explicit operands chosen above. -/
theorem equal_column_profiles_obstruct
    (E H : Fin 4 → Set (Zero G))
    (h : profile E H (col G 0) = profile E H (col G 1)) :
    ∀ i : Fin 4, ¬ Covers (upTwo (col G 1) {zero00}) (E i) (H i) := by
  intro i hi
  have hc := subset_compatible E H
    (Set.singleton_subset_iff.mpr rfl : ({zero00} : Set (Zero G)) ⊆ col G 0)
  rw [h] at hc
  exact hc (covers_opposes E H i hi).symm

#print axioms plane3_row_mixed_four
#print axioms explicit_missing_mixed_witness
#print axioms equal_column_profiles_obstruct

end FusionRowMixedCounterexample
