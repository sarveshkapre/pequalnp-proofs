import FusionFanoAssembly
import FusionFanoCertificates
import FusionProfileRelabel
import FusionWeightedObstruction
import FusionRowMixed
import FusionExamples

/- A finite geometric obstruction to three full fusion pairs on the Fano plane.
The proof checks a complete catalogue of row antichains and integer pair-weight
certificates. It does not use SAT solver output or an external UNSAT assumption. -/
namespace FusionFanoLower

open FusionCanonical FusionFull FusionMixed FusionProfiles FusionCube
open FusionFanoCertificates FusionWeightedObstruction FusionRowMixed
open scoped BigOperators

theorem no_local_profile_three_of_steiner_seven
    {L : Type*} [Fintype L] (G : Fin 7 → L → Prop) [DecidableRel G]
    (separates : ∀ r s, r ≠ s → ∃ c, G r c ∧ ¬ G s c)
    (triples : ∀ c, ∃ i j k : Fin 7,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ∀ r, G r c ↔ r = i ∨ r = j ∨ r = k)
    (joining : ∀ p q, p ≠ q → ∃! l, G p l ∧ G q l) :
    ¬ LocalProfileModel G 3 := by
  classical
  rintro ⟨rwds,cwds,hlocal⟩
  have hant := row_antichain hlocal separates
  obtain ⟨cert,hcert,e,he⟩ := FusionProfileRelabel.row_antichain_certificate rwds hant
  have hg := case_good cert hcert
  exact FusionFanoAssembly.local_profile_false_of_certificate G triples joining
    rwds cwds hlocal cert hg e he

theorem fano_no_local_profile_three : ¬ LocalProfileModel FusionExamples.fano 3 := by
  apply no_local_profile_three_of_steiner_seven FusionExamples.fano
  · decide +kernel
  · decide +kernel
  · exact FusionExamples.fano_geometry.2.2

/-- The canonical and row-plus-singleton witnesses alone exclude three pairs. -/
theorem fano_not_row_mixed_three : ¬ RowMixedCover FusionExamples.fano 3 :=
  fun h => fano_no_local_profile_three (row_mixed_to_local_profile h)

theorem fano_not_mixed_three : ¬ MixedCover FusionExamples.fano 3 :=
  fun h => fano_not_row_mixed_three (mixed_cover_implies_row_mixed h)

theorem fano_rows_nonempty : ∀ r, (row FusionExamples.fano r).Nonempty := by
  intro r
  obtain ⟨c,hc,_⟩ := FusionExamples.fano_split.row_in r
  exact ⟨⟨(r,c),hc⟩,rfl⟩

theorem fano_cols_nonempty : ∀ c, (col FusionExamples.fano c).Nonempty := by
  intro c
  obtain ⟨r,hr,_⟩ := FusionExamples.fano_split.col_in c
  exact ⟨⟨(r,c),hr⟩,rfl⟩

theorem fano_not_full_three : ¬ FullCover FusionExamples.fano 3 :=
  fun h => fano_not_mixed_three
    (full_cover_implies_mixed fano_rows_nonempty fano_cols_nonempty h)

theorem fano_mixed_lower_bound (k : Nat) (h : MixedCover FusionExamples.fano k) :
    4 ≤ k := by
  by_contra hn
  exact fano_not_mixed_three (mixed_cover_mono (by omega) h)

theorem fano_full_lower_bound (k : Nat) (h : FullCover FusionExamples.fano k) :
    4 ≤ k :=
  fano_mixed_lower_bound k
    (full_cover_implies_mixed fano_rows_nonempty fano_cols_nonempty h)

#print axioms no_local_profile_three_of_steiner_seven
#print axioms fano_no_local_profile_three
#print axioms fano_not_row_mixed_three
#print axioms fano_not_mixed_three
#print axioms fano_not_full_three
#print axioms fano_full_lower_bound

end FusionFanoLower
