import PEqualNP.FiveRows.Templates
import PEqualNP.FiveRows.Geometry

namespace FiveRowDistinct
theorem distinct_iff (n : Nat) : DistinctGap n ↔ 7 ≤ n ∧ n ≤ 22 := by
  constructor
  · rintro ⟨z,hd,h3,h2,h4,lower⟩
    have lo := (FiveRowThreshold.gap_iff_seven_le n).mp ⟨z,h3,h2,h4,lower⟩
    obtain ⟨rows,cols,sep⟩ := uses_shared h3 (lower 3 (by decide)) hd
    exact ⟨lo,FiveRowPartition.shared_columns rows cols sep⟩
  · rintro ⟨lo,hi⟩
    exact intermediate n lo hi
end FiveRowDistinct
