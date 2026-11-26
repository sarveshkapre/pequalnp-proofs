import ProjectedSchedule
namespace DisjointProjected
theorem bit_choose {w : Nat} (q : Bool) (a b : BitVec w) (i : Nat) :
    (if q then a else b).getLsbD i = (if q then a.getLsbD i else b.getLsbD i) := by
  cases q <;> rfl
theorem beqBits4 (x y : BitVec 4) :
    (x == y) = ((x.getLsbD 0 == y.getLsbD 0) && (x.getLsbD 1 == y.getLsbD 1) && (x.getLsbD 2 == y.getLsbD 2) && (x.getLsbD 3 == y.getLsbD 3)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true]
  constructor
  · rintro rfl
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp_all
theorem beqBits5 (x y : BitVec 5) :
    (x == y) = ((x.getLsbD 0 == y.getLsbD 0) && (x.getLsbD 1 == y.getLsbD 1) && (x.getLsbD 2 == y.getLsbD 2) && (x.getLsbD 3 == y.getLsbD 3) && (x.getLsbD 4 == y.getLsbD 4)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true]
  constructor
  · rintro rfl
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp_all
theorem beqBits10 (x y : BitVec 10) :
    (x == y) = ((x.getLsbD 0 == y.getLsbD 0) && (x.getLsbD 1 == y.getLsbD 1) && (x.getLsbD 2 == y.getLsbD 2) && (x.getLsbD 3 == y.getLsbD 3) && (x.getLsbD 4 == y.getLsbD 4) && (x.getLsbD 5 == y.getLsbD 5) && (x.getLsbD 6 == y.getLsbD 6) && (x.getLsbD 7 == y.getLsbD 7) && (x.getLsbD 8 == y.getLsbD 8) && (x.getLsbD 9 == y.getLsbD 9)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true]
  constructor
  · rintro rfl
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
end DisjointProjected
