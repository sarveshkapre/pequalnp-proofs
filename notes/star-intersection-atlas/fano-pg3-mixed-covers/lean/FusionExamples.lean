import FusionProjective

namespace FusionExamples

open FusionCanonical

/- Points and lines are lexicographically ordered nonzero triples over F_q,
   normalized so the first nonzero entry is 1. Incidence is zero dot product.
   The following concrete masks match the experiment's exact matrices. -/
def fanoMask (p : Fin 7) : Nat :=
  ([42,25,76,7,82,97,52] : List Nat).getD p.val 0

def fano (p l : Fin 7) : Prop := (fanoMask p).testBit l.val = true

instance : DecidableRel fano := fun _ _ => inferInstanceAs (Decidable (_ = true))

def fanoPart : Set (Fin 7) := {p | p = 0 ∨ p = 1 ∨ p = 3}

theorem fano_split : SplitZeros fano fanoPart fanoPart := by
  constructor <;> simp only [fanoPart, Set.mem_ofPred_eq] <;> decide +kernel

theorem fano_geometry :
    (∀ p, Fintype.card {l // fano p l} = 3) ∧
    (∀ l, Fintype.card {p // fano p l} = 3) ∧
    (∀ p p', p ≠ p' → ∃! l, fano p l ∧ fano p' l) := by
  simp only [ExistsUnique]
  decide +kernel

theorem fano_canonical_minimum :
    CanonicalCover fano 2 ∧ ∀ k, k < 2 → ¬ CanonicalCover fano k := by
  apply canonical_minimum_two
  exact canonical_exact_two_of_split fano_split (by decide +kernel) (by decide +kernel)

def plane3Mask (p : Fin 13) : Nat :=
  ([1170,113,2584,4372,15,4674,2338,7169,1352,1572,897,2244,4264] : List Nat).getD p.val 0

def plane3 (p l : Fin 13) : Prop := (plane3Mask p).testBit l.val = true

instance : DecidableRel plane3 := fun _ _ => inferInstanceAs (Decidable (_ = true))

theorem plane3_geometry :
    (∀ p, Fintype.card {l // plane3 p l} = 4) ∧
    (∀ l, Fintype.card {p // plane3 p l} = 4) ∧
    (∀ p p', p ≠ p' → ∃! l, plane3 p l ∧ plane3 p' l) := by
  simp only [ExistsUnique]
  decide +kernel

theorem plane3_canonical_minimum :
    CanonicalCover plane3 2 ∧ ∀ k, k < 2 → ¬ CanonicalCover plane3 k := by
  apply canonical_minimum_two
  apply projective_canonical_exact_two 3 13 plane3 (by decide) (by decide)
  · exact plane3_geometry.1
  · exact plane3_geometry.2.1
  · intro p p' h
    exact (plane3_geometry.2.2 p p' h).exists

#print axioms fano_geometry
#print axioms fano_canonical_minimum
#print axioms plane3_geometry
#print axioms plane3_canonical_minimum

end FusionExamples
