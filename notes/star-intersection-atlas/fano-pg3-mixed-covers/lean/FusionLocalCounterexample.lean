import FusionProfiles
import FusionExamples

/-! A checked limitation of the local-profile relaxation. This is a model of
the necessary local cube conditions, not a full fusion cover or a circuit. -/
namespace FusionLocalCounterexample

open FusionProfiles

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def word (c : Nat) : Word 4 := fun i =>
  ⟨c / 3 ^ (3 - i.val) % 3, Nat.mod_lt _ (by decide)⟩

def rowCodes : List Nat :=
  [49, 76, 43, 53, 70, 77, 68, 41, 44, 79, 50, 71, 80]

def columnCodes : List Nat :=
  [24, 24, 3, 3, 11, 27, 28, 10, 1, 63, 57, 18, 1]

def auxiliaryCodes : List Nat :=
  [28, 0, 3, 3, 0, 27, 28, 0, 1, 4, 0, 4, 1,
   0, 73, 3, 3, 0, 0, 0, 55, 1, 4, 57, 4, 1,
   28, 33, 28, 0, 0, 10, 7, 7, 1, 0, 10, 0, 1,
   8, 8, 0, 45, 0, 27, 24, 33, 0, 8, 20, 18, 0,
   0, 0, 0, 0, 60, 10, 7, 7, 1, 63, 10, 55, 1,
   56, 0, 3, 3, 5, 23, 0, 57, 72, 0, 20, 18, 0,
   56, 0, 3, 3, 5, 0, 12, 12, 0, 11, 56, 0, 63,
   0, 29, 3, 3, 5, 27, 12, 12, 39, 11, 0, 0, 0,
   8, 8, 36, 0, 11, 15, 0, 33, 0, 8, 0, 35, 15,
   24, 24, 0, 19, 60, 0, 7, 7, 1, 0, 0, 18, 1,
   0, 29, 3, 3, 5, 23, 30, 0, 0, 0, 20, 18, 48,
   8, 8, 0, 65, 11, 15, 0, 0, 60, 8, 56, 0, 15,
   8, 8, 74, 0, 56, 0, 24, 0, 60, 8, 20, 18, 0]

def rowWords (r : Fin 13) : Word 4 := word (rowCodes.getD r.val 0)
def columnWords (c : Fin 13) : Word 4 := word (columnCodes.getD c.val 0)
def auxiliaryWords (r c : Fin 13) : Word 4 :=
  word (auxiliaryCodes.getD (13 * r.val + c.val) 0)

theorem checked_incidence : ∀ r c : Fin 13,
    FusionExamples.plane3 r c → Opposes (rowWords r) (columnWords c) := by
  unfold Opposes
  decide +kernel

theorem checked_outside : ∀ r c : Fin 13, ¬ FusionExamples.plane3 r c →
    Compatible (rowWords r) (auxiliaryWords r c) ∧
    Compatible (columnWords c) (auxiliaryWords r c) ∧
    ∀ s : Fin 13, FusionExamples.plane3 s c →
      Opposes (rowWords s) (auxiliaryWords r c) := by
  unfold Compatible Opposes
  decide +kernel

theorem plane3_local_profile_four : LocalProfileModel FusionExamples.plane3 4 := by
  refine ⟨rowWords, columnWords, checked_incidence, ?_⟩
  intro r c hrc
  exact ⟨auxiliaryWords r c, checked_outside r c hrc⟩

#print axioms checked_incidence
#print axioms checked_outside
#print axioms plane3_local_profile_four

end FusionLocalCounterexample
