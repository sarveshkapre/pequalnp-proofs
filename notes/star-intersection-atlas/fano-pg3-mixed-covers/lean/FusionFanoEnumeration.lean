import FusionFanoCertificateData
import FusionCube
import FusionAntichainEnum

/-! Complete coverage of all seven-element antichains of three-coordinate
partial words. The data list contains every case, not only symmetry orbits. -/
namespace FusionFanoCertificates

instance decidableRefines {k : Nat} (a b : FusionProfiles.Word k) :
    Decidable (FusionProfiles.Refines a b) := by
  unfold FusionProfiles.Refines
  infer_instance

/-- A structurally recursive evaluator for the proved pruned enumeration. -/
def chooseWithFuel {α : Type*} (rel : α → α → Bool) :
    Nat → Nat → List α → List (List α)
  | 0, n, _ => if n = 0 then [[]] else []
  | _ + 1, 0, _ => [[]]
  | _ + 1, _ + 1, [] => []
  | fuel + 1, n + 1, a :: xs =>
      (chooseWithFuel rel fuel n (xs.filter (rel a))).map (a :: ·) ++
        chooseWithFuel rel fuel (n + 1) xs

theorem chooseWithFuel_eq {α : Type*} (rel : α → α → Bool)
    (fuel n : Nat) (xs : List α) (hlen : xs.length ≤ fuel) :
    chooseWithFuel rel fuel n xs =
      FusionAntichainEnum.chooseCompatible rel n xs := by
  induction fuel generalizing n xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst xs
    cases n <;> simp [chooseWithFuel, FusionAntichainEnum.chooseCompatible]
  | succ fuel ih =>
    cases n with
    | zero => simp [chooseWithFuel, FusionAntichainEnum.chooseCompatible]
    | succ n =>
      cases xs with
      | nil => simp [chooseWithFuel, FusionAntichainEnum.chooseCompatible]
      | cons a xs =>
        have hx : xs.length ≤ fuel := Nat.le_of_succ_le_succ hlen
        have hf : (xs.filter (rel a)).length ≤ fuel :=
          (List.length_filter_le _ _).trans hx
        simp only [chooseWithFuel, FusionAntichainEnum.chooseCompatible]
        rw [ih n _ hf, ih (n + 1) xs hx]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cases_enumerate :
    cases.map (fun c => List.ofFn (rows c)) =
      FusionAntichainEnum.chooseCompatible
        (fun a b : FusionCube.Code => decide
          (¬ FusionProfiles.Refines (FusionCube.decode a) (FusionCube.decode b) ∧
           ¬ FusionProfiles.Refines (FusionCube.decode b) (FusionCube.decode a)))
        7 (List.finRange 27) := by
  let rel : FusionCube.Code → FusionCube.Code → Bool := fun a b => decide
    (¬ FusionProfiles.Refines (FusionCube.decode a) (FusionCube.decode b) ∧
     ¬ FusionProfiles.Refines (FusionCube.decode b) (FusionCube.decode a))
  have h : cases.map (fun c => List.ofFn (rows c)) =
      chooseWithFuel rel 27 7 (List.finRange 27) := by
    decide +kernel
  exact h.trans (chooseWithFuel_eq rel 27 7 (List.finRange 27) (by simp))

#print axioms chooseWithFuel_eq
#print axioms cases_enumerate

end FusionFanoCertificates
