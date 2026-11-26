import SwitchCore

namespace SharedSwitch
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux

abbrev value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) := SwitchCore.value C x w
abbrev belowAnd := SwitchCore.belowAnd
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem matched_pairs_le_dirty {I : Type*} [Fintype I] (ao : IsAO2 n C) (top : TopForm G C)
    (e : I → Bool → Fin n) (neg : (I → Bool) → Fin n → Bool) (W : Set ℕ)
    (under : ∀ w ∈ W, belowAnd n C w) (contains : ∀ b i, neg b (e i (b i)) = true)
    (hit : ∀ i, ∃ w ∈ W, SwitchCore.value C (pairInput (e i false) (e i true)) w = true)
    (quiet : ∀ b w, w ∈ W → SwitchCore.value C (neg b) w = false) :
    Fintype.card I ≤ (junk G C).card := by
  simpa [SwitchCore.gates] using SwitchCore.matched_pairs_le_gates ao top
    (E := ∅) (by simp [SwitchCore.valid]) e neg W
    (fun w hw => Or.inl (under w hw)) contains hit quiet

end SharedSwitch
