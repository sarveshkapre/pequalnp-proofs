import Mathlib.Tactic

namespace PEqualNP.PaidDepth

/- The last label is the second center choice when both readers bypass.
It is present only if the first reader uses the center on both arms. -/
private def rawWord (d : Bool) (w : Nat) (i : Fin 3) (e : Bool) : Bool :=
  let center := decide (w = 2 ∨ w = 4 ∨ w = 6 ∨ w = 7)
  let left := decide (w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6)
  let right := decide (w = 1 ∨ w = 2 ∨ w = 5 ∨ w = 6)
  if i = 0 then !((d || left || right) && (e == center))
  else if i = 1 then e != left
  else e != right

theorem ReaderBypassSharp :
∀ d : Bool, let n := if d then 8 else 7
  ∃ raw : Fin n → Fin 3 → Bool → Bool, ∀ x y : Fin n,
    let hit (i : Fin 3) (e : Bool) := raw x i e || raw y i e
    let center := hit 0 false && hit 0 true
    let left := (hit 1 false || (d && center)) && (hit 1 true || center)
    let right := hit 2 false && (hit 2 true || center)
    (left || right) = false ↔ x = y
 := by
  intro d
  cases d
  · exact ⟨fun w => rawWord false w.val, by decide⟩
  · exact ⟨fun w => rawWord true w.val, by decide⟩

end PEqualNP.PaidDepth
