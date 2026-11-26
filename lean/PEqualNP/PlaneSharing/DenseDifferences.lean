import Mathlib.Tactic

/-! A single invertible change of the output coordinate makes every surjective
two-term slope difference dense outside its two original locations. -/
open scoped BigOperators
namespace PlaneSharing.Density
variable {G K : Type} [Group G] [Fintype G] [Field K]
private def tr (act : G →* (K ≃+* K)) (z : K) := ∑ g : G, act g z

private theorem invariant (act : G →* (K ≃+* K)) (h : G) (z : K) :
    tr act (act h z) = tr act z := by
  have p := Equiv.sum_comp (Equiv.mulRight h) (fun g => act g z)
  simpa [tr, map_mul] using p

private theorem fixed (act : G →* (K ≃+* K)) (h : G) (z : K) :
    act h (tr act z) = tr act z := by
  rw [tr, map_sum]
  have p := Equiv.sum_comp (Equiv.mulLeft h) (fun g => act g z)
  simpa [map_mul] using p

private theorem tr_add (act : G →* (K ≃+* K)) (a b : K) :
    tr act (a+b) = tr act a + tr act b := by simp [tr, Finset.sum_add_distrib]
private theorem tr_sub (act : G →* (K ≃+* K)) (a b : K) :
    tr act (a-b) = tr act a - tr act b := by simp [tr, Finset.sum_sub_distrib]

private theorem adjoint (act : G →* (K ≃+* K)) (i : G) (m x : K) :
    tr act (m * act i x) = tr act ((act i).symm m * x) := by
  simpa using invariant act i ((act i).symm m * x)

private theorem vanish (act : G →* (K ≃+* K)) {u : K} (hu : tr act u = 0) (z : K) :
    tr act (u * tr act z) = 0 := by
  change (∑ g : G, act g (u * tr act z)) = 0
  simp only [map_mul, fixed, ← Finset.sum_mul]
  change tr act u * tr act z = 0
  rw [hu,zero_mul]

private theorem shear (act : G →* (K ≃+* K)) {u : K} (hu : tr act u = 0) :
    Function.Bijective (fun y : K => y + u * tr act y) := by
  let undo := fun y : K => y - u * tr act y
  have left : Function.LeftInverse undo (fun y : K => y + u * tr act y) := by
    intro z
    simp [undo, tr_add, vanish act hu]
  have right : Function.RightInverse undo (fun y : K => y + u * tr act y) := by
    intro z
    simp [undo, tr_sub, vanish act hu]
  exact ⟨left.injective,right.surjective⟩
end PlaneSharing.Density

open PlaneSharing.Density in
theorem PEqualNP.PlaneSharing.DenseDifferences :
    ∀ (G K : Type) [Group G] [Fintype G] [DecidableEq G] [Field K]
    (act : G →* (K ≃+* K)) (i j : G) (m n u : K),
  let tr := fun z : K => ∑ g : G, act g z
  let a := fun x : K => m * act i x - n * act j x
  let s := fun y : K => y + u * tr y
  (∃ z, tr z ≠ 0) → tr u = 0 → u ≠ 0 → Function.Surjective a →
    Function.Bijective s ∧ ∃ v : K, v ≠ 0 ∧
      let coeff := fun g : G => (if g = i then m else 0) -
        (if g = j then n else 0) + u * act g v
      (∀ x, s (a x) = ∑ g : G, coeff g * act g x) ∧
      ∀ g, g ≠ i → g ≠ j → coeff g ≠ 0 := by
  intro G K _ _ _ _ act i j m n u
  dsimp only
  intro nonzero hu u0 onto
  let v := (act i).symm m - (act j).symm n
  have move (x : K) : tr act (m * act i x - n * act j x) = tr act (v*x) := by
    rw [tr_sub, adjoint act i, adjoint act j, show v*x = _ from sub_mul _ _ _, tr_sub]
  have v0 : v ≠ 0 := by
    intro hz
    obtain ⟨z,hz'⟩ := nonzero
    obtain ⟨x,hx⟩ := onto z
    change m * act i x - n * act j x = z at hx
    have eq := move x
    rw [hx,hz,zero_mul] at eq
    exact hz' (eq.trans (by simp [tr]))
  refine ⟨shear act hu,v,v0,?_,?_⟩
  · intro x
    change _ + u * tr act (m * act i x - n * act j x) = _
    rw [move]
    simp [tr, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_assoc, ← map_mul, ← Finset.mul_sum, ite_mul]
  · intro g hi hj
    simp [hi,hj,u0,v0]
