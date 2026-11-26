import PEqualNP.Outside.CircuitCopies
import PEqualNP.Outside.MissingMatching
import PEqualNP.MetaComplexity.Helpers.RepInduced
import PEqualNP.Outside.L_meta_6158

namespace PEqualNP.Outside.ThreeMissing_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
def base (r c : Fin 4) := (64478 : Nat).testBit (4*r.val+c.val)
def padded (r c : Fin 4) := (854 : Nat).testBit (4*r.val+c.val)
private def kept : Finset (Fin 4) := {0,1,2}

private theorem up : RepSizeAtMost base 9 := by
  -- The first seven gates form the majority of the first three row-or-column pairs.
  -- A cell on the fourth row or fourth column is always accepted.
  let D : Circuit := ⟨[
    ⟨.or,[0,4]⟩, ⟨.or,[1,5]⟩, ⟨.or,[2,6]⟩,
    ⟨.or,[8,9]⟩, ⟨.and,[8,9]⟩, ⟨.and,[10,11]⟩, ⟨.or,[12,13]⟩,
    ⟨.or,[3,7]⟩, ⟨.or,[14,15]⟩],16⟩
  refine ⟨D,?_,by decide,by decide⟩
  intro g hg
  simp only [D,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

private theorem lower {k} (h : RepSizeAtMost base k) : 9 ≤ k := by
  obtain ⟨s,rep,count⟩ := PEqualNP.MetaComplexity.RepInduced.induced 4 4 k base kept kept
    (by decide) (by decide) (by decide) h
  have eq : (fun u v => base u v && decide (u ∈ kept) && decide (v ∈ kept)) = padded := by
    funext u v
    exact (by decide : ∀ i j, (base i j && decide (i ∈ kept) && decide (j ∈ kept)) = padded i j) u v
  rw [eq] at rep
  have big : 7 ≤ s := by
    by_contra! small
    obtain ⟨D,ops,size,eval⟩ := rep
    exact L_meta_6158.2 ⟨D,ops,by omega,eval⟩
  have nrows : (Finset.univ.filter (fun a : Fin 4 => ∃ b, base a b = true ∧ ∃ a', base a' b = false)).card = 4 := by decide
  have ncols : (Finset.univ.filter (fun b : Fin 4 => ∃ a, base a b = true ∧ ∃ b', base a b' = false)).card = 4 := by decide
  have krows : (kept.filter (fun a => ∃ b ∈ kept, base a b = true)).card = 3 := by decide
  have kcols : (kept.filter (fun b => ∃ a ∈ kept, base a b = true)).card = 3 := by decide
  rw [nrows,ncols,krows,kcols] at count
  omega

-- Map every additional index to the universal fourth row or column.
private def group {n} (i : Fin n) : Fin 4 := ⟨min i.val 3,by omega⟩

private theorem onto {n} (hn : 4 ≤ n) : Function.Surjective (@group n) := by
  intro i
  refine ⟨⟨i.val,by omega⟩,?_⟩
  apply Fin.ext
  change min i.val 3 = i.val
  exact Nat.min_eq_left (by omega)

theorem threshold {R C} (hr : 4 ≤ R) (hc : 4 ≤ C) (k : Nat) :
    RepSizeAtMost (fun (r : Fin R) (c : Fin C) => base (group r) (group c)) k ↔ R+C+1 ≤ k := by
  rw [CircuitCopies 4 4 R C base (by decide) (by decide) (by decide) (by decide)
    group group (onto hr) (onto hc) k]
  constructor
  · rintro ⟨j,baseBound,count⟩
    have := lower baseBound
    omega
  · intro le
    exact ⟨9,up,by omega⟩

theorem maskEq {R C : Nat} (u : Fin R) (v : Fin C) :
    base (group u) (group v) = !decide (u.val = v.val ∧ u.val < 3) := by
  have fixed : ∀ i j : Fin 4, base i j = !decide (i.val = j.val ∧ i.val < 3) := by decide
  rw [fixed]
  have eq : ((group u).val = (group v).val ∧ (group u).val < 3) ↔
      (u.val = v.val ∧ u.val < 3) := by
    change (min u.val 3 = min v.val 3 ∧ min u.val 3 < 3) ↔ _
    omega
  exact congrArg Bool.not (decide_eq_decide.mpr eq)

end PEqualNP.Outside.ThreeMissing_aux

/-- Three distinct missing pairs give three exact minima for the same repeated desk table. -/
theorem PEqualNP.Outside.ThreeMissing :
  ∀ (R C : Nat), 4 ≤ R → 4 ≤ C → ∀ k : Nat,
  let G := fun (r : Fin R) (c : Fin C) => (64478 : Nat).testBit (4 * min r.val 3 + min c.val 3)
  (PEqualNP.Represents.RepSizeAtMost G k ↔ R+C+1 ≤ k) ∧
  ((∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      D.size ≤ k ∧ PEqualNP.Represents.Represents G D) ↔ 6 ≤ k) ∧
  (PEqualNP.Represents.RepSizeAtMost (fun r c => !G r c) k ↔ 5 ≤ k) := by
  intro R C hr hc k
  let G := fun (r : Fin R) (c : Fin C) => (64478 : Nat).testBit (4 * min r.val 3 + min c.val 3)
  change (PEqualNP.Represents.RepSizeAtMost G k ↔ _) ∧
    ((∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ k ∧
        PEqualNP.Represents.Represents G D) ↔ _) ∧
    (PEqualNP.Represents.RepSizeAtMost (fun r c => !G r c) k ↔ _)
  have eq : G = (fun (r : Fin R) (c : Fin C) => !decide (r.val = c.val ∧ r.val < 3)) :=
    funext fun u => funext fun v => ThreeMissing_aux.maskEq u v
  refine ⟨ThreeMissing_aux.threshold hr hc k, ?_⟩
  rw [eq]
  simpa only [Bool.not_not] using
    (MissingMatching R C 3 (by decide) (by omega) (by omega) k)
