import PEqualNP.SixSharing.ThreeIntersectionsFormula
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

/-! Exact formula budget for equality of biclique-component labels,
including inactive rows or columns, in the project's zero-set model. -/
namespace ForestMatching
open TwoIntersections ThreeIntersectionsFormula Set

private theorem labels {m d h : Nat} (capacity : m ≤ d.choose h) :
    ∃ code : Fin m → Finset (Fin d), Function.Injective code ∧
      ∀ i, (code i).card = h := by
  classical
  let pool := (Finset.univ : Finset (Fin d)).powersetCard h
  have card : Fintype.card ↥pool = d.choose h := by
    simp [pool]
  let pick (i : Fin m) : ↥pool :=
    (Fintype.equivFin ↥pool).symm ⟨i.val, by rw [card]; exact lt_of_lt_of_le i.isLt capacity⟩
  refine ⟨fun i => (pick i).val, ?_, fun i => (Finset.mem_powersetCard.mp (pick i).property).2⟩
  intro i j eqv
  have eqp : pick i = pick j := Subtype.ext eqv
  have eqi := (Fintype.equivFin ↥pool).symm.injective eqp
  exact Fin.ext (congrArg (fun q : Fin (Fintype.card ↥pool) => q.val) eqi)

private def unionOn {X Y I : Type*} (s : I → Set (X × Y)) (l : List I) : Set (X × Y) :=
  {p | ∃ i ∈ l, p ∈ s i}

private theorem union_formula {X Y I : Type*} (s : I → Set (X × Y))
    (rect : ∀ i, Rectangle (s i)) (l : List I) (nonempty : l ≠ []) :
    Formula Rectangle (l.length - 1) (unionOn s l) := by
  induction l with
  | nil => contradiction
  | cons a t ih =>
    cases t with
    | nil =>
      have e : unionOn s [a] = s a := by ext p; simp [unionOn]
      rw [e]
      exact .base (rect a)
    | cons b rest =>
      have e : unionOn s (a::b::rest) = s a ∪ unionOn s (b::rest) := by
        ext p; simp [unionOn]
      rw [e]
      simpa using Formula.join (Formula.base (rect a)) (ih (by simp))

def mismatch {X Y : Type*} {m : Nat} (row : X → Option (Fin m))
    (col : Y → Option (Fin m)) : Set (X × Y) :=
  {p | ¬ ∃ i, row p.1 = some i ∧ col p.2 = some i}

theorem layer_formula {X Y : Type*} {m d h : Nat} (positive : 0 < h) (proper : h < d)
    (capacity : m ≤ d.choose h) (row : X → Option (Fin m)) (col : Y → Option (Fin m)) :
    Formula Rectangle (d-1) (mismatch row col) := by
  classical
  obtain ⟨code, injective, weight⟩ := labels capacity
  let a (i : Fin d) : Set X := {r | ∀ l, row r = some l → i ∈ code l}
  let b (i : Fin d) : Set Y := {c | ∀ l, col c = some l → i ∉ code l}
  let rect (i : Fin d) := a i ×ˢ b i
  have diff : ∀ u v : Fin m, u ≠ v → ∃ i ∈ code u, i ∉ code v := by
    intro u v ne
    by_contra! incl
    exact ne (injective (Finset.eq_of_subset_of_card_le incl (by simp [weight])))
  have represent : unionOn rect (List.finRange d) = mismatch row col := by
    ext ⟨r,c⟩
    change (∃ i ∈ List.finRange d,
      (∀ l, row r = some l → i ∈ code l) ∧ (∀ l, col c = some l → i ∉ code l)) ↔ _
    constructor
    · rintro ⟨i, _, hr, hc⟩ ⟨l, er, ec⟩
      exact hc l ec (hr l er)
    · intro noEdge
      cases hr : row r with
      | none =>
        cases hc : col c with
        | none =>
          have index : Fin d := ⟨0, by omega⟩
          exact ⟨index, List.mem_finRange _, by simp⟩
        | some v =>
          have small : (code v).card < (Finset.univ : Finset (Fin d)).card := by simpa [weight]
          obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card small
          exact ⟨i, List.mem_finRange _, by simpa [hr,hc] using hi⟩
      | some u =>
        cases hc : col c with
        | none =>
          obtain ⟨i,hi⟩ := Finset.card_pos.mp ((weight u).symm ▸ positive)
          exact ⟨i, List.mem_finRange _, by simpa [hr,hc] using hi⟩
        | some v =>
          have ne : u ≠ v := by rintro rfl; exact noEdge ⟨u,hr,hc⟩
          obtain ⟨i, hu, hv⟩ := diff u v ne
          exact ⟨i, List.mem_finRange _, by simpa [hr,hc] using And.intro hu hv⟩
  rw [← represent]
  have hn : List.finRange d ≠ [] := by
    intro e
    have := congrArg List.length e
    simp at this
    omega
  simpa using union_formula rect (fun i => ⟨a i,b i,rfl⟩) _ hn

theorem two_layers {X Y : Type*} {m d h : Nat} (positive : 0 < h) (proper : h < d)
    (capacity : m ≤ d.choose h) (r₀ r₁ : X → Option (Fin m)) (c₀ c₁ : Y → Option (Fin m)) :
    Formula Rectangle (2*(d-1)) (mismatch r₀ c₀ ∩ mismatch r₁ c₁) := by
  simpa [two_mul] using Formula.meet (layer_formula positive proper capacity r₀ c₀)
    (layer_formula positive proper capacity r₁ c₁)

#print axioms ForestMatching.two_layers
end ForestMatching
