import PEqualNP.SparseSharing.ForestSimulation
import PEqualNP.SparseSharing.LayerCode

namespace ForestMatching
open TwoIntersections ThreeIntersectionsFormula SparseSharing Set

/-- A bound on the size of any matching, expressed by distinct endpoints on each shore. -/
def MatchingBound {R C : Type*} (edge : R → C → Prop) (m : Nat) : Prop :=
  ∀ (q : Nat) (r : Fin q → R) (c : Fin q → C), Function.Injective r →
    Function.Injective c → (∀ j, edge (r j) (c j)) → q ≤ m

private theorem encode_layer {R C : Type*} [Fintype R] (L : Layer R C)
    (edge : R → C → Prop) (included : ∀ r c, L.edge r c → edge r c)
    {m : Nat} (bound : MatchingBound edge m) :
    ∃ (row : R → Option (Fin m)) (col : C → Option (Fin m)),
      mismatch row col = {p | ¬ L.edge p.1 p.2} := by
  classical
  let allRows := Finset.univ.image fun r : R => (L.row r).getD 0
  let active := allRows.filter fun i => (∃ r, L.row r = some i) ∧ ∃ c, L.col c = some i
  have active_iff (i) : i ∈ active ↔ (∃ r, L.row r = some i) ∧ ∃ c, L.col c = some i := by
    constructor
    · intro h; exact (Finset.mem_filter.mp h).2
    · intro h
      obtain ⟨r,hr⟩ := h.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨r,Finset.mem_univ _,by simp [hr]⟩,h⟩
  let A := ↥active
  let left (i : A) := ((active_iff i.val).mp i.property).1.choose
  let right (i : A) := ((active_iff i.val).mp i.property).2.choose
  have hl (i : A) : L.row (left i) = some i.val :=
    ((active_iff i.val).mp i.property).1.choose_spec
  have hc (i : A) : L.col (right i) = some i.val :=
    ((active_iff i.val).mp i.property).2.choose_spec
  have il : Function.Injective left := fun i j e =>
    Subtype.ext (Option.some.inj ((hl i).symm.trans ((congrArg L.row e).trans (hl j))))
  have ic : Function.Injective right := fun i j e =>
    Subtype.ext (Option.some.inj ((hc i).symm.trans ((congrArg L.col e).trans (hc j))))
  let e := Fintype.equivFin A
  have card : Fintype.card A ≤ m := bound _ (left ∘ e.symm) (right ∘ e.symm)
    (il.comp e.symm.injective) (ic.comp e.symm.injective)
    (fun j => included _ _ ⟨(e.symm j).val, hl _,hc _⟩)
  let code (i : A) : Fin m := (e i).castLE card
  have inj : Function.Injective code := by
    intro i j he; exact e.injective (Fin.ext (congrArg (fun q : Fin m => q.val) he))
  let compress (i : Nat) : Option (Fin m) :=
    if h : i ∈ active then some (code ⟨i,h⟩) else none
  refine ⟨fun r => (L.row r).bind compress, fun c => (L.col c).bind compress, ?_⟩
  ext ⟨r,c⟩
  change (¬ ∃ i, (L.row r).bind compress = some i ∧ (L.col c).bind compress = some i) ↔ _
  apply not_congr
  constructor
  · rintro ⟨j,hr,hk⟩
    cases er : L.row r with
    | none => simp [er] at hr
    | some a =>
      cases ec : L.col c with
      | none => simp [ec] at hk
      | some b =>
        by_cases ha : a ∈ active <;> simp [er,compress,ha] at hr
        by_cases hb : b ∈ active <;> simp [ec,compress,hb] at hk
        have eqv := inj (hr.trans hk.symm)
        exact ⟨a,er,ec.trans (congrArg some (congrArg Subtype.val eqv).symm)⟩
  · rintro ⟨i,hr,hk⟩
    have hi := (active_iff i).mpr ⟨⟨r,hr⟩,⟨c,hk⟩⟩
    exact ⟨code ⟨i,hi⟩, by simp [hr,compress,hi], by simp [hk,compress,hi]⟩

/-- A matching-number bound controls formula cost on every finite bipartite forest. -/
theorem forest_formula {rows cols m d h : Nat} (G : SimpleGraph (Fin rows ⊕ Fin cols))
    (acyclic : G.IsAcyclic) (bound : MatchingBound (fun r c => G.Adj (.inl r) (.inr c)) m)
    (positive : 0 < h) (proper : h < d) (capacity : m ≤ d.choose h) :
    Formula Rectangle (2*(d-1)) {p : Fin rows × Fin cols | ¬ G.Adj (.inl p.1) (.inr p.2)} := by
  obtain ⟨A,B,split⟩ := exists_two_layers G acyclic
  obtain ⟨ra,ca,ea⟩ := encode_layer A _ (fun r c h => (split r c).mp (Or.inl h)) bound
  obtain ⟨rb,cb,eb⟩ := encode_layer B _ (fun r c h => (split r c).mp (Or.inr h)) bound
  have same : mismatch ra ca ∩ mismatch rb cb =
      {p : Fin rows × Fin cols | ¬ G.Adj (.inl p.1) (.inr p.2)} := by
    rw [ea,eb]
    ext ⟨r,c⟩
    change (¬ A.edge r c) ∧ (¬ B.edge r c) ↔ _
    rw [← not_or,split r c]
    rfl
  rw [← same]
  exact two_layers positive proper capacity ra rb ca cb

#print axioms ForestMatching.forest_formula
end ForestMatching
