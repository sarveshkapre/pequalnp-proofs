import PEqualNP.SharingRank.Formula
import PEqualNP.SharingRank.Witness

namespace SharingRank.Formulas.Expr
open Set
variable {X Y : Type}

private theorem cost_zero (e : Expr X Y) (h : e.cost = 0) :
    ∃ (r : Set X) (c : Set Y), ∀ x y, e.cell x y ↔ x ∈ r ∧ y ∈ c := by
  induction e with
  | rect r c => exact ⟨r,c,fun _ _ => Iff.rfl⟩
  | meet e f he hf =>
    obtain ⟨r,c,h1⟩ := he (by simpa [cost] using (Nat.add_eq_zero_iff.mp h).1)
    obtain ⟨s,t,h2⟩ := hf (Nat.add_eq_zero_iff.mp h).2
    exact ⟨r ∩ s,c ∩ t,fun x y => by simp only [cell,h1,h2,Set.mem_inter_iff]; tauto⟩
  | join e f _ _ => simp [cost] at h

/-- Flattening a formula gives one rectangle clip and one pair of rectangles per paid gate. -/
theorem flat_form (e : Expr X Y) (h : e.Flat) :
    ∃ (r : Set X) (c : Set Y) (a b : Fin e.cost → Set X) (s u : Fin e.cost → Set Y),
      ∀ x y, e.cell x y ↔ x ∈ r ∧ y ∈ c ∧
        ∀ i, (x ∈ a i ∧ y ∈ s i) ∨ (x ∈ b i ∧ y ∈ u i) := by
  induction e with
  | rect r c =>
    exact ⟨r,c,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,fun x y => by simp [cost,cell]⟩
  | meet e f he hf =>
    obtain ⟨r,c,a,b,s,u,h1⟩ := he h.1
    obtain ⟨r',c',a',b',s',u',h2⟩ := hf h.2
    refine ⟨r ∩ r',c ∩ c',Fin.append a a',Fin.append b b',Fin.append s s',Fin.append u u',?_⟩
    intro x y
    simp only [cell,h1,h2,Set.mem_inter_iff,cost,Fin.forall_fin_add,Fin.append_left,Fin.append_right]
    tauto
  | join e f _ _ =>
    obtain ⟨r,c,h1⟩ := cost_zero e h.1
    obtain ⟨s,t,h2⟩ := cost_zero f h.2
    refine ⟨univ,univ,fun _ => r,fun _ => s,fun _ => c,fun _ => t,?_⟩
    intro x y
    simp [cell,h1,h2,cost]

theorem witness_flat_cost {t : Nat} (e : Expr (Witness.Word t) (Witness.Word t))
    (h : e.Flat) (rep : ∀ x y, e.cell x y ↔ Witness.zero x y) : t+4 ≤ e.cost := by
  obtain ⟨r,c,a,b,s,u,h1⟩ := flat_form e h
  have bound := Witness.flat_bound Witness.zero Witness.row Witness.col Witness.anchor Witness.anchor
    Witness.anchors Witness.missing Witness.crossed r c a b s u
    (fun x y => (rep x y).symm.trans (h1 x y))
  simp [Witness.Index,Fintype.card_sum,Fintype.card_prod] at bound
  omega
end SharingRank.Formulas.Expr
