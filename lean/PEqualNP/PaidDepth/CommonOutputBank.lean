import Mathlib.Tactic

namespace PEqualNP.PaidDepth
namespace OutputBank

private abbrev Tile (R C : Type) := (R → Prop) × (C → Prop)
private def hit (t : Tile R C) (x : R) (y : C) := t.1 x ∧ t.2 y
private def meet (a b : Tile R C) : Tile R C := (fun x => a.1 x ∧ b.1 x, fun y => a.2 y ∧ b.2 y)
private theorem hit_meet (a b : Tile R C) (x : R) (y : C) :
    hit (meet a b) x y ↔ hit a x y ∧ hit b x y := by unfold hit meet; tauto

private def covers {I : Type} (b : I → Tile R C) (p : R → C → Prop) :=
  ∀ x y, p x y → ∃ i, hit (b i) x y ∧ ∀ x' y', hit (b i) x' y' → p x' y'

private def strip (r : R → Prop) (c : C → Prop) : Bool → Tile R C
  | false => (r, fun _ => True)
  | true => (fun _ => True, c)

private theorem strip_iff (r : R → Prop) (c : C → Prop) (x : R) (y : C) :
    (r x ∨ c y) ↔ ∃ b, hit (strip r c b) x y := by
  constructor
  · rintro (h|h)
    · exact ⟨false,h,trivial⟩
    · exact ⟨true,trivial,h⟩
  · rintro ⟨b,h⟩
    cases b
    · exact Or.inl h.1
    · exact Or.inr h.2

end OutputBank
open OutputBank

theorem CommonOutputBank :
∀ (s d : Nat) (R C Q : Type)
  (ra : Fin s → Bool → R → Prop) (ca : Fin s → Bool → C → Prop)
  (dep : Fin s → Bool → Fin s → Prop) (wire : Fin s → R → C → Prop)
  (level : Fin s → Nat) (tap : Q → Fin s → Prop),
  (∀ i, level i ≤ d) → (∀ i e j, dep i e j → level j < level i) →
  (∀ i x y, wire i x y ↔ ∀ e, (ra i e x ∨ ca i e y) ∨
    ∃ j, dep i e j ∧ wire j x y) →
  ∃ (rows : Fin ((8*s+1)^(2^d)) → R → Prop)
    (cols : Fin ((8*s+1)^(2^d)) → C → Prop)
    (use : Q → Fin ((8*s+1)^(2^d)) → Prop), ∀ q x y,
    (∃ i, tap q i ∧ wire i x y) ↔ ∃ j, use q j ∧ rows j x ∧ cols j y
 := by
  classical
  intro s d R C Q ra ca dep wire level tap depth earlier gate
  let K := 8*s+1
  let raw (i : Fin s) (e : Bool) := strip (ra i e) (ca i e)
  let arm (i : Fin s) (e : Bool) (x : R) (y : C) :=
    (ra i e x ∨ ca i e y) ∨ ∃ j, dep i e j ∧ wire j x y
  have build : ∀ h : Nat, ∃ bank : Fin (K^(2^h)) → Tile R C,
      (∀ i e b, covers bank (hit (raw i e b))) ∧
      (∀ i, level i ≤ h → covers bank (wire i)) := by
    intro h
    induction h with
    | zero =>
      let Slot := (Fin s × Bool × Bool × Bool) ⊕ Unit
      have card : Fintype.card Slot = K^(2^0) := by simp [Slot,K]; omega
      let num := Fintype.equivFinOfCardEq card
      let tiles : Slot → Tile R C := fun slot => match slot with
        | .inl (i,false,e,b) => raw i e b
        | .inl (i,true,b,c) => meet (raw i false b) (raw i true c)
        | .inr _ => (fun _ => True,fun _ => True)
      refine ⟨fun j => tiles (num.symm j), ?_, ?_⟩
      · intro i e b x y hs
        refine ⟨num (.inl (i,false,e,b)), ?_⟩
        simpa [tiles] using And.intro hs (fun a b' (hh : hit (raw i e b) a b') => hh)
      · intro i hi x y hw
        have choose (e : Bool) : ∃ b, hit (raw i e b) x y := by
          rcases (gate i x y).mp hw e with hr | ⟨j,hj,_⟩
          · exact (strip_iff _ _ _ _).mp hr
          · have := earlier i e j hj
            omega
        obtain ⟨b,hb⟩ := choose false
        obtain ⟨c,hc⟩ := choose true
        refine ⟨num (.inl (i,true,b,c)),?_⟩
        simp only [Equiv.symm_apply_apply]
        change hit (meet _ _) x y ∧ _
        refine ⟨(hit_meet ..).mpr ⟨hb,hc⟩, ?_⟩
        intro x' y' hm
        obtain ⟨l,r⟩ := (hit_meet ..).mp hm
        apply (gate i x' y').mpr
        intro e
        cases e
        · exact Or.inl ((strip_iff ..).mpr ⟨b,l⟩)
        · exact Or.inl ((strip_iff ..).mpr ⟨c,r⟩)
    | succ h ih =>
      obtain ⟨old,rawC,wireC⟩ := ih
      let I := Fin (K^(2^h))
      have card : Fintype.card (I × I) = K^(2^(h+1)) := by
        simp only [I,Fintype.card_prod,Fintype.card_fin,pow_succ,←pow_add]
        congr 1
        omega
      let num := Fintype.equivFinOfCardEq card
      let bank := fun j => meet (old (num.symm j).1) (old (num.symm j).2)
      refine ⟨bank, ?_, ?_⟩
      · intro i e b x y hr
        obtain ⟨z,hz,good⟩ := rawC i e b x y hr
        refine ⟨num (z,z), ?_⟩
        simp only [bank,Equiv.symm_apply_apply,hit_meet]
        exact ⟨⟨hz,hz⟩,fun a b' hh => good a b' hh.1⟩
      · intro i hi x y hw
        have choose (e : Bool) : ∃ z, hit (old z) x y ∧ ∀ a b, hit (old z) a b → arm i e a b := by
          rcases (gate i x y).mp hw e with hr | ⟨j,hj,hv⟩
          · obtain ⟨p,hp⟩ := (strip_iff ..).mp hr
            obtain ⟨z,hz,good⟩ := rawC i e p x y hp
            exact ⟨z,hz,fun a b hh => Or.inl ((strip_iff ..).mpr ⟨p,good a b hh⟩)⟩
          · have prev := earlier i e j hj
            obtain ⟨z,hz,good⟩ := wireC j (by omega) x y hv
            exact ⟨z,hz,fun a b hh => Or.inr ⟨j,hj,good a b hh⟩⟩
        obtain ⟨z,hz,l⟩ := choose false
        obtain ⟨w,hw',r⟩ := choose true
        refine ⟨num (z,w),?_⟩
        simp only [bank,Equiv.symm_apply_apply,hit_meet]
        refine ⟨⟨hz,hw'⟩,?_⟩
        intro a b hh
        apply (gate i a b).mpr
        intro e
        cases e
        · exact l a b hh.1
        · exact r a b hh.2
  obtain ⟨bank,_,wireC⟩ := build d
  let answer (q : Q) (x : R) (y : C) := ∃ i, tap q i ∧ wire i x y
  refine ⟨fun j => (bank j).1,fun j => (bank j).2,
    fun q j => ∀ a b, hit (bank j) a b → answer q a b,?_⟩
  intro q x y
  constructor
  · rintro ⟨i,sel,hw⟩
    obtain ⟨z,hz,good⟩ := wireC i (depth i) x y hw
    exact ⟨z,fun a b hh => ⟨i,sel,good a b hh⟩,hz⟩
  · rintro ⟨z,ok,hr,hc⟩
    exact ok x y ⟨hr,hc⟩

end PEqualNP.PaidDepth
