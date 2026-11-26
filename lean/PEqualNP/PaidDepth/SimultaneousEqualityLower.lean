import PEqualNP.PaidDepth.CommonOutputBank
import PEqualNP.PaidDepth.OptionalEqualityBank

namespace PEqualNP.PaidDepth

theorem SimultaneousEqualityLower :
∀ (g n s d : Nat),
  let X := Fin g → Fin (n+2)
  let Q := Fin g → Bool
  ∀ (ra : Fin s → Bool → X → Prop) (ca : Fin s → Bool → X → Prop)
    (dep : Fin s → Bool → Fin s → Prop) (wire : Fin s → X → X → Prop)
    (level : Fin s → Nat) (tap : Q → Fin s → Prop)
    (outRow outCol : Q → X → Prop),
    (∀ i, level i ≤ d) → (∀ i e j, dep i e j → level j < level i) →
    (∀ i x y, wire i x y ↔ ∀ e, (ra i e x ∨ ca i e y) ∨
      ∃ j, dep i e j ∧ wire j x y) →
    (∀ q x y, (∀ i, q i = true → x i = y i) ↔
      (outRow q x ∨ outCol q y) ∨ ∃ j, tap q j ∧ wire j x y) →
    (n+3)^g ≤ (8*s+1)^(2^d) + 1 ∧ 2^g ≤ s+1
 := by
  classical
  intro g n s d X Q ra ca dep wire level tap outRow outCol depth earlier gate spec
  let nonempty (q : Q) := ∃ i, q i = true
  have noRaw (q : Q) (hq : nonempty q) (x y : X) : ¬(outRow q x ∨ outCol q y) := by
    obtain ⟨i,hi⟩ := hq
    rintro (hr|hc)
    · have h (b : Fin (n+2)) := (spec q x (fun _ => b)).mpr (Or.inl (Or.inl hr)) i hi
      have bad := (h 0).symm.trans (h 1)
      simp at bad
    · have h (b : Fin (n+2)) := (spec q (fun _ => b) y).mpr (Or.inl (Or.inr hc)) i hi
      have bad := (h 0).trans (h 1).symm
      simp at bad
  constructor
  · obtain ⟨row,col,use,bank⟩ := CommonOutputBank s d X X Q ra ca dep wire level tap depth earlier gate
    let k := (8*s+1)^(2^d)
    let num : Option (Fin k) ≃ Fin (k+1) := Fintype.equivFinOfCardEq (by simp)
    let rows : Option (Fin k) → X → Prop := fun o x => o.elim True (fun j => row j x)
    let cols : Option (Fin k) → X → Prop := fun o y => o.elim True (fun j => col j y)
    let sel : Q → Option (Fin k) → Prop := fun q o => o.elim (¬nonempty q) (use q)
    apply (OptionalEqualityBank g n).2
    refine ⟨fun j => rows (num.symm j),fun j => cols (num.symm j),fun q j => sel q (num.symm j), ?_⟩
    intro q x y
    constructor
    · intro eqOn
      by_cases hq : nonempty q
      · rcases (spec q x y).mp eqOn with raw | hit
        · exact (noRaw q hq x y raw).elim
        obtain ⟨j,hj,r,c⟩ := (bank q x y).mp hit
        exact ⟨num (some j),by simpa [sel,rows,cols] using And.intro hj (And.intro r c)⟩
      · exact ⟨num none,by simp [sel,rows,cols,hq]⟩
    · rintro ⟨j,hj,r,c⟩
      cases h : num.symm j with
      | none =>
        have empty : ¬nonempty q := by simpa [sel,h] using hj
        intro i hi
        exact (empty ⟨i,hi⟩).elim
      | some z =>
        apply (spec q x y).mpr
        apply Or.inr
        apply (bank q x y).mpr
        exact ⟨z,by simpa [sel,h] using hj,by simpa [rows,h] using r,by simpa [cols,h] using c⟩
  · let left : X := fun _ => 0
    let right (q : Q) : X := fun i => if q i then 0 else 1
    have agrees (q : Q) : ∀ i, q i = true → left i = right q i := by
      intro i hi
      simp [left,right,hi]
    have pick (q : Q) (hq : nonempty q) : ∃ j, tap q j ∧ wire j left (right q) := by
      rcases (spec q left (right q)).mp (agrees q) with raw | hit
      · exact (noRaw q hq _ _ raw).elim
      · exact hit
    let tag (q : Q) : Option (Fin s) := if h : nonempty q then some (pick q h).choose else none
    have contained (q p : Q) (j : Fin s) (sel : tap q j) (hit : wire j left (right p)) :
        ∀ i, q i = true → p i = true := by
      intro i hi
      have eqv := (spec q left (right p)).mpr (Or.inr ⟨j,sel,hit⟩) i hi
      cases hp : p i with
      | true => rfl
      | false => simp [left,right,hp] at eqv
    have inj : Function.Injective tag := by
      intro q p same
      by_cases hq : nonempty q <;> by_cases hp : nonempty p
      · have idx : (pick q hq).choose = (pick p hp).choose := by simpa [tag,hq,hp] using same
        obtain ⟨sq,wq⟩ := (pick q hq).choose_spec
        obtain ⟨sp,wp⟩ := (pick p hp).choose_spec
        have a := contained q p _ sq (idx.symm ▸ wp)
        have b := contained p q _ sp (idx ▸ wq)
        funext i
        cases h : q i <;> cases h' : p i <;> first
          | rfl
          | exact h.symm.trans (b i h')
          | exact (a i h).symm.trans h'
      · simp [tag,hq,hp] at same
      · simp [tag,hq,hp] at same
      · funext i
        have a : q i ≠ true := fun h => hq ⟨i,h⟩
        have b : p i ≠ true := fun h => hp ⟨i,h⟩
        cases h : q i <;> cases h' : p i <;> first | rfl | exact (a h).elim | exact (b h').elim
    simpa [Q] using Fintype.card_le_of_injective tag inj

end PEqualNP.PaidDepth
