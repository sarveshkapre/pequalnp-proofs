import Mathlib.Tactic

namespace PEqualNP.PaidDepth

theorem PrivateReaders :
∀ (k : Nat) (dep : Fin k → Bool → Fin k → Prop)
  (raw : Fin k → Bool → Prop) (need : Fin k → Prop),
  let arm (X : Fin k → Prop) (i : Fin k) (e : Bool) :=
    raw i e ∨ ∃ j, dep i e j ∧ X j
  let reads (v i : Fin k) := ∃ e, dep i e v
  let hit (W : Finset (Fin k)) (i : Fin k) (e : Bool) := ∃ v ∈ W, dep i e v
  let untouched (W : Finset (Fin k)) (i : Fin k) := i ∉ W ∧ ∀ e, ¬ hit W i e
  (∃ X : Fin k → Prop, (∀ i, (∀ e, arm X i e) → X i) ∧ ∀ i, need i → ¬ X i) ↔
    ∃ W : Finset (Fin k),
      (∀ v ∈ W, ∃ i, reads v i ∧ ∀ u ∈ W, reads u i → u = v) ∧
      ∃ Y : Fin k → Prop,
        (∀ i ∈ W, Y i) ∧
        (∀ i e, hit W i e → arm Y i (!e) → Y i) ∧
        (∀ i, untouched W i → (∀ e, raw i e) → Y i) ∧
        (∀ i, untouched W i → ∀ v, reads v i → ¬ Y v) ∧
        ∀ i, need i → ¬ Y i
 := by
  classical
  intro k dep raw need arm reads hit untouched
  constructor
  · rintro ⟨X,closed,miss⟩
    let represents (W : Finset (Fin k)) := (∀ w ∈ W, X w) ∧
      ∀ i v, X v → reads v i → ∃ w ∈ W, reads w i
    let bound (n : Nat) := ∃ W, represents W ∧ W.card = n
    have possible : ∃ n, bound n := by
      let allX := Finset.univ.filter X
      have mem (v) : v ∈ allX ↔ X v := by simp [allX]
      refine ⟨allX.card,allX,⟨fun w hw => (mem w).mp hw,?_⟩,rfl⟩
      exact fun i v hv edge => ⟨v,(mem v).mpr hv,edge⟩
    obtain ⟨W,rep,size⟩ := Nat.find_spec possible
    refine ⟨W,?_,X,rep.1,?_,?_,?_,miss⟩
    · intro v hv
      by_contra missing
      have smaller : represents (W.erase v) := by
        refine ⟨fun w hw => rep.1 w (Finset.mem_of_mem_erase hw),?_⟩
        intro i u hu edge
        obtain ⟨w,hw,readsW⟩ := rep.2 i u hu edge
        by_contra none
        apply missing
        have only (z) (hz : z ∈ W) (e : reads z i) : z = v := by
          by_contra diff
          exact none ⟨z,Finset.mem_erase.mpr ⟨diff,hz⟩,e⟩
        exact ⟨i,only w hw readsW ▸ readsW,only⟩
      have lower := Nat.find_min' possible (show bound (W.erase v).card from ⟨_,smaller,rfl⟩)
      have less := Finset.card_erase_lt_of_mem hv
      omega
    · intro i e hh rest
      obtain ⟨w,hw,edge⟩ := hh
      have active : arm X i e := Or.inr ⟨w,edge,rep.1 w hw⟩
      apply closed i
      intro f
      cases e <;> cases f <;> first | exact active | exact rest
    · exact fun i _ both => closed i (fun e => Or.inl (both e))
    · intro i fresh v edge hv
      obtain ⟨w,hw,f,ew⟩ := rep.2 i v hv edge
      exact fresh.2 f ⟨w,hw,ew⟩
  · rintro ⟨W,_,Y,force,pass,seed,guard,miss⟩
    refine ⟨Y,?_,miss⟩
    intro i both
    by_cases hw : i ∈ W
    · exact force i hw
    by_cases touched : ∃ e, hit W i e
    · obtain ⟨e,he⟩ := touched
      exact pass i e he (both (!e))
    · have fresh : untouched W i := ⟨hw,fun e he => touched ⟨e,he⟩⟩
      apply seed i fresh
      intro e
      rcases both e with h | ⟨v,edge,hv⟩
      · exact h
      · exact (guard i fresh v ⟨e,edge⟩ hv).elim

end PEqualNP.PaidDepth
