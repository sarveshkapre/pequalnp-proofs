import Mathlib.Tactic

namespace PEqualNP.PaidDepth

theorem ReaderCut :
∀ (k r : Nat) (early : Finset (Fin k))
  (dep : Fin k → Bool → Fin k → Prop) (raw : Fin k → Bool → Prop)
  (need : Fin k → Prop),
  (∀ i ∈ early, ∀ e j, dep i e j → j ∈ early) →
  let arm (X : Fin k → Prop) (i : Fin k) (e : Bool) :=
    raw i e ∨ ∃ j, dep i e j ∧ X j
  let hit (W : Finset (Fin k)) (i : Fin k) (e : Bool) :=
    ∃ j ∈ W, dep i e j
  let rejects := ∃ X : Fin k → Prop,
    (∀ i, (∀ e, arm X i e) → X i) ∧ ∀ i, need i → ¬ X i
  let small (T : Finset (Fin k)) :=
    (∀ i ∈ early, (∀ e, arm (fun j => j ∈ T) i e) → i ∈ T) ∧
    (∀ i ∈ T, ¬ need i) ∧ ∃ Y : Fin k → Prop,
      (∀ i, i ∉ early → (∀ e, arm (fun j => if j ∈ early then j ∈ T else Y j) i e) → Y i) ∧
      ∀ i, i ∉ early → need i → ¬ Y i
  let large (W : Finset (Fin k)) := ∃ Y : Fin k → Prop,
    (∀ i ∈ W, Y i) ∧
    (∀ i, i ∉ W → (∀ e, ¬ hit W i e) → (∀ e, arm Y i e) → Y i) ∧
    (∀ i e, hit W i e → arm Y i (!e) → Y i) ∧
    ∀ i, need i → ¬ Y i
  rejects ↔ (∃ T ⊆ early, T.card < r ∧ small T) ∨
    ∃ W ⊆ early, W.card = r ∧ large W
 := by
  classical
  intro k r early dep raw need ordered arm hit rejects small large
  constructor
  · rintro ⟨X,closed,miss⟩
    let T := early.filter X
    have mem (i) : i ∈ T ↔ i ∈ early ∧ X i := Finset.mem_filter
    by_cases few : T.card < r
    · left
      refine ⟨T,Finset.filter_subset _ _,few,?_,?_,X,?_,?_⟩
      · intro i hi both
        apply (mem i).mpr
        refine ⟨hi,closed i (fun e => ?_)⟩
        rcases both e with h | ⟨j,hj,h⟩
        · exact Or.inl h
        · exact Or.inr ⟨j,hj,((mem j).mp h).2⟩
      · intro i hi hn
        exact miss i hn ((mem i).mp hi).2
      · intro i _ both
        apply closed i
        intro e
        rcases both e with h | ⟨j,hj,h⟩
        · exact Or.inl h
        · refine Or.inr ⟨j,hj,?_⟩
          by_cases he : j ∈ early
          · exact ((mem j).mp (by simpa [he] using h)).2
          · simpa [he] using h
      · exact fun i _ => miss i
    · right
      obtain ⟨W,sub,card⟩ := Finset.exists_subset_card_eq (s := T) (by omega : r ≤ T.card)
      refine ⟨W,fun i hi => ((mem i).mp (sub hi)).1,card,X,
        fun i hi => ((mem i).mp (sub hi)).2,fun i _ _ => closed i,?_,miss⟩
      intro i e hh rest
      obtain ⟨j,hj,edge⟩ := hh
      have active : arm X i e := Or.inr ⟨j,edge,((mem j).mp (sub hj)).2⟩
      apply closed i
      intro f
      cases e <;> cases f <;> first | exact active | exact rest
  · rintro (⟨T,sub,_,pre,absent,Y,post,miss⟩ | ⟨W,_,_,Y,force,keep,pass,miss⟩)
    · let X (j : Fin k) := if j ∈ early then j ∈ T else Y j
      refine ⟨X,?_,?_⟩
      · intro i both
        by_cases hi : i ∈ early
        · have inside : i ∈ T := by
            apply pre i hi
            intro e
            rcases both e with h | ⟨j,hj,h⟩
            · exact Or.inl h
            · exact Or.inr ⟨j,hj,by simpa [X,ordered i hi e j hj] using h⟩
          simpa [X,hi] using inside
        · simpa [X,hi] using post i hi both
      · intro i hn hx
        by_cases hi : i ∈ early
        · exact absent i (by simpa [X,hi] using hx) hn
        · exact miss i hi hn (by simpa [X,hi] using hx)
    · refine ⟨Y,?_,miss⟩
      intro i both
      by_cases hw : i ∈ W
      · exact force i hw
      by_cases touched : ∃ e, hit W i e
      · obtain ⟨e,h⟩ := touched
        exact pass i e h (both (!e))
      · exact keep i hw (fun e h => touched ⟨e,h⟩) both

end PEqualNP.PaidDepth
