import Mathlib.Tactic

/-! A pruned finite enumeration, with completeness for an arbitrary Boolean
    relation. Selecting a head removes incompatible later candidates. No
    symmetry, transitivity, or irreflexivity of the relation is assumed. -/
namespace FusionAntichainEnum

def chooseCompatible {α : Type*} (rel : α → α → Bool) : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | n + 1, a :: xs =>
      (chooseCompatible rel n (xs.filter (rel a))).map (a :: ·) ++
        chooseCompatible rel (n + 1) xs
termination_by _n xs => xs.length
decreasing_by
  all_goals simp_wf
  exact List.length_filter_le _ _

theorem mem_chooseCompatible {α : Type*} (rel : α → α → Bool)
    (n : Nat) (candidates selected : List α) :
    selected ∈ chooseCompatible rel n candidates ↔
      selected.length = n ∧ selected.Sublist candidates ∧
        selected.Pairwise (fun a b => rel a b = true) := by
  cases n with
  | zero =>
    simp [chooseCompatible, List.length_eq_zero_iff]
    rintro rfl
    simp
  | succ n =>
    cases candidates with
    | nil =>
      simp [chooseCompatible]
      intro hlen heq
      subst selected
      simp at hlen
    | cons a xs =>
      rw [chooseCompatible, List.mem_append]
      constructor
      · rintro (h | h)
        · obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp h
          obtain ⟨hlen, hsub, hpair⟩ :=
            (mem_chooseCompatible rel n (xs.filter (rel a)) tail).1 ht
          refine ⟨by simp [hlen], (hsub.trans List.filter_sublist).cons_cons a, ?_⟩
          apply List.pairwise_cons.mpr
          refine ⟨?_, hpair⟩
          intro b hb
          exact (List.mem_filter.mp (hsub.subset hb)).2
        · obtain ⟨hlen, hsub, hpair⟩ :=
            (mem_chooseCompatible rel (n + 1) xs selected).1 h
          exact ⟨hlen, hsub.cons a, hpair⟩
      · rintro ⟨hlen, hsub, hpair⟩
        rcases List.sublist_cons_iff.mp hsub with hs | ⟨tail, rfl, hs⟩
        · exact Or.inr ((mem_chooseCompatible rel (n + 1) xs selected).2
            ⟨hlen, hs, hpair⟩)
        · apply Or.inl
          apply List.mem_map.mpr
          refine ⟨tail, ?_, rfl⟩
          apply (mem_chooseCompatible rel n (xs.filter (rel a)) tail).2
          have hp := List.pairwise_cons.mp hpair
          refine ⟨by simpa using hlen, ?_, hp.2⟩
          have hf := hs.filter (rel a)
          simpa only [List.filter_eq_self.mpr hp.1] using hf
termination_by candidates.length
decreasing_by
  all_goals simp_wf
  all_goals exact List.length_filter_le _ _

theorem chooseCompatible_complete {α : Type*} (rel : α → α → Bool)
    {n : Nat} {candidates selected : List α}
    (hlen : selected.length = n) (hsub : selected.Sublist candidates)
    (hpair : selected.Pairwise (fun a b => rel a b = true)) :
    selected ∈ chooseCompatible rel n candidates :=
  (mem_chooseCompatible rel n candidates selected).2 ⟨hlen, hsub, hpair⟩

theorem chooseCompatible_sound {α : Type*} (rel : α → α → Bool)
    {n : Nat} {candidates selected : List α}
    (h : selected ∈ chooseCompatible rel n candidates) :
    selected.length = n ∧ selected.Sublist candidates ∧
      selected.Pairwise (fun a b => rel a b = true) :=
  (mem_chooseCompatible rel n candidates selected).1 h

#print axioms mem_chooseCompatible
#print axioms chooseCompatible_complete

end FusionAntichainEnum
