import FusionCanonical

/- Full fusion covers, with no restriction to canonical semifilters.
The inductive derivation system records upward closure and reuse of previously
derived intersections. Its soundness is independent of a SAT solver. -/
namespace FusionFull

open FusionCanonical

variable {R C X I : Type*}

def FullCover (G : R → C → Prop) (k : ℕ) : Prop :=
  ∃ E H : Fin k → Set (Zero G), ∀ r c, G r c →
    ∀ F : Set (Set (Zero G)), SemiFilter F →
      row G r ∈ F → col G c ∈ F → ∃ i, ¬ Preserves F (E i) (H i)

def Seeds (G : R → C → Prop) (r : R) (c : C) : Set (Set (Zero G)) :=
  {S | S = row G r ∨ S = col G c}

inductive Derivable (S : Set (Set X)) (E H : I → Set X) : Set X → Prop
  | base {T : Set X} : T ∈ S → Derivable S E H T
  | up {T V : Set X} : Derivable S E H T → T ⊆ V → Derivable S E H V
  | inf (i : I) : Derivable S E H (E i) → Derivable S E H (H i) →
      Derivable S E H (E i ∩ H i)

theorem Derivable.mem {S : Set (Set X)} {E H : I → Set X} {T : Set X}
    (hd : Derivable S E H T) {F : Set (Set X)} (hF : SemiFilter F)
    (hS : S ⊆ F) (hp : ∀ i, Preserves F (E i) (H i)) : T ∈ F := by
  induction hd with
  | base h => exact hS h
  | up _ hs ih => exact hF.2.2 _ ih _ hs
  | inf i _ _ ihE ihH => exact hp i ihE ihH

theorem Derivable.step {S : Set (Set X)} {E H : I → Set X} {A B : Set X}
    (i : I) (hA : Derivable S E H A) (hB : Derivable S E H B)
    (hAE : A ⊆ E i) (hBH : B ⊆ H i) : Derivable S E H (E i ∩ H i) :=
  .inf i (.up hA hAE) (.up hB hBH)

theorem full_cover_of_derives {G : R → C → Prop} {k : ℕ}
    (E H : Fin k → Set (Zero G))
    (hd : ∀ r c, G r c → Derivable (Seeds G r c) E H ∅) : FullCover G k := by
  classical
  refine ⟨E,H,?_⟩
  intro r c hrc F hF hr hc
  by_contra hn
  have hp : ∀ i, Preserves F (E i) (H i) := by
    intro i
    by_contra hi
    exact hn ⟨i,hi⟩
  have hS : Seeds G r c ⊆ F := by
    intro T hT
    rcases hT with hT | hT
    · simpa only [hT] using hr
    · simpa only [hT] using hc
  exact hF.2.1 ((hd r c hrc).mem hF hS hp)

#print axioms Derivable.mem
#print axioms full_cover_of_derives

end FusionFull
