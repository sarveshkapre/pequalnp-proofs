import QuadrangleHandoff
import Lean.Elab.Tactic.Omega

/-! Reused from our earlier certificate proof (published fork commit
931bd355d05b1660f34fa87d3e1082a8fc4f96cf), with only the import path adapted.
No certificate or encoding dependency is imported here.

Padding an existing handoff representation with an unused empty
intersection. This turns the exclusion at three into exclusions at every
smaller gate count without changing pjscruggs's definition. -/
namespace QuadrangleHandoff

/-- Add an unused intersection of two empty unions before all existing gates. -/
theorem Represents.succ {k : Nat} {G : Finset Cell}
    (h : Represents k G) : Represents (k + 1) G := by
  rcases h with ⟨I, A, B, S, back, hand, hout, hgraph⟩
  let I' : Fin (k + 2) → Finset Cell := Fin.cases ∅ I
  let A' : Fin (k + 2) → Fin 2 → Finset (Fin 6) := Fin.cases (fun _ => ∅) A
  let B' : Fin (k + 2) → Fin 2 → Finset (Fin 6) := Fin.cases (fun _ => ∅) B
  let S' : Fin (k + 2) → Fin 2 → Finset (Fin (k + 2)) :=
    Fin.cases (fun _ => ∅) (fun t e => (S t e).image Fin.succ)
  refine ⟨I', A', B', S', ?_, ?_, ?_, ?_⟩
  · intro t
    refine Fin.cases ?_ (fun t => ?_) t
    · intro e r hr
      simp [S'] at hr
    · intro e r hr
      simp only [S', Fin.cases_succ, Finset.mem_image] at hr
      obtain ⟨r, hr, rfl⟩ := hr
      exact Fin.succ_lt_succ_iff.mpr (back t e r hr)
  · intro t
    refine Fin.cases ?_ (fun t => ?_) t
    · intro _ p
      simp [I', A', B', S']
    · intro hne p
      have hne' : t ≠ Fin.last k := by
        intro heq
        apply hne
        simp [heq]
      simpa [I', A', B', S', Finset.exists_mem_image] using hand t hne' p
  · intro p
    rw [← Fin.succ_last k]
    simpa only [I', A', B', S', Fin.cases_succ, Finset.exists_mem_image] using hout p
  · rw [← Fin.succ_last k]
    simpa only [I', Fin.cases_succ] using hgraph

/-- Any representation can be padded to a larger intersection budget. -/
theorem Represents.mono {k l : Nat} {G : Finset Cell}
    (h : Represents k G) (hle : k ≤ l) : Represents l G := by
  induction l, hle using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih.succ

/-- Excluding budget three also excludes every smaller intersection budget. -/
theorem excludes_smaller {G : Finset Cell} (h : ¬ Represents 3 G) :
    ∀ k, k < 4 → ¬ Represents k G := by
  intro k hk hrep
  exact h (hrep.mono (by omega))

#print axioms Represents.succ
#print axioms Represents.mono
#print axioms excludes_smaller
end QuadrangleHandoff
