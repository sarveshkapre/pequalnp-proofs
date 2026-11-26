import PEqualNP.Outside.CircuitCopies
import PEqualNP.Outside.TightFamily

namespace PEqualNP.Outside.OriginalCopyFamily_aux
open PEqualNP.Represents
def seed (r : Fin 3) (c : Fin 4) := (856 : Nat).testBit (4*r.val+c.val)
def original (r : Fin 4) (c : Fin 5) := (101560 : Nat).testBit (5*r.val+c.val)

def rows : Fin 4 → Fin 3 := ![0,1,2,2]
def cols : Fin 5 → Fin 4 := ![0,1,2,3,3]

private theorem transport {M N} (p : Fin M → Fin 3) (q : Fin N → Fin 4)
    (ps : Function.Surjective p) (qs : Function.Surjective q) (k : Nat) :
    RepSizeAtMost (fun r c => seed (p r) (q c)) k ↔
      ∃ j, RepSizeAtMost seed j ∧ j+(M-3)+(N-4) ≤ k :=
  CircuitCopies 3 4 M N seed (by decide) (by decide) (by decide) (by decide) p q ps qs k

private theorem rep {G : Fin 3 → Fin 4 → Bool} {i j} (h : RepSizeAtMost G i) (le : i ≤ j) :
    RepSizeAtMost G j := by
  obtain ⟨circ,arity,size,eval⟩ := h
  exact ⟨circ,arity,size.trans le,eval⟩

private theorem seed_exact : ∀ k, RepSizeAtMost seed k ↔ 7 ≤ k := by
  have rs : ∀ i, ∃ j, rows j = i := by decide
  have cs : ∀ i, ∃ j, cols j = i := by decide
  have map : (fun r c => seed (rows r) (cols c)) = original := by
    funext r c
    exact (by decide : ∀ i j, seed (rows i) (cols j) = original i j) r c
  have t (k) := transport rows cols rs cs k
  simp only [map] at t
  obtain ⟨no,yes⟩ := TightFamily.2 101560 (by decide)
  obtain ⟨m,hm,budget⟩ := (t 9).mp yes
  have hi : RepSizeAtMost seed 7 := rep hm (by omega)
  intro k
  constructor
  · intro h
    by_contra! small
    exact no ((t 8).mpr ⟨k,h,by omega⟩)
  · exact rep hi

theorem family {M N} (p : Fin M → Fin 3) (q : Fin N → Fin 4)
    (ps : Function.Surjective p) (qs : Function.Surjective q) (k : Nat) :
    RepSizeAtMost (fun r c => seed (p r) (q c)) k ↔ M+N ≤ k := by
  have a : 3 ≤ M := by simpa using Fintype.card_le_of_surjective p ps
  have b : 4 ≤ N := by simpa using Fintype.card_le_of_surjective q qs
  rw [transport p q ps qs k]
  constructor
  · rintro ⟨j,h,le⟩
    have := (seed_exact j).mp h
    omega
  · intro h
    exact ⟨7,(seed_exact 7).mpr (by decide),by omega⟩

end PEqualNP.Outside.OriginalCopyFamily_aux

/-- All expansions of the reduced table behind L-meta-20937. -/
theorem PEqualNP.Outside.OriginalCopyFamily :
  ∀ (M N : Nat) (p : Fin M → Fin 3) (q : Fin N → Fin 4),
    Function.Surjective p → Function.Surjective q → ∀ k : Nat,
      PEqualNP.Represents.RepSizeAtMost
        (fun r c => (856 : Nat).testBit (4 * (p r).val + (q c).val)) k ↔ M+N ≤ k := by
  intro M N p q ps qs k
  exact PEqualNP.Outside.OriginalCopyFamily_aux.family p q ps qs k
