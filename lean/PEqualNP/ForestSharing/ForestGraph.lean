import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace ForestTree
open SimpleGraph
abbrev Vertex := Fin 7 ⊕ Fin 7

/-- Vertices on the same side are never adjacent. -/
def adjacent (edge : Fin 7 → Fin 7 → Bool) : Vertex → Vertex → Bool
  | .inl r, .inr c => edge r c
  | .inr c, .inl r => edge r c
  | _, _ => false

def graphOf (edge : Fin 7 → Fin 7 → Bool) : SimpleGraph Vertex where
  Adj u v := adjacent edge u v = true
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro v; cases v <;> simp [adjacent]⟩

instance (edge : Fin 7 → Fin 7 → Bool) : DecidableRel (graphOf edge).Adj :=
  fun x y => inferInstanceAs (Decidable (adjacent edge x y = true))

def matrixEdge (r c : Fin 7) : Bool :=
  !((![117,109,106,62,126,79,119] : Fin 7 → BitVec 7) r).getLsbD c.val

abbrev G := graphOf matrixEdge

private theorem connected : G.Connected := by
  suffices h : ∀ v, G.Reachable (.inl 2) v from
    ⟨fun u v => (h u).symm.trans (h v)⟩
  have root : G.Reachable (.inl 2) (.inl 2) := .refl _
  have c0 : G.Reachable (.inl 2) (.inr 0) :=
    root.trans (SimpleGraph.Adj.reachable (show G.Adj (.inl 2) (.inr 0) by decide))
  have c2 : G.Reachable (.inl 2) (.inr 2) :=
    root.trans (SimpleGraph.Adj.reachable (show G.Adj (.inl 2) (.inr 2) by decide))
  have c4 : G.Reachable (.inl 2) (.inr 4) :=
    root.trans (SimpleGraph.Adj.reachable (show G.Adj (.inl 2) (.inr 4) by decide))
  have r3 : G.Reachable (.inl 2) (.inl 3) :=
    c0.trans (SimpleGraph.Adj.reachable (show G.Adj (.inr 0) (.inl 3) by decide))
  have r4 : G.Reachable (.inl 2) (.inl 4) :=
    c0.trans (SimpleGraph.Adj.reachable (show G.Adj (.inr 0) (.inl 4) by decide))
  have r1 : G.Reachable (.inl 2) (.inl 1) :=
    c4.trans (SimpleGraph.Adj.reachable (show G.Adj (.inr 4) (.inl 1) by decide))
  have r5 : G.Reachable (.inl 2) (.inl 5) :=
    c4.trans (SimpleGraph.Adj.reachable (show G.Adj (.inr 4) (.inl 5) by decide))
  have c6 : G.Reachable (.inl 2) (.inr 6) :=
    r3.trans (SimpleGraph.Adj.reachable (show G.Adj (.inl 3) (.inr 6) by decide))
  have c1 : G.Reachable (.inl 2) (.inr 1) :=
    r1.trans (SimpleGraph.Adj.reachable (show G.Adj (.inl 1) (.inr 1) by decide))
  have c5 : G.Reachable (.inl 2) (.inr 5) :=
    r5.trans (SimpleGraph.Adj.reachable (show G.Adj (.inl 5) (.inr 5) by decide))
  have r0 : G.Reachable (.inl 2) (.inl 0) :=
    c1.trans (SimpleGraph.Adj.reachable (show G.Adj (.inr 1) (.inl 0) by decide))
  have c3 : G.Reachable (.inl 2) (.inr 3) :=
    r0.trans (SimpleGraph.Adj.reachable (show G.Adj (.inl 0) (.inr 3) by decide))
  have r6 : G.Reachable (.inl 2) (.inl 6) :=
    c3.trans (SimpleGraph.Adj.reachable (show G.Adj (.inr 3) (.inl 6) by decide))
  intro v
  rcases v with r | c
  · fin_cases r <;> assumption
  · fin_cases c <;> assumption

theorem isTree : G.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨connected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide +kernel

end ForestTree
