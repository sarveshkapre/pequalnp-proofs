import PEqualNP.SparseSharing.SparseSharing
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SparseSharing

open Set TwoIntersections ThreeIntersectionsFormula SimpleGraph

private noncomputable def root {V : Type*} (G : SimpleGraph V) (v : V) : V :=
  (G.connectedComponentMk v).out

private noncomputable def previous {V : Type*} (G : SimpleGraph V) (u v : V) : V := by
  classical
  exact if h : G.Reachable u v then h.some.toPath.val.penultimate else v

private theorem parent_or {V : Type*} {G : SimpleGraph V} (ha : G.IsAcyclic)
    {v w : V} (h : G.Adj v w) :
    previous G (root G v) v = w ∨ previous G (root G w) w = v := by
  classical
  have e : root G v = root G w :=
    congrArg (fun x : G.ConnectedComponent => x.out) (ConnectedComponent.connectedComponentMk_eq_of_adj h)
  have hv : G.Reachable (root G v) v := ConnectedComponent.exact (G.connectedComponentMk v).out_eq
  have hw := hv.trans h.reachable
  rw [← e]
  simp only [previous, dite_eq_left hv, dite_eq_left hw]
  by_cases hm : w ∈ hv.some.toPath.val.support
  · exact Or.inl (ha.eq_penultimate_of_adj_end hv.some.toPath.property h hm).symm
  · have hm' := ha.mem_support_of_ne_mem_support_of_adj_of_isPath
         hw.some.toPath.property hv.some.toPath.property h.symm hm
    exact Or.inr (ha.eq_penultimate_of_adj_end hw.some.toPath.property h.symm hm').symm

variable {m n : Nat}
private abbrev BGraph (m n : Nat) := SimpleGraph (Fin m ⊕ Fin n)

private noncomputable def sideLabel {q : Nat} (P : Fin q → Prop) : Option Nat := by
  classical
  exact if h : ∃ i, P i then some h.choose.val else none

private theorem label_iff {q : Nat} {P : Fin q → Prop} (uniq : ∀ i j, P i → P j → i = j)
    (i : Fin q) : sideLabel P = some i.val ↔ P i := by
  classical
  unfold sideLabel
  split
  next h =>
    constructor
    · intro he
      have e : h.choose = i := Fin.ext (Option.some.inj he)
      exact e ▸ h.choose_spec
    · intro hi
      rw [uniq _ i h.choose_spec hi]
  next h => simp_all

private noncomputable def forestLayers (G : BGraph m n) : List (Layer (Fin m) (Fin n)) :=
  [⟨fun r => some r.val, fun c => sideLabel fun r =>
      previous G (root G (.inr c)) (.inr c) = .inl r ∧ G.Adj (.inl r) (.inr c)⟩,
   ⟨fun r => sideLabel fun c =>
      previous G (root G (.inl r)) (.inl r) = .inr c ∧ G.Adj (.inl r) (.inr c),
    fun c => some c.val⟩]

private theorem forest_edges (G : BGraph m n) (ha : G.IsAcyclic) (r : Fin m) (c : Fin n) :
    (∃ L ∈ forestLayers G, L.edge r c) ↔ G.Adj (.inl r) (.inr c) := by
  classical
  have leftUnique : ∀ i j : Fin m,
      (previous G (root G (.inr c)) (.inr c) = .inl i ∧ G.Adj (.inl i) (.inr c)) →
      (previous G (root G (.inr c)) (.inr c) = .inl j ∧ G.Adj (.inl j) (.inr c)) → i = j :=
    fun _ _ hi hj => Sum.inl.inj (hi.1.symm.trans hj.1)
  have rightUnique : ∀ i j : Fin n,
      (previous G (root G (.inl r)) (.inl r) = .inr i ∧ G.Adj (.inl r) (.inr i)) →
      (previous G (root G (.inl r)) (.inl r) = .inr j ∧ G.Adj (.inl r) (.inr j)) → i = j :=
    fun _ _ hi hj => Sum.inr.inj (hi.1.symm.trans hj.1)
  simp [forestLayers, Layer.edge, label_iff leftUnique, label_iff rightUnique]
  exact ⟨fun h => h.elim And.right And.right, fun h =>
    (parent_or ha h).elim (fun p => Or.inr ⟨p,h⟩) (fun p => Or.inl ⟨p,h⟩)⟩

/-- The two layers used by forest simulation, exposed for component-sensitive bounds. -/
theorem exists_two_layers (G : SimpleGraph (Fin m ⊕ Fin n)) (ha : G.IsAcyclic) :
    ∃ A B : Layer (Fin m) (Fin n), ∀ r c,
      A.edge r c ∨ B.edge r c ↔ G.Adj (.inl r) (.inr c) := by
  refine ⟨(forestLayers G)[0]'(by simp [forestLayers]),
    (forestLayers G)[1]'(by simp [forestLayers]), ?_⟩
  intro r c
  simpa [forestLayers] using forest_edges G ha r c

/-- The zero set of the union of the cross edges of these forests. -/
def forestZeros (fs : List (SimpleGraph (Fin m ⊕ Fin n))) : Set (Fin m × Fin n) :=
  {p | ∀ G ∈ fs, ¬ G.Adj (.inl p.1) (.inr p.2)}

/-- An edge cover by a forests suffices for a formula with 2a(4k+1) paid gates. -/
theorem arboricity_simulation (fs : List (SimpleGraph (Fin m ⊕ Fin n)))
    (acyclic : ∀ G ∈ fs, G.IsAcyclic) {k : Nat} (h : Circuit Rectangle k (forestZeros fs)) :
    Formula Rectangle (2 * fs.length * (4*k+1)) (forestZeros fs) := by
  have he : zeros (fs.flatMap forestLayers) = forestZeros fs := by
    ext ⟨r,c⟩
    change (∀ L ∈ fs.flatMap forestLayers, ¬ L.edge r c) ↔ _
    constructor
    · intro hh G hg adj
      obtain ⟨L,hl,edge⟩ := (forest_edges G (acyclic G hg) r c).mpr adj
      exact hh L (List.mem_flatMap.mpr ⟨G,hg,hl⟩) edge
    · intro hh L hl edge
      obtain ⟨G,hg,hl⟩ := List.mem_flatMap.mp hl
      exact hh G hg ((forest_edges G (acyclic G hg) r c).mp ⟨L,hl,edge⟩)
  have hn : ∀ xs : List (BGraph m n), (xs.flatMap forestLayers).length = 2 * xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.flatMap_cons,forestLayers] at *; omega
  rw [← he] at h ⊢
  simpa only [hn] using cover_simulation (fs.flatMap forestLayers) h

/-- Every finite bipartite forest with circuit cost k admits a formula of cost 8k+2. -/
theorem forest_simulation (G : SimpleGraph (Fin m ⊕ Fin n)) (ha : G.IsAcyclic) {k : Nat}
    (h : Circuit Rectangle k {p : Fin m × Fin n | ¬ G.Adj (.inl p.1) (.inr p.2)}) :
    Formula Rectangle (8*k+2) {p : Fin m × Fin n | ¬ G.Adj (.inl p.1) (.inr p.2)} := by
  have e : forestZeros [G] = {p : Fin m × Fin n | ¬ G.Adj (.inl p.1) (.inr p.2)} := by
    ext p
    simp [forestZeros]
  rw [← e] at h ⊢
  have th := arboricity_simulation [G] (by simpa using ha) h
  convert th using 1
  simp
  omega

#print axioms SparseSharing.forest_simulation
#print axioms SparseSharing.arboricity_simulation
end SparseSharing
