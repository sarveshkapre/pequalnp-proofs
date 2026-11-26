import MatchingTransfer

/-! The two-edge path and the separate edge need different port rules from the
three-edge path. These examples test only the graph and its matching. -/
namespace DisconnectedGeometry
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The residual edges are 0–1–2 and 4–5. Vertex 3 is outside this set.
abbrev residual := edgeGraph 6 [(0,1),(1,2),(4,5)]
abbrev insideCenter := edgeGraph 6 [(0,1),(1,2),(4,5),(2,3)]
abbrev outsideCenter := edgeGraph 6 [(0,1),(1,2),(4,5),(2,3),(3,4)]
abbrev U : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,2),s(4,5)}
abbrev left : Finset (Fin 6) := {0,2,4}
abbrev matchTo (v : Fin 6) : Fin 6 := v + 1

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem minimum_residual_covers : ∀ K : Finset (Fin 6), K.card ≤ 2 →
    (residual.IsVertexCover (K : Set _) ↔ K = {1,4} ∨ K = {1,5}) := by
  unfold SimpleGraph.IsVertexCover
  decide

/-- Both graphs have a three-edge matching. Deleting the residual edges leaves
one star. In one graph its center is residual vertex 2. In the other its
center is outside, but the leaf port can contain residual vertices 2 and 4. -/
theorem tight_examples :
    NoFourCycle insideCenter ∧ NoFourCycle outsideCenter ∧
    (∀ u v, outsideCenter.Adj u v → (u ∈ left) ≠ (v ∈ left)) ∧
    (∀ u v, insideCenter.Adj u v → outsideCenter.Adj u v) ∧
    left.card = 3 ∧ Function.Injective (fun v : left => matchTo v.val) ∧
    (∀ v : left, matchTo v.val ∉ left ∧ insideCenter.Adj v.val (matchTo v.val)) ∧
    (∀ u v, (insideCenter.deleteEdges ↑U).Adj u v ↔
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)) ∧
    (∀ u v, (outsideCenter.deleteEdges ↑U).Adj u v ↔
      (u = 3 ∧ v ∈ ({2,4} : Finset (Fin 6))) ∨ (v = 3 ∧ u ∈ ({2,4} : Finset (Fin 6)))) := by
  decide

/-- Two ANDs, each passed through an OR with an outside raw input (false on
all projected assignments). The resulting disjunction matches every positive
and the two complement-of-minimum-cover tests, but accepts vertex 1 alone. -/
def relaxed (x : Fin 6 → Bool) : Bool :=
  ((x 1 && x 1) || false) || ((x 4 && x 5) || false)

theorem two_tests_insufficient :
    (∀ x : Fin 6 → Bool,
      (((x 0 && x 1) || (x 1 && x 2)) || (x 4 && x 5)) = true → relaxed x = true) ∧
    relaxed (fun i => i ∈ ({0,2,4} : Finset (Fin 6))) = false ∧
    relaxed (fun i => i ∈ ({0,2,5} : Finset (Fin 6))) = false ∧
    relaxed (fun i => i = 1) = true := by decide

/-- In a cover with at most one spare vertex, two vertices with no neighbor
outside the cover must be adjacent. Otherwise both can be removed together. -/
theorem redundant_adjacent {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (K : Finset V) (k : ℕ) (cover : G.IsVertexCover (K : Set _))
    (minimum : ∀ L : Finset V, G.IsVertexCover (L : Set _) → k ≤ L.card)
    (slack : K.card ≤ k+1) {u v : V} (hu : u ∈ K) (hv : v ∈ K) (distinct : u ≠ v)
    (guardU : ∀ x, G.Adj u x → x ∈ K) (guardV : ∀ x, G.Adj v x → x ∈ K) : G.Adj u v := by
  by_contra miss
  let L := (K.erase u).erase v
  have mem {x : V} (hx : x ∈ K) (a : x ≠ u) (b : x ≠ v) : x ∈ L :=
    Finset.mem_erase.mpr ⟨b,Finset.mem_erase.mpr ⟨a,hx⟩⟩
  have still : G.IsVertexCover (L : Set _) := by
    intro x y edge
    by_cases xu : x = u
    · subst x; exact Or.inr (mem (guardU _ edge) edge.ne.symm (fun h => miss (h ▸ edge)))
    by_cases xv : x = v
    · subst x; exact Or.inr (mem (guardV _ edge) (fun h => miss (h ▸ edge.symm)) edge.ne.symm)
    by_cases yu : y = u
    · subst y; exact Or.inl (mem (guardU _ edge.symm) xu xv)
    by_cases yv : y = v
    · subst y; exact Or.inl (mem (guardV _ edge.symm) xu xv)
    exact (cover edge).imp (fun hx => mem hx xu xv) (fun hy => mem hy yu yv)
  have bound := minimum L still
  simp only [L,Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨distinct.symm,hv⟩),
    Finset.card_erase_of_mem hu] at bound
  have two := Finset.one_lt_card.mpr ⟨u,hu,v,hv,distinct⟩
  omega

/-- In a bipartite graph each of the two colors occurs at most once among
vertices without a private neighbor outside this nearly minimum cover. -/
theorem at_most_two_redundant {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (bip : G.IsBipartite) (R K : Finset V) (k : ℕ) (cover : G.IsVertexCover (K : Set _))
    (minimum : ∀ L : Finset V, G.IsVertexCover (L : Set _) → k ≤ L.card)
    (slack : K.card ≤ k+1) (sub : R ⊆ K) (guards : ∀ v ∈ R, ∀ x, G.Adj v x → x ∈ K) :
    R.card ≤ 2 := by
  classical
  obtain ⟨color⟩ := bip
  have inj : Set.InjOn (fun v => color v) (R : Set _) := by
    intro u hu v hv same
    by_contra distinct
    exact color.valid (redundant_adjacent G K k cover minimum slack (sub hu) (sub hv) distinct
      (guards u hu) (guards v hv)) same
  rw [← Finset.card_image_of_injOn inj]
  exact (Finset.card_le_univ _).trans_eq (by simp)

#print axioms at_most_two_redundant
#print axioms tight_examples
end DisconnectedGeometry
