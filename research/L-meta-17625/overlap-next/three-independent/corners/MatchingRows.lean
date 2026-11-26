import PathBits
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace MatchingRows
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : Nat}
def raw (v : Fin 6 → Fin n) (s : Finset (Fin n)) : BitVec 6 :=
  PathBits.pack fun i => decide (v i ∈ s)

def input (v : Fin 6 → Fin n) (r : BitVec 6) (u : Fin n) : Bool :=
  decide (∃ i : Fin 6, v i = u ∧ r.getLsbD i = true)

@[simp] theorem raw_bit (v : Fin 6 → Fin n) (s : Finset (Fin n)) (i : Fin 6) :
    (raw v s).getLsbD i = decide (v i ∈ s) := PathBits.get_pack .. 

@[simp] theorem input_vertex {v : Fin 6 → Fin n} (inj : Function.Injective v) (r : BitVec 6) (i : Fin 6) :
    input v r (v i) = r.getLsbD i := by
  apply Bool.eq_iff_iff.mpr
  simp [input,inj.eq_iff]

theorem raw_sub (v : Fin 6 → Fin n) {s t : Finset (Fin n)} (h : s ⊆ t) :
    raw v s &&& ~~~(raw v t) = 0 := by
  apply PathBits.bit_ext; intro j
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,raw_bit,j.isLt,decide_true,Bool.true_and]
  by_cases hs : v j ∈ s
  · simp [hs,h hs]
  · simp [hs]

theorem raw_union (v : Fin 6 → Fin n) (s t : Finset (Fin n)) :
    raw v (s ∪ t) = raw v s ||| raw v t := by
  apply PathBits.bit_ext; intro i; simp only [BitVec.getLsbD_or,raw_bit,Finset.mem_union]; simp

theorem raw_empty (v : Fin 6 → Fin n) : raw v ∅ = 0 := by
  apply PathBits.bit_ext; intro i; rw [raw_bit]; simp

def bitSubset (a b : BitVec 6) := ∀ i : Fin 6, a.getLsbD i = true → b.getLsbD i = true

theorem subset_iff (a b : BitVec 6) : bitSubset a b ↔ a &&& ~~~b = 0 := by
  constructor
  · intro h; apply PathBits.bit_ext; intro i
    specialize h i
    simp [i.isLt]
    grind
  · intro h i ha
    have e := congrArg (fun m : BitVec 6 => m.getLsbD i) h
    simpa [BitVec.getLsbD_and,BitVec.getLsbD_not,ha,i.isLt] using e

/-- The raw centre and leaf support of a clean top can never include a
residual pair on opposite sides, and its ordinary cross pairs are edges. -/
theorem leaf_spec {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (v : Fin 6 → Fin n) (ao : IsAO2 n C) (a : tops G C) (p : Fin 2)
    (z : Fin n) (single : side (n := n) C a p = {z}) {i j : Fin 6}
    (hi : (raw v (side (n := n) C a p)).getLsbD i = true)
    (hj : (raw v (side (n := n) C a (1-p))).getLsbD j = true) :
    G.Adj (v i) (v j) ∧ s(v i,v j) ∉ Ustar G C := by
  have hz : v i = z := by simpa only [raw_bit,decide_eq_true_eq,single,Finset.mem_singleton] using hi
  have mem : v i ∈ side (n := n) C a p := by simp [single,hz]
  exact SimpleGraph.deleteEdges_adj.mp (cleanAdj ao a.2 p mem (by simpa only [raw_bit,decide_eq_true_eq] using hj))

/-- All raw literals reaching a leaf lie in one colour class. Any two of
them cannot already have another common neighbour, including a neighbour
joined to one of them by a residual edge. -/
theorem leaf_geometry {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (v : Fin 6 → Fin n) (inj : Function.Injective v) (ao : IsAO2 n C)
    (four : NoFourCycle G) (color : G.Coloring (Fin 2)) (a : tops G C) (p : Fin 2)
    (z : Fin n) (single : side (n := n) C a p = {z}) :
    let m := raw v (side (n := n) C a (1-p))
    ∀ i j : Fin 6, m.getLsbD i = true → m.getLsbD j = true →
      color (v i) = color (v j) ∧
      (i ≠ j → ∀ w : Fin n, G.Adj w (v i) → G.Adj w (v j) →
        s(w,v i) ∉ Ustar G C ∧ s(w,v j) ∉ Ustar G C) := by
  dsimp only
  have cm : z ∈ side (n := n) C a p := by simp [single]
  intro i j hi hj
  have zi := SimpleGraph.deleteEdges_adj.mp (cleanAdj ao a.2 p cm (by simpa only [raw_bit,decide_eq_true_eq] using hi))
  have zj := SimpleGraph.deleteEdges_adj.mp (cleanAdj ao a.2 p cm (by simpa only [raw_bit,decide_eq_true_eq] using hj))
  refine ⟨by have := color.valid zi.1; have := color.valid zj.1; omega,?_⟩
  intro ne w wi wj
  have wz : w = z := Finset.card_le_one.mp (four _ _ (inj.ne ne)) w
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,wi.symm,wj.symm⟩) z
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,zi.1.symm,zj.1.symm⟩)
  exact wz ▸ ⟨zi.2,zj.2⟩

/-- The graph function on a supported input depends exactly on the induced
subgraph on those six terminals. -/
theorem edge_on_row (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin 6 → Fin n)
    (r : BitVec 6) : graphFun G ∅ (input v r) = true ↔
      ∃ i j : Fin 6, G.Adj (v i) (v j) ∧ r.getLsbD i = true ∧ r.getLsbD j = true := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
    Bool.false_or,decide_eq_true_eq,input]
  grind

#print axioms leaf_geometry
#print axioms edge_on_row
end MatchingRows
