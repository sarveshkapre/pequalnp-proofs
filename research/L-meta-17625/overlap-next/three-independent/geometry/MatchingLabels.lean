import MatchingPorts

namespace MatchingLabels
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

structure Labels (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) where
  left : Fin 3 → Fin n
  right : Fin 3 → Fin n
  distinct : Function.Injective (fun p : Fin 3 × Bool => if p.2 then right p.1 else left p.1)
  color : G.Coloring (Fin 2)
  leftColor : ∀ i, color (left i) = 0
  rightColor : ∀ i, color (right i) = 1
  diagonal : ∀ i, s(left i,right i) ∈ Ustar G C
  residual : ∀ q, q ∈ Ustar G C ↔ ∃ i, q = s(left i,right i)
  port : tops G C → Fin 2
  center : tops G C → Fin n
  raw : ∀ t : tops G C, side (n := n) C t (port t) = {center t}
  serves : ∀ u v, (G.deleteEdges ↑(Ustar G C)).Adj u v → ∃ t,
    (u = center t ∧ v ∈ side (n := n) C t (1-port t)) ∨
    (v = center t ∧ u ∈ side (n := n) C t (1-port t))
  avoid : ∀ t i, i ≠ 2 → center t ≠ left i ∧ center t ≠ right i

private theorem orient (color : G.Coloring (Fin 2)) {q : Sym2 (Fin n)}
    (member : q ∈ Ustar G C) :
    ∃ l r, q = s(l,r) ∧ color l = 0 ∧ color r = 1 := by
  induction q using Sym2.ind with
  | h u v =>
    have adj := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp member).1
    have distinct : color u ≠ color v := color.valid adj
    by_cases hu : color u = 0
    · exact ⟨u,v,rfl,hu,by omega⟩
    · exact ⟨v,u,Sym2.eq_swap,by omega,by omega⟩

theorem of_failure (four : NoFourCycle G) (bip : G.IsBipartite) (nonempty : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (disjoint : ∀ {q r : Sym2 (Fin n)}, q ∈ Ustar G C → r ∈ Ustar G C → q ≠ r →
      ∀ x : Fin n, x ∈ q → x ∉ r)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (failure : ¬ GeneralThree.wireBound G C S) :
    Nonempty (Labels G C) := by
  classical
  obtain ⟨_,zero,_,_⟩ := GeneralThree.remaining G C four nonempty least top three S f inj partners failure
  obtain ⟨p,z,raw,serve⟩ := topIndexedStars four least.1 (Finset.card_eq_zero.mp zero)
  obtain ⟨T,many,promoted⟩ := MatchingPorts.two_promoted G C four nonempty least top three S f inj partners
    failure p z raw (by
      intro u v h; obtain ⟨t,⟨eq,_⟩|⟨eq,_⟩⟩ := serve u v h
      · exact ⟨t,.inl eq⟩
      · exact ⟨t,.inr eq⟩)
  obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  let a := s(i.val,f i)
  let b := s(j.val,f j)
  have ab : a ≠ b := by
    intro eq
    rcases Sym2.eq_iff.mp eq with h|h
    · exact ij (Subtype.ext h.1)
    · exact (partners j).1 (h.1 ▸ i.property)
  have ma : a ∈ Ustar G C := (promoted i hi).1
  have mb : b ∈ Ustar G C := (promoted j hj).1
  have third : ∃ q ∈ Ustar G C, q ≠ a ∧ q ≠ b := by
    by_contra! no
    have sub : Ustar G C ⊆ {a,b} := by
      intro q hq
      by_cases eq : q = a
      · simp [eq]
      · simp [no q hq eq]
    have cnt := Finset.card_le_card sub
    simp [three,ab] at cnt
  obtain ⟨c,mc,ca,cb⟩ := third
  let edge : Fin 3 → Sym2 (Fin n) := ![a,b,c]
  have edist : Function.Injective edge := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all [edge]
  have mem (k : Fin 3) : edge k ∈ Ustar G C := by
    fin_cases k <;> first | exact ma | exact mb | exact mc
  have cover : Finset.univ.image edge = Ustar G C := by
    apply Finset.eq_of_subset_of_card_le
    · intro q h; obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp h; exact mem k
    · rw [Finset.card_image_of_injective _ edist,three]; simp
  obtain ⟨color⟩ := bip
  choose l r eq le ri using fun k => orient color (mem k)
  let x (w : Fin 3 × Bool) := if w.2 then r w.1 else l w.1
  have onEdge (w : Fin 3 × Bool) : x w ∈ edge w.1 := by
    rw [eq]
    rcases w with ⟨k,b⟩; cases b <;> simp [x]
  have dis : Function.Injective x := by
    intro u v h
    have eqi : u.1 = v.1 := by
      by_contra diff
      exact disjoint (mem _) (mem _) (edist.ne diff) _ (onEdge u) (h ▸ onEdge v)
    rcases u with ⟨k,b⟩; rcases v with ⟨j,d⟩
    change k = j at eqi; subst j
    have lr : l k ≠ r k := fun same => by have h := (le k).symm.trans ((congrArg color same).trans (ri k)); omega
    cases b <;> cases d <;> simp_all [x]
  refine ⟨⟨l,r,dis,color,le,ri,(fun k => eq k ▸ mem k),?_,p,z,raw,serve,?_⟩⟩
  · intro q
    rw [←cover, Finset.mem_image]
    constructor
    · rintro ⟨k,_,h⟩; exact ⟨k,h.symm.trans (eq k)⟩
    · rintro ⟨k,h⟩; exact ⟨k,Finset.mem_univ _, (eq k).trans h.symm⟩
  · intro t k hk
    have outside (m : S) (hm : m ∈ T) (edgeEq : edge k = s(m.val,f m)) :
        z t ≠ l k ∧ z t ≠ r k := by
      have avoid := (promoted m hm).2.1 t
      rcases Sym2.eq_iff.mp (edgeEq.symm.trans (eq k)) with h|h <;> grind
    fin_cases k
    · exact outside i hi rfl
    · exact outside j hj rfl
    · exact (hk rfl).elim

#print axioms of_failure
end MatchingLabels
