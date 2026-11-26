import GeneralThree

namespace PathGeometry
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

/-- The two omitted positions in each negative input. The corresponding
selected path vertices are (0,2), (0,3), and (1,3) respectively. -/
def cut : Fin 3 → Fin 2 → Fin 4 := ![![1,3],![1,2],![0,2]]
def kept (i : Fin 3) (j : Fin 4) : Bool := decide (∀ k, cut i k ≠ j)

theorem hits_path : ∀ (i : Fin 3) (j : Fin 3),
    ∃ k, cut i k = j.castSucc ∨ cut i k = j.succ := by decide

theorem position_occurs : ∀ j : Fin 4, ∃ i k, cut i k = j := by decide

def pathEdges {n} (e : Fin 4 → Fin n) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image (fun j : Fin 3 => s(e j.castSucc,e j.succ))

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The retained neighbors of any vertex outside an induced three-edge path
can contain at most one path vertex. -/
theorem sparse_neighbors (four : NoFourCycle G) (bip : G.IsBipartite)
    (e : Fin 4 → Fin n) (einj : Function.Injective e)
    (edges : ∀ j : Fin 3, G.Adj (e j.castSucc) (e j.succ))
    (x : Fin n) (outside : ∀ i, x ≠ e i) :
    ∀ i j, G.Adj x (e i) → G.Adj x (e j) → i = j := by
  have e01 : G.Adj (e 0) (e 1) := edges 0
  have e12 : G.Adj (e 1) (e 2) := edges 1
  have e23 : G.Adj (e 2) (e 3) := edges 2
  have shared (v : Fin 4) {p q : Fin 4} (pq : p ≠ q) (vp : G.Adj (e v) (e p)) (vq : G.Adj (e v) (e q))
      (xp : G.Adj x (e p)) (xq : G.Adj x (e q)) : False :=
    pq (einj (Finset.card_le_one.mp (four x (e v) (outside v)) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xp,vp⟩)
      _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xq,vq⟩)))
  obtain ⟨color⟩ := bip
  have d01 := color.valid e01
  have d12 := color.valid e12
  have d23 := color.valid e23
  intro i j hi hj
  have monochrome {r s : Fin 4} (rx : G.Adj x (e r)) (sx : G.Adj x (e s)) : color (e r) = color (e s) := by
    have rne := color.valid rx; have sne := color.valid sx; omega
  have d03 : color (e 0) ≠ color (e 3) := by omega
  have e01x (h : G.Adj x (e 0)) (k : G.Adj x (e 1)) := d01 (monochrome h k)
  have e12x (h : G.Adj x (e 1)) (k : G.Adj x (e 2)) := d12 (monochrome h k)
  have e23x (h : G.Adj x (e 2)) (k : G.Adj x (e 3)) := d23 (monochrome h k)
  have e03x (h : G.Adj x (e 0)) (k : G.Adj x (e 3)) := d03 (monochrome h k)
  have s02 : G.Adj x (e 0) → G.Adj x (e 2) → False := shared 1 (by decide) e01.symm e12
  have s13 : G.Adj x (e 1) → G.Adj x (e 3) → False := shared 2 (by decide) e12.symm e23
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (s02 hi hj).elim | exact (s02 hj hi).elim | exact (s13 hi hj).elim | exact (s13 hj hi).elim | exact (e01x hi hj).elim | exact (e01x hj hi).elim | exact (e12x hi hj).elim | exact (e12x hj hi).elim | exact (e23x hi hj).elim | exact (e23x hj hi).elim | exact (e03x hi hj).elim | exact (e03x hj hi).elim

structure Witness {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : Fin 4 → Fin n) where
  b : tops G C → Fin 2
  z : tops G C → Fin n
  neg : Fin 3 → Fin n → Bool
  raw : ∀ a : tops G C, side (n := n) C a (b a) = {z a}
  outside : ∀ a j, z a ≠ e j
  inj : Function.Injective z
  noEdge : ∀ i, graphFun G ∅ (neg i) = false
  bits : ∀ i j, neg i (e j) = kept i j
  leaf : ∀ a : tops G C, ∀ i, ∃ w ∈ side (n := n) C a (1-b a), neg i w = true
  thin : ∀ a : tops G C, ∀ p : Fin 2, (Finset.univ.filter (fun j : Fin 4 => e j ∈ side (n := n) C a p)).card ≤ 1
  positive : ∀ j : Fin 3, G.Adj (e j.castSucc) (e j.succ)

theorem witness (four : NoFourCycle G) (bip : G.IsBipartite) (nonempty : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (injF : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (failure : ¬ GeneralThree.wireBound G C S)
    (e : Fin 4 → Fin n) (einj : Function.Injective e) (path : Ustar G C = pathEdges e) :
    Nonempty (Witness G C e) := by
  classical
  obtain ⟨_,zero,_,_⟩ := GeneralThree.remaining G C four nonempty least top three S f injF partners failure
  have tight := (GeneralThree.tight_if_failed G C four nonempty least top three S f injF partners failure).1
  obtain ⟨b,z,raw,serve⟩ := topIndexedStars four least.1 (Finset.card_eq_zero.mp zero)
  let slots (i : Fin 3) : tops G C ⊕ Fin 2 → Fin n := Sum.elim z (fun j => e (cut i j))
  let K (i : Fin 3) := Finset.univ.image (slots i)
  have mem (i) (j : tops G C ⊕ Fin 2) : slots i j ∈ K i := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have inPath (j : Fin 3) : s(e j.castSucc,e j.succ) ∈ Ustar G C := by
    rw [path]; exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have edge (j : Fin 3) : G.Adj (e j.castSucc) (e j.succ) :=
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (inPath j)).1
  have eqEnds {u v : Fin n} (h : s(u,v) ∈ Ustar G C) :
      ∃ j : Fin 3, (u = e j.castSucc ∧ v = e j.succ) ∨ (u = e j.succ ∧ v = e j.castSucc) := by
    rw [path] at h
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp h
    exact ⟨j,Sym2.eq_iff.mp eq.symm⟩
  have covers (i) : G.IsVertexCover (K i : Set _) := by
    intro u v adj
    by_cases residual : s(u,v) ∈ Ustar G C
    · obtain ⟨j,eq⟩ := eqEnds residual
      obtain ⟨k,hk⟩ := hits_path i j
      have supplied : e (cut i k) ∈ K i := mem i (.inr k)
      rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases hk with hk|hk <;> rw [hk] at supplied <;>
        first | exact Or.inl supplied | exact Or.inr supplied
    · obtain ⟨a,⟨rfl,_⟩|⟨rfl,_⟩⟩ := serve u v (SimpleGraph.deleteEdges_adj.mpr ⟨adj,residual⟩)
      · exact Or.inl (mem i (.inl a))
      · exact Or.inr (mem i (.inl a))
  have lower (T : Finset (Fin n)) (cov : G.IsVertexCover (T : Set _)) : (tops G C).card + 2 ≤ T.card := by
    rw [←tight]; exact ResidualDegree.matched_le_cover G S f injF partners _ cov
  have card (i) : (K i).card = (tops G C).card + 2 :=
    le_antisymm (Finset.card_image_le.trans_eq (by simp)) (lower _ (covers i))
  have cinj (i) : Function.Injective (slots i) := by
    have eq : (Finset.univ.image (slots i)).card = (Finset.univ : Finset (tops G C ⊕ Fin 2)).card := by
      change (K i).card = _; rw [card]; simp
    exact fun _ _ h => Finset.injOn_of_card_image_eq eq (Finset.mem_univ _) (Finset.mem_univ _) h
  have zinj : Function.Injective z := fun a c h => Sum.inl.inj (@cinj 0 (.inl a) (.inl c) h)
  have outside (a : tops G C) (j) : z a ≠ e j := by
    obtain ⟨i,k,h⟩ := position_occurs j; subst j
    intro eq
    have bad := @cinj i (.inl a) (.inr k) eq
    cases bad
  let neg (i : Fin 3) (v : Fin n) := decide (v ∉ K i)
  have noEdge (i) : graphFun G ∅ (neg i) = false := by
    apply Bool.eq_false_iff.mpr; intro on
    simp [graphFun] at on
    obtain ⟨u,v,uv,hu,hv⟩ := on
    have outu : u ∉ K i := by simpa [neg] using hu
    have outv : v ∉ K i := by simpa [neg] using hv
    exact (covers i uv).elim outu outv
  have bits (i j) : neg i (e j) = kept i j := by
    apply Bool.eq_iff_iff.mpr
    simp only [neg,kept,decide_eq_true_eq]
    constructor
    · intro out k eq; exact out (eq ▸ mem i (.inr k))
    · intro avoid h
      obtain ⟨a,_,eq⟩ := Finset.mem_image.mp h
      rcases a with a|k
      · exact outside a j eq
      · exact avoid k (einj eq)
  have leaf (a : tops G C) (i : Fin 3) : ∃ w ∈ side (n := n) C a (1-b a), neg i w = true := by
    have priv : ∃ w, G.Adj (z a) w ∧ w ∉ K i := by
      by_contra! all
      have erased : G.IsVertexCover (((K i).erase (z a)) : Finset _) := by
        intro u v adj
        by_cases hu : u = z a
        · subst u; exact Or.inr (Finset.mem_erase.mpr ⟨adj.ne.symm,all v adj⟩)
        by_cases hv : v = z a
        · subst v; exact Or.inl (Finset.mem_erase.mpr ⟨adj.ne,all u adj.symm⟩)
        exact (covers i adj).imp (fun m => Finset.mem_erase.mpr ⟨hu,m⟩) (fun m => Finset.mem_erase.mpr ⟨hv,m⟩)
      have bad := lower _ erased
      rw [Finset.card_erase_of_mem (show z a ∈ K i from mem i (.inl a)),card] at bad
      omega
    obtain ⟨w,adj,out⟩ := priv
    have old : s(z a,w) ∉ Ustar G C := by
      intro m
      obtain ⟨j,⟨eq,_⟩|⟨eq,_⟩⟩ := eqEnds m
      · exact outside a j.castSucc eq
      · exact outside a j.succ eq
    obtain ⟨c,⟨eq,l⟩|⟨eq,_⟩⟩ := serve _ _ (SimpleGraph.deleteEdges_adj.mpr ⟨adj,old⟩)
    · exact ⟨w,(zinj eq).symm ▸ l,decide_eq_true out⟩
    · exact (out (eq ▸ mem i (.inl c))).elim
  refine ⟨⟨b,z,neg,raw,outside,zinj,noEdge,bits,leaf,?_,edge⟩⟩
  intro a p
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have mi := (Finset.mem_filter.mp hi).2
  have mj := (Finset.mem_filter.mp hj).2
  rcases opposite (b a) p with rfl|rfl
  · rw [raw a, Finset.mem_singleton] at mi mj
    exact einj (mi.trans mj.symm)
  · have center : z a ∈ side (n := n) C a (b a) := by rw [raw]; simp
    apply sparse_neighbors four bip e einj edge _ (outside a) i j
    · exact (SimpleGraph.deleteEdges_adj.mp (cleanAdj least.1 a.2 (b a) center mi)).1
    · exact (SimpleGraph.deleteEdges_adj.mp (cleanAdj least.1 a.2 (b a) center mj)).1

#print axioms witness
end PathGeometry
