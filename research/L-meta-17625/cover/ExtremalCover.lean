import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity.NestedCover

namespace ExtremalCover

/-- If every center and one endpoint of every residual edge are necessary in a
cover, all endpoint transversals extend to independent sets hitting every top's
opposite port. The number of residual edges is arbitrary. -/
theorem transversals {n k : ℕ} {I : Type*} [Fintype I] (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z : I → Fin n) (L : I → Finset (Fin n))
    (ends : Fin k → Bool → Fin n) (pairAdj : ∀ i, G.Adj (ends i false) (ends i true))
    (routes : ∀ u v, G.Adj u v →
      (∃ a, (u = z a ∧ v ∈ L a) ∨ (v = z a ∧ u ∈ L a)) ∨
      ∃ i, s(u,v) = s(ends i false, ends i true))
    (lower : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set _) → Fintype.card I + k ≤ K.card) :
    (∀ i a, z a ≠ ends i false ∧ z a ≠ ends i true) ∧
    ∃ neg : (Fin k → Bool) → Fin n → Bool,
      (∀ b, graphFun G ∅ (neg b) = false) ∧
      (∀ b i, neg b (ends i (b i)) = true) ∧
      ∀ a b, ∃ w ∈ L a, neg b w = true := by
  classical
  let slots (b : Fin k → Bool) : I ⊕ Fin k → Fin n := Sum.elim z (fun i => ends i (b i))
  let K (b : Fin k → Bool) := Finset.univ.image (slots b)
  have slot_mem (b) (i : I ⊕ Fin k) : slots b i ∈ K b :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have covers (b) : G.IsVertexCover (K b : Set _) := by
    intro u v adj
    rcases routes u v adj with ⟨a, ⟨rfl,_⟩ | ⟨rfl,_⟩⟩ | ⟨i,eq⟩
    · exact Or.inl (slot_mem b (.inl a))
    · exact Or.inr (slot_mem b (.inl a))
    · have h : ends i (b i) ∈ K b := slot_mem b (.inr i)
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases hb : b i <;> simp_all
  have full (b) : (K b).card = Fintype.card I + k := by
    refine le_antisymm ?_ (lower _ (covers b))
    exact (Finset.card_image_le : (K b).card ≤ (Finset.univ : Finset (I ⊕ Fin k)).card).trans_eq (by simp)
  have inj (b : Fin k → Bool) : Function.Injective (slots b) := by
    have eq : (K b).card = (Finset.univ : Finset (I ⊕ Fin k)).card := by rw [full]; simp
    exact fun x y h => (Finset.injOn_of_card_image_eq eq) (Finset.mem_univ x) (Finset.mem_univ y) h
  have sep (i : Fin k) (a : I) (v : Bool) : z a ≠ ends i v := by
    intro h
    have eq := @inj (fun _ => v) (.inl a) (.inr i) h
    cases eq
  have inz : Function.Injective z := by
    intro a b h
    exact Sum.inl.inj (@inj (fun _ => false) (.inl a) (.inl b) h)
  have indep (i j : Fin k) (ne : i ≠ j) (s t : Bool) : ends i s ≠ ends j t := by
    intro eq
    let mask := fun x : Fin k => if x = i then s else t
    apply ne
    apply Sum.inr.inj
    apply inj mask
    simpa [slots, mask, ne.symm] using eq
  refine ⟨fun i a => ⟨sep i a false, sep i a true⟩, fun b v => decide (v ∉ K (fun i => !(b i))), ?_, ?_, ?_⟩
  · intro b
    apply Bool.eq_false_iff.mpr
    intro on
    simp [graphFun] at on
    obtain ⟨u,v,uv,hu,hv⟩ := on
    exact (covers (fun i => !(b i)) uv).elim hu hv
  · intro b i
    apply decide_eq_true
    intro he
    obtain ⟨a,_,eq⟩ := Finset.mem_image.mp he
    rcases a with a | j
    · exact sep i a _ eq
    · change ends j (!(b j)) = ends i (b i) at eq
      by_cases ij : j = i
      · subst j
        cases hb : b i <;> simp [hb] at eq
        · exact (pairAdj i).ne eq.symm
        · exact (pairAdj i).ne eq
      · exact indep j i ij _ _ eq
  · intro a b
    let mask := fun i => !(b i)
    have center : z a ∈ K mask := slot_mem mask (.inl a)
    have privateNbr : ∃ w, G.Adj (z a) w ∧ w ∉ K mask := by
      by_contra! impossible
      have survives : G.IsVertexCover ((K mask).erase (z a) : Finset _) := by
        intro u v adj
        by_cases ha : u = z a
        · subst u
          exact .inr (Finset.mem_erase.mpr ⟨adj.ne.symm, impossible v adj⟩)
        by_cases hv : v = z a
        · subst v
          exact .inl (Finset.mem_erase.mpr ⟨ha, impossible u adj.symm⟩)
        exact (covers mask adj).imp (fun h => Finset.mem_erase.mpr ⟨ha,h⟩)
                                     (fun h => Finset.mem_erase.mpr ⟨hv,h⟩)
      have card := lower _ survives
      rw [Finset.card_erase_of_mem center, full] at card
      have h := Finset.card_pos.mpr (show (K mask).Nonempty from ⟨_,center⟩)
      rw [full] at h
      omega
    obtain ⟨w,adj,hout⟩ := privateNbr
    refine ⟨w, ?_, decide_eq_true hout⟩
    rcases routes (z a) w adj with ⟨c,⟨eq,leaf⟩ | ⟨eq,_⟩⟩ | ⟨i,eq⟩
    · simpa [inz eq] using leaf
    · exact (hout (eq ▸ slot_mem mask (.inl c))).elim
    · rcases Sym2.eq_iff.mp eq with ⟨h,_⟩ | ⟨h,_⟩
      · exact (sep i a false h).elim
      · exact (sep i a true h).elim

#print axioms ExtremalCover.transversals

end ExtremalCover
