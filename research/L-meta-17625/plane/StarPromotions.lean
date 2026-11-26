import PEqualNP.Outside.L_meta_7465

namespace StarPromotions
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux
open PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem on_port (ao : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (p : Fin 2) (available : (side (n := n) C a p).Nonempty)
    {x : Fin n → Bool} (on : val C (List.ofFn x) (opnd C a p) = true)
    (quiet : ∀ v ∈ side (n := n) C a p, x v ≠ true) :
    ∃ h ∈ orN G C \ lam G C, (orIn n C (n+h)).Nonempty ∧
      orIn n C (n+h) ⊆ side C a p := by
  have bound := opndBound ao ha p
  rcases (nonemptyPortValue (G := G) ao x _ (by omega) available).mp on with ⟨t,mem,yes⟩ | ⟨h,m,_⟩
  · exact (quiet t mem yes).elim
  · change h ∈ (orN G C \ lam G C).filter _ at m
    obtain ⟨exc,raw,path⟩ := Finset.mem_filter.mp m
    exact ⟨h,exc,raw,fun t mt => reach_mem_orIn t
      ((orReaches_reach h _ path).1.trans (mem_orIn_reach t mt))⟩

set_option maxHeartbeats 1500000 in
/-- For a star of unserved incidences, two exceptional ORs cannot afford one
whose raw literals contain two different neighbors of the common vertex.
Each ordinary star serves at most one neighboring input on its leaf side. -/
theorem raw_neighbors_le_one (least : IsLeastAO G C)
    (budget : (orN G C \ lam G C).card ≤ 2)
    (v : Fin n) (L : Finset (Fin n)) (two : 2 ≤ L.card) (adj : ∀ l ∈ L, G.Adj v l)
    (port : tops G C → Fin 2) (z : tops G C → Fin n) (unique : Function.Injective z)
    (one : ∀ a : tops G C, side (n := n) C a (port a) = {z a})
    (nonempty : ∀ a : tops G C, (side (n := n) C a (1-port a)).Nonempty)
    (centerAway : ∀ a, z a ≠ v ∧ z a ∉ L)
    (leafAway : ∀ a : tops G C, v ∉ side (n := n) C a (1-port a) ∧ z a ∉ side C a (1-port a))
    (thin : ∀ a : tops G C, (side (n := n) C a (1-port a) ∩ L).card ≤ 1) :
    ∀ h ∈ orN G C \ lam G C, (orIn n C (n+h) ∩ L).card ≤ 1 := by
  classical
  let B := orN G C \ lam G C
  let R (h : ℕ) := orIn n C (n+h)
  let leaf (a : tops G C) := side (n := n) C a (1-port a)
  intro bad hbad
  by_contra! large
  have few : (B.erase bad).card ≤ 1 := by
    have taken := Finset.card_erase_add_one (s := B) hbad
    change B.card ≤ 2 at budget
    omega
  have single {h g : ℕ} (hh : h ∈ B) (hg : g ∈ B) (hnb : h ≠ bad) (gnb : g ≠ bad) : h = g :=
    Finset.card_le_one.mp few _ (Finset.mem_erase.mpr ⟨hnb,hh⟩) _ (Finset.mem_erase.mpr ⟨gnb,hg⟩)
  have cannot {T : Finset (Fin n)} (small : (T ∩ L).card ≤ 1) : ¬ R bad ⊆ T := by
    intro sub
    change (R bad ∩ L).card > 1 at large
    have inc : R bad ∩ L ⊆ T ∩ L := fun x m =>
      Finset.mem_inter.mpr ⟨sub (Finset.mem_inter.mp m).1,(Finset.mem_inter.mp m).2⟩
    exact (Nat.not_le_of_lt large) ((Finset.card_le_card inc).trans small)
  have centerOn {l : Fin n} (mem : l ∈ L) (a : tops G C)
      (fired : gateVal n C a (pairInput v l) = true) :
      ∃ h ∈ B, h ≠ bad ∧ (R h).Nonempty ∧ R h ⊆ {z a} := by
    have info := topData a.2
    have on := (andValOperands least.1 info.1 info.2.1 _).mp fired (port a)
    obtain ⟨h,hm,ne,sub⟩ := on_port (G := G) least.1 info.1 (port a)
      (by rw [one a]; exact Finset.singleton_nonempty _) on (by
        intro t mt xt
        have same : t = z a := by simpa [one a] using mt
        rw [same] at xt
        rcases (pairInput_true _ _ _).mp xt with eq | eq
        · exact (centerAway a).1 eq
        · exact (centerAway a).2 (eq ▸ mem))
    rw [one a] at sub
    refine ⟨h,hm,?_,ne,sub⟩
    rintro rfl
    exact cannot ((Finset.card_le_card Finset.inter_subset_left).trans (Finset.card_singleton _).le) sub
  obtain ⟨l,ml⟩ := Finset.card_pos.mp (show 0 < L.card by omega)
  obtain ⟨a,ma,on⟩ := acceptedTop least (adj l ml)
  let star : tops G C := ⟨a,ma⟩
  obtain ⟨g,mg,gnb,nonzero,sg⟩ := centerOn ml star on
  obtain ⟨raw,mraw⟩ := nonzero
  have rawEq : raw = z star := Finset.mem_singleton.mp (sg mraw)
  have fixed {d : Fin n} (md : d ∈ L) (b : tops G C)
      (fires : gateVal n C b (pairInput v d) = true) : b = star := by
    obtain ⟨q,mq,qnb,_,sq⟩ := centerOn md b fires
    have same := single mq mg qnb gnb
    subst q
    exact unique ((Finset.mem_singleton.mp (sq mraw)).symm.trans rawEq)
  have missed : ¬ L ⊆ leaf star := by
    intro all
    have equal := Finset.inter_eq_right.mpr all
    have low := thin star
    change (leaf star ∩ L).card ≤ 1 at low
    rw [equal] at low
    omega
  obtain ⟨d,md,out⟩ := Finset.not_subset.mp missed
  obtain ⟨b,mb,onb⟩ := acceptedTop least (adj d md)
  have same := fixed md ⟨b,mb⟩ onb
  have onstar : gateVal n C star (pairInput v d) = true := by
    change gateVal n C (⟨b,mb⟩ : tops G C).val (pairInput v d) = true at onb
    rwa [same] at onb
  have hd := topData star.2
  have lit := (andValOperands least.1 hd.1 hd.2.1 _).mp onstar (1-port star)
  obtain ⟨h,mh,_,sh⟩ := on_port (G := G) least.1 hd.1 (1-port star) (nonempty star) lit (by
    intro t mt yes
    rcases (pairInput_true _ _ _).mp yes with rfl | rfl
    · exact (leafAway star).1 mt
    · exact out mt)
  have hnb : h ≠ bad := by
    rintro rfl
    exact cannot (thin star) sh
  have hsame := single mh mg hnb gnb
  subst h
  exact (leafAway star).2 (rawEq ▸ sh mraw)

#print axioms raw_neighbors_le_one
end StarPromotions
