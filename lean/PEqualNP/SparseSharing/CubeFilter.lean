import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Equiv.Fin.Basic

/-- Local recovery from a cube address and a bounded neighbour-tag dictionary.
The conclusion gives an explicit number of rectangles covering exactly the zeros. -/
private theorem decode
    (m n d q t b D : Nat) (edge : Fin m → Fin n → Prop)
    (addr : Fin m → Finset (Fin d)) (hull : Fin n → Finset (Fin d))
    (tag : Fin m → Fin t) (tags : Fin n → Finset (Fin t))
    (code : Fin t → Finset (Fin q))
    (inside : ∀ r c, edge r c → addr r ⊆ hull c)
    (slack : ∀ r c, edge r c → (hull c \ addr r).card ≤ b)
    (recover : ∀ r s, tag r = tag s → (addr r \ addr s).card ≤ b → r = s)
    (dictionary : ∀ z c, z ∈ tags c ↔ ∃ s, edge s c ∧ tag s = z)
    (degree : ∀ c, (tags c).card ≤ D)
    (separate : ∀ z (J : Finset (Fin t)), J.card ≤ D →
      code z ⊆ J.biUnion code → z ∈ J) :
    ∃ (left : Fin (d+q) → Set (Fin m)) (right : Fin (d+q) → Set (Fin n)),
      ∀ r c, ¬ edge r c ↔ ∃ i, r ∈ left i ∧ c ∈ right i := by
  classical
  have test (r c) : edge r c ↔
      addr r ⊆ hull c ∧ code (tag r) ⊆ (tags c).biUnion code := by
    constructor
    · intro h
      refine ⟨inside r c h, ?_⟩
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨tag r, (dictionary _ c).mpr ⟨r,h,rfl⟩,hi⟩
    · rintro ⟨hr,hz⟩
      obtain ⟨s,hs,ht⟩ := (dictionary _ c).mp (separate _ _ (degree c) hz)
      have sub : addr r \ addr s ⊆ hull c \ addr s := by
        intro a ha
        obtain ⟨ar,as'⟩ := Finset.mem_sdiff.mp ha
        exact Finset.mem_sdiff.mpr ⟨hr ar,as'⟩
      have e := recover r s ht.symm ((Finset.card_le_card sub).trans (slack s c hs))
      exact e.symm ▸ hs
  let L : Fin d ⊕ Fin q → Set (Fin m) :=
    Sum.elim (fun i => {r | i ∈ addr r}) (fun i => {r | i ∈ code (tag r)})
  let R : Fin d ⊕ Fin q → Set (Fin n) :=
    Sum.elim (fun i => {c | i ∉ hull c}) (fun i => {c | i ∉ (tags c).biUnion code})
  refine ⟨fun i => L (finSumFinEquiv.symm i), fun i => R (finSumFinEquiv.symm i), ?_⟩
  intro r c
  constructor
  · intro hn
    by_cases h : addr r ⊆ hull c
    · have bad : ¬ code (tag r) ⊆ (tags c).biUnion code := fun v => hn ((test r c).mpr ⟨h,v⟩)
      obtain ⟨i,hi,hj⟩ := Finset.not_subset.mp bad
      exact ⟨finSumFinEquiv (.inr i), by simpa [L,R] using And.intro hi hj⟩
    · obtain ⟨i,hi,hj⟩ := Finset.not_subset.mp h
      exact ⟨finSumFinEquiv (.inl i), by simpa [L,R] using And.intro hi hj⟩
  · rintro ⟨i,hi,hj⟩ he
    obtain ⟨ha,hb⟩ := (test r c).mp he
    cases eqn : finSumFinEquiv.symm i with
    | inl x =>
      simp only [eqn,L,R,Sum.elim_inl,Set.mem_ofPred_eq] at hi hj
      exact hj (ha hi)
    | inr x =>
      simp only [eqn,L,R,Sum.elim_inr,Set.mem_ofPred_eq] at hi hj
      exact hj (hb hi)

private theorem union_slack {m d : Nat} (a : Fin m → Finset (Fin d))
    (p : Finset (Fin d)) (u : Nat) (J : Finset (Fin m))
    (each : ∀ j ∈ J, (a j \ p).card ≤ u) :
    (J.biUnion a \ p).card ≤ J.card * u := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J fresh ih =>
    have h := ih (fun j hj => each j (Finset.mem_insert_of_mem hj))
    have hi := each i (Finset.mem_insert_self i J)
    have incl : (insert i J).biUnion a \ p ⊆ (a i \ p) ∪ (J.biUnion a \ p) := by
      intro z hz
      obtain ⟨mem,hp⟩ := Finset.mem_sdiff.mp hz
      rcases Finset.mem_biUnion.mp mem with ⟨j,hj,hzj⟩
      rcases Finset.mem_insert.mp hj with e|jmem
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨e ▸ hzj,hp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_biUnion.mpr ⟨j,jmem,hzj⟩,hp⟩)
    have hle := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
    rw [Finset.card_insert_of_notMem fresh,Nat.add_mul]
    omega

/-- From short cube edges, equal-weight color separation and a disjunct code,
obtain d+q zero rectangles on the entire bipartite grid. -/
theorem PEqualNP.SparseSharing.CubeFilter
    (m n d q t R D : Nat)
    (N : Fin n → Finset (Fin m)) (x : Fin m → Finset (Fin d))
    (y : Fin n → Finset (Fin d)) (tag : Fin m → Fin t)
    (code : Fin t → Finset (Fin q))
    (degree : ∀ c, (N c).card ≤ D)
    (locality : ∀ c r, r ∈ N c →
      (x r \ y c).card ≤ R ∧ (y c \ x r).card ≤ R)
    (weight : ∀ r s, tag r = tag s → (x r).card = (x s).card)
    (color : ∀ r s, tag r = tag s →
      (x r \ x s).card + (x s \ x r).card ≤ 2 * (D * (2*R)) → r = s)
    (separate : ∀ z (J : Finset (Fin t)), J.card ≤ D →
      code z ⊆ J.biUnion code → z ∈ J) :
    ∃ (left : Fin (d+q) → Set (Fin m)) (right : Fin (d+q) → Set (Fin n)),
      ∀ r c, r ∉ N c ↔ ∃ i, r ∈ left i ∧ c ∈ right i := by
  classical
  apply decode m n d q t (D*(2*R)) D (fun r c => r ∈ N c) x
    (fun c => (N c).biUnion x) tag (fun c => (N c).image tag) code
  · intro r c hr i hi
    exact Finset.mem_biUnion.mpr ⟨r,hr,hi⟩
  · intro r c hr
    apply (union_slack x (x r) (2*R) (N c) ?_).trans
      (Nat.mul_le_mul_right (2*R) (degree c))
    intro s hs
    have incl : x s \ x r ⊆ (x s \ y c) ∪ (y c \ x r) := by
      intro i hi
      obtain ⟨his,hir⟩ := Finset.mem_sdiff.mp hi
      by_cases hy : i ∈ y c
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy,hir⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨his,hy⟩)
    have bound := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
    have h1 := (locality c s hs).1
    have h2 := (locality c r hr).2
    omega
  · intro r s ht h
    apply color r s ht
    have eq := Finset.card_sdiff_comm (weight r s ht)
    omega
  · intro z c
    exact Finset.mem_image
  · intro c
    exact Finset.card_image_le.trans (degree c)
  · exact separate
