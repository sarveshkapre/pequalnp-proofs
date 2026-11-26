import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Fin.Basic

/-- A vertex records its earlier neighbours on its own branch. Colours of tags
    can be reused on different branches. The output is an exact rectangle cover
    of nonadjacency, including pairs from incomparable branches. -/
theorem PEqualNP.SparseSharing.BranchDecoder
    {V : Type} [DecidableEq V] (d q : Nat)
    (tag : V → Nat × Nat) (path : V → Nat → Nat) (earlier : V → Finset V)
    (same : ∀ x y, tag x = tag y →
      path x (tag x).1 = path y (tag x).1 → x = y)
    (back : ∀ x y, y ∈ earlier x →
      (tag y).1 ≤ (tag x).1 ∧ ∀ i, i ≤ (tag y).1 → path x i = path y i)
    (A B : Fin d → V → Prop)
    (branch : ∀ x y, (∀ i, i ≤ (tag x).1 → i ≤ (tag y).1 → path x i = path y i) ↔
      ¬ ∃ j, A j x ∧ B j y)
    (red blue : Fin q → Nat × Nat → Prop)
    (distinguish : ∀ x y,
      tag x ∉ (earlier y).image tag → tag y ∉ (earlier x).image tag →
      ∃ j, red j (tag x) ∧ blue j (tag y) ∧
        (∀ u ∈ earlier y, ¬ red j (tag u)) ∧
        (∀ v ∈ earlier x, ¬ blue j (tag v))) :
    ∃ (L R : Fin (d+q) → Set V), ∀ x y,
      (y ∉ earlier x ∧ x ∉ earlier y) ↔ ∃ j, x ∈ L j ∧ y ∈ R j := by
  classical
  let aligned (x y : V) := ∀ i, i ≤ (tag x).1 → i ≤ (tag y).1 → path x i = path y i
  have recover (x y : V) (h : aligned x y) (mem : tag y ∈ (earlier x).image tag) :
      y ∈ earlier x := by
    obtain ⟨z,hz,e⟩ := Finset.mem_image.mp mem
    obtain ⟨le,hp⟩ := back x z hz
    have lev := congrArg Prod.fst e
    have he : path z (tag z).1 = path y (tag z).1 :=
      (hp _ (le_refl _)).symm.trans (h _ le (le_of_eq lev))
    exact (same z y e he) ▸ hz
  let L' : Fin d ⊕ Fin q → Set V := Sum.elim (fun j => {x | A j x})
    (fun j => {x | red j (tag x) ∧ ∀ v ∈ earlier x, ¬ blue j (tag v)})
  let R' : Fin d ⊕ Fin q → Set V := Sum.elim (fun j => {y | B j y})
    (fun j => {y | blue j (tag y) ∧ ∀ u ∈ earlier y, ¬ red j (tag u)})
  refine ⟨fun j => L' (finSumFinEquiv.symm j), fun j => R' (finSumFinEquiv.symm j), ?_⟩
  intro x y
  constructor
  · rintro ⟨hn,hrev⟩
    by_cases h : aligned x y
    · have rev : aligned y x := fun i hy hx => (h i hx hy).symm
      obtain ⟨j,rx,by',avoidR,avoidB⟩ := distinguish x y
        (fun hm => hrev (recover y x rev hm)) (fun hm => hn (recover x y h hm))
      exact ⟨finSumFinEquiv (.inr j), by simpa [L',R'] using (And.intro (And.intro rx avoidB) (And.intro by' avoidR))⟩
    · by_contra no
      apply h
      apply (branch x y).mpr
      rintro ⟨j,ha,hb⟩
      have pair : x ∈ L' (finSumFinEquiv.symm (finSumFinEquiv (.inl j))) ∧
          y ∈ R' (finSumFinEquiv.symm (finSumFinEquiv (.inl j))) := by
        simpa [L',R'] using And.intro ha hb
      exact no ⟨_,pair⟩
  · rintro ⟨j,hx,hy⟩
    cases eqn : finSumFinEquiv.symm j with
    | inl i =>
      simp only [eqn,L',R',Sum.elim_inl,Set.mem_ofPred_eq] at hx hy
      have na := fun h => ((branch x y).mp h) ⟨i,hx,hy⟩
      exact ⟨fun e => na (fun k _ hk => (back x y e).2 k hk),
        fun e => na (fun k hk _ => ((back y x e).2 k hk).symm)⟩
    | inr i =>
      simp only [eqn,L',R',Sum.elim_inr,Set.mem_ofPred_eq] at hx hy
      exact ⟨fun e => hx.2 y e hy.1, fun e => hy.2 x e hx.1⟩
