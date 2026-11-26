import Mathlib.Tactic

/-! Translating a free-intersection rectangle formula into a bipartite formula.
An arbitrary rectangle may be intersected with the output without changing the bound. -/
namespace PlaneSharing
open Set
variable {X Y : Type}

private def Bip (s : Nat) (z : Set (X × Y)) : Prop :=
  ∀ P : Nat → Set (X × Y) → Prop,
    (∀ a : Set X, P 1 (a ×ˢ univ)) → (∀ b : Set Y, P 1 (univ ×ˢ b)) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∪ b)) → P s z

private theorem box (a : Set X) (b : Set Y) : Bip 2 (a ×ˢ b) := by
  intro P row col meet _
  have h := meet 1 1 _ _ (row a) (col b)
  simpa [Set.prod_inter_prod] using h

private theorem combineMeet {i j : Nat} {a b : Set (X × Y)} (ha : Bip i a) (hb : Bip j b) :
    Bip (i+j) (a ∩ b) :=
  fun P row col meet join => meet _ _ _ _ (ha P row col meet join) (hb P row col meet join)
private theorem combineJoin {i j : Nat} {a b : Set (X × Y)} (ha : Bip i a) (hb : Bip j b) :
    Bip (i+j) (a ∪ b) :=
  fun P row col meet join => join _ _ _ _ (ha P row col meet join) (hb P row col meet join)

private def Invariant (k : Nat) (z : Set (X × Y)) : Prop :=
  (k = 0 → ∃ a b, z = a ×ˢ b) ∧
  ∀ (r : Set X) (c : Set Y), ∃ s ≤ max 2 (4*k), Bip s ((r ×ˢ c) ∩ z)

private theorem baseInv (a : Set X) (b : Set Y) : Invariant 0 (a ×ˢ b) := by
  refine ⟨fun _ => ⟨a,b,rfl⟩, ?_⟩
  intro r c
  exact ⟨2, by decide, by simpa [Set.prod_inter_prod] using box (r ∩ a) (c ∩ b)⟩

private theorem meetInv {i j : Nat} {a b : Set (X × Y)} (ha : Invariant i a)
    (hb : Invariant j b) : Invariant (i+j) (a ∩ b) := by
  constructor
  · intro hz
    obtain ⟨r,c,rfl⟩ := ha.1 (by omega)
    obtain ⟨u,v,rfl⟩ := hb.1 (by omega)
    exact ⟨r ∩ u,c ∩ v, Set.prod_inter_prod ..⟩
  · intro r c
    by_cases ia : i = 0
    · obtain ⟨u,v,rfl⟩ := ha.1 ia
      obtain ⟨s,bound,rep⟩ := hb.2 (r ∩ u) (c ∩ v)
      refine ⟨s,by simpa [ia] using bound,?_⟩
      simpa only [← Set.inter_assoc, Set.prod_inter_prod] using rep
    by_cases jb : j = 0
    · obtain ⟨u,v,rfl⟩ := hb.1 jb
      obtain ⟨s,bound,rep⟩ := ha.2 (r ∩ u) (c ∩ v)
      refine ⟨s,by simpa [jb] using bound,?_⟩
      rwa [Set.inter_comm a, ← Set.inter_assoc, Set.prod_inter_prod]
    obtain ⟨s,hs,as⟩ := ha.2 r c
    obtain ⟨t,ht,bt⟩ := hb.2 univ univ
    have bt' : Bip t b := by simpa using bt
    exact ⟨s+t,by omega,by simpa only [Set.inter_assoc] using combineMeet as bt'⟩

private theorem joinInv {i j : Nat} {a b : Set (X × Y)} (ha : Invariant i a)
    (hb : Invariant j b) : Invariant (i+j+1) (a ∪ b) := by
  refine ⟨by omega,?_⟩
  intro r c
  obtain ⟨s,hs,as⟩ := ha.2 r c
  obtain ⟨t,ht,bt⟩ := hb.2 r c
  exact ⟨s+t,by omega,by simpa only [Set.inter_union_distrib_left] using combineJoin as bt⟩
end PlaneSharing

open PlaneSharing in
theorem PEqualNP.PlaneSharing.Transfer :
    ∀ (m n k : Nat) (z : Set (Fin m × Fin n)),
  let R := Set (Fin m × Fin n)
  (∀ P : Nat → R → Prop,
    (∀ (a : Set (Fin m)) (b : Set (Fin n)), P 0 (Set.prod a b)) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
    (∀ i j a b, P i a → P j b → P (i+j+1) (a ∪ b)) → P k z) →
  ∃ s ≤ max 2 (4*k), ∀ P : Nat → R → Prop,
    (∀ a : Set (Fin m), P 1 (Set.prod a Set.univ)) →
    (∀ b : Set (Fin n), P 1 (Set.prod Set.univ b)) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∩ b)) →
    (∀ i j a b, P i a → P j b → P (i+j) (a ∪ b)) → P s z := by
  intro m n k z
  dsimp only
  intro h
  have inv := h Invariant baseInv (fun _ _ _ _ => meetInv) (fun _ _ _ _ => joinInv)
  obtain ⟨s,bound,rep⟩ := inv.2 Set.univ Set.univ
  refine ⟨s,bound,?_⟩
  have eq : (Set.univ ×ˢ Set.univ) ∩ z = z := by simp
  rw [eq] at rep
  exact rep
