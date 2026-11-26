import Mathlib.Tactic

namespace PaidDepth

abbrev Slot (k : Nat) := (Fin k × ((Bool × Bool) ⊕ (Bool × Bool))) ⊕ Bool
private abbrev Rect (R C : Type) := Set R × Set C
private def hits (a : Rect R C) (x : R × C) := x.1 ∈ a.1 ∧ x.2 ∈ a.2
private def meet (a b : Rect R C) : Rect R C := (a.1 ∩ b.1, a.2 ∩ b.2)
private def raw (a : Set R) (b : Set C) : Bool → Rect R C
  | false => (a, Set.univ)
  | true => (Set.univ, b)

private theorem raw_hit {a : Set R} {b : Set C} {x : R × C} :
    (∃ s, hits (raw a b s) x) ↔ x.1 ∈ a ∨ x.2 ∈ b := by
  constructor
  · rintro ⟨s,h⟩
    cases s
    · exact Or.inl h.1
    · exact Or.inr h.2
  · rintro (h|h)
    · exact ⟨false,h,Set.mem_univ _⟩
    · exact ⟨true,Set.mem_univ _,h⟩

private def bank (a : Fin k → Bool → Bool → Rect R C) (out : Bool → Rect R C) :
    Slot k → Rect R C
  | .inr b => out b
  | .inl (i, .inl (e, b)) => a i e b
  | .inl (i, .inr (s, t)) => meet (a i false s) (a i true t)

private def inside (D : Slot k → Rect R C) (J : Finset (Slot k)) (x : R × C) :=
  ∀ z ∈ J, hits (D z) x

private def cert (D : Slot k → Rect R C) (x : R × C) (P : R × C → Prop) (n : Nat) :=
  ∃ J : Finset (Slot k), J.card ≤ n ∧ inside D J x ∧ ∀ y, inside D J y → P y

private theorem single {D : Slot k → Rect R C} {x : R × C} {z : Slot k} {P : R × C → Prop}
    (hx : hits (D z) x) (hp : ∀ y, hits (D z) y → P y) : cert D x P 1 := by
  refine ⟨{z},by simp,?_,fun y hy => hp y (hy z (by simp))⟩
  intro w hw
  simpa [Finset.mem_singleton.mp hw] using hx

private theorem weaken {D : Slot k → Rect R C} {x : R × C} {P Q : R × C → Prop} {n m}
    (h : cert D x P n) (hn : n ≤ m) (hp : ∀ y, P y → Q y) : cert D x Q m := by
  obtain ⟨s,hs,hx,hp'⟩ := h
  exact ⟨s,hs.trans hn,hx,fun y hy => hp y (hp' y hy)⟩

private theorem combine {D : Slot k → Rect R C} {x : R × C} {P Q T : R × C → Prop} {n}
    (p : cert D x P n) (q : cert D x Q n) (step : ∀ y, P y → Q y → T y) :
    cert D x T (n+n) := by
  obtain ⟨a,ha,xa,pa⟩ := p
  obtain ⟨b,hb,xb,pb⟩ := q
  refine ⟨a ∪ b,(Finset.card_union_le a b).trans (Nat.add_le_add ha hb),?_,?_⟩
  · intro z hz
    exact (Finset.mem_union.mp hz).elim (xa z) (xb z)
  · intro y hy
    exact step y (pa y (fun z hz => hy z (Finset.mem_union_left _ hz)))
      (pb y (fun z hz => hy z (Finset.mem_union_right _ hz)))

private def arm (a : Fin k → Bool → Bool → Rect R C)
    (deps : Fin k → Bool → Fin k → Prop) (wire : Fin k → R × C → Prop)
    (i : Fin k) (e : Bool) (x : R × C) :=
  (∃ b, hits (a i e b) x) ∨ ∃ j, deps i e j ∧ wire j x

private theorem extract (a : Fin k → Bool → Bool → Rect R C) (out : Bool → Rect R C)
    (deps : Fin k → Bool → Fin k → Prop) (wire : Fin k → R × C → Prop) (level : Fin k → Nat)
    (smaller : ∀ i e j, deps i e j → level j < level i)
    (gate : ∀ i x, wire i x ↔ arm a deps wire i false x ∧ arm a deps wire i true x) :
    ∀ h i, level i ≤ h → ∀ x, wire i x → cert (bank a out) x (wire i) (2^h) := by
  intro h
  induction h with
  | zero =>
    intro i hi x hx
    have chooseRaw : ∀ e, arm a deps wire i e x → ∃ b, hits (a i e b) x := by
      rintro e (rawCase|⟨j,hj,_⟩)
      · exact rawCase
      · have := smaller i e j hj
        omega
    obtain ⟨left,right⟩ := (gate i x).mp hx
    obtain ⟨s,hs⟩ := chooseRaw false left
    obtain ⟨t,ht⟩ := chooseRaw true right
    apply single (z := Sum.inl (i, Sum.inr (s,t)))
    · exact ⟨⟨hs.1,ht.1⟩,hs.2,ht.2⟩
    · intro y hy
      exact (gate i y).mpr ⟨Or.inl ⟨s,hy.1.1,hy.2.1⟩,Or.inl ⟨t,hy.1.2,hy.2.2⟩⟩
  | succ h ih =>
    intro i hi x hx
    have getArm : ∀ e, arm a deps wire i e x → cert (bank a out) x (arm a deps wire i e) (2^h) := by
      rintro e (⟨b,hb⟩|⟨j,hj,hxj⟩)
      · have one : cert (bank a out) x (arm a deps wire i e) 1 :=
          single (z := Sum.inl (i, Sum.inl (e,b))) hb (fun _ hy => Or.inl ⟨b,hy⟩)
        exact weaken one (Nat.one_le_pow _ _ (by decide)) (fun _ p => p)
      · have hj' := smaller i e j hj
        exact weaken (ih j (by omega) x hxj) (Nat.le_refl _) (fun _ p => Or.inr ⟨j,hj,p⟩)
    obtain ⟨left,right⟩ := (gate i x).mp hx
    simpa [pow_succ,Nat.mul_two] using combine (getArm false left) (getArm true right)
      (fun y p q => (gate i y).mpr ⟨p,q⟩)

end PaidDepth

open PaidDepth in
theorem PEqualNP.PaidDepth.FoolingBound :
    ∀ (r c k d m : Nat) (A : Fin k → Bool → Set (Fin r)) (B : Fin k → Bool → Set (Fin c))
      (deps : Fin k → Bool → Fin k → Prop) (level : Fin k → Nat)
      (wire : Fin k → Fin r × Fin c → Prop) (row : Set (Fin r)) (col : Set (Fin c))
      (use : Fin k → Prop) (G : Fin r × Fin c → Prop) (points : Fin m → Fin r × Fin c),
    (∀ i e j, deps i e j → level j < level i) →
    (∀ i x, wire i x ↔ ∀ e, x.1 ∈ A i e ∨ x.2 ∈ B i e ∨ ∃ j, deps i e j ∧ wire j x) →
    (∀ i, use i → level i ≤ d) →
    (∀ x, G x ↔ x.1 ∈ row ∨ x.2 ∈ col ∨ ∃ i, use i ∧ wire i x) →
    (∀ i, G (points i)) →
    (∀ i j, i ≠ j → ¬ (G ((points i).1,(points j).2) ∧ G ((points j).1,(points i).2))) →
    m ≤ Fintype.card {s : Finset ((Fin k × ((Bool × Bool) ⊕ (Bool × Bool))) ⊕ Bool) //
      s.card ≤ 2^d} := by
  classical
  intro r c k d m A B deps level wire row col use G points decrease gates bounded output on cross
  let a := fun i e => raw (A i e) (B i e)
  let out := raw row col
  let D := bank a out
  have norm : ∀ i x, wire i x ↔ arm a deps wire i false x ∧ arm a deps wire i true x := by
    intro i x
    rw [gates]
    have eqv (e : Bool) : arm a deps wire i e x ↔
        x.1 ∈ A i e ∨ x.2 ∈ B i e ∨ ∃ j, deps i e j ∧ wire j x := by
      unfold arm a
      rw [raw_hit, or_assoc]
    exact ⟨fun h => ⟨(eqv false).mpr (h false),(eqv true).mpr (h true)⟩,
      fun ⟨p,q⟩ e => by cases e <;> first | exact (eqv _).mp p | exact (eqv _).mp q⟩
  have witness (i : Fin m) : cert D (points i) G (2^d) := by
    rcases (output _).mp (on i) with hr|hc|⟨j,hj,hw⟩
    · apply weaken (single (D := D) (z := Sum.inr false) ⟨hr,Set.mem_univ _⟩
        (fun y hy => (output y).mpr (Or.inl hy.1))) _ (fun _ h => h)
      exact Nat.one_le_pow _ _ (by decide)
    · apply weaken (single (D := D) (z := Sum.inr true) ⟨Set.mem_univ _,hc⟩
        (fun y hy => (output y).mpr (Or.inr (Or.inl hy.2)))) _ (fun _ h => h)
      exact Nat.one_le_pow _ _ (by decide)
    · exact weaken (extract a out deps wire level decrease norm d j (bounded j hj) _ hw)
        (Nat.le_refl _) (fun y hy => (output y).mpr (Or.inr (Or.inr ⟨j,hj,hy⟩)))
  choose sets count atPoint forces using witness
  let key (i : Fin m) : {s : Finset (Slot k) // s.card ≤ 2^d} := ⟨sets i,count i⟩
  have inj : Function.Injective key := by
    intro i j eq
    by_contra ne
    have same : sets i = sets j := congrArg Subtype.val eq
    have pj : inside D (sets i) (points j) := same.symm ▸ atPoint j
    apply cross i j ne
    exact ⟨forces i _ (fun z hz => ⟨(atPoint i z hz).1,(pj z hz).2⟩),
      forces i _ (fun z hz => ⟨(pj z hz).1,(atPoint i z hz).2⟩)⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective key inj
