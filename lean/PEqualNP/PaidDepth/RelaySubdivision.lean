import Mathlib.Tactic

namespace PEqualNP.PaidDepth
namespace RelayRegionCode

private def encode (center left right : Bool) : Fin 7 :=
  if left then
    if right then (if center then 6 else 5) else (if center then 4 else 3)
  else if right then (if center then 2 else 1) else 0

private def decode (z : Fin 7) (slot : Fin 3) : Bool :=
  if slot = 0 then decide (z = 2 ∨ z = 4 ∨ z = 6)
  else if slot = 1 then decide (3 ≤ z.val)
  else decide (z = 1 ∨ z = 2 ∨ 5 ≤ z.val)

private theorem digits : ∀ c l r : Bool,
    decode (encode c l r) 1 = l ∧ decode (encode c l r) 2 = r ∧
    ((l = true ∨ r = true) → decode (encode c l r) 0 = c) := by decide

end RelayRegionCode

private theorem regionBound :
∀ (r h : Nat) (R C : Type),
  let G := Fin r ⊕ (Fin h × Fin 3)
  ∀ (seed : G → Prop) (edge : G → Bool → G → Prop)
    (row : G → Bool → R → Prop) (col : G → Bool → C → Prop),
    ∀ region : Fin h → G → Prop,
    (∀ b, region b (.inr (b,0))) →
    (∀ b i, region b i → ¬seed i) →
    (∀ (b : Fin h) i j e, region b j → ¬region b i → edge i e j →
      e = true ∧ (i = .inr (b,1) ∨ i = .inr (b,2))) →
    ∃ (rows : Fin (2^r * 7^h) → R → Prop) (cols : Fin (2^r * 7^h) → C → Prop),
      ∀ x y, (∃ (arm : G → Bool) (active : G → Prop),
        (∀ i, seed i → active i) ∧
        (∀ i, active i → row i (arm i) x ∧ col i (arm i) y) ∧
        (∀ i j, active i → edge i (arm i) j → active j)) ↔
        ∃ j, rows j x ∧ cols j y
 := by
  classical
  intro r h R C G seed edge row col region centerIn unseeded incoming
  let Code := (Fin r → Bool) × (Fin h → Fin 7)
  have count : Fintype.card Code = 2^r * 7^h := by simp [Code]
  let number := Fintype.equivFinOfCardEq count
  let read (q : Code) : G → Bool := Sum.elim q.1 fun bs => RelayRegionCode.decode (q.2 bs.1) bs.2
  let half (q : Code) (test : G → Bool → Prop) :=
    ∃ U : G → Prop, (∀ i, seed i → U i) ∧ (∀ i, U i → test i (read q i)) ∧
      ∀ i j, U i → edge i (read q i) j → U j
  refine ⟨fun j x => half (number.symm j) (fun i e => row i e x),
    fun j y => half (number.symm j) (fun i e => col i e y), ?_⟩
  intro x y
  constructor
  · rintro ⟨arm, active, roots, raw, closed⟩
    let q : Code := (fun i => arm (.inl i), fun b =>
      RelayRegionCode.encode (arm (.inr (b,0))) (arm (.inr (b,1))) (arm (.inr (b,2))))
    let keep (i : G) := ∀ b, region b i →
      arm (.inr (b,1)) = true ∨ arm (.inr (b,2)) = true
    have agree (i : G) (ki : keep i) : read q i = arm i := by
      rcases i with i | ⟨b,s⟩
      · rfl
      · have dig := RelayRegionCode.digits (arm (.inr (b,0))) (arm (.inr (b,1))) (arm (.inr (b,2)))
        fin_cases s
        · exact dig.2.2 (ki b (centerIn b))
        · exact dig.1
        · exact dig.2.1
    have rootKeep (i : G) (s : seed i) : keep i := by
      intro b hin
      exact (unseeded b i hin s).elim
    have stepKeep (i j : G) (ki : keep i) (d : edge i (arm i) j) : keep j := by
      intro b hj
      by_cases hi : region b i
      · exact ki b hi
      · obtain ⟨bit,hp | hp⟩ := incoming b i j (arm i) hj hi d
        · subst i
          exact Or.inl bit
        · subst i
          exact Or.inr bit
    let U (i : G) := active i ∧ keep i
    have rootU (i : G) (s : seed i) : U i := ⟨roots i s, rootKeep i s⟩
    have rawU (i : G) (u : U i) : row i (read q i) x ∧ col i (read q i) y := by
      rw [agree i u.2]
      exact raw i u.1
    have stepU (i j : G) (u : U i) (d : edge i (read q i) j) : U j := by
      rw [agree i u.2] at d
      exact ⟨closed i j u.1 d, stepKeep i j u.2 d⟩
    refine ⟨number q, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ⟨⟨U,rootU,fun i u => (rawU i u).1,stepU⟩,
      ⟨U,rootU,fun i u => (rawU i u).2,stepU⟩⟩
  · rintro ⟨j, ⟨U,ru,au,cu⟩, ⟨V,rv,av,cv⟩⟩
    exact ⟨read (number.symm j),fun i => U i ∧ V i,
      fun i si => ⟨ru i si,rv i si⟩,fun i ai => ⟨au i ai.1,av i ai.2⟩,
      fun i j ai d => ⟨cu i j ai.1 d,cv i j ai.2 d⟩⟩

private theorem mandatoryCut :
∀ (G : Type) (seed banned : G → Prop) (edge : G → Bool → G → Prop)
  (raw : G → Bool → Prop) (p q : G) (removed : G → Prop),
  let reaches := Relation.ReflTransGen (fun i j => ∀ e, edge i e j)
  let witness := fun (roots off : G → Prop) (deps : G → Bool → G → Prop) =>
    ∃ (arm : G → Bool) (active : G → Prop),
      (∀ i, roots i → active i) ∧ (∀ i, active i → ¬off i) ∧
      (∀ i, active i → raw i (arm i)) ∧
      (∀ i j, active i → deps i (arm i) j → active j)
  reaches p q → removed p → (∀ i, removed i → reaches i p) →
    (witness seed banned edge ↔
      witness (fun i => seed i ∨ i = p ∨ i = q) banned
        (fun i e j => edge i e j ∧ j ≠ p ∧ j ≠ q) ∨
      witness seed (fun i => banned i ∨ removed i) edge)
 := by
  intro G seed banned edge raw p q removed reaches witness pq rp toP
  constructor
  · rintro ⟨arm, active, roots, off, hit, closed⟩
    have travel {i j : G} (h : reaches i j) (hi : active i) : active j := by
      induction h with
      | refl => exact hi
      | tail _ last ih => exact closed _ _ ih (last _)
    by_cases hp : active p
    · left
      refine ⟨arm, active, ?_, off, hit, ?_⟩
      · intro i h
        rcases h with si | rfl | rfl
        · exact roots i si
        · exact hp
        · exact travel pq hp
      · exact fun i j ai h => closed i j ai h.1
    · right
      refine ⟨arm, active, roots, ?_, hit, closed⟩
      intro i ai h
      rcases h with h | h
      · exact off i ai h
      · exact hp (travel (toP i h) ai)
  · rintro (⟨arm,active,roots,off,hit,closed⟩ | ⟨arm,active,roots,off,hit,closed⟩)
    · refine ⟨arm,active,fun i h => roots i (Or.inl h),off,hit,?_⟩
      intro i j ai h
      by_cases jp : j = p
      · exact roots j (Or.inr (Or.inl jp))
      by_cases jq : j = q
      · exact roots j (Or.inr (Or.inr jq))
      exact closed i j ai ⟨h,jp,jq⟩
    · exact ⟨arm,active,roots,fun i ai bi => off i ai (Or.inl bi),hit,closed⟩

theorem RelaySubdivision :
(∀ (r h : Nat) (R C : Type),
  let G := Fin r ⊕ (Fin h × Fin 3)
  ∀ (seed : G → Prop) (edge : G → Bool → G → Prop)
    (row : G → Bool → R → Prop) (col : G → Bool → C → Prop),
    ∀ region : Fin h → G → Prop,
    (∀ b, region b (.inr (b,0))) →
    (∀ b i, region b i → ¬seed i) →
    (∀ (b : Fin h) i j e, region b j → ¬region b i → edge i e j →
      e = true ∧ (i = .inr (b,1) ∨ i = .inr (b,2))) →
    ∃ (rows : Fin (2^r * 7^h) → R → Prop) (cols : Fin (2^r * 7^h) → C → Prop),
      ∀ x y, (∃ (arm : G → Bool) (active : G → Prop),
        (∀ i, seed i → active i) ∧
        (∀ i, active i → row i (arm i) x ∧ col i (arm i) y) ∧
        (∀ i j, active i → edge i (arm i) j → active j)) ↔
        ∃ j, rows j x ∧ cols j y) ∧
(∀ (G : Type) (seed banned : G → Prop) (edge : G → Bool → G → Prop)
  (raw : G → Bool → Prop) (p q : G) (removed : G → Prop),
  let reaches := Relation.ReflTransGen (fun i j => ∀ e, edge i e j)
  let witness := fun (roots off : G → Prop) (deps : G → Bool → G → Prop) =>
    ∃ (arm : G → Bool) (active : G → Prop),
      (∀ i, roots i → active i) ∧ (∀ i, active i → ¬off i) ∧
      (∀ i, active i → raw i (arm i)) ∧
      (∀ i j, active i → deps i (arm i) j → active j)
  reaches p q → removed p → (∀ i, removed i → reaches i p) →
    (witness seed banned edge ↔
      witness (fun i => seed i ∨ i = p ∨ i = q) banned
        (fun i e j => edge i e j ∧ j ≠ p ∧ j ≠ q) ∨
      witness seed (fun i => banned i ∨ removed i) edge)) := ⟨regionBound, mandatoryCut⟩

end PEqualNP.PaidDepth
