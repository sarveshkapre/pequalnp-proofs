import Mathlib.Tactic

namespace PEqualNP.PaidDepth
namespace ReaderCode

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

end ReaderCode

theorem ReaderBypass :
∀ (r h : Nat) (R C : Type),
  let G := Fin r ⊕ (Fin h × Fin 3)
  ∀ (seed : G → Prop) (edge : G → Bool → G → Prop)
    (row : G → Bool → R → Prop) (col : G → Bool → C → Prop),
    (∀ b : Fin h, ¬seed (.inr (b,0))) →
    (∀ i e (b : Fin h), edge i e (.inr (b,0)) →
      e = true ∧ (i = .inr (b,1) ∨ i = .inr (b,2))) →
    ∃ (rows : Fin (2^r * 7^h) → R → Prop) (cols : Fin (2^r * 7^h) → C → Prop),
      ∀ x y, (∃ (arm : G → Bool) (active : G → Prop),
        (∀ i, seed i → active i) ∧
        (∀ i, active i → row i (arm i) x ∧ col i (arm i) y) ∧
        (∀ i j, active i → edge i (arm i) j → active j)) ↔
        ∃ j, rows j x ∧ cols j y
 := by
  classical
  intro r h R C G seed edge row col unseeded incoming
  let Code := (Fin r → Bool) × (Fin h → Fin 7)
  have count : Fintype.card Code = 2^r * 7^h := by simp [Code]
  let number := Fintype.equivFinOfCardEq count
  let read (q : Code) : G → Bool := Sum.elim q.1 fun bs => ReaderCode.decode (q.2 bs.1) bs.2
  let half (q : Code) (test : G → Bool → Prop) :=
    ∃ U : G → Prop, (∀ i, seed i → U i) ∧ (∀ i, U i → test i (read q i)) ∧
      ∀ i j, U i → edge i (read q i) j → U j
  refine ⟨fun j x => half (number.symm j) (fun i e => row i e x),
    fun j y => half (number.symm j) (fun i e => col i e y), ?_⟩
  intro x y
  constructor
  · rintro ⟨arm, active, roots, raw, closed⟩
    let q : Code := (fun i => arm (.inl i), fun b =>
      ReaderCode.encode (arm (.inr (b,0))) (arm (.inr (b,1))) (arm (.inr (b,2))))
    let keep : G → Prop := Sum.elim (fun _ => True) fun bs =>
      bs.2 ≠ 0 ∨ arm (.inr (bs.1,1)) = true ∨ arm (.inr (bs.1,2)) = true
    have agree (i : G) (ki : keep i) : read q i = arm i := by
      rcases i with i | ⟨b,s⟩
      · rfl
      · have dig := ReaderCode.digits (arm (.inr (b,0))) (arm (.inr (b,1))) (arm (.inr (b,2)))
        fin_cases s
        · exact dig.2.2 (ki.resolve_left (by simp))
        · exact dig.1
        · exact dig.2.1
    have rootKeep (i : G) (s : seed i) : keep i := by
      rcases i with i | ⟨b,j⟩
      · trivial
      · by_cases zero : j = 0
        · subst j
          exact (unseeded b s).elim
        · exact Or.inl zero
    have stepKeep (i j : G) (d : edge i (arm i) j) : keep j := by
      rcases j with j | ⟨b,s⟩
      · trivial
      · by_cases zero : s = 0
        · subst s
          obtain ⟨bit,hp | hp⟩ := incoming i (arm i) b d
          · subst i
            exact Or.inr (Or.inl bit)
          · subst i
            exact Or.inr (Or.inr bit)
        · exact Or.inl zero
    let U (i : G) := active i ∧ keep i
    have rootU (i : G) (s : seed i) : U i := ⟨roots i s, rootKeep i s⟩
    have rawU (i : G) (u : U i) : row i (read q i) x ∧ col i (read q i) y := by
      rw [agree i u.2]
      exact raw i u.1
    have stepU (i j : G) (u : U i) (d : edge i (read q i) j) : U j := by
      rw [agree i u.2] at d
      exact ⟨closed i j u.1 d, stepKeep i j d⟩
    refine ⟨number q, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ⟨⟨U,rootU,fun i u => (rawU i u).1,stepU⟩,
      ⟨U,rootU,fun i u => (rawU i u).2,stepU⟩⟩
  · rintro ⟨j, ⟨U,ru,au,cu⟩, ⟨V,rv,av,cv⟩⟩
    exact ⟨read (number.symm j),fun i => U i ∧ V i,
      fun i si => ⟨ru i si,rv i si⟩,fun i ai => ⟨au i ai.1,av i ai.2⟩,
      fun i j ai d => ⟨cu i j ai.1 d,cv i j ai.2 d⟩⟩

end PEqualNP.PaidDepth
