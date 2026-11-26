import FusionProfiles
import FusionCubeData

/-!
Three-dimensional Boolean cube semantics for signed profiles. The finite table
dominates the union of all safe cube faces meeting a chosen column face. It
therefore turns the local mixed-witness condition into a small geometric test.
-/
namespace FusionCube

open FusionProfiles

def encode (w : Word 3) : Code :=
  ⟨9 * (w 0).val + 3 * (w 1).val + (w 2).val, by
    have h0 := (w 0).isLt
    have h1 := (w 1).isLt
    have h2 := (w 2).isLt
    omega⟩

def decode (c : Code) : Word 3 :=
  ![⟨c.val / 9, by have h := c.isLt; omega⟩,
    ⟨(c.val / 3) % 3, Nat.mod_lt _ (by decide)⟩,
    ⟨c.val % 3, Nat.mod_lt _ (by decide)⟩]

theorem decode_encode (w : Word 3) : decode (encode w) = w := by
  have h0 := (w 0).isLt
  have h1 := (w 1).isLt
  have h2 := (w 2).isLt
  funext i
  fin_cases i <;> apply Fin.ext <;> dsimp [decode, encode] <;> omega

theorem encode_decode (c : Code) : encode (decode c) = c := by
  have hc := c.isLt
  apply Fin.ext
  dsimp [encode, decode]
  omega

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

theorem decode_injective : Function.Injective decode :=
  Function.LeftInverse.injective encode_decode

def maskDisjoint (a b : Nat) : Prop := a &&& b = 0
def maskMeets (a b : Nat) : Prop := a &&& b ≠ 0
def maskSubset (a b : Nat) : Prop := a &&& b = a

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem face_lt (c : Code) : face c < 256 := by
  have h : ∀ c : Code, face c < 256 := by decide +kernel
  exact h c

theorem opposes_decode_iff : ∀ a b : Code,
    Opposes (decode a) (decode b) ↔ maskDisjoint (face a) (face b) := by
  unfold Opposes maskDisjoint
  decide +kernel

theorem refines_decode_iff : ∀ a b : Code,
    Refines (decode a) (decode b) ↔ maskSubset (face b) (face a) := by
  unfold Refines maskSubset
  decide +kernel

theorem opposes_iff (a b : Word 3) :
    Opposes a b ↔ maskDisjoint (face (encode a)) (face (encode b)) := by
  simpa only [decode_encode] using opposes_decode_iff (encode a) (encode b)

theorem compatible_iff (a b : Word 3) :
    Compatible a b ↔ maskMeets (face (encode a)) (face (encode b)) := by
  unfold Compatible maskMeets
  rw [opposes_iff]
  rfl

theorem refines_iff (a b : Word 3) :
    Refines a b ↔ maskSubset (face (encode b)) (face (encode a)) := by
  simpa only [decode_encode] using refines_decode_iff (encode a) (encode b)

def safe (a b c : Code) : Nat := 255 ^^^ (face a ||| face b ||| face c)

theorem safe_lt (a b c : Code) : safe a b c < 256 := by
  exact Nat.xor_lt_two_pow (n := 8) (by decide)
    (Nat.or_lt_two_pow (Nat.or_lt_two_pow (face_lt a) (face_lt b)) (face_lt c))

theorem face_subset_safe {p a b c : Code}
    (ha : maskDisjoint (face p) (face a))
    (hb : maskDisjoint (face p) (face b))
    (hc : maskDisjoint (face p) (face c)) : maskSubset (face p) (safe a b c) := by
  unfold maskSubset safe
  unfold maskDisjoint at ha hb hc
  simp only [Nat.and_xor_distrib_left, Nat.and_or_distrib_left, ha, hb, hc,
    Nat.zero_or, Nat.xor_zero]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) (face_lt p)

theorem maskMeets.symm {a b : Nat} (h : maskMeets a b) : maskMeets b a := by
  simpa only [maskMeets, Nat.and_comm] using h

theorem maskMeets.of_subset {a b s : Nat}
    (has : maskSubset a s) (hab : maskMeets a b) : maskMeets s b := by
  unfold maskSubset at has
  unfold maskMeets at hab ⊢
  intro hsb
  apply hab
  calc
    a &&& b = (a &&& s) &&& b := by rw [has]
    _ = a &&& (s &&& b) := Nat.and_assoc _ _ _
    _ = 0 := by rw [hsb, Nat.and_zero]

/-- Every safe column face has a table entry containing every safe face meeting it.
This checks all 256 regions, all 27 column faces, and all 27 witness faces. -/
theorem stars_domination : ∀ t : Fin 256, ∀ c : Code,
    maskSubset (face c) t.val → ∃ s ∈ stars t.val,
      ∀ p : Code, maskSubset (face p) t.val → maskMeets (face p) (face c) →
        maskSubset (face p) s := by
  unfold maskSubset maskMeets
  decide +kernel

/-- A local profile model gives a listed cube star meeting every outside row. -/
theorem local_column_star {R C : Type*} {G : R → C → Prop}
    {rowWords : R → Word 3} {colWords : C → Word 3}
    (h : LocalProfileCondition G rowWords colWords)
    (c : C) (r₀ r₁ r₂ : R)
    (line : ∀ r, G r c ↔ r = r₀ ∨ r = r₁ ∨ r = r₂) :
    ∃ s ∈ stars (safe (encode (rowWords r₀)) (encode (rowWords r₁))
        (encode (rowWords r₂))),
      ∀ r, ¬ G r c → s &&& face (encode (rowWords r)) ≠ 0 := by
  have h0 : G r₀ c := (line r₀).2 (Or.inl rfl)
  have h1 : G r₁ c := (line r₁).2 (Or.inr (Or.inl rfl))
  have h2 : G r₂ c := (line r₂).2 (Or.inr (Or.inr rfl))
  let t := safe (encode (rowWords r₀)) (encode (rowWords r₁))
    (encode (rowWords r₂))
  have hc : maskSubset (face (encode (colWords c))) t :=
    face_subset_safe ((opposes_iff _ _).1 (h.1 r₀ c h0).symm)
      ((opposes_iff _ _).1 (h.1 r₁ c h1).symm)
      ((opposes_iff _ _).1 (h.1 r₂ c h2).symm)
  obtain ⟨s,hs,hdom⟩ := stars_domination ⟨t,safe_lt _ _ _⟩ (encode (colWords c)) hc
  refine ⟨s,hs,?_⟩
  intro r hrc
  obtain ⟨p,hpr,hpc,hop⟩ := h.2 r c hrc
  have hp : maskSubset (face (encode p)) t :=
    face_subset_safe ((opposes_iff _ _).1 (hop r₀ h0).symm)
      ((opposes_iff _ _).1 (hop r₁ h1).symm)
      ((opposes_iff _ _).1 (hop r₂ h2).symm)
  have hpC : maskMeets (face (encode p)) (face (encode (colWords c))) :=
    ((compatible_iff _ _).1 hpc).symm
  have hpR : maskMeets (face (encode p)) (face (encode (rowWords r))) :=
    ((compatible_iff _ _).1 hpr).symm
  exact maskMeets.of_subset (hdom (encode p) hp hpC) hpR

#print axioms decode_encode
#print axioms opposes_decode_iff
#print axioms refines_decode_iff
#print axioms stars_domination
#print axioms local_column_star

end FusionCube
