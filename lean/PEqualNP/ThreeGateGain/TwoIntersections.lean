import Mathlib.Tactic

/-! Work with zero sets. A free union of row and column stars has a rectangle
as its zero set. Free gates intersect zero sets and paid gates take their union. -/
namespace TwoIntersections
open Set

variable {α : Type*}
abbrev Family (α : Type*) := Set α → Prop

/-- Closure under arbitrary finite sequences of free binary gates. -/
inductive Free (F : Family α) : Family α where
  | input {s} : F s → Free F s
  | meet {s t} : Free F s → Free F t → Free F (s ∩ t)

def With (F : Family α) (h : Set α) : Family α := fun t => F t ∨ t = h
def Closed (F : Family α) := ∀ {s t}, F s → F t → F (s ∩ t)
def Cut (F : Family α) (h : Set α) : Family α :=
  fun t => F t ∨ ∃ r, F r ∧ t = r ∩ h

private theorem free_base {F : Family α} (hc : Closed F) {t} (ht : Free F t) : F t := by
  induction ht with
  | input h => exact h
  | meet _ _ ih jh => exact hc ih jh

private theorem cut_closed {F : Family α} (hc : Closed F) (h) : Closed (Cut F h) := by
  intro s t hs ht
  rcases hs with hs | ⟨a, ha, rfl⟩ <;> rcases ht with ht | ⟨b, hb, rfl⟩
  · exact Or.inl (hc hs ht)
  · exact Or.inr ⟨_, hc hs hb, by ext x; simp [and_assoc]⟩
  · exact Or.inr ⟨_, hc ha ht, by ext x; simp [and_left_comm, and_comm]⟩
  · exact Or.inr ⟨_, hc ha hb, by ext x; simp [and_assoc, and_left_comm, and_comm]⟩

private theorem free_with {F : Family α} (hc : Closed F) (hu : F univ)
    (h : Set α) {t} (ht : Free (With F h) t) : Cut F h t := by
  induction ht with
  | input hx =>
    rcases hx with hx | rfl
    · exact Or.inl hx
    · exact Or.inr ⟨univ, hu, (univ_inter _).symm⟩
  | meet _ _ ih jh => exact cut_closed hc h ih jh

/-- Two paid gates in topological order, with free gates and fan-out at every stage. -/
def Two (F : Family α) (z : Set α) : Prop :=
  ∃ a b, Free F a ∧ Free F b ∧
    ∃ c d, Free (With F (a ∪ b)) c ∧ Free (With F (a ∪ b)) d ∧
      Free (With (With F (a ∪ b)) (c ∪ d)) z

def Normal (F : Family α) (z : Set α) : Prop :=
  (∃ a b c, F a ∧ F b ∧ F c ∧ z = (a ∪ b) ∪ c) ∨
  (∃ a b c d, F a ∧ F b ∧ F c ∧ F d ∧ z = (a ∪ b) ∩ (c ∪ d))

private theorem cut_union {F : Family α} (hc : Closed F) {a b c d : Set α}
    (ha : F a) (hb : F b) (h₁ : Cut F (a ∪ b) c) (h₂ : Cut F (a ∪ b) d) :
    Normal F (c ∪ d) := by
  rcases h₁ with h₁ | ⟨u, hu, rfl⟩ <;> rcases h₂ with h₂ | ⟨v, hv, rfl⟩
  · exact Or.inl ⟨c, d, d, h₁, h₂, h₂, by ext; simp⟩
  · exact Or.inl ⟨c, v ∩ a, v ∩ b, h₁, hc hv ha, hc hv hb, by ext; simp; tauto⟩
  · exact Or.inl ⟨u ∩ a, u ∩ b, d, hc hu ha, hc hu hb, h₂, by ext; simp; tauto⟩
  · exact Or.inr ⟨u, v, a, b, hu, hv, ha, hb, by ext; simp; tauto⟩

theorem normal_iff {F : Family α} (hc : Closed F) (hu : F univ) (z : Set α) :
    Two F z ↔ Normal F z := by
  constructor
  · rintro ⟨a, b, ha, hb, c, d, h₁, h₂, hz⟩
    have hA := free_base hc ha
    have hB := free_base hc hb
    let H := a ∪ b
    have cH : Closed (Cut F H) := cut_closed hc H
    have first (t : Set α) (ht : With F H t) : Cut F H t :=
      free_with hc hu H (Free.input ht)
    have finalCut : Cut (Cut F H) (c ∪ d) z := by
      apply free_with cH (Or.inl hu)
      induction hz with
      | input hx =>
        rcases hx with hx | hx
        · exact Free.input (Or.inl (first _ hx))
        · exact Free.input (Or.inr hx)
      | meet _ _ ih jh => exact Free.meet ih jh
    rcases finalCut with h | ⟨r, hr, rfl⟩
    · simpa using cut_union hc hA hB h h
    · rw [inter_union_distrib_left]
      exact cut_union hc hA hB (cH hr (free_with hc hu H h₁))
        (cH hr (free_with hc hu H h₂))
  · rintro (⟨a, b, c, ha, hb, hc', rfl⟩ | ⟨a, b, c, d, ha, hb, hc', hd, rfl⟩)
    · exact ⟨a, b, .input ha, .input hb, a ∪ b, c,
        .input (Or.inr rfl), .input (Or.inl hc'), .input (Or.inr rfl)⟩
    · exact ⟨a, b, .input ha, .input hb, c, d, .input (Or.inl hc'), .input (Or.inl hd),
        .meet (.input (Or.inl (Or.inr rfl))) (.input (Or.inr rfl))⟩

def Rectangle {ι κ : Type*} (s : Set (ι × κ)) : Prop :=
  ∃ rows : Set ι, ∃ cols : Set κ, s = rows ×ˢ cols

/-- Selecting rows and columns for a free union leaves exactly this rectangle uncovered. -/
theorem zero_set_of_stars {ι κ : Type*} (rows : Set ι) (cols : Set κ) :
    {x : ι × κ | x.1 ∈ rows ∨ x.2 ∈ cols}ᶜ = rowsᶜ ×ˢ colsᶜ := by
  ext x
  change ¬ (_ ∨ _) ↔ ¬ _ ∧ ¬ _
  exact not_or

theorem rectangle_normal_iff {ι κ : Type*} (z : Set (ι × κ)) :
    Two Rectangle z ↔ Normal Rectangle z := by
  apply normal_iff
  · rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a ∩ c, b ∩ d, by ext x; simp; tauto⟩
  · exact ⟨univ, univ, by simp⟩

#print axioms rectangle_normal_iff
end TwoIntersections
