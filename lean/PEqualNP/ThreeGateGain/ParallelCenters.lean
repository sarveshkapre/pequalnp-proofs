import PEqualNP.ThreeGateGain.IncidenceFree

/- Parallel intersections of free unions of point and line stars,
   with an arbitrary free output union. -/
namespace PlaneParallel
open Configuration

structure Arm (P L : Type*) where
  points : Set P
  lines : Set L

def Arm.eval (a : Arm P L) (p : P) (l : L) : Prop :=
  p ∈ a.points ∨ l ∈ a.lines

structure Circuit (P L : Type*) (gates : ℕ) where
  left : Fin gates → Arm P L
  right : Fin gates → Arm P L
  output : Arm P L

def Circuit.eval (c : Circuit P L t) (p : P) (l : L) : Prop :=
  c.output.eval p l ∨ ∃ i, (c.left i).eval p l ∧ (c.right i).eval p l

structure Rect (P L : Type*) where
  rows : Set P
  cols : Set L

def Rect.mem (a : Rect P L) (p : P) (l : L) := p∈a.rows ∧ l∈a.cols

def Circuit.rect (c : Circuit P L t) : Fin t × Bool → Rect P L
  | (i,false) => ⟨(c.left i).points,(c.right i).lines⟩
  | (i,true) => ⟨(c.right i).points,(c.left i).lines⟩

def partner (s : Fin t × Bool) : Fin t × Bool := (s.1,!s.2)

@[simp] theorem partner_partner (s : Fin t × Bool) : partner (partner s) = s := by
  rcases s with ⟨i,b⟩; cases b <;> rfl

def Computes [Membership P L] (c : Circuit P L t) : Prop :=
  ∀ p l, c.eval p l ↔ p ∈ l

variable {P L : Type*} [Membership P L] [Nondegenerate P L]

theorem point_disjoint (c : Circuit P L t) (hc : Computes c) (i : Fin t) (p : P) :
    ¬ (p∈(c.left i).points ∧ p∈(c.right i).points) := by
  obtain ⟨l,away⟩ := Nondegenerate.exists_line (L:=L) p
  rintro ⟨h,k⟩
  exact away ((hc p l).mp (Or.inr ⟨i,Or.inl h,Or.inl k⟩))

theorem line_disjoint (c : Circuit P L t) (hc : Computes c) (i : Fin t) (l : L) :
    ¬ (l∈(c.left i).lines ∧ l∈(c.right i).lines) := by
  obtain ⟨p,away⟩ := Nondegenerate.exists_point (P:=P) l
  rintro ⟨h,k⟩
  exact away ((hc p l).mp (Or.inr ⟨i,Or.inr h,Or.inr k⟩))

omit [Nondegenerate P L] in
theorem rect_sound (c : Circuit P L t) (hc : Computes c) (s : Fin t × Bool) :
    ∀ p l, (c.rect s).mem p l → p∈l := by
  rintro p l h
  apply (hc p l).mp
  right
  rcases s with ⟨i,b⟩
  cases b
  · exact ⟨i,Or.inl h.1,Or.inr h.2⟩
  · exact ⟨i,Or.inr h.2,Or.inl h.1⟩

theorem rect_complete (c : Circuit P L t) (hc : Computes c) (p : P) (l : L) (hl : p∈l) :
    ∃ s, (c.rect s).mem p l := by
  rcases (hc p l).mpr hl with (row|col)|⟨i,(p₁|l₁),(p₂|l₂)⟩
  · obtain ⟨l',away⟩ := Nondegenerate.exists_line (L:=L) p
    exact (away ((hc p l').mp (Or.inl (Or.inl row)))).elim
  · obtain ⟨p',away⟩ := Nondegenerate.exists_point (P:=P) l
    exact (away ((hc p' l).mp (Or.inl (Or.inr col)))).elim
  · exact (point_disjoint c hc i p ⟨p₁,p₂⟩).elim
  · exact ⟨(i,false),p₁,l₂⟩
  · exact ⟨(i,true),p₂,l₁⟩
  · exact (line_disjoint c hc i l ⟨l₁,l₂⟩).elim

theorem separated_slots (c : Circuit P L t) (hc : Computes c) (s : Fin t × Bool)
    (p p' : P) (l l' : L) (a : (c.rect s).mem p l) (b : (c.rect (partner s)).mem p' l') :
    p≠p' ∧ l≠l' := by
  rcases s with ⟨i,k⟩
  cases k
  · exact ⟨fun h => point_disjoint c hc i p ⟨a.1,h ▸ b.1⟩,
      fun h => line_disjoint c hc i l ⟨h ▸ b.2,a.2⟩⟩
  · exact ⟨fun h => point_disjoint c hc i p ⟨h ▸ b.1,a.1⟩,
      fun h => line_disjoint c hc i l ⟨a.2,h ▸ b.2⟩⟩

/-- A rectangle containing only incidences has a center on one of its two
shores. The label none permits an empty rectangle when either shore is empty. -/
theorem rect_center (r : Rect P L) (sound : ∀ p l, r.mem p l → p∈l) :
    ∃ v : Option (Sum P L), ∀ p l, r.mem p l →
      v=some (Sum.inl p) ∨ v=some (Sum.inr l) := by
  classical
  by_cases empty : ¬ ∃ p l, r.mem p l
  · exact ⟨none,fun p l h => (empty ⟨p,l,h⟩).elim⟩
  push Not at empty
  obtain ⟨p,l,hp,hl⟩ := empty
  by_cases only : ∀ p'∈r.rows, p'=p
  · exact ⟨some (.inl p),fun p' _ h => Or.inl (by rw [only _ h.1])⟩
  push Not at only
  obtain ⟨p',hp',ne⟩ := only
  refine ⟨some (.inr l),fun p'' l' h => Or.inr ?_⟩
  have eq := Nondegenerate.eq_or_eq (sound p' l ⟨hp',hl⟩) (sound p l ⟨hp,hl⟩)
    (sound p' l' ⟨hp',h.2⟩) (sound p l' ⟨hp,h.2⟩)
  rw [eq.resolve_left ne]

#print axioms rect_complete
#print axioms rect_center
end PlaneParallel
