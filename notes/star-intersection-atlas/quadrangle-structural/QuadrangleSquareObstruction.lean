import ThreeIntersectionsQuadrangle

/-!
Small geometric obstructions to an intersection of two unions of rectangles.
Each selected positive cell chooses one of the four product terms. Four
fooling cells must choose distinct terms. A constraint records two pairs of
cells whose rectangular hulls would force the same forbidden cross-cell.
The argument is independent of the concrete quadrangle.
-/
namespace QuadrangleSquareObstruction
open Set TwoIntersections ThreeIntersectionsQuadrangle

abbrev Code := Bool × Bool
abbrev Constraint := (Fin 8 × Fin 8) × (Fin 8 × Fin 8)

def join (a b : Fin 4 → Code) (i : Fin 8) : Code :=
  Fin.addCases (m := 4) (n := 4) (motive := fun _ => Code) a b i

def Active (v : Fin 8 → Code) (t : Constraint) : Prop :=
  (v t.1.1).1 = (v t.1.2).1 ∧ (v t.2.1).2 = (v t.2.2).2

instance (v : Fin 8 → Code) (t : Constraint) : Decidable (Active v t) := by
  unfold Active
  infer_instance

variable {ι κ : Type*}

def Valid (B : Set (ι × κ)) (f : Fin 8 → ι × κ) (t : Constraint) : Prop :=
  (f t.1.1).1 = (f t.2.1).1 ∧
  (f t.1.2).2 = (f t.2.2).2 ∧ ((f t.1.1).1, (f t.1.2).2) ∈ B

instance [DecidableEq ι] [DecidableEq κ] [DecidablePred (· ∈ B)]
    (f : Fin 8 → ι × κ) (t : Constraint) : Decidable (Valid B f t) := by
  unfold Valid
  infer_instance

theorem rectangle_cross {r : Set (ι × κ)} (hr : Rectangle r)
    {x y : ι × κ} (hx : x ∈ r) (hy : y ∈ r) : (x.1, y.2) ∈ r := by
  obtain ⟨rows, cols, rfl⟩ := hr
  exact ⟨hx.1, hy.2⟩

theorem rectangle_inter {a b : Set (ι × κ)}
    (ha : Rectangle a) (hb : Rectangle b) : Rectangle (a ∩ b) := by
  obtain ⟨r, c, rfl⟩ := ha
  obtain ⟨s, d, rfl⟩ := hb
  exact ⟨r ∩ s, c ∩ d, by ext p; simp; tauto⟩

/-- A finite list of valid hull conflicts rules out a square of four terms.
The supplied finite check only ranges over distinct labels on the first four
cells; their fooling property proves that restriction sound. -/
theorem no_square_cover {B : Set (ι × κ)} (f : Fin 8 → ι × κ)
    (hf : Fooling Bᶜ (fun i : Fin 4 => f (i.castAdd 4)))
    (ts : List Constraint) (valid : ∀ t ∈ ts, Valid B f t)
    (hit : ∀ a : Fin 4 → Code, Function.Injective a →
      ∀ b : Fin 4 → Code, ∃ t ∈ ts, Active (join a b) t)
    (r s : Bool → Set (ι × κ))
    (hr : ∀ b, Rectangle (r b)) (hs : ∀ b, Rectangle (s b))
    (cover : ∀ i, ∃ a b, f i ∈ r a ∧ f i ∈ s b)
    (avoid : ∀ p a b, p ∈ r a → p ∈ s b → p ∉ B) : False := by
  classical
  have hchoice : ∀ i, ∃ v : Code, f i ∈ r v.1 ∧ f i ∈ s v.2 := by
    intro i
    obtain ⟨a, b, ha, hb⟩ := cover i
    exact ⟨(a, b), ha, hb⟩
  choose v hv using hchoice
  let a : Fin 4 → Code := fun i => v (i.castAdd 4)
  let b : Fin 4 → Code := fun i => v (i.natAdd 4)
  have hinj : Function.Injective a := by
    intro i j hij
    apply fooling_rectangle_unique hf
      (rectangle_inter (hr (a i).1) (hs (a i).2))
      (fun p hp => avoid p (a i).1 (a i).2 hp.1 hp.2)
      (hv (i.castAdd 4))
    change f (j.castAdd 4) ∈ r (a i).1 ∧ f (j.castAdd 4) ∈ s (a i).2
    rw [hij]
    exact hv (j.castAdd 4)
  have hj : join a b = v := by
    funext i
    exact Fin.addCases_castAdd_natAdd (m := 4) (n := 4) v i
  obtain ⟨t, ht, heq⟩ := hit a hinj b
  rw [hj] at heq
  obtain ⟨hrow, hcol, hbad⟩ := valid t ht
  have hx : ((f t.1.1).1, (f t.1.2).2) ∈ r (v t.1.1).1 := by
    apply rectangle_cross (hr _) (hv t.1.1).1
    simpa only [heq.1] using (hv t.1.2).1
  have hy : ((f t.2.1).1, (f t.2.2).2) ∈ s (v t.2.1).2 := by
    apply rectangle_cross (hs _) (hv t.2.1).2
    simpa only [heq.2] using (hv t.2.2).2
  have hy' : ((f t.1.1).1, (f t.1.2).2) ∈ s (v t.2.1).2 := by
    simpa only [hrow, hcol] using hy
  exact avoid _ _ _ hx hy' hbad

#print axioms no_square_cover
end QuadrangleSquareObstruction
