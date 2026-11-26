import Mathlib.Tactic

/-! Route a vector through a sequence of input-controlled, fixed permutations.
The proof constructs an AND-inverter DAG and counts its individual gates. -/
namespace PlaneSharing.Route
open Set Function
open scoped Classical
variable {α ι : Type}
private abbrev Family (α : Type) := Set (Set α)
private def Paired (W : Family α) (a : Set α) := a ∈ W ∧ aᶜ ∈ W

private inductive Path (base : Family α) : Nat → Family α → Prop where
  | start : Path base 0 base
  | gate {i W a b} : Path base i W → Paired W a → Paired W b →
      Path base (i+1) (insert (a ∩ b) (insert (a ∩ b)ᶜ W))

private theorem incl {base W : Family α} (h : Path base n W) : base ⊆ W := by
  induction h with
  | start => exact Subset.rfl
  | gate _ _ _ ih => exact fun _ hx => Or.inr (Or.inr (ih hx))

private theorem preserve {base W : Family α} {a : Set α}
    (h : Path base n W) (p : Paired base a) : Paired W a :=
  ⟨incl h p.1, incl h p.2⟩

private theorem appendPath {u v w : Family α} (h : Path u i v) (g : Path v j w) :
    Path u (i+j) w := by
  induction g with
  | start => simpa using h
  | gate _ ha hb ih => exact .gate ih ha hb

private theorem record {u v : Family α} (h : Path u k v) (P : Nat → Family α → Prop)
    (initial : P 0 u)
    (extend : ∀ i W (a b : Set α), P i W → Paired W a → Paired W b →
      P (i+1) (insert (a ∩ b) (insert (a ∩ b)ᶜ W))) : P k v := by
  induction h with
  | start => exact initial
  | gate _ a b ih => exact extend _ _ _ _ ih a b

private theorem both {u : Family α} {a b : Set α} (pa : Paired u a) (pb : Paired u b) :
    ∃ v, Path u 1 v ∧ Paired v (a ∩ b) := by
  exact ⟨_,.gate .start pa pb, Or.inl rfl, Or.inr (Or.inl rfl)⟩

private theorem opposite {u : Family α} {a : Set α} (p : Paired u a) : Paired u aᶜ :=
  ⟨p.2, by simpa using p.1⟩

private def select (s a b : Set α) := (s ∩ a) ∪ (sᶜ ∩ b)

private theorem mux {u : Family α} {s a b : Set α}
    (ps : Paired u s) (pa : Paired u a) (pb : Paired u b) :
    ∃ v, Path u 3 v ∧ Paired v (select s a b) := by
  obtain ⟨v,h,p⟩ := both ps pa
  obtain ⟨w,g,q⟩ := both (opposite (preserve h ps)) (preserve h pb)
  obtain ⟨t,k,z⟩ := both (opposite (preserve g p)) (opposite q)
  exact ⟨t,appendPath (appendPath h g) k,by simpa [select] using opposite z⟩

private theorem layer (js : List ι) (s : Set α) (a b : ι → Set α) (u : Family α)
    (ps : Paired u s) (pa : ∀ j, Paired u (a j)) (pb : ∀ j, Paired u (b j)) :
    ∃ v, Path u (3*js.length) v ∧ ∀ j ∈ js, Paired v (select s (a j) (b j)) := by
  induction js with
  | nil => exact ⟨u,.start,by simp⟩
  | cons j js ih =>
    obtain ⟨v,h,old⟩ := ih
    obtain ⟨w,g,new⟩ := mux (preserve h ps) (preserve h (pa j)) (preserve h (pb j))
    refine ⟨w,by simpa [Nat.mul_add] using appendPath h g,?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact new
    · exact preserve g (old i hi)

private noncomputable def amount (se : List (Set α × Nat)) (x : α) :=
  (se.map (fun t => if x ∈ t.1 then t.2 else 0)).sum

private def out (f : ι → ι) (a : ι → Set α) (se : List (Set α × Nat)) (j : ι) : Set α :=
  {x | x ∈ a ((f^[amount se x]) j)}

private theorem route (f : Fin w → Fin w) (a : Fin w → Set α) (se : List (Set α × Nat))
    (u : Family α) (pa : ∀ j, Paired u (a j)) (ps : ∀ t ∈ se, Paired u t.1) :
    ∃ v, Path u (3*w*se.length) v ∧ ∀ j, Paired v (out f a se j) := by
  induction se with
  | nil => exact ⟨u,.start,by simpa [out,amount] using pa⟩
  | cons t ts ih =>
    obtain ⟨v,g,q⟩ := ih (fun z hz => ps z (List.mem_cons_of_mem _ hz))
    obtain ⟨w',k,p⟩ := layer (List.finRange w) t.1
      (fun j => out f a ts ((f^[t.2]) j)) (out f a ts) v
      (preserve g (ps t (by simp))) (fun _ => q _) q
    refine ⟨w',by simpa [Nat.mul_add] using appendPath g k,?_⟩
    intro j
    have eq : out f a (t::ts) j = select t.1 (out f a ts ((f^[t.2]) j)) (out f a ts j) := by
      ext x
      by_cases hx : x ∈ t.1
      · simp [out,select,amount,hx,← Function.iterate_add_apply,Nat.add_comm]
      · simp [out,select,amount,hx]
    rw [eq]
    exact p j (by simp)
end PlaneSharing.Route

open PlaneSharing.Route in
theorem PEqualNP.PlaneSharing.VariableShift :
    ∀ (n w : Nat) (f : Fin w → Fin w) (input : Fin w → Set (Fin n))
    (selectors : List (Set (Fin n) × Nat)) (base : Set (Set (Fin n))),
  let pair := fun (W : Set (Set (Fin n))) (a : Set (Fin n)) => a ∈ W ∧ aᶜ ∈ W
  (∀ j, pair base (input j)) → (∀ t ∈ selectors, pair base t.1) →
  ∃ V : Set (Set (Fin n)),
    (∀ P : Nat → Set (Set (Fin n)) → Prop, P 0 base →
      (∀ i W (a b : Set (Fin n)), P i W → pair W a → pair W b →
        P (i+1) (insert (a ∩ b) (insert (a ∩ b)ᶜ W))) →
      P (3*w*selectors.length) V) ∧
    ∀ j, pair V {x | x ∈ input ((f^[((selectors.map (fun t =>
      @ite Nat (x ∈ t.1) (Classical.propDecidable _) t.2 0)).sum)]) j)} := by
  intro n w f input selectors base
  dsimp only
  intro inputs bits
  obtain ⟨v,h,q⟩ := route f input selectors base inputs bits
  refine ⟨v,?_,q⟩
  intro P initial extend
  exact record h P initial extend
