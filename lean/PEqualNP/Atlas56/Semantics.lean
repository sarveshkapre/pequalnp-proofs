import PEqualNP.Atlas56.Cover
import PEqualNP.Atlas56.QuadrangleStructural

namespace Atlas56
open Set TwoIntersections ThreeIntersectionsFormula

def cells (c : Col → Pat) : Set Cell := {p | (c p.2).val.testBit p.1.val = true}

def orbit (z : Set Cell) : Prop :=
  ∃ (r : Equiv.Perm Row) (c : Equiv.Perm Col),
    z = (fun p : Cell => (r p.1,c p.2)) ⁻¹' ThreeIntersectionsQuadrangle.zero

def cube (z : Set Cell) : Prop :=
  ∃ a b c d e f : Set Cell,
    Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧ Rectangle e ∧ Rectangle f ∧
    z = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f)

theorem choice_gives_cube (cols : Col → Pat) (n : Nat)
    (h : ∀ j, (good (cols j)).testBit n = true) : cube (cells cols) := by
  let rect (k : Fin 6) : Set Cell :=
    {r : Row | (rowBits r k).testBit n = true} ×ˢ
    {j : Col | (colBits (cols j) k).testBit n = true}
  have hr (k : Fin 6) : Rectangle (rect k) := ⟨_,_,rfl⟩
  refine ⟨_,_,_,_,_,_,hr 0,hr 1,hr 2,hr 3,hr 4,hr 5,?_⟩
  ext ⟨r,j⟩
  have he := congrArg (fun t : Nat => t.testBit n) (agree r (cols j))
  have hh : (bits r (cols j)).testBit n = (cols j).val.testBit r.val := by
    cases hc : (cols j).val.testBit r.val <;> simpa [hc,Nat.testBit_and,h j] using he
  change (cols j).val.testBit r.val = true ↔ _
  rw [← hh]
  simp [bits,rect,Nat.testBit_and,Nat.testBit_or]

theorem exc_cells : ∀ (i : Fin 15) (j : Col) (r : Row),
    (excCol i j).val.testBit r.val = true ↔
    (rowMap i r,j) ∈ ThreeIntersectionsQuadrangle.zero := by
  unfold ThreeIntersectionsQuadrangle.zero ThreeIntersectionsQuadrangle.graph
  decide +kernel

theorem choice_gives_orbit (cols : Col → Pat) (i : Fin 15)
    (inj : Function.Injective cols) (h : ∀ j, (exc (cols j)).testBit i.val = true) :
    orbit (cells cols) := by
  choose f hf using fun j => (exc_spec (cols j) i).mp (h j)
  have fi : Function.Injective f := fun a b hab => inj ((hf a).trans ((congrArg (excCol i) hab).trans (hf b).symm))
  let r := Equiv.ofBijective (rowMap i) (Finite.injective_iff_bijective.mp (rowMap_inj i))
  let c := Equiv.ofBijective f (Finite.injective_iff_bijective.mp fi)
  refine ⟨r,c,?_⟩
  ext ⟨a,b⟩
  change (cols b).val.testBit a.val = true ↔ (rowMap i a,f b) ∈ ThreeIntersectionsQuadrangle.zero
  rw [hf b]
  exact exc_cells i (f b) a

theorem alternative (univ : List Pat) (hn : univ.Nodup) (hu : univ.toFinset = Finset.univ)
    (verified : check 6 (univ.map entry) allGood allExc = true) (cols : Col → Pat) :
    cube (cells cols) ∨ orbit (cells cols) := by
  let needed := Finset.univ.image cols
  let used := univ.filter (fun p => p ∈ needed)
  have hmem (p : Pat) : p ∈ univ := List.mem_toFinset.mp (by rw [hu]; simp)
  have same : used.toFinset = needed := by ext p; simp [used,hmem]
  have card : used.length = needed.card := by
    rw [← same, List.toFinset_card_of_nodup (hn.filter _)]
  have upto : used.length ≤ 6 := card.trans_le (Finset.card_image_le.trans (by simp))
  have has (j : Col) : entry (cols j) ∈ used.map entry := by
    apply List.mem_map_of_mem
    simp [used,needed,hmem]
  have result := check_sound (univ.map entry) 6 allGood allExc (used.map entry)
    ((List.filter_sublist (l := univ)).map entry) (by simpa using upto) verified
  rcases result with ok | ⟨six, ex⟩
  · obtain ⟨n, bit⟩ := Nat.exists_testBit_of_ne_zero ok
    have all := (fold_bits (used.map entry) Entry.ok allGood n bit).2
    exact Or.inl (choice_gives_cube cols n (fun j => all _ (has j)))
  · obtain ⟨n, bit⟩ := Nat.exists_testBit_of_ne_zero ex
    obtain ⟨bound,all⟩ := fold_bits (used.map entry) Entry.ex allExc n bit
    have lt : n < 15 := by
      by_contra! bad
      have p : allExc < 2^n := lt_of_lt_of_le (show allExc < 2^15 by decide) (Nat.pow_le_pow_right (by decide) bad)
      simp [Nat.testBit_lt_two_pow p] at bound
    have eqCard : needed.card = (Finset.univ : Finset Col).card := by simpa [← card] using six
    have inj : Function.Injective cols := by
      apply Set.injOn_univ.mp
      simpa using (Finset.card_image_iff.mp eqCard)
    exact Or.inr (choice_gives_orbit cols ⟨n,lt⟩ inj (fun j => all _ (has j)))

theorem encode (z : Set Cell) : ∃ cols : Col → Pat, z = cells cols := by
  classical
  let code (j : Col) := BitVec.ofBoolListLE
    [decide ((0,j) ∈ z),decide ((1,j) ∈ z),decide ((2,j) ∈ z),
     decide ((3,j) ∈ z),decide ((4,j) ∈ z)]
  refine ⟨fun j => (code j).toFin, ?_⟩
  ext ⟨i,j⟩
  change (i,j) ∈ z ↔ (code j).getLsbD i.val = true
  simp only [code,BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> simp [List.getD]

end Atlas56
