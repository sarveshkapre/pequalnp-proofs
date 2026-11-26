import P4Ports

namespace PathBits
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

def pack {k : ℕ} (f : Fin k → Bool) : BitVec k :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

@[simp] theorem get_pack {k : ℕ} (f : Fin k → Bool) (i : Fin k) :
    (pack f).getLsbD i = f i := by
  simp only [pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

theorem bit_ext {k : ℕ} {a b : BitVec k} (h : ∀ i : Fin k, a.getLsbD i = b.getLsbD i) : a = b :=
  BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i,hi⟩)

def raw {n} (e : Fin 4 → Fin n) (R : Finset (Fin n)) : BitVec 4 :=
  pack (fun i => decide (e i ∈ R))

def assignment {n} (e : Fin 4 → Fin n) (r : Fin 16) (v : Fin n) : Bool :=
  decide (∃ i : Fin 4, e i = v ∧ r.val.testBit i.val = true)

theorem supported {n} (e : Fin 4 → Fin n) (r : Fin 16) (v : Fin n)
    (outside : ∀ i, v ≠ e i) : assignment e r v = false := by
  simp only [assignment, decide_eq_false_iff_not]
  rintro ⟨i,eq,_⟩; exact outside i eq.symm

@[simp] theorem at_vertex {n} {e : Fin 4 → Fin n} (inj : Function.Injective e)
    (r : Fin 16) (j : Fin 4) : assignment e r (e j) = r.val.testBit j.val := by
  apply Bool.eq_iff_iff.mpr
  simp [assignment,inj.eq_iff]

def literal (mask : BitVec 4) : BitVec 16 :=
  pack (fun row => decide (∃ i : Fin 4, mask.getLsbD i = true ∧ row.val.testBit i.val = true))

theorem literal_spec {n} (e : Fin 4 → Fin n) (R : Finset (Fin n)) (r : Fin 16) :
    (literal (raw e R)).getLsbD r = true ↔ ∃ v ∈ R, assignment e r v = true := by
  simp only [literal, raw,get_pack,decide_eq_true_eq,assignment]
  constructor
  · rintro ⟨i,hi,on⟩; exact ⟨_,hi,i,rfl,on⟩
  · rintro ⟨_,hi,i,rfl,on⟩; exact ⟨i,hi,on⟩

theorem raw_sub {n} {e : Fin 4 → Fin n} {S T : Finset (Fin n)} (sub : S ⊆ T) :
    raw e T ||| raw e S = raw e T := by
  apply bit_ext
  intro i
  simp only [BitVec.getLsbD_or,raw,get_pack]
  by_cases hs : e i ∈ S
  · simp [hs, sub hs]
  · simp [hs]

theorem raw_union {n} (e : Fin 4 → Fin n) (S T : Finset (Fin n)) :
    raw e (S ∪ T) = raw e S ||| raw e T := by
  apply bit_ext
  intro i
  simp only [raw, BitVec.getLsbD_or, get_pack, Finset.mem_union]; simp

theorem thin_mask {n} {e : Fin 4 → Fin n} (inj : Function.Injective e)
    (R : Finset (Fin n)) (little : (R ∩ Finset.univ.image e).card ≤ 1) :
    raw e R ∈ ([0,1,2,4,8] : List (BitVec 4)) := by
  classical
  by_cases z : ∃ i : Fin 4, e i ∈ R
  · obtain ⟨i,hi⟩ := z
    have uniq (j : Fin 4) : e j ∈ R ↔ j = i := by
      refine ⟨fun hj => inj ?_,fun h => h ▸ hi⟩
      exact Finset.card_le_one.mp little _ (Finset.mem_inter.mpr ⟨hj,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
        _ (Finset.mem_inter.mpr ⟨hi,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    have eq : raw e R = pack (fun j => decide (j = i)) := by
      apply bit_ext; intro j; simp [raw,uniq]
    rw [eq]; fin_cases i <;> decide
  · have eq : raw e R = 0 := by
      apply bit_ext; intro j; simp only [raw, get_pack]; rw [decide_eq_false (fun h => z ⟨j,h⟩)]; simp
    simp [eq]

def signal {n} (e : Fin 4 → Fin n) (C : Circuit) (w : ℕ) : BitVec 16 :=
  pack (fun row => val C (List.ofFn (assignment e row)) w)

end PathBits
