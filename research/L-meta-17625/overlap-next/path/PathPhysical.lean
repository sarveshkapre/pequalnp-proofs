import PathBits
import PathSearchDefs
import PathGeometry

namespace PathPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PathBits PathSearch
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def kind (C : Circuit) (g : ℕ) : Bool := decide ((gateAt C g).op = GateOp.or)

def wire (e : Fin 4 → Fin n) (C : Circuit) (w : ℕ) : Wire :=
  ⟨signal e C w, raw e (orIn n C w), decide (orIn n C w).Nonempty⟩

def gate (e : Fin 4 → Fin n) (C : Circuit) (g : ℕ) : PathSearch.Gate := (kind C g, wire e C (n+g))

theorem thin_lam {e : Fin 4 → Fin n} (W : PathGeometry.Witness G C e) {h : ℕ} (mem : h ∈ lam G C) :
    ((orIn n C (n+h)) ∩ Finset.univ.image e).card ≤ 1 := by
  classical
  obtain ⟨_,_,_,a,ha,b,_,reach⟩ := Finset.mem_filter.mp mem
  let J := Finset.univ.filter (fun i : Fin 4 => e i ∈ side (n := n) C a b)
  have sub : orIn n C (n+h) ∩ Finset.univ.image e ⊆ J.image e := by
    intro v m
    obtain ⟨vm,em⟩ := Finset.mem_inter.mp m
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp em
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      reach_mem_orIn _ ((orReaches_reach _ _ reach).1.trans (mem_orIn_reach _ vm))⟩,rfl⟩
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (W.thin ⟨a,ha⟩ b))

theorem or_value (ao : IsAO2 n C) {g : ℕ} (len : g < C.gates.length)
    (op : (gateAt C g).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C g x = true ↔ val C (List.ofFn x) (opnd C g 0) = true ∨
      val C (List.ofFn x) (opnd C g 1) = true := by
  change val C (List.ofFn x) (n+g) = true ↔ _
  rw [val_or (n := n) (by simp) len op]
  constructor
  · rintro ⟨w,hw,_,fire⟩
    obtain ⟨i,rfl⟩ := inputsAsOpnd ao len hw
    fin_cases i
    · exact Or.inl fire
    · exact Or.inr fire
  · rintro (h | h)
    · exact ⟨_,opndMem ao len 0,opndBound ao len 0,h⟩
    · exact ⟨_,opndMem ao len 1,opndBound ao len 1,h⟩

theorem gate_eq (e : Fin 4 → Fin n) (ao : IsAO2 n C) {g : ℕ} (len : g < C.gates.length) :
    gate e C g = (kind C g, combine (kind C g) (wire e C (opnd C g 0)) (wire e C (opnd C g 1))) := by
  refine Prod.ext ?_ ?_
  · rfl
  change wire e C (n+g) = _
  rcases ao.1 _ (gateAt_mem len) with op | op
  · have k : kind C g = false := by simp [kind,op]
    have rawZ := andRawEmpty (n := n) op
    have value_eq : signal e C (n+g) = signal e C (opnd C g 0) &&& signal e C (opnd C g 1) := by
      apply bit_ext; intro i
      simp only [signal,BitVec.getLsbD_and,get_pack]
      apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true]; exact andValBoth ao len op _
    have raw_eq : raw e ∅ = 0 := by
      apply bit_ext; intro i; simp only [raw,get_pack,Finset.notMem_empty,decide_false]; simp
    simp only [k,combine,Bool.false_eq_true,ite_false,wire,rawZ,raw_eq,value_eq]
    rfl
  · have k : kind C g = true := by simp [kind,op]
    have value_eq : signal e C (n+g) = signal e C (opnd C g 0) ||| signal e C (opnd C g 1) := by
      apply bit_ext; intro i
      simp only [signal,BitVec.getLsbD_or,get_pack]
      apply Bool.eq_iff_iff.mpr; simp only [Bool.or_eq_true]; exact or_value ao len op _
    have rawU := orRawUnion ao len op
    simp only [k,combine,ite_true,merge,wire,value_eq,rawU,raw_union]
    change _ = Wire.mk _ _ _
    congr 1
    simp [Finset.union_nonempty,side]

noncomputable def activePrefix (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) : List ℕ := by
  classical
  exact (List.range j).filter fun h => h ∈ P4Ports.active G C

@[simp] theorem mem_prefix {j h : ℕ} : h ∈ activePrefix G C j ↔ h < j ∧ h ∈ P4Ports.active G C := by
  classical
  simp [activePrefix]

theorem budget {e : Fin 4 → Fin n} (j : ℕ) (b : Bool) :
    (((activePrefix G C j).map (gate e C)).map Prod.fst).count b ≤
      (if b then (orN G C \ lam G C).card else (junk G C).card) := by
  classical
  let xs := activePrefix G C j
  let ys := xs.filter fun i => kind C i == b
  have nd : ys.Nodup := (List.nodup_range.filter _).filter _
  have count : ((xs.map (gate e C)).map Prod.fst).count b = ys.length := by
    change ((xs.map (gate e C)).map Prod.fst).count b = (xs.filter _).length
    induction xs with
    | nil => simp
    | cons h t ih =>
      simp only [List.map_cons,List.count_cons,List.filter_cons]
      change _ + (if kind C h == b then 1 else 0) = _
      split <;> simp_all
  change ((xs.map (gate e C)).map Prod.fst).count b ≤ _
  rw [count,← List.toFinset_card_of_nodup nd]
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply Finset.card_le_card
    intro h hm
    obtain ⟨mem,k⟩ := List.mem_filter.mp (List.mem_toFinset.mp hm)
    rcases Finset.mem_union.mp (mem_prefix.mp mem).2 with m|m
    · exact m
    · have hor := (orData (Finset.mem_filter.mp m).1).2.1
      simp [kind,hor] at k
  · apply Finset.card_le_card
    intro h hm
    obtain ⟨mem,k⟩ := List.mem_filter.mp (List.mem_toFinset.mp hm)
    rcases Finset.mem_union.mp (mem_prefix.mp mem).2 with m|m
    · have hand := (junkData m).2.1
      simp [kind,hand] at k
    · exact (Finset.mem_filter.mp m).1

end PathPhysical
