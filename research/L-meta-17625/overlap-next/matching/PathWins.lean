import PathPhysical
import PathPromotion

namespace PathWins
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PathBits PathSearch PathPhysical

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The explicit target mask represents the three consecutive edges. -/
theorem target_bit : ∀ r : Fin 16, target.getLsbD r = true ↔
    ∃ j : Fin 3, r.val.testBit j.castSucc.val = true ∧ r.val.testBit j.succ.val = true := by decide

private theorem signal_bit (e : Fin 4 → Fin n) (C : Circuit) (h : ℕ) (r : Fin 16) :
    (gate e C h).2.value.getLsbD r = gateVal n C h (assignment e r) := by
  change (signal e C (n+h)).getLsbD r = _
  simp only [signal,get_pack,gateVal_eq_val]

private theorem safe_of_bits (w : BitVec 16)
    (safe : ∀ r : Fin 16, w.getLsbD r = true → target.getLsbD r = true) :
    (w &&& ~~~target) = 0 := by
  apply bit_ext
  intro r
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and]
  cases h : w.getLsbD r
  · simp
  · simp [safe r h]

private theorem bit_of_safe {w : BitVec 16} (safe : (w &&& ~~~target) = 0)
    (r : Fin 16) (on : w.getLsbD r = true) : target.getLsbD r = true := by
  have bit := congrArg (fun b : BitVec 16 => b.getLsbD r) safe
  simpa [BitVec.getLsbD_and, BitVec.getLsbD_not, on, r.isLt] using bit

/-- The list of actual exceptional gates on the path has a covering selection.
Other eligible gates can safely be added: each is checked against the same mask. -/
theorem wins (least : IsLeastAO G C) (e : Fin 4 → Fin n) (inj : Function.Injective e)
    (W : PathGeometry.Witness G C e) :
    PathSearch.wins ((activePrefix G C C.gates.length).map (gate e C)) = true := by
  classical
  obtain ⟨K,shape,correct⟩ := PathPromotion.separate least e W
  have spec (r : Fin 16) : (∃ h ∈ K, gateVal n C h (assignment e r) = true) ↔ target.getLsbD r = true := by
    rw [target_bit,correct]
    · simp only [at_vertex inj]
    · intro v on
      obtain ⟨j,eq,_⟩ := of_decide_eq_true on
      exact ⟨j,eq.symm⟩
  apply wins_of_cover
  intro i hi
  let r : Fin 16 := ⟨i,hi⟩
  change target.getLsbD r = true ↔ _
  constructor
  · intro positive
    obtain ⟨h,m,yes⟩ := (spec r).mpr positive
    obtain ⟨active,ex,op,nonempty,disjoint⟩ := shape h m
    have mem : h ∈ activePrefix G C C.gates.length := mem_prefix.mpr ⟨(orData ex).1,active⟩
    have raw_zero : raw e (orIn n C (n+h)) = 0 := by
      apply bit_ext; intro j; simp only [raw,get_pack,decide_eq_false (disjoint j)]; simp
    refine ⟨_,List.mem_map.mpr ⟨h,mem,rfl⟩,?_,?_,raw_zero,?_,?_⟩
    · simp [gate,kind,op]
    · simp [gate,wire,nonempty]
    · apply safe_of_bits
      intro q on
      exact (spec q).mp ⟨h,m,(signal_bit e C h q).symm ▸ on⟩
    · exact (signal_bit e C h r).symm ▸ yes
  · rintro ⟨g,_,_,_,_,safe,on⟩
    exact bit_of_safe safe r on

#print axioms wins
end PathWins
