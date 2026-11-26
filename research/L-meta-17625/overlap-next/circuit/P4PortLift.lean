import PathSearchDefs

namespace P4PortLift
open PathSearch

variable {A : Type*}

/-- OR of the selected earlier wire values, retaining each wire's physical key. -/
def selectedValue (xs : List A) (gate : A → Gate) (keep : A → Bool) : BitVec 16 :=
  match xs with
  | [] => 0
  | i :: is => (if keep i then (gate i).2.value else 0) ||| selectedValue is gate keep

theorem selected_bit (xs : List A) (gate : A → Gate) (keep : A → Bool) (b : ℕ) :
    (selectedValue xs gate keep).getLsbD b = true ↔
      ∃ i ∈ xs, keep i = true ∧ (gate i).2.value.getLsbD b = true := by
  induction xs with
  | nil => simp [selectedValue]
  | cons i is ih =>
    cases hi : keep i <;> simp [selectedValue,hi,ih]

private theorem carry (xs : List A) (gate : A → Gate) (keep : A → Bool)
    (r : BitVec 4) (rThin : thin r = true)
    (eligible : ∀ i ∈ xs, keep i = true →
      (gate i).1 = true ∧ (gate i).2.nz = true ∧ r ||| (gate i).2.raw = r)
    (available : List Wire) (v : BitVec 16) (mem : (⟨v,r,true⟩ : Wire) ∈ available) :
    (⟨v ||| selectedValue xs gate keep,r,true⟩ : Wire) ∈
      (xs.map gate).foldl extendOrdinary available := by
  induction xs generalizing available v with
  | nil => simpa [selectedValue] using mem
  | cons i is ih =>
    have rest (j) (mj : j ∈ is) := eligible j (List.mem_cons_of_mem _ mj)
    simp only [List.map_cons,List.foldl_cons]
    cases keepI : keep i
    · have avail : (⟨v,r,true⟩ : Wire) ∈ extendOrdinary available (gate i) := by
        unfold extendOrdinary; split <;> simp [mem]
      simpa [selectedValue,keepI] using ih rest _ v avail
    · obtain ⟨op,nz,mask⟩ := eligible i (by simp) keepI
      have mergeEq : merge ⟨v,r,true⟩ (gate i).2 = ⟨v ||| (gate i).2.value,r,true⟩ := by simp [merge,mask]
      have avail : (⟨v ||| (gate i).2.value,r,true⟩ : Wire) ∈ extendOrdinary available (gate i) := by
        simp only [extendOrdinary,op,nz,Bool.and_self,ite_true,List.mem_append]
        right
        exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_,mem,mergeEq⟩,rThin⟩
      simpa [selectedValue,keepI,BitVec.or_assoc] using ih rest _ _ avail

/-- A literal, together with any selection of earlier nonempty exceptional ORs
whose raw masks fit inside that same literal, is an allowed enumerated port. -/
theorem selected_port (xs : List A) (gate : A → Gate) (keep : A → Bool) (base : Wire)
    (baseMem : base ∈ single) (baseNZ : base.nz = true) (baseThin : thin base.raw = true)
    (eligible : ∀ i ∈ xs, keep i = true →
      (gate i).1 = true ∧ (gate i).2.nz = true ∧ base.raw ||| (gate i).2.raw = base.raw) :
    (⟨base.value ||| selectedValue xs gate keep,base.raw,true⟩ : Wire) ∈ ports (xs.map gate) := by
  have avail : (⟨base.value,base.raw,true⟩ : Wire) ∈ single := by simpa [←baseNZ] using baseMem
  have h := carry xs gate keep base.raw baseThin eligible single base.value avail
  simpa only [ports,List.mem_eraseDups,List.mem_append] using (Or.inr h :
    (⟨base.value ||| selectedValue xs gate keep,base.raw,true⟩ : Wire) ∈ (xs.map gate).map Prod.snd ∨ _)

theorem direct_port (xs : List A) (gate : A → Gate) {i : A} (hi : i ∈ xs) :
    (gate i).2 ∈ ports (xs.map gate) := by
  simp only [ports, List.mem_eraseDups, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,rfl⟩)

#print axioms selected_port
end P4PortLift
