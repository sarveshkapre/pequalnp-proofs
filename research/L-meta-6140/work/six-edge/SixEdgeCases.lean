import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace SixEdge

/-- The first mask marks the dirty ANDs. The second marks exceptional ORs
    used on the singleton side of at least one top AND. -/
abbrev Case := BitVec 5 × BitVec 5

def dirtySlots (mask : BitVec 5) : Finset (Fin 5) :=
  Finset.univ.filter fun i => mask.getLsbD i

def allowed (k : Case) : Prop :=
  (dirtySlots k.1).card = 2 ∧ k.1.getLsbD 4 = false ∧
    ∀ i : Fin 5, k.2.getLsbD i = true →
      k.1.getLsbD i = false ∧ ∃ j : Fin 5, j < i ∧ k.1.getLsbD j = true

instance (k : Case) : Decidable (allowed k) := by unfold allowed; infer_instance

def cases : List Case :=
  [(3,0), (3,4), (3,8), (3,12), (3,16), (3,20), (3,24), (3,28),
   (5,0), (5,2), (5,8), (5,10), (5,16), (5,18), (5,24), (5,26),
   (9,0), (9,2), (9,4), (9,6), (9,16), (9,18), (9,20), (9,22),
   (6,0), (6,8), (6,16), (6,24),
   (10,0), (10,4), (10,16), (10,20),
   (12,0), (12,16)]

theorem cases_length : cases.length = 34 := by decide

theorem cases_nodup : cases.Nodup := by decide

private theorem index_check :
    ∀ a b : Fin 32, allowed (⟨a⟩, ⟨b⟩) ↔ (⟨a⟩, ⟨b⟩) ∈ cases := by
  decide

theorem mem_cases_iff (k : Case) : k ∈ cases ↔ allowed k := by
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := k
  exact (index_check a b).symm

def ofSlots (p : Fin 5 → Bool) : BitVec 5 :=
  BitVec.ofBoolListLE [p 0, p 1, p 2, p 3, p 4]

@[simp] theorem ofSlots_bit (p : Fin 5 → Bool) (i : Fin 5) :
    (ofSlots p).getLsbD i = p i := by
  fin_cases i <;>
    simp [ofSlots, BitVec.ofBoolListLE]

theorem covers (isDirty feedsCenter : Fin 5 → Bool)
    (two : (Finset.univ.filter fun i => isDirty i = true).card = 2)
    (last : isDirty 4 = false)
    (route : ∀ i, feedsCenter i = true →
      isDirty i = false ∧ ∃ j, j < i ∧ isDirty j = true) :
    (ofSlots isDirty, ofSlots feedsCenter) ∈ cases := by
  apply (mem_cases_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have eq : dirtySlots (ofSlots isDirty) = Finset.univ.filter fun i => isDirty i = true := by
      ext i
      simp only [dirtySlots, Finset.mem_filter, ofSlots_bit]
    rwa [eq]
  · exact (ofSlots_bit isDirty (4 : Fin 5)).trans last
  · intro i h
    obtain ⟨off, j, lt, on⟩ := route i ((ofSlots_bit feedsCenter i).symm.trans h)
    exact ⟨(ofSlots_bit isDirty i).trans off, j, lt, (ofSlots_bit isDirty j).trans on⟩

#print axioms covers

end SixEdge
