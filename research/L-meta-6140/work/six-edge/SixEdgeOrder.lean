import SixEdgeCircuit

namespace SixEdge

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- A wire is raw-only when no dirty AND is reachable through OR gates. -/
def rawOnly (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ¬ ∃ j ∈ junk G C, Relation.ReflTransGen (OrStep n C) w (n+j)

theorem dirty_not_rawOnly {j : ℕ} (h : j ∈ junk G C) : ¬ rawOnly G C (n+j) :=
  fun h₀ => h₀ ⟨j, h, .refl⟩

theorem rawOnly_reaches {u v : ℕ} (h : rawOnly G C u)
    (path : Relation.ReflTransGen (OrStep n C) u v) : rawOnly G C v := by
  rintro ⟨j, hj, p⟩
  exact h ⟨j, hj, path.trans p⟩

/-- A raw-only promotion contributes no new truth value to a top operand. -/
theorem rawOnly_port_redundant (ao : IsAO2 n C) (top : TopForm G C)
    {a g : ℕ} (ht : a ∈ tops G C) (b : Fin 2) {x : Fin n → Bool}
    (pure : rawOnly G C (n+g))
    (reach : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+g))
    (on : gateVal n C g x = true) :
    ∃ t ∈ side (n := n) C a b, x t = true := by
  obtain ⟨w, path, fires, input | ⟨j, jl, eq, notOr⟩⟩ :=
    or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) (n+g) on
  · let t : Fin n := ⟨w, input⟩
    exact ⟨t, reach_mem_orIn t (reach.trans path), (val_ofFn C x t).symm.trans fires⟩
  · rw [eq] at path
    have ja : (gateAt C j).op = GateOp.and := by
      rcases ao.1 _ (gateAt_mem jl) with h | h
      · exact h
      · exact (notOr h).elim
    have data := topData ht
    have dirty := operandOrAndJunk ao top data.1 data.2.1
      (reach_orReaches (reach.trans path) j rfl jl) ja
    exact (pure ⟨j, dirty, path⟩).elim

/-- When sorting, raw-only ORs move to the front. Inside each class the key
    preserves the original order. -/
def stageKey (raw : Fin 5 → Bool) (i : Fin 5) : ℕ :=
  i.val + if raw i then 0 else 5

theorem key_injective (raw : Fin 5 → Bool) : Function.Injective (stageKey raw) := by
  intro a b eq
  unfold stageKey at eq
  by_cases ha : raw a = true <;> by_cases hb : raw b = true <;>
    simp [ha, hb] at eq <;> apply Fin.ext <;> omega

theorem key_keeps_reads (raw : Fin 5 → Bool) {i j : Fin 5}
    (earlier : i < j) (closure : raw j = true → raw i = true) :
    stageKey raw i < stageKey raw j := by
  unfold stageKey
  by_cases hj : raw j = true
  · simp [hj, closure hj, earlier]
  · by_cases hi : raw i = true <;> simp [hj, hi] <;> omega

theorem key_puts_raw_first (raw : Fin 5 → Bool) {i j : Fin 5}
    (hi : raw i = true) (hj : raw j = false) : stageKey raw i < stageKey raw j := by
  simp [stageKey, hi, hj]
  omega

noncomputable def reordered (raw : Fin 5 → Bool) : Fin 5 ≃ Fin 5 := by
  let ks := (Finset.univ : Finset (Fin 5)).image (stageKey raw)
  have card : ks.card = 5 := by
    simp only [ks, Finset.card_image_of_injective _ (key_injective raw)]
    decide
  let f : Fin 5 → ↥ks := fun i => ⟨stageKey raw i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have inj : Function.Injective f := fun _ _ eq => key_injective raw (congrArg Subtype.val eq)
  have surj : Function.Surjective f := by
    intro a
    obtain ⟨i, _, eq⟩ := Finset.mem_image.mp a.property
    exact ⟨i, Subtype.ext eq⟩
  exact (Equiv.ofBijective f ⟨inj, surj⟩).trans (ks.orderIsoOfFin card).symm.toEquiv

theorem reordered_lt (raw : Fin 5 → Bool) (i j : Fin 5) :
    reordered raw i < reordered raw j ↔ stageKey raw i < stageKey raw j := by
  unfold reordered
  exact OrderIso.lt_iff_lt _

theorem reordered_keeps_reads (raw : Fin 5 → Bool) {i j : Fin 5}
    (earlier : i < j) (closure : raw j = true → raw i = true) :
    reordered raw i < reordered raw j :=
  (reordered_lt _ _ _).mpr (key_keeps_reads _ earlier closure)

theorem reordered_puts_raw_first (raw : Fin 5 → Bool) {i j : Fin 5}
    (hi : raw i = true) (hj : raw j = false) :
    reordered raw i < reordered raw j :=
  (reordered_lt _ _ _).mpr (key_puts_raw_first _ hi hj)

#print axioms reordered_keeps_reads

end SixEdge
