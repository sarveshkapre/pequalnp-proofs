import FusionProfiles
import FusionAntichainEnum
import FusionCube
import FusionFanoEnumeration

/-!
Relabel an arbitrary injective family by its increasing code order. A complete
pruned enumeration then supplies a certificate case and a permutation of the
original row labels. This step uses no unproved symmetry reduction.
-/
namespace FusionProfileRelabel

open FusionProfiles FusionAntichainEnum

theorem sort_sublist_finRange {m : Nat} (S : Finset (Fin m)) :
    S.sort.Sublist (List.finRange m) := by
  have heq : S.sort = (List.finRange m).filter (fun x => decide (x ∈ S)) := by
    apply S.sortedLT_sort.eq_of_mem_iff
      (((List.sortedLT_finRange m).pairwise.filter _).sortedLT)
    intro x
    simp
  rw [heq]
  exact List.filter_sublist

theorem sorted_image_mem {n m : Nat} (f : Fin n → Fin m)
    (hinj : Function.Injective f) (rel : Fin m → Fin m → Bool)
    (hrel : ∀ i j, i ≠ j → rel (f i) (f j) = true) :
    (Finset.univ.image f).sort ∈ chooseCompatible rel n (List.finRange m) := by
  classical
  apply chooseCompatible_complete rel
  · simp [Finset.card_image_of_injective _ hinj]
  · exact sort_sublist_finRange _
  · apply ((Finset.univ.image f).sort_nodup (· ≤ ·)).imp_of_mem
    intro a b ha hb hab
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp
      ((Finset.mem_sort (· ≤ ·)).mp ha)
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp
      ((Finset.mem_sort (· ≤ ·)).mp hb)
    exact hrel i j (fun hij => hab (congrArg f hij))

theorem relabel_of_mem {α : Type*} {n : Nat} (f g : Fin n → α)
    (hinj : Function.Injective f)
    (hmem : ∀ i, f i ∈ List.ofFn g) :
    ∃ e : Fin n ≃ Fin n, ∀ i, g (e i) = f i := by
  classical
  have hpre : ∀ i, ∃ j, g j = f i := by
    intro i
    exact List.mem_ofFn.mp (hmem i)
  choose p hp using hpre
  have hp_inj : Function.Injective p := by
    intro i j hij
    apply hinj
    rw [← hp i, ← hp j, hij]
  let e : Fin n ≃ Fin n := Equiv.ofBijective p
    ⟨hp_inj, (Finite.injective_iff_surjective).mp hp_inj⟩
  exact ⟨e,hp⟩

theorem enumeration_relabels {α : Type*} {n m : Nat}
    (f : Fin n → Fin m) (hinj : Function.Injective f)
    (rel : Fin m → Fin m → Bool)
    (hrel : ∀ i j, i ≠ j → rel (f i) (f j) = true)
    (cases : List α) (rows : α → Fin n → Fin m)
    (henum : cases.map (fun c => List.ofFn (rows c)) =
      chooseCompatible rel n (List.finRange m)) :
    ∃ c ∈ cases, ∃ e : Fin n ≃ Fin n, ∀ i, rows c (e i) = f i := by
  classical
  have hmem := sorted_image_mem f hinj rel hrel
  rw [← henum] at hmem
  obtain ⟨c,hc,hrows⟩ := List.mem_map.mp hmem
  refine ⟨c,hc,?_⟩
  apply relabel_of_mem f (rows c) hinj
  intro i
  rw [hrows]
  simp

theorem row_antichain_certificate (rowWords : Fin 7 → Word 3)
    (h : RowAntichain rowWords) :
    ∃ c ∈ FusionFanoCertificates.cases, ∃ e : Fin 7 ≃ Fin 7,
      ∀ r, FusionFanoCertificates.rows c (e r) = FusionCube.encode (rowWords r) := by
  refine enumeration_relabels (fun r => FusionCube.encode (rowWords r))
    (FusionCube.encode_injective.comp h.injective)
    (fun a b => decide
      (¬ Refines (FusionCube.decode a) (FusionCube.decode b) ∧
       ¬ Refines (FusionCube.decode b) (FusionCube.decode a))) ?_
    FusionFanoCertificates.cases FusionFanoCertificates.rows
    FusionFanoCertificates.cases_enumerate
  intro i j hij
  simp only [FusionCube.decode_encode, decide_eq_true_eq]
  exact ⟨h i j hij,h j i hij.symm⟩

#print axioms sorted_image_mem
#print axioms relabel_of_mem
#print axioms enumeration_relabels
#print axioms row_antichain_certificate

end FusionProfileRelabel
