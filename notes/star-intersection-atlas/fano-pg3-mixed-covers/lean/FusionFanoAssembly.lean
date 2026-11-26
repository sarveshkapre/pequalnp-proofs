import FusionCube
import FusionFanoCertificateData
import FusionWeightedObstruction

namespace FusionFanoAssembly

open FusionProfiles FusionCube FusionFanoCertificates FusionWeightedObstruction
open scoped BigOperators

/-- A checked pair-weight certificate contradicts a local profile model of a
seven-point Steiner triple incidence system, independently of enumeration. -/
theorem local_profile_false_of_certificate
    {L : Type*} [Fintype L] (G : Fin 7 → L → Prop) [DecidableRel G]
    (triples : ∀ c, ∃ i j k : Fin 7,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ∀ r, G r c ↔ r = i ∨ r = j ∨ r = k)
    (joining : ∀ p q, p ≠ q → ∃! l, G p l ∧ G q l)
    (rwds : Fin 7 → Word 3) (cwds : L → Word 3)
    (hlocal : LocalProfileCondition G rwds cwds)
    (cert : Case) (hg : Good cert) (e : Fin 7 ≃ Fin 7)
    (he : ∀ r, rows cert (e r) = encode (rwds r)) : False := by
  classical
  let w : Fin 7 → Fin 7 → ℤ := fun r s => weights cert (e r) (e s)
  have hdiag : ∀ r, w r r = 0 := fun r => weights_diag cert (e r)
  have hsymm : ∀ r s, w r s = w s r := fun r s => weights_symm cert (e r) (e s)
  have hpositive : 0 < ∑ r, ∑ s, w r s := by
    dsimp [w]
    have heq : (∑ r, ∑ s, weights cert (e r) (e s)) =
        ∑ i, ∑ j, weights cert i j := by
      calc
        _ = ∑ r, ∑ j, weights cert (e r) j := by
          apply Finset.sum_congr rfl
          intro r _
          exact Equiv.sum_comp e (fun j => weights cert (e r) j)
        _ = _ := Equiv.sum_comp e (fun i => ∑ j, weights cert i j)
    rw [heq]
    exact hg.1
  apply no_pair_weight_certificate G w hdiag joining hpositive
  intro c
  obtain ⟨i,j,k,hij,hik,hjk,hline⟩ := triples c
  rw [lineWeight_three G w hdiag hsymm c i j k hij hik hjk hline]
  have ht : w i j + w i k + w j k ≤ 0 := by
    by_contra hn
    have hp : 0 < weights cert (e i) (e j) + weights cert (e i) (e k) +
        weights cert (e j) (e k) := by
      change 0 < w i j + w i k + w j k
      omega
    obtain ⟨s,hs,hmeets⟩ := local_column_star hlocal c i j k hline
    have hs' : s ∈ stars (safe (rows cert (e i)) (rows cert (e j)) (rows cert (e k))) := by
      simpa only [he] using hs
    obtain ⟨a,hai,haj,hak,ha⟩ := hg.2 (e i) (e j) (e k)
      (fun h => hij (e.injective h)) (fun h => hik (e.injective h))
      (fun h => hjk (e.injective h)) hp s hs'
    have hout : ¬ G (e.symm a) c := by
      intro h
      rcases (hline _).1 h with h | h | h
      · exact hai (by simpa using congrArg e h)
      · exact haj (by simpa using congrArg e h)
      · exact hak (by simpa using congrArg e h)
    have hm := hmeets (e.symm a) hout
    have he' : rows cert a = encode (rwds (e.symm a)) := by
      simpa using he (e.symm a)
    rw [← he', Nat.and_comm] at hm
    exact hm ha
  omega

#print axioms local_profile_false_of_certificate

end FusionFanoAssembly
