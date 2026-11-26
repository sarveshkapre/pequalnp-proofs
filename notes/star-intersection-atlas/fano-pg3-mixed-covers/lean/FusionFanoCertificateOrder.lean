import FusionFanoCertificateData

namespace FusionFanoCertificates

private theorem natOrLeftComm (a b c : Nat) : a ||| (b ||| c) = b ||| (a ||| c) := by
  rw [← Nat.or_assoc, Nat.or_comm a b, Nat.or_assoc]

/-- Symmetry of weights and cube unions reduces checking to increasing triples. -/
theorem good_of_ascending (c : Case) (h : GoodAsc c) : Good c := by
  refine ⟨h.1, ?_⟩
  intro i j k hij hik hjk
  have hji := weights_symm c j i
  have hki := weights_symm c k i
  have hkj := weights_symm c k j
  have orders :
      (i < j ∧ j < k) ∨ (i < k ∧ k < j) ∨
      (j < i ∧ i < k) ∨ (j < k ∧ k < i) ∨
      (k < i ∧ i < j) ∨ (k < j ∧ j < i) := by omega
  rcases orders with hlt | hlt | hlt | hlt | hlt | hlt
  · exact h.2 i j k hlt.1 hlt.2
  · simpa only [hji,hki,hkj,Nat.or_assoc,Nat.or_comm,natOrLeftComm,
      add_assoc,add_comm,add_left_comm,and_assoc,and_comm,and_left_comm]
      using h.2 i k j hlt.1 hlt.2
  · simpa only [hji,hki,hkj,Nat.or_assoc,Nat.or_comm,natOrLeftComm,
      add_assoc,add_comm,add_left_comm,and_assoc,and_comm,and_left_comm]
      using h.2 j i k hlt.1 hlt.2
  · simpa only [hji,hki,hkj,Nat.or_assoc,Nat.or_comm,natOrLeftComm,
      add_assoc,add_comm,add_left_comm,and_assoc,and_comm,and_left_comm]
      using h.2 j k i hlt.1 hlt.2
  · simpa only [hji,hki,hkj,Nat.or_assoc,Nat.or_comm,natOrLeftComm,
      add_assoc,add_comm,add_left_comm,and_assoc,and_comm,and_left_comm]
      using h.2 k i j hlt.1 hlt.2
  · simpa only [hji,hki,hkj,Nat.or_assoc,Nat.or_comm,natOrLeftComm,
      add_assoc,add_comm,add_left_comm,and_assoc,and_comm,and_left_comm]
      using h.2 k j i hlt.1 hlt.2

#print axioms good_of_ascending

end FusionFanoCertificates
