import PEqualNP.ThreeGateGain.FiniteV12P006

namespace GainFinite.F12
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n560 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b19 = true := join_dead n559 (by decide +kernel)

theorem n561 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b18 = true := join_dead n560 (by decide +kernel)

theorem n562 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b17 = true := join_dead n561 (by decide +kernel)

theorem n563 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b16 = true := join_dead n562 (by decide +kernel)

theorem n564 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b15 = true := join_live n551 n563

theorem n565 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b14 = true := join_dead n564 (by decide +kernel)

theorem n566 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b13 = true := join_dead n565 (by decide +kernel)

theorem n567 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b12 = true := join_dead n566 (by decide +kernel)

theorem n568 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b11 = true := join_dead n567 (by decide +kernel)

theorem n569 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b10 = true := join_dead n568 (by decide +kernel)

theorem n570 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b9 = true := join_dead n569 (by decide +kernel)

theorem n571 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b8 = true := join_dead n570 (by decide +kernel)

theorem n572 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b7 = true := join_dead n571 (by decide +kernel)

theorem n573 : fastVisit (leafCols 12 bank) [7,4,2,1] ⟨33481720,[524408,4202624,131072,262144]⟩ b7 = true := by decide +kernel

theorem n574 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b6 = true := join_live n572 n573

theorem n575 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b5 = true := join_dead n574 (by decide +kernel)

theorem n576 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b4 = true := join_dead n575 (by decide +kernel)

theorem n577 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b3 = true := join_live n550 n576

theorem n578 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b2 = true := join_dead n577 (by decide +kernel)

theorem n579 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b1 = true := join_live n491 n578

theorem n580 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b0 = true := join_live n390 n579

theorem passed : quickHost 12 = true := by
  rw [← leafHost_sparse]
  have pool_correct : sparseRows 12 = bank := by decide +kernel
  rw [pool_correct]
  exact n580

end GainFinite.F12
