import PEqualNP.ThreeGateGain.FiniteV10P004

namespace GainFinite.F10
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n400 : fastVisit (leafCols 10 bank) [14,1] ⟨134213110,[57517266,18468]⟩ b14 = true := by decide +kernel

theorem n401 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b13 = true := join_live n399 n400

theorem n402 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b12 = true := join_dead n401 (by decide +kernel)

theorem n403 : fastVisit (leafCols 10 bank) [12,1] ⟨134203876,[57508032,18468]⟩ b12 = true := by decide +kernel

theorem n404 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b11 = true := join_live n402 n403

theorem n405 : fastVisit (leafCols 10 bank) [11,1] ⟨134180278,[57484434,149796]⟩ b11 = true := by decide +kernel

theorem n406 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b10 = true := join_live n404 n405

theorem n407 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b9 = true := join_dead n406 (by decide +kernel)

theorem n408 : fastVisit (leafCols 10 bank) [9,1] ⟨134105380,[57409536,149796]⟩ b9 = true := by decide +kernel

theorem n409 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b8 = true := join_live n407 n408

theorem n410 : fastVisit (leafCols 10 bank) [8,1] ⟨117145022,[40449178,68290820]⟩ b8 = true := by decide +kernel

theorem n411 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b7 = true := join_live n409 n410

theorem n412 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b6 = true := join_dead n411 (by decide +kernel)

theorem n413 : fastVisit (leafCols 10 bank) [6,1] ⟨82999612,[6303768,68290820]⟩ b6 = true := by decide +kernel

theorem n414 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b5 = true := join_live n412 n413

theorem n415 : fastVisit (leafCols 10 bank) [5,1] ⟨131853814,[55157970,9455652]⟩ b6 = true := by decide +kernel

theorem n416 : fastVisit (leafCols 10 bank) [6,5,1] ⟨133955070,[2101256,50955458,1050628]⟩ b6 = true := by decide +kernel

theorem n417 : fastVisit (leafCols 10 bank) [5,1] ⟨131853814,[55157970,9455652]⟩ b5 = true := join_live n415 n416

theorem n418 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b4 = true := join_live n414 n417

theorem n419 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b3 = true := join_dead n418 (by decide +kernel)

theorem n420 : fastVisit (leafCols 10 bank) [3,1] ⟨127125988,[50430144,9455652]⟩ b8 = true := by decide +kernel

theorem n421 : fastVisit (leafCols 10 bank) [8,3,1] ⟨133955070,[6829082,16810048,1050628]⟩ b8 = true := by decide +kernel

theorem n422 : fastVisit (leafCols 10 bank) [3,1] ⟨127125988,[50430144,9455652]⟩ b7 = true := join_live n420 n421

theorem n423 : fastVisit (leafCols 10 bank) [3,1] ⟨127125988,[50430144,9455652]⟩ b6 = true := join_dead n422 (by decide +kernel)

theorem n424 : fastVisit (leafCols 10 bank) [6,3,1] ⟨133429756,[6303768,50430144,1050628]⟩ b6 = true := by decide +kernel

theorem n425 : fastVisit (leafCols 10 bank) [3,1] ⟨127125988,[50430144,9455652]⟩ b5 = true := join_live n423 n424

theorem n426 : fastVisit (leafCols 10 bank) [3,1] ⟨127125988,[50430144,9455652]⟩ b4 = true := join_dead n425 (by decide +kernel)

theorem n427 : fastVisit (leafCols 10 bank) [3,1] ⟨127125988,[50430144,9455652]⟩ b3 = true := join_dead n426 (by decide +kernel)

theorem n428 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b2 = true := join_live n419 n427

theorem n429 : fastVisit (leafCols 10 bank) [2,1] ⟨115043766,[38347922,76695844]⟩ b3 = true := by decide +kernel

theorem n430 : fastVisit (leafCols 10 bank) [3,2,1] ⟨131853814,[16810048,4727826,9455652]⟩ b3 = true := by decide +kernel

theorem n431 : fastVisit (leafCols 10 bank) [2,1] ⟨115043766,[38347922,76695844]⟩ b2 = true := join_live n429 n430

theorem n432 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b1 = true := join_live n428 n431

theorem n433 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b0 = true := join_live n371 n432

theorem passed : quickHost 10 = true := by
  rw [← leafHost_sparse]
  have pool_correct : sparseRows 10 = bank := by decide +kernel
  rw [pool_correct]
  exact n433

end GainFinite.F10
