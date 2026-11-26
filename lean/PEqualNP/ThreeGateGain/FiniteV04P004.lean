import PEqualNP.ThreeGateGain.FiniteV04P003

namespace GainFinite.F4
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n320 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [] ⟨0,[]⟩ b45 = true := join_live n318 n319

theorem n321 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b14 = true := enterColumns 4 bank [4,2,1] ⟨26624,[2048,8192,16384]⟩ b14 b45 (by decide +kernel) (by decide +kernel) n320

theorem n322 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b13 = true := join_dead n321 (by decide +kernel)

theorem n323 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b12 = true := join_dead n322 (by decide +kernel)

theorem n324 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b11 = true := join_dead n323 (by decide +kernel)

theorem n325 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b10 = true := join_dead n324 (by decide +kernel)

theorem n326 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b9 = true := join_dead n325 (by decide +kernel)

theorem n327 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b8 = true := join_dead n326 (by decide +kernel)

theorem n328 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [] ⟨0,[]⟩ b56 = true := by decide +kernel

theorem n329 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [5] ⟨19456,[19456]⟩ b56 = true := by decide +kernel

theorem n330 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [] ⟨0,[]⟩ b55 = true := join_live n328 n329

theorem n331 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [4] ⟨2048,[2048]⟩ b55 = true := by decide +kernel

theorem n332 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [] ⟨0,[]⟩ b54 = true := join_live n330 n331

theorem n333 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b56 = true := by decide +kernel

theorem n334 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [5,3] ⟨31744,[3072,12288]⟩ b56 = true := by decide +kernel

theorem n335 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b55 = true := join_live n333 n334

theorem n336 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [4,3] ⟨30720,[2048,28672]⟩ b55 = true := by decide +kernel

theorem n337 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b54 = true := join_live n335 n336

theorem n338 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [] ⟨0,[]⟩ b53 = true := join_live n332 n337

theorem n339 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [2] ⟨8192,[8192]⟩ b53 = true := by decide +kernel

theorem n340 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [] ⟨0,[]⟩ b52 = true := join_live n338 n339

theorem n341 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [1] ⟨16384,[16384]⟩ b52 = true := by decide +kernel

theorem n342 : fastVisit (leafFrame 4 [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩) [] ⟨0,[]⟩ b51 = true := join_live n340 n341

theorem n343 : fastVisit (leafCols 4 bank) [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩ b14 = true := enterColumns 4 bank [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩ b14 b51 (by decide +kernel) (by decide +kernel) n342

theorem n344 : fastVisit (leafCols 4 bank) [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩ b13 = true := join_dead n343 (by decide +kernel)

theorem n345 : fastVisit (leafCols 4 bank) [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩ b12 = true := join_dead n344 (by decide +kernel)

theorem n346 : fastVisit (leafCols 4 bank) [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩ b11 = true := join_dead n345 (by decide +kernel)

theorem n347 : fastVisit (leafCols 4 bank) [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩ b10 = true := join_dead n346 (by decide +kernel)

theorem n348 : fastVisit (leafCols 4 bank) [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩ b9 = true := join_dead n347 (by decide +kernel)

theorem n349 : fastVisit (leafCols 4 bank) [8,4,2,1] ⟨26752,[128,2048,8192,16384]⟩ b8 = true := join_dead n348 (by decide +kernel)

theorem n350 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b7 = true := join_live n327 n349

theorem n351 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b6 = true := join_dead n350 (by decide +kernel)

theorem n352 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b5 = true := join_dead n351 (by decide +kernel)

theorem n353 : fastVisit (leafCols 4 bank) [4,2,1] ⟨26624,[2048,8192,16384]⟩ b4 = true := join_dead n352 (by decide +kernel)

theorem n354 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b3 = true := join_live n309 n353

theorem n355 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b2 = true := join_dead n354 (by decide +kernel)

theorem n356 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b1 = true := join_live n276 n355

theorem n357 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b0 = true := join_live n210 n356

theorem passed : quickHost 4 = true := by
  rw [← leafHost_sparse]
  have pool_correct : sparseRows 4 = bank := by decide +kernel
  rw [pool_correct]
  exact n357

end GainFinite.F4
