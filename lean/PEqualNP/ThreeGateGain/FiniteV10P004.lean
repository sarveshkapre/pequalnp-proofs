import PEqualNP.ThreeGateGain.FiniteV10P003

namespace GainFinite.F10
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n320 : fastVisit (leafFrame 10 [2] ⟨38347922,[38347922]⟩) [] ⟨0,[]⟩ b43 = true := join_live n318 n319

theorem n321 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b26 = true := enterColumns 10 bank [2] ⟨38347922,[38347922]⟩ b26 b43 (by decide +kernel) (by decide +kernel) n320

theorem n322 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b25 = true := join_dead n321 (by decide +kernel)

theorem n323 : fastVisit (leafCols 10 bank) [25,2] ⟨117178302,[78830380,34078850]⟩ b25 = true := by decide +kernel

theorem n324 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b24 = true := join_live n322 n323

theorem n325 : fastVisit (leafCols 10 bank) [24,2] ⟨49020602,[10672680,34078850]⟩ b24 = true := by decide +kernel

theorem n326 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b23 = true := join_live n324 n325

theorem n327 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b22 = true := join_dead n326 (by decide +kernel)

theorem n328 : fastVisit (leafCols 10 bank) [22,2] ⟨131858422,[93510500,4718610]⟩ b22 = true := by decide +kernel

theorem n329 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b21 = true := join_live n327 n328

theorem n330 : fastVisit (leafCols 10 bank) [21,2] ⟨122421202,[84073280,4718610]⟩ b21 = true := by decide +kernel

theorem n331 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b20 = true := join_live n329 n330

theorem n332 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b19 = true := join_dead n331 (by decide +kernel)

theorem n333 : fastVisit (leafCols 10 bank) [19,2] ⟨115081142,[76733220,38273170]⟩ b19 = true := by decide +kernel

theorem n334 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b18 = true := join_live n332 n333

theorem n335 : fastVisit (leafCols 10 bank) [18,2] ⟨38534802,[186880,38273170]⟩ b18 = true := by decide +kernel

theorem n336 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b17 = true := join_live n334 n335

theorem n337 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b16 = true := join_dead n336 (by decide +kernel)

theorem n338 : fastVisit (leafCols 10 bank) [16,2] ⟨134184382,[95836460,66690]⟩ b16 = true := by decide +kernel

theorem n339 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b15 = true := join_live n337 n338

theorem n340 : fastVisit (leafCols 10 bank) [15,2] ⟨134051002,[95703080,66690]⟩ b15 = true := by decide +kernel

theorem n341 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b14 = true := join_live n339 n340

theorem n342 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b13 = true := join_dead n341 (by decide +kernel)

theorem n343 : fastVisit (leafCols 10 bank) [13,2] ⟨134213110,[95865188,9234]⟩ b13 = true := by decide +kernel

theorem n344 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b12 = true := join_live n342 n343

theorem n345 : fastVisit (leafCols 10 bank) [12,2] ⟨134194642,[95846720,9234]⟩ b12 = true := by decide +kernel

theorem n346 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b11 = true := join_live n344 n345

theorem n347 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b10 = true := join_dead n346 (by decide +kernel)

theorem n348 : fastVisit (leafCols 10 bank) [10,2] ⟨134180278,[95832356,74898]⟩ b10 = true := by decide +kernel

theorem n349 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b9 = true := join_live n347 n348

theorem n350 : fastVisit (leafCols 10 bank) [9,2] ⟨134030482,[95682560,74898]⟩ b9 = true := by decide +kernel

theorem n351 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b8 = true := join_live n349 n350

theorem n352 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b7 = true := join_dead n351 (by decide +kernel)

theorem n353 : fastVisit (leafCols 10 bank) [7,2] ⟨117145022,[78797100,34145410]⟩ b7 = true := by decide +kernel

theorem n354 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b6 = true := join_live n352 n353

theorem n355 : fastVisit (leafCols 10 bank) [6,2] ⟨48854202,[10506280,34145410]⟩ b6 = true := by decide +kernel

theorem n356 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b5 = true := join_live n354 n355

theorem n357 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b4 = true := join_dead n356 (by decide +kernel)

theorem n358 : fastVisit (leafCols 10 bank) [4,2] ⟨131853814,[93505892,4727826]⟩ b6 = true := by decide +kernel

theorem n359 : fastVisit (leafCols 10 bank) [6,4,2] ⟨133955070,[2101256,85100868,525314]⟩ b6 = true := by decide +kernel

theorem n360 : fastVisit (leafCols 10 bank) [4,2] ⟨131853814,[93505892,4727826]⟩ b5 = true := join_live n358 n359

theorem n361 : fastVisit (leafCols 10 bank) [4,2] ⟨131853814,[93505892,4727826]⟩ b4 = true := join_dead n360 (by decide +kernel)

theorem n362 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b3 = true := join_live n357 n361

theorem n363 : fastVisit (leafCols 10 bank) [3,2] ⟨122398162,[84050240,4727826]⟩ b7 = true := by decide +kernel

theorem n364 : fastVisit (leafCols 10 bank) [7,3,2] ⟨133955070,[11556908,16810048,525314]⟩ b7 = true := by decide +kernel

theorem n365 : fastVisit (leafCols 10 bank) [3,2] ⟨122398162,[84050240,4727826]⟩ b6 = true := join_live n363 n364

theorem n366 : fastVisit (leafCols 10 bank) [6,3,2] ⟨132904442,[10506280,84050240,525314]⟩ b6 = true := by decide +kernel

theorem n367 : fastVisit (leafCols 10 bank) [3,2] ⟨122398162,[84050240,4727826]⟩ b5 = true := join_live n365 n366

theorem n368 : fastVisit (leafCols 10 bank) [3,2] ⟨122398162,[84050240,4727826]⟩ b4 = true := join_dead n367 (by decide +kernel)

theorem n369 : fastVisit (leafCols 10 bank) [3,2] ⟨122398162,[84050240,4727826]⟩ b3 = true := join_dead n368 (by decide +kernel)

theorem n370 : fastVisit (leafCols 10 bank) [2] ⟨38347922,[38347922]⟩ b2 = true := join_live n362 n369

theorem n371 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b1 = true := join_live n313 n370

theorem n372 : fastVisit (leafFrame 10 [1] ⟨76695844,[76695844]⟩) [] ⟨0,[]⟩ b50 = true := by decide +kernel

theorem n373 : fastVisit (leafFrame 10 [1] ⟨76695844,[76695844]⟩) [4] ⟨127125988,[127125988]⟩ b50 = true := by decide +kernel

theorem n374 : fastVisit (leafFrame 10 [1] ⟨76695844,[76695844]⟩) [] ⟨0,[]⟩ b49 = true := join_live n372 n373

theorem n375 : fastVisit (leafFrame 10 [1] ⟨76695844,[76695844]⟩) [3] ⟨117670336,[117670336]⟩ b49 = true := by decide +kernel

theorem n376 : fastVisit (leafFrame 10 [1] ⟨76695844,[76695844]⟩) [] ⟨0,[]⟩ b48 = true := join_live n374 n375

theorem n377 : fastVisit (leafFrame 10 [1] ⟨76695844,[76695844]⟩) [1] ⟨76695844,[76695844]⟩ b48 = true := by decide +kernel

theorem n378 : fastVisit (leafFrame 10 [1] ⟨76695844,[76695844]⟩) [] ⟨0,[]⟩ b47 = true := join_live n376 n377

theorem n379 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b26 = true := enterColumns 10 bank [1] ⟨76695844,[76695844]⟩ b26 b47 (by decide +kernel) (by decide +kernel) n378

theorem n380 : fastVisit (leafCols 10 bank) [26,1] ⟨117178302,[40482458,68157700]⟩ b26 = true := by decide +kernel

theorem n381 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b25 = true := join_live n379 n380

theorem n382 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b24 = true := join_dead n381 (by decide +kernel)

theorem n383 : fastVisit (leafCols 10 bank) [24,1] ⟨83099452,[6403608,68157700]⟩ b24 = true := by decide +kernel

theorem n384 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b23 = true := join_live n382 n383

theorem n385 : fastVisit (leafCols 10 bank) [23,1] ⟨131858422,[55162578,9437220]⟩ b23 = true := by decide +kernel

theorem n386 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b22 = true := join_live n384 n385

theorem n387 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b21 = true := join_dead n386 (by decide +kernel)

theorem n388 : fastVisit (leafCols 10 bank) [21,1] ⟨127139812,[50443968,9437220]⟩ b21 = true := by decide +kernel

theorem n389 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b20 = true := join_live n387 n388

theorem n390 : fastVisit (leafCols 10 bank) [20,1] ⟨115081142,[38385298,76546340]⟩ b20 = true := by decide +kernel

theorem n391 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b19 = true := join_live n389 n390

theorem n392 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b18 = true := join_dead n391 (by decide +kernel)

theorem n393 : fastVisit (leafCols 10 bank) [18,1] ⟨76807972,[112128,76546340]⟩ b18 = true := by decide +kernel

theorem n394 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b17 = true := join_live n392 n393

theorem n395 : fastVisit (leafCols 10 bank) [17,1] ⟨134184382,[57488538,133380]⟩ b17 = true := by decide +kernel

theorem n396 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b16 = true := join_live n394 n395

theorem n397 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b15 = true := join_dead n396 (by decide +kernel)

theorem n398 : fastVisit (leafCols 10 bank) [15,1] ⟨134117692,[57421848,133380]⟩ b15 = true := by decide +kernel

theorem n399 : fastVisit (leafCols 10 bank) [1] ⟨76695844,[76695844]⟩ b14 = true := join_live n397 n398

end GainFinite.F10
