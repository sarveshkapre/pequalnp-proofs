import PEqualNP.ThreeGateGain.FiniteV05P003

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n320 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b11 = true := join_dead n319 (by decide +kernel)

theorem n321 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b10 = true := join_dead n320 (by decide +kernel)

theorem n322 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b9 = true := join_live n309 n321

theorem n323 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b17 = true := by decide +kernel

theorem n324 : fastVisit (leafCols 5 bank) [17,9,5] ⟨522876,[636,2048,65536]⟩ b17 = true := by decide +kernel

theorem n325 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b16 = true := join_live n323 n324

theorem n326 : fastVisit (leafCols 5 bank) [16,9,5] ⟨522360,[120,2048,331776]⟩ b16 = true := by decide +kernel

theorem n327 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b15 = true := join_live n325 n326

theorem n328 : fastVisit (leafCols 5 bank) [15,9,5] ⟨523178,[938,8192,4096]⟩ b15 = true := by decide +kernel

theorem n329 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b14 = true := join_live n327 n328

theorem n330 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b13 = true := join_dead n329 (by decide +kernel)

theorem n331 : fastVisit (leafCols 5 bank) [13,9,5] ⟨523144,[904,26624,4096]⟩ b13 = true := by decide +kernel

theorem n332 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b12 = true := join_live n330 n331

theorem n333 : fastVisit (leafCols 5 bank) [12,9,5] ⟨522538,[298,8192,331776]⟩ b12 = true := by decide +kernel

theorem n334 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b11 = true := join_live n332 n333

theorem n335 : fastVisit (leafCols 5 bank) [11,9,5] ⟨522828,[588,26624,65536]⟩ b11 = true := by decide +kernel

theorem n336 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b10 = true := join_live n334 n335

theorem n337 : fastVisit (leafFrame 5 [10,9,5] ⟨522248,[8,26624,331776]⟩) [] ⟨0,[]⟩ b45 = true := by decide +kernel

theorem n338 : fastVisit (leafFrame 5 [10,9,5] ⟨522248,[8,26624,331776]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n339 : fastVisit (leafFrame 5 [10,9,5] ⟨522248,[8,26624,331776]⟩) [] ⟨0,[]⟩ b44 = true := join_live n337 n338

theorem n340 : fastVisit (leafFrame 5 [10,9,5] ⟨522248,[8,26624,331776]⟩) [1] ⟨299008,[299008]⟩ b44 = true := by decide +kernel

theorem n341 : fastVisit (leafFrame 5 [10,9,5] ⟨522248,[8,26624,331776]⟩) [] ⟨0,[]⟩ b43 = true := join_live n339 n340

theorem n342 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b18 = true := enterColumns 5 bank [10,9,5] ⟨522248,[8,26624,331776]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n341

theorem n343 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b17 = true := join_dead n342 (by decide +kernel)

theorem n344 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b16 = true := join_dead n343 (by decide +kernel)

theorem n345 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b15 = true := join_dead n344 (by decide +kernel)

theorem n346 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b14 = true := join_dead n345 (by decide +kernel)

theorem n347 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b13 = true := join_dead n346 (by decide +kernel)

theorem n348 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b12 = true := join_dead n347 (by decide +kernel)

theorem n349 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b11 = true := join_dead n348 (by decide +kernel)

theorem n350 : fastVisit (leafCols 5 bank) [10,9,5] ⟨522248,[8,26624,331776]⟩ b10 = true := join_dead n349 (by decide +kernel)

theorem n351 : fastVisit (leafCols 5 bank) [9,5] ⟨522240,[26624,331776]⟩ b9 = true := join_live n336 n350

theorem n352 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b8 = true := join_live n322 n351

theorem n353 : fastVisit (leafFrame 5 [8,5] ⟨520192,[24576,196608]⟩) [] ⟨0,[]⟩ b49 = true := by decide +kernel

theorem n354 : fastVisit (leafFrame 5 [8,5] ⟨520192,[24576,196608]⟩) [1] ⟨299008,[299008]⟩ b49 = true := by decide +kernel

theorem n355 : fastVisit (leafFrame 5 [8,5] ⟨520192,[24576,196608]⟩) [] ⟨0,[]⟩ b48 = true := join_live n353 n354

theorem n356 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b18 = true := enterColumns 5 bank [8,5] ⟨520192,[24576,196608]⟩ b18 b48 (by decide +kernel) (by decide +kernel) n355

theorem n357 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b17 = true := join_dead n356 (by decide +kernel)

theorem n358 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b16 = true := join_dead n357 (by decide +kernel)

theorem n359 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b15 = true := join_dead n358 (by decide +kernel)

theorem n360 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b14 = true := join_dead n359 (by decide +kernel)

theorem n361 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b13 = true := join_dead n360 (by decide +kernel)

theorem n362 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b12 = true := join_dead n361 (by decide +kernel)

theorem n363 : fastVisit (leafCols 5 bank) [12,8,5] ⟨522538,[2346,8192,65536]⟩ b12 = true := by decide +kernel

theorem n364 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b11 = true := join_live n362 n363

theorem n365 : fastVisit (leafCols 5 bank) [11,8,5] ⟨520780,[588,24576,196608]⟩ b11 = true := by decide +kernel

theorem n366 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b10 = true := join_live n364 n365

theorem n367 : fastVisit (leafFrame 5 [10,8,5] ⟨520200,[8,24576,196608]⟩) [] ⟨0,[]⟩ b52 = true := by decide +kernel

theorem n368 : fastVisit (leafFrame 5 [10,8,5] ⟨520200,[8,24576,196608]⟩) [2] ⟨149504,[149504]⟩ b52 = true := by decide +kernel

theorem n369 : fastVisit (leafFrame 5 [10,8,5] ⟨520200,[8,24576,196608]⟩) [] ⟨0,[]⟩ b51 = true := join_live n367 n368

theorem n370 : fastVisit (leafFrame 5 [10,8,5] ⟨520200,[8,24576,196608]⟩) [1] ⟨299008,[299008]⟩ b51 = true := by decide +kernel

theorem n371 : fastVisit (leafFrame 5 [10,8,5] ⟨520200,[8,24576,196608]⟩) [] ⟨0,[]⟩ b50 = true := join_live n369 n370

theorem n372 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b18 = true := enterColumns 5 bank [10,8,5] ⟨520200,[8,24576,196608]⟩ b18 b50 (by decide +kernel) (by decide +kernel) n371

theorem n373 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b17 = true := join_dead n372 (by decide +kernel)

theorem n374 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b16 = true := join_dead n373 (by decide +kernel)

theorem n375 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b15 = true := join_dead n374 (by decide +kernel)

theorem n376 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b14 = true := join_dead n375 (by decide +kernel)

theorem n377 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b13 = true := join_dead n376 (by decide +kernel)

theorem n378 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b12 = true := join_dead n377 (by decide +kernel)

theorem n379 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b11 = true := join_dead n378 (by decide +kernel)

theorem n380 : fastVisit (leafCols 5 bank) [10,8,5] ⟨520200,[8,24576,196608]⟩ b10 = true := join_dead n379 (by decide +kernel)

theorem n381 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b9 = true := join_live n366 n380

theorem n382 : fastVisit (leafCols 5 bank) [8,5] ⟨520192,[24576,196608]⟩ b8 = true := join_dead n381 (by decide +kernel)

theorem n383 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b7 = true := join_live n352 n382

theorem n384 : fastVisit (leafFrame 5 [7,5] ⟨520192,[24576,462848]⟩) [] ⟨0,[]⟩ b49 = true := by decide +kernel

theorem n385 : fastVisit (leafFrame 5 [7,5] ⟨520192,[24576,462848]⟩) [1] ⟨299008,[299008]⟩ b49 = true := by decide +kernel

theorem n386 : fastVisit (leafFrame 5 [7,5] ⟨520192,[24576,462848]⟩) [] ⟨0,[]⟩ b48 = true := join_live n384 n385

theorem n387 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b18 = true := enterColumns 5 bank [7,5] ⟨520192,[24576,462848]⟩ b18 b48 (by decide +kernel) (by decide +kernel) n386

theorem n388 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b17 = true := join_dead n387 (by decide +kernel)

theorem n389 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b16 = true := join_dead n388 (by decide +kernel)

theorem n390 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b15 = true := join_dead n389 (by decide +kernel)

theorem n391 : fastVisit (leafCols 5 bank) [15,7,5] ⟨523178,[2986,8192,4096]⟩ b15 = true := by decide +kernel

theorem n392 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b14 = true := join_live n390 n391

theorem n393 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b13 = true := join_dead n392 (by decide +kernel)

theorem n394 : fastVisit (leafCols 5 bank) [13,7,5] ⟨521096,[904,24576,4096]⟩ b13 = true := by decide +kernel

theorem n395 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b12 = true := join_live n393 n394

theorem n396 : fastVisit (leafCols 5 bank) [12,7,5] ⟨522538,[2346,8192,331776]⟩ b12 = true := by decide +kernel

theorem n397 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b11 = true := join_live n395 n396

theorem n398 : fastVisit (leafCols 5 bank) [11,7,5] ⟨520780,[588,24576,196608]⟩ b11 = true := by decide +kernel

theorem n399 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b10 = true := join_live n397 n398

end GainFinite.F5
