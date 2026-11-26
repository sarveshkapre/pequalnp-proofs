import PEqualNP.ThreeGateGain.FiniteV05P004

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n400 : fastVisit (leafFrame 5 [10,7,5] ⟨520200,[8,24576,462848]⟩) [] ⟨0,[]⟩ b52 = true := by decide +kernel

theorem n401 : fastVisit (leafFrame 5 [10,7,5] ⟨520200,[8,24576,462848]⟩) [2] ⟨149504,[149504]⟩ b52 = true := by decide +kernel

theorem n402 : fastVisit (leafFrame 5 [10,7,5] ⟨520200,[8,24576,462848]⟩) [] ⟨0,[]⟩ b51 = true := join_live n400 n401

theorem n403 : fastVisit (leafFrame 5 [10,7,5] ⟨520200,[8,24576,462848]⟩) [1] ⟨299008,[299008]⟩ b51 = true := by decide +kernel

theorem n404 : fastVisit (leafFrame 5 [10,7,5] ⟨520200,[8,24576,462848]⟩) [] ⟨0,[]⟩ b50 = true := join_live n402 n403

theorem n405 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b18 = true := enterColumns 5 bank [10,7,5] ⟨520200,[8,24576,462848]⟩ b18 b50 (by decide +kernel) (by decide +kernel) n404

theorem n406 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b17 = true := join_dead n405 (by decide +kernel)

theorem n407 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b16 = true := join_dead n406 (by decide +kernel)

theorem n408 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b15 = true := join_dead n407 (by decide +kernel)

theorem n409 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b14 = true := join_dead n408 (by decide +kernel)

theorem n410 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b13 = true := join_dead n409 (by decide +kernel)

theorem n411 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b12 = true := join_dead n410 (by decide +kernel)

theorem n412 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b11 = true := join_dead n411 (by decide +kernel)

theorem n413 : fastVisit (leafCols 5 bank) [10,7,5] ⟨520200,[8,24576,462848]⟩ b10 = true := join_dead n412 (by decide +kernel)

theorem n414 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b9 = true := join_live n399 n413

theorem n415 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b8 = true := join_dead n414 (by decide +kernel)

theorem n416 : fastVisit (leafCols 5 bank) [7,5] ⟨520192,[24576,462848]⟩ b7 = true := join_dead n415 (by decide +kernel)

theorem n417 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b6 = true := join_live n383 n416

theorem n418 : fastVisit (leafFrame 5 [6,5] ⟨514048,[18432,36864]⟩) [] ⟨0,[]⟩ b54 = true := by decide +kernel

theorem n419 : fastVisit (leafFrame 5 [6,5] ⟨514048,[18432,36864]⟩) [1] ⟨299008,[299008]⟩ b54 = true := by decide +kernel

theorem n420 : fastVisit (leafFrame 5 [6,5] ⟨514048,[18432,36864]⟩) [] ⟨0,[]⟩ b53 = true := join_live n418 n419

theorem n421 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b18 = true := enterColumns 5 bank [6,5] ⟨514048,[18432,36864]⟩ b18 b53 (by decide +kernel) (by decide +kernel) n420

theorem n422 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b17 = true := join_dead n421 (by decide +kernel)

theorem n423 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b16 = true := join_dead n422 (by decide +kernel)

theorem n424 : fastVisit (leafCols 5 bank) [16,6,5] ⟨522360,[8312,2048,4096]⟩ b16 = true := by decide +kernel

theorem n425 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b15 = true := join_live n423 n424

theorem n426 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b14 = true := join_dead n425 (by decide +kernel)

theorem n427 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b13 = true := join_dead n426 (by decide +kernel)

theorem n428 : fastVisit (leafCols 5 bank) [13,6,5] ⟨514952,[904,18432,36864]⟩ b13 = true := by decide +kernel

theorem n429 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b12 = true := join_live n427 n428

theorem n430 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b11 = true := join_dead n429 (by decide +kernel)

theorem n431 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b10 = true := join_dead n430 (by decide +kernel)

theorem n432 : fastVisit (leafFrame 5 [10,6,5] ⟨514056,[8,18432,36864]⟩) [] ⟨0,[]⟩ b57 = true := by decide +kernel

theorem n433 : fastVisit (leafFrame 5 [10,6,5] ⟨514056,[8,18432,36864]⟩) [2] ⟨149504,[149504]⟩ b57 = true := by decide +kernel

theorem n434 : fastVisit (leafFrame 5 [10,6,5] ⟨514056,[8,18432,36864]⟩) [] ⟨0,[]⟩ b56 = true := join_live n432 n433

theorem n435 : fastVisit (leafFrame 5 [10,6,5] ⟨514056,[8,18432,36864]⟩) [1] ⟨299008,[299008]⟩ b57 = true := by decide +kernel

theorem n436 : fastVisit (leafFrame 5 [10,6,5] ⟨514056,[8,18432,36864]⟩) [2,1] ⟨448512,[149504,299008]⟩ b57 = true := by decide +kernel

theorem n437 : fastVisit (leafFrame 5 [10,6,5] ⟨514056,[8,18432,36864]⟩) [1] ⟨299008,[299008]⟩ b56 = true := join_live n435 n436

theorem n438 : fastVisit (leafFrame 5 [10,6,5] ⟨514056,[8,18432,36864]⟩) [] ⟨0,[]⟩ b55 = true := join_live n434 n437

theorem n439 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b18 = true := enterColumns 5 bank [10,6,5] ⟨514056,[8,18432,36864]⟩ b18 b55 (by decide +kernel) (by decide +kernel) n438

theorem n440 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b17 = true := join_dead n439 (by decide +kernel)

theorem n441 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b16 = true := join_dead n440 (by decide +kernel)

theorem n442 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b15 = true := join_dead n441 (by decide +kernel)

theorem n443 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b14 = true := join_dead n442 (by decide +kernel)

theorem n444 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b13 = true := join_dead n443 (by decide +kernel)

theorem n445 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b12 = true := join_dead n444 (by decide +kernel)

theorem n446 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b11 = true := join_dead n445 (by decide +kernel)

theorem n447 : fastVisit (leafCols 5 bank) [10,6,5] ⟨514056,[8,18432,36864]⟩ b10 = true := join_dead n446 (by decide +kernel)

theorem n448 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b9 = true := join_live n431 n447

theorem n449 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b8 = true := join_dead n448 (by decide +kernel)

theorem n450 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b7 = true := join_dead n449 (by decide +kernel)

theorem n451 : fastVisit (leafFrame 5 [7,6,5] ⟨522240,[8192,2048,4096]⟩) [] ⟨0,[]⟩ b60 = true := by decide +kernel

theorem n452 : fastVisit (leafFrame 5 [7,6,5] ⟨522240,[8192,2048,4096]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n453 : fastVisit (leafFrame 5 [7,6,5] ⟨522240,[8192,2048,4096]⟩) [] ⟨0,[]⟩ b59 = true := join_live n451 n452

theorem n454 : fastVisit (leafFrame 5 [7,6,5] ⟨522240,[8192,2048,4096]⟩) [1] ⟨299008,[299008]⟩ b59 = true := by decide +kernel

theorem n455 : fastVisit (leafFrame 5 [7,6,5] ⟨522240,[8192,2048,4096]⟩) [] ⟨0,[]⟩ b58 = true := join_live n453 n454

theorem n456 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b18 = true := enterColumns 5 bank [7,6,5] ⟨522240,[8192,2048,4096]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n455

theorem n457 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b17 = true := join_dead n456 (by decide +kernel)

theorem n458 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b16 = true := join_dead n457 (by decide +kernel)

theorem n459 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b15 = true := join_dead n458 (by decide +kernel)

theorem n460 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b14 = true := join_dead n459 (by decide +kernel)

theorem n461 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b13 = true := join_dead n460 (by decide +kernel)

theorem n462 : fastVisit (leafCols 5 bank) [13,7,6,5] ⟨523144,[904,8192,2048,4096]⟩ b13 = true := by decide +kernel

theorem n463 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b12 = true := join_live n461 n462

theorem n464 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b11 = true := join_dead n463 (by decide +kernel)

theorem n465 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b10 = true := join_dead n464 (by decide +kernel)

theorem n466 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n467 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n468 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [] ⟨0,[]⟩ b61 = true := join_live n466 n467

theorem n469 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n470 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [] ⟨0,[]⟩ b45 = true := join_live n468 n469

theorem n471 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n472 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [] ⟨0,[]⟩ b44 = true := join_live n470 n471

theorem n473 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

theorem n474 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n475 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n473 n474

theorem n476 : fastVisit (leafFrame 5 [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩) [] ⟨0,[]⟩ b43 = true := join_live n472 n475

theorem n477 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b18 = true := enterColumns 5 bank [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n476

theorem n478 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b17 = true := join_dead n477 (by decide +kernel)

theorem n479 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b16 = true := join_dead n478 (by decide +kernel)

end GainFinite.F5
