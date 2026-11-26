import PEqualNP.ThreeGateGain.FiniteV05P005

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n480 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b15 = true := join_dead n479 (by decide +kernel)

theorem n481 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b14 = true := join_dead n480 (by decide +kernel)

theorem n482 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b13 = true := join_dead n481 (by decide +kernel)

theorem n483 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b12 = true := join_dead n482 (by decide +kernel)

theorem n484 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b11 = true := join_dead n483 (by decide +kernel)

theorem n485 : fastVisit (leafCols 5 bank) [10,7,6,5] ⟨522248,[8,8192,2048,4096]⟩ b10 = true := join_dead n484 (by decide +kernel)

theorem n486 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b9 = true := join_live n465 n485

theorem n487 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b8 = true := join_dead n486 (by decide +kernel)

theorem n488 : fastVisit (leafCols 5 bank) [7,6,5] ⟨522240,[8192,2048,4096]⟩ b7 = true := join_dead n487 (by decide +kernel)

theorem n489 : fastVisit (leafCols 5 bank) [6,5] ⟨514048,[18432,36864]⟩ b6 = true := join_live n450 n488

theorem n490 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b5 = true := join_live n417 n489

theorem n491 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b4 = true := join_live n297 n490

theorem n492 : fastVisit (leafFrame 5 [4] ⟨458752,[458752]⟩) [] ⟨0,[]⟩ b65 = true := by decide +kernel

theorem n493 : fastVisit (leafFrame 5 [4] ⟨458752,[458752]⟩) [2] ⟨149504,[149504]⟩ b65 = true := by decide +kernel

theorem n494 : fastVisit (leafFrame 5 [4] ⟨458752,[458752]⟩) [] ⟨0,[]⟩ b64 = true := join_live n492 n493

theorem n495 : fastVisit (leafFrame 5 [4] ⟨458752,[458752]⟩) [1] ⟨299008,[299008]⟩ b64 = true := by decide +kernel

theorem n496 : fastVisit (leafFrame 5 [4] ⟨458752,[458752]⟩) [] ⟨0,[]⟩ b63 = true := join_live n494 n495

theorem n497 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b18 = true := enterColumns 5 bank [4] ⟨458752,[458752]⟩ b18 b63 (by decide +kernel) (by decide +kernel) n496

theorem n498 : fastVisit (leafCols 5 bank) [18,4] ⟨518522,[59770,327680]⟩ b18 = true := by decide +kernel

theorem n499 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b17 = true := join_live n497 n498

theorem n500 : fastVisit (leafCols 5 bank) [17,4] ⟨520828,[62076,196608]⟩ b17 = true := by decide +kernel

theorem n501 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b16 = true := join_live n499 n500

theorem n502 : fastVisit (leafCols 5 bank) [16,4] ⟨516216,[57464,458752]⟩ b16 = true := by decide +kernel

theorem n503 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b15 = true := join_live n501 n502

theorem n504 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b14 = true := join_dead n503 (by decide +kernel)

theorem n505 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b13 = true := join_dead n504 (by decide +kernel)

theorem n506 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b12 = true := join_dead n505 (by decide +kernel)

theorem n507 : fastVisit (leafCols 5 bank) [12,4] ⟨477482,[18730,327680]⟩ b12 = true := by decide +kernel

theorem n508 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b11 = true := join_live n506 n507

theorem n509 : fastVisit (leafCols 5 bank) [11,4] ⟨496204,[37452,196608]⟩ b11 = true := by decide +kernel

theorem n510 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b10 = true := join_live n508 n509

theorem n511 : fastVisit (leafFrame 5 [10,4] ⟨458760,[8,458752]⟩) [] ⟨0,[]⟩ b68 = true := by decide +kernel

theorem n512 : fastVisit (leafFrame 5 [10,4] ⟨458760,[8,458752]⟩) [2] ⟨149504,[149504]⟩ b68 = true := by decide +kernel

theorem n513 : fastVisit (leafFrame 5 [10,4] ⟨458760,[8,458752]⟩) [] ⟨0,[]⟩ b67 = true := join_live n511 n512

theorem n514 : fastVisit (leafFrame 5 [10,4] ⟨458760,[8,458752]⟩) [1] ⟨299008,[299008]⟩ b68 = true := by decide +kernel

theorem n515 : fastVisit (leafFrame 5 [10,4] ⟨458760,[8,458752]⟩) [2,1] ⟨448512,[149504,299008]⟩ b68 = true := by decide +kernel

theorem n516 : fastVisit (leafFrame 5 [10,4] ⟨458760,[8,458752]⟩) [1] ⟨299008,[299008]⟩ b67 = true := join_live n514 n515

theorem n517 : fastVisit (leafFrame 5 [10,4] ⟨458760,[8,458752]⟩) [] ⟨0,[]⟩ b66 = true := join_live n513 n516

theorem n518 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b18 = true := enterColumns 5 bank [10,4] ⟨458760,[8,458752]⟩ b18 b66 (by decide +kernel) (by decide +kernel) n517

theorem n519 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b17 = true := join_dead n518 (by decide +kernel)

theorem n520 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b16 = true := join_dead n519 (by decide +kernel)

theorem n521 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b15 = true := join_dead n520 (by decide +kernel)

theorem n522 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b14 = true := join_dead n521 (by decide +kernel)

theorem n523 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b13 = true := join_dead n522 (by decide +kernel)

theorem n524 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b12 = true := join_dead n523 (by decide +kernel)

theorem n525 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b11 = true := join_dead n524 (by decide +kernel)

theorem n526 : fastVisit (leafCols 5 bank) [10,4] ⟨458760,[8,458752]⟩ b10 = true := join_dead n525 (by decide +kernel)

theorem n527 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b9 = true := join_live n510 n526

theorem n528 : fastVisit (leafFrame 5 [9,4] ⟨518144,[59392,327680]⟩) [] ⟨0,[]⟩ b39 = true := by decide +kernel

theorem n529 : fastVisit (leafFrame 5 [9,4] ⟨518144,[59392,327680]⟩) [1] ⟨299008,[299008]⟩ b39 = true := by decide +kernel

theorem n530 : fastVisit (leafFrame 5 [9,4] ⟨518144,[59392,327680]⟩) [] ⟨0,[]⟩ b38 = true := join_live n528 n529

theorem n531 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b18 = true := enterColumns 5 bank [9,4] ⟨518144,[59392,327680]⟩ b18 b38 (by decide +kernel) (by decide +kernel) n530

theorem n532 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b17 = true := join_dead n531 (by decide +kernel)

theorem n533 : fastVisit (leafCols 5 bank) [17,9,4] ⟨522876,[4732,2048,65536]⟩ b17 = true := by decide +kernel

theorem n534 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b16 = true := join_live n532 n533

theorem n535 : fastVisit (leafCols 5 bank) [16,9,4] ⟨518264,[120,2048,327680]⟩ b16 = true := by decide +kernel

theorem n536 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b15 = true := join_live n534 n535

theorem n537 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b14 = true := join_dead n536 (by decide +kernel)

theorem n538 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b13 = true := join_dead n537 (by decide +kernel)

theorem n539 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b12 = true := join_dead n538 (by decide +kernel)

theorem n540 : fastVisit (leafCols 5 bank) [12,9,4] ⟨518442,[298,40960,327680]⟩ b12 = true := by decide +kernel

theorem n541 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b11 = true := join_live n539 n540

theorem n542 : fastVisit (leafCols 5 bank) [11,9,4] ⟨522828,[4684,26624,65536]⟩ b11 = true := by decide +kernel

theorem n543 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b10 = true := join_live n541 n542

theorem n544 : fastVisit (leafFrame 5 [10,9,4] ⟨518152,[8,59392,327680]⟩) [] ⟨0,[]⟩ b42 = true := by decide +kernel

theorem n545 : fastVisit (leafFrame 5 [10,9,4] ⟨518152,[8,59392,327680]⟩) [2] ⟨149504,[149504]⟩ b42 = true := by decide +kernel

theorem n546 : fastVisit (leafFrame 5 [10,9,4] ⟨518152,[8,59392,327680]⟩) [] ⟨0,[]⟩ b41 = true := join_live n544 n545

theorem n547 : fastVisit (leafFrame 5 [10,9,4] ⟨518152,[8,59392,327680]⟩) [1] ⟨299008,[299008]⟩ b42 = true := by decide +kernel

theorem n548 : fastVisit (leafFrame 5 [10,9,4] ⟨518152,[8,59392,327680]⟩) [2,1] ⟨448512,[149504,299008]⟩ b42 = true := by decide +kernel

theorem n549 : fastVisit (leafFrame 5 [10,9,4] ⟨518152,[8,59392,327680]⟩) [1] ⟨299008,[299008]⟩ b41 = true := join_live n547 n548

theorem n550 : fastVisit (leafFrame 5 [10,9,4] ⟨518152,[8,59392,327680]⟩) [] ⟨0,[]⟩ b40 = true := join_live n546 n549

theorem n551 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b18 = true := enterColumns 5 bank [10,9,4] ⟨518152,[8,59392,327680]⟩ b18 b40 (by decide +kernel) (by decide +kernel) n550

theorem n552 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b17 = true := join_dead n551 (by decide +kernel)

theorem n553 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b16 = true := join_dead n552 (by decide +kernel)

theorem n554 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b15 = true := join_dead n553 (by decide +kernel)

theorem n555 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b14 = true := join_dead n554 (by decide +kernel)

theorem n556 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b13 = true := join_dead n555 (by decide +kernel)

theorem n557 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b12 = true := join_dead n556 (by decide +kernel)

theorem n558 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b11 = true := join_dead n557 (by decide +kernel)

theorem n559 : fastVisit (leafCols 5 bank) [10,9,4] ⟨518152,[8,59392,327680]⟩ b10 = true := join_dead n558 (by decide +kernel)

end GainFinite.F5
