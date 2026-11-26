import PEqualNP.ThreeGateGain.FiniteV12P004

namespace GainFinite.F12
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n400 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [2] ⟨9584896,[9584896]⟩ b46 = true := by decide +kernel

theorem n401 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [] ⟨0,[]⟩ b45 = true := join_live n399 n400

theorem n402 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [1] ⟨19169792,[19169792]⟩ b45 = true := by decide +kernel

theorem n403 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [] ⟨0,[]⟩ b44 = true := join_live n401 n402

theorem n404 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b24 = true := enterColumns 12 bank [1] ⟨19169792,[19169792]⟩ b24 b44 (by decide +kernel) (by decide +kernel) n403

theorem n405 : fastVisit (leafCols 12 bank) [24,1] ⟨29294458,[10124666,17039872]⟩ b24 = true := by decide +kernel

theorem n406 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b23 = true := join_live n404 n405

theorem n407 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b22 = true := join_dead n406 (by decide +kernel)

theorem n408 : fastVisit (leafCols 12 bank) [22,1] ⟨20774520,[1604728,17039872]⟩ b22 = true := by decide +kernel

theorem n409 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b21 = true := join_live n407 n408

theorem n410 : fastVisit (leafCols 12 bank) [21,1] ⟨32964522,[13794730,2359296]⟩ b21 = true := by decide +kernel

theorem n411 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b20 = true := join_live n409 n410

theorem n412 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b19 = true := join_dead n411 (by decide +kernel)

theorem n413 : fastVisit (leafCols 12 bank) [19,1] ⟨31784840,[12615048,2359296]⟩ b19 = true := by decide +kernel

theorem n414 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b18 = true := join_live n412 n413

theorem n415 : fastVisit (leafCols 12 bank) [18,1] ⟨28770090,[9600298,19137024]⟩ b18 = true := by decide +kernel

theorem n416 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b17 = true := join_live n414 n415

theorem n417 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b16 = true := join_dead n416 (by decide +kernel)

theorem n418 : fastVisit (leafFrame 12 [16,1] ⟨19201544,[31752,19137024]⟩) [] ⟨0,[]⟩ b52 = true := by decide +kernel

theorem n419 : fastVisit (leafFrame 12 [16,1] ⟨19201544,[31752,19137024]⟩) [1] ⟨19169792,[19169792]⟩ b52 = true := by decide +kernel

theorem n420 : fastVisit (leafFrame 12 [16,1] ⟨19201544,[31752,19137024]⟩) [] ⟨0,[]⟩ b51 = true := join_live n418 n419

theorem n421 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b24 = true := enterColumns 12 bank [16,1] ⟨19201544,[31752,19137024]⟩ b24 b51 (by decide +kernel) (by decide +kernel) n420

theorem n422 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b23 = true := join_dead n421 (by decide +kernel)

theorem n423 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b22 = true := join_dead n422 (by decide +kernel)

theorem n424 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b21 = true := join_dead n423 (by decide +kernel)

theorem n425 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b20 = true := join_dead n424 (by decide +kernel)

theorem n426 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b19 = true := join_dead n425 (by decide +kernel)

theorem n427 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b18 = true := join_dead n426 (by decide +kernel)

theorem n428 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b17 = true := join_dead n427 (by decide +kernel)

theorem n429 : fastVisit (leafCols 12 bank) [16,1] ⟨19201544,[31752,19137024]⟩ b16 = true := join_dead n428 (by decide +kernel)

theorem n430 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b15 = true := join_live n417 n429

theorem n431 : fastVisit (leafCols 12 bank) [15,1] ⟨33540986,[14371194,33280]⟩ b15 = true := by decide +kernel

theorem n432 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b14 = true := join_live n430 n431

theorem n433 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b13 = true := join_dead n432 (by decide +kernel)

theorem n434 : fastVisit (leafCols 12 bank) [13,1] ⟨33522296,[14352504,33280]⟩ b13 = true := by decide +kernel

theorem n435 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b12 = true := join_live n433 n434

theorem n436 : fastVisit (leafCols 12 bank) [12,1] ⟨33538816,[14369024,33280]⟩ b12 = true := by decide +kernel

theorem n437 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b11 = true := join_live n435 n436

theorem n438 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b10 = true := join_dead n437 (by decide +kernel)

theorem n439 : fastVisit (leafCols 12 bank) [10,1] ⟨33522176,[14352384,33280]⟩ b10 = true := by decide +kernel

theorem n440 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b9 = true := join_live n438 n439

theorem n441 : fastVisit (leafCols 12 bank) [9,1] ⟨29281146,[10111354,17072640]⟩ b9 = true := by decide +kernel

theorem n442 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b8 = true := join_live n440 n441

theorem n443 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b7 = true := join_dead n442 (by decide +kernel)

theorem n444 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b21 = true := by decide +kernel

theorem n445 : fastVisit (leafCols 12 bank) [21,7,1] ⟨33488890,[12746114,524368,262144]⟩ b21 = true := by decide +kernel

theorem n446 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b20 = true := join_live n444 n445

theorem n447 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b19 = true := join_dead n446 (by decide +kernel)

theorem n448 : fastVisit (leafCols 12 bank) [19,7,1] ⟨33357816,[12615040,1572976,262144]⟩ b19 = true := by decide +kernel

theorem n449 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b18 = true := join_live n447 n448

theorem n450 : fastVisit (leafCols 12 bank) [18,7,1] ⟨29294458,[8551682,524368,17039872]⟩ b18 = true := by decide +kernel

theorem n451 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b17 = true := join_live n449 n450

theorem n452 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b16 = true := join_dead n451 (by decide +kernel)

theorem n453 : fastVisit (leafCols 12 bank) [16,7,1] ⟨20774520,[31744,1572976,17039872]⟩ b16 = true := by decide +kernel

theorem n454 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b15 = true := join_live n452 n453

theorem n455 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b14 = true := join_dead n454 (by decide +kernel)

theorem n456 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b13 = true := join_dead n455 (by decide +kernel)

theorem n457 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b12 = true := join_dead n456 (by decide +kernel)

theorem n458 : fastVisit (leafCols 12 bank) [12,7,1] ⟨33538936,[12796160,120,33280]⟩ b12 = true := by decide +kernel

theorem n459 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b11 = true := join_live n457 n458

theorem n460 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b10 = true := join_dead n459 (by decide +kernel)

theorem n461 : fastVisit (leafCols 12 bank) [10,7,1] ⟨33522296,[12779520,120,33280]⟩ b10 = true := by decide +kernel

theorem n462 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b9 = true := join_live n460 n461

theorem n463 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b8 = true := join_dead n462 (by decide +kernel)

theorem n464 : fastVisit (leafCols 12 bank) [7,1] ⟨20742776,[1572984,17072640]⟩ b7 = true := join_dead n463 (by decide +kernel)

theorem n465 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b6 = true := join_live n443 n464

theorem n466 : fastVisit (leafCols 12 bank) [6,1] ⟨32957312,[13787520,2359296]⟩ b9 = true := by decide +kernel

theorem n467 : fastVisit (leafCols 12 bank) [9,6,1] ⟨33483770,[526458,4202624,262144]⟩ b9 = true := by decide +kernel

theorem n468 : fastVisit (leafCols 12 bank) [6,1] ⟨32957312,[13787520,2359296]⟩ b8 = true := join_live n466 n467

theorem n469 : fastVisit (leafCols 12 bank) [6,1] ⟨32957312,[13787520,2359296]⟩ b7 = true := join_dead n468 (by decide +kernel)

theorem n470 : fastVisit (leafCols 12 bank) [7,6,1] ⟨33481720,[524408,12738944,262144]⟩ b7 = true := by decide +kernel

theorem n471 : fastVisit (leafCols 12 bank) [6,1] ⟨32957312,[13787520,2359296]⟩ b6 = true := join_live n469 n470

theorem n472 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b5 = true := join_live n465 n471

theorem n473 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b4 = true := join_dead n472 (by decide +kernel)

theorem n474 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b16 = true := by decide +kernel

theorem n475 : fastVisit (leafCols 12 bank) [16,4,1] ⟨31784840,[7176,12583296,2359296]⟩ b16 = true := by decide +kernel

theorem n476 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b15 = true := join_live n474 n475

theorem n477 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b14 = true := join_dead n476 (by decide +kernel)

theorem n478 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b13 = true := join_dead n477 (by decide +kernel)

theorem n479 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b12 = true := join_dead n478 (by decide +kernel)

end GainFinite.F12
