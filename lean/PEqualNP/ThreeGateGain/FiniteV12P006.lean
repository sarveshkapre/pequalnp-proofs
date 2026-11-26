import PEqualNP.ThreeGateGain.FiniteV12P005

namespace GainFinite.F12
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n480 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b11 = true := join_dead n479 (by decide +kernel)

theorem n481 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b10 = true := join_dead n480 (by decide +kernel)

theorem n482 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b9 = true := join_dead n481 (by decide +kernel)

theorem n483 : fastVisit (leafCols 12 bank) [9,4,1] ⟨33483770,[1706106,4202624,262144]⟩ b9 = true := by decide +kernel

theorem n484 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b8 = true := join_live n482 n483

theorem n485 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b7 = true := join_dead n484 (by decide +kernel)

theorem n486 : fastVisit (leafCols 12 bank) [7,4,1] ⟨33350648,[1572984,12607872,262144]⟩ b7 = true := by decide +kernel

theorem n487 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b6 = true := join_live n485 n486

theorem n488 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b5 = true := join_dead n487 (by decide +kernel)

theorem n489 : fastVisit (leafCols 12 bank) [4,1] ⟨31777664,[12607872,2359296]⟩ b4 = true := join_dead n488 (by decide +kernel)

theorem n490 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b3 = true := join_live n473 n489

theorem n491 : fastVisit (leafCols 12 bank) [1] ⟨19169792,[19169792]⟩ b2 = true := join_dead n490 (by decide +kernel)

theorem n492 : fastVisit (leafFrame 12 [2,1] ⟨28754688,[9584896,19169792]⟩) [] ⟨0,[]⟩ b54 = true := by decide +kernel

theorem n493 : fastVisit (leafFrame 12 [2,1] ⟨28754688,[9584896,19169792]⟩) [1] ⟨19169792,[19169792]⟩ b54 = true := by decide +kernel

theorem n494 : fastVisit (leafFrame 12 [2,1] ⟨28754688,[9584896,19169792]⟩) [] ⟨0,[]⟩ b53 = true := join_live n492 n493

theorem n495 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b24 = true := enterColumns 12 bank [2,1] ⟨28754688,[9584896,19169792]⟩ b24 b53 (by decide +kernel) (by decide +kernel) n494

theorem n496 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b23 = true := join_dead n495 (by decide +kernel)

theorem n497 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b22 = true := join_dead n496 (by decide +kernel)

theorem n498 : fastVisit (leafCols 12 bank) [22,2,1] ⟨29294456,[539768,8519936,17039872]⟩ b22 = true := by decide +kernel

theorem n499 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b21 = true := join_live n497 n498

theorem n500 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b20 = true := join_dead n499 (by decide +kernel)

theorem n501 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b19 = true := join_dead n500 (by decide +kernel)

theorem n502 : fastVisit (leafCols 12 bank) [19,2,1] ⟨32964488,[4209800,1179648,2359296]⟩ b19 = true := by decide +kernel

theorem n503 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b18 = true := join_live n501 n502

theorem n504 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b17 = true := join_dead n503 (by decide +kernel)

theorem n505 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b16 = true := join_dead n504 (by decide +kernel)

theorem n506 : fastVisit (leafCols 12 bank) [16,2,1] ⟨28770056,[15368,9568512,19137024]⟩ b16 = true := by decide +kernel

theorem n507 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b15 = true := join_live n505 n506

theorem n508 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b14 = true := join_dead n507 (by decide +kernel)

theorem n509 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b13 = true := join_dead n508 (by decide +kernel)

theorem n510 : fastVisit (leafCols 12 bank) [13,2,1] ⟨33538936,[4784248,16640,33280]⟩ b13 = true := by decide +kernel

theorem n511 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b12 = true := join_live n509 n510

theorem n512 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b11 = true := join_dead n511 (by decide +kernel)

theorem n513 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b10 = true := join_dead n512 (by decide +kernel)

theorem n514 : fastVisit (leafCols 12 bank) [10,2,1] ⟨33538816,[4784128,16640,33280]⟩ b16 = true := by decide +kernel

theorem n515 : fastVisit (leafCols 12 bank) [16,10,2,1] ⟨33554184,[15368,4784128,256,512]⟩ b16 = true := by decide +kernel

theorem n516 : fastVisit (leafCols 12 bank) [10,2,1] ⟨33538816,[4784128,16640,33280]⟩ b15 = true := join_live n514 n515

theorem n517 : fastVisit (leafCols 12 bank) [10,2,1] ⟨33538816,[4784128,16640,33280]⟩ b14 = true := join_dead n516 (by decide +kernel)

theorem n518 : fastVisit (leafCols 12 bank) [10,2,1] ⟨33538816,[4784128,16640,33280]⟩ b13 = true := join_dead n517 (by decide +kernel)

theorem n519 : fastVisit (leafCols 12 bank) [10,2,1] ⟨33538816,[4784128,16640,33280]⟩ b12 = true := join_dead n518 (by decide +kernel)

theorem n520 : fastVisit (leafCols 12 bank) [10,2,1] ⟨33538816,[4784128,16640,33280]⟩ b11 = true := join_dead n519 (by decide +kernel)

theorem n521 : fastVisit (leafCols 12 bank) [10,2,1] ⟨33538816,[4784128,16640,33280]⟩ b10 = true := join_dead n520 (by decide +kernel)

theorem n522 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b9 = true := join_live n513 n521

theorem n523 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b8 = true := join_dead n522 (by decide +kernel)

theorem n524 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b7 = true := join_dead n523 (by decide +kernel)

theorem n525 : fastVisit (leafCols 12 bank) [7,2,1] ⟨29279096,[524408,8536320,17072640]⟩ b10 = true := by decide +kernel

theorem n526 : fastVisit (leafFrame 12 [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩) [] ⟨0,[]⟩ b56 = true := by decide +kernel

theorem n527 : fastVisit (leafFrame 12 [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩) [1] ⟨19169792,[19169792]⟩ b56 = true := by decide +kernel

theorem n528 : fastVisit (leafFrame 12 [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩) [] ⟨0,[]⟩ b55 = true := join_live n526 n527

theorem n529 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b24 = true := enterColumns 12 bank [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b24 b55 (by decide +kernel) (by decide +kernel) n528

theorem n530 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b23 = true := join_dead n529 (by decide +kernel)

theorem n531 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b22 = true := join_dead n530 (by decide +kernel)

theorem n532 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b21 = true := join_dead n531 (by decide +kernel)

theorem n533 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b20 = true := join_dead n532 (by decide +kernel)

theorem n534 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b19 = true := join_dead n533 (by decide +kernel)

theorem n535 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b18 = true := join_dead n534 (by decide +kernel)

theorem n536 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b17 = true := join_dead n535 (by decide +kernel)

theorem n537 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b16 = true := join_dead n536 (by decide +kernel)

theorem n538 : fastVisit (leafCols 12 bank) [16,10,7,2,1] ⟨33554296,[15360,4259840,112,256,512]⟩ b16 = true := by decide +kernel

theorem n539 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b15 = true := join_live n537 n538

theorem n540 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b14 = true := join_dead n539 (by decide +kernel)

theorem n541 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b13 = true := join_dead n540 (by decide +kernel)

theorem n542 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b12 = true := join_dead n541 (by decide +kernel)

theorem n543 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b11 = true := join_dead n542 (by decide +kernel)

theorem n544 : fastVisit (leafCols 12 bank) [10,7,2,1] ⟨33538936,[4259840,120,16640,33280]⟩ b10 = true := join_dead n543 (by decide +kernel)

theorem n545 : fastVisit (leafCols 12 bank) [7,2,1] ⟨29279096,[524408,8536320,17072640]⟩ b9 = true := join_live n525 n544

theorem n546 : fastVisit (leafCols 12 bank) [7,2,1] ⟨29279096,[524408,8536320,17072640]⟩ b8 = true := join_dead n545 (by decide +kernel)

theorem n547 : fastVisit (leafCols 12 bank) [7,2,1] ⟨29279096,[524408,8536320,17072640]⟩ b7 = true := join_dead n546 (by decide +kernel)

theorem n548 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b6 = true := join_live n524 n547

theorem n549 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b5 = true := join_dead n548 (by decide +kernel)

theorem n550 : fastVisit (leafCols 12 bank) [2,1] ⟨28754688,[9584896,19169792]⟩ b4 = true := join_dead n549 (by decide +kernel)

theorem n551 : fastVisit (leafCols 12 bank) [4,2,1] ⟨32957312,[4202624,1179648,2359296]⟩ b16 = true := by decide +kernel

theorem n552 : fastVisit (leafFrame 12 [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩) [] ⟨0,[]⟩ b58 = true := by decide +kernel

theorem n553 : fastVisit (leafFrame 12 [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩) [1] ⟨19169792,[19169792]⟩ b58 = true := by decide +kernel

theorem n554 : fastVisit (leafFrame 12 [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩) [] ⟨0,[]⟩ b57 = true := join_live n552 n553

theorem n555 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b24 = true := enterColumns 12 bank [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b24 b57 (by decide +kernel) (by decide +kernel) n554

theorem n556 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b23 = true := join_dead n555 (by decide +kernel)

theorem n557 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b22 = true := join_dead n556 (by decide +kernel)

theorem n558 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b21 = true := join_dead n557 (by decide +kernel)

theorem n559 : fastVisit (leafCols 12 bank) [16,4,2,1] ⟨32964488,[7176,4194432,1179648,2359296]⟩ b20 = true := join_dead n558 (by decide +kernel)

end GainFinite.F12
