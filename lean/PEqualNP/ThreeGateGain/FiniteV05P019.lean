import PEqualNP.ThreeGateGain.FiniteV05P018

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n1520 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [1] ⟨299008,[299008]⟩ b60 = true := by decide +kernel

theorem n1521 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [2,1] ⟨448512,[149504,299008]⟩ b60 = true := by decide +kernel

theorem n1522 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [1] ⟨299008,[299008]⟩ b59 = true := join_live n1520 n1521

theorem n1523 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b58 = true := join_live n1519 n1522

theorem n1524 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b18 = true := enterColumns 5 bank [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n1523

theorem n1525 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b17 = true := join_dead n1524 (by decide +kernel)

theorem n1526 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b16 = true := join_dead n1525 (by decide +kernel)

theorem n1527 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b15 = true := join_dead n1526 (by decide +kernel)

theorem n1528 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b14 = true := join_dead n1527 (by decide +kernel)

theorem n1529 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b13 = true := join_dead n1528 (by decide +kernel)

theorem n1530 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b12 = true := join_dead n1529 (by decide +kernel)

theorem n1531 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b11 = true := join_dead n1530 (by decide +kernel)

theorem n1532 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b10 = true := join_dead n1531 (by decide +kernel)

theorem n1533 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n1534 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n1535 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b61 = true := join_live n1533 n1534

theorem n1536 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n1537 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b45 = true := join_live n1535 n1536

theorem n1538 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n1539 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b44 = true := join_live n1537 n1538

theorem n1540 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

theorem n1541 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n1542 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n1540 n1541

theorem n1543 : fastVisit (leafFrame 5 [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b43 = true := join_live n1539 n1542

theorem n1544 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b18 = true := enterColumns 5 bank [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n1543

theorem n1545 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b17 = true := join_dead n1544 (by decide +kernel)

theorem n1546 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b16 = true := join_dead n1545 (by decide +kernel)

theorem n1547 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b15 = true := join_dead n1546 (by decide +kernel)

theorem n1548 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b14 = true := join_dead n1547 (by decide +kernel)

theorem n1549 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b13 = true := join_dead n1548 (by decide +kernel)

theorem n1550 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b12 = true := join_dead n1549 (by decide +kernel)

theorem n1551 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b11 = true := join_dead n1550 (by decide +kernel)

theorem n1552 : fastVisit (leafCols 5 bank) [10,7,4,2,1] ⟨522248,[8,8192,65536,2048,4096]⟩ b10 = true := join_dead n1551 (by decide +kernel)

theorem n1553 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b9 = true := join_live n1532 n1552

theorem n1554 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b8 = true := join_dead n1553 (by decide +kernel)

theorem n1555 : fastVisit (leafCols 5 bank) [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩ b7 = true := join_dead n1554 (by decide +kernel)

theorem n1556 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b6 = true := join_live n1510 n1555

theorem n1557 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b5 = true := join_dead n1556 (by decide +kernel)

theorem n1558 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b4 = true := join_dead n1557 (by decide +kernel)

theorem n1559 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b3 = true := join_live n1464 n1558

theorem n1560 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b2 = true := join_dead n1559 (by decide +kernel)

theorem n1561 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b1 = true := join_live n1380 n1560

theorem n1562 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b0 = true := join_live n1031 n1561

theorem passed : quickHost 5 = true := by
  rw [← leafHost_sparse]
  have pool_correct : sparseRows 5 = bank := by decide +kernel
  rw [pool_correct]
  exact n1562

end GainFinite.F5
