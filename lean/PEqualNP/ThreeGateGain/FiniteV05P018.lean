import PEqualNP.ThreeGateGain.FiniteV05P017

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n1440 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [2] ⟨149504,[149504]⟩ b120 = true := by decide +kernel

theorem n1441 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [4,2] ⟨477184,[327680,18432]⟩ b120 = true := by decide +kernel

theorem n1442 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [2] ⟨149504,[149504]⟩ b29 = true := join_live n1440 n1441

theorem n1443 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [] ⟨0,[]⟩ b28 = true := join_live n1439 n1442

theorem n1444 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [1] ⟨299008,[299008]⟩ b120 = true := by decide +kernel

theorem n1445 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [4,1] ⟨495616,[196608,36864]⟩ b120 = true := by decide +kernel

theorem n1446 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [1] ⟨299008,[299008]⟩ b29 = true := join_live n1444 n1445

theorem n1447 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [2,1] ⟨448512,[149504,299008]⟩ b29 = true := by decide +kernel

theorem n1448 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [1] ⟨299008,[299008]⟩ b28 = true := join_live n1446 n1447

theorem n1449 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [] ⟨0,[]⟩ b27 = true := join_live n1443 n1448

theorem n1450 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b18 = true := enterColumns 5 bank [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b18 b27 (by decide +kernel) (by decide +kernel) n1449

theorem n1451 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b17 = true := join_dead n1450 (by decide +kernel)

theorem n1452 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b16 = true := join_dead n1451 (by decide +kernel)

theorem n1453 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b15 = true := join_dead n1452 (by decide +kernel)

theorem n1454 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b14 = true := join_dead n1453 (by decide +kernel)

theorem n1455 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b13 = true := join_dead n1454 (by decide +kernel)

theorem n1456 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b12 = true := join_dead n1455 (by decide +kernel)

theorem n1457 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b11 = true := join_dead n1456 (by decide +kernel)

theorem n1458 : fastVisit (leafCols 5 bank) [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩ b10 = true := join_dead n1457 (by decide +kernel)

theorem n1459 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b9 = true := join_live n1434 n1458

theorem n1460 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b8 = true := join_dead n1459 (by decide +kernel)

theorem n1461 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b7 = true := join_dead n1460 (by decide +kernel)

theorem n1462 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b6 = true := join_live n1415 n1461

theorem n1463 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b5 = true := join_dead n1462 (by decide +kernel)

theorem n1464 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b4 = true := join_dead n1463 (by decide +kernel)

theorem n1465 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [] ⟨0,[]⟩ b57 = true := by decide +kernel

theorem n1466 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [3] ⟨523264,[523264]⟩ b57 = true := by decide +kernel

theorem n1467 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [] ⟨0,[]⟩ b122 = true := join_live n1465 n1466

theorem n1468 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [2] ⟨149504,[149504]⟩ b122 = true := by decide +kernel

theorem n1469 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [] ⟨0,[]⟩ b54 = true := join_live n1467 n1468

theorem n1470 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [1] ⟨299008,[299008]⟩ b122 = true := by decide +kernel

theorem n1471 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [2,1] ⟨448512,[149504,299008]⟩ b122 = true := by decide +kernel

theorem n1472 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [1] ⟨299008,[299008]⟩ b54 = true := join_live n1470 n1471

theorem n1473 : fastVisit (leafFrame 5 [4,2,1] ⟨514048,[65536,18432,36864]⟩) [] ⟨0,[]⟩ b53 = true := join_live n1469 n1472

theorem n1474 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b18 = true := enterColumns 5 bank [4,2,1] ⟨514048,[65536,18432,36864]⟩ b18 b53 (by decide +kernel) (by decide +kernel) n1473

theorem n1475 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b17 = true := join_dead n1474 (by decide +kernel)

theorem n1476 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b16 = true := join_dead n1475 (by decide +kernel)

theorem n1477 : fastVisit (leafCols 5 bank) [16,4,2,1] ⟨522360,[8312,65536,2048,4096]⟩ b16 = true := by decide +kernel

theorem n1478 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b15 = true := join_live n1476 n1477

theorem n1479 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b14 = true := join_dead n1478 (by decide +kernel)

theorem n1480 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b13 = true := join_dead n1479 (by decide +kernel)

theorem n1481 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b12 = true := join_dead n1480 (by decide +kernel)

theorem n1482 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b11 = true := join_dead n1481 (by decide +kernel)

theorem n1483 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b10 = true := join_dead n1482 (by decide +kernel)

theorem n1484 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [] ⟨0,[]⟩ b124 = true := by decide +kernel

theorem n1485 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [5] ⟨495616,[495616]⟩ b124 = true := by decide +kernel

theorem n1486 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [] ⟨0,[]⟩ b123 = true := join_live n1484 n1485

theorem n1487 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [4] ⟨458752,[458752]⟩ b123 = true := by decide +kernel

theorem n1488 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [] ⟨0,[]⟩ b57 = true := join_live n1486 n1487

theorem n1489 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [2] ⟨149504,[149504]⟩ b123 = true := by decide +kernel

theorem n1490 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [4,2] ⟨477184,[327680,18432]⟩ b123 = true := by decide +kernel

theorem n1491 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [2] ⟨149504,[149504]⟩ b57 = true := join_live n1489 n1490

theorem n1492 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [] ⟨0,[]⟩ b56 = true := join_live n1488 n1491

theorem n1493 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [1] ⟨299008,[299008]⟩ b123 = true := by decide +kernel

theorem n1494 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [4,1] ⟨495616,[196608,36864]⟩ b123 = true := by decide +kernel

theorem n1495 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [1] ⟨299008,[299008]⟩ b57 = true := join_live n1493 n1494

theorem n1496 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [2,1] ⟨448512,[149504,299008]⟩ b57 = true := by decide +kernel

theorem n1497 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [1] ⟨299008,[299008]⟩ b56 = true := join_live n1495 n1496

theorem n1498 : fastVisit (leafFrame 5 [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩) [] ⟨0,[]⟩ b55 = true := join_live n1492 n1497

theorem n1499 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b18 = true := enterColumns 5 bank [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b18 b55 (by decide +kernel) (by decide +kernel) n1498

theorem n1500 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b17 = true := join_dead n1499 (by decide +kernel)

theorem n1501 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b16 = true := join_dead n1500 (by decide +kernel)

theorem n1502 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b15 = true := join_dead n1501 (by decide +kernel)

theorem n1503 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b14 = true := join_dead n1502 (by decide +kernel)

theorem n1504 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b13 = true := join_dead n1503 (by decide +kernel)

theorem n1505 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b12 = true := join_dead n1504 (by decide +kernel)

theorem n1506 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b11 = true := join_dead n1505 (by decide +kernel)

theorem n1507 : fastVisit (leafCols 5 bank) [10,4,2,1] ⟨514056,[8,65536,18432,36864]⟩ b10 = true := join_dead n1506 (by decide +kernel)

theorem n1508 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b9 = true := join_live n1483 n1507

theorem n1509 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b8 = true := join_dead n1508 (by decide +kernel)

theorem n1510 : fastVisit (leafCols 5 bank) [4,2,1] ⟨514048,[65536,18432,36864]⟩ b7 = true := join_dead n1509 (by decide +kernel)

theorem n1511 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n1512 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n1513 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b61 = true := join_live n1511 n1512

theorem n1514 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n1515 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b45 = true := join_live n1513 n1514

theorem n1516 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [3] ⟨523264,[523264]⟩ b45 = true := by decide +kernel

theorem n1517 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b60 = true := join_live n1515 n1516

theorem n1518 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n1519 : fastVisit (leafFrame 5 [7,4,2,1] ⟨522240,[8192,65536,2048,4096]⟩) [] ⟨0,[]⟩ b59 = true := join_live n1517 n1518

end GainFinite.F5
