import PEqualNP.ThreeGateGain.FiniteV05P016

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n1360 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [1] ⟨299008,[299008]⟩ b52 = true := by decide +kernel

theorem n1361 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [2,1] ⟨448512,[149504,299008]⟩ b52 = true := by decide +kernel

theorem n1362 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [1] ⟨299008,[299008]⟩ b51 = true := join_live n1360 n1361

theorem n1363 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [] ⟨0,[]⟩ b50 = true := join_live n1359 n1362

theorem n1364 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b18 = true := enterColumns 5 bank [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b18 b50 (by decide +kernel) (by decide +kernel) n1363

theorem n1365 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b17 = true := join_dead n1364 (by decide +kernel)

theorem n1366 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b16 = true := join_dead n1365 (by decide +kernel)

theorem n1367 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b15 = true := join_dead n1366 (by decide +kernel)

theorem n1368 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b14 = true := join_dead n1367 (by decide +kernel)

theorem n1369 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b13 = true := join_dead n1368 (by decide +kernel)

theorem n1370 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b12 = true := join_dead n1369 (by decide +kernel)

theorem n1371 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b11 = true := join_dead n1370 (by decide +kernel)

theorem n1372 : fastVisit (leafCols 5 bank) [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩ b10 = true := join_dead n1371 (by decide +kernel)

theorem n1373 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b9 = true := join_live n1350 n1372

theorem n1374 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b8 = true := join_dead n1373 (by decide +kernel)

theorem n1375 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b7 = true := join_dead n1374 (by decide +kernel)

theorem n1376 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b6 = true := join_live n1335 n1375

theorem n1377 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b5 = true := join_dead n1376 (by decide +kernel)

theorem n1378 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b4 = true := join_dead n1377 (by decide +kernel)

theorem n1379 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b3 = true := join_live n1256 n1378

theorem n1380 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b2 = true := join_dead n1379 (by decide +kernel)

theorem n1381 : fastVisit (leafFrame 5 [2,1] ⟨448512,[149504,299008]⟩) [] ⟨0,[]⟩ b114 = true := by decide +kernel

theorem n1382 : fastVisit (leafFrame 5 [2,1] ⟨448512,[149504,299008]⟩) [1] ⟨299008,[299008]⟩ b114 = true := by decide +kernel

theorem n1383 : fastVisit (leafFrame 5 [2,1] ⟨448512,[149504,299008]⟩) [] ⟨0,[]⟩ b113 = true := join_live n1381 n1382

theorem n1384 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b18 = true := enterColumns 5 bank [2,1] ⟨448512,[149504,299008]⟩ b18 b113 (by decide +kernel) (by decide +kernel) n1383

theorem n1385 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b17 = true := join_dead n1384 (by decide +kernel)

theorem n1386 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b16 = true := join_dead n1385 (by decide +kernel)

theorem n1387 : fastVisit (leafCols 5 bank) [16,2,1] ⟨456824,[8312,133120,266240]⟩ b16 = true := by decide +kernel

theorem n1388 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b15 = true := join_live n1386 n1387

theorem n1389 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b14 = true := join_dead n1388 (by decide +kernel)

theorem n1390 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b13 = true := join_dead n1389 (by decide +kernel)

theorem n1391 : fastVisit (leafCols 5 bank) [13,2,1] ⟨514952,[66440,18432,36864]⟩ b13 = true := by decide +kernel

theorem n1392 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b12 = true := join_live n1390 n1391

theorem n1393 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b11 = true := join_dead n1392 (by decide +kernel)

theorem n1394 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b10 = true := join_dead n1393 (by decide +kernel)

theorem n1395 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [] ⟨0,[]⟩ b118 = true := by decide +kernel

theorem n1396 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [4] ⟨458752,[458752]⟩ b118 = true := by decide +kernel

theorem n1397 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [] ⟨0,[]⟩ b117 = true := join_live n1395 n1396

theorem n1398 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [2] ⟨149504,[149504]⟩ b117 = true := by decide +kernel

theorem n1399 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [] ⟨0,[]⟩ b116 = true := join_live n1397 n1398

theorem n1400 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [1] ⟨299008,[299008]⟩ b117 = true := by decide +kernel

theorem n1401 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [2,1] ⟨448512,[149504,299008]⟩ b117 = true := by decide +kernel

theorem n1402 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [1] ⟨299008,[299008]⟩ b116 = true := join_live n1400 n1401

theorem n1403 : fastVisit (leafFrame 5 [10,2,1] ⟨448520,[8,149504,299008]⟩) [] ⟨0,[]⟩ b115 = true := join_live n1399 n1402

theorem n1404 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b18 = true := enterColumns 5 bank [10,2,1] ⟨448520,[8,149504,299008]⟩ b18 b115 (by decide +kernel) (by decide +kernel) n1403

theorem n1405 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b17 = true := join_dead n1404 (by decide +kernel)

theorem n1406 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b16 = true := join_dead n1405 (by decide +kernel)

theorem n1407 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b15 = true := join_dead n1406 (by decide +kernel)

theorem n1408 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b14 = true := join_dead n1407 (by decide +kernel)

theorem n1409 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b13 = true := join_dead n1408 (by decide +kernel)

theorem n1410 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b12 = true := join_dead n1409 (by decide +kernel)

theorem n1411 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b11 = true := join_dead n1410 (by decide +kernel)

theorem n1412 : fastVisit (leafCols 5 bank) [10,2,1] ⟨448520,[8,149504,299008]⟩ b10 = true := join_dead n1411 (by decide +kernel)

theorem n1413 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b9 = true := join_live n1394 n1412

theorem n1414 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b8 = true := join_dead n1413 (by decide +kernel)

theorem n1415 : fastVisit (leafCols 5 bank) [2,1] ⟨448512,[149504,299008]⟩ b7 = true := join_dead n1414 (by decide +kernel)

theorem n1416 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [] ⟨0,[]⟩ b29 = true := by decide +kernel

theorem n1417 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [3] ⟨523264,[523264]⟩ b29 = true := by decide +kernel

theorem n1418 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [] ⟨0,[]⟩ b119 = true := join_live n1416 n1417

theorem n1419 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [2] ⟨149504,[149504]⟩ b119 = true := by decide +kernel

theorem n1420 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [] ⟨0,[]⟩ b26 = true := join_live n1418 n1419

theorem n1421 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [1] ⟨299008,[299008]⟩ b119 = true := by decide +kernel

theorem n1422 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [2,1] ⟨448512,[149504,299008]⟩ b119 = true := by decide +kernel

theorem n1423 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [1] ⟨299008,[299008]⟩ b26 = true := join_live n1421 n1422

theorem n1424 : fastVisit (leafFrame 5 [7,2,1] ⟨456704,[8192,133120,266240]⟩) [] ⟨0,[]⟩ b25 = true := join_live n1420 n1423

theorem n1425 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b18 = true := enterColumns 5 bank [7,2,1] ⟨456704,[8192,133120,266240]⟩ b18 b25 (by decide +kernel) (by decide +kernel) n1424

theorem n1426 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b17 = true := join_dead n1425 (by decide +kernel)

theorem n1427 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b16 = true := join_dead n1426 (by decide +kernel)

theorem n1428 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b15 = true := join_dead n1427 (by decide +kernel)

theorem n1429 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b14 = true := join_dead n1428 (by decide +kernel)

theorem n1430 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b13 = true := join_dead n1429 (by decide +kernel)

theorem n1431 : fastVisit (leafCols 5 bank) [13,7,2,1] ⟨523144,[66440,8192,2048,4096]⟩ b13 = true := by decide +kernel

theorem n1432 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b12 = true := join_live n1430 n1431

theorem n1433 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b11 = true := join_dead n1432 (by decide +kernel)

theorem n1434 : fastVisit (leafCols 5 bank) [7,2,1] ⟨456704,[8192,133120,266240]⟩ b10 = true := join_dead n1433 (by decide +kernel)

theorem n1435 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [] ⟨0,[]⟩ b121 = true := by decide +kernel

theorem n1436 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [5] ⟨495616,[495616]⟩ b121 = true := by decide +kernel

theorem n1437 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [] ⟨0,[]⟩ b120 = true := join_live n1435 n1436

theorem n1438 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [4] ⟨458752,[458752]⟩ b120 = true := by decide +kernel

theorem n1439 : fastVisit (leafFrame 5 [10,7,2,1] ⟨456712,[8,8192,133120,266240]⟩) [] ⟨0,[]⟩ b29 = true := join_live n1437 n1438

end GainFinite.F5
