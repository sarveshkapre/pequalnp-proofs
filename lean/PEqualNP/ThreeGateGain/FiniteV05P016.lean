import PEqualNP.ThreeGateGain.FiniteV05P015

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n1280 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [4,2] ⟨477184,[327680,18432]⟩ b108 = true := by decide +kernel

theorem n1281 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [2] ⟨149504,[149504]⟩ b107 = true := join_live n1279 n1280

theorem n1282 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [] ⟨0,[]⟩ b47 = true := join_live n1278 n1281

theorem n1283 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [1] ⟨299008,[299008]⟩ b107 = true := by decide +kernel

theorem n1284 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [2,1] ⟨448512,[149504,299008]⟩ b107 = true := by decide +kernel

theorem n1285 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [1] ⟨299008,[299008]⟩ b47 = true := join_live n1283 n1284

theorem n1286 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [] ⟨0,[]⟩ b46 = true := join_live n1282 n1285

theorem n1287 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b18 = true := enterColumns 5 bank [10,4,1] ⟨495624,[8,196608,36864]⟩ b18 b46 (by decide +kernel) (by decide +kernel) n1286

theorem n1288 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b17 = true := join_dead n1287 (by decide +kernel)

theorem n1289 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b16 = true := join_dead n1288 (by decide +kernel)

theorem n1290 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b15 = true := join_dead n1289 (by decide +kernel)

theorem n1291 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b14 = true := join_dead n1290 (by decide +kernel)

theorem n1292 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b13 = true := join_dead n1291 (by decide +kernel)

theorem n1293 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b12 = true := join_dead n1292 (by decide +kernel)

theorem n1294 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b11 = true := join_dead n1293 (by decide +kernel)

theorem n1295 : fastVisit (leafCols 5 bank) [10,4,1] ⟨495624,[8,196608,36864]⟩ b10 = true := join_dead n1294 (by decide +kernel)

theorem n1296 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b9 = true := join_live n1273 n1295

theorem n1297 : fastVisit (leafFrame 5 [9,4,1] ⟨522240,[26624,65536,4096]⟩) [] ⟨0,[]⟩ b60 = true := by decide +kernel

theorem n1298 : fastVisit (leafFrame 5 [9,4,1] ⟨522240,[26624,65536,4096]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n1299 : fastVisit (leafFrame 5 [9,4,1] ⟨522240,[26624,65536,4096]⟩) [] ⟨0,[]⟩ b59 = true := join_live n1297 n1298

theorem n1300 : fastVisit (leafFrame 5 [9,4,1] ⟨522240,[26624,65536,4096]⟩) [1] ⟨299008,[299008]⟩ b59 = true := by decide +kernel

theorem n1301 : fastVisit (leafFrame 5 [9,4,1] ⟨522240,[26624,65536,4096]⟩) [] ⟨0,[]⟩ b58 = true := join_live n1299 n1300

theorem n1302 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b18 = true := enterColumns 5 bank [9,4,1] ⟨522240,[26624,65536,4096]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n1301

theorem n1303 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b17 = true := join_dead n1302 (by decide +kernel)

theorem n1304 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b16 = true := join_dead n1303 (by decide +kernel)

theorem n1305 : fastVisit (leafCols 5 bank) [16,9,4,1] ⟨522360,[120,2048,65536,4096]⟩ b16 = true := by decide +kernel

theorem n1306 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b15 = true := join_live n1304 n1305

theorem n1307 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b14 = true := join_dead n1306 (by decide +kernel)

theorem n1308 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b13 = true := join_dead n1307 (by decide +kernel)

theorem n1309 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b12 = true := join_dead n1308 (by decide +kernel)

theorem n1310 : fastVisit (leafCols 5 bank) [12,9,4,1] ⟨522538,[298,8192,65536,4096]⟩ b12 = true := by decide +kernel

theorem n1311 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b11 = true := join_live n1309 n1310

theorem n1312 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b10 = true := join_dead n1311 (by decide +kernel)

theorem n1313 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n1314 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n1315 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [] ⟨0,[]⟩ b61 = true := join_live n1313 n1314

theorem n1316 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n1317 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [] ⟨0,[]⟩ b45 = true := join_live n1315 n1316

theorem n1318 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n1319 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [] ⟨0,[]⟩ b44 = true := join_live n1317 n1318

theorem n1320 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

theorem n1321 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n1322 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n1320 n1321

theorem n1323 : fastVisit (leafFrame 5 [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩) [] ⟨0,[]⟩ b43 = true := join_live n1319 n1322

theorem n1324 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b18 = true := enterColumns 5 bank [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n1323

theorem n1325 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b17 = true := join_dead n1324 (by decide +kernel)

theorem n1326 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b16 = true := join_dead n1325 (by decide +kernel)

theorem n1327 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b15 = true := join_dead n1326 (by decide +kernel)

theorem n1328 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b14 = true := join_dead n1327 (by decide +kernel)

theorem n1329 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b13 = true := join_dead n1328 (by decide +kernel)

theorem n1330 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b12 = true := join_dead n1329 (by decide +kernel)

theorem n1331 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b11 = true := join_dead n1330 (by decide +kernel)

theorem n1332 : fastVisit (leafCols 5 bank) [10,9,4,1] ⟨522248,[8,26624,65536,4096]⟩ b10 = true := join_dead n1331 (by decide +kernel)

theorem n1333 : fastVisit (leafCols 5 bank) [9,4,1] ⟨522240,[26624,65536,4096]⟩ b9 = true := join_live n1312 n1332

theorem n1334 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b8 = true := join_live n1296 n1333

theorem n1335 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b7 = true := join_dead n1334 (by decide +kernel)

theorem n1336 : fastVisit (leafFrame 5 [7,4,1] ⟨520192,[24576,196608,4096]⟩) [] ⟨0,[]⟩ b110 = true := by decide +kernel

theorem n1337 : fastVisit (leafFrame 5 [7,4,1] ⟨520192,[24576,196608,4096]⟩) [2] ⟨149504,[149504]⟩ b110 = true := by decide +kernel

theorem n1338 : fastVisit (leafFrame 5 [7,4,1] ⟨520192,[24576,196608,4096]⟩) [] ⟨0,[]⟩ b49 = true := join_live n1336 n1337

theorem n1339 : fastVisit (leafFrame 5 [7,4,1] ⟨520192,[24576,196608,4096]⟩) [1] ⟨299008,[299008]⟩ b49 = true := by decide +kernel

theorem n1340 : fastVisit (leafFrame 5 [7,4,1] ⟨520192,[24576,196608,4096]⟩) [] ⟨0,[]⟩ b48 = true := join_live n1338 n1339

theorem n1341 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b18 = true := enterColumns 5 bank [7,4,1] ⟨520192,[24576,196608,4096]⟩ b18 b48 (by decide +kernel) (by decide +kernel) n1340

theorem n1342 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b17 = true := join_dead n1341 (by decide +kernel)

theorem n1343 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b16 = true := join_dead n1342 (by decide +kernel)

theorem n1344 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b15 = true := join_dead n1343 (by decide +kernel)

theorem n1345 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b14 = true := join_dead n1344 (by decide +kernel)

theorem n1346 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b13 = true := join_dead n1345 (by decide +kernel)

theorem n1347 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b12 = true := join_dead n1346 (by decide +kernel)

theorem n1348 : fastVisit (leafCols 5 bank) [12,7,4,1] ⟨522538,[2346,8192,65536,4096]⟩ b12 = true := by decide +kernel

theorem n1349 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b11 = true := join_live n1347 n1348

theorem n1350 : fastVisit (leafCols 5 bank) [7,4,1] ⟨520192,[24576,196608,4096]⟩ b10 = true := join_dead n1349 (by decide +kernel)

theorem n1351 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [] ⟨0,[]⟩ b112 = true := by decide +kernel

theorem n1352 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [5] ⟨495616,[495616]⟩ b112 = true := by decide +kernel

theorem n1353 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [] ⟨0,[]⟩ b111 = true := join_live n1351 n1352

theorem n1354 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [4] ⟨458752,[458752]⟩ b111 = true := by decide +kernel

theorem n1355 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [] ⟨0,[]⟩ b52 = true := join_live n1353 n1354

theorem n1356 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [2] ⟨149504,[149504]⟩ b111 = true := by decide +kernel

theorem n1357 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [4,2] ⟨477184,[327680,18432]⟩ b111 = true := by decide +kernel

theorem n1358 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [2] ⟨149504,[149504]⟩ b52 = true := join_live n1356 n1357

theorem n1359 : fastVisit (leafFrame 5 [10,7,4,1] ⟨520200,[8,24576,196608,4096]⟩) [] ⟨0,[]⟩ b51 = true := join_live n1355 n1358

end GainFinite.F5
