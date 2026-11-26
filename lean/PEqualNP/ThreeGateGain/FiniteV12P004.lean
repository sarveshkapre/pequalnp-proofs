import PEqualNP.ThreeGateGain.FiniteV12P003

namespace GainFinite.F12
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n320 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b24 = true := enterColumns 12 bank [16,2] ⟨9633032,[48136,9568512]⟩ b24 b42 (by decide +kernel) (by decide +kernel) n319

theorem n321 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b23 = true := join_dead n320 (by decide +kernel)

theorem n322 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b22 = true := join_dead n321 (by decide +kernel)

theorem n323 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b21 = true := join_dead n322 (by decide +kernel)

theorem n324 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b20 = true := join_dead n323 (by decide +kernel)

theorem n325 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b19 = true := join_dead n324 (by decide +kernel)

theorem n326 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b18 = true := join_dead n325 (by decide +kernel)

theorem n327 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b17 = true := join_dead n326 (by decide +kernel)

theorem n328 : fastVisit (leafCols 12 bank) [16,2] ⟨9633032,[48136,9568512]⟩ b16 = true := join_dead n327 (by decide +kernel)

theorem n329 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b15 = true := join_live n316 n328

theorem n330 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b14 = true := join_dead n329 (by decide +kernel)

theorem n331 : fastVisit (leafCols 12 bank) [14,2] ⟨33543036,[23958140,16640]⟩ b14 = true := by decide +kernel

theorem n332 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b13 = true := join_live n330 n331

theorem n333 : fastVisit (leafCols 12 bank) [13,2] ⟨33505656,[23920760,16640]⟩ b13 = true := by decide +kernel

theorem n334 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b12 = true := join_live n332 n333

theorem n335 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b11 = true := join_dead n334 (by decide +kernel)

theorem n336 : fastVisit (leafCols 12 bank) [11,2] ⟨33538816,[23953920,16640]⟩ b11 = true := by decide +kernel

theorem n337 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b10 = true := join_live n335 n336

theorem n338 : fastVisit (leafCols 12 bank) [10,2] ⟨33505536,[23920640,16640]⟩ b10 = true := by decide +kernel

theorem n339 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b9 = true := join_live n337 n338

theorem n340 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b8 = true := join_dead n339 (by decide +kernel)

theorem n341 : fastVisit (leafCols 12 bank) [8,2] ⟨29283196,[19698300,8536320]⟩ b8 = true := by decide +kernel

theorem n342 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b7 = true := join_live n340 n341

theorem n343 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b20 = true := by decide +kernel

theorem n344 : fastVisit (leafCols 12 bank) [20,7,2] ⟨33488892,[21282436,524336,131072]⟩ b20 = true := by decide +kernel

theorem n345 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b19 = true := join_live n343 n344

theorem n346 : fastVisit (leafCols 12 bank) [19,7,2] ⟨33226744,[21020288,2621552,131072]⟩ b19 = true := by decide +kernel

theorem n347 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b18 = true := join_live n345 n346

theorem n348 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b17 = true := join_dead n347 (by decide +kernel)

theorem n349 : fastVisit (leafCols 12 bank) [17,7,2] ⟨29294460,[17088004,524336,8519936]⟩ b17 = true := by decide +kernel

theorem n350 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b16 = true := join_live n348 n349

theorem n351 : fastVisit (leafCols 12 bank) [16,7,2] ⟨12254584,[48128,2621552,8519936]⟩ b16 = true := by decide +kernel

theorem n352 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b15 = true := join_live n350 n351

theorem n353 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b14 = true := join_dead n352 (by decide +kernel)

theorem n354 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b13 = true := join_dead n353 (by decide +kernel)

theorem n355 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b12 = true := join_dead n354 (by decide +kernel)

theorem n356 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b11 = true := join_dead n355 (by decide +kernel)

theorem n357 : fastVisit (leafCols 12 bank) [11,7,2] ⟨33538936,[21332480,120,16640]⟩ b11 = true := by decide +kernel

theorem n358 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b10 = true := join_live n356 n357

theorem n359 : fastVisit (leafCols 12 bank) [10,7,2] ⟨33505656,[21299200,120,16640]⟩ b10 = true := by decide +kernel

theorem n360 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b9 = true := join_live n358 n359

theorem n361 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b8 = true := join_dead n360 (by decide +kernel)

theorem n362 : fastVisit (leafCols 12 bank) [7,2] ⟨12206456,[2621560,8536320]⟩ b7 = true := join_dead n361 (by decide +kernel)

theorem n363 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b6 = true := join_live n342 n362

theorem n364 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b5 = true := join_dead n363 (by decide +kernel)

theorem n365 : fastVisit (leafCols 12 bank) [5,2] ⟨32957312,[23372416,1179648]⟩ b8 = true := by decide +kernel

theorem n366 : fastVisit (leafCols 12 bank) [8,5,2] ⟨33485820,[528508,4202624,131072]⟩ b8 = true := by decide +kernel

theorem n367 : fastVisit (leafCols 12 bank) [5,2] ⟨32957312,[23372416,1179648]⟩ b7 = true := join_live n365 n366

theorem n368 : fastVisit (leafCols 12 bank) [7,5,2] ⟨33481720,[524408,21275264,131072]⟩ b7 = true := by decide +kernel

theorem n369 : fastVisit (leafCols 12 bank) [5,2] ⟨32957312,[23372416,1179648]⟩ b6 = true := join_live n367 n368

theorem n370 : fastVisit (leafCols 12 bank) [5,2] ⟨32957312,[23372416,1179648]⟩ b5 = true := join_dead n369 (by decide +kernel)

theorem n371 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b4 = true := join_live n364 n370

theorem n372 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b16 = true := by decide +kernel

theorem n373 : fastVisit (leafCols 12 bank) [16,4,2] ⟨30605192,[7176,20972160,1179648]⟩ b16 = true := by decide +kernel

theorem n374 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b15 = true := join_live n372 n373

theorem n375 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b14 = true := join_dead n374 (by decide +kernel)

theorem n376 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b13 = true := join_dead n375 (by decide +kernel)

theorem n377 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b12 = true := join_dead n376 (by decide +kernel)

theorem n378 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b11 = true := join_dead n377 (by decide +kernel)

theorem n379 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b10 = true := join_dead n378 (by decide +kernel)

theorem n380 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b9 = true := join_dead n379 (by decide +kernel)

theorem n381 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b8 = true := join_dead n380 (by decide +kernel)

theorem n382 : fastVisit (leafCols 12 bank) [8,4,2] ⟨33485820,[2887804,4202624,131072]⟩ b8 = true := by decide +kernel

theorem n383 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b7 = true := join_live n381 n382

theorem n384 : fastVisit (leafCols 12 bank) [7,4,2] ⟨33219576,[2621560,21013120,131072]⟩ b7 = true := by decide +kernel

theorem n385 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b6 = true := join_live n383 n384

theorem n386 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b5 = true := join_dead n385 (by decide +kernel)

theorem n387 : fastVisit (leafCols 12 bank) [4,2] ⟨30598016,[21013120,1179648]⟩ b4 = true := join_dead n386 (by decide +kernel)

theorem n388 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b3 = true := join_live n371 n387

theorem n389 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b2 = true := join_dead n388 (by decide +kernel)

theorem n390 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b1 = true := join_live n289 n389

theorem n391 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [] ⟨0,[]⟩ b50 = true := by decide +kernel

theorem n392 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [6] ⟨30598016,[30598016]⟩ b50 = true := by decide +kernel

theorem n393 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [] ⟨0,[]⟩ b49 = true := join_live n391 n392

theorem n394 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [5] ⟨31777664,[31777664]⟩ b49 = true := by decide +kernel

theorem n395 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [] ⟨0,[]⟩ b48 = true := join_live n393 n394

theorem n396 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [4] ⟨29418368,[29418368]⟩ b48 = true := by decide +kernel

theorem n397 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [] ⟨0,[]⟩ b47 = true := join_live n395 n396

theorem n398 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [3] ⟨33547136,[33547136]⟩ b47 = true := by decide +kernel

theorem n399 : fastVisit (leafFrame 12 [1] ⟨19169792,[19169792]⟩) [] ⟨0,[]⟩ b46 = true := join_live n397 n398

end GainFinite.F12
