import PEqualNP.ThreeGateGain.FiniteV12P002

namespace GainFinite.F12
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n240 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b6 = true := join_live n238 n239

theorem n241 : fastVisit (leafCols 12 bank) [6,5] ⟨32957312,[1179648,2359296]⟩ b6 = true := by decide +kernel

theorem n242 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b5 = true := join_live n240 n241

theorem n243 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b4 = true := join_live n215 n242

theorem n244 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b24 = true := by decide +kernel

theorem n245 : fastVisit (leafCols 12 bank) [24,4] ⟨33226746,[3808378,20972160]⟩ b24 = true := by decide +kernel

theorem n246 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b23 = true := join_live n244 n245

theorem n247 : fastVisit (leafCols 12 bank) [23,4] ⟨33357820,[3939452,12583296]⟩ b23 = true := by decide +kernel

theorem n248 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b22 = true := join_live n246 n247

theorem n249 : fastVisit (leafCols 12 bank) [22,4] ⟨33095672,[3677304,29361024]⟩ b22 = true := by decide +kernel

theorem n250 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b21 = true := join_live n248 n249

theorem n251 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b20 = true := join_dead n250 (by decide +kernel)

theorem n252 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b19 = true := join_dead n251 (by decide +kernel)

theorem n253 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b18 = true := join_dead n252 (by decide +kernel)

theorem n254 : fastVisit (leafCols 12 bank) [18,4] ⟨30605226,[1186858,20972160]⟩ b18 = true := by decide +kernel

theorem n255 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b17 = true := join_live n253 n254

theorem n256 : fastVisit (leafCols 12 bank) [17,4] ⟨31784908,[2366540,12583296]⟩ b17 = true := by decide +kernel

theorem n257 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b16 = true := join_live n255 n256

theorem n258 : fastVisit (leafCols 12 bank) [16,4] ⟨29425544,[7176,29361024]⟩ b16 = true := by decide +kernel

theorem n259 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b15 = true := join_live n257 n258

theorem n260 : fastVisit (leafCols 12 bank) [15,4] ⟨33549306,[4130938,41600]⟩ b15 = true := by decide +kernel

theorem n261 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b14 = true := join_live n259 n260

theorem n262 : fastVisit (leafCols 12 bank) [14,4] ⟨33551356,[4132988,24960]⟩ b14 = true := by decide +kernel

theorem n263 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b13 = true := join_live n261 n262

theorem n264 : fastVisit (leafCols 12 bank) [13,4] ⟨33547256,[4128888,58240]⟩ b13 = true := by decide +kernel

theorem n265 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b12 = true := join_live n263 n264

theorem n266 : fastVisit (leafCols 12 bank) [12,4] ⟨33547136,[4128768,41600]⟩ b12 = true := by decide +kernel

theorem n267 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b11 = true := join_live n265 n266

theorem n268 : fastVisit (leafCols 12 bank) [11,4] ⟨33547136,[4128768,24960]⟩ b11 = true := by decide +kernel

theorem n269 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b10 = true := join_live n267 n268

theorem n270 : fastVisit (leafCols 12 bank) [10,4] ⟨33547136,[4128768,58240]⟩ b10 = true := by decide +kernel

theorem n271 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b9 = true := join_live n269 n270

theorem n272 : fastVisit (leafCols 12 bank) [9,4] ⟨33221626,[3803258,21013120]⟩ b9 = true := by decide +kernel

theorem n273 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b8 = true := join_live n271 n272

theorem n274 : fastVisit (leafCols 12 bank) [8,4] ⟨33354748,[3936380,12607872]⟩ b8 = true := by decide +kernel

theorem n275 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b7 = true := join_live n273 n274

theorem n276 : fastVisit (leafCols 12 bank) [7,4] ⟨33088504,[3670136,29418368]⟩ b7 = true := by decide +kernel

theorem n277 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b6 = true := join_live n275 n276

theorem n278 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b5 = true := join_dead n277 (by decide +kernel)

theorem n279 : fastVisit (leafCols 12 bank) [4] ⟨29418368,[29418368]⟩ b4 = true := join_dead n278 (by decide +kernel)

theorem n280 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b3 = true := join_live n243 n279

theorem n281 : fastVisit (leafCols 12 bank) [3] ⟨33547136,[33547136]⟩ b8 = true := by decide +kernel

theorem n282 : fastVisit (leafCols 12 bank) [8,3] ⟨33551356,[4220,12804480]⟩ b8 = true := by decide +kernel

theorem n283 : fastVisit (leafCols 12 bank) [3] ⟨33547136,[33547136]⟩ b7 = true := join_live n281 n282

theorem n284 : fastVisit (leafCols 12 bank) [7,3] ⟨33547256,[120,29877120]⟩ b7 = true := by decide +kernel

theorem n285 : fastVisit (leafCols 12 bank) [3] ⟨33547136,[33547136]⟩ b6 = true := join_live n283 n284

theorem n286 : fastVisit (leafCols 12 bank) [3] ⟨33547136,[33547136]⟩ b5 = true := join_dead n285 (by decide +kernel)

theorem n287 : fastVisit (leafCols 12 bank) [3] ⟨33547136,[33547136]⟩ b4 = true := join_dead n286 (by decide +kernel)

theorem n288 : fastVisit (leafCols 12 bank) [3] ⟨33547136,[33547136]⟩ b3 = true := join_dead n287 (by decide +kernel)

theorem n289 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b2 = true := join_live n280 n288

theorem n290 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [] ⟨0,[]⟩ b41 = true := by decide +kernel

theorem n291 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [6] ⟨30598016,[30598016]⟩ b41 = true := by decide +kernel

theorem n292 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [] ⟨0,[]⟩ b40 = true := join_live n290 n291

theorem n293 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [5] ⟨31777664,[31777664]⟩ b40 = true := by decide +kernel

theorem n294 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [] ⟨0,[]⟩ b39 = true := join_live n292 n293

theorem n295 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [4] ⟨29418368,[29418368]⟩ b39 = true := by decide +kernel

theorem n296 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [] ⟨0,[]⟩ b38 = true := join_live n294 n295

theorem n297 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [3] ⟨33547136,[33547136]⟩ b38 = true := by decide +kernel

theorem n298 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [] ⟨0,[]⟩ b37 = true := join_live n296 n297

theorem n299 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [2] ⟨9584896,[9584896]⟩ b37 = true := by decide +kernel

theorem n300 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [] ⟨0,[]⟩ b36 = true := join_live n298 n299

theorem n301 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [1] ⟨19169792,[19169792]⟩ b36 = true := by decide +kernel

theorem n302 : fastVisit (leafFrame 12 [2] ⟨9584896,[9584896]⟩) [] ⟨0,[]⟩ b35 = true := join_live n300 n301

theorem n303 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b24 = true := enterColumns 12 bank [2] ⟨9584896,[9584896]⟩ b24 b35 (by decide +kernel) (by decide +kernel) n302

theorem n304 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b23 = true := join_dead n303 (by decide +kernel)

theorem n305 : fastVisit (leafCols 12 bank) [23,2] ⟨29294460,[19709564,8519936]⟩ b23 = true := by decide +kernel

theorem n306 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b22 = true := join_live n304 n305

theorem n307 : fastVisit (leafCols 12 bank) [22,2] ⟨12254584,[2669688,8519936]⟩ b22 = true := by decide +kernel

theorem n308 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b21 = true := join_live n306 n307

theorem n309 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b20 = true := join_dead n308 (by decide +kernel)

theorem n310 : fastVisit (leafCols 12 bank) [20,2] ⟨32964556,[23379660,1179648]⟩ b20 = true := by decide +kernel

theorem n311 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b19 = true := join_live n309 n310

theorem n312 : fastVisit (leafCols 12 bank) [19,2] ⟨30605192,[21020296,1179648]⟩ b19 = true := by decide +kernel

theorem n313 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b18 = true := join_live n311 n312

theorem n314 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b17 = true := join_dead n313 (by decide +kernel)

theorem n315 : fastVisit (leafCols 12 bank) [17,2] ⟨28770124,[19185228,9568512]⟩ b17 = true := by decide +kernel

theorem n316 : fastVisit (leafCols 12 bank) [2] ⟨9584896,[9584896]⟩ b16 = true := join_live n314 n315

theorem n317 : fastVisit (leafFrame 12 [16,2] ⟨9633032,[48136,9568512]⟩) [] ⟨0,[]⟩ b43 = true := by decide +kernel

theorem n318 : fastVisit (leafFrame 12 [16,2] ⟨9633032,[48136,9568512]⟩) [1] ⟨19169792,[19169792]⟩ b43 = true := by decide +kernel

theorem n319 : fastVisit (leafFrame 12 [16,2] ⟨9633032,[48136,9568512]⟩) [] ⟨0,[]⟩ b42 = true := join_live n317 n318

end GainFinite.F12
