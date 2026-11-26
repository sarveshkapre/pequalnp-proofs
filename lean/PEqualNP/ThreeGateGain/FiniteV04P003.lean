import PEqualNP.ThreeGateGain.FiniteV04P002

namespace GainFinite.F4
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n240 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b5 = true := join_live n229 n239

theorem n241 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b4 = true := join_dead n240 (by decide +kernel)

theorem n242 : fastVisit (leafFrame 4 [4,1] ⟨18432,[2048,16384]⟩) [] ⟨0,[]⟩ b30 = true := by decide +kernel

theorem n243 : fastVisit (leafFrame 4 [4,1] ⟨18432,[2048,16384]⟩) [1] ⟨16384,[16384]⟩ b30 = true := by decide +kernel

theorem n244 : fastVisit (leafFrame 4 [4,1] ⟨18432,[2048,16384]⟩) [] ⟨0,[]⟩ b29 = true := join_live n242 n243

theorem n245 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b14 = true := enterColumns 4 bank [4,1] ⟨18432,[2048,16384]⟩ b14 b29 (by decide +kernel) (by decide +kernel) n244

theorem n246 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b13 = true := join_dead n245 (by decide +kernel)

theorem n247 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b12 = true := join_dead n246 (by decide +kernel)

theorem n248 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b11 = true := join_dead n247 (by decide +kernel)

theorem n249 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b10 = true := join_dead n248 (by decide +kernel)

theorem n250 : fastVisit (leafCols 4 bank) [10,4,1] ⟨26784,[8352,2048,16384]⟩ b10 = true := by decide +kernel

theorem n251 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b9 = true := join_live n249 n250

theorem n252 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b8 = true := join_dead n251 (by decide +kernel)

theorem n253 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [] ⟨0,[]⟩ b34 = true := by decide +kernel

theorem n254 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [3] ⟨28672,[28672]⟩ b36 = true := by decide +kernel

theorem n255 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [5,3] ⟨31744,[3072,12288]⟩ b36 = true := by decide +kernel

theorem n256 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [3] ⟨28672,[28672]⟩ b35 = true := join_live n254 n255

theorem n257 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [4,3] ⟨30720,[2048,28672]⟩ b35 = true := by decide +kernel

theorem n258 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [3] ⟨28672,[28672]⟩ b34 = true := join_live n256 n257

theorem n259 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [] ⟨0,[]⟩ b33 = true := join_live n253 n258

theorem n260 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [2] ⟨8192,[8192]⟩ b33 = true := by decide +kernel

theorem n261 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [] ⟨0,[]⟩ b32 = true := join_live n259 n260

theorem n262 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [1] ⟨16384,[16384]⟩ b32 = true := by decide +kernel

theorem n263 : fastVisit (leafFrame 4 [8,4,1] ⟨18560,[128,2048,16384]⟩) [] ⟨0,[]⟩ b31 = true := join_live n261 n262

theorem n264 : fastVisit (leafCols 4 bank) [8,4,1] ⟨18560,[128,2048,16384]⟩ b14 = true := enterColumns 4 bank [8,4,1] ⟨18560,[128,2048,16384]⟩ b14 b31 (by decide +kernel) (by decide +kernel) n263

theorem n265 : fastVisit (leafCols 4 bank) [8,4,1] ⟨18560,[128,2048,16384]⟩ b13 = true := join_dead n264 (by decide +kernel)

theorem n266 : fastVisit (leafCols 4 bank) [8,4,1] ⟨18560,[128,2048,16384]⟩ b12 = true := join_dead n265 (by decide +kernel)

theorem n267 : fastVisit (leafCols 4 bank) [8,4,1] ⟨18560,[128,2048,16384]⟩ b11 = true := join_dead n266 (by decide +kernel)

theorem n268 : fastVisit (leafCols 4 bank) [8,4,1] ⟨18560,[128,2048,16384]⟩ b10 = true := join_dead n267 (by decide +kernel)

theorem n269 : fastVisit (leafCols 4 bank) [8,4,1] ⟨18560,[128,2048,16384]⟩ b9 = true := join_dead n268 (by decide +kernel)

theorem n270 : fastVisit (leafCols 4 bank) [8,4,1] ⟨18560,[128,2048,16384]⟩ b8 = true := join_dead n269 (by decide +kernel)

theorem n271 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b7 = true := join_live n252 n270

theorem n272 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b6 = true := join_dead n271 (by decide +kernel)

theorem n273 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b5 = true := join_dead n272 (by decide +kernel)

theorem n274 : fastVisit (leafCols 4 bank) [4,1] ⟨18432,[2048,16384]⟩ b4 = true := join_dead n273 (by decide +kernel)

theorem n275 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b3 = true := join_live n241 n274

theorem n276 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b2 = true := join_dead n275 (by decide +kernel)

theorem n277 : fastVisit (leafFrame 4 [2,1] ⟨24576,[8192,16384]⟩) [] ⟨0,[]⟩ b38 = true := by decide +kernel

theorem n278 : fastVisit (leafFrame 4 [2,1] ⟨24576,[8192,16384]⟩) [1] ⟨16384,[16384]⟩ b38 = true := by decide +kernel

theorem n279 : fastVisit (leafFrame 4 [2,1] ⟨24576,[8192,16384]⟩) [] ⟨0,[]⟩ b37 = true := join_live n277 n278

theorem n280 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b14 = true := enterColumns 4 bank [2,1] ⟨24576,[8192,16384]⟩ b14 b37 (by decide +kernel) (by decide +kernel) n279

theorem n281 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b13 = true := join_dead n280 (by decide +kernel)

theorem n282 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b12 = true := join_dead n281 (by decide +kernel)

theorem n283 : fastVisit (leafCols 4 bank) [12,2,1] ⟨26760,[2184,8192,16384]⟩ b12 = true := by decide +kernel

theorem n284 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b11 = true := join_live n282 n283

theorem n285 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b10 = true := join_dead n284 (by decide +kernel)

theorem n286 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b9 = true := join_dead n285 (by decide +kernel)

theorem n287 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b8 = true := join_dead n286 (by decide +kernel)

theorem n288 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [] ⟨0,[]⟩ b42 = true := by decide +kernel

theorem n289 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b44 = true := by decide +kernel

theorem n290 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [5,3] ⟨31744,[3072,12288]⟩ b44 = true := by decide +kernel

theorem n291 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b43 = true := join_live n289 n290

theorem n292 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [4,3] ⟨30720,[2048,28672]⟩ b43 = true := by decide +kernel

theorem n293 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b42 = true := join_live n291 n292

theorem n294 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [] ⟨0,[]⟩ b41 = true := join_live n288 n293

theorem n295 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [2] ⟨8192,[8192]⟩ b41 = true := by decide +kernel

theorem n296 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [] ⟨0,[]⟩ b40 = true := join_live n294 n295

theorem n297 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [1] ⟨16384,[16384]⟩ b40 = true := by decide +kernel

theorem n298 : fastVisit (leafFrame 4 [8,2,1] ⟨24704,[128,8192,16384]⟩) [] ⟨0,[]⟩ b39 = true := join_live n296 n297

theorem n299 : fastVisit (leafCols 4 bank) [8,2,1] ⟨24704,[128,8192,16384]⟩ b14 = true := enterColumns 4 bank [8,2,1] ⟨24704,[128,8192,16384]⟩ b14 b39 (by decide +kernel) (by decide +kernel) n298

theorem n300 : fastVisit (leafCols 4 bank) [8,2,1] ⟨24704,[128,8192,16384]⟩ b13 = true := join_dead n299 (by decide +kernel)

theorem n301 : fastVisit (leafCols 4 bank) [8,2,1] ⟨24704,[128,8192,16384]⟩ b12 = true := join_dead n300 (by decide +kernel)

theorem n302 : fastVisit (leafCols 4 bank) [8,2,1] ⟨24704,[128,8192,16384]⟩ b11 = true := join_dead n301 (by decide +kernel)

theorem n303 : fastVisit (leafCols 4 bank) [8,2,1] ⟨24704,[128,8192,16384]⟩ b10 = true := join_dead n302 (by decide +kernel)

theorem n304 : fastVisit (leafCols 4 bank) [8,2,1] ⟨24704,[128,8192,16384]⟩ b9 = true := join_dead n303 (by decide +kernel)

theorem n305 : fastVisit (leafCols 4 bank) [8,2,1] ⟨24704,[128,8192,16384]⟩ b8 = true := join_dead n304 (by decide +kernel)

theorem n306 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b7 = true := join_live n287 n305

theorem n307 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b6 = true := join_dead n306 (by decide +kernel)

theorem n308 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b5 = true := join_dead n307 (by decide +kernel)

theorem n309 : fastVisit (leafCols 4 bank) [2,1] ⟨24576,[8192,16384]⟩ b4 = true := join_dead n308 (by decide +kernel)

theorem n310 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [] ⟨0,[]⟩ b48 = true := by decide +kernel

theorem n311 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b50 = true := by decide +kernel

theorem n312 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [5,3] ⟨31744,[3072,12288]⟩ b50 = true := by decide +kernel

theorem n313 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b49 = true := join_live n311 n312

theorem n314 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [4,3] ⟨30720,[2048,28672]⟩ b49 = true := by decide +kernel

theorem n315 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [3] ⟨28672,[28672]⟩ b48 = true := join_live n313 n314

theorem n316 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [] ⟨0,[]⟩ b47 = true := join_live n310 n315

theorem n317 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [2] ⟨8192,[8192]⟩ b47 = true := by decide +kernel

theorem n318 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [] ⟨0,[]⟩ b46 = true := join_live n316 n317

theorem n319 : fastVisit (leafFrame 4 [4,2,1] ⟨26624,[2048,8192,16384]⟩) [1] ⟨16384,[16384]⟩ b46 = true := by decide +kernel

end GainFinite.F4
