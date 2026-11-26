import PEqualNP.ThreeGateGain.FiniteV05P002

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n240 : fastVisit (leafCols 5 bank) [12,8,6] ⟨522538,[298,45056,65536]⟩ b12 = true := by decide +kernel

theorem n241 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b11 = true := join_live n239 n240

theorem n242 : fastVisit (leafCols 5 bank) [11,8,6] ⟨522828,[588,8192,198656]⟩ b11 = true := by decide +kernel

theorem n243 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b10 = true := join_live n241 n242

theorem n244 : fastVisit (leafFrame 5 [10,8,6] ⟨522248,[8,45056,198656]⟩) [] ⟨0,[]⟩ b45 = true := by decide +kernel

theorem n245 : fastVisit (leafFrame 5 [10,8,6] ⟨522248,[8,45056,198656]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n246 : fastVisit (leafFrame 5 [10,8,6] ⟨522248,[8,45056,198656]⟩) [] ⟨0,[]⟩ b44 = true := join_live n244 n245

theorem n247 : fastVisit (leafFrame 5 [10,8,6] ⟨522248,[8,45056,198656]⟩) [1] ⟨299008,[299008]⟩ b44 = true := by decide +kernel

theorem n248 : fastVisit (leafFrame 5 [10,8,6] ⟨522248,[8,45056,198656]⟩) [] ⟨0,[]⟩ b43 = true := join_live n246 n247

theorem n249 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b18 = true := enterColumns 5 bank [10,8,6] ⟨522248,[8,45056,198656]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n248

theorem n250 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b17 = true := join_dead n249 (by decide +kernel)

theorem n251 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b16 = true := join_dead n250 (by decide +kernel)

theorem n252 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b15 = true := join_dead n251 (by decide +kernel)

theorem n253 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b14 = true := join_dead n252 (by decide +kernel)

theorem n254 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b13 = true := join_dead n253 (by decide +kernel)

theorem n255 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b12 = true := join_dead n254 (by decide +kernel)

theorem n256 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b11 = true := join_dead n255 (by decide +kernel)

theorem n257 : fastVisit (leafCols 5 bank) [10,8,6] ⟨522248,[8,45056,198656]⟩ b10 = true := join_dead n256 (by decide +kernel)

theorem n258 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b9 = true := join_live n243 n257

theorem n259 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b8 = true := join_dead n258 (by decide +kernel)

theorem n260 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b7 = true := join_live n228 n259

theorem n261 : fastVisit (leafFrame 5 [7,6] ⟨518144,[40960,460800]⟩) [] ⟨0,[]⟩ b39 = true := by decide +kernel

theorem n262 : fastVisit (leafFrame 5 [7,6] ⟨518144,[40960,460800]⟩) [1] ⟨299008,[299008]⟩ b39 = true := by decide +kernel

theorem n263 : fastVisit (leafFrame 5 [7,6] ⟨518144,[40960,460800]⟩) [] ⟨0,[]⟩ b38 = true := join_live n261 n262

theorem n264 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b18 = true := enterColumns 5 bank [7,6] ⟨518144,[40960,460800]⟩ b18 b38 (by decide +kernel) (by decide +kernel) n263

theorem n265 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b17 = true := join_dead n264 (by decide +kernel)

theorem n266 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b16 = true := join_dead n265 (by decide +kernel)

theorem n267 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b15 = true := join_dead n266 (by decide +kernel)

theorem n268 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b14 = true := join_dead n267 (by decide +kernel)

theorem n269 : fastVisit (leafCols 5 bank) [14,7,6] ⟨523212,[5068,8192,2048]⟩ b14 = true := by decide +kernel

theorem n270 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b13 = true := join_live n268 n269

theorem n271 : fastVisit (leafCols 5 bank) [13,7,6] ⟨519048,[904,40960,2048]⟩ b13 = true := by decide +kernel

theorem n272 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b12 = true := join_live n270 n271

theorem n273 : fastVisit (leafCols 5 bank) [12,7,6] ⟨518442,[298,40960,327680]⟩ b12 = true := by decide +kernel

theorem n274 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b11 = true := join_live n272 n273

theorem n275 : fastVisit (leafCols 5 bank) [11,7,6] ⟨522828,[4684,8192,198656]⟩ b11 = true := by decide +kernel

theorem n276 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b10 = true := join_live n274 n275

theorem n277 : fastVisit (leafFrame 5 [10,7,6] ⟨518152,[8,40960,460800]⟩) [] ⟨0,[]⟩ b42 = true := by decide +kernel

theorem n278 : fastVisit (leafFrame 5 [10,7,6] ⟨518152,[8,40960,460800]⟩) [2] ⟨149504,[149504]⟩ b42 = true := by decide +kernel

theorem n279 : fastVisit (leafFrame 5 [10,7,6] ⟨518152,[8,40960,460800]⟩) [] ⟨0,[]⟩ b41 = true := join_live n277 n278

theorem n280 : fastVisit (leafFrame 5 [10,7,6] ⟨518152,[8,40960,460800]⟩) [1] ⟨299008,[299008]⟩ b42 = true := by decide +kernel

theorem n281 : fastVisit (leafFrame 5 [10,7,6] ⟨518152,[8,40960,460800]⟩) [2,1] ⟨448512,[149504,299008]⟩ b42 = true := by decide +kernel

theorem n282 : fastVisit (leafFrame 5 [10,7,6] ⟨518152,[8,40960,460800]⟩) [1] ⟨299008,[299008]⟩ b41 = true := join_live n280 n281

theorem n283 : fastVisit (leafFrame 5 [10,7,6] ⟨518152,[8,40960,460800]⟩) [] ⟨0,[]⟩ b40 = true := join_live n279 n282

theorem n284 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b18 = true := enterColumns 5 bank [10,7,6] ⟨518152,[8,40960,460800]⟩ b18 b40 (by decide +kernel) (by decide +kernel) n283

theorem n285 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b17 = true := join_dead n284 (by decide +kernel)

theorem n286 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b16 = true := join_dead n285 (by decide +kernel)

theorem n287 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b15 = true := join_dead n286 (by decide +kernel)

theorem n288 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b14 = true := join_dead n287 (by decide +kernel)

theorem n289 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b13 = true := join_dead n288 (by decide +kernel)

theorem n290 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b12 = true := join_dead n289 (by decide +kernel)

theorem n291 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b11 = true := join_dead n290 (by decide +kernel)

theorem n292 : fastVisit (leafCols 5 bank) [10,7,6] ⟨518152,[8,40960,460800]⟩ b10 = true := join_dead n291 (by decide +kernel)

theorem n293 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b9 = true := join_live n276 n292

theorem n294 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b8 = true := join_dead n293 (by decide +kernel)

theorem n295 : fastVisit (leafCols 5 bank) [7,6] ⟨518144,[40960,460800]⟩ b7 = true := join_dead n294 (by decide +kernel)

theorem n296 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b6 = true := join_live n260 n295

theorem n297 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b5 = true := join_live n171 n296

theorem n298 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b16 = true := by decide +kernel

theorem n299 : fastVisit (leafCols 5 bank) [16,5] ⟨520312,[24696,462848]⟩ b16 = true := by decide +kernel

theorem n300 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b15 = true := join_live n298 n299

theorem n301 : fastVisit (leafCols 5 bank) [15,5] ⟨514986,[19370,36864]⟩ b15 = true := by decide +kernel

theorem n302 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b14 = true := join_live n300 n301

theorem n303 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b13 = true := join_dead n302 (by decide +kernel)

theorem n304 : fastVisit (leafCols 5 bank) [13,5] ⟨496520,[904,36864]⟩ b13 = true := by decide +kernel

theorem n305 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b12 = true := join_live n303 n304

theorem n306 : fastVisit (leafCols 5 bank) [12,5] ⟨514346,[18730,364544]⟩ b12 = true := by decide +kernel

theorem n307 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b11 = true := join_live n305 n306

theorem n308 : fastVisit (leafCols 5 bank) [11,5] ⟨496204,[588,196608]⟩ b11 = true := by decide +kernel

theorem n309 : fastVisit (leafCols 5 bank) [5] ⟨495616,[495616]⟩ b10 = true := join_live n307 n308

theorem n310 : fastVisit (leafFrame 5 [10,5] ⟨495624,[8,495616]⟩) [] ⟨0,[]⟩ b47 = true := by decide +kernel

theorem n311 : fastVisit (leafFrame 5 [10,5] ⟨495624,[8,495616]⟩) [1] ⟨299008,[299008]⟩ b47 = true := by decide +kernel

theorem n312 : fastVisit (leafFrame 5 [10,5] ⟨495624,[8,495616]⟩) [] ⟨0,[]⟩ b46 = true := join_live n310 n311

theorem n313 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b18 = true := enterColumns 5 bank [10,5] ⟨495624,[8,495616]⟩ b18 b46 (by decide +kernel) (by decide +kernel) n312

theorem n314 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b17 = true := join_dead n313 (by decide +kernel)

theorem n315 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b16 = true := join_dead n314 (by decide +kernel)

theorem n316 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b15 = true := join_dead n315 (by decide +kernel)

theorem n317 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b14 = true := join_dead n316 (by decide +kernel)

theorem n318 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b13 = true := join_dead n317 (by decide +kernel)

theorem n319 : fastVisit (leafCols 5 bank) [10,5] ⟨495624,[8,495616]⟩ b12 = true := join_dead n318 (by decide +kernel)

end GainFinite.F5
