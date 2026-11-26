import PEqualNP.ThreeGateGain.FiniteV08P002

namespace GainFinite.F8
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n240 : fastVisit (leafCols 8 bank) [9,2] ⟨2094226,[1495040,1170]⟩ b9 = true := by decide +kernel

theorem n241 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b8 = true := join_live n239 n240

theorem n242 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b7 = true := join_dead n241 (by decide +kernel)

theorem n243 : fastVisit (leafCols 8 bank) [7,2] ⟨1830326,[1231140,533650]⟩ b7 = true := by decide +kernel

theorem n244 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b6 = true := join_live n242 n243

theorem n245 : fastVisit (leafCols 8 bank) [6,2] ⟨763026,[163840,533650]⟩ b6 = true := by decide +kernel

theorem n246 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b5 = true := join_live n244 n245

theorem n247 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b4 = true := join_dead n246 (by decide +kernel)

theorem n248 : fastVisit (leafCols 8 bank) [4,2] ⟨2059702,[1460516,74898]⟩ b4 = true := by decide +kernel

theorem n249 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b3 = true := join_live n247 n248

theorem n250 : fastVisit (leafCols 8 bank) [3,2] ⟨1909906,[1310720,74898]⟩ b7 = true := by decide +kernel

theorem n251 : fastVisit (leafCols 8 bank) [7,3,2] ⟨2092470,[182564,262144,9362]⟩ b7 = true := by decide +kernel

theorem n252 : fastVisit (leafCols 8 bank) [3,2] ⟨1909906,[1310720,74898]⟩ b6 = true := join_live n250 n251

theorem n253 : fastVisit (leafCols 8 bank) [6,3,2] ⟨2073746,[163840,1310720,9362]⟩ b12 = true := by decide +kernel

theorem n254 : fastVisit (leafCols 8 bank) [12,6,3,2] ⟨2076306,[2560,163840,1310720,8338]⟩ b12 = true := by decide +kernel

theorem n255 : fastVisit (leafCols 8 bank) [6,3,2] ⟨2073746,[163840,1310720,9362]⟩ b11 = true := join_live n253 n254

theorem n256 : fastVisit (leafCols 8 bank) [6,3,2] ⟨2073746,[163840,1310720,9362]⟩ b10 = true := join_dead n255 (by decide +kernel)

theorem n257 : fastVisit (leafCols 8 bank) [6,3,2] ⟨2073746,[163840,1310720,9362]⟩ b9 = true := join_dead n256 (by decide +kernel)

theorem n258 : fastVisit (leafCols 8 bank) [6,3,2] ⟨2073746,[163840,1310720,9362]⟩ b8 = true := join_dead n257 (by decide +kernel)

theorem n259 : fastVisit (leafCols 8 bank) [6,3,2] ⟨2073746,[163840,1310720,9362]⟩ b7 = true := join_dead n258 (by decide +kernel)

theorem n260 : fastVisit (leafCols 8 bank) [6,3,2] ⟨2073746,[163840,1310720,9362]⟩ b6 = true := join_dead n259 (by decide +kernel)

theorem n261 : fastVisit (leafCols 8 bank) [3,2] ⟨1909906,[1310720,74898]⟩ b5 = true := join_live n252 n260

theorem n262 : fastVisit (leafCols 8 bank) [3,2] ⟨1909906,[1310720,74898]⟩ b4 = true := join_dead n261 (by decide +kernel)

theorem n263 : fastVisit (leafCols 8 bank) [3,2] ⟨1909906,[1310720,74898]⟩ b3 = true := join_dead n262 (by decide +kernel)

theorem n264 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b2 = true := join_live n249 n263

theorem n265 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b1 = true := join_live n233 n264

theorem n266 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b12 = true := by decide +kernel

theorem n267 : fastVisit (leafCols 8 bank) [12,1] ⟨1199908,[1536,1196324]⟩ b12 = true := by decide +kernel

theorem n268 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b11 = true := join_live n266 n267

theorem n269 : fastVisit (leafCols 8 bank) [11,1] ⟨2096566,[898194,2340]⟩ b11 = true := by decide +kernel

theorem n270 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b10 = true := join_live n268 n269

theorem n271 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b9 = true := join_dead n270 (by decide +kernel)

theorem n272 : fastVisit (leafCols 8 bank) [9,1] ⟨2095396,[897024,2340]⟩ b9 = true := by decide +kernel

theorem n273 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b8 = true := join_live n271 n272

theorem n274 : fastVisit (leafCols 8 bank) [8,1] ⟨1830326,[631954,1067300]⟩ b8 = true := by decide +kernel

theorem n275 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b7 = true := join_live n273 n274

theorem n276 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b6 = true := join_dead n275 (by decide +kernel)

theorem n277 : fastVisit (leafCols 8 bank) [6,1] ⟨1296676,[98304,1067300]⟩ b6 = true := by decide +kernel

theorem n278 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b5 = true := join_live n276 n277

theorem n279 : fastVisit (leafCols 8 bank) [5,1] ⟨2059702,[861330,149796]⟩ b5 = true := by decide +kernel

theorem n280 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b4 = true := join_live n278 n279

theorem n281 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b3 = true := join_dead n280 (by decide +kernel)

theorem n282 : fastVisit (leafCols 8 bank) [3,1] ⟨1984804,[786432,149796]⟩ b8 = true := by decide +kernel

theorem n283 : fastVisit (leafCols 8 bank) [8,3,1] ⟨2092470,[107666,262144,18724]⟩ b8 = true := by decide +kernel

theorem n284 : fastVisit (leafCols 8 bank) [3,1] ⟨1984804,[786432,149796]⟩ b7 = true := join_live n282 n283

theorem n285 : fastVisit (leafCols 8 bank) [3,1] ⟨1984804,[786432,149796]⟩ b6 = true := join_dead n284 (by decide +kernel)

theorem n286 : fastVisit (leafCols 8 bank) [6,3,1] ⟨2083108,[98304,786432,18724]⟩ b12 = true := by decide +kernel

theorem n287 : fastVisit (leafCols 8 bank) [12,6,3,1] ⟨2084644,[1536,98304,786432,16676]⟩ b12 = true := by decide +kernel

theorem n288 : fastVisit (leafCols 8 bank) [6,3,1] ⟨2083108,[98304,786432,18724]⟩ b11 = true := join_live n286 n287

theorem n289 : fastVisit (leafCols 8 bank) [6,3,1] ⟨2083108,[98304,786432,18724]⟩ b10 = true := join_dead n288 (by decide +kernel)

theorem n290 : fastVisit (leafCols 8 bank) [6,3,1] ⟨2083108,[98304,786432,18724]⟩ b9 = true := join_dead n289 (by decide +kernel)

theorem n291 : fastVisit (leafCols 8 bank) [6,3,1] ⟨2083108,[98304,786432,18724]⟩ b8 = true := join_dead n290 (by decide +kernel)

theorem n292 : fastVisit (leafCols 8 bank) [6,3,1] ⟨2083108,[98304,786432,18724]⟩ b7 = true := join_dead n291 (by decide +kernel)

theorem n293 : fastVisit (leafCols 8 bank) [6,3,1] ⟨2083108,[98304,786432,18724]⟩ b6 = true := join_dead n292 (by decide +kernel)

theorem n294 : fastVisit (leafCols 8 bank) [3,1] ⟨1984804,[786432,149796]⟩ b5 = true := join_live n285 n293

theorem n295 : fastVisit (leafCols 8 bank) [3,1] ⟨1984804,[786432,149796]⟩ b4 = true := join_dead n294 (by decide +kernel)

theorem n296 : fastVisit (leafCols 8 bank) [3,1] ⟨1984804,[786432,149796]⟩ b3 = true := join_dead n295 (by decide +kernel)

theorem n297 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b2 = true := join_live n281 n296

theorem n298 : fastVisit (leafCols 8 bank) [2,1] ⟨1797558,[599186,1198372]⟩ b3 = true := by decide +kernel

theorem n299 : fastVisit (leafCols 8 bank) [3,2,1] ⟨2059702,[262144,74898,149796]⟩ b3 = true := by decide +kernel

theorem n300 : fastVisit (leafCols 8 bank) [2,1] ⟨1797558,[599186,1198372]⟩ b2 = true := join_live n298 n299

theorem n301 : fastVisit (leafCols 8 bank) [1] ⟨1198372,[1198372]⟩ b1 = true := join_live n297 n300

theorem n302 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b0 = true := join_live n265 n301

theorem passed : quickHost 8 = true := by
  rw [← leafHost_sparse]
  have pool_correct : sparseRows 8 = bank := by decide +kernel
  rw [pool_correct]
  exact n302

end GainFinite.F8
