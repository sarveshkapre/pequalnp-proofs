import PEqualNP.ThreeGateGain.FiniteV10P002

namespace GainFinite.F10
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n240 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b7 = true := join_live n238 n239

theorem n241 : fastVisit (leafCols 10 bank) [7,5] ⟨133955070,[11556908,50955458]⟩ b7 = true := by decide +kernel

theorem n242 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b6 = true := join_live n240 n241

theorem n243 : fastVisit (leafCols 10 bank) [6,5] ⟨132904442,[10506280,118195650]⟩ b6 = true := by decide +kernel

theorem n244 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b5 = true := join_live n242 n243

theorem n245 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b4 = true := join_live n227 n244

theorem n246 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b14 = true := by decide +kernel

theorem n247 : fastVisit (leafCols 10 bank) [14,4] ⟨134213110,[7087122,18468]⟩ b14 = true := by decide +kernel

theorem n248 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b13 = true := join_live n246 n247

theorem n249 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b12 = true := join_dead n248 (by decide +kernel)

theorem n250 : fastVisit (leafCols 10 bank) [12,4] ⟨134203876,[7077888,18468]⟩ b12 = true := by decide +kernel

theorem n251 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b11 = true := join_live n249 n250

theorem n252 : fastVisit (leafCols 10 bank) [11,4] ⟨134213110,[7087122,182628]⟩ b11 = true := by decide +kernel

theorem n253 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b10 = true := join_live n251 n252

theorem n254 : fastVisit (leafCols 10 bank) [10,4] ⟨134203876,[7077888,98496]⟩ b10 = true := by decide +kernel

theorem n255 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b9 = true := join_live n253 n254

theorem n256 : fastVisit (leafCols 10 bank) [9,4] ⟨134203876,[7077888,248292]⟩ b9 = true := by decide +kernel

theorem n257 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b8 = true := join_live n255 n256

theorem n258 : fastVisit (leafCols 10 bank) [8,4] ⟨133955070,[6829082,85100868]⟩ b8 = true := by decide +kernel

theorem n259 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b7 = true := join_live n257 n258

theorem n260 : fastVisit (leafCols 10 bank) [7,4] ⟨133429756,[6303768,50430144]⟩ b7 = true := by decide +kernel

theorem n261 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b6 = true := join_live n259 n260

theorem n262 : fastVisit (leafCols 10 bank) [6,4] ⟨133429756,[6303768,118720964]⟩ b6 = true := by decide +kernel

theorem n263 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b5 = true := join_live n261 n262

theorem n264 : fastVisit (leafCols 10 bank) [5,4] ⟨131853814,[4727826,9455652]⟩ b5 = true := by decide +kernel

theorem n265 : fastVisit (leafCols 10 bank) [4] ⟨127125988,[127125988]⟩ b4 = true := join_live n263 n264

theorem n266 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b3 = true := join_live n245 n265

theorem n267 : fastVisit (leafFrame 10 [3] ⟨117670336,[117670336]⟩) [] ⟨0,[]⟩ b42 = true := by decide +kernel

theorem n268 : fastVisit (leafFrame 10 [3] ⟨117670336,[117670336]⟩) [3] ⟨117670336,[117670336]⟩ b42 = true := by decide +kernel

theorem n269 : fastVisit (leafFrame 10 [3] ⟨117670336,[117670336]⟩) [] ⟨0,[]⟩ b41 = true := join_live n267 n268

theorem n270 : fastVisit (leafFrame 10 [3] ⟨117670336,[117670336]⟩) [2] ⟨38347922,[38347922]⟩ b41 = true := by decide +kernel

theorem n271 : fastVisit (leafFrame 10 [3] ⟨117670336,[117670336]⟩) [] ⟨0,[]⟩ b40 = true := join_live n269 n270

theorem n272 : fastVisit (leafFrame 10 [3] ⟨117670336,[117670336]⟩) [1] ⟨76695844,[76695844]⟩ b40 = true := by decide +kernel

theorem n273 : fastVisit (leafFrame 10 [3] ⟨117670336,[117670336]⟩) [] ⟨0,[]⟩ b39 = true := join_live n271 n272

theorem n274 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b26 = true := enterColumns 10 bank [3] ⟨117670336,[117670336]⟩ b26 b39 (by decide +kernel) (by decide +kernel) n273

theorem n275 : fastVisit (leafCols 10 bank) [26,3] ⟨132907002,[15236666,83886400]⟩ b26 = true := by decide +kernel

theorem n276 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b25 = true := join_live n274 n275

theorem n277 : fastVisit (leafCols 10 bank) [25,3] ⟨133431292,[15760956,50331840]⟩ b25 = true := by decide +kernel

theorem n278 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b24 = true := join_live n276 n277

theorem n279 : fastVisit (leafCols 10 bank) [24,3] ⟨132382712,[14712376,117440960]⟩ b24 = true := by decide +kernel

theorem n280 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b23 = true := join_live n278 n279

theorem n281 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b22 = true := join_dead n280 (by decide +kernel)

theorem n282 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b21 = true := join_dead n281 (by decide +kernel)

theorem n283 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b20 = true := join_dead n282 (by decide +kernel)

theorem n284 : fastVisit (leafCols 10 bank) [20,3] ⟨122421202,[4750866,83886400]⟩ b20 = true := by decide +kernel

theorem n285 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b19 = true := join_live n283 n284

theorem n286 : fastVisit (leafCols 10 bank) [19,3] ⟨127139812,[9469476,50331840]⟩ b19 = true := by decide +kernel

theorem n287 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b18 = true := join_live n285 n286

theorem n288 : fastVisit (leafCols 10 bank) [18,3] ⟨117702592,[32256,117440960]⟩ b18 = true := by decide +kernel

theorem n289 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b17 = true := join_live n287 n288

theorem n290 : fastVisit (leafCols 10 bank) [17,3] ⟨134215162,[16544826,164160]⟩ b17 = true := by decide +kernel

theorem n291 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b16 = true := join_live n289 n290

theorem n292 : fastVisit (leafCols 10 bank) [16,3] ⟨134216188,[16545852,98496]⟩ b16 = true := by decide +kernel

theorem n293 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b15 = true := join_live n291 n292

theorem n294 : fastVisit (leafCols 10 bank) [15,3] ⟨134214136,[16543800,229824]⟩ b15 = true := by decide +kernel

theorem n295 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b14 = true := join_live n293 n294

theorem n296 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b13 = true := join_dead n295 (by decide +kernel)

theorem n297 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b12 = true := join_dead n296 (by decide +kernel)

theorem n298 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b11 = true := join_dead n297 (by decide +kernel)

theorem n299 : fastVisit (leafCols 10 bank) [11,3] ⟨134194642,[16524306,164160]⟩ b11 = true := by decide +kernel

theorem n300 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b10 = true := join_live n298 n299

theorem n301 : fastVisit (leafCols 10 bank) [10,3] ⟨134203876,[16533540,98496]⟩ b10 = true := by decide +kernel

theorem n302 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b9 = true := join_live n300 n301

theorem n303 : fastVisit (leafCols 10 bank) [9,3] ⟨134185408,[16515072,229824]⟩ b9 = true := by decide +kernel

theorem n304 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b8 = true := join_live n302 n303

theorem n305 : fastVisit (leafCols 10 bank) [8,3] ⟨132904442,[15234106,84050240]⟩ b8 = true := by decide +kernel

theorem n306 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b7 = true := join_live n304 n305

theorem n307 : fastVisit (leafCols 10 bank) [7,3] ⟨133429756,[15759420,50430144]⟩ b7 = true := by decide +kernel

theorem n308 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b6 = true := join_live n306 n307

theorem n309 : fastVisit (leafCols 10 bank) [6,3] ⟨132379128,[14708792,117670336]⟩ b6 = true := by decide +kernel

theorem n310 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b5 = true := join_live n308 n309

theorem n311 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b4 = true := join_dead n310 (by decide +kernel)

theorem n312 : fastVisit (leafCols 10 bank) [3] ⟨117670336,[117670336]⟩ b3 = true := join_dead n311 (by decide +kernel)

theorem n313 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b2 = true := join_live n266 n312

theorem n314 : fastVisit (leafFrame 10 [2] ⟨38347922,[38347922]⟩) [] ⟨0,[]⟩ b46 = true := by decide +kernel

theorem n315 : fastVisit (leafFrame 10 [2] ⟨38347922,[38347922]⟩) [5] ⟨122398162,[122398162]⟩ b46 = true := by decide +kernel

theorem n316 : fastVisit (leafFrame 10 [2] ⟨38347922,[38347922]⟩) [] ⟨0,[]⟩ b45 = true := join_live n314 n315

theorem n317 : fastVisit (leafFrame 10 [2] ⟨38347922,[38347922]⟩) [3] ⟨117670336,[117670336]⟩ b45 = true := by decide +kernel

theorem n318 : fastVisit (leafFrame 10 [2] ⟨38347922,[38347922]⟩) [] ⟨0,[]⟩ b44 = true := join_live n316 n317

theorem n319 : fastVisit (leafFrame 10 [2] ⟨38347922,[38347922]⟩) [2] ⟨38347922,[38347922]⟩ b44 = true := by decide +kernel

end GainFinite.F10
