import PEqualNP.ThreeGateGain.FiniteV10P001

namespace GainFinite.F10
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n160 : fastVisit (leafCols 10 bank) [12,8] ⟨134215162,[85360960,29754]⟩ b12 = true := by decide +kernel

theorem n161 : fastVisit (leafCols 10 bank) [8] ⟨48854202,[48854202]⟩ b11 = true := join_live n159 n160

theorem n162 : fastVisit (leafCols 10 bank) [11,8] ⟨134051002,[85196800,20520]⟩ b11 = true := by decide +kernel

theorem n163 : fastVisit (leafCols 10 bank) [8] ⟨48854202,[48854202]⟩ b10 = true := join_live n161 n162

theorem n164 : fastVisit (leafCols 10 bank) [10,8] ⟨134184382,[85330180,79002]⟩ b10 = true := by decide +kernel

theorem n165 : fastVisit (leafCols 10 bank) [8] ⟨48854202,[48854202]⟩ b9 = true := join_live n163 n164

theorem n166 : fastVisit (leafCols 10 bank) [9,8] ⟨134051002,[85196800,95418]⟩ b9 = true := by decide +kernel

theorem n167 : fastVisit (leafCols 10 bank) [8] ⟨48854202,[48854202]⟩ b8 = true := join_live n165 n166

theorem n168 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b7 = true := join_live n152 n167

theorem n169 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b15 = true := by decide +kernel

theorem n170 : fastVisit (leafCols 10 bank) [15,7] ⟨134117692,[51118080,133380]⟩ b15 = true := by decide +kernel

theorem n171 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b14 = true := join_live n169 n170

theorem n172 : fastVisit (leafCols 10 bank) [14,7] ⟨134217214,[51217602,22572]⟩ b14 = true := by decide +kernel

theorem n173 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b13 = true := join_live n171 n172

theorem n174 : fastVisit (leafCols 10 bank) [13,7] ⟨134216188,[51216576,12312]⟩ b13 = true := by decide +kernel

theorem n175 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b12 = true := join_live n173 n174

theorem n176 : fastVisit (leafCols 10 bank) [12,7] ⟨134216188,[51216576,30780]⟩ b12 = true := by decide +kernel

theorem n177 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b11 = true := join_live n175 n176

theorem n178 : fastVisit (leafCols 10 bank) [11,7] ⟨134184382,[51184770,153900]⟩ b11 = true := by decide +kernel

theorem n179 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b10 = true := join_live n177 n178

theorem n180 : fastVisit (leafCols 10 bank) [10,7] ⟨134117692,[51118080,12312]⟩ b10 = true := by decide +kernel

theorem n181 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b9 = true := join_live n179 n180

theorem n182 : fastVisit (leafCols 10 bank) [9,7] ⟨134117692,[51118080,162108]⟩ b9 = true := by decide +kernel

theorem n183 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b8 = true := join_live n181 n182

theorem n184 : fastVisit (leafCols 10 bank) [8,7] ⟨117145022,[34145410,68290820]⟩ b8 = true := by decide +kernel

theorem n185 : fastVisit (leafCols 10 bank) [7] ⟨82999612,[82999612]⟩ b7 = true := join_live n183 n184

theorem n186 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b6 = true := join_live n168 n185

theorem n187 : fastVisit (leafFrame 10 [6] ⟨14708792,[14708792]⟩) [] ⟨0,[]⟩ b38 = true := by decide +kernel

theorem n188 : fastVisit (leafFrame 10 [6] ⟨14708792,[14708792]⟩) [6] ⟨14708792,[14708792]⟩ b38 = true := by decide +kernel

theorem n189 : fastVisit (leafFrame 10 [6] ⟨14708792,[14708792]⟩) [] ⟨0,[]⟩ b37 = true := join_live n187 n188

theorem n190 : fastVisit (leafFrame 10 [6] ⟨14708792,[14708792]⟩) [2] ⟨38347922,[38347922]⟩ b37 = true := by decide +kernel

theorem n191 : fastVisit (leafFrame 10 [6] ⟨14708792,[14708792]⟩) [] ⟨0,[]⟩ b36 = true := join_live n189 n190

theorem n192 : fastVisit (leafFrame 10 [6] ⟨14708792,[14708792]⟩) [1] ⟨76695844,[76695844]⟩ b36 = true := by decide +kernel

theorem n193 : fastVisit (leafFrame 10 [6] ⟨14708792,[14708792]⟩) [] ⟨0,[]⟩ b35 = true := join_live n191 n192

theorem n194 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b26 = true := enterColumns 10 bank [6] ⟨14708792,[14708792]⟩ b26 b35 (by decide +kernel) (by decide +kernel) n193

theorem n195 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b25 = true := join_dead n194 (by decide +kernel)

theorem n196 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b24 = true := join_dead n195 (by decide +kernel)

theorem n197 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b23 = true := join_dead n196 (by decide +kernel)

theorem n198 : fastVisit (leafCols 10 bank) [23,6] ⟨132907002,[118198210,10485800]⟩ b23 = true := by decide +kernel

theorem n199 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b22 = true := join_live n197 n198

theorem n200 : fastVisit (leafCols 10 bank) [22,6] ⟨133431292,[118722500,6291480]⟩ b22 = true := by decide +kernel

theorem n201 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b21 = true := join_live n199 n200

theorem n202 : fastVisit (leafCols 10 bank) [21,6] ⟨132382712,[117673920,14680120]⟩ b21 = true := by decide +kernel

theorem n203 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b20 = true := join_live n201 n202

theorem n204 : fastVisit (leafCols 10 bank) [20,6] ⟨49020602,[34311810,10485800]⟩ b20 = true := by decide +kernel

theorem n205 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b19 = true := join_live n203 n204

theorem n206 : fastVisit (leafCols 10 bank) [19,6] ⟨83099452,[68390660,6291480]⟩ b19 = true := by decide +kernel

theorem n207 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b18 = true := join_live n205 n206

theorem n208 : fastVisit (leafCols 10 bank) [18,6] ⟨14941752,[232960,14680120]⟩ b18 = true := by decide +kernel

theorem n209 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b17 = true := join_live n207 n208

theorem n210 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b16 = true := join_dead n209 (by decide +kernel)

theorem n211 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b15 = true := join_dead n210 (by decide +kernel)

theorem n212 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b14 = true := join_dead n211 (by decide +kernel)

theorem n213 : fastVisit (leafCols 10 bank) [14,6] ⟨134215162,[119506370,20520]⟩ b14 = true := by decide +kernel

theorem n214 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b13 = true := join_live n212 n213

theorem n215 : fastVisit (leafCols 10 bank) [13,6] ⟨134216188,[119507396,12312]⟩ b13 = true := by decide +kernel

theorem n216 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b12 = true := join_live n214 n215

theorem n217 : fastVisit (leafCols 10 bank) [12,6] ⟨134214136,[119505344,28728]⟩ b12 = true := by decide +kernel

theorem n218 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b11 = true := join_live n216 n217

theorem n219 : fastVisit (leafCols 10 bank) [11,6] ⟨134051002,[119342210,20520]⟩ b11 = true := by decide +kernel

theorem n220 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b10 = true := join_live n218 n219

theorem n221 : fastVisit (leafCols 10 bank) [10,6] ⟨134117692,[119408900,12312]⟩ b10 = true := by decide +kernel

theorem n222 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b9 = true := join_live n220 n221

theorem n223 : fastVisit (leafCols 10 bank) [9,6] ⟨133984312,[119275520,28728]⟩ b9 = true := by decide +kernel

theorem n224 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b8 = true := join_live n222 n223

theorem n225 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b7 = true := join_dead n224 (by decide +kernel)

theorem n226 : fastVisit (leafCols 10 bank) [6] ⟨14708792,[14708792]⟩ b6 = true := join_dead n225 (by decide +kernel)

theorem n227 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b5 = true := join_live n186 n226

theorem n228 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b13 = true := by decide +kernel

theorem n229 : fastVisit (leafCols 10 bank) [13,5] ⟨134213110,[11814948,9234]⟩ b13 = true := by decide +kernel

theorem n230 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b12 = true := join_live n228 n229

theorem n231 : fastVisit (leafCols 10 bank) [12,5] ⟨134194642,[11796480,9234]⟩ b12 = true := by decide +kernel

theorem n232 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b11 = true := join_live n230 n231

theorem n233 : fastVisit (leafCols 10 bank) [11,5] ⟨134194642,[11796480,164160]⟩ b11 = true := by decide +kernel

theorem n234 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b10 = true := join_live n232 n233

theorem n235 : fastVisit (leafCols 10 bank) [10,5] ⟨134213110,[11814948,107730]⟩ b10 = true := by decide +kernel

theorem n236 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b9 = true := join_live n234 n235

theorem n237 : fastVisit (leafCols 10 bank) [9,5] ⟨134194642,[11796480,239058]⟩ b9 = true := by decide +kernel

theorem n238 : fastVisit (leafCols 10 bank) [5] ⟨122398162,[122398162]⟩ b8 = true := join_live n236 n237

theorem n239 : fastVisit (leafCols 10 bank) [8,5] ⟨132904442,[10506280,84050240]⟩ b8 = true := by decide +kernel

end GainFinite.F10
