import PEqualNP.ThreeGateGain.FiniteV08P001

namespace GainFinite.F8
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n160 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [1] ⟨1198372,[1198372]⟩ b32 = true := by decide +kernel

theorem n161 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [] ⟨0,[]⟩ b31 = true := join_live n159 n160

theorem n162 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b20 = true := enterColumns 8 bank [3] ⟨1835008,[1835008]⟩ b20 b31 (by decide +kernel) (by decide +kernel) n161

theorem n163 : fastVisit (leafCols 8 bank) [20,3] ⟨2076346,[241338,1310720]⟩ b20 = true := by decide +kernel

theorem n164 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b19 = true := join_live n162 n163

theorem n165 : fastVisit (leafCols 8 bank) [19,3] ⟨2084668,[249660,786432]⟩ b19 = true := by decide +kernel

theorem n166 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b18 = true := join_live n164 n165

theorem n167 : fastVisit (leafCols 8 bank) [18,3] ⟨2068024,[233016,1835008]⟩ b18 = true := by decide +kernel

theorem n168 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b17 = true := join_live n166 n167

theorem n169 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b16 = true := join_dead n168 (by decide +kernel)

theorem n170 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b15 = true := join_dead n169 (by decide +kernel)

theorem n171 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b14 = true := join_dead n170 (by decide +kernel)

theorem n172 : fastVisit (leafCols 8 bank) [14,3] ⟨1912466,[77458,1310720]⟩ b14 = true := by decide +kernel

theorem n173 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b13 = true := join_live n171 n172

theorem n174 : fastVisit (leafCols 8 bank) [13,3] ⟨1986340,[151332,786432]⟩ b13 = true := by decide +kernel

theorem n175 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b12 = true := join_live n173 n174

theorem n176 : fastVisit (leafFrame 8 [12,3] ⟨1838592,[3584,1835008]⟩) [] ⟨0,[]⟩ b37 = true := by decide +kernel

theorem n177 : fastVisit (leafFrame 8 [12,3] ⟨1838592,[3584,1835008]⟩) [1] ⟨1198372,[1198372]⟩ b37 = true := by decide +kernel

theorem n178 : fastVisit (leafFrame 8 [12,3] ⟨1838592,[3584,1835008]⟩) [] ⟨0,[]⟩ b36 = true := join_live n176 n177

theorem n179 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b20 = true := enterColumns 8 bank [12,3] ⟨1838592,[3584,1835008]⟩ b20 b36 (by decide +kernel) (by decide +kernel) n178

theorem n180 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b19 = true := join_dead n179 (by decide +kernel)

theorem n181 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b18 = true := join_dead n180 (by decide +kernel)

theorem n182 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b17 = true := join_dead n181 (by decide +kernel)

theorem n183 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b16 = true := join_dead n182 (by decide +kernel)

theorem n184 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b15 = true := join_dead n183 (by decide +kernel)

theorem n185 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b14 = true := join_dead n184 (by decide +kernel)

theorem n186 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b13 = true := join_dead n185 (by decide +kernel)

theorem n187 : fastVisit (leafCols 8 bank) [12,3] ⟨1838592,[3584,1835008]⟩ b12 = true := join_dead n186 (by decide +kernel)

theorem n188 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b11 = true := join_live n175 n187

theorem n189 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b10 = true := join_dead n188 (by decide +kernel)

theorem n190 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b9 = true := join_dead n189 (by decide +kernel)

theorem n191 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b8 = true := join_dead n190 (by decide +kernel)

theorem n192 : fastVisit (leafCols 8 bank) [8,3] ⟨2073746,[238738,1310720]⟩ b8 = true := by decide +kernel

theorem n193 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b7 = true := join_live n191 n192

theorem n194 : fastVisit (leafCols 8 bank) [7,3] ⟨2083108,[248100,786432]⟩ b7 = true := by decide +kernel

theorem n195 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b6 = true := join_live n193 n194

theorem n196 : fastVisit (leafFrame 8 [6,3] ⟨2064384,[229376,1835008]⟩) [] ⟨0,[]⟩ b39 = true := by decide +kernel

theorem n197 : fastVisit (leafFrame 8 [6,3] ⟨2064384,[229376,1835008]⟩) [1] ⟨1198372,[1198372]⟩ b39 = true := by decide +kernel

theorem n198 : fastVisit (leafFrame 8 [6,3] ⟨2064384,[229376,1835008]⟩) [] ⟨0,[]⟩ b38 = true := join_live n196 n197

theorem n199 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b20 = true := enterColumns 8 bank [6,3] ⟨2064384,[229376,1835008]⟩ b20 b38 (by decide +kernel) (by decide +kernel) n198

theorem n200 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b19 = true := join_dead n199 (by decide +kernel)

theorem n201 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b18 = true := join_dead n200 (by decide +kernel)

theorem n202 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b17 = true := join_dead n201 (by decide +kernel)

theorem n203 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b16 = true := join_dead n202 (by decide +kernel)

theorem n204 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b15 = true := join_dead n203 (by decide +kernel)

theorem n205 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b14 = true := join_dead n204 (by decide +kernel)

theorem n206 : fastVisit (leafCols 8 bank) [14,6,3] ⟨2076306,[11922,163840,1310720]⟩ b14 = true := by decide +kernel

theorem n207 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b13 = true := join_live n205 n206

theorem n208 : fastVisit (leafCols 8 bank) [13,6,3] ⟨2084644,[20260,98304,786432]⟩ b13 = true := by decide +kernel

theorem n209 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b12 = true := join_live n207 n208

theorem n210 : fastVisit (leafFrame 8 [12,6,3] ⟨2067968,[3584,229376,1835008]⟩) [] ⟨0,[]⟩ b42 = true := by decide +kernel

theorem n211 : fastVisit (leafFrame 8 [12,6,3] ⟨2067968,[3584,229376,1835008]⟩) [2] ⟨599186,[599186]⟩ b42 = true := by decide +kernel

theorem n212 : fastVisit (leafFrame 8 [12,6,3] ⟨2067968,[3584,229376,1835008]⟩) [] ⟨0,[]⟩ b41 = true := join_live n210 n211

theorem n213 : fastVisit (leafFrame 8 [12,6,3] ⟨2067968,[3584,229376,1835008]⟩) [1] ⟨1198372,[1198372]⟩ b41 = true := by decide +kernel

theorem n214 : fastVisit (leafFrame 8 [12,6,3] ⟨2067968,[3584,229376,1835008]⟩) [] ⟨0,[]⟩ b40 = true := join_live n212 n213

theorem n215 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b20 = true := enterColumns 8 bank [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b20 b40 (by decide +kernel) (by decide +kernel) n214

theorem n216 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b19 = true := join_dead n215 (by decide +kernel)

theorem n217 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b18 = true := join_dead n216 (by decide +kernel)

theorem n218 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b17 = true := join_dead n217 (by decide +kernel)

theorem n219 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b16 = true := join_dead n218 (by decide +kernel)

theorem n220 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b15 = true := join_dead n219 (by decide +kernel)

theorem n221 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b14 = true := join_dead n220 (by decide +kernel)

theorem n222 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b13 = true := join_dead n221 (by decide +kernel)

theorem n223 : fastVisit (leafCols 8 bank) [12,6,3] ⟨2067968,[3584,229376,1835008]⟩ b12 = true := join_dead n222 (by decide +kernel)

theorem n224 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b11 = true := join_live n209 n223

theorem n225 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b10 = true := join_dead n224 (by decide +kernel)

theorem n226 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b9 = true := join_dead n225 (by decide +kernel)

theorem n227 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b8 = true := join_dead n226 (by decide +kernel)

theorem n228 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b7 = true := join_dead n227 (by decide +kernel)

theorem n229 : fastVisit (leafCols 8 bank) [6,3] ⟨2064384,[229376,1835008]⟩ b6 = true := join_dead n228 (by decide +kernel)

theorem n230 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b5 = true := join_live n195 n229

theorem n231 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b4 = true := join_dead n230 (by decide +kernel)

theorem n232 : fastVisit (leafCols 8 bank) [3] ⟨1835008,[1835008]⟩ b3 = true := join_dead n231 (by decide +kernel)

theorem n233 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b2 = true := join_live n152 n232

theorem n234 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b12 = true := by decide +kernel

theorem n235 : fastVisit (leafCols 8 bank) [12,2] ⟨601746,[2560,598162]⟩ b12 = true := by decide +kernel

theorem n236 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b11 = true := join_live n234 n235

theorem n237 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b10 = true := join_dead n236 (by decide +kernel)

theorem n238 : fastVisit (leafCols 8 bank) [10,2] ⟨2096566,[1497380,1170]⟩ b10 = true := by decide +kernel

theorem n239 : fastVisit (leafCols 8 bank) [2] ⟨599186,[599186]⟩ b9 = true := join_live n237 n238

end GainFinite.F8
