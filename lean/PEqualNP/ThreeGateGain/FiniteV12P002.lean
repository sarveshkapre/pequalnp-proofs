import PEqualNP.ThreeGateGain.FiniteV12P001

namespace GainFinite.F12
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n160 : fastVisit (leafFrame 12 [7] ⟨3670136,[3670136]⟩) [1] ⟨19169792,[19169792]⟩ b32 = true := by decide +kernel

theorem n161 : fastVisit (leafFrame 12 [7] ⟨3670136,[3670136]⟩) [] ⟨0,[]⟩ b31 = true := join_live n159 n160

theorem n162 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b24 = true := enterColumns 12 bank [7] ⟨3670136,[3670136]⟩ b24 b31 (by decide +kernel) (by decide +kernel) n161

theorem n163 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b23 = true := join_dead n162 (by decide +kernel)

theorem n164 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b22 = true := join_dead n163 (by decide +kernel)

theorem n165 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b21 = true := join_dead n164 (by decide +kernel)

theorem n166 : fastVisit (leafCols 12 bank) [21,7] ⟨33226746,[29556610,2621520]⟩ b21 = true := by decide +kernel

theorem n167 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b20 = true := join_live n165 n166

theorem n168 : fastVisit (leafCols 12 bank) [20,7] ⟨33357820,[29687684,1572912]⟩ b20 = true := by decide +kernel

theorem n169 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b19 = true := join_live n167 n168

theorem n170 : fastVisit (leafCols 12 bank) [19,7] ⟨33095672,[29425536,3670128]⟩ b19 = true := by decide +kernel

theorem n171 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b18 = true := join_live n169 n170

theorem n172 : fastVisit (leafCols 12 bank) [18,7] ⟨12254586,[8584450,2621520]⟩ b18 = true := by decide +kernel

theorem n173 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b17 = true := join_live n171 n172

theorem n174 : fastVisit (leafCols 12 bank) [17,7] ⟨20774524,[17104388,1572912]⟩ b17 = true := by decide +kernel

theorem n175 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b16 = true := join_live n173 n174

theorem n176 : fastVisit (leafCols 12 bank) [16,7] ⟨3734648,[64512,3670128]⟩ b16 = true := by decide +kernel

theorem n177 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b15 = true := join_live n175 n176

theorem n178 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b14 = true := join_dead n177 (by decide +kernel)

theorem n179 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b13 = true := join_dead n178 (by decide +kernel)

theorem n180 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b12 = true := join_dead n179 (by decide +kernel)

theorem n181 : fastVisit (leafCols 12 bank) [12,7] ⟨33505656,[29835520,120]⟩ b12 = true := by decide +kernel

theorem n182 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b11 = true := join_live n180 n181

theorem n183 : fastVisit (leafCols 12 bank) [11,7] ⟨33522296,[29852160,120]⟩ b11 = true := by decide +kernel

theorem n184 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b10 = true := join_live n182 n183

theorem n185 : fastVisit (leafCols 12 bank) [10,7] ⟨33489016,[29818880,120]⟩ b10 = true := by decide +kernel

theorem n186 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b9 = true := join_live n184 n185

theorem n187 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b8 = true := join_dead n186 (by decide +kernel)

theorem n188 : fastVisit (leafCols 12 bank) [7] ⟨3670136,[3670136]⟩ b7 = true := join_dead n187 (by decide +kernel)

theorem n189 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b6 = true := join_live n154 n188

theorem n190 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b18 = true := by decide +kernel

theorem n191 : fastVisit (leafCols 12 bank) [18,6] ⟨30605226,[7210,20972160]⟩ b18 = true := by decide +kernel

theorem n192 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b17 = true := join_live n190 n191

theorem n193 : fastVisit (leafCols 12 bank) [17,6] ⟨32964556,[2366540,13762944]⟩ b17 = true := by decide +kernel

theorem n194 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b16 = true := join_live n192 n193

theorem n195 : fastVisit (leafCols 12 bank) [16,6] ⟨30605192,[7176,30540672]⟩ b16 = true := by decide +kernel

theorem n196 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b15 = true := join_live n194 n195

theorem n197 : fastVisit (leafCols 12 bank) [15,6] ⟨33549306,[2951290,41600]⟩ b15 = true := by decide +kernel

theorem n198 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b14 = true := join_live n196 n197

theorem n199 : fastVisit (leafCols 12 bank) [14,6] ⟨33551356,[2953340,24960]⟩ b14 = true := by decide +kernel

theorem n200 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b13 = true := join_live n198 n199

theorem n201 : fastVisit (leafCols 12 bank) [13,6] ⟨33547256,[2949240,58240]⟩ b13 = true := by decide +kernel

theorem n202 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b12 = true := join_live n200 n201

theorem n203 : fastVisit (leafCols 12 bank) [12,6] ⟨33547136,[2949120,41600]⟩ b12 = true := by decide +kernel

theorem n204 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b11 = true := join_live n202 n203

theorem n205 : fastVisit (leafCols 12 bank) [11,6] ⟨33547136,[2949120,24960]⟩ b11 = true := by decide +kernel

theorem n206 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b10 = true := join_live n204 n205

theorem n207 : fastVisit (leafCols 12 bank) [10,6] ⟨33547136,[2949120,58240]⟩ b10 = true := by decide +kernel

theorem n208 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b9 = true := join_live n206 n207

theorem n209 : fastVisit (leafCols 12 bank) [9,6] ⟨33221626,[2623610,21013120]⟩ b9 = true := by decide +kernel

theorem n210 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b8 = true := join_live n208 n209

theorem n211 : fastVisit (leafCols 12 bank) [8,6] ⟨33485820,[2887804,12738944]⟩ b8 = true := by decide +kernel

theorem n212 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b7 = true := join_live n210 n211

theorem n213 : fastVisit (leafCols 12 bank) [7,6] ⟨33219576,[2621560,29549440]⟩ b7 = true := by decide +kernel

theorem n214 : fastVisit (leafCols 12 bank) [6] ⟨30598016,[30598016]⟩ b6 = true := join_live n212 n213

theorem n215 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b5 = true := join_live n189 n214

theorem n216 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b18 = true := by decide +kernel

theorem n217 : fastVisit (leafCols 12 bank) [18,5] ⟨32964522,[1186858,23331456]⟩ b18 = true := by decide +kernel

theorem n218 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b17 = true := join_live n216 n217

theorem n219 : fastVisit (leafCols 12 bank) [17,5] ⟨31784908,[7244,12583296]⟩ b17 = true := by decide +kernel

theorem n220 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b16 = true := join_live n218 n219

theorem n221 : fastVisit (leafCols 12 bank) [16,5] ⟨31784840,[7176,31720320]⟩ b16 = true := by decide +kernel

theorem n222 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b15 = true := join_live n220 n221

theorem n223 : fastVisit (leafCols 12 bank) [15,5] ⟨33549306,[1771642,41600]⟩ b15 = true := by decide +kernel

theorem n224 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b14 = true := join_live n222 n223

theorem n225 : fastVisit (leafCols 12 bank) [14,5] ⟨33551356,[1773692,24960]⟩ b14 = true := by decide +kernel

theorem n226 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b13 = true := join_live n224 n225

theorem n227 : fastVisit (leafCols 12 bank) [13,5] ⟨33547256,[1769592,58240]⟩ b13 = true := by decide +kernel

theorem n228 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b12 = true := join_live n226 n227

theorem n229 : fastVisit (leafCols 12 bank) [12,5] ⟨33547136,[1769472,41600]⟩ b12 = true := by decide +kernel

theorem n230 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b11 = true := join_live n228 n229

theorem n231 : fastVisit (leafCols 12 bank) [11,5] ⟨33547136,[1769472,24960]⟩ b11 = true := by decide +kernel

theorem n232 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b10 = true := join_live n230 n231

theorem n233 : fastVisit (leafCols 12 bank) [10,5] ⟨33547136,[1769472,58240]⟩ b10 = true := by decide +kernel

theorem n234 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b9 = true := join_live n232 n233

theorem n235 : fastVisit (leafCols 12 bank) [9,5] ⟨33483770,[1706106,21275264]⟩ b9 = true := by decide +kernel

theorem n236 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b8 = true := join_live n234 n235

theorem n237 : fastVisit (leafCols 12 bank) [8,5] ⟨33354748,[1577084,12607872]⟩ b8 = true := by decide +kernel

theorem n238 : fastVisit (leafCols 12 bank) [5] ⟨31777664,[31777664]⟩ b7 = true := join_live n236 n237

theorem n239 : fastVisit (leafCols 12 bank) [7,5] ⟨33350648,[1572984,29680512]⟩ b7 = true := by decide +kernel

end GainFinite.F12
