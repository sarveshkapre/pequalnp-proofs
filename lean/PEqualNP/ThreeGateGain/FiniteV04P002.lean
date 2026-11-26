import PEqualNP.ThreeGateGain.FiniteV04P001

namespace GainFinite.F4
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n160 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b7 = true := join_live n149 n159

theorem n161 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b6 = true := join_dead n160 (by decide +kernel)

theorem n162 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b5 = true := join_dead n161 (by decide +kernel)

theorem n163 : fastVisit (leafCols 4 bank) [5,2] ⟨27648,[19456,8192]⟩ b9 = true := by decide +kernel

theorem n164 : fastVisit (leafCols 4 bank) [9,5,2] ⟨27840,[192,3072,8192]⟩ b12 = true := by decide +kernel

theorem n165 : fastVisit (leafCols 4 bank) [12,9,5,2] ⟨27848,[8,64,1024,8192]⟩ b12 = true := by decide +kernel

theorem n166 : fastVisit (leafCols 4 bank) [9,5,2] ⟨27840,[192,3072,8192]⟩ b11 = true := join_live n164 n165

theorem n167 : fastVisit (leafCols 4 bank) [9,5,2] ⟨27840,[192,3072,8192]⟩ b10 = true := join_dead n166 (by decide +kernel)

theorem n168 : fastVisit (leafCols 4 bank) [9,5,2] ⟨27840,[192,3072,8192]⟩ b9 = true := join_dead n167 (by decide +kernel)

theorem n169 : fastVisit (leafCols 4 bank) [5,2] ⟨27648,[19456,8192]⟩ b8 = true := join_live n163 n168

theorem n170 : fastVisit (leafCols 4 bank) [8,5,2] ⟨27776,[128,19456,8192]⟩ b8 = true := by decide +kernel

theorem n171 : fastVisit (leafCols 4 bank) [5,2] ⟨27648,[19456,8192]⟩ b7 = true := join_live n169 n170

theorem n172 : fastVisit (leafCols 4 bank) [5,2] ⟨27648,[19456,8192]⟩ b6 = true := join_dead n171 (by decide +kernel)

theorem n173 : fastVisit (leafCols 4 bank) [5,2] ⟨27648,[19456,8192]⟩ b5 = true := join_dead n172 (by decide +kernel)

theorem n174 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b4 = true := join_live n162 n173

theorem n175 : fastVisit (leafFrame 4 [4,2] ⟨10240,[2048,8192]⟩) [] ⟨0,[]⟩ b20 = true := by decide +kernel

theorem n176 : fastVisit (leafFrame 4 [4,2] ⟨10240,[2048,8192]⟩) [1] ⟨16384,[16384]⟩ b20 = true := by decide +kernel

theorem n177 : fastVisit (leafFrame 4 [4,2] ⟨10240,[2048,8192]⟩) [] ⟨0,[]⟩ b19 = true := join_live n175 n176

theorem n178 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b14 = true := enterColumns 4 bank [4,2] ⟨10240,[2048,8192]⟩ b14 b19 (by decide +kernel) (by decide +kernel) n177

theorem n179 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b13 = true := join_dead n178 (by decide +kernel)

theorem n180 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b12 = true := join_dead n179 (by decide +kernel)

theorem n181 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b11 = true := join_dead n180 (by decide +kernel)

theorem n182 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b10 = true := join_dead n181 (by decide +kernel)

theorem n183 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b9 = true := join_dead n182 (by decide +kernel)

theorem n184 : fastVisit (leafCols 4 bank) [9,4,2] ⟨26816,[16576,2048,8192]⟩ b9 = true := by decide +kernel

theorem n185 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b8 = true := join_live n183 n184

theorem n186 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [] ⟨0,[]⟩ b24 = true := by decide +kernel

theorem n187 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [3] ⟨28672,[28672]⟩ b26 = true := by decide +kernel

theorem n188 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [5,3] ⟨31744,[3072,12288]⟩ b26 = true := by decide +kernel

theorem n189 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [3] ⟨28672,[28672]⟩ b25 = true := join_live n187 n188

theorem n190 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [4,3] ⟨30720,[2048,28672]⟩ b25 = true := by decide +kernel

theorem n191 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [3] ⟨28672,[28672]⟩ b24 = true := join_live n189 n190

theorem n192 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [] ⟨0,[]⟩ b23 = true := join_live n186 n191

theorem n193 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [2] ⟨8192,[8192]⟩ b23 = true := by decide +kernel

theorem n194 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [] ⟨0,[]⟩ b22 = true := join_live n192 n193

theorem n195 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [1] ⟨16384,[16384]⟩ b22 = true := by decide +kernel

theorem n196 : fastVisit (leafFrame 4 [8,4,2] ⟨10368,[128,2048,8192]⟩) [] ⟨0,[]⟩ b21 = true := join_live n194 n195

theorem n197 : fastVisit (leafCols 4 bank) [8,4,2] ⟨10368,[128,2048,8192]⟩ b14 = true := enterColumns 4 bank [8,4,2] ⟨10368,[128,2048,8192]⟩ b14 b21 (by decide +kernel) (by decide +kernel) n196

theorem n198 : fastVisit (leafCols 4 bank) [8,4,2] ⟨10368,[128,2048,8192]⟩ b13 = true := join_dead n197 (by decide +kernel)

theorem n199 : fastVisit (leafCols 4 bank) [8,4,2] ⟨10368,[128,2048,8192]⟩ b12 = true := join_dead n198 (by decide +kernel)

theorem n200 : fastVisit (leafCols 4 bank) [8,4,2] ⟨10368,[128,2048,8192]⟩ b11 = true := join_dead n199 (by decide +kernel)

theorem n201 : fastVisit (leafCols 4 bank) [8,4,2] ⟨10368,[128,2048,8192]⟩ b10 = true := join_dead n200 (by decide +kernel)

theorem n202 : fastVisit (leafCols 4 bank) [8,4,2] ⟨10368,[128,2048,8192]⟩ b9 = true := join_dead n201 (by decide +kernel)

theorem n203 : fastVisit (leafCols 4 bank) [8,4,2] ⟨10368,[128,2048,8192]⟩ b8 = true := join_dead n202 (by decide +kernel)

theorem n204 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b7 = true := join_live n185 n203

theorem n205 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b6 = true := join_dead n204 (by decide +kernel)

theorem n206 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b5 = true := join_dead n205 (by decide +kernel)

theorem n207 : fastVisit (leafCols 4 bank) [4,2] ⟨10240,[2048,8192]⟩ b4 = true := join_dead n206 (by decide +kernel)

theorem n208 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b3 = true := join_live n174 n207

theorem n209 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b2 = true := join_dead n208 (by decide +kernel)

theorem n210 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b1 = true := join_live n142 n209

theorem n211 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b12 = true := by decide +kernel

theorem n212 : fastVisit (leafCols 4 bank) [12,1] ⟨18568,[2184,16384]⟩ b12 = true := by decide +kernel

theorem n213 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b11 = true := join_live n211 n212

theorem n214 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b10 = true := join_dead n213 (by decide +kernel)

theorem n215 : fastVisit (leafCols 4 bank) [10,1] ⟨24736,[8352,16384]⟩ b10 = true := by decide +kernel

theorem n216 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b9 = true := join_live n214 n215

theorem n217 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b8 = true := join_dead n216 (by decide +kernel)

theorem n218 : fastVisit (leafFrame 4 [8,1] ⟨16512,[128,16384]⟩) [] ⟨0,[]⟩ b28 = true := by decide +kernel

theorem n219 : fastVisit (leafFrame 4 [8,1] ⟨16512,[128,16384]⟩) [1] ⟨16384,[16384]⟩ b28 = true := by decide +kernel

theorem n220 : fastVisit (leafFrame 4 [8,1] ⟨16512,[128,16384]⟩) [] ⟨0,[]⟩ b27 = true := join_live n218 n219

theorem n221 : fastVisit (leafCols 4 bank) [8,1] ⟨16512,[128,16384]⟩ b14 = true := enterColumns 4 bank [8,1] ⟨16512,[128,16384]⟩ b14 b27 (by decide +kernel) (by decide +kernel) n220

theorem n222 : fastVisit (leafCols 4 bank) [8,1] ⟨16512,[128,16384]⟩ b13 = true := join_dead n221 (by decide +kernel)

theorem n223 : fastVisit (leafCols 4 bank) [8,1] ⟨16512,[128,16384]⟩ b12 = true := join_dead n222 (by decide +kernel)

theorem n224 : fastVisit (leafCols 4 bank) [8,1] ⟨16512,[128,16384]⟩ b11 = true := join_dead n223 (by decide +kernel)

theorem n225 : fastVisit (leafCols 4 bank) [8,1] ⟨16512,[128,16384]⟩ b10 = true := join_dead n224 (by decide +kernel)

theorem n226 : fastVisit (leafCols 4 bank) [8,1] ⟨16512,[128,16384]⟩ b9 = true := join_dead n225 (by decide +kernel)

theorem n227 : fastVisit (leafCols 4 bank) [8,1] ⟨16512,[128,16384]⟩ b8 = true := join_dead n226 (by decide +kernel)

theorem n228 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b7 = true := join_live n217 n227

theorem n229 : fastVisit (leafCols 4 bank) [1] ⟨16384,[16384]⟩ b6 = true := join_dead n228 (by decide +kernel)

theorem n230 : fastVisit (leafCols 4 bank) [6,1] ⟨27136,[10752,16384]⟩ b10 = true := by decide +kernel

theorem n231 : fastVisit (leafCols 4 bank) [10,6,1] ⟨27296,[160,2560,16384]⟩ b12 = true := by decide +kernel

theorem n232 : fastVisit (leafCols 4 bank) [12,10,6,1] ⟨27304,[8,32,512,16384]⟩ b12 = true := by decide +kernel

theorem n233 : fastVisit (leafCols 4 bank) [10,6,1] ⟨27296,[160,2560,16384]⟩ b11 = true := join_live n231 n232

theorem n234 : fastVisit (leafCols 4 bank) [10,6,1] ⟨27296,[160,2560,16384]⟩ b10 = true := join_dead n233 (by decide +kernel)

theorem n235 : fastVisit (leafCols 4 bank) [6,1] ⟨27136,[10752,16384]⟩ b9 = true := join_live n230 n234

theorem n236 : fastVisit (leafCols 4 bank) [6,1] ⟨27136,[10752,16384]⟩ b8 = true := join_dead n235 (by decide +kernel)

theorem n237 : fastVisit (leafCols 4 bank) [8,6,1] ⟨27264,[128,10752,16384]⟩ b8 = true := by decide +kernel

theorem n238 : fastVisit (leafCols 4 bank) [6,1] ⟨27136,[10752,16384]⟩ b7 = true := join_live n236 n237

theorem n239 : fastVisit (leafCols 4 bank) [6,1] ⟨27136,[10752,16384]⟩ b6 = true := join_dead n238 (by decide +kernel)

end GainFinite.F4
