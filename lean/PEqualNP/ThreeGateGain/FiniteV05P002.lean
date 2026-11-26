import PEqualNP.ThreeGateGain.FiniteV05P001

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n160 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b17 = true := join_dead n159 (by decide +kernel)

theorem n161 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b16 = true := join_dead n160 (by decide +kernel)

theorem n162 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b15 = true := join_dead n161 (by decide +kernel)

theorem n163 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b14 = true := join_dead n162 (by decide +kernel)

theorem n164 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b13 = true := join_dead n163 (by decide +kernel)

theorem n165 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b12 = true := join_dead n164 (by decide +kernel)

theorem n166 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b11 = true := join_dead n165 (by decide +kernel)

theorem n167 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b10 = true := join_dead n166 (by decide +kernel)

theorem n168 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b9 = true := join_live n151 n167

theorem n169 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b8 = true := join_dead n168 (by decide +kernel)

theorem n170 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b7 = true := join_dead n169 (by decide +kernel)

theorem n171 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b6 = true := join_live n132 n170

theorem n172 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b16 = true := by decide +kernel

theorem n173 : fastVisit (leafCols 5 bank) [16,6] ⟨518264,[41080,460800]⟩ b16 = true := by decide +kernel

theorem n174 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b15 = true := join_live n172 n173

theorem n175 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b14 = true := join_dead n174 (by decide +kernel)

theorem n176 : fastVisit (leafCols 5 bank) [14,6] ⟨515020,[37836,18432]⟩ b14 = true := by decide +kernel

theorem n177 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b13 = true := join_live n175 n176

theorem n178 : fastVisit (leafCols 5 bank) [13,6] ⟨478088,[904,18432]⟩ b13 = true := by decide +kernel

theorem n179 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b12 = true := join_live n177 n178

theorem n180 : fastVisit (leafCols 5 bank) [12,6] ⟨477482,[298,327680]⟩ b12 = true := by decide +kernel

theorem n181 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b11 = true := join_live n179 n180

theorem n182 : fastVisit (leafCols 5 bank) [11,6] ⟨514636,[37452,215040]⟩ b11 = true := by decide +kernel

theorem n183 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b10 = true := join_live n181 n182

theorem n184 : fastVisit (leafFrame 5 [10,6] ⟨477192,[8,477184]⟩) [] ⟨0,[]⟩ b37 = true := by decide +kernel

theorem n185 : fastVisit (leafFrame 5 [10,6] ⟨477192,[8,477184]⟩) [1] ⟨299008,[299008]⟩ b37 = true := by decide +kernel

theorem n186 : fastVisit (leafFrame 5 [10,6] ⟨477192,[8,477184]⟩) [] ⟨0,[]⟩ b36 = true := join_live n184 n185

theorem n187 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b18 = true := enterColumns 5 bank [10,6] ⟨477192,[8,477184]⟩ b18 b36 (by decide +kernel) (by decide +kernel) n186

theorem n188 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b17 = true := join_dead n187 (by decide +kernel)

theorem n189 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b16 = true := join_dead n188 (by decide +kernel)

theorem n190 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b15 = true := join_dead n189 (by decide +kernel)

theorem n191 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b14 = true := join_dead n190 (by decide +kernel)

theorem n192 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b13 = true := join_dead n191 (by decide +kernel)

theorem n193 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b12 = true := join_dead n192 (by decide +kernel)

theorem n194 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b11 = true := join_dead n193 (by decide +kernel)

theorem n195 : fastVisit (leafCols 5 bank) [10,6] ⟨477192,[8,477184]⟩ b10 = true := join_dead n194 (by decide +kernel)

theorem n196 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b9 = true := join_live n183 n195

theorem n197 : fastVisit (leafFrame 5 [9,6] ⟨518144,[40960,327680]⟩) [] ⟨0,[]⟩ b39 = true := by decide +kernel

theorem n198 : fastVisit (leafFrame 5 [9,6] ⟨518144,[40960,327680]⟩) [1] ⟨299008,[299008]⟩ b39 = true := by decide +kernel

theorem n199 : fastVisit (leafFrame 5 [9,6] ⟨518144,[40960,327680]⟩) [] ⟨0,[]⟩ b38 = true := join_live n197 n198

theorem n200 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b18 = true := enterColumns 5 bank [9,6] ⟨518144,[40960,327680]⟩ b18 b38 (by decide +kernel) (by decide +kernel) n199

theorem n201 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b17 = true := join_dead n200 (by decide +kernel)

theorem n202 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b16 = true := join_dead n201 (by decide +kernel)

theorem n203 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b15 = true := join_dead n202 (by decide +kernel)

theorem n204 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b14 = true := join_dead n203 (by decide +kernel)

theorem n205 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b13 = true := join_dead n204 (by decide +kernel)

theorem n206 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b12 = true := join_dead n205 (by decide +kernel)

theorem n207 : fastVisit (leafCols 5 bank) [12,9,6] ⟨518442,[298,40960,327680]⟩ b12 = true := by decide +kernel

theorem n208 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b11 = true := join_live n206 n207

theorem n209 : fastVisit (leafCols 5 bank) [11,9,6] ⟨522828,[4684,8192,65536]⟩ b11 = true := by decide +kernel

theorem n210 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b10 = true := join_live n208 n209

theorem n211 : fastVisit (leafFrame 5 [10,9,6] ⟨518152,[8,40960,327680]⟩) [] ⟨0,[]⟩ b42 = true := by decide +kernel

theorem n212 : fastVisit (leafFrame 5 [10,9,6] ⟨518152,[8,40960,327680]⟩) [2] ⟨149504,[149504]⟩ b42 = true := by decide +kernel

theorem n213 : fastVisit (leafFrame 5 [10,9,6] ⟨518152,[8,40960,327680]⟩) [] ⟨0,[]⟩ b41 = true := join_live n211 n212

theorem n214 : fastVisit (leafFrame 5 [10,9,6] ⟨518152,[8,40960,327680]⟩) [1] ⟨299008,[299008]⟩ b42 = true := by decide +kernel

theorem n215 : fastVisit (leafFrame 5 [10,9,6] ⟨518152,[8,40960,327680]⟩) [2,1] ⟨448512,[149504,299008]⟩ b42 = true := by decide +kernel

theorem n216 : fastVisit (leafFrame 5 [10,9,6] ⟨518152,[8,40960,327680]⟩) [1] ⟨299008,[299008]⟩ b41 = true := join_live n214 n215

theorem n217 : fastVisit (leafFrame 5 [10,9,6] ⟨518152,[8,40960,327680]⟩) [] ⟨0,[]⟩ b40 = true := join_live n213 n216

theorem n218 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b18 = true := enterColumns 5 bank [10,9,6] ⟨518152,[8,40960,327680]⟩ b18 b40 (by decide +kernel) (by decide +kernel) n217

theorem n219 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b17 = true := join_dead n218 (by decide +kernel)

theorem n220 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b16 = true := join_dead n219 (by decide +kernel)

theorem n221 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b15 = true := join_dead n220 (by decide +kernel)

theorem n222 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b14 = true := join_dead n221 (by decide +kernel)

theorem n223 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b13 = true := join_dead n222 (by decide +kernel)

theorem n224 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b12 = true := join_dead n223 (by decide +kernel)

theorem n225 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b11 = true := join_dead n224 (by decide +kernel)

theorem n226 : fastVisit (leafCols 5 bank) [10,9,6] ⟨518152,[8,40960,327680]⟩ b10 = true := join_dead n225 (by decide +kernel)

theorem n227 : fastVisit (leafCols 5 bank) [9,6] ⟨518144,[40960,327680]⟩ b9 = true := join_live n210 n226

theorem n228 : fastVisit (leafCols 5 bank) [6] ⟨477184,[477184]⟩ b8 = true := join_live n196 n227

theorem n229 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b18 = true := by decide +kernel

theorem n230 : fastVisit (leafCols 5 bank) [18,8,6] ⟨522618,[378,4096,65536]⟩ b18 = true := by decide +kernel

theorem n231 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b17 = true := join_live n229 n230

theorem n232 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b16 = true := join_dead n231 (by decide +kernel)

theorem n233 : fastVisit (leafCols 5 bank) [16,8,6] ⟨522360,[120,4096,198656]⟩ b16 = true := by decide +kernel

theorem n234 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b15 = true := join_live n232 n233

theorem n235 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b14 = true := join_dead n234 (by decide +kernel)

theorem n236 : fastVisit (leafCols 5 bank) [14,8,6] ⟨523212,[972,8192,2048]⟩ b14 = true := by decide +kernel

theorem n237 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b13 = true := join_live n235 n236

theorem n238 : fastVisit (leafCols 5 bank) [13,8,6] ⟨523144,[904,45056,2048]⟩ b13 = true := by decide +kernel

theorem n239 : fastVisit (leafCols 5 bank) [8,6] ⟨522240,[45056,198656]⟩ b12 = true := join_live n237 n238

end GainFinite.F5
