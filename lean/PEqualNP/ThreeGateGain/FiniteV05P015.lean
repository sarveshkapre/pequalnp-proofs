import PEqualNP.ThreeGateGain.FiniteV05P014

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n1200 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n1201 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n1199 n1200

theorem n1202 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [] ⟨0,[]⟩ b43 = true := join_live n1198 n1201

theorem n1203 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b18 = true := enterColumns 5 bank [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n1202

theorem n1204 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b17 = true := join_dead n1203 (by decide +kernel)

theorem n1205 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b16 = true := join_dead n1204 (by decide +kernel)

theorem n1206 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b15 = true := join_dead n1205 (by decide +kernel)

theorem n1207 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b14 = true := join_dead n1206 (by decide +kernel)

theorem n1208 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b13 = true := join_dead n1207 (by decide +kernel)

theorem n1209 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b12 = true := join_dead n1208 (by decide +kernel)

theorem n1210 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b11 = true := join_dead n1209 (by decide +kernel)

theorem n1211 : fastVisit (leafCols 5 bank) [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩ b10 = true := join_dead n1210 (by decide +kernel)

theorem n1212 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b9 = true := join_live n1191 n1211

theorem n1213 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b8 = true := join_live n1176 n1212

theorem n1214 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b7 = true := join_dead n1213 (by decide +kernel)

theorem n1215 : fastVisit (leafFrame 5 [7,6,1] ⟨522240,[8192,198656,4096]⟩) [] ⟨0,[]⟩ b60 = true := by decide +kernel

theorem n1216 : fastVisit (leafFrame 5 [7,6,1] ⟨522240,[8192,198656,4096]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n1217 : fastVisit (leafFrame 5 [7,6,1] ⟨522240,[8192,198656,4096]⟩) [] ⟨0,[]⟩ b59 = true := join_live n1215 n1216

theorem n1218 : fastVisit (leafFrame 5 [7,6,1] ⟨522240,[8192,198656,4096]⟩) [1] ⟨299008,[299008]⟩ b59 = true := by decide +kernel

theorem n1219 : fastVisit (leafFrame 5 [7,6,1] ⟨522240,[8192,198656,4096]⟩) [] ⟨0,[]⟩ b58 = true := join_live n1217 n1218

theorem n1220 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b18 = true := enterColumns 5 bank [7,6,1] ⟨522240,[8192,198656,4096]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n1219

theorem n1221 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b17 = true := join_dead n1220 (by decide +kernel)

theorem n1222 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b16 = true := join_dead n1221 (by decide +kernel)

theorem n1223 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b15 = true := join_dead n1222 (by decide +kernel)

theorem n1224 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b14 = true := join_dead n1223 (by decide +kernel)

theorem n1225 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b13 = true := join_dead n1224 (by decide +kernel)

theorem n1226 : fastVisit (leafCols 5 bank) [13,7,6,1] ⟨523144,[904,8192,2048,4096]⟩ b13 = true := by decide +kernel

theorem n1227 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b12 = true := join_live n1225 n1226

theorem n1228 : fastVisit (leafCols 5 bank) [12,7,6,1] ⟨522538,[298,8192,65536,4096]⟩ b12 = true := by decide +kernel

theorem n1229 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b11 = true := join_live n1227 n1228

theorem n1230 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b10 = true := join_dead n1229 (by decide +kernel)

theorem n1231 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n1232 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n1233 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [] ⟨0,[]⟩ b61 = true := join_live n1231 n1232

theorem n1234 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n1235 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [] ⟨0,[]⟩ b45 = true := join_live n1233 n1234

theorem n1236 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n1237 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [] ⟨0,[]⟩ b44 = true := join_live n1235 n1236

theorem n1238 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

theorem n1239 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n1240 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n1238 n1239

theorem n1241 : fastVisit (leafFrame 5 [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩) [] ⟨0,[]⟩ b43 = true := join_live n1237 n1240

theorem n1242 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b18 = true := enterColumns 5 bank [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n1241

theorem n1243 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b17 = true := join_dead n1242 (by decide +kernel)

theorem n1244 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b16 = true := join_dead n1243 (by decide +kernel)

theorem n1245 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b15 = true := join_dead n1244 (by decide +kernel)

theorem n1246 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b14 = true := join_dead n1245 (by decide +kernel)

theorem n1247 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b13 = true := join_dead n1246 (by decide +kernel)

theorem n1248 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b12 = true := join_dead n1247 (by decide +kernel)

theorem n1249 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b11 = true := join_dead n1248 (by decide +kernel)

theorem n1250 : fastVisit (leafCols 5 bank) [10,7,6,1] ⟨522248,[8,8192,198656,4096]⟩ b10 = true := join_dead n1249 (by decide +kernel)

theorem n1251 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b9 = true := join_live n1230 n1250

theorem n1252 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b8 = true := join_dead n1251 (by decide +kernel)

theorem n1253 : fastVisit (leafCols 5 bank) [7,6,1] ⟨522240,[8192,198656,4096]⟩ b7 = true := join_dead n1252 (by decide +kernel)

theorem n1254 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b6 = true := join_live n1214 n1253

theorem n1255 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b5 = true := join_live n1143 n1254

theorem n1256 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b4 = true := join_dead n1255 (by decide +kernel)

theorem n1257 : fastVisit (leafFrame 5 [4,1] ⟨495616,[196608,36864]⟩) [] ⟨0,[]⟩ b106 = true := by decide +kernel

theorem n1258 : fastVisit (leafFrame 5 [4,1] ⟨495616,[196608,36864]⟩) [2] ⟨149504,[149504]⟩ b106 = true := by decide +kernel

theorem n1259 : fastVisit (leafFrame 5 [4,1] ⟨495616,[196608,36864]⟩) [] ⟨0,[]⟩ b105 = true := join_live n1257 n1258

theorem n1260 : fastVisit (leafFrame 5 [4,1] ⟨495616,[196608,36864]⟩) [1] ⟨299008,[299008]⟩ b105 = true := by decide +kernel

theorem n1261 : fastVisit (leafFrame 5 [4,1] ⟨495616,[196608,36864]⟩) [] ⟨0,[]⟩ b104 = true := join_live n1259 n1260

theorem n1262 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b18 = true := enterColumns 5 bank [4,1] ⟨495616,[196608,36864]⟩ b18 b104 (by decide +kernel) (by decide +kernel) n1261

theorem n1263 : fastVisit (leafCols 5 bank) [18,4,1] ⟨522618,[27002,65536,4096]⟩ b18 = true := by decide +kernel

theorem n1264 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b17 = true := join_live n1262 n1263

theorem n1265 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b16 = true := join_dead n1264 (by decide +kernel)

theorem n1266 : fastVisit (leafCols 5 bank) [16,4,1] ⟨520312,[24696,196608,4096]⟩ b16 = true := by decide +kernel

theorem n1267 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b15 = true := join_live n1265 n1266

theorem n1268 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b14 = true := join_dead n1267 (by decide +kernel)

theorem n1269 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b13 = true := join_dead n1268 (by decide +kernel)

theorem n1270 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b12 = true := join_dead n1269 (by decide +kernel)

theorem n1271 : fastVisit (leafCols 5 bank) [12,4,1] ⟨514346,[18730,65536,36864]⟩ b12 = true := by decide +kernel

theorem n1272 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b11 = true := join_live n1270 n1271

theorem n1273 : fastVisit (leafCols 5 bank) [4,1] ⟨495616,[196608,36864]⟩ b10 = true := join_dead n1272 (by decide +kernel)

theorem n1274 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [] ⟨0,[]⟩ b109 = true := by decide +kernel

theorem n1275 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [5] ⟨495616,[495616]⟩ b109 = true := by decide +kernel

theorem n1276 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [] ⟨0,[]⟩ b108 = true := join_live n1274 n1275

theorem n1277 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [4] ⟨458752,[458752]⟩ b108 = true := by decide +kernel

theorem n1278 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [] ⟨0,[]⟩ b107 = true := join_live n1276 n1277

theorem n1279 : fastVisit (leafFrame 5 [10,4,1] ⟨495624,[8,196608,36864]⟩) [2] ⟨149504,[149504]⟩ b108 = true := by decide +kernel

end GainFinite.F5
