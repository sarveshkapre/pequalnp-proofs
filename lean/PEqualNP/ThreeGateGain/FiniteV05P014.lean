import PEqualNP.ThreeGateGain.FiniteV05P013

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n1120 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [] ⟨0,[]⟩ b103 = true := by decide +kernel

theorem n1121 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [4] ⟨458752,[458752]⟩ b103 = true := by decide +kernel

theorem n1122 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [] ⟨0,[]⟩ b102 = true := join_live n1120 n1121

theorem n1123 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [2] ⟨149504,[149504]⟩ b103 = true := by decide +kernel

theorem n1124 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [4,2] ⟨477184,[327680,18432]⟩ b103 = true := by decide +kernel

theorem n1125 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [2] ⟨149504,[149504]⟩ b102 = true := join_live n1123 n1124

theorem n1126 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [] ⟨0,[]⟩ b24 = true := join_live n1122 n1125

theorem n1127 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [1] ⟨299008,[299008]⟩ b102 = true := by decide +kernel

theorem n1128 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [2,1] ⟨448512,[149504,299008]⟩ b102 = true := by decide +kernel

theorem n1129 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [1] ⟨299008,[299008]⟩ b24 = true := join_live n1127 n1128

theorem n1130 : fastVisit (leafFrame 5 [10,7,1] ⟨323592,[8,24576,266240]⟩) [] ⟨0,[]⟩ b23 = true := join_live n1126 n1129

theorem n1131 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b18 = true := enterColumns 5 bank [10,7,1] ⟨323592,[8,24576,266240]⟩ b18 b23 (by decide +kernel) (by decide +kernel) n1130

theorem n1132 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b17 = true := join_dead n1131 (by decide +kernel)

theorem n1133 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b16 = true := join_dead n1132 (by decide +kernel)

theorem n1134 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b15 = true := join_dead n1133 (by decide +kernel)

theorem n1135 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b14 = true := join_dead n1134 (by decide +kernel)

theorem n1136 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b13 = true := join_dead n1135 (by decide +kernel)

theorem n1137 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b12 = true := join_dead n1136 (by decide +kernel)

theorem n1138 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b11 = true := join_dead n1137 (by decide +kernel)

theorem n1139 : fastVisit (leafCols 5 bank) [10,7,1] ⟨323592,[8,24576,266240]⟩ b10 = true := join_dead n1138 (by decide +kernel)

theorem n1140 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b9 = true := join_live n1119 n1139

theorem n1141 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b8 = true := join_dead n1140 (by decide +kernel)

theorem n1142 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b7 = true := join_dead n1141 (by decide +kernel)

theorem n1143 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b6 = true := join_live n1102 n1142

theorem n1144 : fastVisit (leafFrame 5 [6,1] ⟨514048,[215040,36864]⟩) [] ⟨0,[]⟩ b54 = true := by decide +kernel

theorem n1145 : fastVisit (leafFrame 5 [6,1] ⟨514048,[215040,36864]⟩) [1] ⟨299008,[299008]⟩ b54 = true := by decide +kernel

theorem n1146 : fastVisit (leafFrame 5 [6,1] ⟨514048,[215040,36864]⟩) [] ⟨0,[]⟩ b53 = true := join_live n1144 n1145

theorem n1147 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b18 = true := enterColumns 5 bank [6,1] ⟨514048,[215040,36864]⟩ b18 b53 (by decide +kernel) (by decide +kernel) n1146

theorem n1148 : fastVisit (leafCols 5 bank) [18,6,1] ⟨522618,[8570,65536,4096]⟩ b18 = true := by decide +kernel

theorem n1149 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b17 = true := join_live n1147 n1148

theorem n1150 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b16 = true := join_dead n1149 (by decide +kernel)

theorem n1151 : fastVisit (leafCols 5 bank) [16,6,1] ⟨522360,[8312,198656,4096]⟩ b16 = true := by decide +kernel

theorem n1152 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b15 = true := join_live n1150 n1151

theorem n1153 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b14 = true := join_dead n1152 (by decide +kernel)

theorem n1154 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b13 = true := join_dead n1153 (by decide +kernel)

theorem n1155 : fastVisit (leafCols 5 bank) [13,6,1] ⟨514952,[904,18432,36864]⟩ b13 = true := by decide +kernel

theorem n1156 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b12 = true := join_live n1154 n1155

theorem n1157 : fastVisit (leafCols 5 bank) [12,6,1] ⟨514346,[298,65536,36864]⟩ b12 = true := by decide +kernel

theorem n1158 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b11 = true := join_live n1156 n1157

theorem n1159 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b10 = true := join_dead n1158 (by decide +kernel)

theorem n1160 : fastVisit (leafFrame 5 [10,6,1] ⟨514056,[8,215040,36864]⟩) [] ⟨0,[]⟩ b57 = true := by decide +kernel

theorem n1161 : fastVisit (leafFrame 5 [10,6,1] ⟨514056,[8,215040,36864]⟩) [2] ⟨149504,[149504]⟩ b57 = true := by decide +kernel

theorem n1162 : fastVisit (leafFrame 5 [10,6,1] ⟨514056,[8,215040,36864]⟩) [] ⟨0,[]⟩ b56 = true := join_live n1160 n1161

theorem n1163 : fastVisit (leafFrame 5 [10,6,1] ⟨514056,[8,215040,36864]⟩) [1] ⟨299008,[299008]⟩ b57 = true := by decide +kernel

theorem n1164 : fastVisit (leafFrame 5 [10,6,1] ⟨514056,[8,215040,36864]⟩) [2,1] ⟨448512,[149504,299008]⟩ b57 = true := by decide +kernel

theorem n1165 : fastVisit (leafFrame 5 [10,6,1] ⟨514056,[8,215040,36864]⟩) [1] ⟨299008,[299008]⟩ b56 = true := join_live n1163 n1164

theorem n1166 : fastVisit (leafFrame 5 [10,6,1] ⟨514056,[8,215040,36864]⟩) [] ⟨0,[]⟩ b55 = true := join_live n1162 n1165

theorem n1167 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b18 = true := enterColumns 5 bank [10,6,1] ⟨514056,[8,215040,36864]⟩ b18 b55 (by decide +kernel) (by decide +kernel) n1166

theorem n1168 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b17 = true := join_dead n1167 (by decide +kernel)

theorem n1169 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b16 = true := join_dead n1168 (by decide +kernel)

theorem n1170 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b15 = true := join_dead n1169 (by decide +kernel)

theorem n1171 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b14 = true := join_dead n1170 (by decide +kernel)

theorem n1172 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b13 = true := join_dead n1171 (by decide +kernel)

theorem n1173 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b12 = true := join_dead n1172 (by decide +kernel)

theorem n1174 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b11 = true := join_dead n1173 (by decide +kernel)

theorem n1175 : fastVisit (leafCols 5 bank) [10,6,1] ⟨514056,[8,215040,36864]⟩ b10 = true := join_dead n1174 (by decide +kernel)

theorem n1176 : fastVisit (leafCols 5 bank) [6,1] ⟨514048,[215040,36864]⟩ b9 = true := join_live n1159 n1175

theorem n1177 : fastVisit (leafFrame 5 [9,6,1] ⟨522240,[8192,65536,4096]⟩) [] ⟨0,[]⟩ b60 = true := by decide +kernel

theorem n1178 : fastVisit (leafFrame 5 [9,6,1] ⟨522240,[8192,65536,4096]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n1179 : fastVisit (leafFrame 5 [9,6,1] ⟨522240,[8192,65536,4096]⟩) [] ⟨0,[]⟩ b59 = true := join_live n1177 n1178

theorem n1180 : fastVisit (leafFrame 5 [9,6,1] ⟨522240,[8192,65536,4096]⟩) [1] ⟨299008,[299008]⟩ b59 = true := by decide +kernel

theorem n1181 : fastVisit (leafFrame 5 [9,6,1] ⟨522240,[8192,65536,4096]⟩) [] ⟨0,[]⟩ b58 = true := join_live n1179 n1180

theorem n1182 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b18 = true := enterColumns 5 bank [9,6,1] ⟨522240,[8192,65536,4096]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n1181

theorem n1183 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b17 = true := join_dead n1182 (by decide +kernel)

theorem n1184 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b16 = true := join_dead n1183 (by decide +kernel)

theorem n1185 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b15 = true := join_dead n1184 (by decide +kernel)

theorem n1186 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b14 = true := join_dead n1185 (by decide +kernel)

theorem n1187 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b13 = true := join_dead n1186 (by decide +kernel)

theorem n1188 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b12 = true := join_dead n1187 (by decide +kernel)

theorem n1189 : fastVisit (leafCols 5 bank) [12,9,6,1] ⟨522538,[298,8192,65536,4096]⟩ b12 = true := by decide +kernel

theorem n1190 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b11 = true := join_live n1188 n1189

theorem n1191 : fastVisit (leafCols 5 bank) [9,6,1] ⟨522240,[8192,65536,4096]⟩ b10 = true := join_dead n1190 (by decide +kernel)

theorem n1192 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n1193 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n1194 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [] ⟨0,[]⟩ b61 = true := join_live n1192 n1193

theorem n1195 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n1196 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [] ⟨0,[]⟩ b45 = true := join_live n1194 n1195

theorem n1197 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n1198 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [] ⟨0,[]⟩ b44 = true := join_live n1196 n1197

theorem n1199 : fastVisit (leafFrame 5 [10,9,6,1] ⟨522248,[8,8192,65536,4096]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

end GainFinite.F5
