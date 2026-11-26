import PEqualNP.ThreeGateGain.FiniteV10P000

namespace GainFinite.F10
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n80 : fastVisit (leafFrame 10 [18] ⟨261632,[261632]⟩) [] ⟨0,[]⟩ b27 = true := join_live n78 n79

theorem n81 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b26 = true := enterColumns 10 bank [18] ⟨261632,[261632]⟩ b26 b27 (by decide +kernel) (by decide +kernel) n80

theorem n82 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b25 = true := join_dead n81 (by decide +kernel)

theorem n83 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b24 = true := join_dead n82 (by decide +kernel)

theorem n84 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b23 = true := join_dead n83 (by decide +kernel)

theorem n85 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b22 = true := join_dead n84 (by decide +kernel)

theorem n86 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b21 = true := join_dead n85 (by decide +kernel)

theorem n87 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b20 = true := join_dead n86 (by decide +kernel)

theorem n88 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b19 = true := join_dead n87 (by decide +kernel)

theorem n89 : fastVisit (leafCols 10 bank) [18] ⟨261632,[261632]⟩ b18 = true := join_dead n88 (by decide +kernel)

theorem n90 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b17 = true := join_live n73 n89

theorem n91 : fastVisit (leafCols 10 bank) [17] ⟨134051002,[134051002]⟩ b17 = true := by decide +kernel

theorem n92 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b16 = true := join_live n90 n91

theorem n93 : fastVisit (leafCols 10 bank) [16] ⟨134117692,[134117692]⟩ b16 = true := by decide +kernel

theorem n94 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b15 = true := join_live n92 n93

theorem n95 : fastVisit (leafCols 10 bank) [15] ⟨133984312,[133984312]⟩ b15 = true := by decide +kernel

theorem n96 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b14 = true := join_live n94 n95

theorem n97 : fastVisit (leafCols 10 bank) [14] ⟨134194642,[134194642]⟩ b14 = true := by decide +kernel

theorem n98 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b13 = true := join_live n96 n97

theorem n99 : fastVisit (leafCols 10 bank) [13] ⟨134203876,[134203876]⟩ b13 = true := by decide +kernel

theorem n100 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b12 = true := join_live n98 n99

theorem n101 : fastVisit (leafCols 10 bank) [12] ⟨134185408,[134185408]⟩ b12 = true := by decide +kernel

theorem n102 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b11 = true := join_live n100 n101

theorem n103 : fastVisit (leafCols 10 bank) [11] ⟨134030482,[134030482]⟩ b13 = true := by decide +kernel

theorem n104 : fastVisit (leafCols 10 bank) [13,11] ⟨134213110,[182628,9234]⟩ b13 = true := by decide +kernel

theorem n105 : fastVisit (leafCols 10 bank) [11] ⟨134030482,[134030482]⟩ b12 = true := join_live n103 n104

theorem n106 : fastVisit (leafCols 10 bank) [12,11] ⟨134194642,[164160,9234]⟩ b12 = true := by decide +kernel

theorem n107 : fastVisit (leafCols 10 bank) [11] ⟨134030482,[134030482]⟩ b11 = true := join_live n105 n106

theorem n108 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b10 = true := join_live n102 n107

theorem n109 : fastVisit (leafCols 10 bank) [10] ⟨134105380,[134105380]⟩ b14 = true := by decide +kernel

theorem n110 : fastVisit (leafCols 10 bank) [14,10] ⟨134213110,[107730,18468]⟩ b14 = true := by decide +kernel

theorem n111 : fastVisit (leafCols 10 bank) [10] ⟨134105380,[134105380]⟩ b13 = true := join_live n109 n110

theorem n112 : fastVisit (leafCols 10 bank) [10] ⟨134105380,[134105380]⟩ b12 = true := join_dead n111 (by decide +kernel)

theorem n113 : fastVisit (leafCols 10 bank) [12,10] ⟨134203876,[98496,18468]⟩ b12 = true := by decide +kernel

theorem n114 : fastVisit (leafCols 10 bank) [10] ⟨134105380,[134105380]⟩ b11 = true := join_live n112 n113

theorem n115 : fastVisit (leafCols 10 bank) [11,10] ⟨134180278,[74898,149796]⟩ b11 = true := by decide +kernel

theorem n116 : fastVisit (leafCols 10 bank) [10] ⟨134105380,[134105380]⟩ b10 = true := join_live n114 n115

theorem n117 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b9 = true := join_live n108 n116

theorem n118 : fastVisit (leafFrame 10 [9] ⟨133955584,[133955584]⟩) [] ⟨0,[]⟩ b34 = true := by decide +kernel

theorem n119 : fastVisit (leafFrame 10 [9] ⟨133955584,[133955584]⟩) [3] ⟨117670336,[117670336]⟩ b34 = true := by decide +kernel

theorem n120 : fastVisit (leafFrame 10 [9] ⟨133955584,[133955584]⟩) [] ⟨0,[]⟩ b33 = true := join_live n118 n119

theorem n121 : fastVisit (leafFrame 10 [9] ⟨133955584,[133955584]⟩) [2] ⟨38347922,[38347922]⟩ b33 = true := by decide +kernel

theorem n122 : fastVisit (leafFrame 10 [9] ⟨133955584,[133955584]⟩) [] ⟨0,[]⟩ b32 = true := join_live n120 n121

theorem n123 : fastVisit (leafFrame 10 [9] ⟨133955584,[133955584]⟩) [1] ⟨76695844,[76695844]⟩ b32 = true := by decide +kernel

theorem n124 : fastVisit (leafFrame 10 [9] ⟨133955584,[133955584]⟩) [] ⟨0,[]⟩ b31 = true := join_live n122 n123

theorem n125 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b26 = true := enterColumns 10 bank [9] ⟨133955584,[133955584]⟩ b26 b31 (by decide +kernel) (by decide +kernel) n124

theorem n126 : fastVisit (leafCols 10 bank) [26,9] ⟨134217402,[261818,85196800]⟩ b26 = true := by decide +kernel

theorem n127 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b25 = true := join_live n125 n126

theorem n128 : fastVisit (leafCols 10 bank) [25,9] ⟨134217532,[261948,51118080]⟩ b25 = true := by decide +kernel

theorem n129 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b24 = true := join_live n127 n128

theorem n130 : fastVisit (leafCols 10 bank) [24,9] ⟨134217272,[261688,119275520]⟩ b24 = true := by decide +kernel

theorem n131 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b23 = true := join_live n129 n130

theorem n132 : fastVisit (leafCols 10 bank) [23,9] ⟨134217682,[262098,11796480]⟩ b23 = true := by decide +kernel

theorem n133 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b22 = true := join_live n131 n132

theorem n134 : fastVisit (leafCols 10 bank) [22,9] ⟨134217700,[262116,7077888]⟩ b22 = true := by decide +kernel

theorem n135 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b21 = true := join_live n133 n134

theorem n136 : fastVisit (leafCols 10 bank) [21,9] ⟨134217664,[262080,16515072]⟩ b21 = true := by decide +kernel

theorem n137 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b20 = true := join_live n135 n136

theorem n138 : fastVisit (leafCols 10 bank) [20,9] ⟨134217362,[261778,95682560]⟩ b20 = true := by decide +kernel

theorem n139 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b19 = true := join_live n137 n138

theorem n140 : fastVisit (leafCols 10 bank) [19,9] ⟨134217508,[261924,57409536]⟩ b19 = true := by decide +kernel

theorem n141 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b18 = true := join_live n139 n140

theorem n142 : fastVisit (leafCols 10 bank) [18,9] ⟨134217216,[261632,133955584]⟩ b18 = true := by decide +kernel

theorem n143 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b17 = true := join_live n141 n142

theorem n144 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b16 = true := join_dead n143 (by decide +kernel)

theorem n145 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b15 = true := join_dead n144 (by decide +kernel)

theorem n146 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b14 = true := join_dead n145 (by decide +kernel)

theorem n147 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b13 = true := join_dead n146 (by decide +kernel)

theorem n148 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b12 = true := join_dead n147 (by decide +kernel)

theorem n149 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b11 = true := join_dead n148 (by decide +kernel)

theorem n150 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b10 = true := join_dead n149 (by decide +kernel)

theorem n151 : fastVisit (leafCols 10 bank) [9] ⟨133955584,[133955584]⟩ b9 = true := join_dead n150 (by decide +kernel)

theorem n152 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b8 = true := join_live n117 n151

theorem n153 : fastVisit (leafCols 10 bank) [8] ⟨48854202,[48854202]⟩ b15 = true := by decide +kernel

theorem n154 : fastVisit (leafCols 10 bank) [15,8] ⟨134051002,[85196800,66690]⟩ b15 = true := by decide +kernel

theorem n155 : fastVisit (leafCols 10 bank) [8] ⟨48854202,[48854202]⟩ b14 = true := join_live n153 n154

theorem n156 : fastVisit (leafCols 10 bank) [14,8] ⟨134215162,[85360960,20520]⟩ b14 = true := by decide +kernel

theorem n157 : fastVisit (leafCols 10 bank) [8] ⟨48854202,[48854202]⟩ b13 = true := join_live n155 n156

theorem n158 : fastVisit (leafCols 10 bank) [13,8] ⟨134217214,[85363012,13338]⟩ b13 = true := by decide +kernel

theorem n159 : fastVisit (leafCols 10 bank) [8] ⟨48854202,[48854202]⟩ b12 = true := join_live n157 n158

end GainFinite.F10
