import PEqualNP.ThreeGateGain.FiniteV12P000

namespace GainFinite.F12
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n80 : fastVisit (leafCols 12 bank) [17,12] ⟨33554252,[48716,14352640]⟩ b17 = true := by decide +kernel

theorem n81 : fastVisit (leafCols 12 bank) [12] ⟨33505536,[33505536]⟩ b16 = true := join_live n79 n80

theorem n82 : fastVisit (leafCols 12 bank) [16,12] ⟨33553672,[48136,33489152]⟩ b16 = true := by decide +kernel

theorem n83 : fastVisit (leafCols 12 bank) [12] ⟨33505536,[33505536]⟩ b15 = true := join_live n81 n82

theorem n84 : fastVisit (leafCols 12 bank) [12] ⟨33505536,[33505536]⟩ b14 = true := join_dead n83 (by decide +kernel)

theorem n85 : fastVisit (leafCols 12 bank) [14,12] ⟨33543036,[37500,16640]⟩ b14 = true := by decide +kernel

theorem n86 : fastVisit (leafCols 12 bank) [12] ⟨33505536,[33505536]⟩ b13 = true := join_live n84 n85

theorem n87 : fastVisit (leafCols 12 bank) [13,12] ⟨33505656,[120,16640]⟩ b13 = true := by decide +kernel

theorem n88 : fastVisit (leafCols 12 bank) [12] ⟨33505536,[33505536]⟩ b12 = true := join_live n86 n87

theorem n89 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b11 = true := join_live n76 n88

theorem n90 : fastVisit (leafCols 12 bank) [11] ⟨33522176,[33522176]⟩ b18 = true := by decide +kernel

theorem n91 : fastVisit (leafCols 12 bank) [18,11] ⟨33554218,[32042,23921152]⟩ b18 = true := by decide +kernel

theorem n92 : fastVisit (leafCols 12 bank) [11] ⟨33522176,[33522176]⟩ b17 = true := join_live n90 n91

theorem n93 : fastVisit (leafCols 12 bank) [17,11] ⟨33553996,[31820,14352384]⟩ b17 = true := by decide +kernel

theorem n94 : fastVisit (leafCols 12 bank) [11] ⟨33522176,[33522176]⟩ b16 = true := join_live n92 n93

theorem n95 : fastVisit (leafCols 12 bank) [16,11] ⟨33553928,[31752,33489408]⟩ b16 = true := by decide +kernel

theorem n96 : fastVisit (leafCols 12 bank) [11] ⟨33522176,[33522176]⟩ b15 = true := join_live n94 n95

theorem n97 : fastVisit (leafCols 12 bank) [15,11] ⟨33540986,[18810,33280]⟩ b15 = true := by decide +kernel

theorem n98 : fastVisit (leafCols 12 bank) [11] ⟨33522176,[33522176]⟩ b14 = true := join_live n96 n97

theorem n99 : fastVisit (leafCols 12 bank) [11] ⟨33522176,[33522176]⟩ b13 = true := join_dead n98 (by decide +kernel)

theorem n100 : fastVisit (leafCols 12 bank) [13,11] ⟨33522296,[120,33280]⟩ b13 = true := by decide +kernel

theorem n101 : fastVisit (leafCols 12 bank) [11] ⟨33522176,[33522176]⟩ b12 = true := join_live n99 n100

theorem n102 : fastVisit (leafCols 12 bank) [12,11] ⟨33538816,[16640,33280]⟩ b12 = true := by decide +kernel

theorem n103 : fastVisit (leafCols 12 bank) [11] ⟨33522176,[33522176]⟩ b11 = true := join_live n101 n102

theorem n104 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b10 = true := join_live n89 n103

theorem n105 : fastVisit (leafFrame 12 [10] ⟨33488896,[33488896]⟩) [] ⟨0,[]⟩ b30 = true := by decide +kernel

theorem n106 : fastVisit (leafFrame 12 [10] ⟨33488896,[33488896]⟩) [1] ⟨19169792,[19169792]⟩ b30 = true := by decide +kernel

theorem n107 : fastVisit (leafFrame 12 [10] ⟨33488896,[33488896]⟩) [] ⟨0,[]⟩ b29 = true := join_live n105 n106

theorem n108 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b24 = true := enterColumns 12 bank [10] ⟨33488896,[33488896]⟩ b24 b29 (by decide +kernel) (by decide +kernel) n107

theorem n109 : fastVisit (leafCols 12 bank) [24,10] ⟨33553786,[64890,21299200]⟩ b24 = true := by decide +kernel

theorem n110 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b23 = true := join_live n108 n109

theorem n111 : fastVisit (leafCols 12 bank) [23,10] ⟨33554044,[65148,12779520]⟩ b23 = true := by decide +kernel

theorem n112 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b22 = true := join_live n110 n111

theorem n113 : fastVisit (leafCols 12 bank) [22,10] ⟨33553528,[64632,29818880]⟩ b22 = true := by decide +kernel

theorem n114 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b21 = true := join_live n112 n113

theorem n115 : fastVisit (leafCols 12 bank) [21,10] ⟨33554346,[65450,2949120]⟩ b21 = true := by decide +kernel

theorem n116 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b20 = true := join_live n114 n115

theorem n117 : fastVisit (leafCols 12 bank) [20,10] ⟨33554380,[65484,1769472]⟩ b20 = true := by decide +kernel

theorem n118 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b19 = true := join_live n116 n117

theorem n119 : fastVisit (leafCols 12 bank) [19,10] ⟨33554312,[65416,4128768]⟩ b19 = true := by decide +kernel

theorem n120 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b18 = true := join_live n118 n119

theorem n121 : fastVisit (leafCols 12 bank) [18,10] ⟨33553706,[64810,23920640]⟩ b18 = true := by decide +kernel

theorem n122 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b17 = true := join_live n120 n121

theorem n123 : fastVisit (leafCols 12 bank) [17,10] ⟨33553996,[65100,14352384]⟩ b17 = true := by decide +kernel

theorem n124 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b16 = true := join_live n122 n123

theorem n125 : fastVisit (leafCols 12 bank) [16,10] ⟨33553416,[64520,33488896]⟩ b16 = true := by decide +kernel

theorem n126 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b15 = true := join_live n124 n125

theorem n127 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b14 = true := join_dead n126 (by decide +kernel)

theorem n128 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b13 = true := join_dead n127 (by decide +kernel)

theorem n129 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b12 = true := join_dead n128 (by decide +kernel)

theorem n130 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b11 = true := join_dead n129 (by decide +kernel)

theorem n131 : fastVisit (leafCols 12 bank) [10] ⟨33488896,[33488896]⟩ b10 = true := join_dead n130 (by decide +kernel)

theorem n132 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b9 = true := join_live n104 n131

theorem n133 : fastVisit (leafCols 12 bank) [9] ⟨12208506,[12208506]⟩ b13 = true := by decide +kernel

theorem n134 : fastVisit (leafCols 12 bank) [13,9] ⟨33507706,[21299200,18690]⟩ b13 = true := by decide +kernel

theorem n135 : fastVisit (leafCols 12 bank) [9] ⟨12208506,[12208506]⟩ b12 = true := join_live n133 n134

theorem n136 : fastVisit (leafCols 12 bank) [12,9] ⟨33507706,[21299200,2170]⟩ b12 = true := by decide +kernel

theorem n137 : fastVisit (leafCols 12 bank) [9] ⟨12208506,[12208506]⟩ b11 = true := join_live n135 n136

theorem n138 : fastVisit (leafCols 12 bank) [11,9] ⟨33540986,[21332480,18810]⟩ b11 = true := by decide +kernel

theorem n139 : fastVisit (leafCols 12 bank) [9] ⟨12208506,[12208506]⟩ b10 = true := join_live n137 n138

theorem n140 : fastVisit (leafCols 12 bank) [10,9] ⟨33507706,[21299200,18810]⟩ b10 = true := by decide +kernel

theorem n141 : fastVisit (leafCols 12 bank) [9] ⟨12208506,[12208506]⟩ b9 = true := join_live n139 n140

theorem n142 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b8 = true := join_live n132 n141

theorem n143 : fastVisit (leafCols 12 bank) [8] ⟨20746876,[20746876]⟩ b13 = true := by decide +kernel

theorem n144 : fastVisit (leafCols 12 bank) [13,8] ⟨33526396,[12779520,37380]⟩ b13 = true := by decide +kernel

theorem n145 : fastVisit (leafCols 12 bank) [8] ⟨20746876,[20746876]⟩ b12 = true := join_live n143 n144

theorem n146 : fastVisit (leafCols 12 bank) [12,8] ⟨33543036,[12796160,37500]⟩ b12 = true := by decide +kernel

theorem n147 : fastVisit (leafCols 12 bank) [8] ⟨20746876,[20746876]⟩ b11 = true := join_live n145 n146

theorem n148 : fastVisit (leafCols 12 bank) [11,8] ⟨33526396,[12779520,4220]⟩ b11 = true := by decide +kernel

theorem n149 : fastVisit (leafCols 12 bank) [8] ⟨20746876,[20746876]⟩ b10 = true := join_live n147 n148

theorem n150 : fastVisit (leafCols 12 bank) [10,8] ⟨33526396,[12779520,37500]⟩ b10 = true := by decide +kernel

theorem n151 : fastVisit (leafCols 12 bank) [8] ⟨20746876,[20746876]⟩ b9 = true := join_live n149 n150

theorem n152 : fastVisit (leafCols 12 bank) [9,8] ⟨29285246,[8538370,17076740]⟩ b9 = true := by decide +kernel

theorem n153 : fastVisit (leafCols 12 bank) [8] ⟨20746876,[20746876]⟩ b8 = true := join_live n151 n152

theorem n154 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b7 = true := join_live n142 n153

theorem n155 : fastVisit (leafFrame 12 [7] ⟨3670136,[3670136]⟩) [] ⟨0,[]⟩ b34 = true := by decide +kernel

theorem n156 : fastVisit (leafFrame 12 [7] ⟨3670136,[3670136]⟩) [7] ⟨3670136,[3670136]⟩ b34 = true := by decide +kernel

theorem n157 : fastVisit (leafFrame 12 [7] ⟨3670136,[3670136]⟩) [] ⟨0,[]⟩ b33 = true := join_live n155 n156

theorem n158 : fastVisit (leafFrame 12 [7] ⟨3670136,[3670136]⟩) [2] ⟨9584896,[9584896]⟩ b33 = true := by decide +kernel

theorem n159 : fastVisit (leafFrame 12 [7] ⟨3670136,[3670136]⟩) [] ⟨0,[]⟩ b32 = true := join_live n157 n158

end GainFinite.F12
