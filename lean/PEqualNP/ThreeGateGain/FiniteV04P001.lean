import PEqualNP.ThreeGateGain.FiniteV04P000

namespace GainFinite.F4
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n80 : fastVisit (leafCols 4 bank) [8,3] ⟨28800,[128,28672]⟩ b8 = true := by decide +kernel

theorem n81 : fastVisit (leafCols 4 bank) [3] ⟨28672,[28672]⟩ b7 = true := join_live n79 n80

theorem n82 : fastVisit (leafCols 4 bank) [3] ⟨28672,[28672]⟩ b6 = true := join_dead n81 (by decide +kernel)

theorem n83 : fastVisit (leafCols 4 bank) [6,3] ⟨31232,[2560,20480]⟩ b10 = true := by decide +kernel

theorem n84 : fastVisit (leafCols 4 bank) [10,6,3] ⟨31392,[160,2560,20480]⟩ b10 = true := by decide +kernel

theorem n85 : fastVisit (leafCols 4 bank) [6,3] ⟨31232,[2560,20480]⟩ b9 = true := join_live n83 n84

theorem n86 : fastVisit (leafCols 4 bank) [9,6,3] ⟨31424,[192,2560,4096]⟩ b10 = true := by decide +kernel

theorem n87 : fastVisit (leafCols 4 bank) [10,9,6,3] ⟨31456,[32,64,2560,4096]⟩ b12 = true := by decide +kernel

theorem n88 : fastVisit (leafCols 4 bank) [12,10,9,6,3] ⟨31464,[8,32,64,512,4096]⟩ b12 = true := by decide +kernel

theorem n89 : fastVisit (leafCols 4 bank) [10,9,6,3] ⟨31456,[32,64,2560,4096]⟩ b11 = true := join_live n87 n88

theorem n90 : fastVisit (leafCols 4 bank) [10,9,6,3] ⟨31456,[32,64,2560,4096]⟩ b10 = true := join_dead n89 (by decide +kernel)

theorem n91 : fastVisit (leafCols 4 bank) [9,6,3] ⟨31424,[192,2560,4096]⟩ b9 = true := join_live n86 n90

theorem n92 : fastVisit (leafCols 4 bank) [6,3] ⟨31232,[2560,20480]⟩ b8 = true := join_live n85 n91

theorem n93 : fastVisit (leafCols 4 bank) [8,6,3] ⟨31360,[128,2560,20480]⟩ b8 = true := by decide +kernel

theorem n94 : fastVisit (leafCols 4 bank) [6,3] ⟨31232,[2560,20480]⟩ b7 = true := join_live n92 n93

theorem n95 : fastVisit (leafCols 4 bank) [6,3] ⟨31232,[2560,20480]⟩ b6 = true := join_dead n94 (by decide +kernel)

theorem n96 : fastVisit (leafCols 4 bank) [3] ⟨28672,[28672]⟩ b5 = true := join_live n82 n95

theorem n97 : fastVisit (leafCols 4 bank) [5,3] ⟨31744,[3072,12288]⟩ b10 = true := by decide +kernel

theorem n98 : fastVisit (leafCols 4 bank) [10,5,3] ⟨31904,[160,3072,4096]⟩ b10 = true := by decide +kernel

theorem n99 : fastVisit (leafCols 4 bank) [5,3] ⟨31744,[3072,12288]⟩ b9 = true := join_live n97 n98

theorem n100 : fastVisit (leafCols 4 bank) [9,5,3] ⟨31936,[192,3072,12288]⟩ b10 = true := by decide +kernel

theorem n101 : fastVisit (leafCols 4 bank) [10,9,5,3] ⟨31968,[32,64,3072,4096]⟩ b12 = true := by decide +kernel

theorem n102 : fastVisit (leafCols 4 bank) [12,10,9,5,3] ⟨31976,[8,32,64,1024,4096]⟩ b12 = true := by decide +kernel

theorem n103 : fastVisit (leafCols 4 bank) [10,9,5,3] ⟨31968,[32,64,3072,4096]⟩ b11 = true := join_live n101 n102

theorem n104 : fastVisit (leafCols 4 bank) [10,9,5,3] ⟨31968,[32,64,3072,4096]⟩ b10 = true := join_dead n103 (by decide +kernel)

theorem n105 : fastVisit (leafCols 4 bank) [9,5,3] ⟨31936,[192,3072,12288]⟩ b9 = true := join_live n100 n104

theorem n106 : fastVisit (leafCols 4 bank) [5,3] ⟨31744,[3072,12288]⟩ b8 = true := join_live n99 n105

theorem n107 : fastVisit (leafCols 4 bank) [8,5,3] ⟨31872,[128,3072,12288]⟩ b8 = true := by decide +kernel

theorem n108 : fastVisit (leafCols 4 bank) [5,3] ⟨31744,[3072,12288]⟩ b7 = true := join_live n106 n107

theorem n109 : fastVisit (leafCols 4 bank) [5,3] ⟨31744,[3072,12288]⟩ b6 = true := join_dead n108 (by decide +kernel)

theorem n110 : fastVisit (leafCols 4 bank) [6,5,3] ⟨32256,[512,1024,4096]⟩ b10 = true := by decide +kernel

theorem n111 : fastVisit (leafCols 4 bank) [10,6,5,3] ⟨32416,[160,512,1024,4096]⟩ b12 = true := by decide +kernel

theorem n112 : fastVisit (leafCols 4 bank) [12,10,6,5,3] ⟨32424,[8,32,512,1024,4096]⟩ b12 = true := by decide +kernel

theorem n113 : fastVisit (leafCols 4 bank) [10,6,5,3] ⟨32416,[160,512,1024,4096]⟩ b11 = true := join_live n111 n112

theorem n114 : fastVisit (leafCols 4 bank) [10,6,5,3] ⟨32416,[160,512,1024,4096]⟩ b10 = true := join_dead n113 (by decide +kernel)

theorem n115 : fastVisit (leafCols 4 bank) [6,5,3] ⟨32256,[512,1024,4096]⟩ b9 = true := join_live n110 n114

theorem n116 : fastVisit (leafCols 4 bank) [9,6,5,3] ⟨32448,[192,512,1024,4096]⟩ b12 = true := by decide +kernel

theorem n117 : fastVisit (leafCols 4 bank) [12,9,6,5,3] ⟨32456,[8,64,512,1024,4096]⟩ b12 = true := by decide +kernel

theorem n118 : fastVisit (leafCols 4 bank) [9,6,5,3] ⟨32448,[192,512,1024,4096]⟩ b11 = true := join_live n116 n117

theorem n119 : fastVisit (leafCols 4 bank) [9,6,5,3] ⟨32448,[192,512,1024,4096]⟩ b10 = true := join_dead n118 (by decide +kernel)

theorem n120 : fastVisit (leafCols 4 bank) [10,9,6,5,3] ⟨32480,[32,64,512,1024,4096]⟩ b12 = true := by decide +kernel

theorem n121 : fastVisit (leafCols 4 bank) [12,10,9,6,5,3] ⟨32488,[8,32,64,512,1024,4096]⟩ b12 = true := by decide +kernel

theorem n122 : fastVisit (leafCols 4 bank) [10,9,6,5,3] ⟨32480,[32,64,512,1024,4096]⟩ b11 = true := join_live n120 n121

theorem n123 : fastVisit (leafCols 4 bank) [10,9,6,5,3] ⟨32480,[32,64,512,1024,4096]⟩ b10 = true := join_dead n122 (by decide +kernel)

theorem n124 : fastVisit (leafCols 4 bank) [9,6,5,3] ⟨32448,[192,512,1024,4096]⟩ b9 = true := join_live n119 n123

theorem n125 : fastVisit (leafCols 4 bank) [6,5,3] ⟨32256,[512,1024,4096]⟩ b8 = true := join_live n115 n124

theorem n126 : fastVisit (leafCols 4 bank) [8,6,5,3] ⟨32384,[128,512,1024,4096]⟩ b8 = true := by decide +kernel

theorem n127 : fastVisit (leafCols 4 bank) [6,5,3] ⟨32256,[512,1024,4096]⟩ b7 = true := join_live n125 n126

theorem n128 : fastVisit (leafCols 4 bank) [6,5,3] ⟨32256,[512,1024,4096]⟩ b6 = true := join_dead n127 (by decide +kernel)

theorem n129 : fastVisit (leafCols 4 bank) [5,3] ⟨31744,[3072,12288]⟩ b5 = true := join_live n109 n128

theorem n130 : fastVisit (leafCols 4 bank) [3] ⟨28672,[28672]⟩ b4 = true := join_live n96 n129

theorem n131 : fastVisit (leafCols 4 bank) [4,3] ⟨30720,[2048,28672]⟩ b9 = true := by decide +kernel

theorem n132 : fastVisit (leafCols 4 bank) [9,4,3] ⟨30912,[192,2048,12288]⟩ b10 = true := by decide +kernel

theorem n133 : fastVisit (leafCols 4 bank) [10,9,4,3] ⟨30944,[32,64,2048,4096]⟩ b10 = true := by decide +kernel

theorem n134 : fastVisit (leafCols 4 bank) [9,4,3] ⟨30912,[192,2048,12288]⟩ b9 = true := join_live n132 n133

theorem n135 : fastVisit (leafCols 4 bank) [4,3] ⟨30720,[2048,28672]⟩ b8 = true := join_live n131 n134

theorem n136 : fastVisit (leafCols 4 bank) [8,4,3] ⟨30848,[128,2048,28672]⟩ b8 = true := by decide +kernel

theorem n137 : fastVisit (leafCols 4 bank) [4,3] ⟨30720,[2048,28672]⟩ b7 = true := join_live n135 n136

theorem n138 : fastVisit (leafCols 4 bank) [4,3] ⟨30720,[2048,28672]⟩ b6 = true := join_dead n137 (by decide +kernel)

theorem n139 : fastVisit (leafCols 4 bank) [4,3] ⟨30720,[2048,28672]⟩ b5 = true := join_dead n138 (by decide +kernel)

theorem n140 : fastVisit (leafCols 4 bank) [4,3] ⟨30720,[2048,28672]⟩ b4 = true := join_dead n139 (by decide +kernel)

theorem n141 : fastVisit (leafCols 4 bank) [3] ⟨28672,[28672]⟩ b3 = true := join_live n130 n140

theorem n142 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b2 = true := join_live n72 n141

theorem n143 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b12 = true := by decide +kernel

theorem n144 : fastVisit (leafCols 4 bank) [12,2] ⟨10376,[2184,8192]⟩ b12 = true := by decide +kernel

theorem n145 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b11 = true := join_live n143 n144

theorem n146 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b10 = true := join_dead n145 (by decide +kernel)

theorem n147 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b9 = true := join_dead n146 (by decide +kernel)

theorem n148 : fastVisit (leafCols 4 bank) [9,2] ⟨24768,[16576,8192]⟩ b9 = true := by decide +kernel

theorem n149 : fastVisit (leafCols 4 bank) [2] ⟨8192,[8192]⟩ b8 = true := join_live n147 n148

theorem n150 : fastVisit (leafFrame 4 [8,2] ⟨8320,[128,8192]⟩) [] ⟨0,[]⟩ b18 = true := by decide +kernel

theorem n151 : fastVisit (leafFrame 4 [8,2] ⟨8320,[128,8192]⟩) [1] ⟨16384,[16384]⟩ b18 = true := by decide +kernel

theorem n152 : fastVisit (leafFrame 4 [8,2] ⟨8320,[128,8192]⟩) [] ⟨0,[]⟩ b17 = true := join_live n150 n151

theorem n153 : fastVisit (leafCols 4 bank) [8,2] ⟨8320,[128,8192]⟩ b14 = true := enterColumns 4 bank [8,2] ⟨8320,[128,8192]⟩ b14 b17 (by decide +kernel) (by decide +kernel) n152

theorem n154 : fastVisit (leafCols 4 bank) [8,2] ⟨8320,[128,8192]⟩ b13 = true := join_dead n153 (by decide +kernel)

theorem n155 : fastVisit (leafCols 4 bank) [8,2] ⟨8320,[128,8192]⟩ b12 = true := join_dead n154 (by decide +kernel)

theorem n156 : fastVisit (leafCols 4 bank) [8,2] ⟨8320,[128,8192]⟩ b11 = true := join_dead n155 (by decide +kernel)

theorem n157 : fastVisit (leafCols 4 bank) [8,2] ⟨8320,[128,8192]⟩ b10 = true := join_dead n156 (by decide +kernel)

theorem n158 : fastVisit (leafCols 4 bank) [8,2] ⟨8320,[128,8192]⟩ b9 = true := join_dead n157 (by decide +kernel)

theorem n159 : fastVisit (leafCols 4 bank) [8,2] ⟨8320,[128,8192]⟩ b8 = true := join_dead n158 (by decide +kernel)

end GainFinite.F4
