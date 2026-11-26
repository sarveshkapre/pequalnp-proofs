import PEqualNP.ThreeGateGain.FiniteV08P000

namespace GainFinite.F8
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n80 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b6 = true := join_live n69 n79

theorem n81 : fastVisit (leafFrame 8 [6] ⟨229376,[229376]⟩) [] ⟨0,[]⟩ b28 = true := by decide +kernel

theorem n82 : fastVisit (leafFrame 8 [6] ⟨229376,[229376]⟩) [3] ⟨1835008,[1835008]⟩ b28 = true := by decide +kernel

theorem n83 : fastVisit (leafFrame 8 [6] ⟨229376,[229376]⟩) [] ⟨0,[]⟩ b27 = true := join_live n81 n82

theorem n84 : fastVisit (leafFrame 8 [6] ⟨229376,[229376]⟩) [2] ⟨599186,[599186]⟩ b27 = true := by decide +kernel

theorem n85 : fastVisit (leafFrame 8 [6] ⟨229376,[229376]⟩) [] ⟨0,[]⟩ b26 = true := join_live n83 n84

theorem n86 : fastVisit (leafFrame 8 [6] ⟨229376,[229376]⟩) [1] ⟨1198372,[1198372]⟩ b26 = true := by decide +kernel

theorem n87 : fastVisit (leafFrame 8 [6] ⟨229376,[229376]⟩) [] ⟨0,[]⟩ b25 = true := join_live n85 n86

theorem n88 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b20 = true := enterColumns 8 bank [6] ⟨229376,[229376]⟩ b20 b25 (by decide +kernel) (by decide +kernel) n87

theorem n89 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b19 = true := join_dead n88 (by decide +kernel)

theorem n90 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b18 = true := join_dead n89 (by decide +kernel)

theorem n91 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b17 = true := join_dead n90 (by decide +kernel)

theorem n92 : fastVisit (leafCols 8 bank) [17,6] ⟨2076626,[1847250,163840]⟩ b17 = true := by decide +kernel

theorem n93 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b16 = true := join_live n91 n92

theorem n94 : fastVisit (leafCols 8 bank) [16,6] ⟨2084836,[1855460,98304]⟩ b16 = true := by decide +kernel

theorem n95 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b15 = true := join_live n93 n94

theorem n96 : fastVisit (leafCols 8 bank) [15,6] ⟨2068416,[1839040,229376]⟩ b15 = true := by decide +kernel

theorem n97 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b14 = true := join_live n95 n96

theorem n98 : fastVisit (leafCols 8 bank) [14,6] ⟨765586,[536210,163840]⟩ b14 = true := by decide +kernel

theorem n99 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b13 = true := join_live n97 n98

theorem n100 : fastVisit (leafCols 8 bank) [13,6] ⟨1298212,[1068836,98304]⟩ b13 = true := by decide +kernel

theorem n101 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b12 = true := join_live n99 n100

theorem n102 : fastVisit (leafFrame 8 [12,6] ⟨232960,[3584,229376]⟩) [] ⟨0,[]⟩ b30 = true := by decide +kernel

theorem n103 : fastVisit (leafFrame 8 [12,6] ⟨232960,[3584,229376]⟩) [1] ⟨1198372,[1198372]⟩ b30 = true := by decide +kernel

theorem n104 : fastVisit (leafFrame 8 [12,6] ⟨232960,[3584,229376]⟩) [] ⟨0,[]⟩ b29 = true := join_live n102 n103

theorem n105 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b20 = true := enterColumns 8 bank [12,6] ⟨232960,[3584,229376]⟩ b20 b29 (by decide +kernel) (by decide +kernel) n104

theorem n106 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b19 = true := join_dead n105 (by decide +kernel)

theorem n107 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b18 = true := join_dead n106 (by decide +kernel)

theorem n108 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b17 = true := join_dead n107 (by decide +kernel)

theorem n109 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b16 = true := join_dead n108 (by decide +kernel)

theorem n110 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b15 = true := join_dead n109 (by decide +kernel)

theorem n111 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b14 = true := join_dead n110 (by decide +kernel)

theorem n112 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b13 = true := join_dead n111 (by decide +kernel)

theorem n113 : fastVisit (leafCols 8 bank) [12,6] ⟨232960,[3584,229376]⟩ b12 = true := join_dead n112 (by decide +kernel)

theorem n114 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b11 = true := join_live n101 n113

theorem n115 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b10 = true := join_dead n114 (by decide +kernel)

theorem n116 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b9 = true := join_dead n115 (by decide +kernel)

theorem n117 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b8 = true := join_dead n116 (by decide +kernel)

theorem n118 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b7 = true := join_dead n117 (by decide +kernel)

theorem n119 : fastVisit (leafCols 8 bank) [6] ⟨229376,[229376]⟩ b6 = true := join_dead n118 (by decide +kernel)

theorem n120 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b5 = true := join_live n80 n119

theorem n121 : fastVisit (leafCols 8 bank) [5] ⟨1909906,[1909906]⟩ b12 = true := by decide +kernel

theorem n122 : fastVisit (leafCols 8 bank) [12,5] ⟨1912466,[2560,1908882]⟩ b12 = true := by decide +kernel

theorem n123 : fastVisit (leafCols 8 bank) [5] ⟨1909906,[1909906]⟩ b11 = true := join_live n121 n122

theorem n124 : fastVisit (leafCols 8 bank) [5] ⟨1909906,[1909906]⟩ b10 = true := join_dead n123 (by decide +kernel)

theorem n125 : fastVisit (leafCols 8 bank) [10,5] ⟨2096566,[186660,1170]⟩ b10 = true := by decide +kernel

theorem n126 : fastVisit (leafCols 8 bank) [5] ⟨1909906,[1909906]⟩ b9 = true := join_live n124 n125

theorem n127 : fastVisit (leafCols 8 bank) [9,5] ⟨2094226,[184320,1170]⟩ b9 = true := by decide +kernel

theorem n128 : fastVisit (leafCols 8 bank) [5] ⟨1909906,[1909906]⟩ b8 = true := join_live n126 n127

theorem n129 : fastVisit (leafCols 8 bank) [8,5] ⟨2073746,[163840,1310720]⟩ b8 = true := by decide +kernel

theorem n130 : fastVisit (leafCols 8 bank) [5] ⟨1909906,[1909906]⟩ b7 = true := join_live n128 n129

theorem n131 : fastVisit (leafCols 8 bank) [7,5] ⟨2092470,[182564,795794]⟩ b7 = true := by decide +kernel

theorem n132 : fastVisit (leafCols 8 bank) [5] ⟨1909906,[1909906]⟩ b6 = true := join_live n130 n131

theorem n133 : fastVisit (leafCols 8 bank) [6,5] ⟨2073746,[163840,1844370]⟩ b6 = true := by decide +kernel

theorem n134 : fastVisit (leafCols 8 bank) [5] ⟨1909906,[1909906]⟩ b5 = true := join_live n132 n133

theorem n135 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b4 = true := join_live n120 n134

theorem n136 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b12 = true := by decide +kernel

theorem n137 : fastVisit (leafCols 8 bank) [12,4] ⟨1986340,[1536,1982756]⟩ b12 = true := by decide +kernel

theorem n138 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b11 = true := join_live n136 n137

theorem n139 : fastVisit (leafCols 8 bank) [11,4] ⟨2096566,[111762,2340]⟩ b11 = true := by decide +kernel

theorem n140 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b10 = true := join_live n138 n139

theorem n141 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b9 = true := join_dead n140 (by decide +kernel)

theorem n142 : fastVisit (leafCols 8 bank) [9,4] ⟨2095396,[110592,2340]⟩ b9 = true := by decide +kernel

theorem n143 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b8 = true := join_live n141 n142

theorem n144 : fastVisit (leafCols 8 bank) [8,4] ⟨2092470,[107666,1329444]⟩ b8 = true := by decide +kernel

theorem n145 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b7 = true := join_live n143 n144

theorem n146 : fastVisit (leafCols 8 bank) [7,4] ⟨2083108,[98304,786432]⟩ b7 = true := by decide +kernel

theorem n147 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b6 = true := join_live n145 n146

theorem n148 : fastVisit (leafCols 8 bank) [6,4] ⟨2083108,[98304,1853732]⟩ b6 = true := by decide +kernel

theorem n149 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b5 = true := join_live n147 n148

theorem n150 : fastVisit (leafCols 8 bank) [5,4] ⟨2059702,[74898,149796]⟩ b5 = true := by decide +kernel

theorem n151 : fastVisit (leafCols 8 bank) [4] ⟨1984804,[1984804]⟩ b4 = true := join_live n149 n150

theorem n152 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b3 = true := join_live n135 n151

theorem n153 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [] ⟨0,[]⟩ b35 = true := by decide +kernel

theorem n154 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [4] ⟨1984804,[1984804]⟩ b35 = true := by decide +kernel

theorem n155 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [] ⟨0,[]⟩ b34 = true := join_live n153 n154

theorem n156 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [3] ⟨1835008,[1835008]⟩ b34 = true := by decide +kernel

theorem n157 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [] ⟨0,[]⟩ b33 = true := join_live n155 n156

theorem n158 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [2] ⟨599186,[599186]⟩ b33 = true := by decide +kernel

theorem n159 : fastVisit (leafFrame 8 [3] ⟨1835008,[1835008]⟩) [] ⟨0,[]⟩ b32 = true := join_live n157 n158

end GainFinite.F8
