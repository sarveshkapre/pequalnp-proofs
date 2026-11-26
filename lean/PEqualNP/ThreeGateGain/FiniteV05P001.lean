import PEqualNP.ThreeGateGain.FiniteV05P000

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n80 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b13 = true := join_live n78 n79

theorem n81 : fastVisit (leafCols 5 bank) [13,8] ⟨521096,[197512,61440]⟩ b13 = true := by decide +kernel

theorem n82 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b12 = true := join_live n80 n81

theorem n83 : fastVisit (leafCols 5 bank) [12,8] ⟨457002,[133418,307200]⟩ b12 = true := by decide +kernel

theorem n84 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b11 = true := join_live n82 n83

theorem n85 : fastVisit (leafCols 5 bank) [11,8] ⟨324172,[588,24576]⟩ b11 = true := by decide +kernel

theorem n86 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b10 = true := join_live n84 n85

theorem n87 : fastVisit (leafFrame 5 [10,8] ⟨323592,[8,323584]⟩) [] ⟨0,[]⟩ b24 = true := by decide +kernel

theorem n88 : fastVisit (leafFrame 5 [10,8] ⟨323592,[8,323584]⟩) [1] ⟨299008,[299008]⟩ b24 = true := by decide +kernel

theorem n89 : fastVisit (leafFrame 5 [10,8] ⟨323592,[8,323584]⟩) [] ⟨0,[]⟩ b23 = true := join_live n87 n88

theorem n90 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b18 = true := enterColumns 5 bank [10,8] ⟨323592,[8,323584]⟩ b18 b23 (by decide +kernel) (by decide +kernel) n89

theorem n91 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b17 = true := join_dead n90 (by decide +kernel)

theorem n92 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b16 = true := join_dead n91 (by decide +kernel)

theorem n93 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b15 = true := join_dead n92 (by decide +kernel)

theorem n94 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b14 = true := join_dead n93 (by decide +kernel)

theorem n95 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b13 = true := join_dead n94 (by decide +kernel)

theorem n96 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b12 = true := join_dead n95 (by decide +kernel)

theorem n97 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b11 = true := join_dead n96 (by decide +kernel)

theorem n98 : fastVisit (leafCols 5 bank) [10,8] ⟨323592,[8,323584]⟩ b10 = true := join_dead n97 (by decide +kernel)

theorem n99 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b9 = true := join_live n86 n98

theorem n100 : fastVisit (leafFrame 5 [9,8] ⟨456704,[133120,266240]⟩) [] ⟨0,[]⟩ b26 = true := by decide +kernel

theorem n101 : fastVisit (leafFrame 5 [9,8] ⟨456704,[133120,266240]⟩) [1] ⟨299008,[299008]⟩ b26 = true := by decide +kernel

theorem n102 : fastVisit (leafFrame 5 [9,8] ⟨456704,[133120,266240]⟩) [] ⟨0,[]⟩ b25 = true := join_live n100 n101

theorem n103 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b18 = true := enterColumns 5 bank [9,8] ⟨456704,[133120,266240]⟩ b18 b25 (by decide +kernel) (by decide +kernel) n102

theorem n104 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b17 = true := join_dead n103 (by decide +kernel)

theorem n105 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b16 = true := join_dead n104 (by decide +kernel)

theorem n106 : fastVisit (leafCols 5 bank) [16,9,8] ⟨456824,[120,133120,266240]⟩ b16 = true := by decide +kernel

theorem n107 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b15 = true := join_live n105 n106

theorem n108 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b14 = true := join_dead n107 (by decide +kernel)

theorem n109 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b13 = true := join_dead n108 (by decide +kernel)

theorem n110 : fastVisit (leafCols 5 bank) [13,9,8] ⟨523144,[66440,2048,4096]⟩ b13 = true := by decide +kernel

theorem n111 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b12 = true := join_live n109 n110

theorem n112 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b11 = true := join_dead n111 (by decide +kernel)

theorem n113 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b10 = true := join_dead n112 (by decide +kernel)

theorem n114 : fastVisit (leafFrame 5 [10,9,8] ⟨456712,[8,133120,266240]⟩) [] ⟨0,[]⟩ b29 = true := by decide +kernel

theorem n115 : fastVisit (leafFrame 5 [10,9,8] ⟨456712,[8,133120,266240]⟩) [2] ⟨149504,[149504]⟩ b29 = true := by decide +kernel

theorem n116 : fastVisit (leafFrame 5 [10,9,8] ⟨456712,[8,133120,266240]⟩) [] ⟨0,[]⟩ b28 = true := join_live n114 n115

theorem n117 : fastVisit (leafFrame 5 [10,9,8] ⟨456712,[8,133120,266240]⟩) [1] ⟨299008,[299008]⟩ b29 = true := by decide +kernel

theorem n118 : fastVisit (leafFrame 5 [10,9,8] ⟨456712,[8,133120,266240]⟩) [2,1] ⟨448512,[149504,299008]⟩ b29 = true := by decide +kernel

theorem n119 : fastVisit (leafFrame 5 [10,9,8] ⟨456712,[8,133120,266240]⟩) [1] ⟨299008,[299008]⟩ b28 = true := join_live n117 n118

theorem n120 : fastVisit (leafFrame 5 [10,9,8] ⟨456712,[8,133120,266240]⟩) [] ⟨0,[]⟩ b27 = true := join_live n116 n119

theorem n121 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b18 = true := enterColumns 5 bank [10,9,8] ⟨456712,[8,133120,266240]⟩ b18 b27 (by decide +kernel) (by decide +kernel) n120

theorem n122 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b17 = true := join_dead n121 (by decide +kernel)

theorem n123 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b16 = true := join_dead n122 (by decide +kernel)

theorem n124 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b15 = true := join_dead n123 (by decide +kernel)

theorem n125 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b14 = true := join_dead n124 (by decide +kernel)

theorem n126 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b13 = true := join_dead n125 (by decide +kernel)

theorem n127 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b12 = true := join_dead n126 (by decide +kernel)

theorem n128 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b11 = true := join_dead n127 (by decide +kernel)

theorem n129 : fastVisit (leafCols 5 bank) [10,9,8] ⟨456712,[8,133120,266240]⟩ b10 = true := join_dead n128 (by decide +kernel)

theorem n130 : fastVisit (leafCols 5 bank) [9,8] ⟨456704,[133120,266240]⟩ b9 = true := join_live n113 n129

theorem n131 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b8 = true := join_live n99 n130

theorem n132 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b7 = true := join_live n73 n131

theorem n133 : fastVisit (leafFrame 5 [7] ⟨57344,[57344]⟩) [] ⟨0,[]⟩ b32 = true := by decide +kernel

theorem n134 : fastVisit (leafFrame 5 [7] ⟨57344,[57344]⟩) [2] ⟨149504,[149504]⟩ b32 = true := by decide +kernel

theorem n135 : fastVisit (leafFrame 5 [7] ⟨57344,[57344]⟩) [] ⟨0,[]⟩ b31 = true := join_live n133 n134

theorem n136 : fastVisit (leafFrame 5 [7] ⟨57344,[57344]⟩) [1] ⟨299008,[299008]⟩ b31 = true := by decide +kernel

theorem n137 : fastVisit (leafFrame 5 [7] ⟨57344,[57344]⟩) [] ⟨0,[]⟩ b30 = true := join_live n135 n136

theorem n138 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b18 = true := enterColumns 5 bank [7] ⟨57344,[57344]⟩ b18 b30 (by decide +kernel) (by decide +kernel) n137

theorem n139 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b17 = true := join_dead n138 (by decide +kernel)

theorem n140 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b16 = true := join_dead n139 (by decide +kernel)

theorem n141 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b15 = true := join_dead n140 (by decide +kernel)

theorem n142 : fastVisit (leafCols 5 bank) [15,7] ⟨519082,[461738,40960]⟩ b15 = true := by decide +kernel

theorem n143 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b14 = true := join_live n141 n142

theorem n144 : fastVisit (leafCols 5 bank) [14,7] ⟨521164,[463820,24576]⟩ b14 = true := by decide +kernel

theorem n145 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b13 = true := join_live n143 n144

theorem n146 : fastVisit (leafCols 5 bank) [13,7] ⟨517000,[459656,57344]⟩ b13 = true := by decide +kernel

theorem n147 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b12 = true := join_live n145 n146

theorem n148 : fastVisit (leafCols 5 bank) [12,7] ⟨190762,[133418,40960]⟩ b12 = true := by decide +kernel

theorem n149 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b11 = true := join_live n147 n148

theorem n150 : fastVisit (leafCols 5 bank) [11,7] ⟨324172,[266828,24576]⟩ b11 = true := by decide +kernel

theorem n151 : fastVisit (leafCols 5 bank) [7] ⟨57344,[57344]⟩ b10 = true := join_live n149 n150

theorem n152 : fastVisit (leafFrame 5 [10,7] ⟨57352,[8,57344]⟩) [] ⟨0,[]⟩ b35 = true := by decide +kernel

theorem n153 : fastVisit (leafFrame 5 [10,7] ⟨57352,[8,57344]⟩) [2] ⟨149504,[149504]⟩ b35 = true := by decide +kernel

theorem n154 : fastVisit (leafFrame 5 [10,7] ⟨57352,[8,57344]⟩) [] ⟨0,[]⟩ b34 = true := join_live n152 n153

theorem n155 : fastVisit (leafFrame 5 [10,7] ⟨57352,[8,57344]⟩) [1] ⟨299008,[299008]⟩ b35 = true := by decide +kernel

theorem n156 : fastVisit (leafFrame 5 [10,7] ⟨57352,[8,57344]⟩) [2,1] ⟨448512,[149504,299008]⟩ b35 = true := by decide +kernel

theorem n157 : fastVisit (leafFrame 5 [10,7] ⟨57352,[8,57344]⟩) [1] ⟨299008,[299008]⟩ b34 = true := join_live n155 n156

theorem n158 : fastVisit (leafFrame 5 [10,7] ⟨57352,[8,57344]⟩) [] ⟨0,[]⟩ b33 = true := join_live n154 n157

theorem n159 : fastVisit (leafCols 5 bank) [10,7] ⟨57352,[8,57344]⟩ b18 = true := enterColumns 5 bank [10,7] ⟨57352,[8,57344]⟩ b18 b33 (by decide +kernel) (by decide +kernel) n158

end GainFinite.F5
