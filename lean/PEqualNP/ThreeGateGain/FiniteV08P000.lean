import PEqualNP.ThreeGateGain.FiniteB08

namespace GainFinite.F8
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n0 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b7 = true := by decide +kernel

theorem n1 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [7] ⟨1296676,[1296676]⟩ b7 = true := by decide +kernel

theorem n2 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b6 = true := join_live n0 n1

theorem n3 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [6] ⟨229376,[229376]⟩ b6 = true := by decide +kernel

theorem n4 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b5 = true := join_live n2 n3

theorem n5 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [5] ⟨1909906,[1909906]⟩ b5 = true := by decide +kernel

theorem n6 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b4 = true := join_live n4 n5

theorem n7 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [4] ⟨1984804,[1984804]⟩ b4 = true := by decide +kernel

theorem n8 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b3 = true := join_live n6 n7

theorem n9 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [3] ⟨1835008,[1835008]⟩ b3 = true := by decide +kernel

theorem n10 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b2 = true := join_live n8 n9

theorem n11 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [2] ⟨599186,[599186]⟩ b2 = true := by decide +kernel

theorem n12 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b1 = true := join_live n10 n11

theorem n13 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [1] ⟨1198372,[1198372]⟩ b1 = true := by decide +kernel

theorem n14 : fastVisit (leafFrame 8 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b0 = true := join_live n12 n13

theorem n15 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b20 = true := enterColumns 8 bank [] ⟨0,[]⟩ b20 b0 (by decide +kernel) (by decide +kernel) n14

theorem n16 : fastVisit (leafCols 8 bank) [20] ⟨765626,[765626]⟩ b20 = true := by decide +kernel

theorem n17 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b19 = true := join_live n15 n16

theorem n18 : fastVisit (leafCols 8 bank) [19] ⟨1298236,[1298236]⟩ b19 = true := by decide +kernel

theorem n19 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b18 = true := join_live n17 n18

theorem n20 : fastVisit (leafCols 8 bank) [18] ⟨233016,[233016]⟩ b18 = true := by decide +kernel

theorem n21 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b17 = true := join_live n19 n20

theorem n22 : fastVisit (leafCols 8 bank) [17] ⟨1912786,[1912786]⟩ b17 = true := by decide +kernel

theorem n23 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b16 = true := join_live n21 n22

theorem n24 : fastVisit (leafCols 8 bank) [16] ⟨1986532,[1986532]⟩ b16 = true := by decide +kernel

theorem n25 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b15 = true := join_live n23 n24

theorem n26 : fastVisit (leafCols 8 bank) [15] ⟨1839040,[1839040]⟩ b15 = true := by decide +kernel

theorem n27 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b14 = true := join_live n25 n26

theorem n28 : fastVisit (leafCols 8 bank) [14] ⟨601746,[601746]⟩ b14 = true := by decide +kernel

theorem n29 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b13 = true := join_live n27 n28

theorem n30 : fastVisit (leafCols 8 bank) [13] ⟨1199908,[1199908]⟩ b13 = true := by decide +kernel

theorem n31 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b12 = true := join_live n29 n30

theorem n32 : fastVisit (leafFrame 8 [12] ⟨3584,[3584]⟩) [] ⟨0,[]⟩ b24 = true := by decide +kernel

theorem n33 : fastVisit (leafFrame 8 [12] ⟨3584,[3584]⟩) [3] ⟨1835008,[1835008]⟩ b24 = true := by decide +kernel

theorem n34 : fastVisit (leafFrame 8 [12] ⟨3584,[3584]⟩) [] ⟨0,[]⟩ b23 = true := join_live n32 n33

theorem n35 : fastVisit (leafFrame 8 [12] ⟨3584,[3584]⟩) [2] ⟨599186,[599186]⟩ b23 = true := by decide +kernel

theorem n36 : fastVisit (leafFrame 8 [12] ⟨3584,[3584]⟩) [] ⟨0,[]⟩ b22 = true := join_live n34 n35

theorem n37 : fastVisit (leafFrame 8 [12] ⟨3584,[3584]⟩) [1] ⟨1198372,[1198372]⟩ b22 = true := by decide +kernel

theorem n38 : fastVisit (leafFrame 8 [12] ⟨3584,[3584]⟩) [] ⟨0,[]⟩ b21 = true := join_live n36 n37

theorem n39 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b20 = true := enterColumns 8 bank [12] ⟨3584,[3584]⟩ b20 b21 (by decide +kernel) (by decide +kernel) n38

theorem n40 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b19 = true := join_dead n39 (by decide +kernel)

theorem n41 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b18 = true := join_dead n40 (by decide +kernel)

theorem n42 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b17 = true := join_dead n41 (by decide +kernel)

theorem n43 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b16 = true := join_dead n42 (by decide +kernel)

theorem n44 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b15 = true := join_dead n43 (by decide +kernel)

theorem n45 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b14 = true := join_dead n44 (by decide +kernel)

theorem n46 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b13 = true := join_dead n45 (by decide +kernel)

theorem n47 : fastVisit (leafCols 8 bank) [12] ⟨3584,[3584]⟩ b12 = true := join_dead n46 (by decide +kernel)

theorem n48 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b11 = true := join_live n31 n47

theorem n49 : fastVisit (leafCols 8 bank) [11] ⟨2094226,[2094226]⟩ b11 = true := by decide +kernel

theorem n50 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b10 = true := join_live n48 n49

theorem n51 : fastVisit (leafCols 8 bank) [10] ⟨2095396,[2095396]⟩ b10 = true := by decide +kernel

theorem n52 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b9 = true := join_live n50 n51

theorem n53 : fastVisit (leafCols 8 bank) [9] ⟨2093056,[2093056]⟩ b13 = true := by decide +kernel

theorem n54 : fastVisit (leafCols 8 bank) [13,9] ⟨2096932,[3876,897024]⟩ b13 = true := by decide +kernel

theorem n55 : fastVisit (leafCols 8 bank) [9] ⟨2093056,[2093056]⟩ b12 = true := join_live n53 n54

theorem n56 : fastVisit (leafCols 8 bank) [12,9] ⟨2096640,[3584,2093056]⟩ b12 = true := by decide +kernel

theorem n57 : fastVisit (leafCols 8 bank) [9] ⟨2093056,[2093056]⟩ b11 = true := join_live n55 n56

theorem n58 : fastVisit (leafCols 8 bank) [9] ⟨2093056,[2093056]⟩ b10 = true := join_dead n57 (by decide +kernel)

theorem n59 : fastVisit (leafCols 8 bank) [9] ⟨2093056,[2093056]⟩ b9 = true := join_dead n58 (by decide +kernel)

theorem n60 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b8 = true := join_live n52 n59

theorem n61 : fastVisit (leafCols 8 bank) [8] ⟨763026,[763026]⟩ b12 = true := by decide +kernel

theorem n62 : fastVisit (leafCols 8 bank) [12,8] ⟨765586,[2560,762002]⟩ b12 = true := by decide +kernel

theorem n63 : fastVisit (leafCols 8 bank) [8] ⟨763026,[763026]⟩ b11 = true := join_live n61 n62

theorem n64 : fastVisit (leafCols 8 bank) [8] ⟨763026,[763026]⟩ b10 = true := join_dead n63 (by decide +kernel)

theorem n65 : fastVisit (leafCols 8 bank) [10,8] ⟨2096566,[1333540,1170]⟩ b10 = true := by decide +kernel

theorem n66 : fastVisit (leafCols 8 bank) [8] ⟨763026,[763026]⟩ b9 = true := join_live n64 n65

theorem n67 : fastVisit (leafCols 8 bank) [9,8] ⟨2094226,[1331200,1170]⟩ b9 = true := by decide +kernel

theorem n68 : fastVisit (leafCols 8 bank) [8] ⟨763026,[763026]⟩ b8 = true := join_live n66 n67

theorem n69 : fastVisit (leafCols 8 bank) [] ⟨0,[]⟩ b7 = true := join_live n60 n68

theorem n70 : fastVisit (leafCols 8 bank) [7] ⟨1296676,[1296676]⟩ b12 = true := by decide +kernel

theorem n71 : fastVisit (leafCols 8 bank) [12,7] ⟨1298212,[1536,1294628]⟩ b12 = true := by decide +kernel

theorem n72 : fastVisit (leafCols 8 bank) [7] ⟨1296676,[1296676]⟩ b11 = true := join_live n70 n71

theorem n73 : fastVisit (leafCols 8 bank) [11,7] ⟨2096566,[799890,2340]⟩ b11 = true := by decide +kernel

theorem n74 : fastVisit (leafCols 8 bank) [7] ⟨1296676,[1296676]⟩ b10 = true := join_live n72 n73

theorem n75 : fastVisit (leafCols 8 bank) [7] ⟨1296676,[1296676]⟩ b9 = true := join_dead n74 (by decide +kernel)

theorem n76 : fastVisit (leafCols 8 bank) [9,7] ⟨2095396,[798720,2340]⟩ b9 = true := by decide +kernel

theorem n77 : fastVisit (leafCols 8 bank) [7] ⟨1296676,[1296676]⟩ b8 = true := join_live n75 n76

theorem n78 : fastVisit (leafCols 8 bank) [8,7] ⟨1830326,[533650,1067300]⟩ b8 = true := by decide +kernel

theorem n79 : fastVisit (leafCols 8 bank) [7] ⟨1296676,[1296676]⟩ b7 = true := join_live n77 n78

end GainFinite.F8
