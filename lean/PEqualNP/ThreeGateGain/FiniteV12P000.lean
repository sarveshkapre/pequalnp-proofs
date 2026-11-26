import PEqualNP.ThreeGateGain.FiniteB12

namespace GainFinite.F12
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n0 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b11 = true := by decide +kernel

theorem n1 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [11] ⟨33522176,[33522176]⟩ b11 = true := by decide +kernel

theorem n2 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b10 = true := join_live n0 n1

theorem n3 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [10] ⟨33488896,[33488896]⟩ b10 = true := by decide +kernel

theorem n4 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b9 = true := join_live n2 n3

theorem n5 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [9] ⟨12208506,[12208506]⟩ b9 = true := by decide +kernel

theorem n6 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b8 = true := join_live n4 n5

theorem n7 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [8] ⟨20746876,[20746876]⟩ b8 = true := by decide +kernel

theorem n8 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b7 = true := join_live n6 n7

theorem n9 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [7] ⟨3670136,[3670136]⟩ b7 = true := by decide +kernel

theorem n10 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b6 = true := join_live n8 n9

theorem n11 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [6] ⟨30598016,[30598016]⟩ b8 = true := by decide +kernel

theorem n12 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [8,6] ⟨33485820,[2887804,12738944]⟩ b8 = true := by decide +kernel

theorem n13 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [6] ⟨30598016,[30598016]⟩ b7 = true := join_live n11 n12

theorem n14 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [7,6] ⟨33219576,[2621560,29549440]⟩ b7 = true := by decide +kernel

theorem n15 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [6] ⟨30598016,[30598016]⟩ b6 = true := join_live n13 n14

theorem n16 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b5 = true := join_live n10 n15

theorem n17 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [5] ⟨31777664,[31777664]⟩ b8 = true := by decide +kernel

theorem n18 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [8,5] ⟨33354748,[1577084,12607872]⟩ b8 = true := by decide +kernel

theorem n19 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [5] ⟨31777664,[31777664]⟩ b7 = true := join_live n17 n18

theorem n20 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [7,5] ⟨33350648,[1572984,29680512]⟩ b7 = true := by decide +kernel

theorem n21 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [5] ⟨31777664,[31777664]⟩ b6 = true := join_live n19 n20

theorem n22 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [6,5] ⟨32957312,[1179648,2359296]⟩ b6 = true := by decide +kernel

theorem n23 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [5] ⟨31777664,[31777664]⟩ b5 = true := join_live n21 n22

theorem n24 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b4 = true := join_live n16 n23

theorem n25 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [4] ⟨29418368,[29418368]⟩ b7 = true := by decide +kernel

theorem n26 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [7,4] ⟨33088504,[3670136,29418368]⟩ b7 = true := by decide +kernel

theorem n27 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [4] ⟨29418368,[29418368]⟩ b6 = true := join_live n25 n26

theorem n28 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [4] ⟨29418368,[29418368]⟩ b5 = true := join_dead n27 (by decide +kernel)

theorem n29 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [4] ⟨29418368,[29418368]⟩ b4 = true := join_dead n28 (by decide +kernel)

theorem n30 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b3 = true := join_live n24 n29

theorem n31 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [3] ⟨33547136,[33547136]⟩ b3 = true := by decide +kernel

theorem n32 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b2 = true := join_live n30 n31

theorem n33 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [2] ⟨9584896,[9584896]⟩ b2 = true := by decide +kernel

theorem n34 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b1 = true := join_live n32 n33

theorem n35 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [1] ⟨19169792,[19169792]⟩ b1 = true := by decide +kernel

theorem n36 : fastVisit (leafFrame 12 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b0 = true := join_live n34 n35

theorem n37 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b24 = true := enterColumns 12 bank [] ⟨0,[]⟩ b24 b0 (by decide +kernel) (by decide +kernel) n36

theorem n38 : fastVisit (leafCols 12 bank) [24] ⟨12254586,[12254586]⟩ b24 = true := by decide +kernel

theorem n39 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b23 = true := join_live n37 n38

theorem n40 : fastVisit (leafCols 12 bank) [23] ⟨20774524,[20774524]⟩ b23 = true := by decide +kernel

theorem n41 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b22 = true := join_live n39 n40

theorem n42 : fastVisit (leafCols 12 bank) [22] ⟨3734648,[3734648]⟩ b22 = true := by decide +kernel

theorem n43 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b21 = true := join_live n41 n42

theorem n44 : fastVisit (leafCols 12 bank) [21] ⟨30605226,[30605226]⟩ b21 = true := by decide +kernel

theorem n45 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b20 = true := join_live n43 n44

theorem n46 : fastVisit (leafCols 12 bank) [20] ⟨31784908,[31784908]⟩ b20 = true := by decide +kernel

theorem n47 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b19 = true := join_live n45 n46

theorem n48 : fastVisit (leafCols 12 bank) [19] ⟨29425544,[29425544]⟩ b19 = true := by decide +kernel

theorem n49 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b18 = true := join_live n47 n48

theorem n50 : fastVisit (leafCols 12 bank) [18] ⟨9633066,[9633066]⟩ b18 = true := by decide +kernel

theorem n51 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b17 = true := join_live n49 n50

theorem n52 : fastVisit (leafCols 12 bank) [17] ⟨19201612,[19201612]⟩ b17 = true := by decide +kernel

theorem n53 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b16 = true := join_live n51 n52

theorem n54 : fastVisit (leafFrame 12 [16] ⟨64520,[64520]⟩) [] ⟨0,[]⟩ b28 = true := by decide +kernel

theorem n55 : fastVisit (leafFrame 12 [16] ⟨64520,[64520]⟩) [4] ⟨29418368,[29418368]⟩ b28 = true := by decide +kernel

theorem n56 : fastVisit (leafFrame 12 [16] ⟨64520,[64520]⟩) [] ⟨0,[]⟩ b27 = true := join_live n54 n55

theorem n57 : fastVisit (leafFrame 12 [16] ⟨64520,[64520]⟩) [2] ⟨9584896,[9584896]⟩ b27 = true := by decide +kernel

theorem n58 : fastVisit (leafFrame 12 [16] ⟨64520,[64520]⟩) [] ⟨0,[]⟩ b26 = true := join_live n56 n57

theorem n59 : fastVisit (leafFrame 12 [16] ⟨64520,[64520]⟩) [1] ⟨19169792,[19169792]⟩ b26 = true := by decide +kernel

theorem n60 : fastVisit (leafFrame 12 [16] ⟨64520,[64520]⟩) [] ⟨0,[]⟩ b25 = true := join_live n58 n59

theorem n61 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b24 = true := enterColumns 12 bank [16] ⟨64520,[64520]⟩ b24 b25 (by decide +kernel) (by decide +kernel) n60

theorem n62 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b23 = true := join_dead n61 (by decide +kernel)

theorem n63 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b22 = true := join_dead n62 (by decide +kernel)

theorem n64 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b21 = true := join_dead n63 (by decide +kernel)

theorem n65 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b20 = true := join_dead n64 (by decide +kernel)

theorem n66 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b19 = true := join_dead n65 (by decide +kernel)

theorem n67 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b18 = true := join_dead n66 (by decide +kernel)

theorem n68 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b17 = true := join_dead n67 (by decide +kernel)

theorem n69 : fastVisit (leafCols 12 bank) [16] ⟨64520,[64520]⟩ b16 = true := join_dead n68 (by decide +kernel)

theorem n70 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b15 = true := join_live n53 n69

theorem n71 : fastVisit (leafCols 12 bank) [15] ⟨33507706,[33507706]⟩ b15 = true := by decide +kernel

theorem n72 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b14 = true := join_live n70 n71

theorem n73 : fastVisit (leafCols 12 bank) [14] ⟨33526396,[33526396]⟩ b14 = true := by decide +kernel

theorem n74 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b13 = true := join_live n72 n73

theorem n75 : fastVisit (leafCols 12 bank) [13] ⟨33489016,[33489016]⟩ b13 = true := by decide +kernel

theorem n76 : fastVisit (leafCols 12 bank) [] ⟨0,[]⟩ b12 = true := join_live n74 n75

theorem n77 : fastVisit (leafCols 12 bank) [12] ⟨33505536,[33505536]⟩ b18 = true := by decide +kernel

theorem n78 : fastVisit (leafCols 12 bank) [18,12] ⟨33553706,[48170,23920640]⟩ b18 = true := by decide +kernel

theorem n79 : fastVisit (leafCols 12 bank) [12] ⟨33505536,[33505536]⟩ b17 = true := join_live n77 n78

end GainFinite.F12
