import PEqualNP.ThreeGateGain.FiniteB04

namespace GainFinite.F4
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n0 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b13 = true := by decide +kernel

theorem n1 : fastVisit (leafCols 4 bank) [13] ⟨19660,[19660]⟩ b13 = true := by decide +kernel

theorem n2 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b12 = true := join_live n0 n1

theorem n3 : fastVisit (leafCols 4 bank) [12] ⟨2184,[2184]⟩ b12 = true := by decide +kernel

theorem n4 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b11 = true := join_live n2 n3

theorem n5 : fastVisit (leafCols 4 bank) [11] ⟨28912,[28912]⟩ b11 = true := by decide +kernel

theorem n6 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b10 = true := join_live n4 n5

theorem n7 : fastVisit (leafCols 4 bank) [10] ⟨8352,[8352]⟩ b10 = true := by decide +kernel

theorem n8 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b9 = true := join_live n6 n7

theorem n9 : fastVisit (leafCols 4 bank) [9] ⟨16576,[16576]⟩ b10 = true := by decide +kernel

theorem n10 : fastVisit (leafCols 4 bank) [10,9] ⟨24800,[8224,16448]⟩ b10 = true := by decide +kernel

theorem n11 : fastVisit (leafCols 4 bank) [9] ⟨16576,[16576]⟩ b9 = true := join_live n9 n10

theorem n12 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b8 = true := join_live n8 n11

theorem n13 : fastVisit (leafCols 4 bank) [8] ⟨128,[128]⟩ b8 = true := by decide +kernel

theorem n14 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b7 = true := join_live n12 n13

theorem n15 : fastVisit (leafCols 4 bank) [7] ⟨32512,[32512]⟩ b7 = true := by decide +kernel

theorem n16 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b6 = true := join_live n14 n15

theorem n17 : fastVisit (leafCols 4 bank) [6] ⟨10752,[10752]⟩ b10 = true := by decide +kernel

theorem n18 : fastVisit (leafCols 4 bank) [10,6] ⟨10912,[160,2560]⟩ b10 = true := by decide +kernel

theorem n19 : fastVisit (leafCols 4 bank) [6] ⟨10752,[10752]⟩ b9 = true := join_live n17 n18

theorem n20 : fastVisit (leafCols 4 bank) [9,6] ⟨27328,[16576,10752]⟩ b10 = true := by decide +kernel

theorem n21 : fastVisit (leafCols 4 bank) [10,9,6] ⟨27360,[32,16448,2560]⟩ b10 = true := by decide +kernel

theorem n22 : fastVisit (leafCols 4 bank) [9,6] ⟨27328,[16576,10752]⟩ b9 = true := join_live n20 n21

theorem n23 : fastVisit (leafCols 4 bank) [6] ⟨10752,[10752]⟩ b8 = true := join_live n19 n22

theorem n24 : fastVisit (leafCols 4 bank) [8,6] ⟨10880,[128,10752]⟩ b8 = true := by decide +kernel

theorem n25 : fastVisit (leafCols 4 bank) [6] ⟨10752,[10752]⟩ b7 = true := join_live n23 n24

theorem n26 : fastVisit (leafCols 4 bank) [6] ⟨10752,[10752]⟩ b6 = true := join_dead n25 (by decide +kernel)

theorem n27 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b5 = true := join_live n16 n26

theorem n28 : fastVisit (leafCols 4 bank) [5] ⟨19456,[19456]⟩ b10 = true := by decide +kernel

theorem n29 : fastVisit (leafCols 4 bank) [10,5] ⟨27808,[8352,19456]⟩ b10 = true := by decide +kernel

theorem n30 : fastVisit (leafCols 4 bank) [5] ⟨19456,[19456]⟩ b9 = true := join_live n28 n29

theorem n31 : fastVisit (leafCols 4 bank) [9,5] ⟨19648,[192,3072]⟩ b10 = true := by decide +kernel

theorem n32 : fastVisit (leafCols 4 bank) [10,9,5] ⟨27872,[8224,64,3072]⟩ b10 = true := by decide +kernel

theorem n33 : fastVisit (leafCols 4 bank) [9,5] ⟨19648,[192,3072]⟩ b9 = true := join_live n31 n32

theorem n34 : fastVisit (leafCols 4 bank) [5] ⟨19456,[19456]⟩ b8 = true := join_live n30 n33

theorem n35 : fastVisit (leafCols 4 bank) [8,5] ⟨19584,[128,19456]⟩ b8 = true := by decide +kernel

theorem n36 : fastVisit (leafCols 4 bank) [5] ⟨19456,[19456]⟩ b7 = true := join_live n34 n35

theorem n37 : fastVisit (leafCols 4 bank) [5] ⟨19456,[19456]⟩ b6 = true := join_dead n36 (by decide +kernel)

theorem n38 : fastVisit (leafCols 4 bank) [6,5] ⟨28160,[8704,17408]⟩ b10 = true := by decide +kernel

theorem n39 : fastVisit (leafCols 4 bank) [10,6,5] ⟨28320,[160,512,17408]⟩ b10 = true := by decide +kernel

theorem n40 : fastVisit (leafCols 4 bank) [6,5] ⟨28160,[8704,17408]⟩ b9 = true := join_live n38 n39

theorem n41 : fastVisit (leafCols 4 bank) [9,6,5] ⟨28352,[192,8704,1024]⟩ b10 = true := by decide +kernel

theorem n42 : fastVisit (leafCols 4 bank) [10,9,6,5] ⟨28384,[32,64,512,1024]⟩ b12 = true := by decide +kernel

theorem n43 : fastVisit (leafCols 4 bank) [12,10,9,6,5] ⟨28392,[8,32,64,512,1024]⟩ b12 = true := by decide +kernel

theorem n44 : fastVisit (leafCols 4 bank) [10,9,6,5] ⟨28384,[32,64,512,1024]⟩ b11 = true := join_live n42 n43

theorem n45 : fastVisit (leafCols 4 bank) [10,9,6,5] ⟨28384,[32,64,512,1024]⟩ b10 = true := join_dead n44 (by decide +kernel)

theorem n46 : fastVisit (leafCols 4 bank) [9,6,5] ⟨28352,[192,8704,1024]⟩ b9 = true := join_live n41 n45

theorem n47 : fastVisit (leafCols 4 bank) [6,5] ⟨28160,[8704,17408]⟩ b8 = true := join_live n40 n46

theorem n48 : fastVisit (leafCols 4 bank) [8,6,5] ⟨28288,[128,8704,17408]⟩ b8 = true := by decide +kernel

theorem n49 : fastVisit (leafCols 4 bank) [6,5] ⟨28160,[8704,17408]⟩ b7 = true := join_live n47 n48

theorem n50 : fastVisit (leafCols 4 bank) [6,5] ⟨28160,[8704,17408]⟩ b6 = true := join_dead n49 (by decide +kernel)

theorem n51 : fastVisit (leafCols 4 bank) [5] ⟨19456,[19456]⟩ b5 = true := join_live n37 n50

theorem n52 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b4 = true := join_live n27 n51

theorem n53 : fastVisit (leafCols 4 bank) [4] ⟨2048,[2048]⟩ b10 = true := by decide +kernel

theorem n54 : fastVisit (leafCols 4 bank) [10,4] ⟨10400,[8352,2048]⟩ b10 = true := by decide +kernel

theorem n55 : fastVisit (leafCols 4 bank) [4] ⟨2048,[2048]⟩ b9 = true := join_live n53 n54

theorem n56 : fastVisit (leafCols 4 bank) [9,4] ⟨18624,[16576,2048]⟩ b9 = true := by decide +kernel

theorem n57 : fastVisit (leafCols 4 bank) [4] ⟨2048,[2048]⟩ b8 = true := join_live n55 n56

theorem n58 : fastVisit (leafFrame 4 [8,4] ⟨2176,[128,2048]⟩) [] ⟨0,[]⟩ b16 = true := by decide +kernel

theorem n59 : fastVisit (leafFrame 4 [8,4] ⟨2176,[128,2048]⟩) [1] ⟨16384,[16384]⟩ b16 = true := by decide +kernel

theorem n60 : fastVisit (leafFrame 4 [8,4] ⟨2176,[128,2048]⟩) [] ⟨0,[]⟩ b15 = true := join_live n58 n59

theorem n61 : fastVisit (leafCols 4 bank) [8,4] ⟨2176,[128,2048]⟩ b14 = true := enterColumns 4 bank [8,4] ⟨2176,[128,2048]⟩ b14 b15 (by decide +kernel) (by decide +kernel) n60

theorem n62 : fastVisit (leafCols 4 bank) [8,4] ⟨2176,[128,2048]⟩ b13 = true := join_dead n61 (by decide +kernel)

theorem n63 : fastVisit (leafCols 4 bank) [8,4] ⟨2176,[128,2048]⟩ b12 = true := join_dead n62 (by decide +kernel)

theorem n64 : fastVisit (leafCols 4 bank) [8,4] ⟨2176,[128,2048]⟩ b11 = true := join_dead n63 (by decide +kernel)

theorem n65 : fastVisit (leafCols 4 bank) [8,4] ⟨2176,[128,2048]⟩ b10 = true := join_dead n64 (by decide +kernel)

theorem n66 : fastVisit (leafCols 4 bank) [8,4] ⟨2176,[128,2048]⟩ b9 = true := join_dead n65 (by decide +kernel)

theorem n67 : fastVisit (leafCols 4 bank) [8,4] ⟨2176,[128,2048]⟩ b8 = true := join_dead n66 (by decide +kernel)

theorem n68 : fastVisit (leafCols 4 bank) [4] ⟨2048,[2048]⟩ b7 = true := join_live n57 n67

theorem n69 : fastVisit (leafCols 4 bank) [4] ⟨2048,[2048]⟩ b6 = true := join_dead n68 (by decide +kernel)

theorem n70 : fastVisit (leafCols 4 bank) [4] ⟨2048,[2048]⟩ b5 = true := join_dead n69 (by decide +kernel)

theorem n71 : fastVisit (leafCols 4 bank) [4] ⟨2048,[2048]⟩ b4 = true := join_dead n70 (by decide +kernel)

theorem n72 : fastVisit (leafCols 4 bank) [] ⟨0,[]⟩ b3 = true := join_live n52 n71

theorem n73 : fastVisit (leafCols 4 bank) [3] ⟨28672,[28672]⟩ b10 = true := by decide +kernel

theorem n74 : fastVisit (leafCols 4 bank) [10,3] ⟨28832,[160,20480]⟩ b10 = true := by decide +kernel

theorem n75 : fastVisit (leafCols 4 bank) [3] ⟨28672,[28672]⟩ b9 = true := join_live n73 n74

theorem n76 : fastVisit (leafCols 4 bank) [9,3] ⟨28864,[192,12288]⟩ b10 = true := by decide +kernel

theorem n77 : fastVisit (leafCols 4 bank) [10,9,3] ⟨28896,[32,64,4096]⟩ b10 = true := by decide +kernel

theorem n78 : fastVisit (leafCols 4 bank) [9,3] ⟨28864,[192,12288]⟩ b9 = true := join_live n76 n77

theorem n79 : fastVisit (leafCols 4 bank) [3] ⟨28672,[28672]⟩ b8 = true := join_live n75 n78

end GainFinite.F4
