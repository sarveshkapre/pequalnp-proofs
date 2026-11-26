import PEqualNP.ThreeGateGain.FiniteB10

namespace GainFinite.F10
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n0 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b12 = true := by decide +kernel

theorem n1 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [12] ⟨134185408,[134185408]⟩ b12 = true := by decide +kernel

theorem n2 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b11 = true := join_live n0 n1

theorem n3 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [11] ⟨134030482,[134030482]⟩ b11 = true := by decide +kernel

theorem n4 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b10 = true := join_live n2 n3

theorem n5 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [10] ⟨134105380,[134105380]⟩ b10 = true := by decide +kernel

theorem n6 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b9 = true := join_live n4 n5

theorem n7 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [9] ⟨133955584,[133955584]⟩ b9 = true := by decide +kernel

theorem n8 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b8 = true := join_live n6 n7

theorem n9 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [8] ⟨48854202,[48854202]⟩ b8 = true := by decide +kernel

theorem n10 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b7 = true := join_live n8 n9

theorem n11 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [7] ⟨82999612,[82999612]⟩ b7 = true := by decide +kernel

theorem n12 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b6 = true := join_live n10 n11

theorem n13 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [6] ⟨14708792,[14708792]⟩ b6 = true := by decide +kernel

theorem n14 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b5 = true := join_live n12 n13

theorem n15 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [5] ⟨122398162,[122398162]⟩ b7 = true := by decide +kernel

theorem n16 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [7,5] ⟨133955070,[11556908,50955458]⟩ b7 = true := by decide +kernel

theorem n17 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [5] ⟨122398162,[122398162]⟩ b6 = true := join_live n15 n16

theorem n18 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [6,5] ⟨132904442,[10506280,118195650]⟩ b6 = true := by decide +kernel

theorem n19 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [5] ⟨122398162,[122398162]⟩ b5 = true := join_live n17 n18

theorem n20 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b4 = true := join_live n14 n19

theorem n21 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [4] ⟨127125988,[127125988]⟩ b7 = true := by decide +kernel

theorem n22 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [7,4] ⟨133429756,[6303768,50430144]⟩ b7 = true := by decide +kernel

theorem n23 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [4] ⟨127125988,[127125988]⟩ b6 = true := join_live n21 n22

theorem n24 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [6,4] ⟨133429756,[6303768,118720964]⟩ b6 = true := by decide +kernel

theorem n25 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [4] ⟨127125988,[127125988]⟩ b5 = true := join_live n23 n24

theorem n26 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [5,4] ⟨131853814,[4727826,9455652]⟩ b5 = true := by decide +kernel

theorem n27 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [4] ⟨127125988,[127125988]⟩ b4 = true := join_live n25 n26

theorem n28 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b3 = true := join_live n20 n27

theorem n29 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [3] ⟨117670336,[117670336]⟩ b7 = true := by decide +kernel

theorem n30 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [7,3] ⟨133429756,[15759420,50430144]⟩ b7 = true := by decide +kernel

theorem n31 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [3] ⟨117670336,[117670336]⟩ b6 = true := join_live n29 n30

theorem n32 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [6,3] ⟨132379128,[14708792,117670336]⟩ b6 = true := by decide +kernel

theorem n33 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [3] ⟨117670336,[117670336]⟩ b5 = true := join_live n31 n32

theorem n34 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [3] ⟨117670336,[117670336]⟩ b4 = true := join_dead n33 (by decide +kernel)

theorem n35 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [3] ⟨117670336,[117670336]⟩ b3 = true := join_dead n34 (by decide +kernel)

theorem n36 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b2 = true := join_live n28 n35

theorem n37 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [2] ⟨38347922,[38347922]⟩ b6 = true := by decide +kernel

theorem n38 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [6,2] ⟨48854202,[10506280,34145410]⟩ b6 = true := by decide +kernel

theorem n39 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [2] ⟨38347922,[38347922]⟩ b5 = true := join_live n37 n38

theorem n40 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [2] ⟨38347922,[38347922]⟩ b4 = true := join_dead n39 (by decide +kernel)

theorem n41 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [4,2] ⟨131853814,[93505892,4727826]⟩ b4 = true := by decide +kernel

theorem n42 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [2] ⟨38347922,[38347922]⟩ b3 = true := join_live n40 n41

theorem n43 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [3,2] ⟨122398162,[84050240,4727826]⟩ b3 = true := by decide +kernel

theorem n44 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [2] ⟨38347922,[38347922]⟩ b2 = true := join_live n42 n43

theorem n45 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b1 = true := join_live n36 n44

theorem n46 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [1] ⟨76695844,[76695844]⟩ b6 = true := by decide +kernel

theorem n47 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [6,1] ⟨82999612,[6303768,68290820]⟩ b6 = true := by decide +kernel

theorem n48 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [1] ⟨76695844,[76695844]⟩ b5 = true := join_live n46 n47

theorem n49 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [5,1] ⟨131853814,[55157970,9455652]⟩ b5 = true := by decide +kernel

theorem n50 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [1] ⟨76695844,[76695844]⟩ b4 = true := join_live n48 n49

theorem n51 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [1] ⟨76695844,[76695844]⟩ b3 = true := join_dead n50 (by decide +kernel)

theorem n52 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [3,1] ⟨127125988,[50430144,9455652]⟩ b3 = true := by decide +kernel

theorem n53 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [1] ⟨76695844,[76695844]⟩ b2 = true := join_live n51 n52

theorem n54 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [2,1] ⟨115043766,[38347922,76695844]⟩ b2 = true := by decide +kernel

theorem n55 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [1] ⟨76695844,[76695844]⟩ b1 = true := join_live n53 n54

theorem n56 : fastVisit (leafFrame 10 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b0 = true := join_live n45 n55

theorem n57 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b26 = true := enterColumns 10 bank [] ⟨0,[]⟩ b26 b0 (by decide +kernel) (by decide +kernel) n56

theorem n58 : fastVisit (leafCols 10 bank) [26] ⟨49020602,[49020602]⟩ b26 = true := by decide +kernel

theorem n59 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b25 = true := join_live n57 n58

theorem n60 : fastVisit (leafCols 10 bank) [25] ⟨83099452,[83099452]⟩ b25 = true := by decide +kernel

theorem n61 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b24 = true := join_live n59 n60

theorem n62 : fastVisit (leafCols 10 bank) [24] ⟨14941752,[14941752]⟩ b24 = true := by decide +kernel

theorem n63 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b23 = true := join_live n61 n62

theorem n64 : fastVisit (leafCols 10 bank) [23] ⟨122421202,[122421202]⟩ b23 = true := by decide +kernel

theorem n65 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b22 = true := join_live n63 n64

theorem n66 : fastVisit (leafCols 10 bank) [22] ⟨127139812,[127139812]⟩ b22 = true := by decide +kernel

theorem n67 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b21 = true := join_live n65 n66

theorem n68 : fastVisit (leafCols 10 bank) [21] ⟨117702592,[117702592]⟩ b21 = true := by decide +kernel

theorem n69 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b20 = true := join_live n67 n68

theorem n70 : fastVisit (leafCols 10 bank) [20] ⟨38534802,[38534802]⟩ b20 = true := by decide +kernel

theorem n71 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b19 = true := join_live n69 n70

theorem n72 : fastVisit (leafCols 10 bank) [19] ⟨76807972,[76807972]⟩ b19 = true := by decide +kernel

theorem n73 : fastVisit (leafCols 10 bank) [] ⟨0,[]⟩ b18 = true := join_live n71 n72

theorem n74 : fastVisit (leafFrame 10 [18] ⟨261632,[261632]⟩) [] ⟨0,[]⟩ b30 = true := by decide +kernel

theorem n75 : fastVisit (leafFrame 10 [18] ⟨261632,[261632]⟩) [3] ⟨117670336,[117670336]⟩ b30 = true := by decide +kernel

theorem n76 : fastVisit (leafFrame 10 [18] ⟨261632,[261632]⟩) [] ⟨0,[]⟩ b29 = true := join_live n74 n75

theorem n77 : fastVisit (leafFrame 10 [18] ⟨261632,[261632]⟩) [2] ⟨38347922,[38347922]⟩ b29 = true := by decide +kernel

theorem n78 : fastVisit (leafFrame 10 [18] ⟨261632,[261632]⟩) [] ⟨0,[]⟩ b28 = true := join_live n76 n77

theorem n79 : fastVisit (leafFrame 10 [18] ⟨261632,[261632]⟩) [1] ⟨76695844,[76695844]⟩ b28 = true := by decide +kernel

end GainFinite.F10
