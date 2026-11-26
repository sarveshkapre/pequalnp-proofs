import PEqualNP.ThreeGateGain.FiniteB05

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n0 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b5 = true := by decide +kernel

theorem n1 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [5] ⟨495616,[495616]⟩ b5 = true := by decide +kernel

theorem n2 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b4 = true := join_live n0 n1

theorem n3 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [4] ⟨458752,[458752]⟩ b4 = true := by decide +kernel

theorem n4 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b3 = true := join_live n2 n3

theorem n5 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [3] ⟨523264,[523264]⟩ b3 = true := by decide +kernel

theorem n6 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b2 = true := join_live n4 n5

theorem n7 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [2] ⟨149504,[149504]⟩ b2 = true := by decide +kernel

theorem n8 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b1 = true := join_live n6 n7

theorem n9 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [1] ⟨299008,[299008]⟩ b1 = true := by decide +kernel

theorem n10 : fastVisit (leafFrame 5 [] ⟨0,[]⟩) [] ⟨0,[]⟩ b0 = true := join_live n8 n9

theorem n11 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b18 = true := enterColumns 5 bank [] ⟨0,[]⟩ b18 b0 (by decide +kernel) (by decide +kernel) n10

theorem n12 : fastVisit (leafCols 5 bank) [18] ⟨190842,[190842]⟩ b18 = true := by decide +kernel

theorem n13 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b17 = true := join_live n11 n12

theorem n14 : fastVisit (leafCols 5 bank) [17] ⟨324220,[324220]⟩ b17 = true := by decide +kernel

theorem n15 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b16 = true := join_live n13 n14

theorem n16 : fastVisit (leafCols 5 bank) [16] ⟨57464,[57464]⟩ b16 = true := by decide +kernel

theorem n17 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b15 = true := join_live n15 n16

theorem n18 : fastVisit (leafCols 5 bank) [15] ⟨478122,[478122]⟩ b15 = true := by decide +kernel

theorem n19 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b14 = true := join_live n17 n18

theorem n20 : fastVisit (leafCols 5 bank) [14] ⟨496588,[496588]⟩ b14 = true := by decide +kernel

theorem n21 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b13 = true := join_live n19 n20

theorem n22 : fastVisit (leafCols 5 bank) [13] ⟨459656,[459656]⟩ b13 = true := by decide +kernel

theorem n23 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b12 = true := join_live n21 n22

theorem n24 : fastVisit (leafCols 5 bank) [12] ⟨149802,[149802]⟩ b12 = true := by decide +kernel

theorem n25 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b11 = true := join_live n23 n24

theorem n26 : fastVisit (leafCols 5 bank) [11] ⟨299596,[299596]⟩ b11 = true := by decide +kernel

theorem n27 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b10 = true := join_live n25 n26

theorem n28 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [] ⟨0,[]⟩ b5 = true := by decide +kernel

theorem n29 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [5] ⟨495616,[495616]⟩ b5 = true := by decide +kernel

theorem n30 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [] ⟨0,[]⟩ b4 = true := join_live n28 n29

theorem n31 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [4] ⟨458752,[458752]⟩ b4 = true := by decide +kernel

theorem n32 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [] ⟨0,[]⟩ b3 = true := join_live n30 n31

theorem n33 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [2] ⟨149504,[149504]⟩ b3 = true := by decide +kernel

theorem n34 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [] ⟨0,[]⟩ b20 = true := join_live n32 n33

theorem n35 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [1] ⟨299008,[299008]⟩ b20 = true := by decide +kernel

theorem n36 : fastVisit (leafFrame 5 [10] ⟨8,[8]⟩) [] ⟨0,[]⟩ b19 = true := join_live n34 n35

theorem n37 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b18 = true := enterColumns 5 bank [10] ⟨8,[8]⟩ b18 b19 (by decide +kernel) (by decide +kernel) n36

theorem n38 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b17 = true := join_dead n37 (by decide +kernel)

theorem n39 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b16 = true := join_dead n38 (by decide +kernel)

theorem n40 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b15 = true := join_dead n39 (by decide +kernel)

theorem n41 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b14 = true := join_dead n40 (by decide +kernel)

theorem n42 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b13 = true := join_dead n41 (by decide +kernel)

theorem n43 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b12 = true := join_dead n42 (by decide +kernel)

theorem n44 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b11 = true := join_dead n43 (by decide +kernel)

theorem n45 : fastVisit (leafCols 5 bank) [10] ⟨8,[8]⟩ b10 = true := join_dead n44 (by decide +kernel)

theorem n46 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b9 = true := join_live n27 n45

theorem n47 : fastVisit (leafCols 5 bank) [9] ⟨190464,[190464]⟩ b16 = true := by decide +kernel

theorem n48 : fastVisit (leafCols 5 bank) [16,9] ⟨190584,[120,133120]⟩ b16 = true := by decide +kernel

theorem n49 : fastVisit (leafCols 5 bank) [9] ⟨190464,[190464]⟩ b15 = true := join_live n47 n48

theorem n50 : fastVisit (leafCols 5 bank) [15,9] ⟨519082,[328618,40960]⟩ b15 = true := by decide +kernel

theorem n51 : fastVisit (leafCols 5 bank) [9] ⟨190464,[190464]⟩ b14 = true := join_live n49 n50

theorem n52 : fastVisit (leafCols 5 bank) [14,9] ⟨523212,[332748,26624]⟩ b14 = true := by decide +kernel

theorem n53 : fastVisit (leafCols 5 bank) [9] ⟨190464,[190464]⟩ b13 = true := join_live n51 n52

theorem n54 : fastVisit (leafCols 5 bank) [13,9] ⟨519048,[328584,59392]⟩ b13 = true := by decide +kernel

theorem n55 : fastVisit (leafCols 5 bank) [9] ⟨190464,[190464]⟩ b12 = true := join_live n53 n54

theorem n56 : fastVisit (leafCols 5 bank) [12,9] ⟨190762,[298,40960]⟩ b12 = true := by decide +kernel

theorem n57 : fastVisit (leafCols 5 bank) [9] ⟨190464,[190464]⟩ b11 = true := join_live n55 n56

theorem n58 : fastVisit (leafCols 5 bank) [11,9] ⟨457292,[266828,157696]⟩ b11 = true := by decide +kernel

theorem n59 : fastVisit (leafCols 5 bank) [9] ⟨190464,[190464]⟩ b10 = true := join_live n57 n58

theorem n60 : fastVisit (leafFrame 5 [10,9] ⟨190472,[8,190464]⟩) [] ⟨0,[]⟩ b22 = true := by decide +kernel

theorem n61 : fastVisit (leafFrame 5 [10,9] ⟨190472,[8,190464]⟩) [1] ⟨299008,[299008]⟩ b22 = true := by decide +kernel

theorem n62 : fastVisit (leafFrame 5 [10,9] ⟨190472,[8,190464]⟩) [] ⟨0,[]⟩ b21 = true := join_live n60 n61

theorem n63 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b18 = true := enterColumns 5 bank [10,9] ⟨190472,[8,190464]⟩ b18 b21 (by decide +kernel) (by decide +kernel) n62

theorem n64 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b17 = true := join_dead n63 (by decide +kernel)

theorem n65 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b16 = true := join_dead n64 (by decide +kernel)

theorem n66 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b15 = true := join_dead n65 (by decide +kernel)

theorem n67 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b14 = true := join_dead n66 (by decide +kernel)

theorem n68 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b13 = true := join_dead n67 (by decide +kernel)

theorem n69 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b12 = true := join_dead n68 (by decide +kernel)

theorem n70 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b11 = true := join_dead n69 (by decide +kernel)

theorem n71 : fastVisit (leafCols 5 bank) [10,9] ⟨190472,[8,190464]⟩ b10 = true := join_dead n70 (by decide +kernel)

theorem n72 : fastVisit (leafCols 5 bank) [9] ⟨190464,[190464]⟩ b9 = true := join_live n59 n71

theorem n73 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b8 = true := join_live n46 n72

theorem n74 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b16 = true := by decide +kernel

theorem n75 : fastVisit (leafCols 5 bank) [16,8] ⟨323704,[120,266240]⟩ b16 = true := by decide +kernel

theorem n76 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b15 = true := join_live n74 n75

theorem n77 : fastVisit (leafCols 5 bank) [15,8] ⟨523178,[199594,45056]⟩ b15 = true := by decide +kernel

theorem n78 : fastVisit (leafCols 5 bank) [8] ⟨323584,[323584]⟩ b14 = true := join_live n76 n77

theorem n79 : fastVisit (leafCols 5 bank) [14,8] ⟨521164,[197580,24576]⟩ b14 = true := by decide +kernel

end GainFinite.F5
