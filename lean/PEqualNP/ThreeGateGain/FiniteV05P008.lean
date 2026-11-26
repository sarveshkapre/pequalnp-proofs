import PEqualNP.ThreeGateGain.FiniteV05P007

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n640 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b12 = true := join_dead n639 (by decide +kernel)

theorem n641 : fastVisit (leafCols 5 bank) [12,7,4] ⟨518442,[2346,40960,327680]⟩ b12 = true := by decide +kernel

theorem n642 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b11 = true := join_live n640 n641

theorem n643 : fastVisit (leafCols 5 bank) [11,7,4] ⟨520780,[4684,24576,196608]⟩ b11 = true := by decide +kernel

theorem n644 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b10 = true := join_live n642 n643

theorem n645 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [] ⟨0,[]⟩ b75 = true := by decide +kernel

theorem n646 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [5] ⟨495616,[495616]⟩ b75 = true := by decide +kernel

theorem n647 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [] ⟨0,[]⟩ b74 = true := join_live n645 n646

theorem n648 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [4] ⟨458752,[458752]⟩ b74 = true := by decide +kernel

theorem n649 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [] ⟨0,[]⟩ b73 = true := join_live n647 n648

theorem n650 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [2] ⟨149504,[149504]⟩ b73 = true := by decide +kernel

theorem n651 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [] ⟨0,[]⟩ b72 = true := join_live n649 n650

theorem n652 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [1] ⟨299008,[299008]⟩ b73 = true := by decide +kernel

theorem n653 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [2,1] ⟨448512,[149504,299008]⟩ b73 = true := by decide +kernel

theorem n654 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [1] ⟨299008,[299008]⟩ b72 = true := join_live n652 n653

theorem n655 : fastVisit (leafFrame 5 [10,7,4] ⟨516104,[8,57344,458752]⟩) [] ⟨0,[]⟩ b71 = true := join_live n651 n654

theorem n656 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b18 = true := enterColumns 5 bank [10,7,4] ⟨516104,[8,57344,458752]⟩ b18 b71 (by decide +kernel) (by decide +kernel) n655

theorem n657 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b17 = true := join_dead n656 (by decide +kernel)

theorem n658 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b16 = true := join_dead n657 (by decide +kernel)

theorem n659 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b15 = true := join_dead n658 (by decide +kernel)

theorem n660 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b14 = true := join_dead n659 (by decide +kernel)

theorem n661 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b13 = true := join_dead n660 (by decide +kernel)

theorem n662 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b12 = true := join_dead n661 (by decide +kernel)

theorem n663 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b11 = true := join_dead n662 (by decide +kernel)

theorem n664 : fastVisit (leafCols 5 bank) [10,7,4] ⟨516104,[8,57344,458752]⟩ b10 = true := join_dead n663 (by decide +kernel)

theorem n665 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b9 = true := join_live n644 n664

theorem n666 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b8 = true := join_dead n665 (by decide +kernel)

theorem n667 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b7 = true := join_dead n666 (by decide +kernel)

theorem n668 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b6 = true := join_live n630 n667

theorem n669 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b5 = true := join_dead n668 (by decide +kernel)

theorem n670 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b4 = true := join_dead n669 (by decide +kernel)

theorem n671 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b3 = true := join_live n491 n670

theorem n672 : fastVisit (leafCols 5 bank) [3] ⟨523264,[523264]⟩ b10 = true := by decide +kernel

theorem n673 : fastVisit (leafCols 5 bank) [10,3] ⟨523272,[8,523264]⟩ b10 = true := by decide +kernel

theorem n674 : fastVisit (leafCols 5 bank) [3] ⟨523264,[523264]⟩ b9 = true := join_live n672 n673

theorem n675 : fastVisit (leafCols 5 bank) [3] ⟨523264,[523264]⟩ b8 = true := join_dead n674 (by decide +kernel)

theorem n676 : fastVisit (leafCols 5 bank) [3] ⟨523264,[523264]⟩ b7 = true := join_dead n675 (by decide +kernel)

theorem n677 : fastVisit (leafCols 5 bank) [3] ⟨523264,[523264]⟩ b6 = true := join_dead n676 (by decide +kernel)

theorem n678 : fastVisit (leafCols 5 bank) [3] ⟨523264,[523264]⟩ b5 = true := join_dead n677 (by decide +kernel)

theorem n679 : fastVisit (leafCols 5 bank) [3] ⟨523264,[523264]⟩ b4 = true := join_dead n678 (by decide +kernel)

theorem n680 : fastVisit (leafCols 5 bank) [3] ⟨523264,[523264]⟩ b3 = true := join_dead n679 (by decide +kernel)

theorem n681 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b2 = true := join_live n671 n680

theorem n682 : fastVisit (leafFrame 5 [2] ⟨149504,[149504]⟩) [] ⟨0,[]⟩ b77 = true := by decide +kernel

theorem n683 : fastVisit (leafFrame 5 [2] ⟨149504,[149504]⟩) [1] ⟨299008,[299008]⟩ b77 = true := by decide +kernel

theorem n684 : fastVisit (leafFrame 5 [2] ⟨149504,[149504]⟩) [] ⟨0,[]⟩ b76 = true := join_live n682 n683

theorem n685 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b18 = true := enterColumns 5 bank [2] ⟨149504,[149504]⟩ b18 b76 (by decide +kernel) (by decide +kernel) n684

theorem n686 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b17 = true := join_dead n685 (by decide +kernel)

theorem n687 : fastVisit (leafCols 5 bank) [17,2] ⟨457340,[307836,133120]⟩ b17 = true := by decide +kernel

theorem n688 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b16 = true := join_live n686 n687

theorem n689 : fastVisit (leafCols 5 bank) [16,2] ⟨190584,[41080,133120]⟩ b16 = true := by decide +kernel

theorem n690 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b15 = true := join_live n688 n689

theorem n691 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b14 = true := join_dead n690 (by decide +kernel)

theorem n692 : fastVisit (leafCols 5 bank) [14,2] ⟨515020,[365516,18432]⟩ b14 = true := by decide +kernel

theorem n693 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b13 = true := join_live n691 n692

theorem n694 : fastVisit (leafCols 5 bank) [13,2] ⟨478088,[328584,18432]⟩ b13 = true := by decide +kernel

theorem n695 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b12 = true := join_live n693 n694

theorem n696 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b11 = true := join_dead n695 (by decide +kernel)

theorem n697 : fastVisit (leafCols 5 bank) [11,2] ⟨449100,[299596,149504]⟩ b11 = true := by decide +kernel

theorem n698 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b10 = true := join_live n696 n697

theorem n699 : fastVisit (leafFrame 5 [10,2] ⟨149512,[8,149504]⟩) [] ⟨0,[]⟩ b80 = true := by decide +kernel

theorem n700 : fastVisit (leafFrame 5 [10,2] ⟨149512,[8,149504]⟩) [2] ⟨149504,[149504]⟩ b80 = true := by decide +kernel

theorem n701 : fastVisit (leafFrame 5 [10,2] ⟨149512,[8,149504]⟩) [] ⟨0,[]⟩ b79 = true := join_live n699 n700

theorem n702 : fastVisit (leafFrame 5 [10,2] ⟨149512,[8,149504]⟩) [1] ⟨299008,[299008]⟩ b80 = true := by decide +kernel

theorem n703 : fastVisit (leafFrame 5 [10,2] ⟨149512,[8,149504]⟩) [2,1] ⟨448512,[149504,299008]⟩ b80 = true := by decide +kernel

theorem n704 : fastVisit (leafFrame 5 [10,2] ⟨149512,[8,149504]⟩) [1] ⟨299008,[299008]⟩ b79 = true := join_live n702 n703

theorem n705 : fastVisit (leafFrame 5 [10,2] ⟨149512,[8,149504]⟩) [] ⟨0,[]⟩ b78 = true := join_live n701 n704

theorem n706 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b18 = true := enterColumns 5 bank [10,2] ⟨149512,[8,149504]⟩ b18 b78 (by decide +kernel) (by decide +kernel) n705

theorem n707 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b17 = true := join_dead n706 (by decide +kernel)

theorem n708 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b16 = true := join_dead n707 (by decide +kernel)

theorem n709 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b15 = true := join_dead n708 (by decide +kernel)

theorem n710 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b14 = true := join_dead n709 (by decide +kernel)

theorem n711 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b13 = true := join_dead n710 (by decide +kernel)

theorem n712 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b12 = true := join_dead n711 (by decide +kernel)

theorem n713 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b11 = true := join_dead n712 (by decide +kernel)

theorem n714 : fastVisit (leafCols 5 bank) [10,2] ⟨149512,[8,149504]⟩ b10 = true := join_dead n713 (by decide +kernel)

theorem n715 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b9 = true := join_live n698 n714

theorem n716 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b8 = true := join_dead n715 (by decide +kernel)

theorem n717 : fastVisit (leafFrame 5 [8,2] ⟨456704,[307200,133120]⟩) [] ⟨0,[]⟩ b26 = true := by decide +kernel

theorem n718 : fastVisit (leafFrame 5 [8,2] ⟨456704,[307200,133120]⟩) [1] ⟨299008,[299008]⟩ b26 = true := by decide +kernel

theorem n719 : fastVisit (leafFrame 5 [8,2] ⟨456704,[307200,133120]⟩) [] ⟨0,[]⟩ b25 = true := join_live n717 n718

end GainFinite.F5
