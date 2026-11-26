import PEqualNP.ThreeGateGain.FiniteV05P008

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n720 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b18 = true := enterColumns 5 bank [8,2] ⟨456704,[307200,133120]⟩ b18 b25 (by decide +kernel) (by decide +kernel) n719

theorem n721 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b17 = true := join_dead n720 (by decide +kernel)

theorem n722 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b16 = true := join_dead n721 (by decide +kernel)

theorem n723 : fastVisit (leafCols 5 bank) [16,8,2] ⟨456824,[120,266240,133120]⟩ b16 = true := by decide +kernel

theorem n724 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b15 = true := join_live n722 n723

theorem n725 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b14 = true := join_dead n724 (by decide +kernel)

theorem n726 : fastVisit (leafCols 5 bank) [14,8,2] ⟨523212,[66508,8192,2048]⟩ b14 = true := by decide +kernel

theorem n727 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b13 = true := join_live n725 n726

theorem n728 : fastVisit (leafCols 5 bank) [13,8,2] ⟨523144,[66440,45056,2048]⟩ b13 = true := by decide +kernel

theorem n729 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b12 = true := join_live n727 n728

theorem n730 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b11 = true := join_dead n729 (by decide +kernel)

theorem n731 : fastVisit (leafCols 5 bank) [11,8,2] ⟨457292,[588,8192,133120]⟩ b11 = true := by decide +kernel

theorem n732 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b10 = true := join_live n730 n731

theorem n733 : fastVisit (leafFrame 5 [10,8,2] ⟨456712,[8,307200,133120]⟩) [] ⟨0,[]⟩ b29 = true := by decide +kernel

theorem n734 : fastVisit (leafFrame 5 [10,8,2] ⟨456712,[8,307200,133120]⟩) [2] ⟨149504,[149504]⟩ b29 = true := by decide +kernel

theorem n735 : fastVisit (leafFrame 5 [10,8,2] ⟨456712,[8,307200,133120]⟩) [] ⟨0,[]⟩ b28 = true := join_live n733 n734

theorem n736 : fastVisit (leafFrame 5 [10,8,2] ⟨456712,[8,307200,133120]⟩) [1] ⟨299008,[299008]⟩ b29 = true := by decide +kernel

theorem n737 : fastVisit (leafFrame 5 [10,8,2] ⟨456712,[8,307200,133120]⟩) [2,1] ⟨448512,[149504,299008]⟩ b29 = true := by decide +kernel

theorem n738 : fastVisit (leafFrame 5 [10,8,2] ⟨456712,[8,307200,133120]⟩) [1] ⟨299008,[299008]⟩ b28 = true := join_live n736 n737

theorem n739 : fastVisit (leafFrame 5 [10,8,2] ⟨456712,[8,307200,133120]⟩) [] ⟨0,[]⟩ b27 = true := join_live n735 n738

theorem n740 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b18 = true := enterColumns 5 bank [10,8,2] ⟨456712,[8,307200,133120]⟩ b18 b27 (by decide +kernel) (by decide +kernel) n739

theorem n741 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b17 = true := join_dead n740 (by decide +kernel)

theorem n742 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b16 = true := join_dead n741 (by decide +kernel)

theorem n743 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b15 = true := join_dead n742 (by decide +kernel)

theorem n744 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b14 = true := join_dead n743 (by decide +kernel)

theorem n745 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b13 = true := join_dead n744 (by decide +kernel)

theorem n746 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b12 = true := join_dead n745 (by decide +kernel)

theorem n747 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b11 = true := join_dead n746 (by decide +kernel)

theorem n748 : fastVisit (leafCols 5 bank) [10,8,2] ⟨456712,[8,307200,133120]⟩ b10 = true := join_dead n747 (by decide +kernel)

theorem n749 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b9 = true := join_live n732 n748

theorem n750 : fastVisit (leafCols 5 bank) [8,2] ⟨456704,[307200,133120]⟩ b8 = true := join_dead n749 (by decide +kernel)

theorem n751 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b7 = true := join_live n716 n750

theorem n752 : fastVisit (leafFrame 5 [7,2] ⟨190464,[40960,133120]⟩) [] ⟨0,[]⟩ b82 = true := by decide +kernel

theorem n753 : fastVisit (leafFrame 5 [7,2] ⟨190464,[40960,133120]⟩) [1] ⟨299008,[299008]⟩ b82 = true := by decide +kernel

theorem n754 : fastVisit (leafFrame 5 [7,2] ⟨190464,[40960,133120]⟩) [] ⟨0,[]⟩ b81 = true := join_live n752 n753

theorem n755 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b18 = true := enterColumns 5 bank [7,2] ⟨190464,[40960,133120]⟩ b18 b81 (by decide +kernel) (by decide +kernel) n754

theorem n756 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b17 = true := join_dead n755 (by decide +kernel)

theorem n757 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b16 = true := join_dead n756 (by decide +kernel)

theorem n758 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b15 = true := join_dead n757 (by decide +kernel)

theorem n759 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b14 = true := join_dead n758 (by decide +kernel)

theorem n760 : fastVisit (leafCols 5 bank) [14,7,2] ⟨523212,[332748,8192,2048]⟩ b14 = true := by decide +kernel

theorem n761 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b13 = true := join_live n759 n760

theorem n762 : fastVisit (leafCols 5 bank) [13,7,2] ⟨519048,[328584,40960,2048]⟩ b13 = true := by decide +kernel

theorem n763 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b12 = true := join_live n761 n762

theorem n764 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b11 = true := join_dead n763 (by decide +kernel)

theorem n765 : fastVisit (leafCols 5 bank) [11,7,2] ⟨457292,[266828,8192,133120]⟩ b11 = true := by decide +kernel

theorem n766 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b10 = true := join_live n764 n765

theorem n767 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [] ⟨0,[]⟩ b84 = true := by decide +kernel

theorem n768 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [4] ⟨458752,[458752]⟩ b84 = true := by decide +kernel

theorem n769 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [] ⟨0,[]⟩ b83 = true := join_live n767 n768

theorem n770 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [2] ⟨149504,[149504]⟩ b83 = true := by decide +kernel

theorem n771 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [] ⟨0,[]⟩ b22 = true := join_live n769 n770

theorem n772 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [1] ⟨299008,[299008]⟩ b84 = true := by decide +kernel

theorem n773 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [4,1] ⟨495616,[196608,36864]⟩ b84 = true := by decide +kernel

theorem n774 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [1] ⟨299008,[299008]⟩ b83 = true := join_live n772 n773

theorem n775 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [2,1] ⟨448512,[149504,299008]⟩ b83 = true := by decide +kernel

theorem n776 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [1] ⟨299008,[299008]⟩ b22 = true := join_live n774 n775

theorem n777 : fastVisit (leafFrame 5 [10,7,2] ⟨190472,[8,40960,133120]⟩) [] ⟨0,[]⟩ b21 = true := join_live n771 n776

theorem n778 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b18 = true := enterColumns 5 bank [10,7,2] ⟨190472,[8,40960,133120]⟩ b18 b21 (by decide +kernel) (by decide +kernel) n777

theorem n779 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b17 = true := join_dead n778 (by decide +kernel)

theorem n780 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b16 = true := join_dead n779 (by decide +kernel)

theorem n781 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b15 = true := join_dead n780 (by decide +kernel)

theorem n782 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b14 = true := join_dead n781 (by decide +kernel)

theorem n783 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b13 = true := join_dead n782 (by decide +kernel)

theorem n784 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b12 = true := join_dead n783 (by decide +kernel)

theorem n785 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b11 = true := join_dead n784 (by decide +kernel)

theorem n786 : fastVisit (leafCols 5 bank) [10,7,2] ⟨190472,[8,40960,133120]⟩ b10 = true := join_dead n785 (by decide +kernel)

theorem n787 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b9 = true := join_live n766 n786

theorem n788 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b8 = true := join_dead n787 (by decide +kernel)

theorem n789 : fastVisit (leafCols 5 bank) [7,2] ⟨190464,[40960,133120]⟩ b7 = true := join_dead n788 (by decide +kernel)

theorem n790 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b6 = true := join_live n751 n789

theorem n791 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b5 = true := join_dead n790 (by decide +kernel)

theorem n792 : fastVisit (leafFrame 5 [5,2] ⟨514048,[364544,18432]⟩) [] ⟨0,[]⟩ b54 = true := by decide +kernel

theorem n793 : fastVisit (leafFrame 5 [5,2] ⟨514048,[364544,18432]⟩) [1] ⟨299008,[299008]⟩ b54 = true := by decide +kernel

theorem n794 : fastVisit (leafFrame 5 [5,2] ⟨514048,[364544,18432]⟩) [] ⟨0,[]⟩ b53 = true := join_live n792 n793

theorem n795 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b18 = true := enterColumns 5 bank [5,2] ⟨514048,[364544,18432]⟩ b18 b53 (by decide +kernel) (by decide +kernel) n794

theorem n796 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b17 = true := join_dead n795 (by decide +kernel)

theorem n797 : fastVisit (leafCols 5 bank) [17,5,2] ⟨522876,[8828,65536,2048]⟩ b17 = true := by decide +kernel

theorem n798 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b16 = true := join_live n796 n797

theorem n799 : fastVisit (leafCols 5 bank) [16,5,2] ⟨522360,[8312,331776,2048]⟩ b16 = true := by decide +kernel

end GainFinite.F5
