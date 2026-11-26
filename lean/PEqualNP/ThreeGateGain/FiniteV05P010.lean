import PEqualNP.ThreeGateGain.FiniteV05P009

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n800 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b15 = true := join_live n798 n799

theorem n801 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b14 = true := join_dead n800 (by decide +kernel)

theorem n802 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b13 = true := join_dead n801 (by decide +kernel)

theorem n803 : fastVisit (leafCols 5 bank) [13,5,2] ⟨514952,[904,36864,18432]⟩ b13 = true := by decide +kernel

theorem n804 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b12 = true := join_live n802 n803

theorem n805 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b11 = true := join_dead n804 (by decide +kernel)

theorem n806 : fastVisit (leafCols 5 bank) [11,5,2] ⟨514636,[588,65536,18432]⟩ b11 = true := by decide +kernel

theorem n807 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b10 = true := join_live n805 n806

theorem n808 : fastVisit (leafFrame 5 [10,5,2] ⟨514056,[8,364544,18432]⟩) [] ⟨0,[]⟩ b57 = true := by decide +kernel

theorem n809 : fastVisit (leafFrame 5 [10,5,2] ⟨514056,[8,364544,18432]⟩) [2] ⟨149504,[149504]⟩ b57 = true := by decide +kernel

theorem n810 : fastVisit (leafFrame 5 [10,5,2] ⟨514056,[8,364544,18432]⟩) [] ⟨0,[]⟩ b56 = true := join_live n808 n809

theorem n811 : fastVisit (leafFrame 5 [10,5,2] ⟨514056,[8,364544,18432]⟩) [1] ⟨299008,[299008]⟩ b57 = true := by decide +kernel

theorem n812 : fastVisit (leafFrame 5 [10,5,2] ⟨514056,[8,364544,18432]⟩) [2,1] ⟨448512,[149504,299008]⟩ b57 = true := by decide +kernel

theorem n813 : fastVisit (leafFrame 5 [10,5,2] ⟨514056,[8,364544,18432]⟩) [1] ⟨299008,[299008]⟩ b56 = true := join_live n811 n812

theorem n814 : fastVisit (leafFrame 5 [10,5,2] ⟨514056,[8,364544,18432]⟩) [] ⟨0,[]⟩ b55 = true := join_live n810 n813

theorem n815 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b18 = true := enterColumns 5 bank [10,5,2] ⟨514056,[8,364544,18432]⟩ b18 b55 (by decide +kernel) (by decide +kernel) n814

theorem n816 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b17 = true := join_dead n815 (by decide +kernel)

theorem n817 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b16 = true := join_dead n816 (by decide +kernel)

theorem n818 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b15 = true := join_dead n817 (by decide +kernel)

theorem n819 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b14 = true := join_dead n818 (by decide +kernel)

theorem n820 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b13 = true := join_dead n819 (by decide +kernel)

theorem n821 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b12 = true := join_dead n820 (by decide +kernel)

theorem n822 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b11 = true := join_dead n821 (by decide +kernel)

theorem n823 : fastVisit (leafCols 5 bank) [10,5,2] ⟨514056,[8,364544,18432]⟩ b10 = true := join_dead n822 (by decide +kernel)

theorem n824 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b9 = true := join_live n807 n823

theorem n825 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b8 = true := join_dead n824 (by decide +kernel)

theorem n826 : fastVisit (leafFrame 5 [8,5,2] ⟨522240,[8192,65536,2048]⟩) [] ⟨0,[]⟩ b60 = true := by decide +kernel

theorem n827 : fastVisit (leafFrame 5 [8,5,2] ⟨522240,[8192,65536,2048]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n828 : fastVisit (leafFrame 5 [8,5,2] ⟨522240,[8192,65536,2048]⟩) [] ⟨0,[]⟩ b59 = true := join_live n826 n827

theorem n829 : fastVisit (leafFrame 5 [8,5,2] ⟨522240,[8192,65536,2048]⟩) [1] ⟨299008,[299008]⟩ b59 = true := by decide +kernel

theorem n830 : fastVisit (leafFrame 5 [8,5,2] ⟨522240,[8192,65536,2048]⟩) [] ⟨0,[]⟩ b58 = true := join_live n828 n829

theorem n831 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b18 = true := enterColumns 5 bank [8,5,2] ⟨522240,[8192,65536,2048]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n830

theorem n832 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b17 = true := join_dead n831 (by decide +kernel)

theorem n833 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b16 = true := join_dead n832 (by decide +kernel)

theorem n834 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b15 = true := join_dead n833 (by decide +kernel)

theorem n835 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b14 = true := join_dead n834 (by decide +kernel)

theorem n836 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b13 = true := join_dead n835 (by decide +kernel)

theorem n837 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b12 = true := join_dead n836 (by decide +kernel)

theorem n838 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b11 = true := join_dead n837 (by decide +kernel)

theorem n839 : fastVisit (leafCols 5 bank) [11,8,5,2] ⟨522828,[588,8192,65536,2048]⟩ b11 = true := by decide +kernel

theorem n840 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b10 = true := join_live n838 n839

theorem n841 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n842 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n843 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [] ⟨0,[]⟩ b61 = true := join_live n841 n842

theorem n844 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n845 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [] ⟨0,[]⟩ b45 = true := join_live n843 n844

theorem n846 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n847 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [] ⟨0,[]⟩ b44 = true := join_live n845 n846

theorem n848 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

theorem n849 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n850 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n848 n849

theorem n851 : fastVisit (leafFrame 5 [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩) [] ⟨0,[]⟩ b43 = true := join_live n847 n850

theorem n852 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b18 = true := enterColumns 5 bank [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n851

theorem n853 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b17 = true := join_dead n852 (by decide +kernel)

theorem n854 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b16 = true := join_dead n853 (by decide +kernel)

theorem n855 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b15 = true := join_dead n854 (by decide +kernel)

theorem n856 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b14 = true := join_dead n855 (by decide +kernel)

theorem n857 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b13 = true := join_dead n856 (by decide +kernel)

theorem n858 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b12 = true := join_dead n857 (by decide +kernel)

theorem n859 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b11 = true := join_dead n858 (by decide +kernel)

theorem n860 : fastVisit (leafCols 5 bank) [10,8,5,2] ⟨522248,[8,8192,65536,2048]⟩ b10 = true := join_dead n859 (by decide +kernel)

theorem n861 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b9 = true := join_live n840 n860

theorem n862 : fastVisit (leafCols 5 bank) [8,5,2] ⟨522240,[8192,65536,2048]⟩ b8 = true := join_dead n861 (by decide +kernel)

theorem n863 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b7 = true := join_live n825 n862

theorem n864 : fastVisit (leafFrame 5 [7,5,2] ⟨522240,[8192,331776,2048]⟩) [] ⟨0,[]⟩ b60 = true := by decide +kernel

theorem n865 : fastVisit (leafFrame 5 [7,5,2] ⟨522240,[8192,331776,2048]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n866 : fastVisit (leafFrame 5 [7,5,2] ⟨522240,[8192,331776,2048]⟩) [] ⟨0,[]⟩ b59 = true := join_live n864 n865

theorem n867 : fastVisit (leafFrame 5 [7,5,2] ⟨522240,[8192,331776,2048]⟩) [1] ⟨299008,[299008]⟩ b59 = true := by decide +kernel

theorem n868 : fastVisit (leafFrame 5 [7,5,2] ⟨522240,[8192,331776,2048]⟩) [] ⟨0,[]⟩ b58 = true := join_live n866 n867

theorem n869 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b18 = true := enterColumns 5 bank [7,5,2] ⟨522240,[8192,331776,2048]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n868

theorem n870 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b17 = true := join_dead n869 (by decide +kernel)

theorem n871 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b16 = true := join_dead n870 (by decide +kernel)

theorem n872 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b15 = true := join_dead n871 (by decide +kernel)

theorem n873 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b14 = true := join_dead n872 (by decide +kernel)

theorem n874 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b13 = true := join_dead n873 (by decide +kernel)

theorem n875 : fastVisit (leafCols 5 bank) [13,7,5,2] ⟨523144,[904,8192,4096,2048]⟩ b13 = true := by decide +kernel

theorem n876 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b12 = true := join_live n874 n875

theorem n877 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b11 = true := join_dead n876 (by decide +kernel)

theorem n878 : fastVisit (leafCols 5 bank) [11,7,5,2] ⟨522828,[588,8192,65536,2048]⟩ b11 = true := by decide +kernel

theorem n879 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b10 = true := join_live n877 n878

end GainFinite.F5
