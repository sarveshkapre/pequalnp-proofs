import PEqualNP.ThreeGateGain.FiniteV05P010

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n880 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n881 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n882 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [] ⟨0,[]⟩ b61 = true := join_live n880 n881

theorem n883 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n884 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [] ⟨0,[]⟩ b45 = true := join_live n882 n883

theorem n885 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n886 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [] ⟨0,[]⟩ b44 = true := join_live n884 n885

theorem n887 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

theorem n888 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n889 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n887 n888

theorem n890 : fastVisit (leafFrame 5 [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩) [] ⟨0,[]⟩ b43 = true := join_live n886 n889

theorem n891 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b18 = true := enterColumns 5 bank [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n890

theorem n892 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b17 = true := join_dead n891 (by decide +kernel)

theorem n893 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b16 = true := join_dead n892 (by decide +kernel)

theorem n894 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b15 = true := join_dead n893 (by decide +kernel)

theorem n895 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b14 = true := join_dead n894 (by decide +kernel)

theorem n896 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b13 = true := join_dead n895 (by decide +kernel)

theorem n897 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b12 = true := join_dead n896 (by decide +kernel)

theorem n898 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b11 = true := join_dead n897 (by decide +kernel)

theorem n899 : fastVisit (leafCols 5 bank) [10,7,5,2] ⟨522248,[8,8192,331776,2048]⟩ b10 = true := join_dead n898 (by decide +kernel)

theorem n900 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b9 = true := join_live n879 n899

theorem n901 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b8 = true := join_dead n900 (by decide +kernel)

theorem n902 : fastVisit (leafCols 5 bank) [7,5,2] ⟨522240,[8192,331776,2048]⟩ b7 = true := join_dead n901 (by decide +kernel)

theorem n903 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b6 = true := join_live n863 n902

theorem n904 : fastVisit (leafCols 5 bank) [5,2] ⟨514048,[364544,18432]⟩ b5 = true := join_dead n903 (by decide +kernel)

theorem n905 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b4 = true := join_live n791 n904

theorem n906 : fastVisit (leafFrame 5 [4,2] ⟨477184,[327680,18432]⟩) [] ⟨0,[]⟩ b86 = true := by decide +kernel

theorem n907 : fastVisit (leafFrame 5 [4,2] ⟨477184,[327680,18432]⟩) [1] ⟨299008,[299008]⟩ b86 = true := by decide +kernel

theorem n908 : fastVisit (leafFrame 5 [4,2] ⟨477184,[327680,18432]⟩) [] ⟨0,[]⟩ b85 = true := join_live n906 n907

theorem n909 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b18 = true := enterColumns 5 bank [4,2] ⟨477184,[327680,18432]⟩ b18 b85 (by decide +kernel) (by decide +kernel) n908

theorem n910 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b17 = true := join_dead n909 (by decide +kernel)

theorem n911 : fastVisit (leafCols 5 bank) [17,4,2] ⟨522876,[45692,65536,2048]⟩ b17 = true := by decide +kernel

theorem n912 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b16 = true := join_live n910 n911

theorem n913 : fastVisit (leafCols 5 bank) [16,4,2] ⟨518264,[41080,327680,2048]⟩ b16 = true := by decide +kernel

theorem n914 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b15 = true := join_live n912 n913

theorem n915 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b14 = true := join_dead n914 (by decide +kernel)

theorem n916 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b13 = true := join_dead n915 (by decide +kernel)

theorem n917 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b12 = true := join_dead n916 (by decide +kernel)

theorem n918 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b11 = true := join_dead n917 (by decide +kernel)

theorem n919 : fastVisit (leafCols 5 bank) [11,4,2] ⟨514636,[37452,65536,18432]⟩ b11 = true := by decide +kernel

theorem n920 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b10 = true := join_live n918 n919

theorem n921 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [] ⟨0,[]⟩ b89 = true := by decide +kernel

theorem n922 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [5] ⟨495616,[495616]⟩ b89 = true := by decide +kernel

theorem n923 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [] ⟨0,[]⟩ b88 = true := join_live n921 n922

theorem n924 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [4] ⟨458752,[458752]⟩ b88 = true := by decide +kernel

theorem n925 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [] ⟨0,[]⟩ b87 = true := join_live n923 n924

theorem n926 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [2] ⟨149504,[149504]⟩ b87 = true := by decide +kernel

theorem n927 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [] ⟨0,[]⟩ b37 = true := join_live n925 n926

theorem n928 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [1] ⟨299008,[299008]⟩ b88 = true := by decide +kernel

theorem n929 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [4,1] ⟨495616,[196608,36864]⟩ b88 = true := by decide +kernel

theorem n930 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [1] ⟨299008,[299008]⟩ b87 = true := join_live n928 n929

theorem n931 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [2,1] ⟨448512,[149504,299008]⟩ b87 = true := by decide +kernel

theorem n932 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [1] ⟨299008,[299008]⟩ b37 = true := join_live n930 n931

theorem n933 : fastVisit (leafFrame 5 [10,4,2] ⟨477192,[8,327680,18432]⟩) [] ⟨0,[]⟩ b36 = true := join_live n927 n932

theorem n934 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b18 = true := enterColumns 5 bank [10,4,2] ⟨477192,[8,327680,18432]⟩ b18 b36 (by decide +kernel) (by decide +kernel) n933

theorem n935 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b17 = true := join_dead n934 (by decide +kernel)

theorem n936 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b16 = true := join_dead n935 (by decide +kernel)

theorem n937 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b15 = true := join_dead n936 (by decide +kernel)

theorem n938 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b14 = true := join_dead n937 (by decide +kernel)

theorem n939 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b13 = true := join_dead n938 (by decide +kernel)

theorem n940 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b12 = true := join_dead n939 (by decide +kernel)

theorem n941 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b11 = true := join_dead n940 (by decide +kernel)

theorem n942 : fastVisit (leafCols 5 bank) [10,4,2] ⟨477192,[8,327680,18432]⟩ b10 = true := join_dead n941 (by decide +kernel)

theorem n943 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b9 = true := join_live n920 n942

theorem n944 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b8 = true := join_dead n943 (by decide +kernel)

theorem n945 : fastVisit (leafFrame 5 [8,4,2] ⟨522240,[45056,65536,2048]⟩) [] ⟨0,[]⟩ b60 = true := by decide +kernel

theorem n946 : fastVisit (leafFrame 5 [8,4,2] ⟨522240,[45056,65536,2048]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n947 : fastVisit (leafFrame 5 [8,4,2] ⟨522240,[45056,65536,2048]⟩) [] ⟨0,[]⟩ b59 = true := join_live n945 n946

theorem n948 : fastVisit (leafFrame 5 [8,4,2] ⟨522240,[45056,65536,2048]⟩) [1] ⟨299008,[299008]⟩ b59 = true := by decide +kernel

theorem n949 : fastVisit (leafFrame 5 [8,4,2] ⟨522240,[45056,65536,2048]⟩) [] ⟨0,[]⟩ b58 = true := join_live n947 n948

theorem n950 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b18 = true := enterColumns 5 bank [8,4,2] ⟨522240,[45056,65536,2048]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n949

theorem n951 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b17 = true := join_dead n950 (by decide +kernel)

theorem n952 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b16 = true := join_dead n951 (by decide +kernel)

theorem n953 : fastVisit (leafCols 5 bank) [16,8,4,2] ⟨522360,[120,4096,65536,2048]⟩ b16 = true := by decide +kernel

theorem n954 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b15 = true := join_live n952 n953

theorem n955 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b14 = true := join_dead n954 (by decide +kernel)

theorem n956 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b13 = true := join_dead n955 (by decide +kernel)

theorem n957 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b12 = true := join_dead n956 (by decide +kernel)

theorem n958 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b11 = true := join_dead n957 (by decide +kernel)

theorem n959 : fastVisit (leafCols 5 bank) [11,8,4,2] ⟨522828,[588,8192,65536,2048]⟩ b11 = true := by decide +kernel

end GainFinite.F5
