import PEqualNP.ThreeGateGain.FiniteV05P011

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n960 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b10 = true := join_live n958 n959

theorem n961 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n962 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n963 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [] ⟨0,[]⟩ b61 = true := join_live n961 n962

theorem n964 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n965 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [] ⟨0,[]⟩ b45 = true := join_live n963 n964

theorem n966 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n967 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [] ⟨0,[]⟩ b44 = true := join_live n965 n966

theorem n968 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

theorem n969 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n970 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n968 n969

theorem n971 : fastVisit (leafFrame 5 [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩) [] ⟨0,[]⟩ b43 = true := join_live n967 n970

theorem n972 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b18 = true := enterColumns 5 bank [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n971

theorem n973 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b17 = true := join_dead n972 (by decide +kernel)

theorem n974 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b16 = true := join_dead n973 (by decide +kernel)

theorem n975 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b15 = true := join_dead n974 (by decide +kernel)

theorem n976 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b14 = true := join_dead n975 (by decide +kernel)

theorem n977 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b13 = true := join_dead n976 (by decide +kernel)

theorem n978 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b12 = true := join_dead n977 (by decide +kernel)

theorem n979 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b11 = true := join_dead n978 (by decide +kernel)

theorem n980 : fastVisit (leafCols 5 bank) [10,8,4,2] ⟨522248,[8,45056,65536,2048]⟩ b10 = true := join_dead n979 (by decide +kernel)

theorem n981 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b9 = true := join_live n960 n980

theorem n982 : fastVisit (leafCols 5 bank) [8,4,2] ⟨522240,[45056,65536,2048]⟩ b8 = true := join_dead n981 (by decide +kernel)

theorem n983 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b7 = true := join_live n944 n982

theorem n984 : fastVisit (leafFrame 5 [7,4,2] ⟨518144,[40960,327680,2048]⟩) [] ⟨0,[]⟩ b90 = true := by decide +kernel

theorem n985 : fastVisit (leafFrame 5 [7,4,2] ⟨518144,[40960,327680,2048]⟩) [2] ⟨149504,[149504]⟩ b90 = true := by decide +kernel

theorem n986 : fastVisit (leafFrame 5 [7,4,2] ⟨518144,[40960,327680,2048]⟩) [] ⟨0,[]⟩ b39 = true := join_live n984 n985

theorem n987 : fastVisit (leafFrame 5 [7,4,2] ⟨518144,[40960,327680,2048]⟩) [1] ⟨299008,[299008]⟩ b90 = true := by decide +kernel

theorem n988 : fastVisit (leafFrame 5 [7,4,2] ⟨518144,[40960,327680,2048]⟩) [2,1] ⟨448512,[149504,299008]⟩ b90 = true := by decide +kernel

theorem n989 : fastVisit (leafFrame 5 [7,4,2] ⟨518144,[40960,327680,2048]⟩) [1] ⟨299008,[299008]⟩ b39 = true := join_live n987 n988

theorem n990 : fastVisit (leafFrame 5 [7,4,2] ⟨518144,[40960,327680,2048]⟩) [] ⟨0,[]⟩ b38 = true := join_live n986 n989

theorem n991 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b18 = true := enterColumns 5 bank [7,4,2] ⟨518144,[40960,327680,2048]⟩ b18 b38 (by decide +kernel) (by decide +kernel) n990

theorem n992 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b17 = true := join_dead n991 (by decide +kernel)

theorem n993 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b16 = true := join_dead n992 (by decide +kernel)

theorem n994 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b15 = true := join_dead n993 (by decide +kernel)

theorem n995 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b14 = true := join_dead n994 (by decide +kernel)

theorem n996 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b13 = true := join_dead n995 (by decide +kernel)

theorem n997 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b12 = true := join_dead n996 (by decide +kernel)

theorem n998 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b11 = true := join_dead n997 (by decide +kernel)

theorem n999 : fastVisit (leafCols 5 bank) [11,7,4,2] ⟨522828,[4684,8192,65536,2048]⟩ b11 = true := by decide +kernel

theorem n1000 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b10 = true := join_live n998 n999

theorem n1001 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [] ⟨0,[]⟩ b92 = true := by decide +kernel

theorem n1002 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [5] ⟨495616,[495616]⟩ b92 = true := by decide +kernel

theorem n1003 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [] ⟨0,[]⟩ b91 = true := join_live n1001 n1002

theorem n1004 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [4] ⟨458752,[458752]⟩ b91 = true := by decide +kernel

theorem n1005 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [] ⟨0,[]⟩ b42 = true := join_live n1003 n1004

theorem n1006 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [2] ⟨149504,[149504]⟩ b42 = true := by decide +kernel

theorem n1007 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [] ⟨0,[]⟩ b41 = true := join_live n1005 n1006

theorem n1008 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [1] ⟨299008,[299008]⟩ b91 = true := by decide +kernel

theorem n1009 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [4,1] ⟨495616,[196608,36864]⟩ b91 = true := by decide +kernel

theorem n1010 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [1] ⟨299008,[299008]⟩ b42 = true := join_live n1008 n1009

theorem n1011 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [2,1] ⟨448512,[149504,299008]⟩ b42 = true := by decide +kernel

theorem n1012 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [1] ⟨299008,[299008]⟩ b41 = true := join_live n1010 n1011

theorem n1013 : fastVisit (leafFrame 5 [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩) [] ⟨0,[]⟩ b40 = true := join_live n1007 n1012

theorem n1014 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b18 = true := enterColumns 5 bank [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b18 b40 (by decide +kernel) (by decide +kernel) n1013

theorem n1015 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b17 = true := join_dead n1014 (by decide +kernel)

theorem n1016 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b16 = true := join_dead n1015 (by decide +kernel)

theorem n1017 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b15 = true := join_dead n1016 (by decide +kernel)

theorem n1018 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b14 = true := join_dead n1017 (by decide +kernel)

theorem n1019 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b13 = true := join_dead n1018 (by decide +kernel)

theorem n1020 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b12 = true := join_dead n1019 (by decide +kernel)

theorem n1021 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b11 = true := join_dead n1020 (by decide +kernel)

theorem n1022 : fastVisit (leafCols 5 bank) [10,7,4,2] ⟨518152,[8,40960,327680,2048]⟩ b10 = true := join_dead n1021 (by decide +kernel)

theorem n1023 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b9 = true := join_live n1000 n1022

theorem n1024 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b8 = true := join_dead n1023 (by decide +kernel)

theorem n1025 : fastVisit (leafCols 5 bank) [7,4,2] ⟨518144,[40960,327680,2048]⟩ b7 = true := join_dead n1024 (by decide +kernel)

theorem n1026 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b6 = true := join_live n983 n1025

theorem n1027 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b5 = true := join_dead n1026 (by decide +kernel)

theorem n1028 : fastVisit (leafCols 5 bank) [4,2] ⟨477184,[327680,18432]⟩ b4 = true := join_dead n1027 (by decide +kernel)

theorem n1029 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b3 = true := join_live n905 n1028

theorem n1030 : fastVisit (leafCols 5 bank) [2] ⟨149504,[149504]⟩ b2 = true := join_dead n1029 (by decide +kernel)

theorem n1031 : fastVisit (leafCols 5 bank) [] ⟨0,[]⟩ b1 = true := join_live n681 n1030

theorem n1032 : fastVisit (leafFrame 5 [1] ⟨299008,[299008]⟩) [] ⟨0,[]⟩ b95 = true := by decide +kernel

theorem n1033 : fastVisit (leafFrame 5 [1] ⟨299008,[299008]⟩) [2] ⟨149504,[149504]⟩ b95 = true := by decide +kernel

theorem n1034 : fastVisit (leafFrame 5 [1] ⟨299008,[299008]⟩) [] ⟨0,[]⟩ b94 = true := join_live n1032 n1033

theorem n1035 : fastVisit (leafFrame 5 [1] ⟨299008,[299008]⟩) [1] ⟨299008,[299008]⟩ b94 = true := by decide +kernel

theorem n1036 : fastVisit (leafFrame 5 [1] ⟨299008,[299008]⟩) [] ⟨0,[]⟩ b93 = true := join_live n1034 n1035

theorem n1037 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b18 = true := enterColumns 5 bank [1] ⟨299008,[299008]⟩ b18 b93 (by decide +kernel) (by decide +kernel) n1036

theorem n1038 : fastVisit (leafCols 5 bank) [18,1] ⟨457082,[158074,266240]⟩ b18 = true := by decide +kernel

theorem n1039 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b17 = true := join_live n1037 n1038

end GainFinite.F5
