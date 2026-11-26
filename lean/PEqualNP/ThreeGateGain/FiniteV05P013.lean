import PEqualNP.ThreeGateGain.FiniteV05P012

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n1040 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b16 = true := join_dead n1039 (by decide +kernel)

theorem n1041 : fastVisit (leafCols 5 bank) [16,1] ⟨323704,[24696,266240]⟩ b16 = true := by decide +kernel

theorem n1042 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b15 = true := join_live n1040 n1041

theorem n1043 : fastVisit (leafCols 5 bank) [15,1] ⟨514986,[215978,36864]⟩ b15 = true := by decide +kernel

theorem n1044 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b14 = true := join_live n1042 n1043

theorem n1045 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b13 = true := join_dead n1044 (by decide +kernel)

theorem n1046 : fastVisit (leafCols 5 bank) [13,1] ⟨496520,[197512,36864]⟩ b13 = true := by decide +kernel

theorem n1047 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b12 = true := join_live n1045 n1046

theorem n1048 : fastVisit (leafCols 5 bank) [12,1] ⟨448810,[149802,299008]⟩ b12 = true := by decide +kernel

theorem n1049 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b11 = true := join_live n1047 n1048

theorem n1050 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b10 = true := join_dead n1049 (by decide +kernel)

theorem n1051 : fastVisit (leafFrame 5 [10,1] ⟨299016,[8,299008]⟩) [] ⟨0,[]⟩ b98 = true := by decide +kernel

theorem n1052 : fastVisit (leafFrame 5 [10,1] ⟨299016,[8,299008]⟩) [2] ⟨149504,[149504]⟩ b98 = true := by decide +kernel

theorem n1053 : fastVisit (leafFrame 5 [10,1] ⟨299016,[8,299008]⟩) [] ⟨0,[]⟩ b97 = true := join_live n1051 n1052

theorem n1054 : fastVisit (leafFrame 5 [10,1] ⟨299016,[8,299008]⟩) [1] ⟨299008,[299008]⟩ b98 = true := by decide +kernel

theorem n1055 : fastVisit (leafFrame 5 [10,1] ⟨299016,[8,299008]⟩) [2,1] ⟨448512,[149504,299008]⟩ b98 = true := by decide +kernel

theorem n1056 : fastVisit (leafFrame 5 [10,1] ⟨299016,[8,299008]⟩) [1] ⟨299008,[299008]⟩ b97 = true := join_live n1054 n1055

theorem n1057 : fastVisit (leafFrame 5 [10,1] ⟨299016,[8,299008]⟩) [] ⟨0,[]⟩ b96 = true := join_live n1053 n1056

theorem n1058 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b18 = true := enterColumns 5 bank [10,1] ⟨299016,[8,299008]⟩ b18 b96 (by decide +kernel) (by decide +kernel) n1057

theorem n1059 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b17 = true := join_dead n1058 (by decide +kernel)

theorem n1060 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b16 = true := join_dead n1059 (by decide +kernel)

theorem n1061 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b15 = true := join_dead n1060 (by decide +kernel)

theorem n1062 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b14 = true := join_dead n1061 (by decide +kernel)

theorem n1063 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b13 = true := join_dead n1062 (by decide +kernel)

theorem n1064 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b12 = true := join_dead n1063 (by decide +kernel)

theorem n1065 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b11 = true := join_dead n1064 (by decide +kernel)

theorem n1066 : fastVisit (leafCols 5 bank) [10,1] ⟨299016,[8,299008]⟩ b10 = true := join_dead n1065 (by decide +kernel)

theorem n1067 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b9 = true := join_live n1050 n1066

theorem n1068 : fastVisit (leafFrame 5 [9,1] ⟨456704,[157696,266240]⟩) [] ⟨0,[]⟩ b26 = true := by decide +kernel

theorem n1069 : fastVisit (leafFrame 5 [9,1] ⟨456704,[157696,266240]⟩) [1] ⟨299008,[299008]⟩ b26 = true := by decide +kernel

theorem n1070 : fastVisit (leafFrame 5 [9,1] ⟨456704,[157696,266240]⟩) [] ⟨0,[]⟩ b25 = true := join_live n1068 n1069

theorem n1071 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b18 = true := enterColumns 5 bank [9,1] ⟨456704,[157696,266240]⟩ b18 b25 (by decide +kernel) (by decide +kernel) n1070

theorem n1072 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b17 = true := join_dead n1071 (by decide +kernel)

theorem n1073 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b16 = true := join_dead n1072 (by decide +kernel)

theorem n1074 : fastVisit (leafCols 5 bank) [16,9,1] ⟨456824,[120,133120,266240]⟩ b16 = true := by decide +kernel

theorem n1075 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b15 = true := join_live n1073 n1074

theorem n1076 : fastVisit (leafCols 5 bank) [15,9,1] ⟨523178,[66474,8192,4096]⟩ b15 = true := by decide +kernel

theorem n1077 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b14 = true := join_live n1075 n1076

theorem n1078 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b13 = true := join_dead n1077 (by decide +kernel)

theorem n1079 : fastVisit (leafCols 5 bank) [13,9,1] ⟨523144,[66440,26624,4096]⟩ b13 = true := by decide +kernel

theorem n1080 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b12 = true := join_live n1078 n1079

theorem n1081 : fastVisit (leafCols 5 bank) [12,9,1] ⟨457002,[298,8192,266240]⟩ b12 = true := by decide +kernel

theorem n1082 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b11 = true := join_live n1080 n1081

theorem n1083 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b10 = true := join_dead n1082 (by decide +kernel)

theorem n1084 : fastVisit (leafFrame 5 [10,9,1] ⟨456712,[8,157696,266240]⟩) [] ⟨0,[]⟩ b29 = true := by decide +kernel

theorem n1085 : fastVisit (leafFrame 5 [10,9,1] ⟨456712,[8,157696,266240]⟩) [2] ⟨149504,[149504]⟩ b29 = true := by decide +kernel

theorem n1086 : fastVisit (leafFrame 5 [10,9,1] ⟨456712,[8,157696,266240]⟩) [] ⟨0,[]⟩ b28 = true := join_live n1084 n1085

theorem n1087 : fastVisit (leafFrame 5 [10,9,1] ⟨456712,[8,157696,266240]⟩) [1] ⟨299008,[299008]⟩ b29 = true := by decide +kernel

theorem n1088 : fastVisit (leafFrame 5 [10,9,1] ⟨456712,[8,157696,266240]⟩) [2,1] ⟨448512,[149504,299008]⟩ b29 = true := by decide +kernel

theorem n1089 : fastVisit (leafFrame 5 [10,9,1] ⟨456712,[8,157696,266240]⟩) [1] ⟨299008,[299008]⟩ b28 = true := join_live n1087 n1088

theorem n1090 : fastVisit (leafFrame 5 [10,9,1] ⟨456712,[8,157696,266240]⟩) [] ⟨0,[]⟩ b27 = true := join_live n1086 n1089

theorem n1091 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b18 = true := enterColumns 5 bank [10,9,1] ⟨456712,[8,157696,266240]⟩ b18 b27 (by decide +kernel) (by decide +kernel) n1090

theorem n1092 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b17 = true := join_dead n1091 (by decide +kernel)

theorem n1093 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b16 = true := join_dead n1092 (by decide +kernel)

theorem n1094 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b15 = true := join_dead n1093 (by decide +kernel)

theorem n1095 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b14 = true := join_dead n1094 (by decide +kernel)

theorem n1096 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b13 = true := join_dead n1095 (by decide +kernel)

theorem n1097 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b12 = true := join_dead n1096 (by decide +kernel)

theorem n1098 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b11 = true := join_dead n1097 (by decide +kernel)

theorem n1099 : fastVisit (leafCols 5 bank) [10,9,1] ⟨456712,[8,157696,266240]⟩ b10 = true := join_dead n1098 (by decide +kernel)

theorem n1100 : fastVisit (leafCols 5 bank) [9,1] ⟨456704,[157696,266240]⟩ b9 = true := join_live n1083 n1099

theorem n1101 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b8 = true := join_live n1067 n1100

theorem n1102 : fastVisit (leafCols 5 bank) [1] ⟨299008,[299008]⟩ b7 = true := join_dead n1101 (by decide +kernel)

theorem n1103 : fastVisit (leafFrame 5 [7,1] ⟨323584,[24576,266240]⟩) [] ⟨0,[]⟩ b101 = true := by decide +kernel

theorem n1104 : fastVisit (leafFrame 5 [7,1] ⟨323584,[24576,266240]⟩) [2] ⟨149504,[149504]⟩ b101 = true := by decide +kernel

theorem n1105 : fastVisit (leafFrame 5 [7,1] ⟨323584,[24576,266240]⟩) [] ⟨0,[]⟩ b100 = true := join_live n1103 n1104

theorem n1106 : fastVisit (leafFrame 5 [7,1] ⟨323584,[24576,266240]⟩) [1] ⟨299008,[299008]⟩ b100 = true := by decide +kernel

theorem n1107 : fastVisit (leafFrame 5 [7,1] ⟨323584,[24576,266240]⟩) [] ⟨0,[]⟩ b99 = true := join_live n1105 n1106

theorem n1108 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b18 = true := enterColumns 5 bank [7,1] ⟨323584,[24576,266240]⟩ b18 b99 (by decide +kernel) (by decide +kernel) n1107

theorem n1109 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b17 = true := join_dead n1108 (by decide +kernel)

theorem n1110 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b16 = true := join_dead n1109 (by decide +kernel)

theorem n1111 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b15 = true := join_dead n1110 (by decide +kernel)

theorem n1112 : fastVisit (leafCols 5 bank) [15,7,1] ⟨523178,[199594,8192,4096]⟩ b15 = true := by decide +kernel

theorem n1113 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b14 = true := join_live n1111 n1112

theorem n1114 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b13 = true := join_dead n1113 (by decide +kernel)

theorem n1115 : fastVisit (leafCols 5 bank) [13,7,1] ⟨521096,[197512,24576,4096]⟩ b13 = true := by decide +kernel

theorem n1116 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b12 = true := join_live n1114 n1115

theorem n1117 : fastVisit (leafCols 5 bank) [12,7,1] ⟨457002,[133418,8192,266240]⟩ b12 = true := by decide +kernel

theorem n1118 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b11 = true := join_live n1116 n1117

theorem n1119 : fastVisit (leafCols 5 bank) [7,1] ⟨323584,[24576,266240]⟩ b10 = true := join_dead n1118 (by decide +kernel)

end GainFinite.F5
