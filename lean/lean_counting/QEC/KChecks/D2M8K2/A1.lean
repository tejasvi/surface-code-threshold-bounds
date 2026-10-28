import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A0

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows1196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1196 = true := by
  rw [show D2M8K2.u1196 = KTree.node D2M8K2.t1200 (nat_lit 2511026) (nat_lit 2000341364) (nat_lit 0) D2M8K2.t1201 from rfl, allE_node, rows1200, irow1196, rows1201]
  all_goals rfl

theorem atot1196 : totK PD2M8K2 D2M8K2.u1196 = [0, 88265605660, 694086678928, 813516188858, 142731758143, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1196 = KTree.node D2M8K2.t1200 (nat_lit 2511026) (nat_lit 2000341364) (nat_lit 0) D2M8K2.t1201 from rfl, totK_node, tot1200, tot1201]
  decide +kernel

theorem arows1197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1197 = true := by
  rw [show D2M8K2.u1197 = KTree.node D2M8K2.t1202 (nat_lit 2516646) (nat_lit 2583851253) (nat_lit 0) D2M8K2.t1203 from rfl, allE_node, rows1202, irow1197, rows1203]
  all_goals rfl

theorem atot1197 : totK PD2M8K2 D2M8K2.u1197 = [0, 412050283868, 959904722333, 399209131312, 17690209400, 0, 0, 0] := by
  rw [show D2M8K2.u1197 = KTree.node D2M8K2.t1202 (nat_lit 2516646) (nat_lit 2583851253) (nat_lit 0) D2M8K2.t1203 from rfl, totK_node, tot1202, tot1203]
  decide +kernel

theorem arows1199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1199 = true := by
  rw [show D2M8K2.u1199 = KTree.node D2M8K2.t1204 (nat_lit 2519976) (nat_lit 2704631544) (nat_lit 0) D2M8K2.t1205 from rfl, allE_node, rows1204, irow1199, rows1205]
  all_goals rfl

theorem atot1199 : totK PD2M8K2 D2M8K2.u1199 = [0, 342181946802, 938338554316, 479099766316, 26623967090, 0, 0, 0] := by
  rw [show D2M8K2.u1199 = KTree.node D2M8K2.t1204 (nat_lit 2519976) (nat_lit 2704631544) (nat_lit 0) D2M8K2.t1205 from rfl, totK_node, tot1204, tot1205]
  decide +kernel

theorem arows1200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1200 = true := by
  rw [show D2M8K2.u1200 = KTree.node D2M8K2.t1206 (nat_lit 2523514) (nat_lit 3646692530) (nat_lit 0) D2M8K2.t1207 from rfl, allE_node, rows1206, irow1200, rows1207]
  all_goals rfl

theorem atot1200 : totK PD2M8K2 D2M8K2.u1200 = [0, 390771302641, 935975113717, 429035940013, 27040075559, 0, 0, 0] := by
  rw [show D2M8K2.u1200 = KTree.node D2M8K2.t1206 (nat_lit 2523514) (nat_lit 3646692530) (nat_lit 0) D2M8K2.t1207 from rfl, totK_node, tot1206, tot1207]
  decide +kernel

theorem arows1203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1203 = true := by
  rw [show D2M8K2.u1203 = KTree.node D2M8K2.t1208 (nat_lit 2526838) (nat_lit 3374378094) (nat_lit 0) D2M8K2.t1209 from rfl, allE_node, rows1208, irow1203, rows1209]
  all_goals rfl

theorem atot1203 : totK PD2M8K2 D2M8K2.u1203 = [0, 353044976374, 954744559721, 467082656002, 20161118843, 0, 0, 0] := by
  rw [show D2M8K2.u1203 = KTree.node D2M8K2.t1208 (nat_lit 2526838) (nat_lit 3374378094) (nat_lit 0) D2M8K2.t1209 from rfl, totK_node, tot1208, tot1209]
  decide +kernel

theorem arows1204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1204 = true := by
  rw [show D2M8K2.u1204 = KTree.node D2M8K2.t1210 (nat_lit 2533770) (nat_lit 3826710699) (nat_lit 0) D2M8K2.t1211 from rfl, allE_node, rows1210, irow1204, rows1211]
  all_goals rfl

theorem atot1204 : totK PD2M8K2 D2M8K2.u1204 = [268111487010, 747866708719, 620816669046, 187655800864, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u1204 = KTree.node D2M8K2.t1210 (nat_lit 2533770) (nat_lit 3826710699) (nat_lit 0) D2M8K2.t1211 from rfl, totK_node, tot1210, tot1211]
  decide +kernel

theorem arows1206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1206 = true := by
  rw [show D2M8K2.u1206 = KTree.node D2M8K2.t1212 (nat_lit 2535299) (nat_lit 2848308795) (nat_lit 0) D2M8K2.t1213 from rfl, allE_node, rows1212, irow1206, rows1213]
  all_goals rfl

theorem atot1206 : totK PD2M8K2 D2M8K2.u1206 = [162641740095, 641422731658, 711653699249, 280203797718, 25373788367, 0, 0, 0] := by
  rw [show D2M8K2.u1206 = KTree.node D2M8K2.t1212 (nat_lit 2535299) (nat_lit 2848308795) (nat_lit 0) D2M8K2.t1213 from rfl, totK_node, tot1212, tot1213]
  decide +kernel

theorem arows1207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1207 = true := by
  rw [show D2M8K2.u1207 = KTree.node D2M8K2.t1214 (nat_lit 2536498) (nat_lit 4005483109) (nat_lit 0) D2M8K2.t1215 from rfl, allE_node, rows1214, irow1207, rows1215]
  all_goals rfl

theorem atot1207 : totK PD2M8K2 D2M8K2.u1207 = [156454984840, 590725622510, 762146388625, 302142189886, 12235609738, 0, 0, 0] := by
  rw [show D2M8K2.u1207 = KTree.node D2M8K2.t1214 (nat_lit 2536498) (nat_lit 4005483109) (nat_lit 0) D2M8K2.t1215 from rfl, totK_node, tot1214, tot1215]
  decide +kernel

theorem arows1213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1213 = true := by
  rw [show D2M8K2.u1213 = KTree.node D2M8K2.t1216 (nat_lit 2538099) (nat_lit 2986366710) (nat_lit 0) D2M8K2.t1217 from rfl, allE_node, rows1216, irow1213, rows1217]
  all_goals rfl

theorem atot1213 : totK PD2M8K2 D2M8K2.u1213 = [247081501245, 788194307541, 661653290390, 107177277620, 1163840124, 0, 0, 0] := by
  rw [show D2M8K2.u1213 = KTree.node D2M8K2.t1216 (nat_lit 2538099) (nat_lit 2986366710) (nat_lit 0) D2M8K2.t1217 from rfl, totK_node, tot1216, tot1217]
  decide +kernel

theorem arows1214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1214 = true := by
  rw [show D2M8K2.u1214 = KTree.node D2M8K2.t1218 (nat_lit 2539872) (nat_lit 3623718774) (nat_lit 0) D2M8K2.t1219 from rfl, allE_node, rows1218, irow1214, rows1219]
  all_goals rfl

theorem atot1214 : totK PD2M8K2 D2M8K2.u1214 = [156547374977, 648063431530, 765570844447, 222467982165, 11842047461, 0, 0, 0] := by
  rw [show D2M8K2.u1214 = KTree.node D2M8K2.t1218 (nat_lit 2539872) (nat_lit 3623718774) (nat_lit 0) D2M8K2.t1219 from rfl, totK_node, tot1218, tot1219]
  decide +kernel

theorem arows1216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1216 = true := by
  rw [show D2M8K2.u1216 = KTree.node D2M8K2.t1220 (nat_lit 2541565) (nat_lit 1063116097) (nat_lit 0) D2M8K2.t1221 from rfl, allE_node, rows1220, irow1216, rows1221]
  all_goals rfl

theorem atot1216 : totK PD2M8K2 D2M8K2.u1216 = [247247727347, 801646665107, 658874601486, 104270984191, 1197396724, 0, 0, 0] := by
  rw [show D2M8K2.u1216 = KTree.node D2M8K2.t1220 (nat_lit 2541565) (nat_lit 1063116097) (nat_lit 0) D2M8K2.t1221 from rfl, totK_node, tot1220, tot1221]
  decide +kernel

theorem arows1217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1217 = true := by
  rw [show D2M8K2.u1217 = KTree.node D2M8K2.t1222 (nat_lit 2543335) (nat_lit 2345565721) (nat_lit 0) D2M8K2.t1223 from rfl, allE_node, rows1222, irow1217, rows1223]
  all_goals rfl

theorem atot1217 : totK PD2M8K2 D2M8K2.u1217 = [162238061422, 648042195592, 759521203961, 230140050845, 12006692157, 0, 0, 0] := by
  rw [show D2M8K2.u1217 = KTree.node D2M8K2.t1222 (nat_lit 2543335) (nat_lit 2345565721) (nat_lit 0) D2M8K2.t1223 from rfl, totK_node, tot1222, tot1223]
  decide +kernel

theorem arows1220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1220 = true := by
  rw [show D2M8K2.u1220 = KTree.node D2M8K2.t1224 (nat_lit 2548155) (nat_lit 3437358801) (nat_lit 0) D2M8K2.t1225 from rfl, allE_node, rows1224, irow1220, rows1225]
  all_goals rfl

theorem atot1220 : totK PD2M8K2 D2M8K2.u1220 = [266108403091, 806978522741, 636263524782, 96690995529, 1267860612, 0, 0, 0] := by
  rw [show D2M8K2.u1220 = KTree.node D2M8K2.t1224 (nat_lit 2548155) (nat_lit 3437358801) (nat_lit 0) D2M8K2.t1225 from rfl, totK_node, tot1224, tot1225]
  decide +kernel

theorem arows1221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1221 = true := by
  rw [show D2M8K2.u1221 = KTree.node D2M8K2.t1226 (nat_lit 2549806) (nat_lit 4022582217) (nat_lit 0) D2M8K2.t1227 from rfl, allE_node, rows1226, irow1221, rows1227]
  all_goals rfl

theorem atot1221 : totK PD2M8K2 D2M8K2.u1221 = [0, 448539435805, 963775598254, 367323016114, 20760161187, 0, 0, 0] := by
  rw [show D2M8K2.u1221 = KTree.node D2M8K2.t1226 (nat_lit 2549806) (nat_lit 4022582217) (nat_lit 0) D2M8K2.t1227 from rfl, totK_node, tot1226, tot1227]
  decide +kernel

theorem arows1223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1223 = true := by
  rw [show D2M8K2.u1223 = KTree.node D2M8K2.t1228 (nat_lit 2554986) (nat_lit 3859613824) (nat_lit 0) D2M8K2.t1229 from rfl, allE_node, rows1228, irow1223, rows1229]
  all_goals rfl

theorem atot1223 : totK PD2M8K2 D2M8K2.u1223 = [0, 335852059307, 920964718628, 534125761203, 39439534227, 0, 0, 0] := by
  rw [show D2M8K2.u1223 = KTree.node D2M8K2.t1228 (nat_lit 2554986) (nat_lit 3859613824) (nat_lit 0) D2M8K2.t1229 from rfl, totK_node, tot1228, tot1229]
  decide +kernel

theorem arows1224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1224 = true := by
  rw [show D2M8K2.u1224 = KTree.node D2M8K2.t1230 (nat_lit 2556490) (nat_lit 3819550451) (nat_lit 0) D2M8K2.t1231 from rfl, allE_node, rows1230, irow1224, rows1231]
  all_goals rfl

theorem atot1224 : totK PD2M8K2 D2M8K2.u1224 = [0, 0, 395568921864, 933496375471, 430425306420, 30397782892, 0, 0] := by
  rw [show D2M8K2.u1224 = KTree.node D2M8K2.t1230 (nat_lit 2556490) (nat_lit 3819550451) (nat_lit 0) D2M8K2.t1231 from rfl, totK_node, tot1230, tot1231]
  decide +kernel

theorem arows1228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1228 = true := by
  rw [show D2M8K2.u1228 = KTree.node D2M8K2.t1232 (nat_lit 2557870) (nat_lit 4014593938) (nat_lit 0) D2M8K2.t1233 from rfl, allE_node, rows1232, irow1228, rows1233]
  all_goals rfl

theorem atot1228 : totK PD2M8K2 D2M8K2.u1228 = [0, 315068060263, 802750778865, 547423837491, 132477993940, 6524090962, 0, 0] := by
  rw [show D2M8K2.u1228 = KTree.node D2M8K2.t1232 (nat_lit 2557870) (nat_lit 4014593938) (nat_lit 0) D2M8K2.t1233 from rfl, totK_node, tot1232, tot1233]
  decide +kernel

theorem arows1229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1229 = true := by
  rw [show D2M8K2.u1229 = KTree.node D2M8K2.t1234 (nat_lit 2559561) (nat_lit 1879110636) (nat_lit 0) D2M8K2.t1235 from rfl, allE_node, rows1234, irow1229, rows1235]
  all_goals rfl

theorem atot1229 : totK PD2M8K2 D2M8K2.u1229 = [0, 87395272022, 635035450531, 855197875004, 198924558616, 5159868635, 0, 0] := by
  rw [show D2M8K2.u1229 = KTree.node D2M8K2.t1234 (nat_lit 2559561) (nat_lit 1879110636) (nat_lit 0) D2M8K2.t1235 from rfl, totK_node, tot1234, tot1235]
  decide +kernel

theorem arows1231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1231 = true := by
  rw [show D2M8K2.u1231 = KTree.node D2M8K2.t1236 (nat_lit 2561467) (nat_lit 1172708448) (nat_lit 0) D2M8K2.t1237 from rfl, allE_node, rows1236, irow1231, rows1237]
  all_goals rfl

theorem atot1231 : totK PD2M8K2 D2M8K2.u1231 = [0, 356908838520, 900085784886, 514757994459, 46597402189, 0, 0, 0] := by
  rw [show D2M8K2.u1231 = KTree.node D2M8K2.t1236 (nat_lit 2561467) (nat_lit 1172708448) (nat_lit 0) D2M8K2.t1237 from rfl, totK_node, tot1236, tot1237]
  decide +kernel

theorem arows1232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1232 = true := by
  rw [show D2M8K2.u1232 = KTree.node D2M8K2.t1238 (nat_lit 2563596) (nat_lit 2796269112) (nat_lit 0) D2M8K2.t1239 from rfl, allE_node, rows1238, irow1232, rows1239]
  all_goals rfl

theorem atot1232 : totK PD2M8K2 D2M8K2.u1232 = [0, 98121291846, 627206728276, 850685995442, 210980902586, 5218872685, 0, 0] := by
  rw [show D2M8K2.u1232 = KTree.node D2M8K2.t1238 (nat_lit 2563596) (nat_lit 2796269112) (nat_lit 0) D2M8K2.t1239 from rfl, totK_node, tot1238, tot1239]
  decide +kernel

theorem arows1235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1235 = true := by
  rw [show D2M8K2.u1235 = KTree.node D2M8K2.t1240 (nat_lit 2568518) (nat_lit 3977188800) (nat_lit 0) D2M8K2.t1241 from rfl, allE_node, rows1240, irow1235, rows1241]
  all_goals rfl

theorem atot1235 : totK PD2M8K2 D2M8K2.u1235 = [0, 374222194908, 940094290343, 484623015532, 36140781951, 0, 0, 0] := by
  rw [show D2M8K2.u1235 = KTree.node D2M8K2.t1240 (nat_lit 2568518) (nat_lit 3977188800) (nat_lit 0) D2M8K2.t1241 from rfl, totK_node, tot1240, tot1241]
  decide +kernel

theorem arows1236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1236 = true := by
  rw [show D2M8K2.u1236 = KTree.node D2M8K2.t1242 (nat_lit 2570324) (nat_lit 1569038788) (nat_lit 0) D2M8K2.t1243 from rfl, allE_node, rows1242, irow1236, rows1243]
  all_goals rfl

theorem atot1236 : totK PD2M8K2 D2M8K2.u1236 = [18872545859, 24649648434, 498890929249, 938127989251, 285262578984, 9302370699, 0, 0] := by
  rw [show D2M8K2.u1236 = KTree.node D2M8K2.t1242 (nat_lit 2570324) (nat_lit 1569038788) (nat_lit 0) D2M8K2.t1243 from rfl, totK_node, tot1242, tot1243]
  decide +kernel

theorem arows1238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1238 = true := by
  rw [show D2M8K2.u1238 = KTree.node D2M8K2.t1244 (nat_lit 2572230) (nat_lit 3665200477) (nat_lit 0) D2M8K2.t1245 from rfl, allE_node, rows1244, irow1238, rows1245]
  all_goals rfl

theorem atot1238 : totK PD2M8K2 D2M8K2.u1238 = [391635362137, 949953709099, 425879540012, 23617954233, 0, 0, 0, 0] := by
  rw [show D2M8K2.u1238 = KTree.node D2M8K2.t1244 (nat_lit 2572230) (nat_lit 3665200477) (nat_lit 0) D2M8K2.t1245 from rfl, totK_node, tot1244, tot1245]
  decide +kernel

theorem arows1239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1239 = true := by
  rw [show D2M8K2.u1239 = KTree.node D2M8K2.t1246 (nat_lit 2573950) (nat_lit 3656565512) (nat_lit 0) D2M8K2.t1247 from rfl, allE_node, rows1246, irow1239, rows1247]
  all_goals rfl

theorem atot1239 : totK PD2M8K2 D2M8K2.u1239 = [91193102611, 658257722569, 893886273412, 165504969851, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u1239 = KTree.node D2M8K2.t1246 (nat_lit 2573950) (nat_lit 3656565512) (nat_lit 0) D2M8K2.t1247 from rfl, totK_node, tot1246, tot1247]
  decide +kernel

theorem arows1244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1244 = true := by
  rw [show D2M8K2.u1244 = KTree.node D2M8K2.t1248 (nat_lit 2575910) (nat_lit 4150076328) (nat_lit 0) D2M8K2.t1249 from rfl, allE_node, rows1248, irow1244, rows1249]
  all_goals rfl

theorem atot1244 : totK PD2M8K2 D2M8K2.u1244 = [296843622796, 887886029750, 582454671822, 57631309978, 0, 0, 0, 0] := by
  rw [show D2M8K2.u1244 = KTree.node D2M8K2.t1248 (nat_lit 2575910) (nat_lit 4150076328) (nat_lit 0) D2M8K2.t1249 from rfl, totK_node, tot1248, tot1249]
  decide +kernel

theorem arows1245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1245 = true := by
  rw [show D2M8K2.u1245 = KTree.node D2M8K2.t1250 (nat_lit 2577484) (nat_lit 3209142557) (nat_lit 0) D2M8K2.t1251 from rfl, allE_node, rows1250, irow1245, rows1251]
  all_goals rfl

theorem atot1245 : totK PD2M8K2 D2M8K2.u1245 = [37176659836, 354206329751, 884524141305, 491659917947, 36278427075, 0, 0, 0] := by
  rw [show D2M8K2.u1245 = KTree.node D2M8K2.t1250 (nat_lit 2577484) (nat_lit 3209142557) (nat_lit 0) D2M8K2.t1251 from rfl, totK_node, tot1250, tot1251]
  decide +kernel

theorem arows1247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1247 = true := by
  rw [show D2M8K2.u1247 = KTree.node D2M8K2.t1252 (nat_lit 2578800) (nat_lit 3579177068) (nat_lit 0) D2M8K2.t1253 from rfl, allE_node, rows1252, irow1247, rows1253]
  all_goals rfl

theorem atot1247 : totK PD2M8K2 D2M8K2.u1247 = [370365293103, 935314475984, 474331242089, 34851549612, 0, 0, 0, 0] := by
  rw [show D2M8K2.u1247 = KTree.node D2M8K2.t1252 (nat_lit 2578800) (nat_lit 3579177068) (nat_lit 0) D2M8K2.t1253 from rfl, totK_node, tot1252, tot1253]
  decide +kernel

theorem arows1248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1248 = true := by
  rw [show D2M8K2.u1248 = KTree.node D2M8K2.t1254 (nat_lit 2580329) (nat_lit 1609440031) (nat_lit 0) D2M8K2.t1255 from rfl, allE_node, rows1254, irow1248, rows1255]
  all_goals rfl

theorem atot1248 : totK PD2M8K2 D2M8K2.u1248 = [30598352162, 518471714495, 931575880957, 282569207072, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u1248 = KTree.node D2M8K2.t1254 (nat_lit 2580329) (nat_lit 1609440031) (nat_lit 0) D2M8K2.t1255 from rfl, totK_node, tot1254, tot1255]
  decide +kernel

theorem arows1251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1251 = true := by
  rw [show D2M8K2.u1251 = KTree.node D2M8K2.t1256 (nat_lit 2585644) (nat_lit 3752094956) (nat_lit 0) D2M8K2.t1257 from rfl, allE_node, rows1256, irow1251, rows1257]
  all_goals rfl

theorem atot1251 : totK PD2M8K2 D2M8K2.u1251 = [326321130087, 900251054780, 539451176885, 55654847090, 0, 0, 0, 0] := by
  rw [show D2M8K2.u1251 = KTree.node D2M8K2.t1256 (nat_lit 2585644) (nat_lit 3752094956) (nat_lit 0) D2M8K2.t1257 from rfl, totK_node, tot1256, tot1257]
  decide +kernel

theorem arows1252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1252 = true := by
  rw [show D2M8K2.u1252 = KTree.node D2M8K2.t1258 (nat_lit 2588037) (nat_lit 1513247326) (nat_lit 0) D2M8K2.t1259 from rfl, allE_node, rows1258, irow1252, rows1259]
  all_goals rfl

theorem atot1252 : totK PD2M8K2 D2M8K2.u1252 = [172161542757, 668921953941, 757863133987, 184121177812, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u1252 = KTree.node D2M8K2.t1258 (nat_lit 2588037) (nat_lit 1513247326) (nat_lit 0) D2M8K2.t1259 from rfl, totK_node, tot1258, tot1259]
  decide +kernel

theorem arows1254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1254 = true := by
  rw [show D2M8K2.u1254 = KTree.node D2M8K2.t1260 (nat_lit 2589564) (nat_lit 3151755176) (nat_lit 0) D2M8K2.t1261 from rfl, allE_node, rows1260, irow1254, rows1261]
  all_goals rfl

theorem atot1254 : totK PD2M8K2 D2M8K2.u1254 = [254226189196, 819660895890, 651289299783, 92503851416, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u1254 = KTree.node D2M8K2.t1260 (nat_lit 2589564) (nat_lit 3151755176) (nat_lit 0) D2M8K2.t1261 from rfl, totK_node, tot1260, tot1261]
  decide +kernel

theorem arows1255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1255 = true := by
  rw [show D2M8K2.u1255 = KTree.node D2M8K2.t1262 (nat_lit 2591261) (nat_lit 1732392732) (nat_lit 0) D2M8K2.t1263 from rfl, allE_node, rows1262, irow1255, rows1263]
  all_goals rfl

theorem atot1255 : totK PD2M8K2 D2M8K2.u1255 = [0, 429016359505, 957330717183, 371812171661, 20774199517, 0, 0, 0] := by
  rw [show D2M8K2.u1255 = KTree.node D2M8K2.t1262 (nat_lit 2591261) (nat_lit 1732392732) (nat_lit 0) D2M8K2.t1263 from rfl, totK_node, tot1262, tot1263]
  decide +kernel

theorem arows1259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1259 = true := by
  rw [show D2M8K2.u1259 = KTree.node D2M8K2.t1264 (nat_lit 2593152) (nat_lit 3716921436) (nat_lit 0) D2M8K2.t1265 from rfl, allE_node, rows1264, irow1259, rows1265]
  all_goals rfl

theorem atot1259 : totK PD2M8K2 D2M8K2.u1259 = [0, 319787423424, 936818433423, 490427465025, 28388460899, 0, 0, 0] := by
  rw [show D2M8K2.u1259 = KTree.node D2M8K2.t1264 (nat_lit 2593152) (nat_lit 3716921436) (nat_lit 0) D2M8K2.t1265 from rfl, totK_node, tot1264, tot1265]
  decide +kernel

theorem arows1260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1260 = true := by
  rw [show D2M8K2.u1260 = KTree.node D2M8K2.t1266 (nat_lit 2595186) (nat_lit 2713804981) (nat_lit 0) D2M8K2.t1267 from rfl, allE_node, rows1266, irow1260, rows1267]
  all_goals rfl

theorem atot1260 : totK PD2M8K2 D2M8K2.u1260 = [0, 179483303131, 733029871666, 741481909454, 113578468643, 1206465782, 0, 0] := by
  rw [show D2M8K2.u1260 = KTree.node D2M8K2.t1266 (nat_lit 2595186) (nat_lit 2713804981) (nat_lit 0) D2M8K2.t1267 from rfl, totK_node, tot1266, tot1267]
  decide +kernel

theorem arows1262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1262 = true := by
  rw [show D2M8K2.u1262 = KTree.node D2M8K2.t1268 (nat_lit 2596975) (nat_lit 2364120786) (nat_lit 0) D2M8K2.t1269 from rfl, allE_node, rows1268, irow1262, rows1269]
  all_goals rfl

theorem atot1262 : totK PD2M8K2 D2M8K2.u1262 = [0, 376656937555, 953277590804, 449152098614, 25693354060, 0, 0, 0] := by
  rw [show D2M8K2.u1262 = KTree.node D2M8K2.t1268 (nat_lit 2596975) (nat_lit 2364120786) (nat_lit 0) D2M8K2.t1269 from rfl, totK_node, tot1268, tot1269]
  decide +kernel

theorem arows1263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1263 = true := by
  rw [show D2M8K2.u1263 = KTree.node D2M8K2.t1270 (nat_lit 2600166) (nat_lit 3278648298) (nat_lit 0) D2M8K2.t1271 from rfl, allE_node, rows1270, irow1263, rows1271]
  all_goals rfl

theorem atot1263 : totK PD2M8K2 D2M8K2.u1263 = [0, 267957451133, 862536099585, 594184757299, 65307139461, 1162935789, 0, 0] := by
  rw [show D2M8K2.u1263 = KTree.node D2M8K2.t1270 (nat_lit 2600166) (nat_lit 3278648298) (nat_lit 0) D2M8K2.t1271 from rfl, totK_node, tot1270, tot1271]
  decide +kernel

theorem arows1266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1266 = true := by
  rw [show D2M8K2.u1266 = KTree.node D2M8K2.t1272 (nat_lit 2601864) (nat_lit 3041216750) (nat_lit 0) D2M8K2.t1273 from rfl, allE_node, rows1272, irow1266, rows1273]
  all_goals rfl

theorem atot1266 : totK PD2M8K2 D2M8K2.u1266 = [0, 114968444822, 585032622689, 788679064344, 241345145692, 11853261585, 0, 0] := by
  rw [show D2M8K2.u1266 = KTree.node D2M8K2.t1272 (nat_lit 2601864) (nat_lit 3041216750) (nat_lit 0) D2M8K2.t1273 from rfl, totK_node, tot1272, tot1273]
  decide +kernel

theorem arows1267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1267 = true := by
  rw [show D2M8K2.u1267 = KTree.node D2M8K2.t1274 (nat_lit 2607066) (nat_lit 3733417328) (nat_lit 0) D2M8K2.t1275 from rfl, allE_node, rows1274, irow1267, rows1275]
  all_goals rfl

theorem atot1267 : totK PD2M8K2 D2M8K2.u1267 = [0, 206322869450, 796010269445, 676746138642, 89255472132, 1021600638, 0, 0] := by
  rw [show D2M8K2.u1267 = KTree.node D2M8K2.t1274 (nat_lit 2607066) (nat_lit 3733417328) (nat_lit 0) D2M8K2.t1275 from rfl, totK_node, tot1274, tot1275]
  decide +kernel

theorem arows1269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1269 = true := by
  rw [show D2M8K2.u1269 = KTree.node D2M8K2.t1276 (nat_lit 2609616) (nat_lit 2797969580) (nat_lit 0) D2M8K2.t1277 from rfl, allE_node, rows1276, irow1269, rows1277]
  all_goals rfl

theorem atot1269 : totK PD2M8K2 D2M8K2.u1269 = [0, 284369283705, 797663732536, 580790823973, 104412807615, 3552795014, 0, 0] := by
  rw [show D2M8K2.u1269 = KTree.node D2M8K2.t1276 (nat_lit 2609616) (nat_lit 2797969580) (nat_lit 0) D2M8K2.t1277 from rfl, totK_node, tot1276, tot1277]
  decide +kernel

theorem arows1270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1270 = true := by
  rw [show D2M8K2.u1270 = KTree.node D2M8K2.t1278 (nat_lit 2612821) (nat_lit 1269065816) (nat_lit 0) D2M8K2.t1279 from rfl, allE_node, rows1278, irow1270, rows1279]
  all_goals rfl

theorem atot1270 : totK PD2M8K2 D2M8K2.u1270 = [245750340552, 692404904148, 606190776366, 241329905119, 17476474534, 0, 0, 0] := by
  rw [show D2M8K2.u1270 = KTree.node D2M8K2.t1278 (nat_lit 2612821) (nat_lit 1269065816) (nat_lit 0) D2M8K2.t1279 from rfl, totK_node, tot1278, tot1279]
  decide +kernel

theorem arows1278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1278 = true := by
  rw [show D2M8K2.u1278 = KTree.node D2M8K2.t1280 (nat_lit 2614393) (nat_lit 1444012582) (nat_lit 0) D2M8K2.t1281 from rfl, allE_node, rows1280, irow1278, rows1281]
  all_goals rfl

theorem atot1278 : totK PD2M8K2 D2M8K2.u1278 = [164815754859, 733795514095, 766294141034, 127066547494, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u1278 = KTree.node D2M8K2.t1280 (nat_lit 2614393) (nat_lit 1444012582) (nat_lit 0) D2M8K2.t1281 from rfl, totK_node, tot1280, tot1281]
  decide +kernel

theorem arows1279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1279 = true := by
  rw [show D2M8K2.u1279 = KTree.node D2M8K2.t1282 (nat_lit 2616736) (nat_lit 2781657352) (nat_lit 0) D2M8K2.t1283 from rfl, allE_node, rows1282, irow1279, rows1283]
  all_goals rfl

theorem atot1279 : totK PD2M8K2 D2M8K2.u1279 = [285356006281, 844766135706, 633187601401, 71138528671, 0, 0, 0, 0] := by
  rw [show D2M8K2.u1279 = KTree.node D2M8K2.t1282 (nat_lit 2616736) (nat_lit 2781657352) (nat_lit 0) D2M8K2.t1283 from rfl, totK_node, tot1282, tot1283]
  decide +kernel

theorem arows1281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1281 = true := by
  rw [show D2M8K2.u1281 = KTree.node D2M8K2.t1284 (nat_lit 2618381) (nat_lit 2168440061) (nat_lit 0) D2M8K2.t1285 from rfl, allE_node, rows1284, irow1281, rows1285]
  all_goals rfl

theorem atot1281 : totK PD2M8K2 D2M8K2.u1281 = [102782614777, 551895334249, 788061852571, 339842908115, 28099722102, 0, 0, 0] := by
  rw [show D2M8K2.u1281 = KTree.node D2M8K2.t1284 (nat_lit 2618381) (nat_lit 2168440061) (nat_lit 0) D2M8K2.t1285 from rfl, totK_node, tot1284, tot1285]
  decide +kernel

theorem arows1282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1282 = true := by
  rw [show D2M8K2.u1282 = KTree.node D2M8K2.t1286 (nat_lit 2623208) (nat_lit 3842206317) (nat_lit 0) D2M8K2.t1287 from rfl, allE_node, rows1286, irow1282, rows1287]
  all_goals rfl

theorem atot1282 : totK PD2M8K2 D2M8K2.u1282 = [247993230328, 701404988911, 652010202515, 209004069654, 8209296672, 0, 0, 0] := by
  rw [show D2M8K2.u1282 = KTree.node D2M8K2.t1286 (nat_lit 2623208) (nat_lit 3842206317) (nat_lit 0) D2M8K2.t1287 from rfl, totK_node, tot1286, tot1287]
  decide +kernel

theorem arows1285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1285 = true := by
  rw [show D2M8K2.u1285 = KTree.node D2M8K2.t1288 (nat_lit 2624687) (nat_lit 2777443937) (nat_lit 0) D2M8K2.t1289 from rfl, allE_node, rows1288, irow1285, rows1289]
  all_goals rfl

theorem atot1285 : totK PD2M8K2 D2M8K2.u1285 = [190336416222, 775136721833, 722953999868, 115801168020, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u1285 = KTree.node D2M8K2.t1288 (nat_lit 2624687) (nat_lit 2777443937) (nat_lit 0) D2M8K2.t1289 from rfl, totK_node, tot1288, tot1289]
  decide +kernel

theorem arows1286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1286 = true := by
  rw [show D2M8K2.u1286 = KTree.node D2M8K2.t1290 (nat_lit 2626344) (nat_lit 3497358080) (nat_lit 0) D2M8K2.t1291 from rfl, allE_node, rows1290, irow1286, rows1291]
  all_goals rfl

theorem atot1286 : totK PD2M8K2 D2M8K2.u1286 = [168980700029, 628844672864, 749371817432, 232407806794, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u1286 = KTree.node D2M8K2.t1290 (nat_lit 2626344) (nat_lit 3497358080) (nat_lit 0) D2M8K2.t1291 from rfl, totK_node, tot1290, tot1291]
  decide +kernel

theorem arows1288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1288 = true := by
  rw [show D2M8K2.u1288 = KTree.node D2M8K2.t1292 (nat_lit 2628361) (nat_lit 1506944971) (nat_lit 0) D2M8K2.t1293 from rfl, allE_node, rows1292, irow1288, rows1293]
  all_goals rfl

theorem atot1288 : totK PD2M8K2 D2M8K2.u1288 = [157474047746, 752270412732, 773588724537, 124192191511, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u1288 = KTree.node D2M8K2.t1292 (nat_lit 2628361) (nat_lit 1506944971) (nat_lit 0) D2M8K2.t1293 from rfl, totK_node, tot1292, tot1293]
  decide +kernel

theorem arows1289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1289 = true := by
  rw [show D2M8K2.u1289 = KTree.node D2M8K2.t1294 (nat_lit 2630505) (nat_lit 699420537) (nat_lit 0) D2M8K2.t1295 from rfl, allE_node, rows1294, irow1289, rows1295]
  all_goals rfl

theorem atot1289 : totK PD2M8K2 D2M8K2.u1289 = [333498962213, 834921312121, 525734272965, 105498643880, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u1289 = KTree.node D2M8K2.t1294 (nat_lit 2630505) (nat_lit 699420537) (nat_lit 0) D2M8K2.t1295 from rfl, totK_node, tot1294, tot1295]
  decide +kernel

theorem arows1293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1293 = true := by
  rw [show D2M8K2.u1293 = KTree.node D2M8K2.t1296 (nat_lit 2632015) (nat_lit 1792094332) (nat_lit 0) D2M8K2.t1297 from rfl, allE_node, rows1296, irow1293, rows1297]
  all_goals rfl

theorem atot1293 : totK PD2M8K2 D2M8K2.u1293 = [92934196222, 592473102013, 862106074687, 240136030131, 6030373525, 0, 0, 0] := by
  rw [show D2M8K2.u1293 = KTree.node D2M8K2.t1296 (nat_lit 2632015) (nat_lit 1792094332) (nat_lit 0) D2M8K2.t1297 from rfl, totK_node, tot1296, tot1297]
  decide +kernel

theorem arows1294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1294 = true := by
  rw [show D2M8K2.u1294 = KTree.node D2M8K2.t1298 (nat_lit 2633688) (nat_lit 3601261849) (nat_lit 0) D2M8K2.t1299 from rfl, allE_node, rows1298, irow1294, rows1299]
  all_goals rfl

theorem atot1294 : totK PD2M8K2 D2M8K2.u1294 = [0, 365731036798, 948334640353, 441348300456, 27095274420, 0, 0, 0] := by
  rw [show D2M8K2.u1294 = KTree.node D2M8K2.t1298 (nat_lit 2633688) (nat_lit 3601261849) (nat_lit 0) D2M8K2.t1299 from rfl, totK_node, tot1298, tot1299]
  decide +kernel

theorem arows1296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1296 = true := by
  rw [show D2M8K2.u1296 = KTree.node D2M8K2.t1300 (nat_lit 2635304) (nat_lit 3841917883) (nat_lit 0) D2M8K2.t1301 from rfl, allE_node, rows1300, irow1296, rows1301]
  all_goals rfl

theorem atot1296 : totK PD2M8K2 D2M8K2.u1296 = [0, 136198339934, 735790288369, 768441945385, 104309358406, 1239866073, 0, 0] := by
  rw [show D2M8K2.u1296 = KTree.node D2M8K2.t1300 (nat_lit 2635304) (nat_lit 3841917883) (nat_lit 0) D2M8K2.t1301 from rfl, totK_node, tot1300, tot1301]
  decide +kernel

theorem arows1297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1297 = true := by
  rw [show D2M8K2.u1297 = KTree.node D2M8K2.t1302 (nat_lit 2637818) (nat_lit 4242684642) (nat_lit 0) D2M8K2.t1303 from rfl, allE_node, rows1302, irow1297, rows1303]
  all_goals rfl

theorem atot1297 : totK PD2M8K2 D2M8K2.u1297 = [0, 371304189869, 914324037013, 499788478683, 43811904930, 0, 0, 0] := by
  rw [show D2M8K2.u1297 = KTree.node D2M8K2.t1302 (nat_lit 2637818) (nat_lit 4242684642) (nat_lit 0) D2M8K2.t1303 from rfl, totK_node, tot1302, tot1303]
  decide +kernel

theorem arows1300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1300 = true := by
  rw [show D2M8K2.u1300 = KTree.node D2M8K2.t1304 (nat_lit 2644302) (nat_lit 3873074325) (nat_lit 0) D2M8K2.t1305 from rfl, allE_node, rows1304, irow1300, rows1305]
  all_goals rfl

theorem atot1300 : totK PD2M8K2 D2M8K2.u1300 = [0, 360000722072, 917770858601, 492865021986, 39976398648, 0, 0, 0] := by
  rw [show D2M8K2.u1300 = KTree.node D2M8K2.t1304 (nat_lit 2644302) (nat_lit 3873074325) (nat_lit 0) D2M8K2.t1305 from rfl, totK_node, tot1304, tot1305]
  decide +kernel

theorem arows1301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1301 = true := by
  rw [show D2M8K2.u1301 = KTree.node D2M8K2.t1306 (nat_lit 2645760) (nat_lit 3269460744) (nat_lit 0) D2M8K2.t1307 from rfl, allE_node, rows1306, irow1301, rows1307]
  all_goals rfl

theorem atot1301 : totK PD2M8K2 D2M8K2.u1301 = [0, 88698579362, 628184792653, 815742526515, 208713849799, 9633262574, 0, 0] := by
  rw [show D2M8K2.u1301 = KTree.node D2M8K2.t1306 (nat_lit 2645760) (nat_lit 3269460744) (nat_lit 0) D2M8K2.t1307 from rfl, totK_node, tot1306, tot1307]
  decide +kernel

theorem arows1303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1303 = true := by
  rw [show D2M8K2.u1303 = KTree.node D2M8K2.t1308 (nat_lit 2647669) (nat_lit 1096257171) (nat_lit 0) D2M8K2.t1309 from rfl, allE_node, rows1308, irow1303, rows1309]
  all_goals rfl

theorem atot1303 : totK PD2M8K2 D2M8K2.u1303 = [0, 306293103750, 817054070794, 562932456365, 99591909178, 3472187823, 0, 0] := by
  rw [show D2M8K2.u1303 = KTree.node D2M8K2.t1308 (nat_lit 2647669) (nat_lit 1096257171) (nat_lit 0) D2M8K2.t1309 from rfl, totK_node, tot1308, tot1309]
  decide +kernel

theorem arows1304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1304 = true := by
  rw [show D2M8K2.u1304 = KTree.node D2M8K2.t1310 (nat_lit 2649993) (nat_lit 1907098634) (nat_lit 0) D2M8K2.t1311 from rfl, allE_node, rows1310, irow1304, rows1311]
  all_goals rfl

theorem atot1304 : totK PD2M8K2 D2M8K2.u1304 = [0, 125627079258, 677429603128, 774114192831, 154681345152, 4720618446, 0, 0] := by
  rw [show D2M8K2.u1304 = KTree.node D2M8K2.t1310 (nat_lit 2649993) (nat_lit 1907098634) (nat_lit 0) D2M8K2.t1311 from rfl, totK_node, tot1310, tot1311]
  decide +kernel

theorem arows1309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1309 = true := by
  rw [show D2M8K2.u1309 = KTree.node D2M8K2.t1312 (nat_lit 2651700) (nat_lit 3228748430) (nat_lit 0) D2M8K2.t1313 from rfl, allE_node, rows1312, irow1309, rows1313]
  all_goals rfl

theorem atot1309 : totK PD2M8K2 D2M8K2.u1309 = [51427959908, 383115123106, 845183753168, 497094538540, 45331004983, 0, 0, 0] := by
  rw [show D2M8K2.u1309 = KTree.node D2M8K2.t1312 (nat_lit 2651700) (nat_lit 3228748430) (nat_lit 0) D2M8K2.t1313 from rfl, totK_node, tot1312, tot1313]
  decide +kernel

theorem arows1310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1310 = true := by
  rw [show D2M8K2.u1310 = KTree.node D2M8K2.t1314 (nat_lit 2696658) (nat_lit 3440007327) (nat_lit 0) D2M8K2.t1315 from rfl, allE_node, rows1314, irow1310, rows1315]
  all_goals rfl

theorem atot1310 : totK PD2M8K2 D2M8K2.u1310 = [362942625147, 956093084612, 450739898171, 23571230054, 0, 0, 0, 0] := by
  rw [show D2M8K2.u1310 = KTree.node D2M8K2.t1314 (nat_lit 2696658) (nat_lit 3440007327) (nat_lit 0) D2M8K2.t1315 from rfl, totK_node, tot1314, tot1315]
  decide +kernel

theorem arows1312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1312 = true := by
  rw [show D2M8K2.u1312 = KTree.node D2M8K2.t1316 (nat_lit 2698369) (nat_lit 1473767533) (nat_lit 0) D2M8K2.t1317 from rfl, allE_node, rows1316, irow1312, rows1317]
  all_goals rfl

theorem atot1312 : totK PD2M8K2 D2M8K2.u1312 = [92456189417, 661504557844, 898160445038, 166697627091, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u1312 = KTree.node D2M8K2.t1316 (nat_lit 2698369) (nat_lit 1473767533) (nat_lit 0) D2M8K2.t1317 from rfl, totK_node, tot1316, tot1317]
  decide +kernel

theorem arows1313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1313 = true := by
  rw [show D2M8K2.u1313 = KTree.node D2M8K2.t1318 (nat_lit 2700234) (nat_lit 3720273817) (nat_lit 0) D2M8K2.t1319 from rfl, allE_node, rows1318, irow1313, rows1319]
  all_goals rfl

theorem atot1313 : totK PD2M8K2 D2M8K2.u1313 = [315296789489, 888598190579, 554156105108, 53488314955, 0, 0, 0, 0] := by
  rw [show D2M8K2.u1313 = KTree.node D2M8K2.t1318 (nat_lit 2700234) (nat_lit 3720273817) (nat_lit 0) D2M8K2.t1319 from rfl, totK_node, tot1318, tot1319]
  decide +kernel

theorem arows1316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1316 = true := by
  rw [show D2M8K2.u1316 = KTree.node D2M8K2.t1320 (nat_lit 2701801) (nat_lit 1391289251) (nat_lit 0) D2M8K2.t1321 from rfl, allE_node, rows1320, irow1316, rows1321]
  all_goals rfl

theorem atot1316 : totK PD2M8K2 D2M8K2.u1316 = [0, 365287738542, 938267882114, 456141545198, 30201107409, 0, 0, 0] := by
  rw [show D2M8K2.u1316 = KTree.node D2M8K2.t1320 (nat_lit 2701801) (nat_lit 1391289251) (nat_lit 0) D2M8K2.t1321 from rfl, totK_node, tot1320, tot1321]
  decide +kernel

theorem arows1317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1317 = true := by
  rw [show D2M8K2.u1317 = KTree.node D2M8K2.t1322 (nat_lit 2703138) (nat_lit 2055774313) (nat_lit 0) D2M8K2.t1323 from rfl, allE_node, rows1322, irow1317, rows1323]
  all_goals rfl

theorem atot1317 : totK PD2M8K2 D2M8K2.u1317 = [358626690463, 875640920107, 468038214829, 80910079996, 5618966238, 0, 0, 0] := by
  rw [show D2M8K2.u1317 = KTree.node D2M8K2.t1322 (nat_lit 2703138) (nat_lit 2055774313) (nat_lit 0) D2M8K2.t1323 from rfl, totK_node, tot1322, tot1323]
  decide +kernel

theorem arows1319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1319 = true := by
  rw [show D2M8K2.u1319 = KTree.node D2M8K2.t1324 (nat_lit 2704700) (nat_lit 2076015635) (nat_lit 0) D2M8K2.t1325 from rfl, allE_node, rows1324, irow1319, rows1325]
  all_goals rfl

theorem atot1319 : totK PD2M8K2 D2M8K2.u1319 = [60585930939, 540863115782, 887663102613, 271568200914, 13020426360, 0, 0, 0] := by
  rw [show D2M8K2.u1319 = KTree.node D2M8K2.t1324 (nat_lit 2704700) (nat_lit 2076015635) (nat_lit 0) D2M8K2.t1325 from rfl, totK_node, tot1324, tot1325]
  decide +kernel

theorem arows1320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1320 = true := by
  rw [show D2M8K2.u1320 = KTree.node D2M8K2.t1326 (nat_lit 2706530) (nat_lit 4068535004) (nat_lit 0) D2M8K2.t1327 from rfl, allE_node, rows1326, irow1320, rows1327]
  all_goals rfl

theorem atot1320 : totK PD2M8K2 D2M8K2.u1320 = [329524497426, 887651665804, 538669452115, 55321489653, 0, 0, 0, 0] := by
  rw [show D2M8K2.u1320 = KTree.node D2M8K2.t1326 (nat_lit 2706530) (nat_lit 4068535004) (nat_lit 0) D2M8K2.t1327 from rfl, totK_node, tot1326, tot1327]
  decide +kernel

theorem arows1324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1324 = true := by
  rw [show D2M8K2.u1324 = KTree.node D2M8K2.t1328 (nat_lit 2708093) (nat_lit 2075984595) (nat_lit 0) D2M8K2.t1329 from rfl, allE_node, rows1328, irow1324, rows1329]
  all_goals rfl

theorem atot1324 : totK PD2M8K2 D2M8K2.u1324 = [89913192444, 588007252165, 860501594625, 240185018001, 10663791286, 0, 0, 0] := by
  rw [show D2M8K2.u1324 = KTree.node D2M8K2.t1328 (nat_lit 2708093) (nat_lit 2075984595) (nat_lit 0) D2M8K2.t1329 from rfl, totK_node, tot1328, tot1329]
  decide +kernel

theorem arows1325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1325 = true := by
  rw [show D2M8K2.u1325 = KTree.node D2M8K2.t1330 (nat_lit 2713349) (nat_lit 2218029550) (nat_lit 0) D2M8K2.t1331 from rfl, allE_node, rows1330, irow1325, rows1331]
  all_goals rfl

theorem atot1325 : totK PD2M8K2 D2M8K2.u1325 = [320649576768, 853100221645, 566507890126, 96309086630, 2552562263, 0, 0, 0] := by
  rw [show D2M8K2.u1325 = KTree.node D2M8K2.t1330 (nat_lit 2713349) (nat_lit 2218029550) (nat_lit 0) D2M8K2.t1331 from rfl, totK_node, tot1330, tot1331]
  decide +kernel

theorem arows1327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1327 = true := by
  rw [show D2M8K2.u1327 = KTree.node D2M8K2.t1332 (nat_lit 2714782) (nat_lit 3757582209) (nat_lit 0) D2M8K2.t1333 from rfl, allE_node, rows1332, irow1327, rows1333]
  all_goals rfl

theorem atot1327 : totK PD2M8K2 D2M8K2.u1327 = [127001226279, 651910116020, 824797712376, 206747145821, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u1327 = KTree.node D2M8K2.t1332 (nat_lit 2714782) (nat_lit 3757582209) (nat_lit 0) D2M8K2.t1333 from rfl, totK_node, tot1332, tot1333]
  decide +kernel

theorem arows1328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1328 = true := by
  rw [show D2M8K2.u1328 = KTree.node D2M8K2.t1334 (nat_lit 2716427) (nat_lit 2925092234) (nat_lit 0) D2M8K2.t1335 from rfl, allE_node, rows1334, irow1328, rows1335]
  all_goals rfl

theorem atot1328 : totK PD2M8K2 D2M8K2.u1328 = [0, 400706489629, 956817658355, 414291380768, 22416853141, 0, 0, 0] := by
  rw [show D2M8K2.u1328 = KTree.node D2M8K2.t1334 (nat_lit 2716427) (nat_lit 2925092234) (nat_lit 0) D2M8K2.t1335 from rfl, totK_node, tot1334, tot1335]
  decide +kernel

theorem arows1331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1331 = true := by
  rw [show D2M8K2.u1331 = KTree.node D2M8K2.t1336 (nat_lit 2718027) (nat_lit 3558944539) (nat_lit 0) D2M8K2.t1337 from rfl, allE_node, rows1336, irow1331, rows1337]
  all_goals rfl

theorem atot1331 : totK PD2M8K2 D2M8K2.u1331 = [0, 192768216010, 774249528066, 699049108386, 98005691399, 1310285577, 0, 0] := by
  rw [show D2M8K2.u1331 = KTree.node D2M8K2.t1336 (nat_lit 2718027) (nat_lit 3558944539) (nat_lit 0) D2M8K2.t1337 from rfl, totK_node, tot1336, tot1337]
  decide +kernel

theorem arows1332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1332 = true := by
  rw [show D2M8K2.u1332 = KTree.node D2M8K2.t1338 (nat_lit 2720390) (nat_lit 3911505399) (nat_lit 0) D2M8K2.t1339 from rfl, allE_node, rows1338, irow1332, rows1339]
  all_goals rfl

theorem atot1332 : totK PD2M8K2 D2M8K2.u1332 = [0, 263674928341, 831232941954, 646548403121, 63072035752, 0, 0, 0] := by
  rw [show D2M8K2.u1332 = KTree.node D2M8K2.t1338 (nat_lit 2720390) (nat_lit 3911505399) (nat_lit 0) D2M8K2.t1339 from rfl, totK_node, tot1338, tot1339]
  decide +kernel

theorem arows1334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1334 = true := by
  rw [show D2M8K2.u1334 = KTree.node D2M8K2.t1340 (nat_lit 2723425) (nat_lit 1495221535) (nat_lit 0) D2M8K2.t1341 from rfl, allE_node, rows1340, irow1334, rows1341]
  all_goals rfl

theorem atot1334 : totK PD2M8K2 D2M8K2.u1334 = [0, 381995256664, 929650731481, 468987450821, 35219752488, 0, 0, 0] := by
  rw [show D2M8K2.u1334 = KTree.node D2M8K2.t1340 (nat_lit 2723425) (nat_lit 1495221535) (nat_lit 0) D2M8K2.t1341 from rfl, totK_node, tot1340, tot1341]
  decide +kernel

theorem arows1335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1335 = true := by
  rw [show D2M8K2.u1335 = KTree.node D2M8K2.t1342 (nat_lit 2724940) (nat_lit 3839840330) (nat_lit 0) D2M8K2.t1343 from rfl, allE_node, rows1342, irow1335, rows1343]
  all_goals rfl

theorem atot1335 : totK PD2M8K2 D2M8K2.u1335 = [0, 177465433587, 771858085081, 718093163735, 99718000647, 1075657031, 0, 0] := by
  rw [show D2M8K2.u1335 = KTree.node D2M8K2.t1342 (nat_lit 2724940) (nat_lit 3839840330) (nat_lit 0) D2M8K2.t1343 from rfl, totK_node, tot1342, tot1343]
  decide +kernel

theorem arows1341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1341 = true := by
  rw [show D2M8K2.u1341 = KTree.node D2M8K2.t1344 (nat_lit 2727000) (nat_lit 3578061234) (nat_lit 0) D2M8K2.t1345 from rfl, allE_node, rows1344, irow1341, rows1345]
  all_goals rfl

theorem atot1341 : totK PD2M8K2 D2M8K2.u1341 = [0, 262322408045, 787710730147, 614060958587, 114357670622, 3804183361, 0, 0] := by
  rw [show D2M8K2.u1341 = KTree.node D2M8K2.t1344 (nat_lit 2727000) (nat_lit 3578061234) (nat_lit 0) D2M8K2.t1345 from rfl, totK_node, tot1344, tot1345]
  decide +kernel

theorem arows1342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1342 = true := by
  rw [show D2M8K2.u1342 = KTree.node D2M8K2.t1346 (nat_lit 2728513) (nat_lit 1573092198) (nat_lit 0) D2M8K2.t1347 from rfl, allE_node, rows1346, irow1342, rows1347]
  all_goals rfl

theorem atot1342 : totK PD2M8K2 D2M8K2.u1342 = [0, 155099038844, 692399457939, 749452163912, 155564121935, 4931404646, 0, 0] := by
  rw [show D2M8K2.u1342 = KTree.node D2M8K2.t1346 (nat_lit 2728513) (nat_lit 1573092198) (nat_lit 0) D2M8K2.t1347 from rfl, totK_node, tot1346, tot1347]
  decide +kernel

theorem arows1344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1344 = true := by
  rw [show D2M8K2.u1344 = KTree.node D2M8K2.t1348 (nat_lit 2734049) (nat_lit 2192754424) (nat_lit 0) D2M8K2.t1349 from rfl, allE_node, rows1348, irow1344, rows1349]
  all_goals rfl

theorem atot1344 : totK PD2M8K2 D2M8K2.u1344 = [0, 299901607080, 868774232615, 576208889502, 63646396177, 0, 0, 0] := by
  rw [show D2M8K2.u1344 = KTree.node D2M8K2.t1348 (nat_lit 2734049) (nat_lit 2192754424) (nat_lit 0) D2M8K2.t1349 from rfl, totK_node, tot1348, tot1349]
  decide +kernel

theorem arows1345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1345 = true := by
  rw [show D2M8K2.u1345 = KTree.node D2M8K2.t1350 (nat_lit 2735486) (nat_lit 2773402861) (nat_lit 0) D2M8K2.t1351 from rfl, allE_node, rows1350, irow1345, rows1351]
  all_goals rfl

theorem atot1345 : totK PD2M8K2 D2M8K2.u1345 = [0, 145600847910, 674547579345, 779324950174, 178101295102, 4811815119, 0, 0] := by
  rw [show D2M8K2.u1345 = KTree.node D2M8K2.t1350 (nat_lit 2735486) (nat_lit 2773402861) (nat_lit 0) D2M8K2.t1351 from rfl, totK_node, tot1350, tot1351]
  decide +kernel

theorem arows1348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1348 = true := by
  rw [show D2M8K2.u1348 = KTree.node D2M8K2.t1352 (nat_lit 2737170) (nat_lit 3411630878) (nat_lit 0) D2M8K2.t1353 from rfl, allE_node, rows1352, irow1348, rows1353]
  all_goals rfl

theorem atot1348 : totK PD2M8K2 D2M8K2.u1348 = [0, 218815971136, 685324312304, 642159400771, 220526768209, 16939352947, 0, 0] := by
  rw [show D2M8K2.u1348 = KTree.node D2M8K2.t1352 (nat_lit 2737170) (nat_lit 3411630878) (nat_lit 0) D2M8K2.t1353 from rfl, totK_node, tot1352, tot1353]
  decide +kernel

theorem arows1349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1349 = true := by
  rw [show D2M8K2.u1349 = KTree.node D2M8K2.t1354 (nat_lit 2738677) (nat_lit 1248354771) (nat_lit 0) D2M8K2.t1355 from rfl, allE_node, rows1354, irow1349, rows1355]
  all_goals rfl

theorem atot1349 : totK PD2M8K2 D2M8K2.u1349 = [0, 218693695314, 780101698602, 683934759670, 112483058901, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1349 = KTree.node D2M8K2.t1354 (nat_lit 2738677) (nat_lit 1248354771) (nat_lit 0) D2M8K2.t1355 from rfl, totK_node, tot1354, tot1355]
  decide +kernel

theorem arows1351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1351 = true := by
  rw [show D2M8K2.u1351 = KTree.node D2M8K2.t1356 (nat_lit 2744194) (nat_lit 4106662005) (nat_lit 0) D2M8K2.t1357 from rfl, allE_node, rows1356, irow1351, rows1357]
  all_goals rfl

theorem atot1351 : totK PD2M8K2 D2M8K2.u1351 = [0, 246685655312, 833300806439, 668953431760, 70624634127, 0, 0, 0] := by
  rw [show D2M8K2.u1351 = KTree.node D2M8K2.t1356 (nat_lit 2744194) (nat_lit 4106662005) (nat_lit 0) D2M8K2.t1357 from rfl, totK_node, tot1356, tot1357]
  decide +kernel

theorem arows1352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1352 = true := by
  rw [show D2M8K2.u1352 = KTree.node D2M8K2.t1358 (nat_lit 2745738) (nat_lit 3438012515) (nat_lit 0) D2M8K2.t1359 from rfl, allE_node, rows1358, irow1352, rows1359]
  all_goals rfl

theorem atot1352 : totK PD2M8K2 D2M8K2.u1352 = [0, 166010054258, 717346132033, 759083864597, 138141794582, 1164319620, 0, 0] := by
  rw [show D2M8K2.u1352 = KTree.node D2M8K2.t1358 (nat_lit 2745738) (nat_lit 3438012515) (nat_lit 0) D2M8K2.t1359 from rfl, totK_node, tot1358, tot1359]
  decide +kernel

theorem arows1356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1356 = true := by
  rw [show D2M8K2.u1356 = KTree.node D2M8K2.t1360 (nat_lit 2747743) (nat_lit 2391681949) (nat_lit 0) D2M8K2.t1361 from rfl, allE_node, rows1360, irow1356, rows1361]
  all_goals rfl

theorem atot1356 : totK PD2M8K2 D2M8K2.u1356 = [0, 246837716434, 786894500671, 647129016595, 116810052147, 2896345377, 0, 0] := by
  rw [show D2M8K2.u1356 = KTree.node D2M8K2.t1360 (nat_lit 2747743) (nat_lit 2391681949) (nat_lit 0) D2M8K2.t1361 from rfl, totK_node, tot1360, tot1361]
  decide +kernel

theorem arows1357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1357 = true := by
  rw [show D2M8K2.u1357 = KTree.node D2M8K2.t1362 (nat_lit 2749300) (nat_lit 3761243235) (nat_lit 0) D2M8K2.t1363 from rfl, allE_node, rows1362, irow1357, rows1363]
  all_goals rfl

theorem atot1357 : totK PD2M8K2 D2M8K2.u1357 = [0, 166086246454, 671350277824, 754356428463, 180216996447, 5228939780, 0, 0] := by
  rw [show D2M8K2.u1357 = KTree.node D2M8K2.t1362 (nat_lit 2749300) (nat_lit 3761243235) (nat_lit 0) D2M8K2.t1363 from rfl, totK_node, tot1362, tot1363]
  decide +kernel

theorem arows1359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1359 = true := by
  rw [show D2M8K2.u1359 = KTree.node D2M8K2.t1364 (nat_lit 2751564) (nat_lit 3550057930) (nat_lit 0) D2M8K2.t1365 from rfl, allE_node, rows1364, irow1359, rows1365]
  all_goals rfl

theorem atot1359 : totK PD2M8K2 D2M8K2.u1359 = [0, 289235888417, 857565528300, 576870918820, 65276188768, 0, 0, 0] := by
  rw [show D2M8K2.u1359 = KTree.node D2M8K2.t1364 (nat_lit 2751564) (nat_lit 3550057930) (nat_lit 0) D2M8K2.t1365 from rfl, totK_node, tot1364, tot1365]
  decide +kernel

theorem arows1360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1360 = true := by
  rw [show D2M8K2.u1360 = KTree.node D2M8K2.t1366 (nat_lit 2753569) (nat_lit 1545512104) (nat_lit 0) D2M8K2.t1367 from rfl, allE_node, rows1366, irow1360, rows1367]
  all_goals rfl

theorem atot1360 : totK PD2M8K2 D2M8K2.u1360 = [0, 160890602404, 759245363416, 764385143358, 103791088646, 1096505104, 0, 0] := by
  rw [show D2M8K2.u1360 = KTree.node D2M8K2.t1366 (nat_lit 2753569) (nat_lit 1545512104) (nat_lit 0) D2M8K2.t1367 from rfl, totK_node, tot1366, tot1367]
  decide +kernel

theorem arows1363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1363 = true := by
  rw [show D2M8K2.u1363 = KTree.node D2M8K2.t1368 (nat_lit 2755377) (nat_lit 1760982295) (nat_lit 0) D2M8K2.t1369 from rfl, allE_node, rows1368, irow1363, rows1369]
  all_goals rfl

theorem atot1363 : totK PD2M8K2 D2M8K2.u1363 = [0, 314298660944, 891686780241, 561316507265, 49742541189, 0, 0, 0] := by
  rw [show D2M8K2.u1363 = KTree.node D2M8K2.t1368 (nat_lit 2755377) (nat_lit 1760982295) (nat_lit 0) D2M8K2.t1369 from rfl, totK_node, tot1368, tot1369]
  decide +kernel

theorem arows1364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1364 = true := by
  rw [show D2M8K2.u1364 = KTree.node D2M8K2.t1370 (nat_lit 2757033) (nat_lit 1664204770) (nat_lit 0) D2M8K2.t1371 from rfl, allE_node, rows1370, irow1364, rows1371]
  all_goals rfl

theorem atot1364 : totK PD2M8K2 D2M8K2.u1364 = [0, 0, 396740606984, 956677372958, 387052703971, 21916389073, 0, 0] := by
  rw [show D2M8K2.u1364 = KTree.node D2M8K2.t1370 (nat_lit 2757033) (nat_lit 1664204770) (nat_lit 0) D2M8K2.t1371 from rfl, totK_node, tot1370, tot1371]
  decide +kernel

theorem arows1366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1366 = true := by
  rw [show D2M8K2.u1366 = KTree.node D2M8K2.t1372 (nat_lit 2758845) (nat_lit 1521701831) (nat_lit 0) D2M8K2.t1373 from rfl, allE_node, rows1372, irow1366, rows1373]
  all_goals rfl

theorem atot1366 : totK PD2M8K2 D2M8K2.u1366 = [0, 0, 413423582547, 986122535095, 355919362219, 10449776702, 0, 0] := by
  rw [show D2M8K2.u1366 = KTree.node D2M8K2.t1372 (nat_lit 2758845) (nat_lit 1521701831) (nat_lit 0) D2M8K2.t1373 from rfl, totK_node, tot1372, tot1373]
  decide +kernel

theorem arows1367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1367 = true := by
  rw [show D2M8K2.u1367 = KTree.node D2M8K2.t1374 (nat_lit 2760564) (nat_lit 3244651262) (nat_lit 0) D2M8K2.t1375 from rfl, allE_node, rows1374, irow1367, rows1375]
  all_goals rfl

theorem atot1367 : totK PD2M8K2 D2M8K2.u1367 = [0, 0, 86929735316, 706049536495, 791332192100, 117067624744, 1369150432, 0] := by
  rw [show D2M8K2.u1367 = KTree.node D2M8K2.t1374 (nat_lit 2760564) (nat_lit 3244651262) (nat_lit 0) D2M8K2.t1375 from rfl, totK_node, tot1374, tot1375]
  decide +kernel

theorem arows1372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1372 = true := by
  rw [show D2M8K2.u1372 = KTree.node D2M8K2.t1376 (nat_lit 2766025) (nat_lit 1440812969) (nat_lit 0) D2M8K2.t1377 from rfl, allE_node, rows1376, irow1372, rows1377]
  all_goals rfl

theorem atot1372 : totK PD2M8K2 D2M8K2.u1372 = [0, 0, 412066195397, 970665794501, 377556306405, 15269130972, 0, 0] := by
  rw [show D2M8K2.u1372 = KTree.node D2M8K2.t1376 (nat_lit 2766025) (nat_lit 1440812969) (nat_lit 0) D2M8K2.t1377 from rfl, totK_node, tot1376, tot1377]
  decide +kernel

theorem arows1373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1373 = true := by
  rw [show D2M8K2.u1373 = KTree.node D2M8K2.t1378 (nat_lit 2769416) (nat_lit 3690024426) (nat_lit 0) D2M8K2.t1379 from rfl, allE_node, rows1378, irow1373, rows1379]
  all_goals rfl

theorem atot1373 : totK PD2M8K2 D2M8K2.u1373 = [0, 0, 379408662000, 965201376411, 411051905829, 16674958387, 0, 0] := by
  rw [show D2M8K2.u1373 = KTree.node D2M8K2.t1378 (nat_lit 2769416) (nat_lit 3690024426) (nat_lit 0) D2M8K2.t1379 from rfl, totK_node, tot1378, tot1379]
  decide +kernel

theorem arows1375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1375 = true := by
  rw [show D2M8K2.u1375 = KTree.node D2M8K2.t1380 (nat_lit 2772733) (nat_lit 1182025416) (nat_lit 0) D2M8K2.t1381 from rfl, allE_node, rows1380, irow1375, rows1381]
  all_goals rfl

theorem atot1375 : totK PD2M8K2 D2M8K2.u1375 = [0, 0, 381308172681, 1008015668372, 356556560499, 6148887605, 0, 0] := by
  rw [show D2M8K2.u1375 = KTree.node D2M8K2.t1380 (nat_lit 2772733) (nat_lit 1182025416) (nat_lit 0) D2M8K2.t1381 from rfl, totK_node, tot1380, tot1381]
  decide +kernel

theorem arows1376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1376 = true := by
  rw [show D2M8K2.u1376 = KTree.node D2M8K2.t1382 (nat_lit 2776113) (nat_lit 1752715296) (nat_lit 0) D2M8K2.t1383 from rfl, allE_node, rows1382, irow1376, rows1383]
  all_goals rfl

theorem atot1376 : totK PD2M8K2 D2M8K2.u1376 = [0, 53299326172, 398563743756, 869427649037, 435888044652, 28192849651, 0, 0] := by
  rw [show D2M8K2.u1376 = KTree.node D2M8K2.t1382 (nat_lit 2776113) (nat_lit 1752715296) (nat_lit 0) D2M8K2.t1383 from rfl, totK_node, tot1382, tot1383]
  decide +kernel

theorem arows1379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1379 = true := by
  rw [show D2M8K2.u1379 = KTree.node D2M8K2.t1384 (nat_lit 2783016) (nat_lit 3321026781) (nat_lit 0) D2M8K2.t1385 from rfl, allE_node, rows1384, irow1379, rows1385]
  all_goals rfl

theorem atot1379 : totK PD2M8K2 D2M8K2.u1379 = [0, 373515854198, 930679280850, 486089695877, 40281102770, 0, 0, 0] := by
  rw [show D2M8K2.u1379 = KTree.node D2M8K2.t1384 (nat_lit 2783016) (nat_lit 3321026781) (nat_lit 0) D2M8K2.t1385 from rfl, totK_node, tot1384, tot1385]
  decide +kernel

theorem arows1380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1380 = true := by
  rw [show D2M8K2.u1380 = KTree.node D2M8K2.t1386 (nat_lit 2784485) (nat_lit 2338578389) (nat_lit 0) D2M8K2.t1387 from rfl, allE_node, rows1386, irow1380, rows1387]
  all_goals rfl

theorem atot1380 : totK PD2M8K2 D2M8K2.u1380 = [0, 0, 443776968230, 931228225193, 403672130971, 29308803096, 0, 0] := by
  rw [show D2M8K2.u1380 = KTree.node D2M8K2.t1386 (nat_lit 2784485) (nat_lit 2338578389) (nat_lit 0) D2M8K2.t1387 from rfl, totK_node, tot1386, tot1387]
  decide +kernel

theorem arows1382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1382 = true := by
  rw [show D2M8K2.u1382 = KTree.node D2M8K2.t1388 (nat_lit 2785875) (nat_lit 3710099078) (nat_lit 0) D2M8K2.t1389 from rfl, allE_node, rows1388, irow1382, rows1389]
  all_goals rfl

theorem atot1382 : totK PD2M8K2 D2M8K2.u1382 = [0, 260359755693, 733089320102, 625513015945, 187293917556, 8191853852, 0, 0] := by
  rw [show D2M8K2.u1382 = KTree.node D2M8K2.t1388 (nat_lit 2785875) (nat_lit 3710099078) (nat_lit 0) D2M8K2.t1389 from rfl, totK_node, tot1388, tot1389]
  decide +kernel

theorem arows1383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1383 = true := by
  rw [show D2M8K2.u1383 = KTree.node D2M8K2.t1390 (nat_lit 2787391) (nat_lit 1656281209) (nat_lit 0) D2M8K2.t1391 from rfl, allE_node, rows1390, irow1383, rows1391]
  all_goals rfl

theorem atot1383 : totK PD2M8K2 D2M8K2.u1383 = [0, 142895473479, 662819257282, 777550852053, 205184842452, 7877773091, 0, 0] := by
  rw [show D2M8K2.u1383 = KTree.node D2M8K2.t1390 (nat_lit 2787391) (nat_lit 1656281209) (nat_lit 0) D2M8K2.t1391 from rfl, totK_node, tot1390, tot1391]
  decide +kernel

theorem arows1387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1387 = true := by
  rw [show D2M8K2.u1387 = KTree.node D2M8K2.t1392 (nat_lit 2789363) (nat_lit 2837775339) (nat_lit 0) D2M8K2.t1393 from rfl, allE_node, rows1392, irow1387, rows1393]
  all_goals rfl

theorem atot1387 : totK PD2M8K2 D2M8K2.u1387 = [0, 279110491195, 804364625200, 628697804692, 105880921752, 1189976475, 0, 0] := by
  rw [show D2M8K2.u1387 = KTree.node D2M8K2.t1392 (nat_lit 2789363) (nat_lit 2837775339) (nat_lit 0) D2M8K2.t1393 from rfl, totK_node, tot1392, tot1393]
  decide +kernel

theorem arows1388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1388 = true := by
  rw [show D2M8K2.u1388 = KTree.node D2M8K2.t1394 (nat_lit 2790875) (nat_lit 2143938983) (nat_lit 0) D2M8K2.t1395 from rfl, allE_node, rows1394, irow1388, rows1395]
  all_goals rfl

theorem atot1388 : totK PD2M8K2 D2M8K2.u1388 = [0, 124404585768, 650137097661, 796403423700, 215630440771, 7947699043, 0, 0] := by
  rw [show D2M8K2.u1388 = KTree.node D2M8K2.t1394 (nat_lit 2790875) (nat_lit 2143938983) (nat_lit 0) D2M8K2.t1395 from rfl, totK_node, tot1394, tot1395]
  decide +kernel

theorem arows1390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1390 = true := by
  rw [show D2M8K2.u1390 = KTree.node D2M8K2.t1396 (nat_lit 2796284) (nat_lit 3120573343) (nat_lit 0) D2M8K2.t1397 from rfl, allE_node, rows1396, irow1390, rows1397]
  all_goals rfl

theorem atot1390 : totK PD2M8K2 D2M8K2.u1390 = [0, 302756783482, 811298797263, 601479786159, 104578649489, 1231290674, 0, 0] := by
  rw [show D2M8K2.u1390 = KTree.node D2M8K2.t1396 (nat_lit 2796284) (nat_lit 3120573343) (nat_lit 0) D2M8K2.t1397 from rfl, totK_node, tot1396, tot1397]
  decide +kernel

theorem arows1391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1391 = true := by
  rw [show D2M8K2.u1391 = KTree.node D2M8K2.t1398 (nat_lit 2797715) (nat_lit 2863616273) (nat_lit 0) D2M8K2.t1399 from rfl, allE_node, rows1398, irow1391, rows1399]
  all_goals rfl

theorem atot1391 : totK PD2M8K2 D2M8K2.u1391 = [0, 125368878271, 653795942006, 805754824866, 198894859252, 4903313894, 0, 0] := by
  rw [show D2M8K2.u1391 = KTree.node D2M8K2.t1398 (nat_lit 2797715) (nat_lit 2863616273) (nat_lit 0) D2M8K2.t1399 from rfl, totK_node, tot1398, tot1399]
  decide +kernel

theorem arows1394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1394 = true := by
  rw [show D2M8K2.u1394 = KTree.node D2M8K2.t1400 (nat_lit 2820154) (nat_lit 3892781461) (nat_lit 0) D2M8K2.t1401 from rfl, allE_node, rows1400, irow1394, rows1401]
  all_goals rfl

theorem atot1394 : totK PD2M8K2 D2M8K2.u1394 = [0, 227577009774, 690935139787, 630928927814, 227006577671, 17027268164, 0, 0] := by
  rw [show D2M8K2.u1394 = KTree.node D2M8K2.t1400 (nat_lit 2820154) (nat_lit 3892781461) (nat_lit 0) D2M8K2.t1401 from rfl, totK_node, tot1400, tot1401]
  decide +kernel

theorem arows1395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1395 = true := by
  rw [show D2M8K2.u1395 = KTree.node D2M8K2.t1402 (nat_lit 2821733) (nat_lit 2366347851) (nat_lit 0) D2M8K2.t1403 from rfl, allE_node, rows1402, irow1395, rows1403]
  all_goals rfl

theorem atot1395 : totK PD2M8K2 D2M8K2.u1395 = [0, 178884983718, 748063463861, 728582814535, 114231047278, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1395 = KTree.node D2M8K2.t1402 (nat_lit 2821733) (nat_lit 2366347851) (nat_lit 0) D2M8K2.t1403 from rfl, totK_node, tot1402, tot1403]
  decide +kernel

theorem arows1397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1397 = true := by
  rw [show D2M8K2.u1397 = KTree.node D2M8K2.t1404 (nat_lit 2824084) (nat_lit 3773102988) (nat_lit 0) D2M8K2.t1405 from rfl, allE_node, rows1404, irow1397, rows1405]
  all_goals rfl

theorem atot1397 : totK PD2M8K2 D2M8K2.u1397 = [0, 282165438426, 836961406654, 640733851774, 69762835145, 0, 0, 0] := by
  rw [show D2M8K2.u1397 = KTree.node D2M8K2.t1404 (nat_lit 2824084) (nat_lit 3773102988) (nat_lit 0) D2M8K2.t1405 from rfl, totK_node, tot1404, tot1405]
  decide +kernel

theorem arows1398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1398 = true := by
  rw [show D2M8K2.u1398 = KTree.node D2M8K2.t1406 (nat_lit 2825710) (nat_lit 4019397726) (nat_lit 0) D2M8K2.t1407 from rfl, allE_node, rows1406, irow1398, rows1407]
  all_goals rfl

theorem atot1398 : totK PD2M8K2 D2M8K2.u1398 = [0, 105805967407, 567103482309, 774414718826, 330612649232, 24691320395, 0, 0] := by
  rw [show D2M8K2.u1398 = KTree.node D2M8K2.t1406 (nat_lit 2825710) (nat_lit 4019397726) (nat_lit 0) D2M8K2.t1407 from rfl, totK_node, tot1406, tot1407]
  decide +kernel

theorem arows1405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1405 = true := by
  rw [show D2M8K2.u1405 = KTree.node D2M8K2.t1408 (nat_lit 2827109) (nat_lit 2311029913) (nat_lit 0) D2M8K2.t1409 from rfl, allE_node, rows1408, irow1405, rows1409]
  all_goals rfl

theorem atot1405 : totK PD2M8K2 D2M8K2.u1405 = [0, 247667132635, 694387166980, 654816567476, 209620466107, 8073511420, 0, 0] := by
  rw [show D2M8K2.u1405 = KTree.node D2M8K2.t1408 (nat_lit 2827109) (nat_lit 2311029913) (nat_lit 0) D2M8K2.t1409 from rfl, totK_node, tot1408, tot1409]
  decide +kernel

theorem arows1406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1406 = true := by
  rw [show D2M8K2.u1406 = KTree.node D2M8K2.t1410 (nat_lit 2828585) (nat_lit 1627056749) (nat_lit 0) D2M8K2.t1411 from rfl, allE_node, rows1410, irow1406, rows1411]
  all_goals rfl

theorem atot1406 : totK PD2M8K2 D2M8K2.u1406 = [0, 190126444849, 775637255538, 713539342379, 112310524576, 1164319620, 0, 0] := by
  rw [show D2M8K2.u1406 = KTree.node D2M8K2.t1410 (nat_lit 2828585) (nat_lit 1627056749) (nat_lit 0) D2M8K2.t1411 from rfl, totK_node, tot1410, tot1411]
  decide +kernel

theorem arows1408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1408 = true := by
  rw [show D2M8K2.u1408 = KTree.node D2M8K2.t1412 (nat_lit 2830244) (nat_lit 2765612718) (nat_lit 0) D2M8K2.t1413 from rfl, allE_node, rows1412, irow1408, rows1413]
  all_goals rfl

theorem atot1408 : totK PD2M8K2 D2M8K2.u1408 = [0, 182857076785, 650214628379, 723700229438, 215923783618, 11885407614, 0, 0] := by
  rw [show D2M8K2.u1408 = KTree.node D2M8K2.t1412 (nat_lit 2830244) (nat_lit 2765612718) (nat_lit 0) D2M8K2.t1413 from rfl, totK_node, tot1412, tot1413]
  decide +kernel

theorem arows1409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1409 = true := by
  rw [show D2M8K2.u1409 = KTree.node D2M8K2.t1414 (nat_lit 2835733) (nat_lit 1206690591) (nat_lit 0) D2M8K2.t1415 from rfl, allE_node, rows1414, irow1409, rows1415]
  all_goals rfl

theorem atot1409 : totK PD2M8K2 D2M8K2.u1409 = [0, 139006180021, 729535078851, 791787237483, 119777905158, 1062926506, 0, 0] := by
  rw [show D2M8K2.u1409 = KTree.node D2M8K2.t1414 (nat_lit 2835733) (nat_lit 1206690591) (nat_lit 0) D2M8K2.t1415 from rfl, totK_node, tot1414, tot1415]
  decide +kernel

theorem arows1412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1412 = true := by
  rw [show D2M8K2.u1412 = KTree.node D2M8K2.t1416 (nat_lit 2837892) (nat_lit 1034918011) (nat_lit 0) D2M8K2.t1417 from rfl, allE_node, rows1416, irow1412, rows1417]
  all_goals rfl

theorem atot1412 : totK PD2M8K2 D2M8K2.u1412 = [0, 336573609935, 853641620528, 514944101574, 86615661967, 3720136285, 0, 0] := by
  rw [show D2M8K2.u1412 = KTree.node D2M8K2.t1416 (nat_lit 2837892) (nat_lit 1034918011) (nat_lit 0) D2M8K2.t1417 from rfl, totK_node, tot1416, tot1417]
  decide +kernel

theorem arows1413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1413 = true := by
  rw [show D2M8K2.u1413 = KTree.node D2M8K2.t1418 (nat_lit 2839436) (nat_lit 3504341289) (nat_lit 0) D2M8K2.t1419 from rfl, allE_node, rows1418, irow1413, rows1419]
  all_goals rfl

theorem atot1413 : totK PD2M8K2 D2M8K2.u1413 = [0, 89222919167, 567992935918, 870140701629, 251263909497, 6013758163, 0, 0] := by
  rw [show D2M8K2.u1413 = KTree.node D2M8K2.t1418 (nat_lit 2839436) (nat_lit 3504341289) (nat_lit 0) D2M8K2.t1419 from rfl, totK_node, tot1418, tot1419]
  decide +kernel

theorem arows1415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1415 = true := by
  rw [show D2M8K2.u1415 = KTree.node D2M8K2.t1420 (nat_lit 2841081) (nat_lit 1853318607) (nat_lit 0) D2M8K2.t1421 from rfl, allE_node, rows1420, irow1415, rows1421]
  all_goals rfl

theorem atot1415 : totK PD2M8K2 D2M8K2.u1415 = [0, 0, 394492623256, 948794044833, 399882160136, 22567903075, 0, 0] := by
  rw [show D2M8K2.u1415 = KTree.node D2M8K2.t1420 (nat_lit 2841081) (nat_lit 1853318607) (nat_lit 0) D2M8K2.t1421 from rfl, totK_node, tot1420, tot1421]
  decide +kernel

theorem arows1416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1416 = true := by
  rw [show D2M8K2.u1416 = KTree.node D2M8K2.t1422 (nat_lit 2842726) (nat_lit 2251084471) (nat_lit 0) D2M8K2.t1423 from rfl, allE_node, rows1422, irow1416, rows1423]
  all_goals rfl

theorem atot1416 : totK PD2M8K2 D2M8K2.u1416 = [0, 0, 144773706435, 777431968670, 718108555988, 83044794530, 1166720416, 0] := by
  rw [show D2M8K2.u1416 = KTree.node D2M8K2.t1422 (nat_lit 2842726) (nat_lit 2251084471) (nat_lit 0) D2M8K2.t1423 from rfl, totK_node, tot1422, tot1423]
  decide +kernel

theorem arows1420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1420 = true := by
  rw [show D2M8K2.u1420 = KTree.node D2M8K2.t1424 (nat_lit 2845466) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t1425 from rfl, allE_node, rows1424, irow1420, rows1425]
  all_goals rfl

theorem atot1420 : totK PD2M8K2 D2M8K2.u1420 = [0, 0, 430412896116, 970027566697, 397320094742, 22075222164, 0, 0] := by
  rw [show D2M8K2.u1420 = KTree.node D2M8K2.t1424 (nat_lit 2845466) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t1425 from rfl, totK_node, tot1424, tot1425]
  decide +kernel

theorem arows1421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1421 = true := by
  rw [show D2M8K2.u1421 = KTree.node D2M8K2.t1426 (nat_lit 2848585) (nat_lit 1424660951) (nat_lit 0) D2M8K2.t1427 from rfl, allE_node, rows1426, irow1421, rows1427]
  all_goals rfl

theorem atot1421 : totK PD2M8K2 D2M8K2.u1421 = [0, 0, 346181417545, 925727266324, 482873255454, 32278719857, 0, 0] := by
  rw [show D2M8K2.u1421 = KTree.node D2M8K2.t1426 (nat_lit 2848585) (nat_lit 1424660951) (nat_lit 0) D2M8K2.t1427 from rfl, totK_node, tot1426, tot1427]
  decide +kernel

theorem arows1423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1423 = true := by
  rw [show D2M8K2.u1423 = KTree.node D2M8K2.t1428 (nat_lit 2850629) (nat_lit 2299794389) (nat_lit 0) D2M8K2.t1429 from rfl, allE_node, rows1428, irow1423, rows1429]
  all_goals rfl

theorem atot1423 : totK PD2M8K2 D2M8K2.u1423 = [0, 0, 139663845658, 672672713656, 730117702874, 164048006113, 5134755853, 0] := by
  rw [show D2M8K2.u1423 = KTree.node D2M8K2.t1428 (nat_lit 2850629) (nat_lit 2299794389) (nat_lit 0) D2M8K2.t1429 from rfl, totK_node, tot1428, tot1429]
  decide +kernel

theorem arows1424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1424 = true := by
  rw [show D2M8K2.u1424 = KTree.node D2M8K2.t1430 (nat_lit 2858177) (nat_lit 2152170779) (nat_lit 0) D2M8K2.t1431 from rfl, allE_node, rows1430, irow1424, rows1431]
  all_goals rfl

theorem atot1424 : totK PD2M8K2 D2M8K2.u1424 = [0, 0, 417085054364, 954010578427, 373177443581, 18804176403, 0, 0] := by
  rw [show D2M8K2.u1424 = KTree.node D2M8K2.t1430 (nat_lit 2858177) (nat_lit 2152170779) (nat_lit 0) D2M8K2.t1431 from rfl, totK_node, tot1430, tot1431]
  decide +kernel

theorem arows1427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1427 = true := by
  rw [show D2M8K2.u1427 = KTree.node D2M8K2.t1432 (nat_lit 2859727) (nat_lit 1862675973) (nat_lit 0) D2M8K2.t1433 from rfl, allE_node, rows1432, irow1427, rows1433]
  all_goals rfl

theorem atot1427 : totK PD2M8K2 D2M8K2.u1427 = [0, 163907467286, 581208115922, 700860124997, 316011293730, 22919250980, 0, 0] := by
  rw [show D2M8K2.u1427 = KTree.node D2M8K2.t1432 (nat_lit 2859727) (nat_lit 1862675973) (nat_lit 0) D2M8K2.t1433 from rfl, totK_node, tot1432, tot1433]
  decide +kernel

theorem arows1428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1428 = true := by
  rw [show D2M8K2.u1428 = KTree.node D2M8K2.t1434 (nat_lit 2863058) (nat_lit 3234174346) (nat_lit 0) D2M8K2.t1435 from rfl, allE_node, rows1434, irow1428, rows1435]
  all_goals rfl

theorem atot1428 : totK PD2M8K2 D2M8K2.u1428 = [0, 246179701846, 789921430271, 642812497986, 101822117892, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1428 = KTree.node D2M8K2.t1434 (nat_lit 2863058) (nat_lit 3234174346) (nat_lit 0) D2M8K2.t1435 from rfl, totK_node, tot1434, tot1435]
  decide +kernel

theorem arows1430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1430 = true := by
  rw [show D2M8K2.u1430 = KTree.node D2M8K2.t1436 (nat_lit 2865424) (nat_lit 2844931994) (nat_lit 0) D2M8K2.t1437 from rfl, allE_node, rows1436, irow1430, rows1437]
  all_goals rfl

theorem atot1430 : totK PD2M8K2 D2M8K2.u1430 = [0, 234702012917, 817869838202, 708595814032, 79557903569, 0, 0, 0] := by
  rw [show D2M8K2.u1430 = KTree.node D2M8K2.t1436 (nat_lit 2865424) (nat_lit 2844931994) (nat_lit 0) D2M8K2.t1437 from rfl, totK_node, tot1436, tot1437]
  decide +kernel

theorem arows1431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1431 = true := by
  rw [show D2M8K2.u1431 = KTree.node D2M8K2.t1438 (nat_lit 2867075) (nat_lit 2848308795) (nat_lit 0) D2M8K2.t1439 from rfl, allE_node, rows1438, irow1431, rows1439]
  all_goals rfl

theorem atot1431 : totK PD2M8K2 D2M8K2.u1431 = [0, 153370728324, 648080274408, 723705783752, 264916566064, 20729740161, 0, 0] := by
  rw [show D2M8K2.u1431 = KTree.node D2M8K2.t1438 (nat_lit 2867075) (nat_lit 2848308795) (nat_lit 0) D2M8K2.t1439 from rfl, totK_node, tot1438, tot1439]
  decide +kernel

theorem arows1436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1436 = true := by
  rw [show D2M8K2.u1436 = KTree.node D2M8K2.t1440 (nat_lit 2868418) (nat_lit 3932245291) (nat_lit 0) D2M8K2.t1441 from rfl, allE_node, rows1440, irow1436, rows1441]
  all_goals rfl

theorem atot1436 : totK PD2M8K2 D2M8K2.u1436 = [0, 173283618171, 603905024998, 730379497831, 278143781485, 12075845174, 0, 0] := by
  rw [show D2M8K2.u1436 = KTree.node D2M8K2.t1440 (nat_lit 2868418) (nat_lit 3932245291) (nat_lit 0) D2M8K2.t1441 from rfl, totK_node, tot1440, tot1441]
  decide +kernel

theorem arows1437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1437 = true := by
  rw [show D2M8K2.u1437 = KTree.node D2M8K2.t1442 (nat_lit 2873380) (nat_lit 3400273385) (nat_lit 0) D2M8K2.t1443 from rfl, allE_node, rows1442, irow1437, rows1443]
  all_goals rfl

theorem atot1437 : totK PD2M8K2 D2M8K2.u1437 = [0, 264699936094, 810061776096, 628053365952, 103623521761, 1198073392, 0, 0] := by
  rw [show D2M8K2.u1437 = KTree.node D2M8K2.t1442 (nat_lit 2873380) (nat_lit 3400273385) (nat_lit 0) D2M8K2.t1443 from rfl, totK_node, tot1442, tot1443]
  decide +kernel

theorem arows1439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1439 = true := by
  rw [show D2M8K2.u1439 = KTree.node D2M8K2.t1444 (nat_lit 2874994) (nat_lit 2715182938) (nat_lit 0) D2M8K2.t1445 from rfl, allE_node, rows1444, irow1439, rows1445]
  all_goals rfl

theorem atot1439 : totK PD2M8K2 D2M8K2.u1439 = [0, 151251940429, 629810556761, 761601487527, 228933992539, 11991925116, 0, 0] := by
  rw [show D2M8K2.u1439 = KTree.node D2M8K2.t1444 (nat_lit 2874994) (nat_lit 2715182938) (nat_lit 0) D2M8K2.t1445 from rfl, totK_node, tot1444, tot1445]
  decide +kernel

theorem arows1440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1440 = true := by
  rw [show D2M8K2.u1440 = KTree.node D2M8K2.t1446 (nat_lit 2876717) (nat_lit 1730244115) (nat_lit 0) D2M8K2.t1447 from rfl, allE_node, rows1446, irow1440, rows1447]
  all_goals rfl

theorem atot1440 : totK PD2M8K2 D2M8K2.u1440 = [0, 174478519940, 760261370421, 755122694399, 108645602708, 1096505104, 0, 0] := by
  rw [show D2M8K2.u1440 = KTree.node D2M8K2.t1446 (nat_lit 2876717) (nat_lit 1730244115) (nat_lit 0) D2M8K2.t1447 from rfl, totK_node, tot1446, tot1447]
  decide +kernel

theorem arows1443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1443 = true := by
  rw [show D2M8K2.u1443 = KTree.node D2M8K2.t1448 (nat_lit 2879220) (nat_lit 2669044742) (nat_lit 0) D2M8K2.t1449 from rfl, allE_node, rows1448, irow1443, rows1449]
  all_goals rfl

theorem atot1443 : totK PD2M8K2 D2M8K2.u1443 = [0, 317490084646, 809711313967, 553740232285, 104376813244, 3821179711, 0, 0] := by
  rw [show D2M8K2.u1443 = KTree.node D2M8K2.t1448 (nat_lit 2879220) (nat_lit 2669044742) (nat_lit 0) D2M8K2.t1449 from rfl, totK_node, tot1448, tot1449]
  decide +kernel

theorem arows1444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1444 = true := by
  rw [show D2M8K2.u1444 = KTree.node D2M8K2.t1450 (nat_lit 2880698) (nat_lit 3432611166) (nat_lit 0) D2M8K2.t1451 from rfl, allE_node, rows1450, irow1444, rows1451]
  all_goals rfl

theorem atot1444 : totK PD2M8K2 D2M8K2.u1444 = [0, 108354261105, 637614937936, 830586430606, 207602393110, 4899206309, 0, 0] := by
  rw [show D2M8K2.u1444 = KTree.node D2M8K2.t1450 (nat_lit 2880698) (nat_lit 3432611166) (nat_lit 0) D2M8K2.t1451 from rfl, totK_node, tot1450, tot1451]
  decide +kernel

theorem arows1446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1446 = true := by
  rw [show D2M8K2.u1446 = KTree.node D2M8K2.t1452 (nat_lit 2882394) (nat_lit 3884557329) (nat_lit 0) D2M8K2.t1453 from rfl, allE_node, rows1452, irow1446, rows1453]
  all_goals rfl

theorem atot1446 : totK PD2M8K2 D2M8K2.u1446 = [0, 0, 380238112007, 964826640473, 405159891350, 20781990054, 0, 0] := by
  rw [show D2M8K2.u1446 = KTree.node D2M8K2.t1452 (nat_lit 2882394) (nat_lit 3884557329) (nat_lit 0) D2M8K2.t1453 from rfl, totK_node, tot1452, tot1453]
  decide +kernel

theorem arows1447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1447 = true := by
  rw [show D2M8K2.u1447 = KTree.node D2M8K2.t1454 (nat_lit 2884054) (nat_lit 3389319859) (nat_lit 0) D2M8K2.t1455 from rfl, allE_node, rows1454, irow1447, rows1455]
  all_goals rfl

theorem atot1447 : totK PD2M8K2 D2M8K2.u1447 = [0, 0, 162902740829, 771708692862, 694066669951, 80893241676, 1200365979, 0] := by
  rw [show D2M8K2.u1447 = KTree.node D2M8K2.t1454 (nat_lit 2884054) (nat_lit 3389319859) (nat_lit 0) D2M8K2.t1455 from rfl, totK_node, tot1454, tot1455]
  decide +kernel

theorem arows1451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1451 = true := by
  rw [show D2M8K2.u1451 = KTree.node D2M8K2.t1456 (nat_lit 2886728) (nat_lit 3883878365) (nat_lit 0) D2M8K2.t1457 from rfl, allE_node, rows1456, irow1451, rows1457]
  all_goals rfl

theorem atot1451 : totK PD2M8K2 D2M8K2.u1451 = [0, 0, 419595587292, 956484450559, 430466513147, 28642566137, 0, 0] := by
  rw [show D2M8K2.u1451 = KTree.node D2M8K2.t1456 (nat_lit 2886728) (nat_lit 3883878365) (nat_lit 0) D2M8K2.t1457 from rfl, totK_node, tot1456, tot1457]
  decide +kernel

theorem arows1452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1452 = true := by
  rw [show D2M8K2.u1452 = KTree.node D2M8K2.t1458 (nat_lit 2893645) (nat_lit 1110476738) (nat_lit 0) D2M8K2.t1459 from rfl, allE_node, rows1458, irow1452, rows1459]
  all_goals rfl

theorem atot1452 : totK PD2M8K2 D2M8K2.u1452 = [0, 0, 391716744825, 952325276217, 419362836895, 23659612322, 0, 0] := by
  rw [show D2M8K2.u1452 = KTree.node D2M8K2.t1458 (nat_lit 2893645) (nat_lit 1110476738) (nat_lit 0) D2M8K2.t1459 from rfl, totK_node, tot1458, tot1459]
  decide +kernel

theorem arows1454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1454 = true := by
  rw [show D2M8K2.u1454 = KTree.node D2M8K2.t1460 (nat_lit 2895368) (nat_lit 3791835488) (nat_lit 0) D2M8K2.t1461 from rfl, allE_node, rows1460, irow1454, rows1461]
  all_goals rfl

theorem atot1454 : totK PD2M8K2 D2M8K2.u1454 = [0, 0, 80838430914, 631487878607, 822155626985, 176074068391, 5163565574, 0] := by
  rw [show D2M8K2.u1454 = KTree.node D2M8K2.t1460 (nat_lit 2895368) (nat_lit 3791835488) (nat_lit 0) D2M8K2.t1461 from rfl, totK_node, tot1460, tot1461]
  decide +kernel

theorem arows1455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1455 = true := by
  rw [show D2M8K2.u1455 = KTree.node D2M8K2.t1462 (nat_lit 2899590) (nat_lit 3784348551) (nat_lit 0) D2M8K2.t1463 from rfl, allE_node, rows1462, irow1455, rows1463]
  all_goals rfl

theorem atot1455 : totK PD2M8K2 D2M8K2.u1455 = [0, 0, 447681933283, 966214444861, 341484276663, 15264253750, 0, 0] := by
  rw [show D2M8K2.u1455 = KTree.node D2M8K2.t1462 (nat_lit 2899590) (nat_lit 3784348551) (nat_lit 0) D2M8K2.t1463 from rfl, totK_node, tot1462, tot1463]
  decide +kernel

theorem arows1458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1458 = true := by
  rw [show D2M8K2.u1458 = KTree.node D2M8K2.t1464 (nat_lit 2901156) (nat_lit 3288206159) (nat_lit 0) D2M8K2.t1465 from rfl, allE_node, rows1464, irow1458, rows1465]
  all_goals rfl

theorem atot1458 : totK PD2M8K2 D2M8K2.u1458 = [0, 176045873872, 581459957297, 696832520136, 330646838670, 23883506540, 0, 0] := by
  rw [show D2M8K2.u1458 = KTree.node D2M8K2.t1464 (nat_lit 2901156) (nat_lit 3288206159) (nat_lit 0) D2M8K2.t1465 from rfl, totK_node, tot1464, tot1465]
  decide +kernel

theorem arows1459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1459 = true := by
  rw [show D2M8K2.u1459 = KTree.node D2M8K2.t1466 (nat_lit 2945909) (nat_lit 2160141787) (nat_lit 0) D2M8K2.t1467 from rfl, allE_node, rows1466, irow1459, rows1467]
  all_goals rfl

theorem atot1459 : totK PD2M8K2 D2M8K2.u1459 = [0, 241702337251, 799994622717, 632116220515, 98191855167, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1459 = KTree.node D2M8K2.t1466 (nat_lit 2945909) (nat_lit 2160141787) (nat_lit 0) D2M8K2.t1467 from rfl, totK_node, tot1466, tot1467]
  decide +kernel

theorem arows1461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1461 = true := by
  rw [show D2M8K2.u1461 = KTree.node D2M8K2.t1468 (nat_lit 2948307) (nat_lit 3716614309) (nat_lit 0) D2M8K2.t1469 from rfl, allE_node, rows1468, irow1461, rows1469]
  all_goals rfl

theorem atot1461 : totK PD2M8K2 D2M8K2.u1461 = [0, 192497381685, 776711551155, 763896967053, 83953371104, 0, 0, 0] := by
  rw [show D2M8K2.u1461 = KTree.node D2M8K2.t1468 (nat_lit 2948307) (nat_lit 3716614309) (nat_lit 0) D2M8K2.t1469 from rfl, totK_node, tot1468, tot1469]
  decide +kernel

theorem arows1462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1462 = true := by
  rw [show D2M8K2.u1462 = KTree.node D2M8K2.t1470 (nat_lit 2949553) (nat_lit 1500535357) (nat_lit 0) D2M8K2.t1471 from rfl, allE_node, rows1470, irow1462, rows1471]
  all_goals rfl

theorem atot1462 : totK PD2M8K2 D2M8K2.u1462 = [0, 215255597221, 738931915601, 642897888612, 199143085826, 18724171075, 0, 0] := by
  rw [show D2M8K2.u1462 = KTree.node D2M8K2.t1470 (nat_lit 2949553) (nat_lit 1500535357) (nat_lit 0) D2M8K2.t1471 from rfl, totK_node, tot1470, tot1471]
  decide +kernel

theorem arows1468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1468 = true := by
  rw [show D2M8K2.u1468 = KTree.node D2M8K2.t1472 (nat_lit 2951158) (nat_lit 3535023872) (nat_lit 0) D2M8K2.t1473 from rfl, allE_node, rows1472, irow1468, rows1473]
  all_goals rfl

theorem atot1468 : totK PD2M8K2 D2M8K2.u1468 = [0, 130736772173, 526218334135, 784280385451, 330609070018, 11683261214, 0, 0] := by
  rw [show D2M8K2.u1468 = KTree.node D2M8K2.t1472 (nat_lit 2951158) (nat_lit 3535023872) (nat_lit 0) D2M8K2.t1473 from rfl, totK_node, tot1472, tot1473]
  decide +kernel

theorem arows1469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1469 = true := by
  rw [show D2M8K2.u1469 = KTree.node D2M8K2.t1474 (nat_lit 2952616) (nat_lit 3824956936) (nat_lit 0) D2M8K2.t1475 from rfl, allE_node, rows1474, irow1469, rows1475]
  all_goals rfl

theorem atot1469 : totK PD2M8K2 D2M8K2.u1469 = [0, 287891433282, 873128184851, 582102016010, 52261759548, 0, 0, 0] := by
  rw [show D2M8K2.u1469 = KTree.node D2M8K2.t1474 (nat_lit 2952616) (nat_lit 3824956936) (nat_lit 0) D2M8K2.t1475 from rfl, totK_node, tot1474, tot1475]
  decide +kernel

theorem arows1471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1471 = true := by
  rw [show D2M8K2.u1471 = KTree.node D2M8K2.t1476 (nat_lit 2954337) (nat_lit 1329828905) (nat_lit 0) D2M8K2.t1477 from rfl, allE_node, rows1476, irow1471, rows1477]
  all_goals rfl

theorem atot1471 : totK PD2M8K2 D2M8K2.u1471 = [0, 104139918814, 565916393732, 840916134555, 246070265672, 8557595888, 0, 0] := by
  rw [show D2M8K2.u1471 = KTree.node D2M8K2.t1476 (nat_lit 2954337) (nat_lit 1329828905) (nat_lit 0) D2M8K2.t1477 from rfl, totK_node, tot1476, tot1477]
  decide +kernel

theorem arows1472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1472 = true := by
  rw [show D2M8K2.u1472 = KTree.node D2M8K2.t1478 (nat_lit 2956032) (nat_lit 3661434734) (nat_lit 0) D2M8K2.t1479 from rfl, allE_node, rows1478, irow1472, rows1479]
  all_goals rfl

theorem atot1472 : totK PD2M8K2 D2M8K2.u1472 = [0, 314717506997, 888296869473, 554369799294, 51361371222, 0, 0, 0] := by
  rw [show D2M8K2.u1472 = KTree.node D2M8K2.t1478 (nat_lit 2956032) (nat_lit 3661434734) (nat_lit 0) D2M8K2.t1479 from rfl, totK_node, tot1478, tot1479]
  decide +kernel

theorem arows1475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1475 = true := by
  rw [show D2M8K2.u1475 = KTree.node D2M8K2.t1480 (nat_lit 2957736) (nat_lit 3263067135) (nat_lit 0) D2M8K2.t1481 from rfl, allE_node, rows1480, irow1475, rows1481]
  all_goals rfl

theorem atot1475 : totK PD2M8K2 D2M8K2.u1475 = [0, 86902333671, 549993853334, 859921906176, 257694840761, 8656689423, 0, 0] := by
  rw [show D2M8K2.u1475 = KTree.node D2M8K2.t1480 (nat_lit 2957736) (nat_lit 3263067135) (nat_lit 0) D2M8K2.t1481 from rfl, totK_node, tot1480, tot1481]
  decide +kernel

theorem arows1476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1476 = true := by
  rw [show D2M8K2.u1476 = KTree.node D2M8K2.t1482 (nat_lit 2962580) (nat_lit 3041590597) (nat_lit 0) D2M8K2.t1483 from rfl, allE_node, rows1482, irow1476, rows1483]
  all_goals rfl

theorem atot1476 : totK PD2M8K2 D2M8K2.u1476 = [0, 360527532845, 932501101437, 513616335495, 40649028012, 0, 0, 0] := by
  rw [show D2M8K2.u1476 = KTree.node D2M8K2.t1482 (nat_lit 2962580) (nat_lit 3041590597) (nat_lit 0) D2M8K2.t1483 from rfl, totK_node, tot1482, tot1483]
  decide +kernel

theorem arows1478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1478 = true := by
  rw [show D2M8K2.u1478 = KTree.node D2M8K2.t1484 (nat_lit 2964213) (nat_lit 945595911) (nat_lit 0) D2M8K2.t1485 from rfl, allE_node, rows1484, irow1478, rows1485]
  all_goals rfl

theorem atot1478 : totK PD2M8K2 D2M8K2.u1478 = [0, 0, 470474028053, 997826877176, 313393336300, 8710740030, 0, 0] := by
  rw [show D2M8K2.u1478 = KTree.node D2M8K2.t1484 (nat_lit 2964213) (nat_lit 945595911) (nat_lit 0) D2M8K2.t1485 from rfl, totK_node, tot1484, tot1485]
  decide +kernel

theorem arows1479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1479 = true := by
  rw [show D2M8K2.u1479 = KTree.node D2M8K2.t1486 (nat_lit 2966002) (nat_lit 3847972966) (nat_lit 0) D2M8K2.t1487 from rfl, allE_node, rows1486, irow1479, rows1487]
  all_goals rfl

theorem atot1479 : totK PD2M8K2 D2M8K2.u1479 = [0, 0, 356484732694, 931793508620, 418598518513, 23658994969, 0, 0] := by
  rw [show D2M8K2.u1479 = KTree.node D2M8K2.t1486 (nat_lit 2966002) (nat_lit 3847972966) (nat_lit 0) D2M8K2.t1487 from rfl, totK_node, tot1486, tot1487]
  decide +kernel

theorem arows1483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1483 = true := by
  rw [show D2M8K2.u1483 = KTree.node D2M8K2.t1488 (nat_lit 2967653) (nat_lit 2189620926) (nat_lit 0) D2M8K2.t1489 from rfl, allE_node, rows1488, irow1483, rows1489]
  all_goals rfl

theorem atot1483 : totK PD2M8K2 D2M8K2.u1483 = [0, 0, 128483596095, 698547113954, 807867034310, 119074394429, 1288491354, 0] := by
  rw [show D2M8K2.u1483 = KTree.node D2M8K2.t1488 (nat_lit 2967653) (nat_lit 2189620926) (nat_lit 0) D2M8K2.t1489 from rfl, totK_node, tot1488, tot1489]
  decide +kernel

theorem arows1484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1484 = true := by
  rw [show D2M8K2.u1484 = KTree.node D2M8K2.t1490 (nat_lit 2969713) (nat_lit 1457317368) (nat_lit 0) D2M8K2.t1491 from rfl, allE_node, rows1490, irow1484, rows1491]
  all_goals rfl

theorem atot1484 : totK PD2M8K2 D2M8K2.u1484 = [0, 0, 395008400376, 944956816624, 435562452243, 33171106730, 0, 0] := by
  rw [show D2M8K2.u1484 = KTree.node D2M8K2.t1490 (nat_lit 2969713) (nat_lit 1457317368) (nat_lit 0) D2M8K2.t1491 from rfl, totK_node, tot1490, tot1491]
  decide +kernel

theorem arows1486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1486 = true := by
  rw [show D2M8K2.u1486 = KTree.node D2M8K2.t1492 (nat_lit 2972885) (nat_lit 2240260661) (nat_lit 0) D2M8K2.t1493 from rfl, allE_node, rows1492, irow1486, rows1493]
  all_goals rfl

theorem atot1486 : totK PD2M8K2 D2M8K2.u1486 = [0, 0, 348231790004, 943291281349, 461637103182, 25357605310, 0, 0] := by
  rw [show D2M8K2.u1486 = KTree.node D2M8K2.t1492 (nat_lit 2972885) (nat_lit 2240260661) (nat_lit 0) D2M8K2.t1493 from rfl, totK_node, tot1492, tot1493]
  decide +kernel

theorem arows1487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1487 = true := by
  rw [show D2M8K2.u1487 = KTree.node D2M8K2.t1494 (nat_lit 2974668) (nat_lit 2818113576) (nat_lit 0) D2M8K2.t1495 from rfl, allE_node, rows1494, irow1487, rows1495]
  all_goals rfl

theorem atot1487 : totK PD2M8K2 D2M8K2.u1487 = [0, 0, 117086725142, 651916907240, 769814705021, 161732344598, 4787054165, 0] := by
  rw [show D2M8K2.u1487 = KTree.node D2M8K2.t1494 (nat_lit 2974668) (nat_lit 2818113576) (nat_lit 0) D2M8K2.t1495 from rfl, totK_node, tot1494, tot1495]
  decide +kernel

theorem arows1490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1490 = true := by
  rw [show D2M8K2.u1490 = KTree.node D2M8K2.t1496 (nat_lit 2976851) (nat_lit 2273961447) (nat_lit 0) D2M8K2.t1497 from rfl, allE_node, rows1496, irow1490, rows1497]
  all_goals rfl

theorem atot1490 : totK PD2M8K2 D2M8K2.u1490 = [0, 0, 296373411962, 851355661897, 546034347425, 63538767247, 1086231185, 0] := by
  rw [show D2M8K2.u1490 = KTree.node D2M8K2.t1496 (nat_lit 2976851) (nat_lit 2273961447) (nat_lit 0) D2M8K2.t1497 from rfl, totK_node, tot1496, tot1497]
  decide +kernel

theorem arows1491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1491 = true := by
  rw [show D2M8K2.u1491 = KTree.node D2M8K2.t1498 (nat_lit 2978856) (nat_lit 3472111809) (nat_lit 0) D2M8K2.t1499 from rfl, allE_node, rows1498, irow1491, rows1499]
  all_goals rfl

theorem atot1491 : totK PD2M8K2 D2M8K2.u1491 = [0, 0, 174703029157, 740232310161, 701202085158, 136161642406, 3752012233, 0] := by
  rw [show D2M8K2.u1491 = KTree.node D2M8K2.t1498 (nat_lit 2978856) (nat_lit 3472111809) (nat_lit 0) D2M8K2.t1499 from rfl, totK_node, tot1498, tot1499]
  decide +kernel

theorem arows1493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1493 = true := by
  rw [show D2M8K2.u1493 = KTree.node D2M8K2.t1500 (nat_lit 2983968) (nat_lit 3708958841) (nat_lit 0) D2M8K2.t1501 from rfl, allE_node, rows1500, irow1493, rows1501]
  all_goals rfl

theorem atot1493 : totK PD2M8K2 D2M8K2.u1493 = [0, 0, 267746219242, 798994763955, 621197644831, 102026845390, 1242138600, 0] := by
  rw [show D2M8K2.u1493 = KTree.node D2M8K2.t1500 (nat_lit 2983968) (nat_lit 3708958841) (nat_lit 0) D2M8K2.t1501 from rfl, totK_node, tot1500, tot1501]
  decide +kernel

theorem arows1494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1494 = true := by
  rw [show D2M8K2.u1494 = KTree.node D2M8K2.t1502 (nat_lit 2985355) (nat_lit 1569277924) (nat_lit 0) D2M8K2.t1503 from rfl, allE_node, rows1502, irow1494, rows1503]
  all_goals rfl

theorem atot1494 : totK PD2M8K2 D2M8K2.u1494 = [0, 92342479873, 218915502108, 403953867966, 724352964819, 295486414894, 20509029466, 0] := by
  rw [show D2M8K2.u1494 = KTree.node D2M8K2.t1502 (nat_lit 2985355) (nat_lit 1569277924) (nat_lit 0) D2M8K2.t1503 from rfl, totK_node, tot1502, tot1503]
  decide +kernel

theorem arows1499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1499 = true := by
  rw [show D2M8K2.u1499 = KTree.node D2M8K2.t1504 (nat_lit 2987141) (nat_lit 2302964739) (nat_lit 0) D2M8K2.t1505 from rfl, allE_node, rows1504, irow1499, rows1505]
  all_goals rfl

theorem atot1499 : totK PD2M8K2 D2M8K2.u1499 = [0, 351010345388, 930974055047, 504011463777, 36075309768, 0, 0, 0] := by
  rw [show D2M8K2.u1499 = KTree.node D2M8K2.t1504 (nat_lit 2987141) (nat_lit 2302964739) (nat_lit 0) D2M8K2.t1505 from rfl, totK_node, tot1504, tot1505]
  decide +kernel

theorem arows1500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1500 = true := by
  rw [show D2M8K2.u1500 = KTree.node D2M8K2.t1506 (nat_lit 2988912) (nat_lit 3527819012) (nat_lit 0) D2M8K2.t1507 from rfl, allE_node, rows1506, irow1500, rows1507]
  all_goals rfl

theorem atot1500 : totK PD2M8K2 D2M8K2.u1500 = [0, 138273776836, 707347111740, 831869549313, 143006563032, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1500 = KTree.node D2M8K2.t1506 (nat_lit 2988912) (nat_lit 3527819012) (nat_lit 0) D2M8K2.t1507 from rfl, totK_node, tot1506, tot1507]
  decide +kernel

theorem arows1502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1502 = true := by
  rw [show D2M8K2.u1502 = KTree.node D2M8K2.t1508 (nat_lit 2994144) (nat_lit 3540450641) (nat_lit 0) D2M8K2.t1509 from rfl, allE_node, rows1508, irow1502, rows1509]
  all_goals rfl

theorem atot1502 : totK PD2M8K2 D2M8K2.u1502 = [0, 282234769951, 872130016028, 594108597149, 54460269654, 0, 0, 0] := by
  rw [show D2M8K2.u1502 = KTree.node D2M8K2.t1508 (nat_lit 2994144) (nat_lit 3540450641) (nat_lit 0) D2M8K2.t1509 from rfl, totK_node, tot1508, tot1509]
  decide +kernel

theorem arows1503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1503 = true := by
  rw [show D2M8K2.u1503 = KTree.node D2M8K2.t1510 (nat_lit 2995836) (nat_lit 3130876508) (nat_lit 0) D2M8K2.t1511 from rfl, allE_node, rows1510, irow1503, rows1511]
  all_goals rfl

theorem atot1503 : totK PD2M8K2 D2M8K2.u1503 = [0, 87978670910, 552022096405, 843564154027, 270765789232, 13049727234, 0, 0] := by
  rw [show D2M8K2.u1503 = KTree.node D2M8K2.t1510 (nat_lit 2995836) (nat_lit 3130876508) (nat_lit 0) D2M8K2.t1511 from rfl, totK_node, tot1510, tot1511]
  decide +kernel

theorem arows1506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1506 = true := by
  rw [show D2M8K2.u1506 = KTree.node D2M8K2.t1512 (nat_lit 2997538) (nat_lit 2557372310) (nat_lit 0) D2M8K2.t1513 from rfl, allE_node, rows1512, irow1506, rows1513]
  all_goals rfl

theorem atot1506 : totK PD2M8K2 D2M8K2.u1506 = [0, 329214290171, 896613236902, 537702460734, 43952040965, 0, 0, 0] := by
  rw [show D2M8K2.u1506 = KTree.node D2M8K2.t1512 (nat_lit 2997538) (nat_lit 2557372310) (nat_lit 0) D2M8K2.t1513 from rfl, totK_node, tot1512, tot1513]
  decide +kernel

theorem arows1507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1507 = true := by
  rw [show D2M8K2.u1507 = KTree.node D2M8K2.t1514 (nat_lit 2999212) (nat_lit 2535916563) (nat_lit 0) D2M8K2.t1515 from rfl, allE_node, rows1514, irow1507, rows1515]
  all_goals rfl

theorem atot1507 : totK PD2M8K2 D2M8K2.u1507 = [0, 87770539582, 511897979677, 863580507552, 291536816979, 13250685261, 0, 0] := by
  rw [show D2M8K2.u1507 = KTree.node D2M8K2.t1514 (nat_lit 2999212) (nat_lit 2535916563) (nat_lit 0) D2M8K2.t1515 from rfl, totK_node, tot1514, tot1515]
  decide +kernel

theorem arows1509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1509 = true := by
  rw [show D2M8K2.u1509 = KTree.node D2M8K2.t1516 (nat_lit 3000630) (nat_lit 2814907876) (nat_lit 0) D2M8K2.t1517 from rfl, allE_node, rows1516, irow1509, rows1517]
  all_goals rfl

theorem atot1509 : totK PD2M8K2 D2M8K2.u1509 = [0, 330467476606, 922309960917, 499364661761, 33972218887, 0, 0, 0] := by
  rw [show D2M8K2.u1509 = KTree.node D2M8K2.t1516 (nat_lit 3000630) (nat_lit 2814907876) (nat_lit 0) D2M8K2.t1517 from rfl, totK_node, tot1516, tot1517]
  decide +kernel

theorem arows1510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1510 = true := by
  rw [show D2M8K2.u1510 = KTree.node D2M8K2.t1518 (nat_lit 3002478) (nat_lit 4072429918) (nat_lit 0) D2M8K2.t1519 from rfl, allE_node, rows1518, irow1510, rows1519]
  all_goals rfl

theorem atot1510 : totK PD2M8K2 D2M8K2.u1510 = [0, 88185535531, 617977631866, 881595367367, 196978301243, 4980514959, 0, 0] := by
  rw [show D2M8K2.u1510 = KTree.node D2M8K2.t1518 (nat_lit 3002478) (nat_lit 4072429918) (nat_lit 0) D2M8K2.t1519 from rfl, totK_node, tot1518, tot1519]
  decide +kernel

theorem arows1514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1514 = true := by
  rw [show D2M8K2.u1514 = KTree.node D2M8K2.t1520 (nat_lit 3004155) (nat_lit 3476371687) (nat_lit 0) D2M8K2.t1521 from rfl, allE_node, rows1520, irow1514, rows1521]
  all_goals rfl

theorem atot1514 : totK PD2M8K2 D2M8K2.u1514 = [0, 334814008584, 897968777322, 533954905240, 49238774594, 0, 0, 0] := by
  rw [show D2M8K2.u1514 = KTree.node D2M8K2.t1520 (nat_lit 3004155) (nat_lit 3476371687) (nat_lit 0) D2M8K2.t1521 from rfl, totK_node, tot1520, tot1521]
  decide +kernel

theorem arows1515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1515 = true := by
  rw [show D2M8K2.u1515 = KTree.node D2M8K2.t1522 (nat_lit 3005782) (nat_lit 2928667812) (nat_lit 0) D2M8K2.t1523 from rfl, allE_node, rows1522, irow1515, rows1523]
  all_goals rfl

theorem atot1515 : totK PD2M8K2 D2M8K2.u1515 = [0, 0, 401762277594, 969026920394, 375681753052, 14971720341, 0, 0] := by
  rw [show D2M8K2.u1515 = KTree.node D2M8K2.t1522 (nat_lit 3005782) (nat_lit 2928667812) (nat_lit 0) D2M8K2.t1523 from rfl, totK_node, tot1522, tot1523]
  decide +kernel

theorem arows1517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1517 = true := by
  rw [show D2M8K2.u1517 = KTree.node D2M8K2.t1524 (nat_lit 3007602) (nat_lit 3443727579) (nat_lit 0) D2M8K2.t1525 from rfl, allE_node, rows1524, irow1517, rows1525]
  all_goals rfl

theorem atot1517 : totK PD2M8K2 D2M8K2.u1517 = [0, 0, 389637871312, 942358518166, 416390356215, 28894120029, 0, 0] := by
  rw [show D2M8K2.u1517 = KTree.node D2M8K2.t1524 (nat_lit 3007602) (nat_lit 3443727579) (nat_lit 0) D2M8K2.t1525 from rfl, totK_node, tot1524, tot1525]
  decide +kernel

theorem arows1518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1518 = true := by
  rw [show D2M8K2.u1518 = KTree.node D2M8K2.t1526 (nat_lit 3009128) (nat_lit 3855031423) (nat_lit 0) D2M8K2.t1527 from rfl, allE_node, rows1526, irow1518, rows1527]
  all_goals rfl

theorem atot1518 : totK PD2M8K2 D2M8K2.u1518 = [0, 0, 120912595093, 699205758049, 781976188066, 142668472581, 1369150432, 0] := by
  rw [show D2M8K2.u1518 = KTree.node D2M8K2.t1526 (nat_lit 3009128) (nat_lit 3855031423) (nat_lit 0) D2M8K2.t1527 from rfl, totK_node, tot1526, tot1527]
  decide +kernel

theorem arows1521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1521 = true := by
  rw [show D2M8K2.u1521 = KTree.node D2M8K2.t1528 (nat_lit 3014411) (nat_lit 2406172620) (nat_lit 0) D2M8K2.t1529 from rfl, allE_node, rows1528, irow1521, rows1529]
  all_goals rfl

theorem atot1521 : totK PD2M8K2 D2M8K2.u1521 = [0, 0, 350229768424, 945428430232, 449654779885, 21551083610, 0, 0] := by
  rw [show D2M8K2.u1521 = KTree.node D2M8K2.t1528 (nat_lit 3014411) (nat_lit 2406172620) (nat_lit 0) D2M8K2.t1529 from rfl, totK_node, tot1528, tot1529]
  decide +kernel

theorem arows1522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1522 = true := by
  rw [show D2M8K2.u1522 = KTree.node D2M8K2.t1530 (nat_lit 3018033) (nat_lit 1851908170) (nat_lit 0) D2M8K2.t1531 from rfl, allE_node, rows1530, irow1522, rows1531]
  all_goals rfl

theorem atot1522 : totK PD2M8K2 D2M8K2.u1522 = [0, 0, 393227633690, 944642362349, 417030287992, 22800187125, 0, 0] := by
  rw [show D2M8K2.u1522 = KTree.node D2M8K2.t1530 (nat_lit 3018033) (nat_lit 1851908170) (nat_lit 0) D2M8K2.t1531 from rfl, totK_node, tot1530, tot1531]
  decide +kernel

theorem arows1524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1524 = true := by
  rw [show D2M8K2.u1524 = KTree.node D2M8K2.t1532 (nat_lit 3021029) (nat_lit 2343579997) (nat_lit 0) D2M8K2.t1533 from rfl, allE_node, rows1532, irow1524, rows1533]
  all_goals rfl

theorem atot1524 : totK PD2M8K2 D2M8K2.u1524 = [0, 0, 349274211901, 943174955978, 442359880752, 25901910195, 0, 0] := by
  rw [show D2M8K2.u1524 = KTree.node D2M8K2.t1532 (nat_lit 3021029) (nat_lit 2343579997) (nat_lit 0) D2M8K2.t1533 from rfl, totK_node, tot1532, tot1533]
  decide +kernel

theorem arows1525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1525 = true := by
  rw [show D2M8K2.u1525 = KTree.node D2M8K2.t1534 (nat_lit 3024328) (nat_lit 3726031425) (nat_lit 0) D2M8K2.t1535 from rfl, allE_node, rows1534, irow1525, rows1535]
  all_goals rfl

theorem atot1525 : totK PD2M8K2 D2M8K2.u1525 = [0, 0, 387647256397, 956982325182, 419762124635, 18737015676, 0, 0] := by
  rw [show D2M8K2.u1525 = KTree.node D2M8K2.t1534 (nat_lit 3024328) (nat_lit 3726031425) (nat_lit 0) D2M8K2.t1535 from rfl, totK_node, tot1534, tot1535]
  decide +kernel

theorem arows1534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1534 = true := by
  rw [show D2M8K2.u1534 = KTree.node D2M8K2.t1536 (nat_lit 3069030) (nat_lit 3631649584) (nat_lit 0) D2M8K2.t1537 from rfl, allE_node, rows1536, irow1534, rows1537]
  all_goals rfl

theorem atot1534 : totK PD2M8K2 D2M8K2.u1534 = [0, 250700835327, 706965969595, 601394963169, 234132484103, 17433533548, 0, 0] := by
  rw [show D2M8K2.u1534 = KTree.node D2M8K2.t1536 (nat_lit 3069030) (nat_lit 3631649584) (nat_lit 0) D2M8K2.t1537 from rfl, totK_node, tot1536, tot1537]
  decide +kernel

theorem arows1535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1535 = true := by
  rw [show D2M8K2.u1535 = KTree.node D2M8K2.t1538 (nat_lit 3070576) (nat_lit 3508687144) (nat_lit 0) D2M8K2.t1539 from rfl, allE_node, rows1538, irow1535, rows1539]
  all_goals rfl

theorem atot1535 : totK PD2M8K2 D2M8K2.u1535 = [0, 171699112667, 735730847266, 749530051155, 127074863306, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1535 = KTree.node D2M8K2.t1538 (nat_lit 3070576) (nat_lit 3508687144) (nat_lit 0) D2M8K2.t1539 from rfl, totK_node, tot1538, tot1539]
  decide +kernel

theorem arows1537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1537 = true := by
  rw [show D2M8K2.u1537 = KTree.node D2M8K2.t1540 (nat_lit 3072991) (nat_lit 1135046655) (nat_lit 0) D2M8K2.t1541 from rfl, allE_node, rows1540, irow1537, rows1541]
  all_goals rfl

theorem atot1537 : totK PD2M8K2 D2M8K2.u1537 = [0, 294358100286, 860917337594, 602588352825, 55553375588, 0, 0, 0] := by
  rw [show D2M8K2.u1537 = KTree.node D2M8K2.t1540 (nat_lit 3072991) (nat_lit 1135046655) (nat_lit 0) D2M8K2.t1541 from rfl, totK_node, tot1540, tot1541]
  decide +kernel

theorem arows1538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1538 = true := by
  rw [show D2M8K2.u1538 = KTree.node D2M8K2.t1542 (nat_lit 3074832) (nat_lit 3421343463) (nat_lit 0) D2M8K2.t1543 from rfl, allE_node, rows1542, irow1538, rows1543]
  all_goals rfl

theorem atot1538 : totK PD2M8K2 D2M8K2.u1538 = [0, 33348887533, 477025289149, 918496011229, 346447186505, 10582935847, 0, 0] := by
  rw [show D2M8K2.u1538 = KTree.node D2M8K2.t1542 (nat_lit 3074832) (nat_lit 3421343463) (nat_lit 0) D2M8K2.t1543 from rfl, totK_node, tot1542, tot1543]
  decide +kernel

theorem arows1541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1541 = true := by
  rw [show D2M8K2.u1541 = KTree.node D2M8K2.t1544 (nat_lit 3076422) (nat_lit 2732429909) (nat_lit 0) D2M8K2.t1545 from rfl, allE_node, rows1544, irow1541, rows1545]
  all_goals rfl

theorem atot1541 : totK PD2M8K2 D2M8K2.u1541 = [0, 372934538607, 922145872740, 469660222167, 54674646731, 3060566153, 0, 0] := by
  rw [show D2M8K2.u1541 = KTree.node D2M8K2.t1544 (nat_lit 3076422) (nat_lit 2732429909) (nat_lit 0) D2M8K2.t1545 from rfl, totK_node, tot1544, tot1545]
  decide +kernel

theorem arows1542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1542 = true := by
  rw [show D2M8K2.u1542 = KTree.node D2M8K2.t1546 (nat_lit 3077942) (nat_lit 3166660447) (nat_lit 0) D2M8K2.t1547 from rfl, allE_node, rows1546, irow1542, rows1547]
  all_goals rfl

theorem atot1542 : totK PD2M8K2 D2M8K2.u1542 = [0, 66582615597, 544447741285, 904774186130, 259188161771, 10568566766, 0, 0] := by
  rw [show D2M8K2.u1542 = KTree.node D2M8K2.t1546 (nat_lit 3077942) (nat_lit 3166660447) (nat_lit 0) D2M8K2.t1547 from rfl, totK_node, tot1546, tot1547]
  decide +kernel

theorem arows1544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1544 = true := by
  rw [show D2M8K2.u1544 = KTree.node D2M8K2.t1548 (nat_lit 3083211) (nat_lit 3773144805) (nat_lit 0) D2M8K2.t1549 from rfl, allE_node, rows1548, irow1544, rows1549]
  all_goals rfl

theorem atot1544 : totK PD2M8K2 D2M8K2.u1544 = [0, 318348875411, 857967634927, 535308045359, 75471687453, 2481160468, 0, 0] := by
  rw [show D2M8K2.u1544 = KTree.node D2M8K2.t1548 (nat_lit 3083211) (nat_lit 3773144805) (nat_lit 0) D2M8K2.t1549 from rfl, totK_node, tot1548, tot1549]
  decide +kernel

theorem arows1545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1545 = true := by
  rw [show D2M8K2.u1545 = KTree.node D2M8K2.t1550 (nat_lit 3084797) (nat_lit 2239468088) (nat_lit 0) D2M8K2.t1551 from rfl, allE_node, rows1550, irow1545, rows1551]
  all_goals rfl

theorem atot1545 : totK PD2M8K2 D2M8K2.u1545 = [0, 90852006335, 670591694844, 869002757717, 148006743606, 1096505104, 0, 0] := by
  rw [show D2M8K2.u1545 = KTree.node D2M8K2.t1550 (nat_lit 3084797) (nat_lit 2239468088) (nat_lit 0) D2M8K2.t1551 from rfl, totK_node, tot1550, tot1551]
  decide +kernel

theorem arows1549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1549 = true := by
  rw [show D2M8K2.u1549 = KTree.node D2M8K2.t1552 (nat_lit 3086740) (nat_lit 3706278238) (nat_lit 0) D2M8K2.t1553 from rfl, allE_node, rows1552, irow1549, rows1553]
  all_goals rfl

theorem atot1549 : totK PD2M8K2 D2M8K2.u1549 = [0, 348259125683, 856868998160, 505466258191, 92157974808, 3884009855, 0, 0] := by
  rw [show D2M8K2.u1549 = KTree.node D2M8K2.t1552 (nat_lit 3086740) (nat_lit 3706278238) (nat_lit 0) D2M8K2.t1553 from rfl, totK_node, tot1552, tot1553]
  decide +kernel

theorem arows1550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1550 = true := by
  rw [show D2M8K2.u1550 = KTree.node D2M8K2.t1554 (nat_lit 3088289) (nat_lit 2107543042) (nat_lit 0) D2M8K2.t1555 from rfl, allE_node, rows1554, irow1550, rows1555]
  all_goals rfl

theorem atot1550 : totK PD2M8K2 D2M8K2.u1550 = [0, 66402094079, 541995632582, 885334583253, 272687693567, 8708200738, 0, 0] := by
  rw [show D2M8K2.u1550 = KTree.node D2M8K2.t1554 (nat_lit 3088289) (nat_lit 2107543042) (nat_lit 0) D2M8K2.t1555 from rfl, totK_node, tot1554, tot1555]
  decide +kernel

theorem arows1552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1552 = true := by
  rw [show D2M8K2.u1552 = KTree.node D2M8K2.t1556 (nat_lit 3090272) (nat_lit 3522676669) (nat_lit 0) D2M8K2.t1557 from rfl, allE_node, rows1556, irow1552, rows1557]
  all_goals rfl

theorem atot1552 : totK PD2M8K2 D2M8K2.u1552 = [0, 0, 396691488278, 949972307501, 406988077352, 24358390853, 0, 0] := by
  rw [show D2M8K2.u1552 = KTree.node D2M8K2.t1556 (nat_lit 3090272) (nat_lit 3522676669) (nat_lit 0) D2M8K2.t1557 from rfl, totK_node, tot1556, tot1557]
  decide +kernel

theorem arows1553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1553 = true := by
  rw [show D2M8K2.u1553 = KTree.node D2M8K2.t1558 (nat_lit 3091544) (nat_lit 3331052932) (nat_lit 0) D2M8K2.t1559 from rfl, allE_node, rows1558, irow1553, rows1559]
  all_goals rfl

theorem atot1553 : totK PD2M8K2 D2M8K2.u1553 = [0, 0, 97940620354, 733708089874, 791484032556, 105390354062, 1206465782, 0] := by
  rw [show D2M8K2.u1553 = KTree.node D2M8K2.t1558 (nat_lit 3091544) (nat_lit 3331052932) (nat_lit 0) D2M8K2.t1559 from rfl, totK_node, tot1558, tot1559]
  decide +kernel

theorem arows1556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1556 = true := by
  rw [show D2M8K2.u1556 = KTree.node D2M8K2.t1560 (nat_lit 3094332) (nat_lit 2960713645) (nat_lit 0) D2M8K2.t1561 from rfl, allE_node, rows1560, irow1556, rows1561]
  all_goals rfl

theorem atot1556 : totK PD2M8K2 D2M8K2.u1556 = [0, 0, 412880851599, 968934179812, 407311591303, 21120756654, 0, 0] := by
  rw [show D2M8K2.u1556 = KTree.node D2M8K2.t1560 (nat_lit 3094332) (nat_lit 2960713645) (nat_lit 0) D2M8K2.t1561 from rfl, totK_node, tot1560, tot1561]
  decide +kernel

theorem arows1557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1557 = true := by
  rw [show D2M8K2.u1557 = KTree.node D2M8K2.t1562 (nat_lit 3097346) (nat_lit 4025770644) (nat_lit 0) D2M8K2.t1563 from rfl, allE_node, rows1562, irow1557, rows1563]
  all_goals rfl

theorem atot1557 : totK PD2M8K2 D2M8K2.u1557 = [0, 0, 351075293417, 945918886578, 468322288156, 24452963376, 0, 0] := by
  rw [show D2M8K2.u1557 = KTree.node D2M8K2.t1562 (nat_lit 3097346) (nat_lit 4025770644) (nat_lit 0) D2M8K2.t1563 from rfl, totK_node, tot1562, tot1563]
  decide +kernel

theorem arows1559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1559 = true := by
  rw [show D2M8K2.u1559 = KTree.node D2M8K2.t1564 (nat_lit 3099046) (nat_lit 2327691398) (nat_lit 0) D2M8K2.t1565 from rfl, allE_node, rows1564, irow1559, rows1565]
  all_goals rfl

theorem atot1559 : totK PD2M8K2 D2M8K2.u1559 = [0, 0, 58987240919, 531303073673, 853774887447, 250981695577, 13016197374, 0] := by
  rw [show D2M8K2.u1559 = KTree.node D2M8K2.t1564 (nat_lit 3099046) (nat_lit 2327691398) (nat_lit 0) D2M8K2.t1565 from rfl, totK_node, tot1564, tot1565]
  decide +kernel

theorem arows1560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1560 = true := by
  rw [show D2M8K2.u1560 = KTree.node D2M8K2.t1566 (nat_lit 3104230) (nat_lit 2301139849) (nat_lit 0) D2M8K2.t1567 from rfl, allE_node, rows1566, irow1560, rows1567]
  all_goals rfl

theorem atot1560 : totK PD2M8K2 D2M8K2.u1560 = [0, 0, 348120428106, 945231541446, 440984062091, 19786607380, 0, 0] := by
  rw [show D2M8K2.u1560 = KTree.node D2M8K2.t1566 (nat_lit 3104230) (nat_lit 2301139849) (nat_lit 0) D2M8K2.t1567 from rfl, totK_node, tot1566, tot1567]
  decide +kernel

theorem arows1565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1565 = true := by
  rw [show D2M8K2.u1565 = KTree.node D2M8K2.t1568 (nat_lit 3106384) (nat_lit 3170405825) (nat_lit 0) D2M8K2.t1569 from rfl, allE_node, rows1568, irow1565, rows1569]
  all_goals rfl

theorem atot1565 : totK PD2M8K2 D2M8K2.u1565 = [0, 0, 138250420949, 685976276656, 725927629768, 136082563603, 4574395652, 0] := by
  rw [show D2M8K2.u1565 = KTree.node D2M8K2.t1568 (nat_lit 3106384) (nat_lit 3170405825) (nat_lit 0) D2M8K2.t1569 from rfl, totK_node, tot1568, tot1569]
  decide +kernel

theorem arows1566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1566 = true := by
  rw [show D2M8K2.u1566 = KTree.node D2M8K2.t1570 (nat_lit 3107981) (nat_lit 1349290865) (nat_lit 512) D2M8K2.t1571 from rfl, allE_node, rows1570, irow1566, rows1571]
  all_goals rfl

theorem atot1566 : totK PD2M8K2 D2M8K2.u1566 = [0, 90907693037, 457681407684, 816806984965, 412410091864, 28033242286, 0, 0] := by
  rw [show D2M8K2.u1566 = KTree.node D2M8K2.t1570 (nat_lit 3107981) (nat_lit 1349290865) (nat_lit 512) D2M8K2.t1571 from rfl, totK_node, tot1570, tot1571]
  decide +kernel

theorem arows1568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1568 = true := by
  rw [show D2M8K2.u1568 = KTree.node D2M8K2.t1572 (nat_lit 3111565) (nat_lit 1385917071) (nat_lit 0) D2M8K2.t1573 from rfl, allE_node, rows1572, irow1568, rows1573]
  all_goals rfl

theorem atot1568 : totK PD2M8K2 D2M8K2.u1568 = [0, 331519811888, 919576200564, 512434998208, 36064407416, 0, 0, 0] := by
  rw [show D2M8K2.u1568 = KTree.node D2M8K2.t1572 (nat_lit 3111565) (nat_lit 1385917071) (nat_lit 0) D2M8K2.t1573 from rfl, totK_node, tot1572, tot1573]
  decide +kernel

theorem arows1569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1569 = true := by
  rw [show D2M8K2.u1569 = KTree.node D2M8K2.t1574 (nat_lit 3113358) (nat_lit 3974425274) (nat_lit 0) D2M8K2.t1575 from rfl, allE_node, rows1574, irow1569, rows1575]
  all_goals rfl

theorem atot1569 : totK PD2M8K2 D2M8K2.u1569 = [0, 162528288142, 702066262188, 815089117266, 142786274005, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1569 = KTree.node D2M8K2.t1574 (nat_lit 3113358) (nat_lit 3974425274) (nat_lit 0) D2M8K2.t1575 from rfl, totK_node, tot1574, tot1575]
  decide +kernel

theorem arows1572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1572 = true := by
  rw [show D2M8K2.u1572 = KTree.node D2M8K2.t1576 (nat_lit 3115474) (nat_lit 4069434322) (nat_lit 0) D2M8K2.t1577 from rfl, allE_node, rows1576, irow1572, rows1577]
  all_goals rfl

theorem atot1572 : totK PD2M8K2 D2M8K2.u1572 = [0, 165324708119, 693117614478, 719922795091, 213374292237, 8070752097, 0, 0] := by
  rw [show D2M8K2.u1572 = KTree.node D2M8K2.t1576 (nat_lit 3115474) (nat_lit 4069434322) (nat_lit 0) D2M8K2.t1577 from rfl, totK_node, tot1576, tot1577]
  decide +kernel

theorem arows1573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1573 = true := by
  rw [show D2M8K2.u1573 = KTree.node D2M8K2.t1578 (nat_lit 3120864) (nat_lit 3592802183) (nat_lit 0) D2M8K2.t1579 from rfl, allE_node, rows1578, irow1573, rows1579]
  all_goals rfl

theorem atot1573 : totK PD2M8K2 D2M8K2.u1573 = [0, 245669156546, 699466002385, 664460085167, 193745715742, 5648725239, 0, 0] := by
  rw [show D2M8K2.u1573 = KTree.node D2M8K2.t1578 (nat_lit 3120864) (nat_lit 3592802183) (nat_lit 0) D2M8K2.t1579 from rfl, totK_node, tot1578, tot1579]
  decide +kernel

theorem arows1575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1575 = true := by
  rw [show D2M8K2.u1575 = KTree.node D2M8K2.t1580 (nat_lit 3122342) (nat_lit 4005331914) (nat_lit 0) D2M8K2.t1581 from rfl, allE_node, rows1580, irow1575, rows1581]
  all_goals rfl

theorem atot1575 : totK PD2M8K2 D2M8K2.u1575 = [0, 194016927859, 778783037814, 721071847298, 114186706523, 1198073392, 0, 0] := by
  rw [show D2M8K2.u1575 = KTree.node D2M8K2.t1580 (nat_lit 3122342) (nat_lit 4005331914) (nat_lit 0) D2M8K2.t1581 from rfl, totK_node, tot1580, tot1581]
  decide +kernel

theorem arows1576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1576 = true := by
  rw [show D2M8K2.u1576 = KTree.node D2M8K2.t1582 (nat_lit 3123995) (nat_lit 2880308392) (nat_lit 0) D2M8K2.t1583 from rfl, allE_node, rows1582, irow1576, rows1583]
  all_goals rfl

theorem atot1576 : totK PD2M8K2 D2M8K2.u1576 = [0, 162822319824, 629941005819, 736654251488, 230443707206, 12052611869, 0, 0] := by
  rw [show D2M8K2.u1576 = KTree.node D2M8K2.t1582 (nat_lit 3123995) (nat_lit 2880308392) (nat_lit 0) D2M8K2.t1583 from rfl, totK_node, tot1582, tot1583]
  decide +kernel

theorem arows1580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1580 = true := by
  rw [show D2M8K2.u1580 = KTree.node D2M8K2.t1584 (nat_lit 3125406) (nat_lit 3855791684) (nat_lit 0) D2M8K2.t1585 from rfl, allE_node, rows1584, irow1580, rows1585]
  all_goals rfl

theorem atot1580 : totK PD2M8K2 D2M8K2.u1580 = [0, 246440256485, 791030590302, 641110248370, 98341300251, 1096505104, 0, 0] := by
  rw [show D2M8K2.u1580 = KTree.node D2M8K2.t1584 (nat_lit 3125406) (nat_lit 3855791684) (nat_lit 0) D2M8K2.t1585 from rfl, totK_node, tot1584, tot1585]
  decide +kernel

theorem arows1581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1581 = true := by
  rw [show D2M8K2.u1581 = KTree.node D2M8K2.t1586 (nat_lit 3127689) (nat_lit 1731736626) (nat_lit 0) D2M8K2.t1587 from rfl, allE_node, rows1586, irow1581, rows1587]
  all_goals rfl

theorem atot1581 : totK PD2M8K2 D2M8K2.u1581 = [0, 196495657683, 722218818647, 728935477091, 144474007427, 3884009855, 0, 0] := by
  rw [show D2M8K2.u1581 = KTree.node D2M8K2.t1586 (nat_lit 3127689) (nat_lit 1731736626) (nat_lit 0) D2M8K2.t1587 from rfl, totK_node, tot1586, tot1587]
  decide +kernel

theorem arows1583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1583 = true := by
  rw [show D2M8K2.u1583 = KTree.node D2M8K2.t1588 (nat_lit 3129244) (nat_lit 3875180351) (nat_lit 0) D2M8K2.t1589 from rfl, allE_node, rows1588, irow1583, rows1589]
  all_goals rfl

theorem atot1583 : totK PD2M8K2 D2M8K2.u1583 = [0, 218243869123, 772526538058, 692938336173, 121913579651, 1268739303, 0, 0] := by
  rw [show D2M8K2.u1583 = KTree.node D2M8K2.t1588 (nat_lit 3129244) (nat_lit 3875180351) (nat_lit 0) D2M8K2.t1589 from rfl, totK_node, tot1588, tot1589]
  decide +kernel

theorem arows1584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1584 = true := by
  rw [show D2M8K2.u1584 = KTree.node D2M8K2.t1590 (nat_lit 3130940) (nat_lit 2670283772) (nat_lit 0) D2M8K2.t1591 from rfl, allE_node, rows1590, irow1584, rows1591]
  all_goals rfl

theorem atot1584 : totK PD2M8K2 D2M8K2.u1584 = [0, 0, 392646121130, 959386097746, 398226178866, 22143218390, 0, 0] := by
  rw [show D2M8K2.u1584 = KTree.node D2M8K2.t1590 (nat_lit 3130940) (nat_lit 2670283772) (nat_lit 0) D2M8K2.t1591 from rfl, totK_node, tot1590, tot1591]
  decide +kernel

theorem arows1587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1587 = true := by
  rw [show D2M8K2.u1587 = KTree.node D2M8K2.t1592 (nat_lit 3132528) (nat_lit 3397798539) (nat_lit 0) D2M8K2.t1593 from rfl, allE_node, rows1592, irow1587, rows1593]
  all_goals rfl

theorem atot1587 : totK PD2M8K2 D2M8K2.u1587 = [0, 0, 259268016322, 814179544755, 589448187275, 82389396836, 1239866073, 0] := by
  rw [show D2M8K2.u1587 = KTree.node D2M8K2.t1592 (nat_lit 3132528) (nat_lit 3397798539) (nat_lit 0) D2M8K2.t1593 from rfl, totK_node, tot1592, tot1593]
  decide +kernel

theorem arows1588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1588 = true := by
  rw [show D2M8K2.u1588 = KTree.node D2M8K2.t1594 (nat_lit 3134985) (nat_lit 1897289975) (nat_lit 0) D2M8K2.t1595 from rfl, allE_node, rows1594, irow1588, rows1595]
  all_goals rfl

theorem atot1588 : totK PD2M8K2 D2M8K2.u1588 = [0, 0, 243163140911, 861919938549, 640276040027, 50266019389, 0, 0] := by
  rw [show D2M8K2.u1588 = KTree.node D2M8K2.t1594 (nat_lit 3134985) (nat_lit 1897289975) (nat_lit 0) D2M8K2.t1595 from rfl, totK_node, tot1594, tot1595]
  decide +kernel

theorem arows1590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1590 = true := by
  rw [show D2M8K2.u1590 = KTree.node D2M8K2.t1596 (nat_lit 3141775) (nat_lit 1875006417) (nat_lit 0) D2M8K2.t1597 from rfl, allE_node, rows1596, irow1590, rows1597]
  all_goals rfl

theorem atot1590 : totK PD2M8K2 D2M8K2.u1590 = [0, 0, 361188682234, 950758195059, 469003177867, 26739617344, 0, 0] := by
  rw [show D2M8K2.u1590 = KTree.node D2M8K2.t1596 (nat_lit 3141775) (nat_lit 1875006417) (nat_lit 0) D2M8K2.t1597 from rfl, totK_node, tot1596, tot1597]
  decide +kernel

theorem arows1591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1591 = true := by
  rw [show D2M8K2.u1591 = KTree.node D2M8K2.t1598 (nat_lit 3143288) (nat_lit 3309803484) (nat_lit 0) D2M8K2.t1599 from rfl, allE_node, rows1598, irow1591, rows1599]
  all_goals rfl

theorem atot1591 : totK PD2M8K2 D2M8K2.u1591 = [0, 0, 159898812404, 690149883266, 716675818745, 175139505476, 8182138156, 0] := by
  rw [show D2M8K2.u1591 = KTree.node D2M8K2.t1598 (nat_lit 3143288) (nat_lit 3309803484) (nat_lit 0) D2M8K2.t1599 from rfl, totK_node, tot1598, tot1599]
  decide +kernel

theorem arows1597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1597 = true := by
  rw [show D2M8K2.u1597 = KTree.node D2M8K2.t1600 (nat_lit 3145126) (nat_lit 2283560379) (nat_lit 0) D2M8K2.t1601 from rfl, allE_node, rows1600, irow1597, rows1601]
  all_goals rfl

theorem atot1597 : totK PD2M8K2 D2M8K2.u1597 = [0, 0, 264246003484, 790962192701, 565318070829, 96989287250, 3472187823, 0] := by
  rw [show D2M8K2.u1597 = KTree.node D2M8K2.t1600 (nat_lit 3145126) (nat_lit 2283560379) (nat_lit 0) D2M8K2.t1601 from rfl, totK_node, tot1600, tot1601]
  decide +kernel

theorem arows1598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1598 = true := by
  rw [show D2M8K2.u1598 = KTree.node D2M8K2.t1602 (nat_lit 3146773) (nat_lit 1251378922) (nat_lit 0) D2M8K2.t1603 from rfl, allE_node, rows1602, irow1598, rows1603]
  all_goals rfl

theorem atot1598 : totK PD2M8K2 D2M8K2.u1598 = [0, 0, 143123251625, 762922771240, 726560870538, 90841507344, 1053411165, 0] := by
  rw [show D2M8K2.u1598 = KTree.node D2M8K2.t1602 (nat_lit 3146773) (nat_lit 1251378922) (nat_lit 0) D2M8K2.t1603 from rfl, totK_node, tot1602, tot1603]
  decide +kernel

theorem arows1600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1600 = true := by
  rw [show D2M8K2.u1600 = KTree.node D2M8K2.t1604 (nat_lit 3148882) (nat_lit 3994184913) (nat_lit 0) D2M8K2.t1605 from rfl, allE_node, rows1604, irow1600, rows1605]
  all_goals rfl

theorem atot1600 : totK PD2M8K2 D2M8K2.u1600 = [0, 0, 321055850556, 851876803924, 508849863519, 81850733305, 3667207281, 0] := by
  rw [show D2M8K2.u1600 = KTree.node D2M8K2.t1604 (nat_lit 3148882) (nat_lit 3994184913) (nat_lit 0) D2M8K2.t1605 from rfl, totK_node, tot1604, tot1605]
  decide +kernel

theorem arows1601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1601 = true := by
  rw [show D2M8K2.u1601 = KTree.node D2M8K2.t1606 (nat_lit 3152455) (nat_lit 2084537503) (nat_lit 0) D2M8K2.t1607 from rfl, allE_node, rows1606, irow1601, rows1607]
  all_goals rfl

theorem atot1601 : totK PD2M8K2 D2M8K2.u1601 = [0, 280420785384, 788192780216, 556018916743, 162204364172, 13566916688, 0, 0] := by
  rw [show D2M8K2.u1601 = KTree.node D2M8K2.t1606 (nat_lit 3152455) (nat_lit 2084537503) (nat_lit 0) D2M8K2.t1607 from rfl, totK_node, tot1606, tot1607]
  decide +kernel

theorem arows1604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1604 = true := by
  rw [show D2M8K2.u1604 = KTree.node D2M8K2.t1608 (nat_lit 3153696) (nat_lit 3619169329) (nat_lit 0) D2M8K2.t1609 from rfl, allE_node, rows1608, irow1604, rows1609]
  all_goals rfl

theorem atot1604 : totK PD2M8K2 D2M8K2.u1604 = [0, 137922024301, 710752164427, 806814393229, 138919598971, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1604 = KTree.node D2M8K2.t1608 (nat_lit 3153696) (nat_lit 3619169329) (nat_lit 0) D2M8K2.t1609 from rfl, totK_node, tot1608, tot1609]
  decide +kernel

theorem arows1605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1605 = true := by
  rw [show D2M8K2.u1605 = KTree.node D2M8K2.t1610 (nat_lit 3156110) (nat_lit 2653529726) (nat_lit 2048) D2M8K2.t1611 from rfl, allE_node, rows1610, irow1605, rows1611]
  all_goals rfl

theorem atot1605 : totK PD2M8K2 D2M8K2.u1605 = [0, 326096556241, 915389423260, 520837731086, 37633926948, 0, 0, 0] := by
  rw [show D2M8K2.u1605 = KTree.node D2M8K2.t1610 (nat_lit 3156110) (nat_lit 2653529726) (nat_lit 2048) D2M8K2.t1611 from rfl, totK_node, tot1610, tot1611]
  decide +kernel

theorem arows1607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1607 = true := by
  rw [show D2M8K2.u1607 = KTree.node D2M8K2.t1612 (nat_lit 3158022) (nat_lit 3872665113) (nat_lit 0) D2M8K2.t1613 from rfl, allE_node, rows1612, irow1607, rows1613]
  all_goals rfl

theorem atot1607 : totK PD2M8K2 D2M8K2.u1607 = [0, 85167078157, 475129341418, 867354976340, 341607207012, 10726140153, 0, 0] := by
  rw [show D2M8K2.u1607 = KTree.node D2M8K2.t1612 (nat_lit 3158022) (nat_lit 3872665113) (nat_lit 0) D2M8K2.t1613 from rfl, totK_node, tot1612, tot1613]
  decide +kernel

theorem arows1608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1608 = true := by
  rw [show D2M8K2.u1608 = KTree.node D2M8K2.t1614 (nat_lit 3159557) (nat_lit 2384514699) (nat_lit 0) D2M8K2.t1615 from rfl, allE_node, rows1614, irow1608, rows1615]
  all_goals rfl

theorem atot1608 : totK PD2M8K2 D2M8K2.u1608 = [0, 325981533770, 908229970491, 513538418914, 43113761083, 0, 0, 0] := by
  rw [show D2M8K2.u1608 = KTree.node D2M8K2.t1614 (nat_lit 3159557) (nat_lit 2384514699) (nat_lit 0) D2M8K2.t1615 from rfl, totK_node, tot1614, tot1615]
  decide +kernel

theorem arows1612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1612 = true := by
  rw [show D2M8K2.u1612 = KTree.node D2M8K2.t1616 (nat_lit 3161283) (nat_lit 2942356659) (nat_lit 0) D2M8K2.t1617 from rfl, allE_node, rows1616, irow1612, rows1617]
  all_goals rfl

theorem atot1612 : totK PD2M8K2 D2M8K2.u1612 = [0, 77354544009, 506182225045, 880342241761, 283703160277, 13049727234, 0, 0] := by
  rw [show D2M8K2.u1612 = KTree.node D2M8K2.t1616 (nat_lit 3161283) (nat_lit 2942356659) (nat_lit 0) D2M8K2.t1617 from rfl, totK_node, tot1616, tot1617]
  decide +kernel

theorem arows1613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1613 = true := by
  rw [show D2M8K2.u1613 = KTree.node D2M8K2.t1618 (nat_lit 3163255) (nat_lit 2359819404) (nat_lit 0) D2M8K2.t1619 from rfl, allE_node, rows1618, irow1613, rows1619]
  all_goals rfl

theorem atot1613 : totK PD2M8K2 D2M8K2.u1613 = [0, 330196738799, 920119322234, 505567696436, 37640258759, 0, 0, 0] := by
  rw [show D2M8K2.u1613 = KTree.node D2M8K2.t1618 (nat_lit 3163255) (nat_lit 2359819404) (nat_lit 0) D2M8K2.t1619 from rfl, totK_node, tot1618, tot1619]
  decide +kernel

theorem arows1615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1615 = true := by
  rw [show D2M8K2.u1615 = KTree.node D2M8K2.t1620 (nat_lit 3164974) (nat_lit 3943118590) (nat_lit 0) D2M8K2.t1621 from rfl, allE_node, rows1620, irow1615, rows1621]
  all_goals rfl

theorem atot1615 : totK PD2M8K2 D2M8K2.u1615 = [0, 47290973909, 488433520354, 914932954064, 301969262762, 13250685261, 0, 0] := by
  rw [show D2M8K2.u1615 = KTree.node D2M8K2.t1620 (nat_lit 3164974) (nat_lit 3943118590) (nat_lit 0) D2M8K2.t1621 from rfl, totK_node, tot1620, tot1621]
  decide +kernel

theorem arows1616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1616 = true := by
  rw [show D2M8K2.u1616 = KTree.node D2M8K2.t1622 (nat_lit 3166371) (nat_lit 3644560346) (nat_lit 0) D2M8K2.t1623 from rfl, allE_node, rows1622, irow1616, rows1623]
  all_goals rfl

theorem atot1616 : totK PD2M8K2 D2M8K2.u1616 = [0, 367297425235, 926189029007, 480925341186, 37636625340, 0, 0, 0] := by
  rw [show D2M8K2.u1616 = KTree.node D2M8K2.t1622 (nat_lit 3166371) (nat_lit 3644560346) (nat_lit 0) D2M8K2.t1623 from rfl, totK_node, tot1622, tot1623]
  decide +kernel

theorem arows1619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1619 = true := by
  rw [show D2M8K2.u1619 = KTree.node D2M8K2.t1624 (nat_lit 3168040) (nat_lit 3812028403) (nat_lit 0) D2M8K2.t1625 from rfl, allE_node, rows1624, irow1619, rows1625]
  all_goals rfl

theorem atot1619 : totK PD2M8K2 D2M8K2.u1619 = [0, 19228354030, 599433311951, 969749339593, 212457460747, 4980514959, 0, 0] := by
  rw [show D2M8K2.u1619 = KTree.node D2M8K2.t1624 (nat_lit 3168040) (nat_lit 3812028403) (nat_lit 0) D2M8K2.t1625 from rfl, totK_node, tot1624, tot1625]
  decide +kernel

theorem arows1620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1620 = true := by
  rw [show D2M8K2.u1620 = KTree.node D2M8K2.t1626 (nat_lit 3173576) (nat_lit 3869296688) (nat_lit 0) D2M8K2.t1627 from rfl, allE_node, rows1626, irow1620, rows1627]
  all_goals rfl

theorem atot1620 : totK PD2M8K2 D2M8K2.u1620 = [0, 0, 379888357068, 952660248450, 407448785917, 22162043758, 0, 0] := by
  rw [show D2M8K2.u1620 = KTree.node D2M8K2.t1626 (nat_lit 3173576) (nat_lit 3869296688) (nat_lit 0) D2M8K2.t1627 from rfl, totK_node, tot1626, tot1627]
  decide +kernel

theorem arows1622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1622 = true := by
  rw [show D2M8K2.u1622 = KTree.node D2M8K2.t1628 (nat_lit 3175516) (nat_lit 3514935932) (nat_lit 0) D2M8K2.t1629 from rfl, allE_node, rows1628, irow1622, rows1629]
  all_goals rfl

theorem atot1622 : totK PD2M8K2 D2M8K2.u1622 = [0, 0, 155465867603, 790468389142, 710246572644, 90350472760, 1138244013, 0] := by
  rw [show D2M8K2.u1622 = KTree.node D2M8K2.t1628 (nat_lit 3175516) (nat_lit 3514935932) (nat_lit 0) D2M8K2.t1629 from rfl, totK_node, tot1628, tot1629]
  decide +kernel

theorem arows1623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1623 = true := by
  rw [show D2M8K2.u1623 = KTree.node D2M8K2.t1630 (nat_lit 3177462) (nat_lit 3725576850) (nat_lit 0) D2M8K2.t1631 from rfl, allE_node, rows1630, irow1623, rows1631]
  all_goals rfl

theorem atot1623 : totK PD2M8K2 D2M8K2.u1623 = [0, 0, 368630825419, 958188398619, 421213331423, 18774786657, 0, 0] := by
  rw [show D2M8K2.u1623 = KTree.node D2M8K2.t1630 (nat_lit 3177462) (nat_lit 3725576850) (nat_lit 0) D2M8K2.t1631 from rfl, totK_node, tot1630, tot1631]
  decide +kernel

theorem arows1628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1628 = true := by
  rw [show D2M8K2.u1628 = KTree.node D2M8K2.t1632 (nat_lit 3181030) (nat_lit 3825229779) (nat_lit 0) D2M8K2.t1633 from rfl, allE_node, rows1632, irow1628, rows1633]
  all_goals rfl

theorem atot1628 : totK PD2M8K2 D2M8K2.u1628 = [0, 0, 373371912558, 950611295138, 420656475601, 19151474518, 0, 0] := by
  rw [show D2M8K2.u1628 = KTree.node D2M8K2.t1632 (nat_lit 3181030) (nat_lit 3825229779) (nat_lit 0) D2M8K2.t1633 from rfl, totK_node, tot1632, tot1633]
  decide +kernel

theorem arows1629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1629 = true := by
  rw [show D2M8K2.u1629 = KTree.node D2M8K2.t1634 (nat_lit 3184372) (nat_lit 3545287213) (nat_lit 0) D2M8K2.t1635 from rfl, allE_node, rows1634, irow1629, rows1635]
  all_goals rfl

theorem atot1629 : totK PD2M8K2 D2M8K2.u1629 = [0, 0, 387043875477, 945864291723, 422390436104, 18931416259, 0, 0] := by
  rw [show D2M8K2.u1629 = KTree.node D2M8K2.t1634 (nat_lit 3184372) (nat_lit 3545287213) (nat_lit 0) D2M8K2.t1635 from rfl, totK_node, tot1634, tot1635]
  decide +kernel

theorem arows1631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1631 = true := by
  rw [show D2M8K2.u1631 = KTree.node D2M8K2.t1636 (nat_lit 3187408) (nat_lit 2809303705) (nat_lit 0) D2M8K2.t1637 from rfl, allE_node, rows1636, irow1631, rows1637]
  all_goals rfl

theorem atot1631 : totK PD2M8K2 D2M8K2.u1631 = [0, 0, 294947291199, 893000795821, 529126105424, 42313909305, 0, 0] := by
  rw [show D2M8K2.u1631 = KTree.node D2M8K2.t1636 (nat_lit 3187408) (nat_lit 2809303705) (nat_lit 0) D2M8K2.t1637 from rfl, totK_node, tot1636, tot1637]
  decide +kernel

theorem arows1632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1632 = true := by
  rw [show D2M8K2.u1632 = KTree.node D2M8K2.t1638 (nat_lit 3189391) (nat_lit 2424167924) (nat_lit 0) D2M8K2.t1639 from rfl, allE_node, rows1638, irow1632, rows1639]
  all_goals rfl

theorem atot1632 : totK PD2M8K2 D2M8K2.u1632 = [0, 176791677709, 369822514279, 448317909801, 595136995289, 153466041709, 4977114383, 0] := by
  rw [show D2M8K2.u1632 = KTree.node D2M8K2.t1638 (nat_lit 3189391) (nat_lit 2424167924) (nat_lit 0) D2M8K2.t1639 from rfl, totK_node, tot1638, tot1639]
  decide +kernel

theorem arows1635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1635 = true := by
  rw [show D2M8K2.u1635 = KTree.node D2M8K2.t1640 (nat_lit 3194719) (nat_lit 2385811682) (nat_lit 0) D2M8K2.t1641 from rfl, allE_node, rows1640, irow1635, rows1641]
  all_goals rfl

theorem atot1635 : totK PD2M8K2 D2M8K2.u1635 = [0, 245872083852, 795477271722, 643088427864, 103517837524, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1635 = KTree.node D2M8K2.t1640 (nat_lit 3194719) (nat_lit 2385811682) (nat_lit 0) D2M8K2.t1641 from rfl, totK_node, tot1640, tot1641]
  decide +kernel

theorem arows1636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1636 = true := by
  rw [show D2M8K2.u1636 = KTree.node D2M8K2.t1642 (nat_lit 3196651) (nat_lit 1551938790) (nat_lit 0) D2M8K2.t1643 from rfl, allE_node, rows1642, irow1636, rows1643]
  all_goals rfl

theorem atot1636 : totK PD2M8K2 D2M8K2.u1636 = [0, 203739346664, 792493456919, 748669794083, 82466660294, 0, 0, 0] := by
  rw [show D2M8K2.u1636 = KTree.node D2M8K2.t1642 (nat_lit 3196651) (nat_lit 1551938790) (nat_lit 0) D2M8K2.t1643 from rfl, totK_node, tot1642, tot1643]
  decide +kernel

theorem arows1638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1638 = true := by
  rw [show D2M8K2.u1638 = KTree.node D2M8K2.t1644 (nat_lit 3198937) (nat_lit 940340346) (nat_lit 0) D2M8K2.t1645 from rfl, allE_node, rows1644, irow1638, rows1645]
  all_goals rfl

theorem atot1638 : totK PD2M8K2 D2M8K2.u1638 = [0, 121836556003, 622821341866, 798576046082, 258929878596, 8585356005, 0, 0] := by
  rw [show D2M8K2.u1638 = KTree.node D2M8K2.t1644 (nat_lit 3198937) (nat_lit 940340346) (nat_lit 0) D2M8K2.t1645 from rfl, totK_node, tot1644, tot1645]
  decide +kernel

theorem arows1639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1639 = true := by
  rw [show D2M8K2.u1639 = KTree.node D2M8K2.t1646 (nat_lit 3200573) (nat_lit 2306284094) (nat_lit 0) D2M8K2.t1647 from rfl, allE_node, rows1646, irow1639, rows1647]
  all_goals rfl

theorem atot1639 : totK PD2M8K2 D2M8K2.u1639 = [0, 263347836700, 747512817989, 602964123823, 176858540768, 8340560233, 0, 0] := by
  rw [show D2M8K2.u1639 = KTree.node D2M8K2.t1646 (nat_lit 3200573) (nat_lit 2306284094) (nat_lit 0) D2M8K2.t1647 from rfl, totK_node, tot1646, tot1647]
  decide +kernel

theorem arows1643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1643 = true := by
  rw [show D2M8K2.u1643 = KTree.node D2M8K2.t1648 (nat_lit 3202076) (nat_lit 2444978290) (nat_lit 0) D2M8K2.t1649 from rfl, allE_node, rows1648, irow1643, rows1649]
  all_goals rfl

theorem atot1643 : totK PD2M8K2 D2M8K2.u1643 = [0, 146479006435, 650650504026, 774545317933, 204665152751, 9583672031, 0, 0] := by
  rw [show D2M8K2.u1643 = KTree.node D2M8K2.t1648 (nat_lit 3202076) (nat_lit 2444978290) (nat_lit 0) D2M8K2.t1649 from rfl, totK_node, tot1648, tot1649]
  decide +kernel

theorem arows1644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1644 = true := by
  rw [show D2M8K2.u1644 = KTree.node D2M8K2.t1650 (nat_lit 3203952) (nat_lit 3538739339) (nat_lit 0) D2M8K2.t1651 from rfl, allE_node, rows1650, irow1644, rows1651]
  all_goals rfl

theorem atot1644 : totK PD2M8K2 D2M8K2.u1644 = [0, 256093106644, 788170798683, 629955738932, 116671808534, 3460111309, 0, 0] := by
  rw [show D2M8K2.u1644 = KTree.node D2M8K2.t1650 (nat_lit 3203952) (nat_lit 3538739339) (nat_lit 0) D2M8K2.t1651 from rfl, totK_node, tot1650, tot1651]
  decide +kernel

theorem arows1646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1646 = true := by
  rw [show D2M8K2.u1646 = KTree.node D2M8K2.t1652 (nat_lit 3205498) (nat_lit 3746633215) (nat_lit 0) D2M8K2.t1653 from rfl, allE_node, rows1652, irow1646, rows1653]
  all_goals rfl

theorem atot1646 : totK PD2M8K2 D2M8K2.u1646 = [0, 156729966339, 674235302627, 774249420069, 182029086044, 5768874209, 0, 0] := by
  rw [show D2M8K2.u1646 = KTree.node D2M8K2.t1652 (nat_lit 3205498) (nat_lit 3746633215) (nat_lit 0) D2M8K2.t1653 from rfl, totK_node, tot1652, tot1653]
  decide +kernel

theorem arows1647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1647 = true := by
  rw [show D2M8K2.u1647 = KTree.node D2M8K2.t1654 (nat_lit 3210776) (nat_lit 3264005468) (nat_lit 0) D2M8K2.t1655 from rfl, allE_node, rows1654, irow1647, rows1655]
  all_goals rfl

theorem atot1647 : totK PD2M8K2 D2M8K2.u1647 = [0, 260010502555, 763017822388, 631012451513, 143213369297, 7474910654, 0, 0] := by
  rw [show D2M8K2.u1647 = KTree.node D2M8K2.t1654 (nat_lit 3210776) (nat_lit 3264005468) (nat_lit 0) D2M8K2.t1655 from rfl, totK_node, tot1654, tot1655]
  decide +kernel

theorem arows1650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1650 = true := by
  rw [show D2M8K2.u1650 = KTree.node D2M8K2.t1656 (nat_lit 3212259) (nat_lit 3476449182) (nat_lit 0) D2M8K2.t1657 from rfl, allE_node, rows1656, irow1650, rows1657]
  all_goals rfl

theorem atot1650 : totK PD2M8K2 D2M8K2.u1650 = [0, 181674658392, 750648491345, 753925133901, 137459292627, 1268739303, 0, 0] := by
  rw [show D2M8K2.u1650 = KTree.node D2M8K2.t1656 (nat_lit 3212259) (nat_lit 3476449182) (nat_lit 0) D2M8K2.t1657 from rfl, totK_node, tot1656, tot1657]
  decide +kernel

theorem arows1651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1651 = true := by
  rw [show D2M8K2.u1651 = KTree.node D2M8K2.t1658 (nat_lit 3213925) (nat_lit 1364819205) (nat_lit 0) D2M8K2.t1659 from rfl, allE_node, rows1658, irow1651, rows1659]
  all_goals rfl

theorem atot1651 : totK PD2M8K2 D2M8K2.u1651 = [0, 0, 389072428098, 959494473960, 405886039120, 22149860293, 0, 0] := by
  rw [show D2M8K2.u1651 = KTree.node D2M8K2.t1658 (nat_lit 3213925) (nat_lit 1364819205) (nat_lit 0) D2M8K2.t1659 from rfl, totK_node, tot1658, tot1659]
  decide +kernel

theorem arows1653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1653 = true := by
  rw [show D2M8K2.u1653 = KTree.node D2M8K2.t1660 (nat_lit 3215525) (nat_lit 2306827367) (nat_lit 0) D2M8K2.t1661 from rfl, allE_node, rows1660, irow1653, rows1661]
  all_goals rfl

theorem atot1653 : totK PD2M8K2 D2M8K2.u1653 = [0, 0, 244573807231, 814259550526, 611386861297, 86170981587, 1310285577, 0] := by
  rw [show D2M8K2.u1653 = KTree.node D2M8K2.t1660 (nat_lit 3215525) (nat_lit 2306827367) (nat_lit 0) D2M8K2.t1661 from rfl, totK_node, tot1660, tot1661]
  decide +kernel

theorem arows1654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1654 = true := by
  rw [show D2M8K2.u1654 = KTree.node D2M8K2.t1662 (nat_lit 3217893) (nat_lit 1133637344) (nat_lit 2) D2M8K2.t1663 from rfl, allE_node, rows1662, irow1654, rows1663]
  all_goals rfl

theorem atot1654 : totK PD2M8K2 D2M8K2.u1654 = [0, 0, 239131204436, 830967489933, 677488438767, 54391851589, 0, 0] := by
  rw [show D2M8K2.u1654 = KTree.node D2M8K2.t1662 (nat_lit 3217893) (nat_lit 1133637344) (nat_lit 2) D2M8K2.t1663 from rfl, totK_node, tot1662, tot1663]
  decide +kernel

theorem arows1661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1661 = true := by
  rw [show D2M8K2.u1661 = KTree.node D2M8K2.t1664 (nat_lit 3221216) (nat_lit 2513604956) (nat_lit 0) D2M8K2.t1665 from rfl, allE_node, rows1664, irow1661, rows1665]
  all_goals rfl

theorem atot1661 : totK PD2M8K2 D2M8K2.u1661 = [0, 0, 344291722675, 951338703764, 477732071888, 29645340015, 0, 0] := by
  rw [show D2M8K2.u1661 = KTree.node D2M8K2.t1664 (nat_lit 3221216) (nat_lit 2513604956) (nat_lit 0) D2M8K2.t1665 from rfl, totK_node, tot1664, tot1665]
  decide +kernel

theorem arows1662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1662 = true := by
  rw [show D2M8K2.u1662 = KTree.node D2M8K2.t1666 (nat_lit 3222804) (nat_lit 3028294347) (nat_lit 0) D2M8K2.t1667 from rfl, allE_node, rows1666, irow1662, rows1667]
  all_goals rfl

theorem atot1662 : totK PD2M8K2 D2M8K2.u1662 = [0, 0, 155794207477, 691423178605, 727033394137, 148258697773, 4879840392, 0] := by
  rw [show D2M8K2.u1662 = KTree.node D2M8K2.t1666 (nat_lit 3222804) (nat_lit 3028294347) (nat_lit 0) D2M8K2.t1667 from rfl, totK_node, tot1666, tot1667]
  decide +kernel

theorem arows1664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1664 = true := by
  rw [show D2M8K2.u1664 = KTree.node D2M8K2.t1668 (nat_lit 3224911) (nat_lit 2245895580) (nat_lit 0) D2M8K2.t1669 from rfl, allE_node, rows1668, irow1664, rows1669]
  all_goals rfl

theorem atot1664 : totK PD2M8K2 D2M8K2.u1664 = [0, 0, 322180617516, 919968113072, 507041991525, 35834187737, 0, 0] := by
  rw [show D2M8K2.u1664 = KTree.node D2M8K2.t1668 (nat_lit 3224911) (nat_lit 2245895580) (nat_lit 0) D2M8K2.t1669 from rfl, totK_node, tot1668, tot1669]
  decide +kernel

theorem arows1665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1665 = true := by
  rw [show D2M8K2.u1665 = KTree.node D2M8K2.t1670 (nat_lit 3226547) (nat_lit 2700065295) (nat_lit 0) D2M8K2.t1671 from rfl, allE_node, rows1670, irow1665, rows1671]
  all_goals rfl

theorem atot1665 : totK PD2M8K2 D2M8K2.u1665 = [0, 0, 107497780954, 647762244663, 811063770891, 169305415987, 4931404646, 0] := by
  rw [show D2M8K2.u1665 = KTree.node D2M8K2.t1670 (nat_lit 3226547) (nat_lit 2700065295) (nat_lit 0) D2M8K2.t1671 from rfl, totK_node, tot1670, tot1671]
  decide +kernel

theorem arows1668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1668 = true := by
  rw [show D2M8K2.u1668 = KTree.node D2M8K2.t1672 (nat_lit 3232000) (nat_lit 3778076146) (nat_lit 0) D2M8K2.t1673 from rfl, allE_node, rows1672, irow1668, rows1673]
  all_goals rfl

theorem atot1668 : totK PD2M8K2 D2M8K2.u1668 = [0, 0, 401536587125, 953425504413, 435439093915, 21298609454, 0, 0] := by
  rw [show D2M8K2.u1668 = KTree.node D2M8K2.t1672 (nat_lit 3232000) (nat_lit 3778076146) (nat_lit 0) D2M8K2.t1673 from rfl, totK_node, tot1672, tot1673]
  decide +kernel

theorem arows1669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1669 = true := by
  rw [show D2M8K2.u1669 = KTree.node D2M8K2.t1674 (nat_lit 3233690) (nat_lit 4188202606) (nat_lit 0) D2M8K2.t1675 from rfl, allE_node, rows1674, irow1669, rows1675]
  all_goals rfl

theorem atot1669 : totK PD2M8K2 D2M8K2.u1669 = [0, 0, 19735703396, 546711457238, 914373378663, 240986309640, 8424427256, 0] := by
  rw [show D2M8K2.u1669 = KTree.node D2M8K2.t1674 (nat_lit 3233690) (nat_lit 4188202606) (nat_lit 0) D2M8K2.t1675 from rfl, totK_node, tot1674, tot1675]
  decide +kernel

theorem arows1671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1671 = true := by
  rw [show D2M8K2.u1671 = KTree.node D2M8K2.t1676 (nat_lit 3235519) (nat_lit 1754300578) (nat_lit 0) D2M8K2.t1677 from rfl, allE_node, rows1676, irow1671, rows1677]
  all_goals rfl

theorem atot1671 : totK PD2M8K2 D2M8K2.u1671 = [0, 0, 352716480902, 831618417434, 469752018135, 128950850074, 13326740810, 0] := by
  rw [show D2M8K2.u1671 = KTree.node D2M8K2.t1676 (nat_lit 3235519) (nat_lit 1754300578) (nat_lit 0) D2M8K2.t1677 from rfl, totK_node, tot1676, tot1677]
  decide +kernel

theorem arows1672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1672 = true := by
  rw [show D2M8K2.u1672 = KTree.node D2M8K2.t1678 (nat_lit 3236698) (nat_lit 3652664584) (nat_lit 0) D2M8K2.t1679 from rfl, allE_node, rows1678, irow1672, rows1679]
  all_goals rfl

theorem atot1672 : totK PD2M8K2 D2M8K2.u1672 = [0, 0, 87720539117, 686785542938, 871356902313, 145371390938, 1369150432, 0] := by
  rw [show D2M8K2.u1672 = KTree.node D2M8K2.t1678 (nat_lit 3236698) (nat_lit 3652664584) (nat_lit 0) D2M8K2.t1679 from rfl, totK_node, tot1678, tot1679]
  decide +kernel

theorem arows1676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1676 = true := by
  rw [show D2M8K2.u1676 = KTree.node D2M8K2.t1680 (nat_lit 3242315) (nat_lit 2888716578) (nat_lit 0) D2M8K2.t1681 from rfl, allE_node, rows1680, irow1676, rows1681]
  all_goals rfl

theorem atot1676 : totK PD2M8K2 D2M8K2.u1676 = [0, 0, 356818487794, 905346785083, 479310775004, 35735217732, 0, 0] := by
  rw [show D2M8K2.u1676 = KTree.node D2M8K2.t1680 (nat_lit 3242315) (nat_lit 2888716578) (nat_lit 0) D2M8K2.t1681 from rfl, totK_node, tot1680, tot1681]
  decide +kernel

theorem arows1677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1677 = true := by
  rw [show D2M8K2.u1677 = KTree.node D2M8K2.t1682 (nat_lit 3243871) (nat_lit 1605344490) (nat_lit 0) D2M8K2.t1683 from rfl, allE_node, rows1682, irow1677, rows1683]
  all_goals rfl

theorem atot1677 : totK PD2M8K2 D2M8K2.u1677 = [0, 0, 55669940329, 530964070455, 872114444871, 248541880554, 12891658009, 0] := by
  rw [show D2M8K2.u1677 = KTree.node D2M8K2.t1682 (nat_lit 3243871) (nat_lit 1605344490) (nat_lit 0) D2M8K2.t1683 from rfl, totK_node, tot1682, tot1683]
  decide +kernel

theorem arows1679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1679 = true := by
  rw [show D2M8K2.u1679 = KTree.node D2M8K2.t1684 (nat_lit 3245759) (nat_lit 1746543188) (nat_lit 0) D2M8K2.t1685 from rfl, allE_node, rows1684, irow1679, rows1685]
  all_goals rfl

theorem atot1679 : totK PD2M8K2 D2M8K2.u1679 = [0, 0, 346945080241, 892441681091, 497594324122, 37455585791, 0, 0] := by
  rw [show D2M8K2.u1679 = KTree.node D2M8K2.t1684 (nat_lit 3245759) (nat_lit 1746543188) (nat_lit 0) D2M8K2.t1685 from rfl, totK_node, tot1684, tot1685]
  decide +kernel

theorem arows1680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1680 = true := by
  rw [show D2M8K2.u1680 = KTree.node D2M8K2.t1686 (nat_lit 3247312) (nat_lit 2088828897) (nat_lit 8) D2M8K2.t1687 from rfl, allE_node, rows1686, irow1680, rows1687]
  all_goals rfl

theorem atot1680 : totK PD2M8K2 D2M8K2.u1680 = [0, 0, 67405133671, 537215688258, 851425142542, 254443974687, 13092379805, 0] := by
  rw [show D2M8K2.u1680 = KTree.node D2M8K2.t1686 (nat_lit 3247312) (nat_lit 2088828897) (nat_lit 8) D2M8K2.t1687 from rfl, totK_node, tot1686, tot1687]
  decide +kernel

theorem arows1683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1683 = true := by
  rw [show D2M8K2.u1683 = KTree.node D2M8K2.t1688 (nat_lit 3249169) (nat_lit 1171846406) (nat_lit 0) D2M8K2.t1689 from rfl, allE_node, rows1688, irow1683, rows1689]
  all_goals rfl

theorem atot1683 : totK PD2M8K2 D2M8K2.u1683 = [0, 0, 321421172707, 862718951007, 520397150074, 44733342516, 0, 0] := by
  rw [show D2M8K2.u1683 = KTree.node D2M8K2.t1688 (nat_lit 3249169) (nat_lit 1171846406) (nat_lit 0) D2M8K2.t1689 from rfl, totK_node, tot1688, tot1689]
  decide +kernel

theorem arows1684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1684 = true := by
  rw [show D2M8K2.u1684 = KTree.node D2M8K2.t1690 (nat_lit 3250742) (nat_lit 2083044935) (nat_lit 2088) D2M8K2.t1691 from rfl, allE_node, rows1690, irow1684, rows1691]
  all_goals rfl

theorem atot1684 : totK PD2M8K2 D2M8K2.u1684 = [0, 0, 90582212958, 639763346429, 854946293797, 159746022755, 2165917952, 0] := by
  rw [show D2M8K2.u1684 = KTree.node D2M8K2.t1690 (nat_lit 3250742) (nat_lit 2083044935) (nat_lit 2088) D2M8K2.t1691 from rfl, totK_node, tot1690, tot1691]
  decide +kernel

theorem arows1686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1686 = true := by
  rw [show D2M8K2.u1686 = KTree.node D2M8K2.t1692 (nat_lit 3252742) (nat_lit 3816079831) (nat_lit 0) D2M8K2.t1693 from rfl, allE_node, rows1692, irow1686, rows1693]
  all_goals rfl

theorem atot1686 : totK PD2M8K2 D2M8K2.u1686 = [0, 0, 396832828058, 907341979636, 425248053284, 43667638861, 2768613583, 0] := by
  rw [show D2M8K2.u1686 = KTree.node D2M8K2.t1692 (nat_lit 3252742) (nat_lit 3816079831) (nat_lit 0) D2M8K2.t1693 from rfl, totK_node, tot1692, tot1693]
  decide +kernel

theorem arows1687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1687 = true := by
  rw [show D2M8K2.u1687 = KTree.node D2M8K2.t1694 (nat_lit 3254431) (nat_lit 1145036779) (nat_lit 0) D2M8K2.t1695 from rfl, allE_node, rows1694, irow1687, rows1695]
  all_goals rfl

theorem atot1687 : totK PD2M8K2 D2M8K2.u1687 = [0, 0, 19692840307, 528454635547, 928564138080, 255236365644, 8631701021, 0] := by
  rw [show D2M8K2.u1687 = KTree.node D2M8K2.t1694 (nat_lit 3254431) (nat_lit 1145036779) (nat_lit 0) D2M8K2.t1695 from rfl, totK_node, tot1694, tot1695]
  decide +kernel

theorem arows1692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1692 = true := by
  rw [show D2M8K2.u1692 = KTree.node D2M8K2.t1696 (nat_lit 3256258) (nat_lit 4107158209) (nat_lit 0) D2M8K2.t1697 from rfl, allE_node, rows1696, irow1692, rows1697]
  all_goals rfl

theorem atot1692 : totK PD2M8K2 D2M8K2.u1692 = [0, 0, 0, 366160764574, 935130616928, 426081444296, 31143077448, 0] := by
  rw [show D2M8K2.u1692 = KTree.node D2M8K2.t1696 (nat_lit 3256258) (nat_lit 4107158209) (nat_lit 0) D2M8K2.t1697 from rfl, totK_node, tot1696, tot1697]
  decide +kernel

theorem arows1693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1693 = true := by
  rw [show D2M8K2.u1693 = KTree.node D2M8K2.t1698 (nat_lit 3257476) (nat_lit 3712782091) (nat_lit 0) D2M8K2.t1699 from rfl, allE_node, rows1698, irow1693, rows1699]
  all_goals rfl

theorem atot1693 : totK PD2M8K2 D2M8K2.u1693 = [0, 0, 0, 85891556825, 693885593482, 789321999119, 139528699494, 1369150432] := by
  rw [show D2M8K2.u1693 = KTree.node D2M8K2.t1698 (nat_lit 3257476) (nat_lit 3712782091) (nat_lit 0) D2M8K2.t1699 from rfl, totK_node, tot1698, tot1699]
  decide +kernel

theorem arows1695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1695 = true := by
  rw [show D2M8K2.u1695 = KTree.node D2M8K2.t1700 (nat_lit 3263217) (nat_lit 1351684481) (nat_lit 0) D2M8K2.t1701 from rfl, allE_node, rows1700, irow1695, rows1701]
  all_goals rfl

theorem atot1695 : totK PD2M8K2 D2M8K2.u1695 = [0, 0, 0, 409380412519, 941658114170, 371932622897, 24212219102, 0] := by
  rw [show D2M8K2.u1695 = KTree.node D2M8K2.t1700 (nat_lit 3263217) (nat_lit 1351684481) (nat_lit 0) D2M8K2.t1701 from rfl, totK_node, tot1700, tot1701]
  decide +kernel

theorem arows1696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1696 = true := by
  rw [show D2M8K2.u1696 = KTree.node D2M8K2.t1702 (nat_lit 3266962) (nat_lit 3791421908) (nat_lit 0) D2M8K2.t1703 from rfl, allE_node, rows1702, irow1696, rows1703]
  all_goals rfl

theorem atot1696 : totK PD2M8K2 D2M8K2.u1696 = [0, 0, 0, 409579540978, 940547585126, 370997606260, 22228110555, 0] := by
  rw [show D2M8K2.u1696 = KTree.node D2M8K2.t1702 (nat_lit 3266962) (nat_lit 3791421908) (nat_lit 0) D2M8K2.t1703 from rfl, totK_node, tot1702, tot1703]
  decide +kernel

theorem arows1699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1699 = true := by
  rw [show D2M8K2.u1699 = KTree.node D2M8K2.t1704 (nat_lit 3270153) (nat_lit 1753499211) (nat_lit 0) D2M8K2.t1705 from rfl, allE_node, rows1704, irow1699, rows1705]
  all_goals rfl

theorem atot1699 : totK PD2M8K2 D2M8K2.u1699 = [0, 0, 0, 407345895775, 937478545146, 365384319852, 23955232979, 0] := by
  rw [show D2M8K2.u1699 = KTree.node D2M8K2.t1704 (nat_lit 3270153) (nat_lit 1753499211) (nat_lit 0) D2M8K2.t1705 from rfl, totK_node, tot1704, tot1705]
  decide +kernel

theorem arows1700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1700 = true := by
  rw [show D2M8K2.u1700 = KTree.node D2M8K2.t1706 (nat_lit 3273611) (nat_lit 2422604085) (nat_lit 0) D2M8K2.t1707 from rfl, allE_node, rows1706, irow1700, rows1707]
  all_goals rfl

theorem atot1700 : totK PD2M8K2 D2M8K2.u1700 = [0, 0, 0, 411640332619, 948795150432, 375103061196, 18225998578, 0] := by
  rw [show D2M8K2.u1700 = KTree.node D2M8K2.t1706 (nat_lit 3273611) (nat_lit 2422604085) (nat_lit 0) D2M8K2.t1707 from rfl, totK_node, tot1706, tot1707]
  decide +kernel

theorem arows1702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1702 = true := by
  rw [show D2M8K2.u1702 = KTree.node D2M8K2.t1708 (nat_lit 3318642) (nat_lit 3428356203) (nat_lit 0) D2M8K2.t1709 from rfl, allE_node, rows1708, irow1702, rows1709]
  all_goals rfl

theorem atot1702 : totK PD2M8K2 D2M8K2.u1702 = [0, 0, 394226098887, 925427628385, 406567623206, 38143555050, 6969953709, 0] := by
  rw [show D2M8K2.u1702 = KTree.node D2M8K2.t1708 (nat_lit 3318642) (nat_lit 3428356203) (nat_lit 0) D2M8K2.t1709 from rfl, totK_node, tot1708, tot1709]
  decide +kernel

theorem arows1703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1703 = true := by
  rw [show D2M8K2.u1703 = KTree.node D2M8K2.t1710 (nat_lit 3320195) (nat_lit 2947981234) (nat_lit 0) D2M8K2.t1711 from rfl, allE_node, rows1710, irow1703, rows1711]
  all_goals rfl

theorem atot1703 : totK PD2M8K2 D2M8K2.u1703 = [0, 0, 96813737248, 671126280380, 864594189630, 151584783526, 1369150432, 0] := by
  rw [show D2M8K2.u1703 = KTree.node D2M8K2.t1710 (nat_lit 3320195) (nat_lit 2947981234) (nat_lit 0) D2M8K2.t1711 from rfl, totK_node, tot1710, tot1711]
  decide +kernel

theorem arows1707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1707 = true := by
  rw [show D2M8K2.u1707 = KTree.node D2M8K2.t1712 (nat_lit 3322611) (nat_lit 2641549717) (nat_lit 128) D2M8K2.t1713 from rfl, allE_node, rows1712, irow1707, rows1713]
  all_goals rfl

theorem atot1707 : totK PD2M8K2 D2M8K2.u1707 = [0, 0, 361424482719, 954673181263, 462783868643, 25870315036, 0, 0] := by
  rw [show D2M8K2.u1707 = KTree.node D2M8K2.t1712 (nat_lit 3322611) (nat_lit 2641549717) (nat_lit 128) D2M8K2.t1713 from rfl, totK_node, tot1712, tot1713]
  decide +kernel

theorem arows1708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1708 = true := by
  rw [show D2M8K2.u1708 = KTree.node D2M8K2.t1714 (nat_lit 3325856) (nat_lit 3817391977) (nat_lit 0) D2M8K2.t1715 from rfl, allE_node, rows1714, irow1708, rows1715]
  all_goals rfl

theorem atot1708 : totK PD2M8K2 D2M8K2.u1708 = [0, 0, 325141764055, 901902402258, 546922852096, 40656488390, 0, 0] := by
  rw [show D2M8K2.u1708 = KTree.node D2M8K2.t1714 (nat_lit 3325856) (nat_lit 3817391977) (nat_lit 0) D2M8K2.t1715 from rfl, totK_node, tot1714, tot1715]
  decide +kernel

theorem arows1710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1710 = true := by
  rw [show D2M8K2.u1710 = KTree.node D2M8K2.t1716 (nat_lit 3327557) (nat_lit 2299794389) (nat_lit 0) D2M8K2.t1717 from rfl, allE_node, rows1716, irow1710, rows1717]
  all_goals rfl

theorem atot1710 : totK PD2M8K2 D2M8K2.u1710 = [0, 0, 84233131292, 543904024437, 853624022724, 246975302222, 13049727234, 0] := by
  rw [show D2M8K2.u1710 = KTree.node D2M8K2.t1716 (nat_lit 3327557) (nat_lit 2299794389) (nat_lit 0) D2M8K2.t1717 from rfl, totK_node, tot1716, tot1717]
  decide +kernel

theorem arows1711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1711 = true := by
  rw [show D2M8K2.u1711 = KTree.node D2M8K2.t1718 (nat_lit 3332424) (nat_lit 3301566151) (nat_lit 0) D2M8K2.t1719 from rfl, allE_node, rows1718, irow1711, rows1719]
  all_goals rfl

theorem atot1711 : totK PD2M8K2 D2M8K2.u1711 = [0, 0, 322899904159, 911972046004, 505211094249, 31394602316, 0, 0] := by
  rw [show D2M8K2.u1711 = KTree.node D2M8K2.t1718 (nat_lit 3332424) (nat_lit 3301566151) (nat_lit 0) D2M8K2.t1719 from rfl, totK_node, tot1718, tot1719]
  decide +kernel

theorem arows1714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1714 = true := by
  rw [show D2M8K2.u1714 = KTree.node D2M8K2.t1720 (nat_lit 3334522) (nat_lit 2743957682) (nat_lit 0) D2M8K2.t1721 from rfl, allE_node, rows1720, irow1714, rows1721]
  all_goals rfl

theorem atot1714 : totK PD2M8K2 D2M8K2.u1714 = [0, 0, 164123406694, 691305237099, 738145934647, 154215298972, 4917269347, 0] := by
  rw [show D2M8K2.u1714 = KTree.node D2M8K2.t1720 (nat_lit 3334522) (nat_lit 2743957682) (nat_lit 0) D2M8K2.t1721 from rfl, totK_node, tot1720, tot1721]
  decide +kernel

theorem arows1715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1715 = true := by
  rw [show D2M8K2.u1715 = KTree.node D2M8K2.t1722 (nat_lit 3336179) (nat_lit 2946963925) (nat_lit 0) D2M8K2.t1723 from rfl, allE_node, rows1722, irow1715, rows1723]
  all_goals rfl

theorem atot1715 : totK PD2M8K2 D2M8K2.u1715 = [0, 0, 248177597587, 812888704952, 640168365774, 94531483393, 1232398321, 0] := by
  rw [show D2M8K2.u1715 = KTree.node D2M8K2.t1722 (nat_lit 3336179) (nat_lit 2946963925) (nat_lit 0) D2M8K2.t1723 from rfl, totK_node, tot1722, tot1723]
  decide +kernel

theorem arows1717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1717 = true := by
  rw [show D2M8K2.u1717 = KTree.node D2M8K2.t1724 (nat_lit 3338353) (nat_lit 1493337294) (nat_lit 0) D2M8K2.t1725 from rfl, allE_node, rows1724, irow1717, rows1725]
  all_goals rfl

theorem atot1717 : totK PD2M8K2 D2M8K2.u1717 = [0, 0, 159868807160, 665426134501, 718344708241, 197020777549, 12451903996, 0] := by
  rw [show D2M8K2.u1717 = KTree.node D2M8K2.t1724 (nat_lit 3338353) (nat_lit 1493337294) (nat_lit 0) D2M8K2.t1725 from rfl, totK_node, tot1724, tot1725]
  decide +kernel

theorem arows1718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1718 = true := by
  rw [show D2M8K2.u1718 = KTree.node D2M8K2.t1726 (nat_lit 3360673) (nat_lit 1562614071) (nat_lit 0) D2M8K2.t1727 from rfl, allE_node, rows1726, irow1718, rows1727]
  all_goals rfl

theorem atot1718 : totK PD2M8K2 D2M8K2.u1718 = [0, 0, 257687754174, 785793171742, 621660079178, 104706131502, 1369150432, 0] := by
  rw [show D2M8K2.u1718 = KTree.node D2M8K2.t1726 (nat_lit 3360673) (nat_lit 1562614071) (nat_lit 0) D2M8K2.t1727 from rfl, totK_node, tot1726, tot1727]
  decide +kernel

theorem arows1724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1724 = true := by
  rw [show D2M8K2.u1724 = KTree.node D2M8K2.t1728 (nat_lit 3363051) (nat_lit 3710783078) (nat_lit 0) D2M8K2.t1729 from rfl, allE_node, rows1728, irow1724, rows1729]
  all_goals rfl

theorem atot1724 : totK PD2M8K2 D2M8K2.u1724 = [0, 0, 224618975371, 808299968572, 700917397022, 74628243833, 0, 0] := by
  rw [show D2M8K2.u1724 = KTree.node D2M8K2.t1728 (nat_lit 3363051) (nat_lit 3710783078) (nat_lit 0) D2M8K2.t1729 from rfl, totK_node, tot1728, tot1729]
  decide +kernel

theorem arows1725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1725 = true := by
  rw [show D2M8K2.u1725 = KTree.node D2M8K2.t1730 (nat_lit 3369800) (nat_lit 3416252201) (nat_lit 0) D2M8K2.t1731 from rfl, allE_node, rows1730, irow1725, rows1731]
  all_goals rfl

theorem atot1725 : totK PD2M8K2 D2M8K2.u1725 = [0, 0, 366086610026, 962728072803, 473833830756, 24830269282, 0, 0] := by
  rw [show D2M8K2.u1725 = KTree.node D2M8K2.t1730 (nat_lit 3369800) (nat_lit 3416252201) (nat_lit 0) D2M8K2.t1731 from rfl, totK_node, tot1730, tot1731]
  decide +kernel

theorem arows1727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1727 = true := by
  rw [show D2M8K2.u1727 = KTree.node D2M8K2.t1732 (nat_lit 3371276) (nat_lit 1532382989) (nat_lit 0) D2M8K2.t1733 from rfl, allE_node, rows1732, irow1727, rows1733]
  all_goals rfl

theorem atot1727 : totK PD2M8K2 D2M8K2.u1727 = [0, 0, 173823516313, 740532956555, 745029748245, 133214006904, 2329117419, 0] := by
  rw [show D2M8K2.u1727 = KTree.node D2M8K2.t1732 (nat_lit 3371276) (nat_lit 1532382989) (nat_lit 0) D2M8K2.t1733 from rfl, totK_node, tot1732, tot1733]
  decide +kernel

theorem arows1728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1728 = true := by
  rw [show D2M8K2.u1728 = KTree.node D2M8K2.t1734 (nat_lit 3373147) (nat_lit 2238214606) (nat_lit 0) D2M8K2.t1735 from rfl, allE_node, rows1734, irow1728, rows1735]
  all_goals rfl

theorem atot1728 : totK PD2M8K2 D2M8K2.u1728 = [0, 0, 228468113188, 712912186840, 630337787511, 152340270936, 10841558499, 0] := by
  rw [show D2M8K2.u1728 = KTree.node D2M8K2.t1734 (nat_lit 3373147) (nat_lit 2238214606) (nat_lit 0) D2M8K2.t1735 from rfl, totK_node, tot1734, tot1735]
  decide +kernel

theorem arows1731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1731 = true := by
  rw [show D2M8K2.u1731 = KTree.node D2M8K2.t1736 (nat_lit 3374454) (nat_lit 3754789756) (nat_lit 0) D2M8K2.t1737 from rfl, allE_node, rows1736, irow1731, rows1737]
  all_goals rfl

theorem atot1731 : totK PD2M8K2 D2M8K2.u1731 = [0, 0, 178725158610, 769156698407, 723776320512, 99435156862, 1096505104, 0] := by
  rw [show D2M8K2.u1731 = KTree.node D2M8K2.t1736 (nat_lit 3374454) (nat_lit 3754789756) (nat_lit 0) D2M8K2.t1737 from rfl, totK_node, tot1736, tot1737]
  decide +kernel

theorem arows1732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1732 = true := by
  rw [show D2M8K2.u1732 = KTree.node D2M8K2.t1738 (nat_lit 3376853) (nat_lit 1751054688) (nat_lit 514) D2M8K2.t1739 from rfl, allE_node, rows1738, irow1732, rows1739]
  all_goals rfl

theorem atot1732 : totK PD2M8K2 D2M8K2.u1732 = [0, 0, 320812187902, 833815892011, 535400407654, 87709381937, 3821179711, 0] := by
  rw [show D2M8K2.u1732 = KTree.node D2M8K2.t1738 (nat_lit 3376853) (nat_lit 1751054688) (nat_lit 514) D2M8K2.t1739 from rfl, totK_node, tot1738, tot1739]
  decide +kernel

theorem arows1734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1734 = true := by
  rw [show D2M8K2.u1734 = KTree.node D2M8K2.t1740 (nat_lit 3378402) (nat_lit 2567541942) (nat_lit 0) D2M8K2.t1741 from rfl, allE_node, rows1740, irow1734, rows1741]
  all_goals rfl

theorem atot1734 : totK PD2M8K2 D2M8K2.u1734 = [0, 0, 91570842872, 659396732308, 848789795333, 181167678231, 4957057700, 0] := by
  rw [show D2M8K2.u1734 = KTree.node D2M8K2.t1740 (nat_lit 3378402) (nat_lit 2567541942) (nat_lit 0) D2M8K2.t1741 from rfl, totK_node, tot1740, tot1741]
  decide +kernel

theorem arows1735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1735 = true := by
  rw [show D2M8K2.u1735 = KTree.node D2M8K2.t1742 (nat_lit 3401384) (nat_lit 3868830926) (nat_lit 0) D2M8K2.t1743 from rfl, allE_node, rows1742, irow1735, rows1743]
  all_goals rfl

theorem atot1735 : totK PD2M8K2 D2M8K2.u1735 = [0, 0, 332352214665, 819212917712, 497460570506, 110932085829, 8757608180, 0] := by
  rw [show D2M8K2.u1735 = KTree.node D2M8K2.t1742 (nat_lit 3401384) (nat_lit 3868830926) (nat_lit 0) D2M8K2.t1743 from rfl, totK_node, tot1742, tot1743]
  decide +kernel

theorem arows1739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1739 = true := by
  rw [show D2M8K2.u1739 = KTree.node D2M8K2.t1744 (nat_lit 3402625) (nat_lit 1489951043) (nat_lit 0) D2M8K2.t1745 from rfl, allE_node, rows1744, irow1739, rows1745]
  all_goals rfl

theorem atot1739 : totK PD2M8K2 D2M8K2.u1739 = [0, 0, 84744980936, 675796772302, 853566439565, 145419054434, 1369150432, 0] := by
  rw [show D2M8K2.u1739 = KTree.node D2M8K2.t1744 (nat_lit 3402625) (nat_lit 1489951043) (nat_lit 0) D2M8K2.t1745 from rfl, totK_node, tot1744, tot1745]
  decide +kernel

theorem arows1740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1740 = true := by
  rw [show D2M8K2.u1740 = KTree.node D2M8K2.t1746 (nat_lit 3405065) (nat_lit 1398141302) (nat_lit 0) D2M8K2.t1747 from rfl, allE_node, rows1746, irow1740, rows1747]
  all_goals rfl

theorem atot1740 : totK PD2M8K2 D2M8K2.u1740 = [0, 0, 389232015820, 933067150472, 440911434615, 32145520586, 0, 0] := by
  rw [show D2M8K2.u1740 = KTree.node D2M8K2.t1746 (nat_lit 3405065) (nat_lit 1398141302) (nat_lit 0) D2M8K2.t1747 from rfl, totK_node, tot1746, tot1747]
  decide +kernel

theorem arows1742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1742 = true := by
  rw [show D2M8K2.u1742 = KTree.node D2M8K2.t1748 (nat_lit 3408349) (nat_lit 1151579436) (nat_lit 0) D2M8K2.t1749 from rfl, allE_node, rows1748, irow1742, rows1749]
  all_goals rfl

theorem atot1742 : totK PD2M8K2 D2M8K2.u1742 = [0, 0, 344247985823, 935077141081, 481740832122, 23153927189, 0, 0] := by
  rw [show D2M8K2.u1742 = KTree.node D2M8K2.t1748 (nat_lit 3408349) (nat_lit 1151579436) (nat_lit 0) D2M8K2.t1749 from rfl, totK_node, tot1748, tot1749]
  decide +kernel

theorem arows1743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1743 = true := by
  rw [show D2M8K2.u1743 = KTree.node D2M8K2.t1750 (nat_lit 3410162) (nat_lit 3474713083) (nat_lit 0) D2M8K2.t1751 from rfl, allE_node, rows1750, irow1743, rows1751]
  all_goals rfl

theorem atot1743 : totK PD2M8K2 D2M8K2.u1743 = [0, 0, 84477287932, 551850659395, 831006040419, 238263656124, 12983449796, 0] := by
  rw [show D2M8K2.u1743 = KTree.node D2M8K2.t1750 (nat_lit 3410162) (nat_lit 3474713083) (nat_lit 0) D2M8K2.t1751 from rfl, totK_node, tot1750, tot1751]
  decide +kernel

theorem arows1746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1746 = true := by
  rw [show D2M8K2.u1746 = KTree.node D2M8K2.t1752 (nat_lit 3412192) (nat_lit 1792061012) (nat_lit 0) D2M8K2.t1753 from rfl, allE_node, rows1752, irow1746, rows1753]
  all_goals rfl

theorem atot1746 : totK PD2M8K2 D2M8K2.u1746 = [0, 0, 324656149756, 921757615854, 518508791988, 29597768105, 0, 0] := by
  rw [show D2M8K2.u1746 = KTree.node D2M8K2.t1752 (nat_lit 3412192) (nat_lit 1792061012) (nat_lit 0) D2M8K2.t1753 from rfl, totK_node, tot1752, tot1753]
  decide +kernel

theorem arows1747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1747 = true := by
  rw [show D2M8K2.u1747 = KTree.node D2M8K2.t1754 (nat_lit 3413984) (nat_lit 3817447700) (nat_lit 0) D2M8K2.t1755 from rfl, allE_node, rows1754, irow1747, rows1755]
  all_goals rfl

theorem atot1747 : totK PD2M8K2 D2M8K2.u1747 = [0, 0, 102556995953, 577834274299, 796122054128, 238298843624, 13184317400, 0] := by
  rw [show D2M8K2.u1747 = KTree.node D2M8K2.t1754 (nat_lit 3413984) (nat_lit 3817447700) (nat_lit 0) D2M8K2.t1755 from rfl, totK_node, tot1754, tot1755]
  decide +kernel

theorem arows1749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1749 = true := by
  rw [show D2M8K2.u1749 = KTree.node D2M8K2.t1756 (nat_lit 3415414) (nat_lit 3106012055) (nat_lit 0) D2M8K2.t1757 from rfl, allE_node, rows1756, irow1749, rows1757]
  all_goals rfl

theorem atot1749 : totK PD2M8K2 D2M8K2.u1749 = [0, 0, 333551571167, 916350214862, 519218627598, 32189588264, 0, 0] := by
  rw [show D2M8K2.u1749 = KTree.node D2M8K2.t1756 (nat_lit 3415414) (nat_lit 3106012055) (nat_lit 0) D2M8K2.t1757 from rfl, totK_node, tot1756, tot1757]
  decide +kernel

theorem arows1750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1750 = true := by
  rw [show D2M8K2.u1750 = KTree.node D2M8K2.t1758 (nat_lit 3417247) (nat_lit 2345006933) (nat_lit 0) D2M8K2.t1759 from rfl, allE_node, rows1758, irow1750, rows1759]
  all_goals rfl

theorem atot1750 : totK PD2M8K2 D2M8K2.u1750 = [0, 0, 118657156765, 654921179790, 815311942672, 174261159905, 4980514959, 0] := by
  rw [show D2M8K2.u1750 = KTree.node D2M8K2.t1758 (nat_lit 3417247) (nat_lit 2345006933) (nat_lit 0) D2M8K2.t1759 from rfl, totK_node, tot1758, tot1759]
  decide +kernel

theorem arows1755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1755 = true := by
  rw [show D2M8K2.u1755 = KTree.node D2M8K2.t1760 (nat_lit 3443400) (nat_lit 3542775029) (nat_lit 0) D2M8K2.t1761 from rfl, allE_node, rows1760, irow1755, rows1761]
  all_goals rfl

theorem atot1755 : totK PD2M8K2 D2M8K2.u1755 = [0, 0, 295483044727, 870477589455, 552595063723, 48160677607, 0, 0] := by
  rw [show D2M8K2.u1755 = KTree.node D2M8K2.t1760 (nat_lit 3443400) (nat_lit 3542775029) (nat_lit 0) D2M8K2.t1761 from rfl, totK_node, tot1760, tot1761]
  decide +kernel

theorem arows1756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1756 = true := by
  rw [show D2M8K2.u1756 = KTree.node D2M8K2.t1762 (nat_lit 3445371) (nat_lit 3519477387) (nat_lit 0) D2M8K2.t1763 from rfl, allE_node, rows1762, irow1756, rows1763]
  all_goals rfl

theorem atot1756 : totK PD2M8K2 D2M8K2.u1756 = [0, 0, 156141088578, 712839418033, 794715192106, 134788305119, 1369150432, 0] := by
  rw [show D2M8K2.u1756 = KTree.node D2M8K2.t1762 (nat_lit 3445371) (nat_lit 3519477387) (nat_lit 0) D2M8K2.t1763 from rfl, totK_node, tot1762, tot1763]
  decide +kernel

theorem arows1758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1758 = true := by
  rw [show D2M8K2.u1758 = KTree.node D2M8K2.t1764 (nat_lit 3449101) (nat_lit 1391311165) (nat_lit 0) D2M8K2.t1765 from rfl, allE_node, rows1764, irow1758, rows1765]
  all_goals rfl

theorem atot1758 : totK PD2M8K2 D2M8K2.u1758 = [0, 0, 391198601304, 965728136896, 448874615618, 22494391888, 0, 0] := by
  rw [show D2M8K2.u1758 = KTree.node D2M8K2.t1764 (nat_lit 3449101) (nat_lit 1391311165) (nat_lit 0) D2M8K2.t1765 from rfl, totK_node, tot1764, tot1765]
  decide +kernel

theorem arows1759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1759 = true := by
  rw [show D2M8K2.u1759 = KTree.node D2M8K2.t1766 (nat_lit 3450701) (nat_lit 2188079480) (nat_lit 0) D2M8K2.t1767 from rfl, allE_node, rows1766, irow1759, rows1767]
  all_goals rfl

theorem atot1759 : totK PD2M8K2 D2M8K2.u1759 = [0, 0, 187639357274, 774873129715, 711791530731, 102328864502, 1129969115, 0] := by
  rw [show D2M8K2.u1759 = KTree.node D2M8K2.t1766 (nat_lit 3450701) (nat_lit 2188079480) (nat_lit 0) D2M8K2.t1767 from rfl, totK_node, tot1766, tot1767]
  decide +kernel

theorem arows1762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1762 = true := by
  rw [show D2M8K2.u1762 = KTree.node D2M8K2.t1768 (nat_lit 3452787) (nat_lit 1037266669) (nat_lit 0) D2M8K2.t1769 from rfl, allE_node, rows1768, irow1762, rows1769]
  all_goals rfl

theorem atot1762 : totK PD2M8K2 D2M8K2.u1762 = [0, 0, 261051720150, 805935677013, 613497404611, 103719041468, 4008488258, 0] := by
  rw [show D2M8K2.u1762 = KTree.node D2M8K2.t1768 (nat_lit 3452787) (nat_lit 1037266669) (nat_lit 0) D2M8K2.t1769 from rfl, totK_node, tot1768, tot1769]
  decide +kernel

theorem arows1763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1763 = true := by
  rw [show D2M8K2.u1763 = KTree.node D2M8K2.t1770 (nat_lit 3454375) (nat_lit 2345131491) (nat_lit 0) D2M8K2.t1771 from rfl, allE_node, rows1770, irow1763, rows1771]
  all_goals rfl

theorem atot1763 : totK PD2M8K2 D2M8K2.u1763 = [0, 0, 145802131707, 692011658735, 761983593686, 166519317540, 5193381917, 0] := by
  rw [show D2M8K2.u1763 = KTree.node D2M8K2.t1770 (nat_lit 3454375) (nat_lit 2345131491) (nat_lit 0) D2M8K2.t1771 from rfl, totK_node, tot1770, tot1771]
  decide +kernel

theorem arows1765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1765 = true := by
  rw [show D2M8K2.u1765 = KTree.node D2M8K2.t1772 (nat_lit 3459921) (nat_lit 958035990) (nat_lit 0) D2M8K2.t1773 from rfl, allE_node, rows1772, irow1765, rows1773]
  all_goals rfl

theorem atot1765 : totK PD2M8K2 D2M8K2.u1765 = [0, 0, 346299867948, 904387715741, 531908820897, 42208342744, 0, 0] := by
  rw [show D2M8K2.u1765 = KTree.node D2M8K2.t1772 (nat_lit 3459921) (nat_lit 958035990) (nat_lit 0) D2M8K2.t1773 from rfl, totK_node, tot1772, tot1773]
  decide +kernel

theorem arows1766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1766 = true := by
  rw [show D2M8K2.u1766 = KTree.node D2M8K2.t1774 (nat_lit 3461344) (nat_lit 2561407382) (nat_lit 0) D2M8K2.t1775 from rfl, allE_node, rows1774, irow1766, rows1775]
  all_goals rfl

theorem atot1766 : totK PD2M8K2 D2M8K2.u1766 = [0, 0, 93773531552, 650762171223, 858291856746, 180538437282, 4882834716, 0] := by
  rw [show D2M8K2.u1766 = KTree.node D2M8K2.t1774 (nat_lit 3461344) (nat_lit 2561407382) (nat_lit 0) D2M8K2.t1775 from rfl, totK_node, tot1774, tot1775]
  decide +kernel

theorem arows1770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1770 = true := by
  rw [show D2M8K2.u1770 = KTree.node D2M8K2.t1776 (nat_lit 3981465) (nat_lit 1739913691) (nat_lit 0) D2M8K2.t1777 from rfl, allE_node, rows1776, irow1770, rows1777]
  all_goals rfl

theorem atot1770 : totK PD2M8K2 D2M8K2.u1770 = [0, 263331878405, 634767790338, 362701242815, 327564815577, 183073852309, 17014456371, 0] := by
  rw [show D2M8K2.u1770 = KTree.node D2M8K2.t1776 (nat_lit 3981465) (nat_lit 1739913691) (nat_lit 0) D2M8K2.t1777 from rfl, totK_node, tot1776, tot1777]
  decide +kernel

theorem arows1771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1771 = true := by
  rw [show D2M8K2.u1771 = KTree.node D2M8K2.t1778 (nat_lit 3982988) (nat_lit 1439703700) (nat_lit 0) D2M8K2.t1779 from rfl, allE_node, rows1778, irow1771, rows1779]
  all_goals rfl

theorem atot1771 : totK PD2M8K2 D2M8K2.u1771 = [0, 174002787257, 739626752769, 757186286595, 128930329777, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1771 = KTree.node D2M8K2.t1778 (nat_lit 3982988) (nat_lit 1439703700) (nat_lit 0) D2M8K2.t1779 from rfl, totK_node, tot1778, tot1779]
  decide +kernel

theorem arows1773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1773 = true := by
  rw [show D2M8K2.u1773 = KTree.node D2M8K2.t1780 (nat_lit 3988554) (nat_lit 2590696279) (nat_lit 0) D2M8K2.t1781 from rfl, allE_node, rows1780, irow1773, rows1781]
  all_goals rfl

theorem atot1773 : totK PD2M8K2 D2M8K2.u1773 = [0, 287103305293, 862896107917, 615312291832, 64201263185, 0, 0, 0] := by
  rw [show D2M8K2.u1773 = KTree.node D2M8K2.t1780 (nat_lit 3988554) (nat_lit 2590696279) (nat_lit 0) D2M8K2.t1781 from rfl, totK_node, tot1780, tot1781]
  decide +kernel

theorem arows1774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1774 = true := by
  rw [show D2M8K2.u1774 = KTree.node D2M8K2.t1782 (nat_lit 3990034) (nat_lit 3717041424) (nat_lit 0) D2M8K2.t1783 from rfl, allE_node, rows1782, irow1774, rows1783]
  all_goals rfl

theorem atot1774 : totK PD2M8K2 D2M8K2.u1774 = [0, 138364426017, 646971735671, 784262903522, 207632042016, 9587713104, 0, 0] := by
  rw [show D2M8K2.u1774 = KTree.node D2M8K2.t1782 (nat_lit 3990034) (nat_lit 3717041424) (nat_lit 0) D2M8K2.t1783 from rfl, totK_node, tot1782, tot1783]
  decide +kernel

theorem arows1777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1777 = true := by
  rw [show D2M8K2.u1777 = KTree.node D2M8K2.t1784 (nat_lit 3991837) (nat_lit 1369549770) (nat_lit 0) D2M8K2.t1785 from rfl, allE_node, rows1784, irow1777, rows1785]
  all_goals rfl

theorem atot1777 : totK PD2M8K2 D2M8K2.u1777 = [0, 257948127225, 801986726876, 604537129259, 109994936516, 3462014130, 0, 0] := by
  rw [show D2M8K2.u1777 = KTree.node D2M8K2.t1784 (nat_lit 3991837) (nat_lit 1369549770) (nat_lit 0) D2M8K2.t1785 from rfl, totK_node, tot1784, tot1785]
  decide +kernel

theorem arows1778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1778 = true := by
  rw [show D2M8K2.u1778 = KTree.node D2M8K2.t1786 (nat_lit 3994290) (nat_lit 3439854659) (nat_lit 0) D2M8K2.t1787 from rfl, allE_node, rows1786, irow1778, rows1787]
  all_goals rfl

theorem atot1778 : totK PD2M8K2 D2M8K2.u1778 = [0, 84245716041, 536473381763, 852411053346, 265180781001, 13250685261, 0, 0] := by
  rw [show D2M8K2.u1778 = KTree.node D2M8K2.t1786 (nat_lit 3994290) (nat_lit 3439854659) (nat_lit 0) D2M8K2.t1787 from rfl, totK_node, tot1786, tot1787]
  decide +kernel

theorem arows1780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1780 = true := by
  rw [show D2M8K2.u1780 = KTree.node D2M8K2.t1788 (nat_lit 3995722) (nat_lit 3571253817) (nat_lit 0) D2M8K2.t1789 from rfl, allE_node, rows1788, irow1780, rows1789]
  all_goals rfl

theorem atot1780 : totK PD2M8K2 D2M8K2.u1780 = [0, 354420908436, 890014850871, 495277480783, 47420104686, 0, 0, 0] := by
  rw [show D2M8K2.u1780 = KTree.node D2M8K2.t1788 (nat_lit 3995722) (nat_lit 3571253817) (nat_lit 0) D2M8K2.t1789 from rfl, totK_node, tot1788, tot1789]
  decide +kernel

theorem arows1781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1781 = true := by
  rw [show D2M8K2.u1781 = KTree.node D2M8K2.t1790 (nat_lit 3997445) (nat_lit 2331823436) (nat_lit 0) D2M8K2.t1791 from rfl, allE_node, rows1790, irow1781, rows1791]
  all_goals rfl

theorem atot1781 : totK PD2M8K2 D2M8K2.u1781 = [0, 77505186634, 613371922907, 880645004841, 200020394712, 4980514959, 0, 0] := by
  rw [show D2M8K2.u1781 = KTree.node D2M8K2.t1790 (nat_lit 3997445) (nat_lit 2331823436) (nat_lit 0) D2M8K2.t1791 from rfl, totK_node, tot1790, tot1791]
  decide +kernel

theorem arows1789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1789 = true := by
  rw [show D2M8K2.u1789 = KTree.node D2M8K2.t1792 (nat_lit 3999273) (nat_lit 1837267740) (nat_lit 0) D2M8K2.t1793 from rfl, allE_node, rows1792, irow1789, rows1793]
  all_goals rfl

theorem atot1789 : totK PD2M8K2 D2M8K2.u1789 = [0, 392661349882, 926551582781, 455857285099, 36657228110, 0, 0, 0] := by
  rw [show D2M8K2.u1789 = KTree.node D2M8K2.t1792 (nat_lit 3999273) (nat_lit 1837267740) (nat_lit 0) D2M8K2.t1793 from rfl, totK_node, tot1792, tot1793]
  decide +kernel

theorem arows1790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1790 = true := by
  rw [show D2M8K2.u1790 = KTree.node D2M8K2.t1794 (nat_lit 4000936) (nat_lit 3857151937) (nat_lit 0) D2M8K2.t1795 from rfl, allE_node, rows1794, irow1790, rows1795]
  all_goals rfl

theorem atot1790 : totK PD2M8K2 D2M8K2.u1790 = [0, 0, 495167949941, 970914736191, 295532602606, 8710740030, 0, 0] := by
  rw [show D2M8K2.u1790 = KTree.node D2M8K2.t1794 (nat_lit 4000936) (nat_lit 3857151937) (nat_lit 0) D2M8K2.t1795 from rfl, totK_node, tot1794, tot1795]
  decide +kernel

theorem arows1792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1792 = true := by
  rw [show D2M8K2.u1792 = KTree.node D2M8K2.t1796 (nat_lit 4002758) (nat_lit 3588384069) (nat_lit 0) D2M8K2.t1797 from rfl, allE_node, rows1796, irow1792, rows1797]
  all_goals rfl

theorem atot1792 : totK PD2M8K2 D2M8K2.u1792 = [0, 0, 367887895776, 934774714201, 442207030224, 31340853708, 0, 0] := by
  rw [show D2M8K2.u1792 = KTree.node D2M8K2.t1796 (nat_lit 4002758) (nat_lit 3588384069) (nat_lit 0) D2M8K2.t1797 from rfl, totK_node, tot1796, tot1797]
  decide +kernel

theorem arows1793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1793 = true := by
  rw [show D2M8K2.u1793 = KTree.node D2M8K2.t1798 (nat_lit 4003972) (nat_lit 3712782091) (nat_lit 0) D2M8K2.t1799 from rfl, allE_node, rows1798, irow1793, rows1799]
  all_goals rfl

theorem atot1793 : totK PD2M8K2 D2M8K2.u1793 = [0, 0, 87476419814, 696854067458, 801548333037, 138447416182, 1369150432, 0] := by
  rw [show D2M8K2.u1793 = KTree.node D2M8K2.t1798 (nat_lit 4003972) (nat_lit 3712782091) (nat_lit 0) D2M8K2.t1799 from rfl, totK_node, tot1798, tot1799]
  decide +kernel

theorem arows1796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1796 = true := by
  rw [show D2M8K2.u1796 = KTree.node D2M8K2.t1800 (nat_lit 4009586) (nat_lit 4030184258) (nat_lit 0) D2M8K2.t1801 from rfl, allE_node, rows1800, irow1796, rows1801]
  all_goals rfl

theorem atot1796 : totK PD2M8K2 D2M8K2.u1796 = [0, 0, 390918880548, 950622091216, 425330485716, 24661452041, 0, 0] := by
  rw [show D2M8K2.u1796 = KTree.node D2M8K2.t1800 (nat_lit 4009586) (nat_lit 4030184258) (nat_lit 0) D2M8K2.t1801 from rfl, totK_node, tot1800, tot1801]
  decide +kernel

theorem arows1797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1797 = true := by
  rw [show D2M8K2.u1797 = KTree.node D2M8K2.t1802 (nat_lit 4013412) (nat_lit 3234241245) (nat_lit 0) D2M8K2.t1803 from rfl, allE_node, rows1802, irow1797, rows1803]
  all_goals rfl

theorem atot1797 : totK PD2M8K2 D2M8K2.u1797 = [0, 0, 374840680209, 945916731821, 430995273536, 23706097634, 0, 0] := by
  rw [show D2M8K2.u1797 = KTree.node D2M8K2.t1802 (nat_lit 4013412) (nat_lit 3234241245) (nat_lit 0) D2M8K2.t1803 from rfl, totK_node, tot1802, tot1803]
  decide +kernel

theorem arows1799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1799 = true := by
  rw [show D2M8K2.u1799 = KTree.node D2M8K2.t1804 (nat_lit 4016479) (nat_lit 1482082196) (nat_lit 0) D2M8K2.t1805 from rfl, allE_node, rows1804, irow1799, rows1805]
  all_goals rfl

theorem atot1799 : totK PD2M8K2 D2M8K2.u1799 = [0, 0, 368912331349, 926543748429, 434090435991, 27234412507, 0, 0] := by
  rw [show D2M8K2.u1799 = KTree.node D2M8K2.t1804 (nat_lit 4016479) (nat_lit 1482082196) (nat_lit 0) D2M8K2.t1805 from rfl, totK_node, tot1804, tot1805]
  decide +kernel

theorem arows1800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1800 = true := by
  rw [show D2M8K2.u1800 = KTree.node D2M8K2.t1806 (nat_lit 4019788) (nat_lit 3760060854) (nat_lit 0) D2M8K2.t1807 from rfl, allE_node, rows1806, irow1800, rows1807]
  all_goals rfl

theorem atot1800 : totK PD2M8K2 D2M8K2.u1800 = [0, 0, 362001906024, 964349595881, 440178109489, 17476056642, 0, 0] := by
  rw [show D2M8K2.u1800 = KTree.node D2M8K2.t1806 (nat_lit 4019788) (nat_lit 3760060854) (nat_lit 0) D2M8K2.t1807 from rfl, totK_node, tot1806, tot1807]
  decide +kernel

theorem arows1804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1804 = true := by
  rw [show D2M8K2.u1804 = KTree.node D2M8K2.t1808 (nat_lit 4026756) (nat_lit 988524660) (nat_lit 0) D2M8K2.t1809 from rfl, allE_node, rows1808, irow1804, rows1809]
  all_goals rfl

theorem atot1804 : totK PD2M8K2 D2M8K2.u1804 = [0, 256340423562, 744493472820, 639082833048, 187739587224, 13468148062, 0, 0] := by
  rw [show D2M8K2.u1804 = KTree.node D2M8K2.t1808 (nat_lit 4026756) (nat_lit 988524660) (nat_lit 0) D2M8K2.t1809 from rfl, totK_node, tot1808, tot1809]
  decide +kernel

theorem arows1805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1805 = true := by
  rw [show D2M8K2.u1805 = KTree.node D2M8K2.t1810 (nat_lit 4028289) (nat_lit 1811934193) (nat_lit 0) D2M8K2.t1811 from rfl, allE_node, rows1810, irow1805, rows1811]
  all_goals rfl

theorem atot1805 : totK PD2M8K2 D2M8K2.u1805 = [0, 174066083134, 636540728558, 700273688953, 279867510875, 25373788367, 0, 0] := by
  rw [show D2M8K2.u1805 = KTree.node D2M8K2.t1810 (nat_lit 4028289) (nat_lit 1811934193) (nat_lit 0) D2M8K2.t1811 from rfl, totK_node, tot1810, tot1811]
  decide +kernel

theorem arows1807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1807 = true := by
  rw [show D2M8K2.u1807 = KTree.node D2M8K2.t1812 (nat_lit 4029487) (nat_lit 2409944126) (nat_lit 0) D2M8K2.t1813 from rfl, allE_node, rows1812, irow1807, rows1813]
  all_goals rfl

theorem atot1807 : totK PD2M8K2 D2M8K2.u1807 = [0, 161348482468, 587841770161, 747469777716, 300941731776, 12235609738, 0, 0] := by
  rw [show D2M8K2.u1807 = KTree.node D2M8K2.t1812 (nat_lit 4029487) (nat_lit 2409944126) (nat_lit 0) D2M8K2.t1813 from rfl, totK_node, tot1812, tot1813]
  decide +kernel

theorem arows1808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1808 = true := by
  rw [show D2M8K2.u1808 = KTree.node D2M8K2.t1814 (nat_lit 4031003) (nat_lit 1002275516) (nat_lit 0) D2M8K2.t1815 from rfl, allE_node, rows1814, irow1808, rows1815]
  all_goals rfl

theorem atot1808 : totK PD2M8K2 D2M8K2.u1808 = [0, 264676472860, 815273324389, 622843327507, 88235471955, 1163840124, 0, 0] := by
  rw [show D2M8K2.u1808 = KTree.node D2M8K2.t1814 (nat_lit 4031003) (nat_lit 1002275516) (nat_lit 0) D2M8K2.t1815 from rfl, totK_node, tot1814, tot1815]
  decide +kernel

theorem arows1811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1811 = true := by
  rw [show D2M8K2.u1811 = KTree.node D2M8K2.t1816 (nat_lit 4032678) (nat_lit 3517145103) (nat_lit 0) D2M8K2.t1817 from rfl, allE_node, rows1816, irow1811, rows1817]
  all_goals rfl

theorem atot1811 : totK PD2M8K2 D2M8K2.u1811 = [0, 124262331957, 607216259954, 812396651977, 235836057644, 11873025674, 0, 0] := by
  rw [show D2M8K2.u1811 = KTree.node D2M8K2.t1816 (nat_lit 4032678) (nat_lit 3517145103) (nat_lit 0) D2M8K2.t1817 from rfl, totK_node, tot1816, tot1817]
  decide +kernel

theorem arows1812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1812 = true := by
  rw [show D2M8K2.u1812 = KTree.node D2M8K2.t1818 (nat_lit 4037566) (nat_lit 3219891645) (nat_lit 0) D2M8K2.t1819 from rfl, allE_node, rows1818, irow1812, rows1819]
  all_goals rfl

theorem atot1812 : totK PD2M8K2 D2M8K2.u1812 = [0, 275939937419, 831829389379, 598191200417, 84787262667, 1096156699, 0, 0] := by
  rw [show D2M8K2.u1812 = KTree.node D2M8K2.t1818 (nat_lit 4037566) (nat_lit 3219891645) (nat_lit 0) D2M8K2.t1819 from rfl, totK_node, tot1818, tot1819]
  decide +kernel

theorem arows1814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1814 = true := by
  rw [show D2M8K2.u1814 = KTree.node D2M8K2.t1820 (nat_lit 4039593) (nat_lit 1920798711) (nat_lit 0) D2M8K2.t1821 from rfl, allE_node, rows1820, irow1814, rows1821]
  all_goals rfl

theorem atot1814 : totK PD2M8K2 D2M8K2.u1814 = [0, 157483264256, 703235038042, 791501631455, 170347434999, 3880716147, 0, 0] := by
  rw [show D2M8K2.u1814 = KTree.node D2M8K2.t1820 (nat_lit 4039593) (nat_lit 1920798711) (nat_lit 0) D2M8K2.t1821 from rfl, totK_node, tot1820, tot1821]
  decide +kernel

theorem arows1815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1815 = true := by
  rw [show D2M8K2.u1815 = KTree.node D2M8K2.t1822 (nat_lit 4041524) (nat_lit 1826854561) (nat_lit 0) D2M8K2.t1823 from rfl, allE_node, rows1822, irow1815, rows1823]
  all_goals rfl

theorem atot1815 : totK PD2M8K2 D2M8K2.u1815 = [0, 248437234595, 791038302810, 655759594348, 111536725062, 1267860612, 0, 0] := by
  rw [show D2M8K2.u1815 = KTree.node D2M8K2.t1822 (nat_lit 4041524) (nat_lit 1826854561) (nat_lit 0) D2M8K2.t1823 from rfl, totK_node, tot1822, tot1823]
  decide +kernel

theorem arows1820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1820 = true := by
  rw [show D2M8K2.u1820 = KTree.node D2M8K2.t1824 (nat_lit 4043278) (nat_lit 4009919491) (nat_lit 0) D2M8K2.t1825 from rfl, allE_node, rows1824, irow1820, rows1825]
  all_goals rfl

theorem atot1820 : totK PD2M8K2 D2M8K2.u1820 = [0, 0, 388747886278, 920121516537, 461827282899, 39031300949, 0, 0] := by
  rw [show D2M8K2.u1820 = KTree.node D2M8K2.t1824 (nat_lit 4043278) (nat_lit 4009919491) (nat_lit 0) D2M8K2.t1825 from rfl, totK_node, tot1824, tot1825]
  decide +kernel

theorem arows1821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1821 = true := by
  rw [show D2M8K2.u1821 = KTree.node D2M8K2.t1826 (nat_lit 4048203) (nat_lit 3652811235) (nat_lit 0) D2M8K2.t1827 from rfl, allE_node, rows1826, irow1821, rows1827]
  all_goals rfl

theorem atot1821 : totK PD2M8K2 D2M8K2.u1821 = [0, 0, 392396870740, 969028117548, 434535901450, 23193112439, 0, 0] := by
  rw [show D2M8K2.u1821 = KTree.node D2M8K2.t1826 (nat_lit 4048203) (nat_lit 3652811235) (nat_lit 0) D2M8K2.t1827 from rfl, totK_node, tot1826, tot1827]
  decide +kernel

theorem arows1823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1823 = true := by
  rw [show D2M8K2.u1823 = KTree.node D2M8K2.t1828 (nat_lit 4051200) (nat_lit 3401275093) (nat_lit 0) D2M8K2.t1829 from rfl, allE_node, rows1828, irow1823, rows1829]
  all_goals rfl

theorem atot1823 : totK PD2M8K2 D2M8K2.u1823 = [0, 0, 353750871746, 934124193667, 490719631131, 32802719617, 0, 0] := by
  rw [show D2M8K2.u1823 = KTree.node D2M8K2.t1828 (nat_lit 4051200) (nat_lit 3401275093) (nat_lit 0) D2M8K2.t1829 from rfl, totK_node, tot1828, tot1829]
  decide +kernel

theorem arows1824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1824 = true := by
  rw [show D2M8K2.u1824 = KTree.node D2M8K2.t1830 (nat_lit 4053334) (nat_lit 1356990985) (nat_lit 0) D2M8K2.t1831 from rfl, allE_node, rows1830, irow1824, rows1831]
  all_goals rfl

theorem atot1824 : totK PD2M8K2 D2M8K2.u1824 = [0, 0, 96716684966, 642590058315, 838770625783, 190216244544, 5159868635, 0] := by
  rw [show D2M8K2.u1824 = KTree.node D2M8K2.t1830 (nat_lit 4053334) (nat_lit 1356990985) (nat_lit 0) D2M8K2.t1831 from rfl, totK_node, tot1830, tot1831]
  decide +kernel

theorem arows1827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1827 = true := by
  rw [show D2M8K2.u1827 = KTree.node D2M8K2.t1832 (nat_lit 4058287) (nat_lit 2447609201) (nat_lit 0) D2M8K2.t1833 from rfl, allE_node, rows1832, irow1827, rows1833]
  all_goals rfl

theorem atot1827 : totK PD2M8K2 D2M8K2.u1827 = [0, 0, 302507265065, 912350857229, 546813035439, 37746320082, 0, 0] := by
  rw [show D2M8K2.u1827 = KTree.node D2M8K2.t1832 (nat_lit 4058287) (nat_lit 2447609201) (nat_lit 0) D2M8K2.t1833 from rfl, totK_node, tot1832, tot1833]
  decide +kernel

theorem arows1828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1828 = true := by
  rw [show D2M8K2.u1828 = KTree.node D2M8K2.t1834 (nat_lit 4060857) (nat_lit 1552291369) (nat_lit 0) D2M8K2.t1835 from rfl, allE_node, rows1834, irow1828, rows1835]
  all_goals rfl

theorem atot1828 : totK PD2M8K2 D2M8K2.u1828 = [0, 0, 225046037020, 782160018658, 691659737633, 106177230070, 1415142070, 0] := by
  rw [show D2M8K2.u1828 = KTree.node D2M8K2.t1834 (nat_lit 4060857) (nat_lit 1552291369) (nat_lit 0) D2M8K2.t1835 from rfl, totK_node, tot1834, tot1835]
  decide +kernel

theorem arows1830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1830 = true := by
  rw [show D2M8K2.u1830 = KTree.node D2M8K2.t1836 (nat_lit 4062419) (nat_lit 2892753708) (nat_lit 0) D2M8K2.t1837 from rfl, allE_node, rows1836, irow1830, rows1837]
  all_goals rfl

theorem atot1830 : totK PD2M8K2 D2M8K2.u1830 = [0, 179396403326, 600636386549, 698921763655, 321230199655, 23165234854, 0, 0] := by
  rw [show D2M8K2.u1830 = KTree.node D2M8K2.t1836 (nat_lit 4062419) (nat_lit 2892753708) (nat_lit 0) D2M8K2.t1837 from rfl, totK_node, tot1836, tot1837]
  decide +kernel

theorem arows1831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1831 = true := by
  rw [show D2M8K2.u1831 = KTree.node D2M8K2.t1838 (nat_lit 4065724) (nat_lit 3811568550) (nat_lit 0) D2M8K2.t1839 from rfl, allE_node, rows1838, irow1831, rows1839]
  all_goals rfl

theorem atot1831 : totK PD2M8K2 D2M8K2.u1831 = [0, 238307877090, 778225264094, 644757179771, 111321297627, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1831 = KTree.node D2M8K2.t1838 (nat_lit 4065724) (nat_lit 3811568550) (nat_lit 0) D2M8K2.t1839 from rfl, totK_node, tot1838, tot1839]
  decide +kernel

theorem arows1835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1835 = true := by
  rw [show D2M8K2.u1835 = KTree.node D2M8K2.t1840 (nat_lit 4068078) (nat_lit 3491593698) (nat_lit 0) D2M8K2.t1841 from rfl, allE_node, rows1840, irow1835, rows1841]
  all_goals rfl

theorem atot1835 : totK PD2M8K2 D2M8K2.u1835 = [0, 213410013759, 787044457573, 743113195616, 90720803371, 0, 0, 0] := by
  rw [show D2M8K2.u1835 = KTree.node D2M8K2.t1840 (nat_lit 4068078) (nat_lit 3491593698) (nat_lit 0) D2M8K2.t1841 from rfl, totK_node, tot1840, tot1841]
  decide +kernel

theorem arows1836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1836 = true := by
  rw [show D2M8K2.u1836 = KTree.node D2M8K2.t1842 (nat_lit 4069331) (nat_lit 2889790332) (nat_lit 0) D2M8K2.t1843 from rfl, allE_node, rows1842, irow1836, rows1843]
  all_goals rfl

theorem atot1836 : totK PD2M8K2 D2M8K2.u1836 = [0, 189253081574, 719652514690, 662386629136, 206692113564, 19153527009, 0, 0] := by
  rw [show D2M8K2.u1836 = KTree.node D2M8K2.t1842 (nat_lit 4069331) (nat_lit 2889790332) (nat_lit 0) D2M8K2.t1843 from rfl, totK_node, tot1842, tot1843]
  decide +kernel

theorem arows1838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1838 = true := by
  rw [show D2M8K2.u1838 = KTree.node D2M8K2.t1844 (nat_lit 4070926) (nat_lit 4014680920) (nat_lit 0) D2M8K2.t1845 from rfl, allE_node, rows1844, irow1838, rows1845]
  all_goals rfl

theorem atot1838 : totK PD2M8K2 D2M8K2.u1838 = [0, 157317981048, 537877289354, 748880023855, 327358312078, 11898455402, 0, 0] := by
  rw [show D2M8K2.u1838 = KTree.node D2M8K2.t1844 (nat_lit 4070926) (nat_lit 4014680920) (nat_lit 0) D2M8K2.t1845 from rfl, totK_node, tot1844, tot1845]
  decide +kernel

theorem arows1839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1839 = true := by
  rw [show D2M8K2.u1839 = KTree.node D2M8K2.t1846 (nat_lit 4072382) (nat_lit 3853134236) (nat_lit 0) D2M8K2.t1847 from rfl, allE_node, rows1846, irow1839, rows1847]
  all_goals rfl

theorem atot1839 : totK PD2M8K2 D2M8K2.u1839 = [0, 288585840939, 892701686257, 595498270451, 55272474675, 0, 0, 0] := by
  rw [show D2M8K2.u1839 = KTree.node D2M8K2.t1846 (nat_lit 4072382) (nat_lit 3853134236) (nat_lit 0) D2M8K2.t1847 from rfl, totK_node, tot1846, tot1847]
  decide +kernel

theorem arows1842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1842 = true := by
  rw [show D2M8K2.u1842 = KTree.node D2M8K2.t1848 (nat_lit 4074056) (nat_lit 3687852363) (nat_lit 0) D2M8K2.t1849 from rfl, allE_node, rows1848, irow1842, rows1849]
  all_goals rfl

theorem atot1842 : totK PD2M8K2 D2M8K2.u1842 = [0, 84415941621, 522118873493, 887377849841, 284902634154, 13049727234, 0, 0] := by
  rw [show D2M8K2.u1842 = KTree.node D2M8K2.t1848 (nat_lit 4074056) (nat_lit 3687852363) (nat_lit 0) D2M8K2.t1849 from rfl, totK_node, tot1848, tot1849]
  decide +kernel

theorem arows1843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1843 = true := by
  rw [show D2M8K2.u1843 = KTree.node D2M8K2.t1850 (nat_lit 4078834) (nat_lit 3704410632) (nat_lit 0) D2M8K2.t1851 from rfl, allE_node, rows1850, irow1843, rows1851]
  all_goals rfl

theorem atot1843 : totK PD2M8K2 D2M8K2.u1843 = [0, 331720656942, 909291978885, 505623826939, 40400906495, 0, 0, 0] := by
  rw [show D2M8K2.u1843 = KTree.node D2M8K2.t1850 (nat_lit 4078834) (nat_lit 3704410632) (nat_lit 0) D2M8K2.t1851 from rfl, totK_node, tot1850, tot1851]
  decide +kernel

theorem arows1845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1845 = true := by
  rw [show D2M8K2.u1845 = KTree.node D2M8K2.t1852 (nat_lit 4080705) (nat_lit 1825578435) (nat_lit 0) D2M8K2.t1853 from rfl, allE_node, rows1852, irow1845, rows1853]
  all_goals rfl

theorem atot1845 : totK PD2M8K2 D2M8K2.u1845 = [0, 85045554163, 612439406632, 868735993896, 202996501451, 4980514959, 0, 0] := by
  rw [show D2M8K2.u1845 = KTree.node D2M8K2.t1852 (nat_lit 4080705) (nat_lit 1825578435) (nat_lit 0) D2M8K2.t1853 from rfl, totK_node, tot1852, tot1853]
  decide +kernel

theorem arows1846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1846 = true := by
  rw [show D2M8K2.u1846 = KTree.node D2M8K2.t1854 (nat_lit 4082364) (nat_lit 2707517519) (nat_lit 0) D2M8K2.t1855 from rfl, allE_node, rows1854, irow1846, rows1855]
  all_goals rfl

theorem atot1846 : totK PD2M8K2 D2M8K2.u1846 = [0, 335781306644, 897675020723, 543301802448, 48752239658, 0, 0, 0] := by
  rw [show D2M8K2.u1846 = KTree.node D2M8K2.t1854 (nat_lit 4082364) (nat_lit 2707517519) (nat_lit 0) D2M8K2.t1855 from rfl, totK_node, tot1854, tot1855]
  decide +kernel

theorem arows1852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1852 = true := by
  rw [show D2M8K2.u1852 = KTree.node D2M8K2.t1856 (nat_lit 4084035) (nat_lit 2387195009) (nat_lit 0) D2M8K2.t1857 from rfl, allE_node, rows1856, irow1852, rows1857]
  all_goals rfl

theorem atot1852 : totK PD2M8K2 D2M8K2.u1852 = [0, 0, 415264582194, 957043178801, 375833262510, 17549628343, 0, 0] := by
  rw [show D2M8K2.u1852 = KTree.node D2M8K2.t1856 (nat_lit 4084035) (nat_lit 2387195009) (nat_lit 0) D2M8K2.t1857 from rfl, totK_node, tot1856, tot1857]
  decide +kernel

theorem arows1853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1853 = true := by
  rw [show D2M8K2.u1853 = KTree.node D2M8K2.t1858 (nat_lit 4085954) (nat_lit 2737036683) (nat_lit 0) D2M8K2.t1859 from rfl, allE_node, rows1858, irow1853, rows1859]
  all_goals rfl

theorem atot1853 : totK PD2M8K2 D2M8K2.u1853 = [0, 0, 396580121276, 970662023608, 384644313535, 16080396318, 0, 0] := by
  rw [show D2M8K2.u1853 = KTree.node D2M8K2.t1858 (nat_lit 4085954) (nat_lit 2737036683) (nat_lit 0) D2M8K2.t1859 from rfl, totK_node, tot1858, tot1859]
  decide +kernel

theorem arows1855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1855 = true := by
  rw [show D2M8K2.u1855 = KTree.node D2M8K2.t1860 (nat_lit 4087715) (nat_lit 2914770304) (nat_lit 0) D2M8K2.t1861 from rfl, allE_node, rows1860, irow1855, rows1861]
  all_goals rfl

theorem atot1855 : totK PD2M8K2 D2M8K2.u1855 = [0, 0, 95587989266, 706064238864, 834920470684, 119598453266, 1206465782, 0] := by
  rw [show D2M8K2.u1855 = KTree.node D2M8K2.t1860 (nat_lit 4087715) (nat_lit 2914770304) (nat_lit 0) D2M8K2.t1861 from rfl, totK_node, tot1860, tot1861]
  decide +kernel

theorem arows1856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1856 = true := by
  rw [show D2M8K2.u1856 = KTree.node D2M8K2.t1862 (nat_lit 4089714) (nat_lit 3320524463) (nat_lit 0) D2M8K2.t1863 from rfl, allE_node, rows1862, irow1856, rows1863]
  all_goals rfl

theorem atot1856 : totK PD2M8K2 D2M8K2.u1856 = [0, 0, 395589069363, 963581285713, 412964878077, 21526878430, 0, 0] := by
  rw [show D2M8K2.u1856 = KTree.node D2M8K2.t1862 (nat_lit 4089714) (nat_lit 3320524463) (nat_lit 0) D2M8K2.t1863 from rfl, totK_node, tot1862, tot1863]
  decide +kernel

theorem arows1859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1859 = true := by
  rw [show D2M8K2.u1859 = KTree.node D2M8K2.t1864 (nat_lit 4092684) (nat_lit 3036536356) (nat_lit 0) D2M8K2.t1865 from rfl, allE_node, rows1864, irow1859, rows1865]
  all_goals rfl

theorem atot1859 : totK PD2M8K2 D2M8K2.u1859 = [0, 0, 357436156466, 949714283730, 480437717194, 30830301070, 0, 0] := by
  rw [show D2M8K2.u1859 = KTree.node D2M8K2.t1864 (nat_lit 4092684) (nat_lit 3036536356) (nat_lit 0) D2M8K2.t1865 from rfl, totK_node, tot1864, tot1865]
  decide +kernel

theorem arows1860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1860 = true := by
  rw [show D2M8K2.u1860 = KTree.node D2M8K2.t1866 (nat_lit 4094363) (nat_lit 2164695725) (nat_lit 0) D2M8K2.t1867 from rfl, allE_node, rows1866, irow1860, rows1867]
  all_goals rfl

theorem atot1860 : totK PD2M8K2 D2M8K2.u1860 = [0, 0, 51694275795, 510700236522, 879081091383, 276226739243, 13016197374, 0] := by
  rw [show D2M8K2.u1860 = KTree.node D2M8K2.t1866 (nat_lit 4094363) (nat_lit 2164695725) (nat_lit 0) D2M8K2.t1867 from rfl, totK_node, tot1866, tot1867]
  decide +kernel

theorem arows1862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1862 = true := by
  rw [show D2M8K2.u1862 = KTree.node D2M8K2.t1868 (nat_lit 4099515) (nat_lit 3029432540) (nat_lit 0) D2M8K2.t1869 from rfl, allE_node, rows1868, irow1862, rows1869]
  all_goals rfl

theorem atot1862 : totK PD2M8K2 D2M8K2.u1862 = [0, 0, 362092441093, 943562033003, 439119458012, 24200525243, 0, 0] := by
  rw [show D2M8K2.u1862 = KTree.node D2M8K2.t1868 (nat_lit 4099515) (nat_lit 3029432540) (nat_lit 0) D2M8K2.t1869 from rfl, totK_node, tot1868, tot1869]
  decide +kernel

theorem arows1863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1863 = true := by
  rw [show D2M8K2.u1863 = KTree.node D2M8K2.t1870 (nat_lit 4101436) (nat_lit 2362542469) (nat_lit 0) D2M8K2.t1871 from rfl, allE_node, rows1870, irow1863, rows1871]
  all_goals rfl

theorem atot1863 : totK PD2M8K2 D2M8K2.u1863 = [0, 0, 104239363842, 657132723963, 774016678479, 152838964140, 4574395652, 0] := by
  rw [show D2M8K2.u1863 = KTree.node D2M8K2.t1870 (nat_lit 4101436) (nat_lit 2362542469) (nat_lit 0) D2M8K2.t1871 from rfl, totK_node, tot1870, tot1871]
  decide +kernel

theorem arows1867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1867 = true := by
  rw [show D2M8K2.u1867 = KTree.node D2M8K2.t1872 (nat_lit 4103166) (nat_lit 3212629448) (nat_lit 0) D2M8K2.t1873 from rfl, allE_node, rows1872, irow1867, rows1873]
  all_goals rfl

theorem atot1867 : totK PD2M8K2 D2M8K2.u1867 = [0, 68882649377, 405383812361, 851051482728, 456273025557, 32154618771, 0, 0] := by
  rw [show D2M8K2.u1867 = KTree.node D2M8K2.t1872 (nat_lit 4103166) (nat_lit 3212629448) (nat_lit 0) D2M8K2.t1873 from rfl, totK_node, tot1872, tot1873]
  decide +kernel

theorem arows1868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1868 = true := by
  rw [show D2M8K2.u1868 = KTree.node D2M8K2.t1874 (nat_lit 4148212) (nat_lit 2726080906) (nat_lit 0) D2M8K2.t1875 from rfl, allE_node, rows1874, irow1868, rows1875]
  all_goals rfl

theorem atot1868 : totK PD2M8K2 D2M8K2.u1868 = [0, 340720605222, 929376347567, 476894333423, 27369820931, 0, 0, 0] := by
  rw [show D2M8K2.u1868 = KTree.node D2M8K2.t1874 (nat_lit 4148212) (nat_lit 2726080906) (nat_lit 0) D2M8K2.t1875 from rfl, totK_node, tot1874, tot1875]
  decide +kernel

theorem arows1870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1870 = true := by
  rw [show D2M8K2.u1870 = KTree.node D2M8K2.t1876 (nat_lit 4150080) (nat_lit 3716921436) (nat_lit 0) D2M8K2.t1877 from rfl, allE_node, rows1876, irow1870, rows1877]
  all_goals rfl

theorem atot1870 : totK PD2M8K2 D2M8K2.u1870 = [0, 90904776651, 658468161183, 890627973029, 163068780704, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1870 = KTree.node D2M8K2.t1876 (nat_lit 4150080) (nat_lit 3716921436) (nat_lit 0) D2M8K2.t1877 from rfl, totK_node, tot1876, tot1877]
  decide +kernel

theorem arows1871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1871 = true := by
  rw [show D2M8K2.u1871 = KTree.node D2M8K2.t1878 (nat_lit 4151868) (nat_lit 2962760524) (nat_lit 0) D2M8K2.t1879 from rfl, allE_node, rows1878, irow1871, rows1879]
  all_goals rfl

theorem atot1871 : totK PD2M8K2 D2M8K2.u1871 = [0, 295282516528, 847294915011, 568215178115, 92652393247, 10210320223, 0, 0] := by
  rw [show D2M8K2.u1871 = KTree.node D2M8K2.t1878 (nat_lit 4151868) (nat_lit 2962760524) (nat_lit 0) D2M8K2.t1879 from rfl, totK_node, tot1878, tot1879]
  decide +kernel

theorem arows1874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1874 = true := by
  rw [show D2M8K2.u1874 = KTree.node D2M8K2.t1880 (nat_lit 4153508) (nat_lit 3195830551) (nat_lit 0) D2M8K2.t1881 from rfl, allE_node, rows1880, irow1874, rows1881]
  all_goals rfl

theorem atot1874 : totK PD2M8K2 D2M8K2.u1874 = [0, 84808482832, 415601334610, 823357995374, 440431751741, 23278313564, 0, 0] := by
  rw [show D2M8K2.u1874 = KTree.node D2M8K2.t1880 (nat_lit 4153508) (nat_lit 3195830551) (nat_lit 0) D2M8K2.t1881 from rfl, totK_node, tot1880, tot1881]
  decide +kernel

theorem arows1875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1875 = true := by
  rw [show D2M8K2.u1875 = KTree.node D2M8K2.t1882 (nat_lit 4154830) (nat_lit 3951767169) (nat_lit 0) D2M8K2.t1883 from rfl, allE_node, rows1882, irow1875, rows1883]
  all_goals rfl

theorem atot1875 : totK PD2M8K2 D2M8K2.u1875 = [0, 338878106662, 925645687731, 505504859164, 36139498989, 0, 0, 0] := by
  rw [show D2M8K2.u1875 = KTree.node D2M8K2.t1882 (nat_lit 4154830) (nat_lit 3951767169) (nat_lit 0) D2M8K2.t1883 from rfl, totK_node, tot1882, tot1883]
  decide +kernel

theorem arows1877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1877 = true := by
  rw [show D2M8K2.u1877 = KTree.node D2M8K2.t1884 (nat_lit 4156536) (nat_lit 3449845102) (nat_lit 0) D2M8K2.t1885 from rfl, allE_node, rows1884, irow1877, rows1885]
  all_goals rfl

theorem atot1877 : totK PD2M8K2 D2M8K2.u1877 = [0, 29121465226, 481560399893, 950191021320, 297926358050, 13049727234, 0, 0] := by
  rw [show D2M8K2.u1877 = KTree.node D2M8K2.t1884 (nat_lit 4156536) (nat_lit 3449845102) (nat_lit 0) D2M8K2.t1885 from rfl, totK_node, tot1884, tot1885]
  decide +kernel

theorem arows1878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1878 = true := by
  rw [show D2M8K2.u1878 = KTree.node D2M8K2.t1886 (nat_lit 4158588) (nat_lit 3174028253) (nat_lit 0) D2M8K2.t1887 from rfl, allE_node, rows1886, irow1878, rows1887]
  all_goals rfl

theorem atot1878 : totK PD2M8K2 D2M8K2.u1878 = [0, 294521837799, 879332278940, 543837373715, 66496395991, 1198073392, 0, 0] := by
  rw [show D2M8K2.u1878 = KTree.node D2M8K2.t1886 (nat_lit 4158588) (nat_lit 3174028253) (nat_lit 0) D2M8K2.t1887 from rfl, totK_node, tot1886, tot1887]
  decide +kernel

theorem arows1883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1883 = true := by
  rw [show D2M8K2.u1883 = KTree.node D2M8K2.t1888 (nat_lit 4160599) (nat_lit 2213781112) (nat_lit 0) D2M8K2.t1889 from rfl, allE_node, rows1888, irow1883, rows1889]
  all_goals rfl

theorem atot1883 : totK PD2M8K2 D2M8K2.u1883 = [0, 172438341442, 642372100849, 731306629041, 227228804566, 12052611869, 0, 0] := by
  rw [show D2M8K2.u1883 = KTree.node D2M8K2.t1888 (nat_lit 4160599) (nat_lit 2213781112) (nat_lit 0) D2M8K2.t1889 from rfl, totK_node, tot1888, tot1889]
  decide +kernel

theorem arows1884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1884 = true := by
  rw [show D2M8K2.u1884 = KTree.node D2M8K2.t1890 (nat_lit 4162123) (nat_lit 2224470779) (nat_lit 0) D2M8K2.t1891 from rfl, allE_node, rows1890, irow1884, rows1891]
  all_goals rfl

theorem atot1884 : totK PD2M8K2 D2M8K2.u1884 = [0, 263371581614, 810902291965, 626233080333, 88166497138, 1096505104, 0, 0] := by
  rw [show D2M8K2.u1884 = KTree.node D2M8K2.t1890 (nat_lit 4162123) (nat_lit 2224470779) (nat_lit 0) D2M8K2.t1891 from rfl, totK_node, tot1890, tot1891]
  decide +kernel

theorem arows1886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1886 = true := by
  rw [show D2M8K2.u1886 = KTree.node D2M8K2.t1892 (nat_lit 4164021) (nat_lit 1741952189) (nat_lit 0) D2M8K2.t1893 from rfl, allE_node, rows1892, irow1886, rows1893]
  all_goals rfl

theorem atot1886 : totK PD2M8K2 D2M8K2.u1886 = [0, 0, 501943246741, 1009188936769, 283028870535, 6406394852, 0, 0] := by
  rw [show D2M8K2.u1886 = KTree.node D2M8K2.t1892 (nat_lit 4164021) (nat_lit 1741952189) (nat_lit 0) D2M8K2.t1893 from rfl, totK_node, tot1892, tot1893]
  decide +kernel

theorem arows1887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1887 = true := by
  rw [show D2M8K2.u1887 = KTree.node D2M8K2.t1894 (nat_lit 4169341) (nat_lit 1093086583) (nat_lit 0) D2M8K2.t1895 from rfl, allE_node, rows1894, irow1887, rows1895]
  all_goals rfl

theorem atot1887 : totK PD2M8K2 D2M8K2.u1887 = [0, 0, 232539821683, 801445386460, 599533484961, 83306070088, 1138244013, 0] := by
  rw [show D2M8K2.u1887 = KTree.node D2M8K2.t1894 (nat_lit 4169341) (nat_lit 1093086583) (nat_lit 0) D2M8K2.t1895 from rfl, totK_node, tot1894, tot1895]
  decide +kernel

theorem arows1890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1890 = true := by
  rw [show D2M8K2.u1890 = KTree.node D2M8K2.t1896 (nat_lit 4171922) (nat_lit 4106108950) (nat_lit 0) D2M8K2.t1897 from rfl, allE_node, rows1896, irow1890, rows1897]
  all_goals rfl

theorem atot1890 : totK PD2M8K2 D2M8K2.u1890 = [0, 0, 287628315796, 895207392312, 563349648191, 45229172547, 0, 0] := by
  rw [show D2M8K2.u1890 = KTree.node D2M8K2.t1896 (nat_lit 4171922) (nat_lit 4106108950) (nat_lit 0) D2M8K2.t1897 from rfl, totK_node, tot1896, tot1897]
  decide +kernel

theorem arows1891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1891 = true := by
  rw [show D2M8K2.u1891 = KTree.node D2M8K2.t1898 (nat_lit 4175096) (nat_lit 3831553615) (nat_lit 0) D2M8K2.t1899 from rfl, allE_node, rows1898, irow1891, rows1899]
  all_goals rfl

theorem atot1891 : totK PD2M8K2 D2M8K2.u1891 = [0, 0, 356421255099, 957928102155, 450484493024, 23591522765, 0, 0] := by
  rw [show D2M8K2.u1891 = KTree.node D2M8K2.t1898 (nat_lit 4175096) (nat_lit 3831553615) (nat_lit 0) D2M8K2.t1899 from rfl, totK_node, tot1898, tot1899]
  decide +kernel

theorem arows1893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1893 = true := by
  rw [show D2M8K2.u1893 = KTree.node D2M8K2.t1900 (nat_lit 4178387) (nat_lit 2611646827) (nat_lit 0) D2M8K2.t1901 from rfl, allE_node, rows1900, irow1893, rows1901]
  all_goals rfl

theorem atot1893 : totK PD2M8K2 D2M8K2.u1893 = [0, 0, 397355933785, 978170300313, 401216837625, 11495139297, 0, 0] := by
  rw [show D2M8K2.u1893 = KTree.node D2M8K2.t1900 (nat_lit 4178387) (nat_lit 2611646827) (nat_lit 0) D2M8K2.t1901 from rfl, totK_node, tot1900, tot1901]
  decide +kernel

theorem arows1894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1894 = true := by
  rw [show D2M8K2.u1894 = KTree.node D2M8K2.t1902 (nat_lit 4182030) (nat_lit 3179752450) (nat_lit 0) D2M8K2.t1903 from rfl, allE_node, rows1902, irow1894, rows1903]
  all_goals rfl

theorem atot1894 : totK PD2M8K2 D2M8K2.u1894 = [0, 0, 356415637409, 924764735722, 456958015304, 30637541494, 0, 0] := by
  rw [show D2M8K2.u1894 = KTree.node D2M8K2.t1902 (nat_lit 4182030) (nat_lit 3179752450) (nat_lit 0) D2M8K2.t1903 from rfl, totK_node, tot1902, tot1903]
  decide +kernel

theorem arows1898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1898 = true := by
  rw [show D2M8K2.u1898 = KTree.node D2M8K2.t1904 (nat_lit 4183548) (nat_lit 3056986619) (nat_lit 0) D2M8K2.t1905 from rfl, allE_node, rows1904, irow1898, rows1905]
  all_goals rfl

theorem atot1898 : totK PD2M8K2 D2M8K2.u1898 = [0, 0, 164321677495, 781269319079, 694799700503, 100197708000, 1095107716, 0] := by
  rw [show D2M8K2.u1898 = KTree.node D2M8K2.t1904 (nat_lit 4183548) (nat_lit 3056986619) (nat_lit 0) D2M8K2.t1905 from rfl, totK_node, tot1904, tot1905]
  decide +kernel

theorem arows1899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1899 = true := by
  rw [show D2M8K2.u1899 = KTree.node D2M8K2.t1906 (nat_lit 4189309) (nat_lit 1224524169) (nat_lit 0) D2M8K2.t1907 from rfl, allE_node, rows1906, irow1899, rows1907]
  all_goals rfl

theorem atot1899 : totK PD2M8K2 D2M8K2.u1899 = [0, 321916336242, 752802330143, 395148680710, 219717260134, 81166966017, 3882006667, 0] := by
  rw [show D2M8K2.u1899 = KTree.node D2M8K2.t1906 (nat_lit 4189309) (nat_lit 1224524169) (nat_lit 0) D2M8K2.t1907 from rfl, totK_node, tot1906, tot1907]
  decide +kernel

theorem arows1901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1901 = true := by
  rw [show D2M8K2.u1901 = KTree.node D2M8K2.t1908 (nat_lit 4190596) (nat_lit 3828483055) (nat_lit 0) D2M8K2.t1909 from rfl, allE_node, rows1908, irow1901, rows1909]
  all_goals rfl

theorem atot1901 : totK PD2M8K2 D2M8K2.u1901 = [0, 88989031395, 678542505699, 880670785213, 150117087308, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1901 = KTree.node D2M8K2.t1908 (nat_lit 4190596) (nat_lit 3828483055) (nat_lit 0) D2M8K2.t1909 from rfl, totK_node, tot1908, tot1909]
  decide +kernel

theorem arows1902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1902 = true := by
  rw [show D2M8K2.u1902 = KTree.node D2M8K2.t1910 (nat_lit 4192908) (nat_lit 2936342548) (nat_lit 0) D2M8K2.t1911 from rfl, allE_node, rows1910, irow1902, rows1911]
  all_goals rfl

theorem atot1902 : totK PD2M8K2 D2M8K2.u1902 = [0, 388275877044, 913296719631, 489068565261, 45792227044, 0, 0, 0] := by
  rw [show D2M8K2.u1902 = KTree.node D2M8K2.t1910 (nat_lit 4192908) (nat_lit 2936342548) (nat_lit 0) D2M8K2.t1911 from rfl, totK_node, tot1910, tot1911]
  decide +kernel

theorem arows1905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1905 = true := by
  rw [show D2M8K2.u1905 = KTree.node D2M8K2.t1912 (nat_lit 4194535) (nat_lit 854750929) (nat_lit 0) D2M8K2.t1913 from rfl, allE_node, rows1912, irow1905, rows1913]
  all_goals rfl

theorem atot1905 : totK PD2M8K2 D2M8K2.u1905 = [0, 0, 438880368138, 929543325041, 416107685888, 26773181648, 0, 0] := by
  rw [show D2M8K2.u1905 = KTree.node D2M8K2.t1912 (nat_lit 4194535) (nat_lit 854750929) (nat_lit 0) D2M8K2.t1913 from rfl, totK_node, tot1912, tot1913]
  decide +kernel

theorem arows1906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1906 = true := by
  rw [show D2M8K2.u1906 = KTree.node D2M8K2.t1914 (nat_lit 4195981) (nat_lit 849227676) (nat_lit 0) D2M8K2.t1915 from rfl, allE_node, rows1914, irow1906, rows1915]
  all_goals rfl

theorem atot1906 : totK PD2M8K2 D2M8K2.u1906 = [0, 316547616090, 803876591489, 545269238874, 132713920449, 6804944647, 0, 0] := by
  rw [show D2M8K2.u1906 = KTree.node D2M8K2.t1914 (nat_lit 4195981) (nat_lit 849227676) (nat_lit 0) D2M8K2.t1915 from rfl, totK_node, tot1914, tot1915]
  decide +kernel

theorem arows1908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1908 = true := by
  rw [show D2M8K2.u1908 = KTree.node D2M8K2.t1916 (nat_lit 4197460) (nat_lit 3636862074) (nat_lit 0) D2M8K2.t1917 from rfl, allE_node, rows1916, irow1908, rows1917]
  all_goals rfl

theorem atot1908 : totK PD2M8K2 D2M8K2.u1908 = [0, 107956299912, 631213200072, 826902372281, 215156537448, 9583672031, 0, 0] := by
  rw [show D2M8K2.u1908 = KTree.node D2M8K2.t1916 (nat_lit 4197460) (nat_lit 3636862074) (nat_lit 0) D2M8K2.t1917 from rfl, totK_node, tot1916, tot1917]
  decide +kernel

theorem arows1909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1909 = true := by
  rw [show D2M8K2.u1909 = KTree.node D2M8K2.t1918 (nat_lit 4199367) (nat_lit 3638020786) (nat_lit 0) D2M8K2.t1919 from rfl, allE_node, rows1918, irow1909, rows1919]
  all_goals rfl

theorem atot1909 : totK PD2M8K2 D2M8K2.u1909 = [0, 302801985352, 829653271214, 582333423530, 101328830053, 3460111309, 0, 0] := by
  rw [show D2M8K2.u1909 = KTree.node D2M8K2.t1918 (nat_lit 4199367) (nat_lit 3638020786) (nat_lit 0) D2M8K2.t1919 from rfl, totK_node, tot1918, tot1919]
  decide +kernel

theorem arows1916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1916 = true := by
  rw [show D2M8K2.u1916 = KTree.node D2M8K2.t1920 (nat_lit 4201658) (nat_lit 4223440842) (nat_lit 0) D2M8K2.t1921 from rfl, allE_node, rows1920, irow1916, rows1921]
  all_goals rfl

theorem atot1916 : totK PD2M8K2 D2M8K2.u1916 = [0, 109965662813, 628074602177, 843051396115, 219790137913, 5455647540, 0, 0] := by
  rw [show D2M8K2.u1916 = KTree.node D2M8K2.t1920 (nat_lit 4201658) (nat_lit 4223440842) (nat_lit 0) D2M8K2.t1921 from rfl, totK_node, tot1920, tot1921]
  decide +kernel

theorem arows1917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1917 = true := by
  rw [show D2M8K2.u1917 = KTree.node D2M8K2.t1922 (nat_lit 4206720) (nat_lit 3402447142) (nat_lit 0) D2M8K2.t1923 from rfl, allE_node, rows1922, irow1917, rows1923]
  all_goals rfl

theorem atot1917 : totK PD2M8K2 D2M8K2.u1917 = [0, 353809416875, 932242820419, 506128861078, 39895622250, 0, 0, 0] := by
  rw [show D2M8K2.u1917 = KTree.node D2M8K2.t1922 (nat_lit 4206720) (nat_lit 3402447142) (nat_lit 0) D2M8K2.t1923 from rfl, totK_node, tot1922, tot1923]
  decide +kernel

theorem arows1919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1919 = true := by
  rw [show D2M8K2.u1919 = KTree.node D2M8K2.t1924 (nat_lit 4208360) (nat_lit 3076964797) (nat_lit 0) D2M8K2.t1925 from rfl, allE_node, rows1924, irow1919, rows1925]
  all_goals rfl

theorem atot1919 : totK PD2M8K2 D2M8K2.u1919 = [0, 0, 474579022955, 995078716356, 309531548993, 8710740030, 0, 0] := by
  rw [show D2M8K2.u1919 = KTree.node D2M8K2.t1924 (nat_lit 4208360) (nat_lit 3076964797) (nat_lit 0) D2M8K2.t1925 from rfl, totK_node, tot1924, tot1925]
  decide +kernel

theorem arows1920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1920 = true := by
  rw [show D2M8K2.u1920 = KTree.node D2M8K2.t1926 (nat_lit 4210160) (nat_lit 2742554369) (nat_lit 0) D2M8K2.t1927 from rfl, allE_node, rows1926, irow1920, rows1927]
  all_goals rfl

theorem atot1920 : totK PD2M8K2 D2M8K2.u1920 = [0, 0, 357866691676, 941170019725, 443406298461, 23772366266, 0, 0] := by
  rw [show D2M8K2.u1920 = KTree.node D2M8K2.t1926 (nat_lit 4210160) (nat_lit 2742554369) (nat_lit 0) D2M8K2.t1927 from rfl, totK_node, tot1926, tot1927]
  decide +kernel

theorem arows1923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1923 = true := by
  rw [show D2M8K2.u1923 = KTree.node D2M8K2.t1928 (nat_lit 4211821) (nat_lit 1048111176) (nat_lit 0) D2M8K2.t1929 from rfl, allE_node, rows1928, irow1923, rows1929]
  all_goals rfl

theorem atot1923 : totK PD2M8K2 D2M8K2.u1923 = [0, 0, 139158424232, 726834517104, 800652832459, 114562071631, 1310285577, 0] := by
  rw [show D2M8K2.u1923 = KTree.node D2M8K2.t1928 (nat_lit 4211821) (nat_lit 1048111176) (nat_lit 0) D2M8K2.t1929 from rfl, totK_node, tot1928, tot1929]
  decide +kernel

theorem arows1924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1924 = true := by
  rw [show D2M8K2.u1924 = KTree.node D2M8K2.t1930 (nat_lit 4213947) (nat_lit 3452925158) (nat_lit 0) D2M8K2.t1931 from rfl, allE_node, rows1930, irow1924, rows1931]
  all_goals rfl

theorem atot1924 : totK PD2M8K2 D2M8K2.u1924 = [0, 0, 346431827631, 905733137559, 523129543522, 44872931961, 0, 0] := by
  rw [show D2M8K2.u1924 = KTree.node D2M8K2.t1930 (nat_lit 4213947) (nat_lit 3452925158) (nat_lit 0) D2M8K2.t1931 from rfl, totK_node, tot1930, tot1931]
  decide +kernel

theorem arows1926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1926 = true := by
  rw [show D2M8K2.u1926 = KTree.node D2M8K2.t1932 (nat_lit 4217005) (nat_lit 1055580061) (nat_lit 0) D2M8K2.t1933 from rfl, allE_node, rows1932, irow1926, rows1933]
  all_goals rfl

theorem atot1926 : totK PD2M8K2 D2M8K2.u1926 = [0, 0, 372141227230, 937187843228, 458159596071, 27963946715, 0, 0] := by
  rw [show D2M8K2.u1926 = KTree.node D2M8K2.t1932 (nat_lit 4217005) (nat_lit 1055580061) (nat_lit 0) D2M8K2.t1933 from rfl, totK_node, tot1932, tot1933]
  decide +kernel

theorem arows1927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1927 = true := by
  rw [show D2M8K2.u1927 = KTree.node D2M8K2.t1934 (nat_lit 4218745) (nat_lit 1458770128) (nat_lit 0) D2M8K2.t1935 from rfl, allE_node, rows1934, irow1927, rows1935]
  all_goals rfl

theorem atot1927 : totK PD2M8K2 D2M8K2.u1927 = [0, 0, 81861026506, 630768655190, 852756341410, 176361097233, 4879840392, 0] := by
  rw [show D2M8K2.u1927 = KTree.node D2M8K2.t1934 (nat_lit 4218745) (nat_lit 1458770128) (nat_lit 0) D2M8K2.t1935 from rfl, totK_node, tot1934, tot1935]
  decide +kernel

theorem arows1931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1931 = true := by
  rw [show D2M8K2.u1931 = KTree.node D2M8K2.t1936 (nat_lit 4221244) (nat_lit 3644773608) (nat_lit 0) D2M8K2.t1937 from rfl, allE_node, rows1936, irow1931, rows1937]
  all_goals rfl

theorem atot1931 : totK PD2M8K2 D2M8K2.u1931 = [0, 0, 384050708202, 965069450042, 454988113936, 21977406651, 0, 0] := by
  rw [show D2M8K2.u1931 = KTree.node D2M8K2.t1936 (nat_lit 4221244) (nat_lit 3644773608) (nat_lit 0) D2M8K2.t1937 from rfl, totK_node, tot1936, tot1937]
  decide +kernel

theorem arows1932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1932 = true := by
  rw [show D2M8K2.u1932 = KTree.node D2M8K2.t1938 (nat_lit 4227634) (nat_lit 3971458393) (nat_lit 0) D2M8K2.t1939 from rfl, allE_node, rows1938, irow1932, rows1939]
  all_goals rfl

theorem atot1932 : totK PD2M8K2 D2M8K2.u1932 = [0, 0, 301120377942, 893836145847, 573119183138, 45477156748, 0, 0] := by
  rw [show D2M8K2.u1932 = KTree.node D2M8K2.t1938 (nat_lit 4227634) (nat_lit 3971458393) (nat_lit 0) D2M8K2.t1939 from rfl, totK_node, tot1938, tot1939]
  decide +kernel

theorem arows1934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1934 = true := by
  rw [show D2M8K2.u1934 = KTree.node D2M8K2.t1940 (nat_lit 4229371) (nat_lit 1893805257) (nat_lit 512) D2M8K2.t1941 from rfl, allE_node, rows1940, irow1934, rows1941]
  all_goals rfl

theorem atot1934 : totK PD2M8K2 D2M8K2.u1934 = [0, 92082099022, 225189286362, 446341428561, 741584435669, 259793522144, 13786494048, 0] := by
  rw [show D2M8K2.u1934 = KTree.node D2M8K2.t1940 (nat_lit 4229371) (nat_lit 1893805257) (nat_lit 512) D2M8K2.t1941 from rfl, totK_node, tot1940, tot1941]
  decide +kernel

theorem arows1935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1935 = true := by
  rw [show D2M8K2.u1935 = KTree.node D2M8K2.t1942 (nat_lit 4480146) (nat_lit 3362829394) (nat_lit 0) D2M8K2.t1943 from rfl, allE_node, rows1942, irow1935, rows1943]
  all_goals rfl

theorem atot1935 : totK PD2M8K2 D2M8K2.u1935 = [0, 345264972849, 918390519142, 507547144889, 36075309768, 0, 0, 0] := by
  rw [show D2M8K2.u1935 = KTree.node D2M8K2.t1942 (nat_lit 4480146) (nat_lit 3362829394) (nat_lit 0) D2M8K2.t1943 from rfl, totK_node, tot1942, tot1943]
  decide +kernel

theorem arows1938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1938 = true := by
  rw [show D2M8K2.u1938 = KTree.node D2M8K2.t1944 (nat_lit 4481921) (nat_lit 2087448358) (nat_lit 0) D2M8K2.t1945 from rfl, allE_node, rows1944, irow1938, rows1945]
  all_goals rfl

theorem atot1938 : totK PD2M8K2 D2M8K2.u1938 = [0, 157384650155, 706363430762, 812215788104, 142949773082, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1938 = KTree.node D2M8K2.t1944 (nat_lit 4481921) (nat_lit 2087448358) (nat_lit 0) D2M8K2.t1945 from rfl, totK_node, tot1944, tot1945]
  decide +kernel

theorem arows1939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1939 = true := by
  rw [show D2M8K2.u1939 = KTree.node D2M8K2.t1946 (nat_lit 4487473) (nat_lit 1530333362) (nat_lit 0) D2M8K2.t1947 from rfl, allE_node, rows1946, irow1939, rows1947]
  all_goals rfl

theorem atot1939 : totK PD2M8K2 D2M8K2.u1939 = [0, 184692093046, 729091109382, 708991828540, 140298094646, 2309606161, 0, 0] := by
  rw [show D2M8K2.u1939 = KTree.node D2M8K2.t1946 (nat_lit 4487473) (nat_lit 1530333362) (nat_lit 0) D2M8K2.t1947 from rfl, totK_node, tot1946, tot1947]
  decide +kernel

theorem arows1941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1941 = true := by
  rw [show D2M8K2.u1941 = KTree.node D2M8K2.t1948 (nat_lit 4489469) (nat_lit 2135832880) (nat_lit 0) D2M8K2.t1949 from rfl, allE_node, rows1948, irow1941, rows1949]
  all_goals rfl

theorem atot1941 : totK PD2M8K2 D2M8K2.u1941 = [0, 252526729190, 741966243808, 632483106262, 154165709416, 10740121073, 0, 0] := by
  rw [show D2M8K2.u1941 = KTree.node D2M8K2.t1948 (nat_lit 4489469) (nat_lit 2135832880) (nat_lit 0) D2M8K2.t1949 from rfl, totK_node, tot1948, tot1949]
  decide +kernel

theorem arows1942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1942 = true := by
  rw [show D2M8K2.u1942 = KTree.node D2M8K2.t1950 (nat_lit 4490988) (nat_lit 2843999758) (nat_lit 0) D2M8K2.t1951 from rfl, allE_node, rows1950, irow1942, rows1951]
  all_goals rfl

theorem atot1942 : totK PD2M8K2 D2M8K2.u1942 = [0, 173115031085, 745104498692, 749570569388, 129455131098, 1198073392, 0, 0] := by
  rw [show D2M8K2.u1942 = KTree.node D2M8K2.t1950 (nat_lit 4490988) (nat_lit 2843999758) (nat_lit 0) D2M8K2.t1951 from rfl, totK_node, tot1950, tot1951]
  decide +kernel

theorem arows1947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1947 = true := by
  rw [show D2M8K2.u1947 = KTree.node D2M8K2.t1952 (nat_lit 4492810) (nat_lit 3665482403) (nat_lit 0) D2M8K2.t1953 from rfl, allE_node, rows1952, irow1947, rows1953]
  all_goals rfl

theorem atot1947 : totK PD2M8K2 D2M8K2.u1947 = [0, 210283719278, 650949974835, 680058078273, 214543396224, 12052611869, 0, 0] := by
  rw [show D2M8K2.u1947 = KTree.node D2M8K2.t1952 (nat_lit 4492810) (nat_lit 3665482403) (nat_lit 0) D2M8K2.t1953 from rfl, totK_node, tot1952, tot1953]
  decide +kernel

theorem arows1948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1948 = true := by
  rw [show D2M8K2.u1948 = KTree.node D2M8K2.t1954 (nat_lit 4494051) (nat_lit 3620178571) (nat_lit 0) D2M8K2.t1955 from rfl, allE_node, rows1954, irow1948, rows1955]
  all_goals rfl

theorem atot1948 : totK PD2M8K2 D2M8K2.u1948 = [0, 199439170717, 769798173141, 697021681859, 105144570241, 1096505104, 0, 0] := by
  rw [show D2M8K2.u1948 = KTree.node D2M8K2.t1954 (nat_lit 4494051) (nat_lit 3620178571) (nat_lit 0) D2M8K2.t1955 from rfl, totK_node, tot1954, tot1955]
  decide +kernel

theorem arows1950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1950 = true := by
  rw [show D2M8K2.u1950 = KTree.node D2M8K2.t1956 (nat_lit 4496370) (nat_lit 3287238043) (nat_lit 0) D2M8K2.t1957 from rfl, allE_node, rows1956, irow1950, rows1957]
  all_goals rfl

theorem atot1950 : totK PD2M8K2 D2M8K2.u1950 = [0, 235465815927, 758474350174, 666725393455, 132802622565, 3884009855, 0, 0] := by
  rw [show D2M8K2.u1950 = KTree.node D2M8K2.t1956 (nat_lit 4496370) (nat_lit 3287238043) (nat_lit 0) D2M8K2.t1957 from rfl, totK_node, tot1956, tot1957]
  decide +kernel

theorem arows1951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1951 = true := by
  rw [show D2M8K2.u1951 = KTree.node D2M8K2.t1958 (nat_lit 4497902) (nat_lit 2559679328) (nat_lit 0) D2M8K2.t1959 from rfl, allE_node, rows1958, irow1951, rows1959]
  all_goals rfl

theorem atot1951 : totK PD2M8K2 D2M8K2.u1951 = [0, 179476509406, 734987158251, 747304996584, 139572217911, 1268739303, 0, 0] := by
  rw [show D2M8K2.u1951 = KTree.node D2M8K2.t1958 (nat_lit 4497902) (nat_lit 2559679328) (nat_lit 0) D2M8K2.t1959 from rfl, totK_node, tot1958, tot1959]
  decide +kernel

theorem arows1954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1954 = true := by
  rw [show D2M8K2.u1954 = KTree.node D2M8K2.t1960 (nat_lit 4499616) (nat_lit 3256153750) (nat_lit 0) D2M8K2.t1961 from rfl, allE_node, rows1960, irow1954, rows1961]
  all_goals rfl

theorem atot1954 : totK PD2M8K2 D2M8K2.u1954 = [0, 0, 353050375270, 943873567878, 444180646551, 28001379322, 0, 0] := by
  rw [show D2M8K2.u1954 = KTree.node D2M8K2.t1960 (nat_lit 4499616) (nat_lit 3256153750) (nat_lit 0) D2M8K2.t1961 from rfl, totK_node, tot1960, tot1961]
  decide +kernel

theorem arows1955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1955 = true := by
  rw [show D2M8K2.u1955 = KTree.node D2M8K2.t1962 (nat_lit 4501118) (nat_lit 2147300753) (nat_lit 0) D2M8K2.t1963 from rfl, allE_node, rows1962, irow1955, rows1963]
  all_goals rfl

theorem atot1955 : totK PD2M8K2 D2M8K2.u1955 = [0, 0, 260990211568, 794144130943, 583145372247, 103918199350, 1369150432, 0] := by
  rw [show D2M8K2.u1955 = KTree.node D2M8K2.t1962 (nat_lit 4501118) (nat_lit 2147300753) (nat_lit 0) D2M8K2.t1963 from rfl, totK_node, tot1962, tot1963]
  decide +kernel

theorem arows1957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1957 = true := by
  rw [show D2M8K2.u1957 = KTree.node D2M8K2.t1964 (nat_lit 4506686) (nat_lit 3081886034) (nat_lit 0) D2M8K2.t1965 from rfl, allE_node, rows1964, irow1957, rows1965]
  all_goals rfl

theorem atot1957 : totK PD2M8K2 D2M8K2.u1957 = [0, 0, 234770307074, 838433312701, 617143748194, 63173249217, 0, 0] := by
  rw [show D2M8K2.u1957 = KTree.node D2M8K2.t1964 (nat_lit 4506686) (nat_lit 3081886034) (nat_lit 0) D2M8K2.t1965 from rfl, totK_node, tot1964, tot1965]
  decide +kernel

theorem arows1958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1958 = true := by
  rw [show D2M8K2.u1958 = KTree.node D2M8K2.t1966 (nat_lit 4510224) (nat_lit 3736152580) (nat_lit 0) D2M8K2.t1967 from rfl, allE_node, rows1966, irow1958, rows1967]
  all_goals rfl

theorem atot1958 : totK PD2M8K2 D2M8K2.u1958 = [0, 0, 358250816749, 954663105096, 452795928712, 24166345301, 0, 0] := by
  rw [show D2M8K2.u1958 = KTree.node D2M8K2.t1966 (nat_lit 4510224) (nat_lit 3736152580) (nat_lit 0) D2M8K2.t1967 from rfl, totK_node, tot1966, tot1967]
  decide +kernel

theorem arows1962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1962 = true := by
  rw [show D2M8K2.u1962 = KTree.node D2M8K2.t1968 (nat_lit 4511806) (nat_lit 3738270421) (nat_lit 0) D2M8K2.t1969 from rfl, allE_node, rows1968, irow1962, rows1969]
  all_goals rfl

theorem atot1962 : totK PD2M8K2 D2M8K2.u1962 = [0, 0, 393379254283, 953558023221, 406857902691, 17844655697, 0, 0] := by
  rw [show D2M8K2.u1962 = KTree.node D2M8K2.t1968 (nat_lit 4511806) (nat_lit 3738270421) (nat_lit 0) D2M8K2.t1969 from rfl, totK_node, tot1968, tot1969]
  decide +kernel

theorem arows1963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1963 = true := by
  rw [show D2M8K2.u1963 = KTree.node D2M8K2.t1970 (nat_lit 4514805) (nat_lit 1741952189) (nat_lit 0) D2M8K2.t1971 from rfl, allE_node, rows1970, irow1963, rows1971]
  all_goals rfl

theorem atot1963 : totK PD2M8K2 D2M8K2.u1963 = [0, 0, 343986993747, 940482025362, 460057077434, 23441354541, 0, 0] := by
  rw [show D2M8K2.u1963 = KTree.node D2M8K2.t1970 (nat_lit 4514805) (nat_lit 1741952189) (nat_lit 0) D2M8K2.t1971 from rfl, totK_node, tot1970, tot1971]
  decide +kernel

theorem arows1965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1965 = true := by
  rw [show D2M8K2.u1965 = KTree.node D2M8K2.t1972 (nat_lit 4518477) (nat_lit 695759587) (nat_lit 0) D2M8K2.t1973 from rfl, allE_node, rows1972, irow1965, rows1973]
  all_goals rfl

theorem atot1965 : totK PD2M8K2 D2M8K2.u1965 = [0, 102184501845, 507463881491, 831508908841, 357861831558, 24343321163, 0, 0] := by
  rw [show D2M8K2.u1965 = KTree.node D2M8K2.t1972 (nat_lit 4518477) (nat_lit 695759587) (nat_lit 0) D2M8K2.t1973 from rfl, totK_node, tot1972, tot1973]
  decide +kernel

theorem arows1966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1966 = true := by
  rw [show D2M8K2.u1966 = KTree.node D2M8K2.t1974 (nat_lit 4525114) (nat_lit 2753779506) (nat_lit 0) D2M8K2.t1975 from rfl, allE_node, rows1974, irow1966, rows1975]
  all_goals rfl

theorem atot1966 : totK PD2M8K2 D2M8K2.u1966 = [0, 324837772498, 914257287951, 531104994069, 47454447075, 0, 0, 0] := by
  rw [show D2M8K2.u1966 = KTree.node D2M8K2.t1974 (nat_lit 4525114) (nat_lit 2753779506) (nat_lit 0) D2M8K2.t1975 from rfl, totK_node, tot1974, tot1975]
  decide +kernel

theorem arows1969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1969 = true := by
  rw [show D2M8K2.u1969 = KTree.node D2M8K2.t1976 (nat_lit 4526613) (nat_lit 1730766126) (nat_lit 0) D2M8K2.t1977 from rfl, allE_node, rows1976, irow1969, rows1977]
  all_goals rfl

theorem atot1969 : totK PD2M8K2 D2M8K2.u1969 = [0, 0, 372352954316, 951794330698, 457106493246, 30804453458, 0, 0] := by
  rw [show D2M8K2.u1969 = KTree.node D2M8K2.t1976 (nat_lit 4526613) (nat_lit 1730766126) (nat_lit 0) D2M8K2.t1977 from rfl, totK_node, tot1976, tot1977]
  decide +kernel

theorem arows1970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1970 = true := by
  rw [show D2M8K2.u1970 = KTree.node D2M8K2.t1978 (nat_lit 4531365) (nat_lit 1403094468) (nat_lit 0) D2M8K2.t1979 from rfl, allE_node, rows1978, irow1970, rows1979]
  all_goals rfl

theorem atot1970 : totK PD2M8K2 D2M8K2.u1970 = [0, 339119349679, 869980961715, 494197285741, 105943637651, 6804944647, 0, 0] := by
  rw [show D2M8K2.u1970 = KTree.node D2M8K2.t1978 (nat_lit 4531365) (nat_lit 1403094468) (nat_lit 0) D2M8K2.t1979 from rfl, totK_node, tot1978, tot1979]
  decide +kernel

theorem arows1972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1972 = true := by
  rw [show D2M8K2.u1972 = KTree.node D2M8K2.t1980 (nat_lit 4532911) (nat_lit 2428327644) (nat_lit 0) D2M8K2.t1981 from rfl, allE_node, rows1980, irow1972, rows1981]
  all_goals rfl

theorem atot1972 : totK PD2M8K2 D2M8K2.u1972 = [0, 87085179265, 561620850004, 870303852609, 254358461236, 10671004620, 0, 0] := by
  rw [show D2M8K2.u1972 = KTree.node D2M8K2.t1980 (nat_lit 4532911) (nat_lit 2428327644) (nat_lit 0) D2M8K2.t1981 from rfl, totK_node, tot1980, tot1981]
  decide +kernel

theorem arows1973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1973 = true := by
  rw [show D2M8K2.u1973 = KTree.node D2M8K2.t1982 (nat_lit 4534739) (nat_lit 2646724390) (nat_lit 0) D2M8K2.t1983 from rfl, allE_node, rows1982, irow1973, rows1983]
  all_goals rfl

theorem atot1973 : totK PD2M8K2 D2M8K2.u1973 = [0, 309888244385, 847820564452, 555423359053, 90171656580, 2566665356, 0, 0] := by
  rw [show D2M8K2.u1973 = KTree.node D2M8K2.t1982 (nat_lit 4534739) (nat_lit 2646724390) (nat_lit 0) D2M8K2.t1983 from rfl, totK_node, tot1982, tot1983]
  decide +kernel

theorem arows1979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1979 = true := by
  rw [show D2M8K2.u1979 = KTree.node D2M8K2.t1984 (nat_lit 4536353) (nat_lit 2184812196) (nat_lit 0) D2M8K2.t1985 from rfl, allE_node, rows1984, irow1979, rows1985]
  all_goals rfl

theorem atot1979 : totK PD2M8K2 D2M8K2.u1979 = [0, 90363393300, 658745330396, 870290160921, 170994204372, 2163539312, 0, 0] := by
  rw [show D2M8K2.u1979 = KTree.node D2M8K2.t1984 (nat_lit 4536353) (nat_lit 2184812196) (nat_lit 0) D2M8K2.t1985 from rfl, totK_node, tot1984, tot1985]
  decide +kernel

theorem arows1980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1980 = true := by
  rw [show D2M8K2.u1980 = KTree.node D2M8K2.t1986 (nat_lit 4538317) (nat_lit 1358046873) (nat_lit 0) D2M8K2.t1987 from rfl, allE_node, rows1986, irow1980, rows1987]
  all_goals rfl

theorem atot1980 : totK PD2M8K2 D2M8K2.u1980 = [0, 367839823673, 892618961795, 491367562242, 70596373760, 2813333534, 0, 0] := by
  rw [show D2M8K2.u1980 = KTree.node D2M8K2.t1986 (nat_lit 4538317) (nat_lit 1358046873) (nat_lit 0) D2M8K2.t1987 from rfl, totK_node, tot1986, tot1987]
  decide +kernel

theorem arows1982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1982 = true := by
  rw [show D2M8K2.u1982 = KTree.node D2M8K2.t1988 (nat_lit 4540044) (nat_lit 3330450072) (nat_lit 0) D2M8K2.t1989 from rfl, allE_node, rows1988, irow1982, rows1989]
  all_goals rfl

theorem atot1982 : totK PD2M8K2 D2M8K2.u1982 = [0, 34693629254, 539565780364, 942415226486, 272741596977, 6396129584, 0, 0] := by
  rw [show D2M8K2.u1982 = KTree.node D2M8K2.t1988 (nat_lit 4540044) (nat_lit 3330450072) (nat_lit 0) D2M8K2.t1989 from rfl, totK_node, tot1988, tot1989]
  decide +kernel

theorem arows1983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1983 = true := by
  rw [show D2M8K2.u1983 = KTree.node D2M8K2.t1990 (nat_lit 4545324) (nat_lit 2366563723) (nat_lit 0) D2M8K2.t1991 from rfl, allE_node, rows1990, irow1983, rows1991]
  all_goals rfl

theorem atot1983 : totK PD2M8K2 D2M8K2.u1983 = [0, 0, 353685341861, 916369206026, 518241654511, 44893233696, 0, 0] := by
  rw [show D2M8K2.u1983 = KTree.node D2M8K2.t1990 (nat_lit 4545324) (nat_lit 2366563723) (nat_lit 0) D2M8K2.t1991 from rfl, totK_node, tot1990, tot1991]
  decide +kernel

theorem arows1986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1986 = true := by
  rw [show D2M8K2.u1986 = KTree.node D2M8K2.t1992 (nat_lit 4551823) (nat_lit 1875006417) (nat_lit 0) D2M8K2.t1993 from rfl, allE_node, rows1992, irow1986, rows1993]
  all_goals rfl

theorem atot1986 : totK PD2M8K2 D2M8K2.u1986 = [0, 0, 340597419107, 925222297492, 519698460666, 40236329694, 0, 0] := by
  rw [show D2M8K2.u1986 = KTree.node D2M8K2.t1992 (nat_lit 4551823) (nat_lit 1875006417) (nat_lit 0) D2M8K2.t1993 from rfl, totK_node, tot1992, tot1993]
  decide +kernel

theorem arows1987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1987 = true := by
  rw [show D2M8K2.u1987 = KTree.node D2M8K2.t1994 (nat_lit 4553280) (nat_lit 3735470318) (nat_lit 0) D2M8K2.t1995 from rfl, allE_node, rows1994, irow1987, rows1995]
  all_goals rfl

theorem atot1987 : totK PD2M8K2 D2M8K2.u1987 = [0, 0, 171714689483, 748518979413, 722353591954, 134379597802, 4031931762, 0] := by
  rw [show D2M8K2.u1987 = KTree.node D2M8K2.t1994 (nat_lit 4553280) (nat_lit 3735470318) (nat_lit 0) D2M8K2.t1995 from rfl, totK_node, tot1994, tot1995]
  decide +kernel

theorem arows1989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1989 = true := by
  rw [show D2M8K2.u1989 = KTree.node D2M8K2.t1996 (nat_lit 4555395) (nat_lit 3717467376) (nat_lit 0) D2M8K2.t1997 from rfl, allE_node, rows1996, irow1989, rows1997]
  all_goals rfl

theorem atot1989 : totK PD2M8K2 D2M8K2.u1989 = [0, 0, 308912402002, 853248402223, 555935873828, 80653677846, 1186940923, 0] := by
  rw [show D2M8K2.u1989 = KTree.node D2M8K2.t1996 (nat_lit 4555395) (nat_lit 3717467376) (nat_lit 0) D2M8K2.t1997 from rfl, totK_node, tot1996, tot1997]
  decide +kernel

theorem arows1990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1990 = true := by
  rw [show D2M8K2.u1990 = KTree.node D2M8K2.t1998 (nat_lit 4557155) (nat_lit 2442644014) (nat_lit 32) D2M8K2.t1999 from rfl, allE_node, rows1998, irow1990, rows1999]
  all_goals rfl

theorem atot1990 : totK PD2M8K2 D2M8K2.u1990 = [0, 0, 139364665451, 739989904588, 784725602652, 114884446429, 1415142070, 0] := by
  rw [show D2M8K2.u1990 = KTree.node D2M8K2.t1998 (nat_lit 4557155) (nat_lit 2442644014) (nat_lit 32) D2M8K2.t1999 from rfl, totK_node, tot1998, tot1999]
  decide +kernel

theorem arows1994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1994 = true := by
  rw [show D2M8K2.u1994 = KTree.node D2M8K2.t2000 (nat_lit 4559215) (nat_lit 1635698009) (nat_lit 0) D2M8K2.t2001 from rfl, allE_node, rows2000, irow1994, rows2001]
  all_goals rfl

theorem atot1994 : totK PD2M8K2 D2M8K2.u1994 = [0, 0, 352326947647, 929503158876, 510053006217, 36268264580, 0, 0] := by
  rw [show D2M8K2.u1994 = KTree.node D2M8K2.t2000 (nat_lit 4559215) (nat_lit 1635698009) (nat_lit 0) D2M8K2.t2001 from rfl, totK_node, tot2000, tot2001]
  decide +kernel

theorem arows1995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1995 = true := by
  rw [show D2M8K2.u1995 = KTree.node D2M8K2.t2002 (nat_lit 4604286) (nat_lit 3963316861) (nat_lit 0) D2M8K2.t2003 from rfl, allE_node, rows2002, irow1995, rows2003]
  all_goals rfl

theorem atot1995 : totK PD2M8K2 D2M8K2.u1995 = [0, 374365455567, 900754812911, 434162765021, 75646303065, 9718976469, 0, 0] := by
  rw [show D2M8K2.u1995 = KTree.node D2M8K2.t2002 (nat_lit 4604286) (nat_lit 3963316861) (nat_lit 0) D2M8K2.t2003 from rfl, totK_node, tot2002, tot2003]
  decide +kernel

theorem arows1997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1997 = true := by
  rw [show D2M8K2.u1997 = KTree.node D2M8K2.t2004 (nat_lit 4605826) (nat_lit 4065923772) (nat_lit 0) D2M8K2.t2005 from rfl, allE_node, rows2004, irow1997, rows2005]
  all_goals rfl

theorem atot1997 : totK PD2M8K2 D2M8K2.u1997 = [0, 107270804487, 674006359046, 871471402525, 153053201175, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1997 = KTree.node D2M8K2.t2004 (nat_lit 4605826) (nat_lit 4065923772) (nat_lit 0) D2M8K2.t2005 from rfl, totK_node, tot2004, tot2005]
  decide +kernel

theorem arows1998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1998 = true := by
  rw [show D2M8K2.u1998 = KTree.node D2M8K2.t2006 (nat_lit 4607928) (nat_lit 3325214047) (nat_lit 0) D2M8K2.t2007 from rfl, allE_node, rows2006, irow1998, rows2007]
  all_goals rfl

theorem atot1998 : totK PD2M8K2 D2M8K2.u1998 = [0, 337075220429, 917138406568, 511915173067, 39956522372, 0, 0, 0] := by
  rw [show D2M8K2.u1998 = KTree.node D2M8K2.t2006 (nat_lit 4607928) (nat_lit 3325214047) (nat_lit 0) D2M8K2.t2007 from rfl, totK_node, tot2006, tot2007]
  decide +kernel

theorem arows2001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2001 = true := by
  rw [show D2M8K2.u2001 = KTree.node D2M8K2.t2008 (nat_lit 4609470) (nat_lit 3971616199) (nat_lit 0) D2M8K2.t2009 from rfl, allE_node, rows2008, irow2001, rows2009]
  all_goals rfl

theorem atot2001 : totK PD2M8K2 D2M8K2.u2001 = [0, 0, 400897070954, 937962679524, 428967743881, 25702258959, 0, 0] := by
  rw [show D2M8K2.u2001 = KTree.node D2M8K2.t2008 (nat_lit 4609470) (nat_lit 3971616199) (nat_lit 0) D2M8K2.t2009 from rfl, totK_node, tot2008, tot2009]
  decide +kernel

theorem arows2002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2002 = true := by
  rw [show D2M8K2.u2002 = KTree.node D2M8K2.t2010 (nat_lit 4614184) (nat_lit 3495518375) (nat_lit 0) D2M8K2.t2011 from rfl, allE_node, rows2010, irow2002, rows2011]
  all_goals rfl

theorem atot2002 : totK PD2M8K2 D2M8K2.u2002 = [0, 338196911627, 832660285263, 532977610257, 127697758962, 5372734930, 0, 0] := by
  rw [show D2M8K2.u2002 = KTree.node D2M8K2.t2010 (nat_lit 4614184) (nat_lit 3495518375) (nat_lit 0) D2M8K2.t2011 from rfl, totK_node, tot2010, tot2011]
  decide +kernel

theorem arows2004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2004 = true := by
  rw [show D2M8K2.u2004 = KTree.node D2M8K2.t2012 (nat_lit 4615631) (nat_lit 2182078361) (nat_lit 0) D2M8K2.t2013 from rfl, allE_node, rows2012, irow2004, rows2013]
  all_goals rfl

theorem atot2004 : totK PD2M8K2 D2M8K2.u2004 = [0, 104296678417, 643659909442, 833714081369, 218874983380, 9668735432, 0, 0] := by
  rw [show D2M8K2.u2004 = KTree.node D2M8K2.t2012 (nat_lit 4615631) (nat_lit 2182078361) (nat_lit 0) D2M8K2.t2013 from rfl, totK_node, tot2012, tot2013]
  decide +kernel

theorem arows2005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2005 = true := by
  rw [show D2M8K2.u2005 = KTree.node D2M8K2.t2014 (nat_lit 4617439) (nat_lit 2383192834) (nat_lit 0) D2M8K2.t2015 from rfl, allE_node, rows2014, irow2005, rows2015]
  all_goals rfl

theorem atot2005 : totK PD2M8K2 D2M8K2.u2005 = [0, 235631258122, 744550628831, 651376485965, 131307602429, 3581949829, 0, 0] := by
  rw [show D2M8K2.u2005 = KTree.node D2M8K2.t2014 (nat_lit 4617439) (nat_lit 2383192834) (nat_lit 0) D2M8K2.t2015 from rfl, totK_node, tot2014, tot2015]
  decide +kernel

theorem arows2010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2010 = true := by
  rw [show D2M8K2.u2010 = KTree.node D2M8K2.t2016 (nat_lit 4618964) (nat_lit 3257634743) (nat_lit 0) D2M8K2.t2017 from rfl, allE_node, rows2016, irow2010, rows2017]
  all_goals rfl

theorem atot2010 : totK PD2M8K2 D2M8K2.u2010 = [0, 180567783026, 755807839050, 748080245214, 117515920148, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2010 = KTree.node D2M8K2.t2016 (nat_lit 4618964) (nat_lit 3257634743) (nat_lit 0) D2M8K2.t2017 from rfl, totK_node, tot2016, tot2017]
  decide +kernel

theorem arows2011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2011 = true := by
  rw [show D2M8K2.u2011 = KTree.node D2M8K2.t2018 (nat_lit 4620992) (nat_lit 3584581762) (nat_lit 0) D2M8K2.t2019 from rfl, allE_node, rows2018, irow2011, rows2019]
  all_goals rfl

theorem atot2011 : totK PD2M8K2 D2M8K2.u2011 = [0, 275137120341, 786613210524, 605179142498, 121536798741, 3884009855, 0, 0] := by
  rw [show D2M8K2.u2011 = KTree.node D2M8K2.t2018 (nat_lit 4620992) (nat_lit 3584581762) (nat_lit 0) D2M8K2.t2019 from rfl, totK_node, tot2018, tot2019]
  decide +kernel

theorem arows2013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2013 = true := by
  rw [show D2M8K2.u2013 = KTree.node D2M8K2.t2020 (nat_lit 4622470) (nat_lit 3681399247) (nat_lit 0) D2M8K2.t2021 from rfl, allE_node, rows2020, irow2013, rows2021]
  all_goals rfl

theorem atot2013 : totK PD2M8K2 D2M8K2.u2013 = [0, 145772694100, 669084438211, 799163432910, 180049742080, 2303467656, 0, 0] := by
  rw [show D2M8K2.u2013 = KTree.node D2M8K2.t2020 (nat_lit 4622470) (nat_lit 3681399247) (nat_lit 0) D2M8K2.t2021 from rfl, totK_node, tot2020, tot2021]
  decide +kernel

theorem arows2014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2014 = true := by
  rw [show D2M8K2.u2014 = KTree.node D2M8K2.t2022 (nat_lit 4624189) (nat_lit 1231020925) (nat_lit 0) D2M8K2.t2023 from rfl, allE_node, rows2022, irow2014, rows2023]
  all_goals rfl

theorem atot2014 : totK PD2M8K2 D2M8K2.u2014 = [0, 0, 401395946771, 969605151257, 393084073099, 17781871142, 0, 0] := by
  rw [show D2M8K2.u2014 = KTree.node D2M8K2.t2022 (nat_lit 4624189) (nat_lit 1231020925) (nat_lit 0) D2M8K2.t2023 from rfl, totK_node, tot2022, tot2023]
  decide +kernel

theorem arows2017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2017 = true := by
  rw [show D2M8K2.u2017 = KTree.node D2M8K2.t2024 (nat_lit 4625765) (nat_lit 1823063267) (nat_lit 0) D2M8K2.t2025 from rfl, allE_node, rows2024, irow2017, rows2025]
  all_goals rfl

theorem atot2017 : totK PD2M8K2 D2M8K2.u2017 = [0, 0, 170711992347, 757190537730, 715996496210, 99028983110, 1239866073, 0] := by
  rw [show D2M8K2.u2017 = KTree.node D2M8K2.t2024 (nat_lit 4625765) (nat_lit 1823063267) (nat_lit 0) D2M8K2.t2025 from rfl, totK_node, tot2024, tot2025]
  decide +kernel

theorem arows2018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2018 = true := by
  rw [show D2M8K2.u2018 = KTree.node D2M8K2.t2026 (nat_lit 4628195) (nat_lit 2812980611) (nat_lit 0) D2M8K2.t2027 from rfl, allE_node, rows2026, irow2018, rows2027]
  all_goals rfl

theorem atot2018 : totK PD2M8K2 D2M8K2.u2018 = [0, 0, 318644923416, 884085181504, 556790909233, 48547964115, 0, 0] := by
  rw [show D2M8K2.u2018 = KTree.node D2M8K2.t2026 (nat_lit 4628195) (nat_lit 2812980611) (nat_lit 0) D2M8K2.t2027 from rfl, totK_node, tot2026, tot2027]
  decide +kernel

theorem arows2020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2020 = true := by
  rw [show D2M8K2.u2020 = KTree.node D2M8K2.t2028 (nat_lit 4634697) (nat_lit 1629921982) (nat_lit 0) D2M8K2.t2029 from rfl, allE_node, rows2028, irow2020, rows2029]
  all_goals rfl

theorem atot2020 : totK PD2M8K2 D2M8K2.u2020 = [0, 0, 354828626487, 934854849537, 488740531717, 31669853575, 0, 0] := by
  rw [show D2M8K2.u2020 = KTree.node D2M8K2.t2028 (nat_lit 4634697) (nat_lit 1629921982) (nat_lit 0) D2M8K2.t2029 from rfl, totK_node, tot2028, tot2029]
  decide +kernel

theorem arows2021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2021 = true := by
  rw [show D2M8K2.u2021 = KTree.node D2M8K2.t2030 (nat_lit 4636160) (nat_lit 2840832856) (nat_lit 0) D2M8K2.t2031 from rfl, allE_node, rows2030, irow2021, rows2031]
  all_goals rfl

theorem atot2021 : totK PD2M8K2 D2M8K2.u2021 = [0, 0, 175567757987, 755636660369, 732936714922, 117365429652, 1171084559, 0] := by
  rw [show D2M8K2.u2021 = KTree.node D2M8K2.t2030 (nat_lit 4636160) (nat_lit 2840832856) (nat_lit 0) D2M8K2.t2031 from rfl, totK_node, tot2030, tot2031]
  decide +kernel

theorem arows2025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2025 = true := by
  rw [show D2M8K2.u2025 = KTree.node D2M8K2.t2032 (nat_lit 4638021) (nat_lit 1509639535) (nat_lit 0) D2M8K2.t2033 from rfl, allE_node, rows2032, irow2025, rows2033]
  all_goals rfl

theorem atot2025 : totK PD2M8K2 D2M8K2.u2025 = [0, 0, 234356747769, 689799447864, 617671777714, 189955401536, 11934365838, 0] := by
  rw [show D2M8K2.u2025 = KTree.node D2M8K2.t2032 (nat_lit 4638021) (nat_lit 1509639535) (nat_lit 0) D2M8K2.t2033 from rfl, totK_node, tot2032, tot2033]
  decide +kernel

theorem arows2026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2026 = true := by
  rw [show D2M8K2.u2026 = KTree.node D2M8K2.t2034 (nat_lit 4639278) (nat_lit 3833293425) (nat_lit 0) D2M8K2.t2035 from rfl, allE_node, rows2034, irow2026, rows2035]
  all_goals rfl

theorem atot2026 : totK PD2M8K2 D2M8K2.u2026 = [0, 0, 179792741300, 804127353503, 667011401107, 82492770400, 1053411165, 0] := by
  rw [show D2M8K2.u2026 = KTree.node D2M8K2.t2034 (nat_lit 4639278) (nat_lit 3833293425) (nat_lit 0) D2M8K2.t2035 from rfl, totK_node, tot2034, tot2035]
  decide +kernel

theorem arows2028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2028 = true := by
  rw [show D2M8K2.u2028 = KTree.node D2M8K2.t2036 (nat_lit 4641679) (nat_lit 1870894709) (nat_lit 0) D2M8K2.t2037 from rfl, allE_node, rows2036, irow2028, rows2037]
  all_goals rfl

theorem atot2028 : totK PD2M8K2 D2M8K2.u2028 = [0, 0, 273945242579, 790860220143, 586088020709, 100323248068, 3667207281, 0] := by
  rw [show D2M8K2.u2028 = KTree.node D2M8K2.t2036 (nat_lit 4641679) (nat_lit 1870894709) (nat_lit 0) D2M8K2.t2037 from rfl, totK_node, tot2036, tot2037]
  decide +kernel

theorem arows2029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2029 = true := by
  rw [show D2M8K2.u2029 = KTree.node D2M8K2.t2038 (nat_lit 4644934) (nat_lit 3385920902) (nat_lit 0) D2M8K2.t2039 from rfl, allE_node, rows2038, irow2029, rows2039]
  all_goals rfl

theorem atot2029 : totK PD2M8K2 D2M8K2.u2029 = [0, 237504842221, 675138737276, 613074855869, 259114094591, 20249401196, 0, 0] := by
  rw [show D2M8K2.u2029 = KTree.node D2M8K2.t2038 (nat_lit 4644934) (nat_lit 3385920902) (nat_lit 0) D2M8K2.t2039 from rfl, totK_node, tot2038, tot2039]
  decide +kernel

theorem arows2032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2032 = true := by
  rw [show D2M8K2.u2032 = KTree.node D2M8K2.t2040 (nat_lit 4646501) (nat_lit 2328801174) (nat_lit 0) D2M8K2.t2041 from rfl, allE_node, rows2040, irow2032, rows2041]
  all_goals rfl

theorem atot2032 : totK PD2M8K2 D2M8K2.u2032 = [0, 172125997828, 742016506738, 738513240216, 127207135171, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2032 = KTree.node D2M8K2.t2040 (nat_lit 4646501) (nat_lit 2328801174) (nat_lit 0) D2M8K2.t2041 from rfl, totK_node, tot2040, tot2041]
  decide +kernel

theorem arows2033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2033 = true := by
  rw [show D2M8K2.u2033 = KTree.node D2M8K2.t2042 (nat_lit 4648849) (nat_lit 1108969780) (nat_lit 0) D2M8K2.t2043 from rfl, allE_node, rows2042, irow2033, rows2043]
  all_goals rfl

theorem atot2033 : totK PD2M8K2 D2M8K2.u2033 = [0, 265832001553, 822772253903, 650027318121, 75071565193, 0, 0, 0] := by
  rw [show D2M8K2.u2033 = KTree.node D2M8K2.t2042 (nat_lit 4648849) (nat_lit 1108969780) (nat_lit 0) D2M8K2.t2043 from rfl, totK_node, tot2042, tot2043]
  decide +kernel

theorem arows2035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2035 = true := by
  rw [show D2M8K2.u2035 = KTree.node D2M8K2.t2044 (nat_lit 4650475) (nat_lit 1473644669) (nat_lit 0) D2M8K2.t2045 from rfl, allE_node, rows2044, irow2035, rows2045]
  all_goals rfl

theorem atot2035 : totK PD2M8K2 D2M8K2.u2035 = [0, 116562474709, 583011525454, 767263754703, 312241672723, 25566528197, 0, 0] := by
  rw [show D2M8K2.u2035 = KTree.node D2M8K2.t2044 (nat_lit 4650475) (nat_lit 1473644669) (nat_lit 0) D2M8K2.t2045 from rfl, totK_node, tot2044, tot2045]
  decide +kernel

theorem arows2036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2036 = true := by
  rw [show D2M8K2.u2036 = KTree.node D2M8K2.t2046 (nat_lit 4651875) (nat_lit 2848734250) (nat_lit 0) D2M8K2.t2047 from rfl, allE_node, rows2046, irow2036, rows2047]
  all_goals rfl

theorem atot2036 : totK PD2M8K2 D2M8K2.u2036 = [0, 238634295211, 718061730256, 628708769924, 206423190908, 7892383752, 0, 0] := by
  rw [show D2M8K2.u2036 = KTree.node D2M8K2.t2046 (nat_lit 4651875) (nat_lit 2848734250) (nat_lit 0) D2M8K2.t2047 from rfl, totK_node, tot2046, tot2047]
  decide +kernel

theorem arows2047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2047 = true := by
  rw [show D2M8K2.u2047 = KTree.node D2M8K2.t2048 (nat_lit 4653838) (nat_lit 3481964015) (nat_lit 0) D2M8K2.t2049 from rfl, allE_node, rows2048, irow2047, rows2049]
  all_goals rfl

theorem atot2047 : totK PD2M8K2 D2M8K2.u2047 = [0, 87654302015, 577283691314, 844685291805, 240223390055, 10568566766, 0, 0] := by
  rw [show D2M8K2.u2047 = KTree.node D2M8K2.t2048 (nat_lit 4653838) (nat_lit 3481964015) (nat_lit 0) D2M8K2.t2049 from rfl, totK_node, tot2048, tot2049]
  decide +kernel

theorem arows2048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2048 = true := by
  rw [show D2M8K2.u2048 = KTree.node D2M8K2.t2050 (nat_lit 4655794) (nat_lit 4046506451) (nat_lit 0) D2M8K2.t2051 from rfl, allE_node, rows2050, irow2048, rows2051]
  all_goals rfl

theorem atot2048 : totK PD2M8K2 D2M8K2.u2048 = [0, 358310205550, 901870440338, 482778367492, 58577597006, 2481160468, 0, 0] := by
  rw [show D2M8K2.u2048 = KTree.node D2M8K2.t2050 (nat_lit 4655794) (nat_lit 4046506451) (nat_lit 0) D2M8K2.t2051 from rfl, totK_node, tot2050, tot2051]
  decide +kernel

theorem arows2050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2050 = true := by
  rw [show D2M8K2.u2050 = KTree.node D2M8K2.t2052 (nat_lit 4657349) (nat_lit 1927042336) (nat_lit 0) D2M8K2.t2053 from rfl, allE_node, rows2052, irow2050, rows2053]
  all_goals rfl

theorem atot2050 : totK PD2M8K2 D2M8K2.u2050 = [0, 65562492737, 530560272923, 895102617489, 273735141835, 10680993762, 0, 0] := by
  rw [show D2M8K2.u2050 = KTree.node D2M8K2.t2052 (nat_lit 4657349) (nat_lit 1927042336) (nat_lit 0) D2M8K2.t2053 from rfl, totK_node, tot2052, tot2053]
  decide +kernel

theorem arows2051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2051 = true := by
  rw [show D2M8K2.u2051 = KTree.node D2M8K2.t2054 (nat_lit 4659160) (nat_lit 3667199931) (nat_lit 0) D2M8K2.t2055 from rfl, allE_node, rows2054, irow2051, rows2055]
  all_goals rfl

theorem atot2051 : totK PD2M8K2 D2M8K2.u2051 = [0, 343105864859, 877428749059, 502745357043, 69416064289, 2569691499, 0, 0] := by
  rw [show D2M8K2.u2051 = KTree.node D2M8K2.t2054 (nat_lit 4659160) (nat_lit 3667199931) (nat_lit 0) D2M8K2.t2055 from rfl, totK_node, tot2054, tot2055]
  decide +kernel

theorem arows2054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2054 = true := by
  rw [show D2M8K2.u2054 = KTree.node D2M8K2.t2056 (nat_lit 4660656) (nat_lit 3443103083) (nat_lit 0) D2M8K2.t2057 from rfl, allE_node, rows2056, irow2054, rows2057]
  all_goals rfl

theorem atot2054 : totK PD2M8K2 D2M8K2.u2054 = [0, 92722817510, 709841315614, 871750005821, 139051943170, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2054 = KTree.node D2M8K2.t2056 (nat_lit 4660656) (nat_lit 3443103083) (nat_lit 0) D2M8K2.t2057 from rfl, totK_node, tot2056, tot2057]
  decide +kernel

theorem arows2055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2055 = true := by
  rw [show D2M8K2.u2055 = KTree.node D2M8K2.t2058 (nat_lit 4666331) (nat_lit 2188862505) (nat_lit 0) D2M8K2.t2059 from rfl, allE_node, rows2058, irow2055, rows2059]
  all_goals rfl

theorem atot2055 : totK PD2M8K2 D2M8K2.u2055 = [0, 0, 366192263535, 944704192041, 417174407392, 23226855963, 0, 0] := by
  rw [show D2M8K2.u2055 = KTree.node D2M8K2.t2058 (nat_lit 4666331) (nat_lit 2188862505) (nat_lit 0) D2M8K2.t2059 from rfl, totK_node, tot2058, tot2059]
  decide +kernel

theorem arows2057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2057 = true := by
  rw [show D2M8K2.u2057 = KTree.node D2M8K2.t2060 (nat_lit 4668005) (nat_lit 2335408628) (nat_lit 0) D2M8K2.t2061 from rfl, allE_node, rows2060, irow2057, rows2061]
  all_goals rfl

theorem atot2057 : totK PD2M8K2 D2M8K2.u2057 = [0, 0, 158494679762, 773146227490, 709977767630, 97706401123, 1138244013, 0] := by
  rw [show D2M8K2.u2057 = KTree.node D2M8K2.t2060 (nat_lit 4668005) (nat_lit 2335408628) (nat_lit 0) D2M8K2.t2061 from rfl, totK_node, tot2060, tot2061]
  decide +kernel

theorem arows2058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2058 = true := by
  rw [show D2M8K2.u2058 = KTree.node D2M8K2.t2062 (nat_lit 4670224) (nat_lit 3036912748) (nat_lit 0) D2M8K2.t2063 from rfl, allE_node, rows2062, irow2058, rows2063]
  all_goals rfl

theorem atot2058 : totK PD2M8K2 D2M8K2.u2058 = [0, 0, 375830539196, 961917915463, 443940751874, 19427720952, 0, 0] := by
  rw [show D2M8K2.u2058 = KTree.node D2M8K2.t2062 (nat_lit 4670224) (nat_lit 3036912748) (nat_lit 0) D2M8K2.t2063 from rfl, totK_node, tot2062, tot2063]
  decide +kernel

theorem arows2062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2062 = true := by
  rw [show D2M8K2.u2062 = KTree.node D2M8K2.t2064 (nat_lit 4673692) (nat_lit 3869945590) (nat_lit 0) D2M8K2.t2065 from rfl, allE_node, rows2064, irow2062, rows2065]
  all_goals rfl

theorem atot2062 : totK PD2M8K2 D2M8K2.u2062 = [0, 0, 382009076888, 970450062730, 409052528581, 15053323725, 0, 0] := by
  rw [show D2M8K2.u2062 = KTree.node D2M8K2.t2064 (nat_lit 4673692) (nat_lit 3869945590) (nat_lit 0) D2M8K2.t2065 from rfl, totK_node, tot2064, tot2065]
  decide +kernel

theorem arows2063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2063 = true := by
  rw [show D2M8K2.u2063 = KTree.node D2M8K2.t2066 (nat_lit 4677200) (nat_lit 3815758046) (nat_lit 0) D2M8K2.t2067 from rfl, allE_node, rows2066, irow2063, rows2067]
  all_goals rfl

theorem atot2063 : totK PD2M8K2 D2M8K2.u2063 = [0, 0, 364570041036, 938465170808, 461780424280, 27314821055, 0, 0] := by
  rw [show D2M8K2.u2063 = KTree.node D2M8K2.t2066 (nat_lit 4677200) (nat_lit 3815758046) (nat_lit 0) D2M8K2.t2067 from rfl, totK_node, tot2066, tot2067]
  decide +kernel

theorem arows2065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2065 = true := by
  rw [show D2M8K2.u2065 = KTree.node D2M8K2.t2068 (nat_lit 4680246) (nat_lit 2842803436) (nat_lit 0) D2M8K2.t2069 from rfl, allE_node, rows2068, irow2065, rows2069]
  all_goals rfl

theorem atot2065 : totK PD2M8K2 D2M8K2.u2065 = [0, 0, 348725908796, 940746977353, 459100714228, 28697161956, 0, 0] := by
  rw [show D2M8K2.u2065 = KTree.node D2M8K2.t2068 (nat_lit 4680246) (nat_lit 2842803436) (nat_lit 0) D2M8K2.t2069 from rfl, totK_node, tot2068, tot2069]
  decide +kernel

theorem arows2066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2066 = true := by
  rw [show D2M8K2.u2066 = KTree.node D2M8K2.t2070 (nat_lit 4682119) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t2071 from rfl, allE_node, rows2070, irow2066, rows2071]
  all_goals rfl

theorem atot2066 : totK PD2M8K2 D2M8K2.u2066 = [0, 107685783034, 248505940659, 502908646848, 695584190784, 172119483308, 4977114383, 0] := by
  rw [show D2M8K2.u2066 = KTree.node D2M8K2.t2070 (nat_lit 4682119) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t2071 from rfl, totK_node, tot2070, tot2071]
  decide +kernel

theorem arows2069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2069 = true := by
  rw [show D2M8K2.u2069 = KTree.node D2M8K2.t2072 (nat_lit 4687569) (nat_lit 1837193033) (nat_lit 0) D2M8K2.t2073 from rfl, allE_node, rows2072, irow2069, rows2073]
  all_goals rfl

theorem atot2069 : totK PD2M8K2 D2M8K2.u2069 = [0, 303252185892, 885165797998, 557384988774, 48314394424, 0, 0, 0] := by
  rw [show D2M8K2.u2069 = KTree.node D2M8K2.t2072 (nat_lit 4687569) (nat_lit 1837193033) (nat_lit 0) D2M8K2.t2073 from rfl, totK_node, tot2072, tot2073]
  decide +kernel

theorem arows2070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2070 = true := by
  rw [show D2M8K2.u2070 = KTree.node D2M8K2.t2074 (nat_lit 4689555) (nat_lit 3203580287) (nat_lit 0) D2M8K2.t2075 from rfl, allE_node, rows2074, irow2070, rows2075]
  all_goals rfl

theorem atot2070 : totK PD2M8K2 D2M8K2.u2070 = [0, 157857407050, 696421468038, 816113004463, 149179353703, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2070 = KTree.node D2M8K2.t2074 (nat_lit 4689555) (nat_lit 3203580287) (nat_lit 0) D2M8K2.t2075 from rfl, totK_node, tot2074, tot2075]
  decide +kernel

theorem arows2072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2072 = true := by
  rw [show D2M8K2.u2072 = KTree.node D2M8K2.t2076 (nat_lit 4691304) (nat_lit 3274361847) (nat_lit 0) D2M8K2.t2077 from rfl, allE_node, rows2076, irow2072, rows2077]
  all_goals rfl

theorem atot2072 : totK PD2M8K2 D2M8K2.u2072 = [0, 230499875977, 739588895768, 631869155641, 198988370057, 19897919922, 0, 0] := by
  rw [show D2M8K2.u2072 = KTree.node D2M8K2.t2076 (nat_lit 4691304) (nat_lit 3274361847) (nat_lit 0) D2M8K2.t2077 from rfl, totK_node, tot2076, tot2077]
  decide +kernel

theorem arows2073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2073 = true := by
  rw [show D2M8K2.u2073 = KTree.node D2M8K2.t2078 (nat_lit 4692967) (nat_lit 1851182081) (nat_lit 0) D2M8K2.t2079 from rfl, allE_node, rows2078, irow2073, rows2079]
  all_goals rfl

theorem atot2073 : totK PD2M8K2 D2M8K2.u2073 = [0, 123510007115, 534836168817, 798533040590, 335736961635, 13757251361, 0, 0] := by
  rw [show D2M8K2.u2073 = KTree.node D2M8K2.t2078 (nat_lit 4692967) (nat_lit 1851182081) (nat_lit 0) D2M8K2.t2079 from rfl, totK_node, tot2078, tot2079]
  decide +kernel

theorem arows2078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2078 = true := by
  rw [show D2M8K2.u2078 = KTree.node D2M8K2.t2080 (nat_lit 4694830) (nat_lit 4051415223) (nat_lit 0) D2M8K2.t2081 from rfl, allE_node, rows2080, irow2078, rows2081]
  all_goals rfl

theorem atot2078 : totK PD2M8K2 D2M8K2.u2078 = [0, 205673097969, 777916298325, 722072193481, 116497442823, 1164319620, 0, 0] := by
  rw [show D2M8K2.u2078 = KTree.node D2M8K2.t2080 (nat_lit 4694830) (nat_lit 4051415223) (nat_lit 0) D2M8K2.t2081 from rfl, totK_node, tot2080, tot2081]
  decide +kernel

theorem arows2079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2079 = true := by
  rw [show D2M8K2.u2079 = KTree.node D2M8K2.t2082 (nat_lit 4696979) (nat_lit 2901676247) (nat_lit 0) D2M8K2.t2083 from rfl, allE_node, rows2082, irow2079, rows2083]
  all_goals rfl

theorem atot2079 : totK PD2M8K2 D2M8K2.u2079 = [0, 263847529590, 779601218058, 628659561594, 134015176331, 4234510686, 0, 0] := by
  rw [show D2M8K2.u2079 = KTree.node D2M8K2.t2082 (nat_lit 4696979) (nat_lit 2901676247) (nat_lit 0) D2M8K2.t2083 from rfl, totK_node, tot2082, tot2083]
  decide +kernel

theorem arows2081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2081 = true := by
  rw [show D2M8K2.u2081 = KTree.node D2M8K2.t2084 (nat_lit 4698489) (nat_lit 1451059575) (nat_lit 0) D2M8K2.t2085 from rfl, allE_node, rows2084, irow2081, rows2085]
  all_goals rfl

theorem atot2081 : totK PD2M8K2 D2M8K2.u2081 = [0, 160859056123, 693616697957, 781609823091, 168938988027, 2348440009, 0, 0] := by
  rw [show D2M8K2.u2081 = KTree.node D2M8K2.t2084 (nat_lit 4698489) (nat_lit 1451059575) (nat_lit 0) D2M8K2.t2085 from rfl, totK_node, tot2084, tot2085]
  decide +kernel

theorem arows2082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2082 = true := by
  rw [show D2M8K2.u2082 = KTree.node D2M8K2.t2086 (nat_lit 4703749) (nat_lit 1376198177) (nat_lit 0) D2M8K2.t2087 from rfl, allE_node, rows2086, irow2082, rows2087]
  all_goals rfl

theorem atot2082 : totK PD2M8K2 D2M8K2.u2082 = [0, 257855678611, 744954188927, 623623455318, 166116526159, 10895344854, 0, 0] := by
  rw [show D2M8K2.u2082 = KTree.node D2M8K2.t2086 (nat_lit 4703749) (nat_lit 1376198177) (nat_lit 0) D2M8K2.t2087 from rfl, totK_node, tot2086, tot2087]
  decide +kernel

theorem arows2085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2085 = true := by
  rw [show D2M8K2.u2085 = KTree.node D2M8K2.t2088 (nat_lit 4705222) (nat_lit 3485877379) (nat_lit 0) D2M8K2.t2089 from rfl, allE_node, rows2088, irow2085, rows2089]
  all_goals rfl

theorem atot2085 : totK PD2M8K2 D2M8K2.u2085 = [0, 182433760473, 751611025911, 748506328459, 131821840687, 1268739303, 0, 0] := by
  rw [show D2M8K2.u2085 = KTree.node D2M8K2.t2088 (nat_lit 4705222) (nat_lit 3485877379) (nat_lit 0) D2M8K2.t2089 from rfl, totK_node, tot2088, tot2089]
  decide +kernel

theorem arows2086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2086 = true := by
  rw [show D2M8K2.u2086 = KTree.node D2M8K2.t2090 (nat_lit 4706878) (nat_lit 3913318184) (nat_lit 0) D2M8K2.t2091 from rfl, allE_node, rows2090, irow2086, rows2091]
  all_goals rfl

theorem atot2086 : totK PD2M8K2 D2M8K2.u2086 = [0, 0, 397619710243, 957214465304, 401327183948, 22149860293, 0, 0] := by
  rw [show D2M8K2.u2086 = KTree.node D2M8K2.t2090 (nat_lit 4706878) (nat_lit 3913318184) (nat_lit 0) D2M8K2.t2091 from rfl, totK_node, tot2090, tot2091]
  decide +kernel

theorem arows2088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2088 = true := by
  rw [show D2M8K2.u2088 = KTree.node D2M8K2.t2092 (nat_lit 4708522) (nat_lit 4010135701) (nat_lit 0) D2M8K2.t2093 from rfl, allE_node, rows2092, irow2088, rows2093]
  all_goals rfl

theorem atot2088 : totK PD2M8K2 D2M8K2.u2088 = [0, 0, 241031236800, 816877793661, 616571135639, 83475950196, 1310285577, 0] := by
  rw [show D2M8K2.u2088 = KTree.node D2M8K2.t2092 (nat_lit 4708522) (nat_lit 4010135701) (nat_lit 0) D2M8K2.t2093 from rfl, totK_node, tot2092, tot2093]
  decide +kernel

theorem arows2089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2089 = true := by
  rw [show D2M8K2.u2089 = KTree.node D2M8K2.t2094 (nat_lit 4710928) (nat_lit 2881020226) (nat_lit 0) D2M8K2.t2095 from rfl, allE_node, rows2094, irow2089, rows2095]
  all_goals rfl

theorem atot2089 : totK PD2M8K2 D2M8K2.u2089 = [0, 0, 244259304450, 822718663042, 679783763016, 65727555701, 0, 0] := by
  rw [show D2M8K2.u2089 = KTree.node D2M8K2.t2094 (nat_lit 4710928) (nat_lit 2881020226) (nat_lit 0) D2M8K2.t2095 from rfl, totK_node, tot2094, tot2095]
  decide +kernel

theorem arows2093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2093 = true := by
  rw [show D2M8K2.u2093 = KTree.node D2M8K2.t2096 (nat_lit 4714004) (nat_lit 3079942732) (nat_lit 0) D2M8K2.t2097 from rfl, allE_node, rows2096, irow2093, rows2097]
  all_goals rfl

theorem atot2093 : totK PD2M8K2 D2M8K2.u2093 = [0, 0, 378342128466, 942140797181, 474497734379, 28959686516, 0, 0] := by
  rw [show D2M8K2.u2093 = KTree.node D2M8K2.t2096 (nat_lit 4714004) (nat_lit 3079942732) (nat_lit 0) D2M8K2.t2097 from rfl, totK_node, tot2096, tot2097]
  decide +kernel

theorem arows2094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2094 = true := by
  rw [show D2M8K2.u2094 = KTree.node D2M8K2.t2098 (nat_lit 4717594) (nat_lit 3805879332) (nat_lit 0) D2M8K2.t2099 from rfl, allE_node, rows2098, irow2094, rows2099]
  all_goals rfl

theorem atot2094 : totK PD2M8K2 D2M8K2.u2094 = [0, 0, 355631624131, 938032845248, 486967005629, 30387616970, 0, 0] := by
  rw [show D2M8K2.u2094 = KTree.node D2M8K2.t2098 (nat_lit 4717594) (nat_lit 3805879332) (nat_lit 0) D2M8K2.t2099 from rfl, totK_node, tot2098, tot2099]
  decide +kernel

theorem arows2096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2096 = true := by
  rw [show D2M8K2.u2096 = KTree.node D2M8K2.t2100 (nat_lit 4719147) (nat_lit 3477485915) (nat_lit 0) D2M8K2.t2101 from rfl, allE_node, rows2100, irow2096, rows2101]
  all_goals rfl

theorem atot2096 : totK PD2M8K2 D2M8K2.u2096 = [0, 0, 159924027347, 730578928129, 745280009775, 129615666176, 2160984415, 0] := by
  rw [show D2M8K2.u2096 = KTree.node D2M8K2.t2100 (nat_lit 4719147) (nat_lit 3477485915) (nat_lit 0) D2M8K2.t2101 from rfl, totK_node, tot2100, tot2101]
  decide +kernel

theorem arows2097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2097 = true := by
  rw [show D2M8K2.u2097 = KTree.node D2M8K2.t2102 (nat_lit 4724684) (nat_lit 3553105308) (nat_lit 0) D2M8K2.t2103 from rfl, allE_node, rows2102, irow2097, rows2103]
  all_goals rfl

theorem atot2097 : totK PD2M8K2 D2M8K2.u2097 = [0, 0, 293114347667, 847477668994, 564998743429, 78146256746, 2770420231, 0] := by
  rw [show D2M8K2.u2097 = KTree.node D2M8K2.t2102 (nat_lit 4724684) (nat_lit 3553105308) (nat_lit 0) D2M8K2.t2103 from rfl, totK_node, tot2102, tot2103]
  decide +kernel

theorem arows2100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2100 = true := by
  rw [show D2M8K2.u2100 = KTree.node D2M8K2.t2104 (nat_lit 4726139) (nat_lit 2869624287) (nat_lit 0) D2M8K2.t2105 from rfl, allE_node, rows2104, irow2100, rows2105]
  all_goals rfl

theorem atot2100 : totK PD2M8K2 D2M8K2.u2100 = [0, 0, 145606561253, 758108645894, 778914150660, 123986146021, 1242138600, 0] := by
  rw [show D2M8K2.u2100 = KTree.node D2M8K2.t2104 (nat_lit 4726139) (nat_lit 2869624287) (nat_lit 0) D2M8K2.t2105 from rfl, totK_node, tot2104, tot2105]
  decide +kernel

theorem arows2101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2101 = true := by
  rw [show D2M8K2.u2101 = KTree.node D2M8K2.t2106 (nat_lit 4976842) (nat_lit 3844158402) (nat_lit 0) D2M8K2.t2107 from rfl, allE_node, rows2106, irow2101, rows2107]
  all_goals rfl

theorem atot2101 : totK PD2M8K2 D2M8K2.u2101 = [0, 265999872914, 652331845296, 381269839998, 312014192592, 162275375658, 12610165304, 0] := by
  rw [show D2M8K2.u2101 = KTree.node D2M8K2.t2106 (nat_lit 4976842) (nat_lit 3844158402) (nat_lit 0) D2M8K2.t2107 from rfl, totK_node, tot2106, tot2107]
  decide +kernel

theorem arows2103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2103 = true := by
  rw [show D2M8K2.u2103 = KTree.node D2M8K2.t2108 (nat_lit 4978363) (nat_lit 1509202998) (nat_lit 0) D2M8K2.t2109 from rfl, allE_node, rows2108, irow2103, rows2109]
  all_goals rfl

theorem atot2103 : totK PD2M8K2 D2M8K2.u2103 = [0, 171191186072, 738467492859, 763609738054, 130426829617, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2103 = KTree.node D2M8K2.t2108 (nat_lit 4978363) (nat_lit 1509202998) (nat_lit 0) D2M8K2.t2109 from rfl, totK_node, tot2108, tot2109]
  decide +kernel

theorem arows2104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2104 = true := by
  rw [show D2M8K2.u2104 = KTree.node D2M8K2.t2110 (nat_lit 4983901) (nat_lit 1105433226) (nat_lit 0) D2M8K2.t2111 from rfl, allE_node, rows2110, irow2104, rows2111]
  all_goals rfl

theorem atot2104 : totK PD2M8K2 D2M8K2.u2104 = [0, 299331389095, 862556611509, 587921903958, 59449859329, 0, 0, 0] := by
  rw [show D2M8K2.u2104 = KTree.node D2M8K2.t2110 (nat_lit 4983901) (nat_lit 1105433226) (nat_lit 0) D2M8K2.t2111 from rfl, totK_node, tot2110, tot2111]
  decide +kernel

theorem arows2110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2110 = true := by
  rw [show D2M8K2.u2110 = KTree.node D2M8K2.t2112 (nat_lit 4985417) (nat_lit 1614614815) (nat_lit 0) D2M8K2.t2113 from rfl, allE_node, rows2112, irow2110, rows2113]
  all_goals rfl

theorem atot2110 : totK PD2M8K2 D2M8K2.u2110 = [0, 108956738322, 630670052982, 813188982577, 212089859423, 9587713104, 0, 0] := by
  rw [show D2M8K2.u2110 = KTree.node D2M8K2.t2112 (nat_lit 4985417) (nat_lit 1614614815) (nat_lit 0) D2M8K2.t2113 from rfl, totK_node, tot2112, tot2113]
  decide +kernel

theorem arows2111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2111 = true := by
  rw [show D2M8K2.u2111 = KTree.node D2M8K2.t2114 (nat_lit 4987327) (nat_lit 2347578052) (nat_lit 0) D2M8K2.t2115 from rfl, allE_node, rows2114, irow2111, rows2115]
  all_goals rfl

theorem atot2111 : totK PD2M8K2 D2M8K2.u2111 = [0, 280940924343, 782294326205, 604790530704, 116075453827, 3462014130, 0, 0] := by
  rw [show D2M8K2.u2111 = KTree.node D2M8K2.t2114 (nat_lit 4987327) (nat_lit 2347578052) (nat_lit 0) D2M8K2.t2115 from rfl, totK_node, tot2114, tot2115]
  decide +kernel

theorem arows2113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2113 = true := by
  rw [show D2M8K2.u2113 = KTree.node D2M8K2.t2116 (nat_lit 4988837) (nat_lit 2115707383) (nat_lit 0) D2M8K2.t2117 from rfl, allE_node, rows2116, irow2113, rows2117]
  all_goals rfl

theorem atot2113 : totK PD2M8K2 D2M8K2.u2113 = [0, 131000226796, 638232987685, 778256148643, 213357162586, 9668735432, 0, 0] := by
  rw [show D2M8K2.u2113 = KTree.node D2M8K2.t2116 (nat_lit 4988837) (nat_lit 2115707383) (nat_lit 0) D2M8K2.t2117 from rfl, totK_node, tot2116, tot2117]
  decide +kernel

theorem arows2114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2114 = true := by
  rw [show D2M8K2.u2114 = KTree.node D2M8K2.t2118 (nat_lit 4990681) (nat_lit 1497717970) (nat_lit 0) D2M8K2.t2119 from rfl, allE_node, rows2118, irow2114, rows2119]
  all_goals rfl

theorem atot2114 : totK PD2M8K2 D2M8K2.u2114 = [0, 245453938460, 766288058179, 643389250594, 125911234289, 3581949829, 0, 0] := by
  rw [show D2M8K2.u2114 = KTree.node D2M8K2.t2118 (nat_lit 4990681) (nat_lit 1497717970) (nat_lit 0) D2M8K2.t2119 from rfl, totK_node, tot2118, tot2119]
  decide +kernel

theorem arows2117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2117 = true := by
  rw [show D2M8K2.u2117 = KTree.node D2M8K2.t2120 (nat_lit 4992205) (nat_lit 1389505568) (nat_lit 0) D2M8K2.t2121 from rfl, allE_node, rows2120, irow2117, rows2121]
  all_goals rfl

theorem atot2117 : totK PD2M8K2 D2M8K2.u2117 = [0, 177877115015, 752687292731, 757902039752, 115095191605, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2117 = KTree.node D2M8K2.t2120 (nat_lit 4992205) (nat_lit 1389505568) (nat_lit 0) D2M8K2.t2121 from rfl, totK_node, tot2120, tot2121]
  decide +kernel

theorem arows2118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2118 = true := by
  rw [show D2M8K2.u2118 = KTree.node D2M8K2.t2122 (nat_lit 4994497) (nat_lit 1552153127) (nat_lit 0) D2M8K2.t2123 from rfl, allE_node, rows2122, irow2118, rows2123]
  all_goals rfl

theorem atot2118 : totK PD2M8K2 D2M8K2.u2118 = [0, 287751775937, 805443224588, 576053880513, 114170847515, 3884009855, 0, 0] := by
  rw [show D2M8K2.u2118 = KTree.node D2M8K2.t2122 (nat_lit 4994497) (nat_lit 1552153127) (nat_lit 0) D2M8K2.t2123 from rfl, totK_node, tot2122, tot2123]
  decide +kernel

theorem arows2120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2120 = true := by
  rw [show D2M8K2.u2120 = KTree.node D2M8K2.t2124 (nat_lit 4996289) (nat_lit 2222962290) (nat_lit 0) D2M8K2.t2125 from rfl, allE_node, rows2124, irow2120, rows2125]
  all_goals rfl

theorem atot2120 : totK PD2M8K2 D2M8K2.u2120 = [0, 55861247081, 529509672035, 904903002728, 272080131077, 8710740030, 0, 0] := by
  rw [show D2M8K2.u2120 = KTree.node D2M8K2.t2124 (nat_lit 4996289) (nat_lit 2222962290) (nat_lit 0) D2M8K2.t2125 from rfl, totK_node, tot2124, tot2125]
  decide +kernel

theorem arows2121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2121 = true := by
  rw [show D2M8K2.u2121 = KTree.node D2M8K2.t2126 (nat_lit 4998124) (nat_lit 3853535266) (nat_lit 0) D2M8K2.t2127 from rfl, allE_node, rows2126, irow2121, rows2127]
  all_goals rfl

theorem atot2121 : totK PD2M8K2 D2M8K2.u2121 = [0, 0, 351835062665, 922707090919, 450744210895, 32422137020, 0, 0] := by
  rw [show D2M8K2.u2121 = KTree.node D2M8K2.t2126 (nat_lit 4998124) (nat_lit 3853535266) (nat_lit 0) D2M8K2.t2127 from rfl, totK_node, tot2126, tot2127]
  decide +kernel

theorem arows2125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2125 = true := by
  rw [show D2M8K2.u2125 = KTree.node D2M8K2.t2128 (nat_lit 4999370) (nat_lit 2055818650) (nat_lit 0) D2M8K2.t2129 from rfl, allE_node, rows2128, irow2125, rows2129]
  all_goals rfl

theorem atot2125 : totK PD2M8K2 D2M8K2.u2125 = [0, 0, 98334361347, 682432347685, 805243007789, 145401435901, 1369150432, 0] := by
  rw [show D2M8K2.u2125 = KTree.node D2M8K2.t2128 (nat_lit 4999370) (nat_lit 2055818650) (nat_lit 0) D2M8K2.t2129 from rfl, totK_node, tot2128, tot2129]
  decide +kernel

theorem arows2126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2126 = true := by
  rw [show D2M8K2.u2126 = KTree.node D2M8K2.t2130 (nat_lit 5004980) (nat_lit 3664909440) (nat_lit 0) D2M8K2.t2131 from rfl, allE_node, rows2130, irow2126, rows2131]
  all_goals rfl

theorem atot2126 : totK PD2M8K2 D2M8K2.u2126 = [0, 0, 392267826671, 960221884819, 400656945430, 17707432322, 0, 0] := by
  rw [show D2M8K2.u2126 = KTree.node D2M8K2.t2130 (nat_lit 5004980) (nat_lit 3664909440) (nat_lit 0) D2M8K2.t2131 from rfl, totK_node, tot2130, tot2131]
  decide +kernel

theorem arows2128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2128 = true := by
  rw [show D2M8K2.u2128 = KTree.node D2M8K2.t2132 (nat_lit 5008307) (nat_lit 2572300603) (nat_lit 32) D2M8K2.t2133 from rfl, allE_node, rows2132, irow2128, rows2133]
  all_goals rfl

theorem atot2128 : totK PD2M8K2 D2M8K2.u2128 = [0, 0, 348969007621, 927031017117, 463532745948, 26643838413, 0, 0] := by
  rw [show D2M8K2.u2128 = KTree.node D2M8K2.t2132 (nat_lit 5008307) (nat_lit 2572300603) (nat_lit 32) D2M8K2.t2133 from rfl, totK_node, tot2132, tot2133]
  decide +kernel

theorem arows2129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2129 = true := by
  rw [show D2M8K2.u2129 = KTree.node D2M8K2.t2134 (nat_lit 5011573) (nat_lit 1085468842) (nat_lit 0) D2M8K2.t2135 from rfl, allE_node, rows2134, irow2129, rows2135]
  all_goals rfl

theorem atot2129 : totK PD2M8K2 D2M8K2.u2129 = [0, 0, 392840740912, 958214442130, 405385612822, 19936045428, 0, 0] := by
  rw [show D2M8K2.u2129 = KTree.node D2M8K2.t2134 (nat_lit 5011573) (nat_lit 1085468842) (nat_lit 0) D2M8K2.t2135 from rfl, totK_node, tot2134, tot2135]
  decide +kernel

theorem arows2132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2132 = true := by
  rw [show D2M8K2.u2132 = KTree.node D2M8K2.t2136 (nat_lit 5014872) (nat_lit 3585373603) (nat_lit 0) D2M8K2.t2137 from rfl, allE_node, rows2136, irow2132, rows2137]
  all_goals rfl

theorem atot2132 : totK PD2M8K2 D2M8K2.u2132 = [0, 0, 363211191551, 948718648238, 442534508922, 21643223360, 0, 0] := by
  rw [show D2M8K2.u2132 = KTree.node D2M8K2.t2136 (nat_lit 5014872) (nat_lit 3585373603) (nat_lit 0) D2M8K2.t2137 from rfl, totK_node, tot2136, tot2137]
  decide +kernel

theorem arows2133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2133 = true := by
  rw [show D2M8K2.u2133 = KTree.node D2M8K2.t2138 (nat_lit 5022124) (nat_lit 3821340757) (nat_lit 0) D2M8K2.t2139 from rfl, allE_node, rows2138, irow2133, rows2139]
  all_goals rfl

theorem atot2133 : totK PD2M8K2 D2M8K2.u2133 = [0, 268027470166, 755543503417, 614146330936, 168737217523, 13468148062, 0, 0] := by
  rw [show D2M8K2.u2133 = KTree.node D2M8K2.t2138 (nat_lit 5022124) (nat_lit 3821340757) (nat_lit 0) D2M8K2.t2139 from rfl, totK_node, tot2138, tot2139]
  decide +kernel

theorem arows2135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2135 = true := by
  rw [show D2M8K2.u2135 = KTree.node D2M8K2.t2140 (nat_lit 5023652) (nat_lit 3305503786) (nat_lit 0) D2M8K2.t2141 from rfl, allE_node, rows2140, irow2135, rows2141]
  all_goals rfl

theorem atot2135 : totK PD2M8K2 D2M8K2.u2135 = [0, 162118832972, 633412716032, 718153317160, 285170496965, 25373788367, 0, 0] := by
  rw [show D2M8K2.u2135 = KTree.node D2M8K2.t2140 (nat_lit 5023652) (nat_lit 3305503786) (nat_lit 0) D2M8K2.t2141 from rfl, totK_node, tot2140, tot2141]
  decide +kernel

theorem arows2136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2136 = true := by
  rw [show D2M8K2.u2136 = KTree.node D2M8K2.t2142 (nat_lit 5024866) (nat_lit 4194847968) (nat_lit 0) D2M8K2.t2143 from rfl, allE_node, rows2142, irow2136, rows2143]
  all_goals rfl

theorem atot2136 : totK PD2M8K2 D2M8K2.u2136 = [0, 156164577673, 583483952496, 757117113559, 301404901138, 12235609738, 0, 0] := by
  rw [show D2M8K2.u2136 = KTree.node D2M8K2.t2142 (nat_lit 5024866) (nat_lit 4194847968) (nat_lit 0) D2M8K2.t2143 from rfl, totK_node, tot2142, tot2143]
  decide +kernel

theorem arows2141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2141 = true := by
  rw [show D2M8K2.u2141 = KTree.node D2M8K2.t2144 (nat_lit 5026400) (nat_lit 3748967494) (nat_lit 0) D2M8K2.t2145 from rfl, allE_node, rows2144, irow2141, rows2145]
  all_goals rfl

theorem atot2141 : totK PD2M8K2 D2M8K2.u2141 = [0, 246240875018, 799937951123, 652055156741, 99757541025, 1163840124, 0, 0] := by
  rw [show D2M8K2.u2141 = KTree.node D2M8K2.t2144 (nat_lit 5026400) (nat_lit 3748967494) (nat_lit 0) D2M8K2.t2145 from rfl, totK_node, tot2144, tot2145]
  decide +kernel

theorem arows2142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2142 = true := by
  rw [show D2M8K2.u2142 = KTree.node D2M8K2.t2146 (nat_lit 5028197) (nat_lit 1991531182) (nat_lit 512) D2M8K2.t2147 from rfl, allE_node, rows2146, irow2142, rows2147]
  all_goals rfl

theorem atot2142 : totK PD2M8K2 D2M8K2.u2142 = [0, 156251266633, 637776835166, 752978715813, 227551155586, 11873025674, 0, 0] := by
  rw [show D2M8K2.u2142 = KTree.node D2M8K2.t2146 (nat_lit 5028197) (nat_lit 1991531182) (nat_lit 512) D2M8K2.t2147 from rfl, totK_node, tot2146, tot2147]
  decide +kernel

theorem arows2144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2144 = true := by
  rw [show D2M8K2.u2144 = KTree.node D2M8K2.t2148 (nat_lit 5029875) (nat_lit 2986295984) (nat_lit 0) D2M8K2.t2149 from rfl, allE_node, rows2148, irow2144, rows2149]
  all_goals rfl

theorem atot2144 : totK PD2M8K2 D2M8K2.u2144 = [0, 246404340763, 792595403462, 654123454365, 103517158663, 1197396724, 0, 0] := by
  rw [show D2M8K2.u2144 = KTree.node D2M8K2.t2148 (nat_lit 5029875) (nat_lit 2986295984) (nat_lit 0) D2M8K2.t2149 from rfl, totK_node, tot2148, tot2149]
  decide +kernel

theorem arows2145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2145 = true := by
  rw [show D2M8K2.u2145 = KTree.node D2M8K2.t2150 (nat_lit 5031656) (nat_lit 1970254619) (nat_lit 0) D2M8K2.t2151 from rfl, allE_node, rows2150, irow2145, rows2151]
  all_goals rfl

theorem atot2145 : totK PD2M8K2 D2M8K2.u2145 = [0, 160540681199, 635122179182, 749983640947, 232867723305, 12040273252, 0, 0] := by
  rw [show D2M8K2.u2145 = KTree.node D2M8K2.t2150 (nat_lit 5031656) (nat_lit 1970254619) (nat_lit 0) D2M8K2.t2151 from rfl, totK_node, tot2150, tot2151]
  decide +kernel

theorem arows2148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2148 = true := by
  rw [show D2M8K2.u2148 = KTree.node D2M8K2.t2152 (nat_lit 5033044) (nat_lit 2800338776) (nat_lit 0) D2M8K2.t2153 from rfl, allE_node, rows2152, irow2148, rows2153]
  all_goals rfl

theorem atot2148 : totK PD2M8K2 D2M8K2.u2148 = [0, 263369271482, 814404214508, 621377845797, 93947865215, 1096156699, 0, 0] := by
  rw [show D2M8K2.u2148 = KTree.node D2M8K2.t2152 (nat_lit 5033044) (nat_lit 2800338776) (nat_lit 0) D2M8K2.t2153 from rfl, totK_node, tot2152, tot2153]
  decide +kernel

theorem arows2149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2149 = true := by
  rw [show D2M8K2.u2149 = KTree.node D2M8K2.t2154 (nat_lit 5034989) (nat_lit 1711811678) (nat_lit 0) D2M8K2.t2155 from rfl, allE_node, rows2154, irow2149, rows2155]
  all_goals rfl

theorem atot2149 : totK PD2M8K2 D2M8K2.u2149 = [0, 0, 490972601748, 975731591996, 342456328311, 25957275831, 0, 0] := by
  rw [show D2M8K2.u2149 = KTree.node D2M8K2.t2154 (nat_lit 5034989) (nat_lit 1711811678) (nat_lit 0) D2M8K2.t2155 from rfl, totK_node, tot2154, tot2155]
  decide +kernel

theorem arows2151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2151 = true := by
  rw [show D2M8K2.u2151 = KTree.node D2M8K2.t2156 (nat_lit 5043697) (nat_lit 1340444844) (nat_lit 0) D2M8K2.t2157 from rfl, allE_node, rows2156, irow2151, rows2157]
  all_goals rfl

theorem atot2151 : totK PD2M8K2 D2M8K2.u2151 = [0, 0, 386679931752, 955142930364, 442412207064, 24263241754, 0, 0] := by
  rw [show D2M8K2.u2151 = KTree.node D2M8K2.t2156 (nat_lit 5043697) (nat_lit 1340444844) (nat_lit 0) D2M8K2.t2157 from rfl, totK_node, tot2156, tot2157]
  decide +kernel

theorem arows2152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2152 = true := by
  rw [show D2M8K2.u2152 = KTree.node D2M8K2.t2158 (nat_lit 5047002) (nat_lit 3720285362) (nat_lit 0) D2M8K2.t2159 from rfl, allE_node, rows2158, irow2152, rows2159]
  all_goals rfl

theorem atot2152 : totK PD2M8K2 D2M8K2.u2152 = [0, 0, 349992289206, 940379581036, 475283919040, 27520684072, 0, 0] := by
  rw [show D2M8K2.u2152 = KTree.node D2M8K2.t2158 (nat_lit 5047002) (nat_lit 3720285362) (nat_lit 0) D2M8K2.t2159 from rfl, totK_node, tot2158, tot2159]
  decide +kernel

theorem arows2156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2156 = true := by
  rw [show D2M8K2.u2156 = KTree.node D2M8K2.t2160 (nat_lit 5050388) (nat_lit 3258327459) (nat_lit 0) D2M8K2.t2161 from rfl, allE_node, rows2160, irow2156, rows2161]
  all_goals rfl

theorem atot2156 : totK PD2M8K2 D2M8K2.u2156 = [0, 0, 385189083395, 948115107826, 454169709856, 26445070431, 0, 0] := by
  rw [show D2M8K2.u2156 = KTree.node D2M8K2.t2160 (nat_lit 5050388) (nat_lit 3258327459) (nat_lit 0) D2M8K2.t2161 from rfl, totK_node, tot2160, tot2161]
  decide +kernel

theorem arows2157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2157 = true := by
  rw [show D2M8K2.u2157 = KTree.node D2M8K2.t2162 (nat_lit 5053426) (nat_lit 3667930186) (nat_lit 0) D2M8K2.t2163 from rfl, allE_node, rows2162, irow2157, rows2163]
  all_goals rfl

theorem atot2157 : totK PD2M8K2 D2M8K2.u2157 = [0, 0, 352391385769, 920425603829, 479703080502, 34347731608, 0, 0] := by
  rw [show D2M8K2.u2157 = KTree.node D2M8K2.t2162 (nat_lit 5053426) (nat_lit 3667930186) (nat_lit 0) D2M8K2.t2163 from rfl, totK_node, tot2162, tot2163]
  decide +kernel

theorem arows2159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2159 = true := by
  rw [show D2M8K2.u2159 = KTree.node D2M8K2.t2164 (nat_lit 5055391) (nat_lit 2343952376) (nat_lit 0) D2M8K2.t2165 from rfl, allE_node, rows2164, irow2159, rows2165]
  all_goals rfl

theorem atot2159 : totK PD2M8K2 D2M8K2.u2159 = [0, 126877611947, 281934289431, 545710793883, 703168107734, 129444096224, 1415142070, 0] := by
  rw [show D2M8K2.u2159 = KTree.node D2M8K2.t2164 (nat_lit 5055391) (nat_lit 2343952376) (nat_lit 0) D2M8K2.t2165 from rfl, totK_node, tot2164, tot2165]
  decide +kernel

theorem arows2160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2160 = true := by
  rw [show D2M8K2.u2160 = KTree.node D2M8K2.t2166 (nat_lit 5060838) (nat_lit 3686030142) (nat_lit 0) D2M8K2.t2167 from rfl, allE_node, rows2166, irow2160, rows2167]
  all_goals rfl

theorem atot2160 : totK PD2M8K2 D2M8K2.u2160 = [0, 279223774694, 849370273918, 580219091508, 62898061331, 0, 0, 0] := by
  rw [show D2M8K2.u2160 = KTree.node D2M8K2.t2166 (nat_lit 5060838) (nat_lit 3686030142) (nat_lit 0) D2M8K2.t2167 from rfl, totK_node, tot2166, tot2167]
  decide +kernel

theorem arows2163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2163 = true := by
  rw [show D2M8K2.u2163 = KTree.node D2M8K2.t2168 (nat_lit 5062832) (nat_lit 1976180664) (nat_lit 0) D2M8K2.t2169 from rfl, allE_node, rows2168, irow2163, rows2169]
  all_goals rfl

theorem atot2163 : totK PD2M8K2 D2M8K2.u2163 = [0, 179491426632, 728121055739, 781538074126, 130614105100, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2163 = KTree.node D2M8K2.t2168 (nat_lit 5062832) (nat_lit 1976180664) (nat_lit 0) D2M8K2.t2169 from rfl, totK_node, tot2168, tot2169]
  decide +kernel

theorem arows2164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2164 = true := by
  rw [show D2M8K2.u2164 = KTree.node D2M8K2.t2170 (nat_lit 5064530) (nat_lit 4049472801) (nat_lit 0) D2M8K2.t2171 from rfl, allE_node, rows2170, irow2164, rows2171]
  all_goals rfl

theorem atot2164 : totK PD2M8K2 D2M8K2.u2164 = [0, 206905526662, 721644676527, 653596855736, 205055488016, 19839770084, 0, 0] := by
  rw [show D2M8K2.u2164 = KTree.node D2M8K2.t2170 (nat_lit 5064530) (nat_lit 4049472801) (nat_lit 0) D2M8K2.t2171 from rfl, totK_node, tot2170, tot2171]
  decide +kernel

theorem arows2166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2166 = true := by
  rw [show D2M8K2.u2166 = KTree.node D2M8K2.t2172 (nat_lit 5066163) (nat_lit 2992475989) (nat_lit 0) D2M8K2.t2173 from rfl, allE_node, rows2172, irow2166, rows2173]
  all_goals rfl

theorem atot2166 : totK PD2M8K2 D2M8K2.u2166 = [0, 144535997026, 541492909403, 763845568204, 327446218610, 13648195412, 0, 0] := by
  rw [show D2M8K2.u2166 = KTree.node D2M8K2.t2172 (nat_lit 5066163) (nat_lit 2992475989) (nat_lit 0) D2M8K2.t2173 from rfl, totK_node, tot2172, tot2173]
  decide +kernel

theorem arows2167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2167 = true := by
  rw [show D2M8K2.u2167 = KTree.node D2M8K2.t2174 (nat_lit 5067704) (nat_lit 3813067118) (nat_lit 0) D2M8K2.t2175 from rfl, allE_node, rows2174, irow2167, rows2175]
  all_goals rfl

theorem atot2167 : totK PD2M8K2 D2M8K2.u2167 = [0, 293259044206, 879103588185, 586020471799, 53752620762, 0, 0, 0] := by
  rw [show D2M8K2.u2167 = KTree.node D2M8K2.t2174 (nat_lit 5067704) (nat_lit 3813067118) (nat_lit 0) D2M8K2.t2175 from rfl, totK_node, tot2174, tot2175]
  decide +kernel

theorem arows2174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2174 = true := by
  rw [show D2M8K2.u2174 = KTree.node D2M8K2.t2176 (nat_lit 5069386) (nat_lit 2580980868) (nat_lit 0) D2M8K2.t2177 from rfl, allE_node, rows2176, irow2174, rows2177]
  all_goals rfl

theorem atot2174 : totK PD2M8K2 D2M8K2.u2174 = [0, 84547450418, 525288682938, 872102688249, 282777125312, 13049727234, 0, 0] := by
  rw [show D2M8K2.u2174 = KTree.node D2M8K2.t2176 (nat_lit 5069386) (nat_lit 2580980868) (nat_lit 0) D2M8K2.t2177 from rfl, totK_node, tot2176, tot2177]
  decide +kernel

theorem arows2175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2175 = true := by
  rw [show D2M8K2.u2175 = KTree.node D2M8K2.t2178 (nat_lit 5074180) (nat_lit 4044005835) (nat_lit 0) D2M8K2.t2179 from rfl, allE_node, rows2178, irow2175, rows2179]
  all_goals rfl

theorem atot2175 : totK PD2M8K2 D2M8K2.u2175 = [0, 337372767861, 914667463699, 509173027142, 40423879950, 0, 0, 0] := by
  rw [show D2M8K2.u2175 = KTree.node D2M8K2.t2178 (nat_lit 5074180) (nat_lit 4044005835) (nat_lit 0) D2M8K2.t2179 from rfl, totK_node, tot2178, tot2179]
  decide +kernel

theorem arows2177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2177 = true := by
  rw [show D2M8K2.u2177 = KTree.node D2M8K2.t2180 (nat_lit 5076033) (nat_lit 1825578435) (nat_lit 0) D2M8K2.t2181 from rfl, allE_node, rows2180, irow2177, rows2181]
  all_goals rfl

theorem atot2177 : totK PD2M8K2 D2M8K2.u2177 = [0, 82236245000, 614204230132, 880342716903, 204422686509, 4980514959, 0, 0] := by
  rw [show D2M8K2.u2177 = KTree.node D2M8K2.t2180 (nat_lit 5076033) (nat_lit 1825578435) (nat_lit 0) D2M8K2.t2181 from rfl, totK_node, tot2180, tot2181]
  decide +kernel

theorem arows2178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2178 = true := by
  rw [show D2M8K2.u2178 = KTree.node D2M8K2.t2182 (nat_lit 5078355) (nat_lit 3631486303) (nat_lit 0) D2M8K2.t2183 from rfl, allE_node, rows2182, irow2178, rows2183]
  all_goals rfl

theorem atot2178 : totK PD2M8K2 D2M8K2.u2178 = [0, 246887870859, 805697952203, 653678964573, 111820933307, 1268739303, 0, 0] := by
  rw [show D2M8K2.u2178 = KTree.node D2M8K2.t2182 (nat_lit 5078355) (nat_lit 3631486303) (nat_lit 0) D2M8K2.t2183 from rfl, totK_node, tot2182, tot2183]
  decide +kernel

theorem arows2181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2181 = true := by
  rw [show D2M8K2.u2181 = KTree.node D2M8K2.t2184 (nat_lit 5080379) (nat_lit 2867322117) (nat_lit 0) D2M8K2.t2185 from rfl, allE_node, rows2184, irow2181, rows2185]
  all_goals rfl

theorem atot2181 : totK PD2M8K2 D2M8K2.u2181 = [0, 0, 398078835250, 954671921809, 405160570196, 22521706927, 0, 0] := by
  rw [show D2M8K2.u2181 = KTree.node D2M8K2.t2184 (nat_lit 5080379) (nat_lit 2867322117) (nat_lit 0) D2M8K2.t2185 from rfl, totK_node, tot2184, tot2185]
  decide +kernel

theorem arows2182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2182 = true := by
  rw [show D2M8K2.u2182 = KTree.node D2M8K2.t2186 (nat_lit 5081965) (nat_lit 1054338249) (nat_lit 0) D2M8K2.t2187 from rfl, allE_node, rows2186, irow2182, rows2187]
  all_goals rfl

theorem atot2182 : totK PD2M8K2 D2M8K2.u2182 = [0, 0, 177710776945, 773946064755, 673215026035, 91305666422, 1206465782, 0] := by
  rw [show D2M8K2.u2182 = KTree.node D2M8K2.t2186 (nat_lit 5081965) (nat_lit 1054338249) (nat_lit 0) D2M8K2.t2187 from rfl, totK_node, tot2186, tot2187]
  decide +kernel

theorem arows2184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2184 = true := by
  rw [show D2M8K2.u2184 = KTree.node D2M8K2.t2188 (nat_lit 5084405) (nat_lit 2401362874) (nat_lit 0) D2M8K2.t2189 from rfl, allE_node, rows2188, irow2184, rows2189]
  all_goals rfl

theorem atot2184 : totK PD2M8K2 D2M8K2.u2184 = [0, 0, 318411232014, 920005319504, 525115402819, 37744195570, 0, 0] := by
  rw [show D2M8K2.u2184 = KTree.node D2M8K2.t2188 (nat_lit 5084405) (nat_lit 2401362874) (nat_lit 0) D2M8K2.t2189 from rfl, totK_node, tot2188, tot2189]
  decide +kernel

theorem arows2185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2185 = true := by
  rw [show D2M8K2.u2185 = KTree.node D2M8K2.t2190 (nat_lit 5087611) (nat_lit 979035802) (nat_lit 128) D2M8K2.t2191 from rfl, allE_node, rows2190, irow2185, rows2191]
  all_goals rfl

theorem atot2185 : totK PD2M8K2 D2M8K2.u2185 = [0, 0, 386315078253, 945132780922, 448380331789, 26156695975, 0, 0] := by
  rw [show D2M8K2.u2185 = KTree.node D2M8K2.t2190 (nat_lit 5087611) (nat_lit 979035802) (nat_lit 128) D2M8K2.t2191 from rfl, totK_node, tot2190, tot2191]
  decide +kernel

theorem arows2189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2189 = true := by
  rw [show D2M8K2.u2189 = KTree.node D2M8K2.t2192 (nat_lit 5089096) (nat_lit 3635322940) (nat_lit 0) D2M8K2.t2193 from rfl, allE_node, rows2192, irow2189, rows2193]
  all_goals rfl

theorem atot2189 : totK PD2M8K2 D2M8K2.u2189 = [0, 0, 115769868190, 658128208665, 763747515091, 189986206741, 9579374723, 0] := by
  rw [show D2M8K2.u2189 = KTree.node D2M8K2.t2192 (nat_lit 5089096) (nat_lit 3635322940) (nat_lit 0) D2M8K2.t2193 from rfl, totK_node, tot2192, tot2193]
  decide +kernel

theorem arows2190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2190 = true := by
  rw [show D2M8K2.u2190 = KTree.node D2M8K2.t2194 (nat_lit 5094488) (nat_lit 3748468480) (nat_lit 0) D2M8K2.t2195 from rfl, allE_node, rows2194, irow2190, rows2195]
  all_goals rfl

theorem atot2190 : totK PD2M8K2 D2M8K2.u2190 = [0, 0, 294998843302, 822279755144, 533479931528, 94141364971, 3436822651, 0] := by
  rw [show D2M8K2.u2190 = KTree.node D2M8K2.t2194 (nat_lit 5094488) (nat_lit 3748468480) (nat_lit 0) D2M8K2.t2195 from rfl, totK_node, tot2194, tot2195]
  decide +kernel

theorem arows2192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2192 = true := by
  rw [show D2M8K2.u2192 = KTree.node D2M8K2.t2196 (nat_lit 5096022) (nat_lit 2932337415) (nat_lit 0) D2M8K2.t2197 from rfl, allE_node, rows2196, irow2192, rows2197]
  all_goals rfl

theorem atot2192 : totK PD2M8K2 D2M8K2.u2192 = [0, 0, 120572411280, 755574640581, 748063273589, 97846623295, 1021600638, 0] := by
  rw [show D2M8K2.u2192 = KTree.node D2M8K2.t2196 (nat_lit 5096022) (nat_lit 2932337415) (nat_lit 0) D2M8K2.t2197 from rfl, totK_node, tot2196, tot2197]
  decide +kernel

theorem arows2193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2193 = true := by
  rw [show D2M8K2.u2193 = KTree.node D2M8K2.t2198 (nat_lit 5098183) (nat_lit 1767557429) (nat_lit 0) D2M8K2.t2199 from rfl, allE_node, rows2198, irow2193, rows2199]
  all_goals rfl

theorem atot2193 : totK PD2M8K2 D2M8K2.u2193 = [0, 28547172183, 361688081685, 836159243883, 481416243570, 75957262203, 3552795014, 0] := by
  rw [show D2M8K2.u2193 = KTree.node D2M8K2.t2198 (nat_lit 5098183) (nat_lit 1767557429) (nat_lit 0) D2M8K2.t2199 from rfl, totK_node, tot2198, tot2199]
  decide +kernel

theorem arows2196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2196 = true := by
  rw [show D2M8K2.u2196 = KTree.node D2M8K2.t2200 (nat_lit 5102047) (nat_lit 2358555796) (nat_lit 0) D2M8K2.t2201 from rfl, allE_node, rows2200, irow2196, rows2201]
  all_goals rfl

theorem atot2196 : totK PD2M8K2 D2M8K2.u2196 = [0, 377896082256, 949147845462, 437765387635, 23644192949, 0, 0, 0] := by
  rw [show D2M8K2.u2196 = KTree.node D2M8K2.t2200 (nat_lit 5102047) (nat_lit 2358555796) (nat_lit 0) D2M8K2.t2201 from rfl, totK_node, tot2200, tot2201]
  decide +kernel

theorem arows2197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2197 = true := by
  rw [show D2M8K2.u2197 = KTree.node D2M8K2.t2202 (nat_lit 5103753) (nat_lit 1894752111) (nat_lit 0) D2M8K2.t2203 from rfl, allE_node, rows2202, irow2197, rows2203]
  all_goals rfl

theorem atot2197 : totK PD2M8K2 D2M8K2.u2197 = [0, 90954164743, 661830153578, 883690210165, 164105918046, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2197 = KTree.node D2M8K2.t2202 (nat_lit 5103753) (nat_lit 1894752111) (nat_lit 0) D2M8K2.t2203 from rfl, totK_node, tot2202, tot2203]
  decide +kernel

theorem arows2199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2199 = true := by
  rw [show D2M8K2.u2199 = KTree.node D2M8K2.t2204 (nat_lit 5105702) (nat_lit 4150076328) (nat_lit 0) D2M8K2.t2205 from rfl, allE_node, rows2204, irow2199, rows2205]
  all_goals rfl

theorem atot2199 : totK PD2M8K2 D2M8K2.u2199 = [0, 295541891143, 873328088483, 587523471360, 60162729682, 0, 0, 0] := by
  rw [show D2M8K2.u2199 = KTree.node D2M8K2.t2204 (nat_lit 5105702) (nat_lit 4150076328) (nat_lit 0) D2M8K2.t2205 from rfl, totK_node, tot2204, tot2205]
  decide +kernel

theorem arows2200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2200 = true := by
  rw [show D2M8K2.u2200 = KTree.node D2M8K2.t2206 (nat_lit 5107342) (nat_lit 2987574754) (nat_lit 0) D2M8K2.t2207 from rfl, allE_node, rows2206, irow2200, rows2207]
  all_goals rfl

theorem atot2200 : totK PD2M8K2 D2M8K2.u2200 = [0, 50460163317, 362938647577, 867325759293, 479240631960, 33457465162, 0, 0] := by
  rw [show D2M8K2.u2200 = KTree.node D2M8K2.t2206 (nat_lit 5107342) (nat_lit 2987574754) (nat_lit 0) D2M8K2.t2207 from rfl, totK_node, tot2206, tot2207]
  decide +kernel

theorem arows2205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2205 = true := by
  rw [show D2M8K2.u2205 = KTree.node D2M8K2.t2208 (nat_lit 5112379) (nat_lit 2243241104) (nat_lit 0) D2M8K2.t2209 from rfl, allE_node, rows2208, irow2205, rows2209]
  all_goals rfl

theorem atot2205 : totK PD2M8K2 D2M8K2.u2205 = [0, 368282039330, 943767261859, 478960873728, 34967699849, 0, 0, 0] := by
  rw [show D2M8K2.u2205 = KTree.node D2M8K2.t2208 (nat_lit 5112379) (nat_lit 2243241104) (nat_lit 0) D2M8K2.t2209 from rfl, totK_node, tot2208, tot2209]
  decide +kernel

theorem arows2206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2206 = true := by
  rw [show D2M8K2.u2206 = KTree.node D2M8K2.t2210 (nat_lit 5114027) (nat_lit 2754748900) (nat_lit 0) D2M8K2.t2211 from rfl, allE_node, rows2210, irow2206, rows2211]
  all_goals rfl

theorem atot2206 : totK PD2M8K2 D2M8K2.u2206 = [0, 19233732584, 499284635599, 945869479880, 295297088149, 13250685261, 0, 0] := by
  rw [show D2M8K2.u2206 = KTree.node D2M8K2.t2210 (nat_lit 5114027) (nat_lit 2754748900) (nat_lit 0) D2M8K2.t2211 from rfl, totK_node, tot2210, tot2211]
  decide +kernel

theorem arows2208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2208 = true := by
  rw [show D2M8K2.u2208 = KTree.node D2M8K2.t2212 (nat_lit 5115391) (nat_lit 2412280812) (nat_lit 0) D2M8K2.t2213 from rfl, allE_node, rows2212, irow2208, rows2213]
  all_goals rfl

theorem atot2208 : totK PD2M8K2 D2M8K2.u2208 = [0, 330235994698, 878336762582, 535153956356, 56025395619, 0, 0, 0] := by
  rw [show D2M8K2.u2208 = KTree.node D2M8K2.t2212 (nat_lit 5115391) (nat_lit 2412280812) (nat_lit 0) D2M8K2.t2213 from rfl, totK_node, tot2212, tot2213]
  decide +kernel

theorem arows2209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2209 = true := by
  rw [show D2M8K2.u2209 = KTree.node D2M8K2.t2214 (nat_lit 5116958) (nat_lit 3880737765) (nat_lit 0) D2M8K2.t2215 from rfl, allE_node, rows2214, irow2209, rows2215]
  all_goals rfl

theorem atot2209 : totK PD2M8K2 D2M8K2.u2209 = [0, 91718010228, 664732837194, 872502515411, 165532119952, 2165917952, 0, 0] := by
  rw [show D2M8K2.u2209 = KTree.node D2M8K2.t2214 (nat_lit 5116958) (nat_lit 3880737765) (nat_lit 0) D2M8K2.t2215 from rfl, totK_node, tot2214, tot2215]
  decide +kernel

theorem arows2212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2212 = true := by
  rw [show D2M8K2.u2212 = KTree.node D2M8K2.t2216 (nat_lit 5119247) (nat_lit 2145845470) (nat_lit 0) D2M8K2.t2217 from rfl, allE_node, rows2216, irow2212, rows2217]
  all_goals rfl

theorem atot2212 : totK PD2M8K2 D2M8K2.u2212 = [0, 329265630786, 895097079038, 530619528286, 70206764883, 2814597007, 0, 0] := by
  rw [show D2M8K2.u2212 = KTree.node D2M8K2.t2216 (nat_lit 5119247) (nat_lit 2145845470) (nat_lit 0) D2M8K2.t2217 from rfl, totK_node, tot2216, tot2217]
  decide +kernel

theorem arows2213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2213 = true := by
  rw [show D2M8K2.u2213 = KTree.node D2M8K2.t2218 (nat_lit 5121535) (nat_lit 2275272199) (nat_lit 0) D2M8K2.t2219 from rfl, allE_node, rows2218, irow2213, rows2219]
  all_goals rfl

theorem atot2213 : totK PD2M8K2 D2M8K2.u2213 = [0, 0, 419543637654, 970588540407, 372727188646, 15385635356, 0, 0] := by
  rw [show D2M8K2.u2213 = KTree.node D2M8K2.t2218 (nat_lit 5121535) (nat_lit 2275272199) (nat_lit 0) D2M8K2.t2219 from rfl, totK_node, tot2218, tot2219]
  decide +kernel

theorem arows2215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2215 = true := by
  rw [show D2M8K2.u2215 = KTree.node D2M8K2.t2220 (nat_lit 5123110) (nat_lit 1227699439) (nat_lit 0) D2M8K2.t2221 from rfl, allE_node, rows2220, irow2215, rows2221]
  all_goals rfl

theorem atot2215 : totK PD2M8K2 D2M8K2.u2215 = [0, 0, 265871566050, 826370970692, 564978329821, 77301978599, 1239866073, 0] := by
  rw [show D2M8K2.u2215 = KTree.node D2M8K2.t2220 (nat_lit 5123110) (nat_lit 1227699439) (nat_lit 0) D2M8K2.t2221 from rfl, totK_node, tot2220, tot2221]
  decide +kernel

theorem arows2216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2216 = true := by
  rw [show D2M8K2.u2216 = KTree.node D2M8K2.t2222 (nat_lit 5125604) (nat_lit 3225891353) (nat_lit 0) D2M8K2.t2223 from rfl, allE_node, rows2222, irow2216, rows2223]
  all_goals rfl

theorem atot2216 : totK PD2M8K2 D2M8K2.u2216 = [0, 0, 232872255416, 854708098804, 651230546122, 56093052288, 0, 0] := by
  rw [show D2M8K2.u2216 = KTree.node D2M8K2.t2222 (nat_lit 5125604) (nat_lit 3225891353) (nat_lit 0) D2M8K2.t2223 from rfl, totK_node, tot2222, tot2223]
  decide +kernel

theorem arows2220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2220 = true := by
  rw [show D2M8K2.u2220 = KTree.node D2M8K2.t2224 (nat_lit 5132218) (nat_lit 3359960666) (nat_lit 0) D2M8K2.t2225 from rfl, allE_node, rows2224, irow2220, rows2225]
  all_goals rfl

theorem atot2220 : totK PD2M8K2 D2M8K2.u2220 = [0, 0, 380896928937, 955498338199, 447102197228, 25393821930, 0, 0] := by
  rw [show D2M8K2.u2220 = KTree.node D2M8K2.t2224 (nat_lit 5132218) (nat_lit 3359960666) (nat_lit 0) D2M8K2.t2225 from rfl, totK_node, tot2224, tot2225]
  decide +kernel

theorem arows2221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2221 = true := by
  rw [show D2M8K2.u2221 = KTree.node D2M8K2.t2226 (nat_lit 5133693) (nat_lit 1405689795) (nat_lit 0) D2M8K2.t2227 from rfl, allE_node, rows2226, irow2221, rows2227]
  all_goals rfl

theorem atot2221 : totK PD2M8K2 D2M8K2.u2221 = [0, 0, 207014733184, 798727566201, 662735790239, 99307273539, 1171084559, 0] := by
  rw [show D2M8K2.u2221 = KTree.node D2M8K2.t2226 (nat_lit 5133693) (nat_lit 1405689795) (nat_lit 0) D2M8K2.t2227 from rfl, totK_node, tot2226, tot2227]
  decide +kernel

theorem arows2223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2223 = true := by
  rw [show D2M8K2.u2223 = KTree.node D2M8K2.t2228 (nat_lit 5135616) (nat_lit 3756869540) (nat_lit 0) D2M8K2.t2229 from rfl, allE_node, rows2228, irow2223, rows2229]
  all_goals rfl

theorem atot2223 : totK PD2M8K2 D2M8K2.u2223 = [0, 0, 203097835338, 682195982016, 652790638904, 187358275775, 11934365838, 0] := by
  rw [show D2M8K2.u2223 = KTree.node D2M8K2.t2228 (nat_lit 5135616) (nat_lit 3756869540) (nat_lit 0) D2M8K2.t2229 from rfl, totK_node, tot2228, tot2229]
  decide +kernel

theorem arows2224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2224 = true := by
  rw [show D2M8K2.u2224 = KTree.node D2M8K2.t2230 (nat_lit 5136862) (nat_lit 3073242423) (nat_lit 0) D2M8K2.t2231 from rfl, allE_node, rows2230, irow2224, rows2231]
  all_goals rfl

theorem atot2224 : totK PD2M8K2 D2M8K2.u2224 = [0, 0, 216566888833, 821443989802, 629272066390, 76953606688, 1053411165, 0] := by
  rw [show D2M8K2.u2224 = KTree.node D2M8K2.t2230 (nat_lit 5136862) (nat_lit 3073242423) (nat_lit 0) D2M8K2.t2231 from rfl, totK_node, tot2230, tot2231]
  decide +kernel

theorem arows2227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2227 = true := by
  rw [show D2M8K2.u2227 = KTree.node D2M8K2.t2232 (nat_lit 5139222) (nat_lit 3671641796) (nat_lit 0) D2M8K2.t2233 from rfl, allE_node, rows2232, irow2227, rows2233]
  all_goals rfl

theorem atot2227 : totK PD2M8K2 D2M8K2.u2227 = [0, 0, 250912155901, 790828473713, 625274636692, 104578664554, 3667207281, 0] := by
  rw [show D2M8K2.u2227 = KTree.node D2M8K2.t2232 (nat_lit 5139222) (nat_lit 3671641796) (nat_lit 0) D2M8K2.t2233 from rfl, totK_node, tot2232, tot2233]
  decide +kernel

theorem arows2228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2228 = true := by
  rw [show D2M8K2.u2228 = KTree.node D2M8K2.t2234 (nat_lit 5143144) (nat_lit 3843936647) (nat_lit 0) D2M8K2.t2235 from rfl, allE_node, rows2234, irow2228, rows2235]
  all_goals rfl

theorem atot2228 : totK PD2M8K2 D2M8K2.u2228 = [0, 306287828847, 801652677965, 547804000051, 139419824279, 9183461301, 0, 0] := by
  rw [show D2M8K2.u2228 = KTree.node D2M8K2.t2234 (nat_lit 5143144) (nat_lit 3843936647) (nat_lit 0) D2M8K2.t2235 from rfl, totK_node, tot2234, tot2235]
  decide +kernel

theorem arows2230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2230 = true := by
  rw [show D2M8K2.u2230 = KTree.node D2M8K2.t2236 (nat_lit 5144388) (nat_lit 3286109597) (nat_lit 0) D2M8K2.t2237 from rfl, allE_node, rows2236, irow2230, rows2237]
  all_goals rfl

theorem atot2230 : totK PD2M8K2 D2M8K2.u2230 = [0, 110938415940, 699248738326, 831883597847, 143037321080, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2230 = KTree.node D2M8K2.t2236 (nat_lit 5144388) (nat_lit 3286109597) (nat_lit 0) D2M8K2.t2237 from rfl, totK_node, tot2236, tot2237]
  decide +kernel

theorem arows2231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2231 = true := by
  rw [show D2M8K2.u2231 = KTree.node D2M8K2.t2238 (nat_lit 5146704) (nat_lit 3526147598) (nat_lit 0) D2M8K2.t2239 from rfl, allE_node, rows2238, irow2231, rows2239]
  all_goals rfl

theorem atot2231 : totK PD2M8K2 D2M8K2.u2231 = [0, 352698323715, 879867944175, 525987666455, 52790153773, 0, 0, 0] := by
  rw [show D2M8K2.u2231 = KTree.node D2M8K2.t2238 (nat_lit 5146704) (nat_lit 3526147598) (nat_lit 0) D2M8K2.t2239 from rfl, totK_node, tot2238, tot2239]
  decide +kernel

theorem arows2237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2237 = true := by
  rw [show D2M8K2.u2237 = KTree.node D2M8K2.t2240 (nat_lit 5148280) (nat_lit 3386255684) (nat_lit 0) D2M8K2.t2241 from rfl, allE_node, rows2240, irow2237, rows2241]
  all_goals rfl

theorem atot2237 : totK PD2M8K2 D2M8K2.u2237 = [0, 52730177238, 507442686763, 834966906298, 364557661047, 26955191807, 0, 0] := by
  rw [show D2M8K2.u2237 = KTree.node D2M8K2.t2240 (nat_lit 5148280) (nat_lit 3386255684) (nat_lit 0) D2M8K2.t2241 from rfl, totK_node, tot2240, tot2241]
  decide +kernel

theorem arows2238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2238 = true := by
  rw [show D2M8K2.u2238 = KTree.node D2M8K2.t2242 (nat_lit 5149637) (nat_lit 2343662941) (nat_lit 0) D2M8K2.t2243 from rfl, allE_node, rows2242, irow2238, rows2243]
  all_goals rfl

theorem atot2238 : totK PD2M8K2 D2M8K2.u2238 = [0, 262544482160, 725687736591, 619867926742, 180214907773, 3782038083, 0, 0] := by
  rw [show D2M8K2.u2238 = KTree.node D2M8K2.t2242 (nat_lit 5149637) (nat_lit 2343662941) (nat_lit 0) D2M8K2.t2243 from rfl, totK_node, tot2242, tot2243]
  decide +kernel

theorem arows2240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2240 = true := by
  rw [show D2M8K2.u2240 = KTree.node D2M8K2.t2244 (nat_lit 5151172) (nat_lit 3793800199) (nat_lit 0) D2M8K2.t2245 from rfl, allE_node, rows2244, irow2240, rows2245]
  all_goals rfl

theorem atot2240 : totK PD2M8K2 D2M8K2.u2240 = [0, 155082416523, 708860356466, 764746319825, 148598678789, 2309606161, 0, 0] := by
  rw [show D2M8K2.u2240 = KTree.node D2M8K2.t2244 (nat_lit 5151172) (nat_lit 3793800199) (nat_lit 0) D2M8K2.t2245 from rfl, totK_node, tot2244, tot2245]
  decide +kernel

theorem arows2241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2241 = true := by
  rw [show D2M8K2.u2241 = KTree.node D2M8K2.t2246 (nat_lit 5153006) (nat_lit 3003675427) (nat_lit 0) D2M8K2.t2247 from rfl, allE_node, rows2246, irow2241, rows2247]
  all_goals rfl

theorem atot2241 : totK PD2M8K2 D2M8K2.u2241 = [0, 245042886548, 707910223087, 641547279224, 177117478536, 10740121073, 0, 0] := by
  rw [show D2M8K2.u2241 = KTree.node D2M8K2.t2246 (nat_lit 5153006) (nat_lit 3003675427) (nat_lit 0) D2M8K2.t2247 from rfl, totK_node, tot2246, tot2247]
  decide +kernel

theorem arows2244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2244 = true := by
  rw [show D2M8K2.u2244 = KTree.node D2M8K2.t2248 (nat_lit 5154502) (nat_lit 3186075066) (nat_lit 0) D2M8K2.t2249 from rfl, allE_node, rows2248, irow2244, rows2249]
  all_goals rfl

theorem atot2244 : totK PD2M8K2 D2M8K2.u2244 = [0, 172787991978, 746562510134, 739410050740, 126186006656, 1198073392, 0, 0] := by
  rw [show D2M8K2.u2244 = KTree.node D2M8K2.t2248 (nat_lit 5154502) (nat_lit 3186075066) (nat_lit 0) D2M8K2.t2249 from rfl, totK_node, tot2248, tot2249]
  decide +kernel

theorem arows2245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2245 = true := by
  rw [show D2M8K2.u2245 = KTree.node D2M8K2.t2250 (nat_lit 5156364) (nat_lit 3603536935) (nat_lit 0) D2M8K2.t2251 from rfl, allE_node, rows2250, irow2245, rows2251]
  all_goals rfl

theorem atot2245 : totK PD2M8K2 D2M8K2.u2245 = [0, 200724484069, 658319353698, 702616186881, 215386152349, 12052611869, 0, 0] := by
  rw [show D2M8K2.u2245 = KTree.node D2M8K2.t2250 (nat_lit 5156364) (nat_lit 3603536935) (nat_lit 0) D2M8K2.t2251 from rfl, totK_node, tot2250, tot2251]
  decide +kernel

theorem arows2247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2247 = true := by
  rw [show D2M8K2.u2247 = KTree.node D2M8K2.t2252 (nat_lit 5157547) (nat_lit 1802348857) (nat_lit 0) D2M8K2.t2253 from rfl, allE_node, rows2252, irow2247, rows2253]
  all_goals rfl

theorem atot2247 : totK PD2M8K2 D2M8K2.u2247 = [0, 243568868677, 816915277900, 661434889862, 96526332779, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2247 = KTree.node D2M8K2.t2252 (nat_lit 5157547) (nat_lit 1802348857) (nat_lit 0) D2M8K2.t2253 from rfl, totK_node, tot2252, tot2253]
  decide +kernel

theorem arows2248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2248 = true := by
  rw [show D2M8K2.u2248 = KTree.node D2M8K2.t2254 (nat_lit 5159484) (nat_lit 2935904622) (nat_lit 0) D2M8K2.t2255 from rfl, allE_node, rows2254, irow2248, rows2255]
  all_goals rfl

theorem atot2248 : totK PD2M8K2 D2M8K2.u2248 = [0, 0, 468692701033, 986980916690, 319200404657, 13624150839, 0, 0] := by
  rw [show D2M8K2.u2248 = KTree.node D2M8K2.t2254 (nat_lit 5159484) (nat_lit 2935904622) (nat_lit 0) D2M8K2.t2255 from rfl, totK_node, tot2254, tot2255]
  decide +kernel

theorem arows2252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2252 = true := by
  rw [show D2M8K2.u2252 = KTree.node D2M8K2.t2256 (nat_lit 5164783) (nat_lit 2408006233) (nat_lit 0) D2M8K2.t2257 from rfl, allE_node, rows2256, irow2252, rows2257]
  all_goals rfl

theorem atot2252 : totK PD2M8K2 D2M8K2.u2252 = [0, 0, 218147338580, 810794192884, 623565078902, 82304319916, 1138244013, 0] := by
  rw [show D2M8K2.u2252 = KTree.node D2M8K2.t2256 (nat_lit 5164783) (nat_lit 2408006233) (nat_lit 0) D2M8K2.t2257 from rfl, totK_node, tot2256, tot2257]
  decide +kernel

theorem arows2253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2253 = true := by
  rw [show D2M8K2.u2253 = KTree.node D2M8K2.t2258 (nat_lit 5167307) (nat_lit 1571062605) (nat_lit 0) D2M8K2.t2259 from rfl, allE_node, rows2258, irow2253, rows2259]
  all_goals rfl

theorem atot2253 : totK PD2M8K2 D2M8K2.u2253 = [0, 0, 296638277289, 885713764876, 548010681262, 48851795943, 0, 0] := by
  rw [show D2M8K2.u2253 = KTree.node D2M8K2.t2258 (nat_lit 5167307) (nat_lit 1571062605) (nat_lit 0) D2M8K2.t2259 from rfl, totK_node, tot2258, tot2259]
  decide +kernel

theorem arows2255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2255 = true := by
  rw [show D2M8K2.u2255 = KTree.node D2M8K2.t2260 (nat_lit 5170421) (nat_lit 2201928532) (nat_lit 0) D2M8K2.t2261 from rfl, allE_node, rows2260, irow2255, rows2261]
  all_goals rfl

theorem atot2255 : totK PD2M8K2 D2M8K2.u2255 = [0, 0, 369398948278, 964780577953, 430576259709, 20857897308, 0, 0] := by
  rw [show D2M8K2.u2255 = KTree.node D2M8K2.t2260 (nat_lit 5170421) (nat_lit 2201928532) (nat_lit 0) D2M8K2.t2261 from rfl, totK_node, tot2260, tot2261]
  decide +kernel

theorem arows2256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2256 = true := by
  rw [show D2M8K2.u2256 = KTree.node D2M8K2.t2262 (nat_lit 5173717) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t2263 from rfl, allE_node, rows2262, irow2256, rows2263]
  all_goals rfl

theorem atot2256 : totK PD2M8K2 D2M8K2.u2256 = [0, 0, 398349275495, 949747169323, 404911945691, 20186750109, 0, 0] := by
  rw [show D2M8K2.u2256 = KTree.node D2M8K2.t2262 (nat_lit 5173717) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t2263 from rfl, totK_node, tot2262, tot2263]
  decide +kernel

theorem arows2259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2259 = true := by
  rw [show D2M8K2.u2259 = KTree.node D2M8K2.t2264 (nat_lit 5175234) (nat_lit 2982729347) (nat_lit 0) D2M8K2.t2265 from rfl, allE_node, rows2264, irow2259, rows2265]
  all_goals rfl

theorem atot2259 : totK PD2M8K2 D2M8K2.u2259 = [0, 0, 345938783016, 930634977710, 465887433752, 30675856042, 0, 0] := by
  rw [show D2M8K2.u2259 = KTree.node D2M8K2.t2264 (nat_lit 5175234) (nat_lit 2982729347) (nat_lit 0) D2M8K2.t2265 from rfl, totK_node, tot2264, tot2265]
  decide +kernel

theorem arows2260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2260 = true := by
  rw [show D2M8K2.u2260 = KTree.node D2M8K2.t2266 (nat_lit 5178213) (nat_lit 1524177181) (nat_lit 0) D2M8K2.t2267 from rfl, allE_node, rows2266, irow2260, rows2267]
  all_goals rfl

theorem atot2260 : totK PD2M8K2 D2M8K2.u2260 = [0, 0, 267823874018, 819939454933, 588641340729, 84164644028, 1095107716, 0] := by
  rw [show D2M8K2.u2260 = KTree.node D2M8K2.t2266 (nat_lit 5178213) (nat_lit 1524177181) (nat_lit 0) D2M8K2.t2267 from rfl, totK_node, tot2266, tot2267]
  decide +kernel

theorem arows2262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2262 = true := by
  rw [show D2M8K2.u2262 = KTree.node D2M8K2.t2268 (nat_lit 5180185) (nat_lit 1300752059) (nat_lit 0) D2M8K2.t2269 from rfl, allE_node, rows2268, irow2262, rows2269]
  all_goals rfl

theorem atot2262 : totK PD2M8K2 D2M8K2.u2262 = [0, 179096909081, 451273943074, 504466747057, 516539566741, 126159599737, 3882006667, 0] := by
  rw [show D2M8K2.u2262 = KTree.node D2M8K2.t2268 (nat_lit 5180185) (nat_lit 1300752059) (nat_lit 0) D2M8K2.t2269 from rfl, totK_node, tot2268, tot2269]
  decide +kernel

theorem arows2263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2263 = true := by
  rw [show D2M8K2.u2263 = KTree.node D2M8K2.t2270 (nat_lit 5475779) (nat_lit 2889018113) (nat_lit 0) D2M8K2.t2271 from rfl, allE_node, rows2270, irow2263, rows2271]
  all_goals rfl

theorem atot2263 : totK PD2M8K2 D2M8K2.u2263 = [0, 258412757369, 805514150686, 636896112986, 105292739757, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2263 = KTree.node D2M8K2.t2270 (nat_lit 5475779) (nat_lit 2889018113) (nat_lit 0) D2M8K2.t2271 from rfl, totK_node, tot2270, tot2271]
  decide +kernel

theorem arows2268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2268 = true := by
  rw [show D2M8K2.u2268 = KTree.node D2M8K2.t2272 (nat_lit 5481286) (nat_lit 3754816840) (nat_lit 0) D2M8K2.t2273 from rfl, allE_node, rows2272, irow2268, rows2273]
  all_goals rfl

theorem atot2268 : totK PD2M8K2 D2M8K2.u2268 = [0, 239496958623, 805256693271, 694900532250, 83510484804, 0, 0, 0] := by
  rw [show D2M8K2.u2268 = KTree.node D2M8K2.t2272 (nat_lit 5481286) (nat_lit 3754816840) (nat_lit 0) D2M8K2.t2273 from rfl, totK_node, tot2272, tot2273]
  decide +kernel

theorem arows2269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2269 = true := by
  rw [show D2M8K2.u2269 = KTree.node D2M8K2.t2274 (nat_lit 5482818) (nat_lit 2839311633) (nat_lit 0) D2M8K2.t2275 from rfl, allE_node, rows2274, irow2269, rows2275]
  all_goals rfl

theorem atot2269 : totK PD2M8K2 D2M8K2.u2269 = [0, 173198750947, 750661137864, 736993222955, 122722575380, 1164319620, 0, 0] := by
  rw [show D2M8K2.u2269 = KTree.node D2M8K2.t2274 (nat_lit 5482818) (nat_lit 2839311633) (nat_lit 0) D2M8K2.t2275 from rfl, totK_node, tot2274, tot2275]
  decide +kernel

theorem arows2271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2271 = true := by
  rw [show D2M8K2.u2271 = KTree.node D2M8K2.t2276 (nat_lit 5484680) (nat_lit 3604243563) (nat_lit 0) D2M8K2.t2277 from rfl, allE_node, rows2276, irow2271, rows2277]
  all_goals rfl

theorem atot2271 : totK PD2M8K2 D2M8K2.u2271 = [0, 210578036420, 661450928799, 686677419680, 204235937958, 11885407614, 0, 0] := by
  rw [show D2M8K2.u2271 = KTree.node D2M8K2.t2276 (nat_lit 5484680) (nat_lit 3604243563) (nat_lit 0) D2M8K2.t2277 from rfl, totK_node, tot2276, tot2277]
  decide +kernel

theorem arows2272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2272 = true := by
  rw [show D2M8K2.u2272 = KTree.node D2M8K2.t2278 (nat_lit 5486237) (nat_lit 2094192553) (nat_lit 0) D2M8K2.t2279 from rfl, allE_node, rows2278, irow2272, rows2279]
  all_goals rfl

theorem atot2272 : totK PD2M8K2 D2M8K2.u2272 = [0, 202345926468, 767126582679, 699706808735, 116854799537, 1198073392, 0, 0] := by
  rw [show D2M8K2.u2272 = KTree.node D2M8K2.t2278 (nat_lit 5486237) (nat_lit 2094192553) (nat_lit 0) D2M8K2.t2279 from rfl, totK_node, tot2278, tot2279]
  decide +kernel

theorem arows2275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2275 = true := by
  rw [show D2M8K2.u2275 = KTree.node D2M8K2.t2280 (nat_lit 5487924) (nat_lit 3173569772) (nat_lit 0) D2M8K2.t2281 from rfl, allE_node, rows2280, irow2275, rows2281]
  all_goals rfl

theorem atot2275 : totK PD2M8K2 D2M8K2.u2275 = [0, 180616041277, 656928653908, 702031925272, 212027053146, 12052611869, 0, 0] := by
  rw [show D2M8K2.u2275 = KTree.node D2M8K2.t2280 (nat_lit 5487924) (nat_lit 3173569772) (nat_lit 0) D2M8K2.t2281 from rfl, totK_node, tot2280, tot2281]
  decide +kernel

theorem arows2276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2276 = true := by
  rw [show D2M8K2.u2276 = KTree.node D2M8K2.t2282 (nat_lit 5489925) (nat_lit 1502350767) (nat_lit 0) D2M8K2.t2283 from rfl, allE_node, rows2282, irow2276, rows2283]
  all_goals rfl

theorem atot2276 : totK PD2M8K2 D2M8K2.u2276 = [0, 156464172225, 742927805880, 758552452925, 113939288353, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2276 = KTree.node D2M8K2.t2282 (nat_lit 5489925) (nat_lit 1502350767) (nat_lit 0) D2M8K2.t2283 from rfl, totK_node, tot2282, tot2283]
  decide +kernel

theorem arows2278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2278 = true := by
  rw [show D2M8K2.u2278 = KTree.node D2M8K2.t2284 (nat_lit 5492080) (nat_lit 3688560836) (nat_lit 0) D2M8K2.t2285 from rfl, allE_node, rows2284, irow2278, rows2285]
  all_goals rfl

theorem atot2278 : totK PD2M8K2 D2M8K2.u2278 = [0, 334844051591, 845635168552, 524656878778, 97826819069, 3884009855, 0, 0] := by
  rw [show D2M8K2.u2278 = KTree.node D2M8K2.t2284 (nat_lit 5492080) (nat_lit 3688560836) (nat_lit 0) D2M8K2.t2285 from rfl, totK_node, tot2284, tot2285]
  decide +kernel

theorem arows2279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2279 = true := by
  rw [show D2M8K2.u2279 = KTree.node D2M8K2.t2286 (nat_lit 5493558) (nat_lit 3366027324) (nat_lit 0) D2M8K2.t2287 from rfl, allE_node, rows2286, irow2279, rows2287]
  all_goals rfl

theorem atot2279 : totK PD2M8K2 D2M8K2.u2279 = [0, 92937627352, 603630242944, 867582432415, 228225747504, 4967996017, 0, 0] := by
  rw [show D2M8K2.u2279 = KTree.node D2M8K2.t2286 (nat_lit 5493558) (nat_lit 3366027324) (nat_lit 0) D2M8K2.t2287 from rfl, totK_node, tot2286, tot2287]
  decide +kernel

theorem arows2283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2283 = true := by
  rw [show D2M8K2.u2283 = KTree.node D2M8K2.t2288 (nat_lit 5495194) (nat_lit 3844086955) (nat_lit 0) D2M8K2.t2289 from rfl, allE_node, rows2288, irow2283, rows2289]
  all_goals rfl

theorem atot2283 : totK PD2M8K2 D2M8K2.u2283 = [0, 0, 357687002685, 941656400309, 447033869359, 27877804034, 0, 0] := by
  rw [show D2M8K2.u2283 = KTree.node D2M8K2.t2288 (nat_lit 5495194) (nat_lit 3844086955) (nat_lit 0) D2M8K2.t2289 from rfl, totK_node, tot2288, tot2289]
  decide +kernel

theorem arows2284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2284 = true := by
  rw [show D2M8K2.u2284 = KTree.node D2M8K2.t2290 (nat_lit 5496718) (nat_lit 3397677032) (nat_lit 0) D2M8K2.t2291 from rfl, allE_node, rows2290, irow2284, rows2291]
  all_goals rfl

theorem atot2284 : totK PD2M8K2 D2M8K2.u2284 = [0, 0, 170591022402, 738386938865, 699847800991, 126348886272, 1369150432, 0] := by
  rw [show D2M8K2.u2284 = KTree.node D2M8K2.t2290 (nat_lit 5496718) (nat_lit 3397677032) (nat_lit 0) D2M8K2.t2291 from rfl, totK_node, tot2290, tot2291]
  decide +kernel

theorem arows2286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2286 = true := by
  rw [show D2M8K2.u2286 = KTree.node D2M8K2.t2292 (nat_lit 5502336) (nat_lit 2544918092) (nat_lit 0) D2M8K2.t2293 from rfl, allE_node, rows2292, irow2286, rows2293]
  all_goals rfl

theorem atot2286 : totK PD2M8K2 D2M8K2.u2286 = [0, 0, 324445543737, 904976676115, 506482365404, 38671121365, 0, 0] := by
  rw [show D2M8K2.u2286 = KTree.node D2M8K2.t2292 (nat_lit 5502336) (nat_lit 2544918092) (nat_lit 0) D2M8K2.t2293 from rfl, totK_node, tot2292, tot2293]
  decide +kernel

theorem arows2287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2287 = true := by
  rw [show D2M8K2.u2287 = KTree.node D2M8K2.t2294 (nat_lit 5505627) (nat_lit 1698665622) (nat_lit 0) D2M8K2.t2295 from rfl, allE_node, rows2294, irow2287, rows2295]
  all_goals rfl

theorem atot2287 : totK PD2M8K2 D2M8K2.u2287 = [0, 0, 354613452065, 947429367380, 460471660694, 24005519740, 0, 0] := by
  rw [show D2M8K2.u2287 = KTree.node D2M8K2.t2294 (nat_lit 5505627) (nat_lit 1698665622) (nat_lit 0) D2M8K2.t2295 from rfl, totK_node, tot2294, tot2295]
  decide +kernel

theorem arows2290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2290 = true := by
  rw [show D2M8K2.u2290 = KTree.node D2M8K2.t2296 (nat_lit 5508955) (nat_lit 2224329603) (nat_lit 0) D2M8K2.t2297 from rfl, allE_node, rows2296, irow2290, rows2297]
  all_goals rfl

theorem atot2290 : totK PD2M8K2 D2M8K2.u2290 = [0, 0, 393871463102, 946872374429, 405619079266, 22319214586, 0, 0] := by
  rw [show D2M8K2.u2290 = KTree.node D2M8K2.t2296 (nat_lit 5508955) (nat_lit 2224329603) (nat_lit 0) D2M8K2.t2297 from rfl, totK_node, tot2296, tot2297]
  decide +kernel

theorem arows2291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2291 = true := by
  rw [show D2M8K2.u2291 = KTree.node D2M8K2.t2298 (nat_lit 5512520) (nat_lit 3268600957) (nat_lit 0) D2M8K2.t2299 from rfl, allE_node, rows2298, irow2291, rows2299]
  all_goals rfl

theorem atot2291 : totK PD2M8K2 D2M8K2.u2291 = [0, 0, 344835305984, 937325930414, 465874055529, 24702880443, 0, 0] := by
  rw [show D2M8K2.u2291 = KTree.node D2M8K2.t2298 (nat_lit 5512520) (nat_lit 3268600957) (nat_lit 0) D2M8K2.t2299 from rfl, totK_node, tot2298, tot2299]
  decide +kernel

theorem arows2293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2293 = true := by
  rw [show D2M8K2.u2293 = KTree.node D2M8K2.t2300 (nat_lit 5519555) (nat_lit 2870342021) (nat_lit 0) D2M8K2.t2301 from rfl, allE_node, rows2300, irow2293, rows2301]
  all_goals rfl

theorem atot2293 : totK PD2M8K2 D2M8K2.u2293 = [0, 181009528986, 624369693706, 732635762587, 272283823780, 17433533548, 0, 0] := by
  rw [show D2M8K2.u2293 = KTree.node D2M8K2.t2300 (nat_lit 5519555) (nat_lit 2870342021) (nat_lit 0) D2M8K2.t2301 from rfl, totK_node, tot2300, tot2301]
  decide +kernel

theorem arows2294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2294 = true := by
  rw [show D2M8K2.u2294 = KTree.node D2M8K2.t2302 (nat_lit 5520730) (nat_lit 4003915680) (nat_lit 0) D2M8K2.t2303 from rfl, allE_node, rows2302, irow2294, rows2303]
  all_goals rfl

theorem atot2294 : totK PD2M8K2 D2M8K2.u2294 = [0, 249743698119, 767831542965, 602904883076, 188974420366, 21400436502, 0, 0] := by
  rw [show D2M8K2.u2294 = KTree.node D2M8K2.t2302 (nat_lit 5520730) (nat_lit 4003915680) (nat_lit 0) D2M8K2.t2303 from rfl, totK_node, tot2302, tot2303]
  decide +kernel

theorem arows2302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2302 = true := by
  rw [show D2M8K2.u2302 = KTree.node D2M8K2.t2304 (nat_lit 5522195) (nat_lit 2158995154) (nat_lit 0) D2M8K2.t2305 from rfl, allE_node, rows2304, irow2302, rows2305]
  all_goals rfl

theorem atot2302 : totK PD2M8K2 D2M8K2.u2302 = [0, 67372906060, 456092051894, 871540023978, 385082390966, 16208961603, 0, 0] := by
  rw [show D2M8K2.u2302 = KTree.node D2M8K2.t2304 (nat_lit 5522195) (nat_lit 2158995154) (nat_lit 0) D2M8K2.t2305 from rfl, totK_node, tot2304, tot2305]
  decide +kernel

theorem arows2303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2303 = true := by
  rw [show D2M8K2.u2303 = KTree.node D2M8K2.t2306 (nat_lit 5523478) (nat_lit 2987652673) (nat_lit 0) D2M8K2.t2307 from rfl, allE_node, rows2306, irow2303, rows2307]
  all_goals rfl

theorem atot2303 : totK PD2M8K2 D2M8K2.u2303 = [0, 336163580025, 910349741162, 534564540168, 47977298481, 0, 0, 0] := by
  rw [show D2M8K2.u2303 = KTree.node D2M8K2.t2306 (nat_lit 5523478) (nat_lit 2987652673) (nat_lit 0) D2M8K2.t2307 from rfl, totK_node, tot2306, tot2307]
  decide +kernel

theorem arows2305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2305 = true := by
  rw [show D2M8K2.u2305 = KTree.node D2M8K2.t2308 (nat_lit 5525252) (nat_lit 3170316863) (nat_lit 0) D2M8K2.t2309 from rfl, allE_node, rows2308, irow2305, rows2309]
  all_goals rfl

theorem atot2305 : totK PD2M8K2 D2M8K2.u2305 = [0, 79435114951, 556562211127, 876866297239, 265863147098, 9479825071, 0, 0] := by
  rw [show D2M8K2.u2305 = KTree.node D2M8K2.t2308 (nat_lit 5525252) (nat_lit 3170316863) (nat_lit 0) D2M8K2.t2309 from rfl, totK_node, tot2308, tot2309]
  decide +kernel

theorem arows2306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2306 = true := by
  rw [show D2M8K2.u2306 = KTree.node D2M8K2.t2310 (nat_lit 5527274) (nat_lit 4006288782) (nat_lit 0) D2M8K2.t2311 from rfl, allE_node, rows2310, irow2306, rows2311]
  all_goals rfl

theorem atot2306 : totK PD2M8K2 D2M8K2.u2306 = [0, 324359987373, 898741368214, 552980927420, 53080731267, 0, 0, 0] := by
  rw [show D2M8K2.u2306 = KTree.node D2M8K2.t2310 (nat_lit 5527274) (nat_lit 4006288782) (nat_lit 0) D2M8K2.t2311 from rfl, totK_node, tot2310, tot2311]
  decide +kernel

theorem arows2309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2309 = true := by
  rw [show D2M8K2.u2309 = KTree.node D2M8K2.t2312 (nat_lit 5529034) (nat_lit 2140057378) (nat_lit 0) D2M8K2.t2313 from rfl, allE_node, rows2312, irow2309, rows2313]
  all_goals rfl

theorem atot2309 : totK PD2M8K2 D2M8K2.u2309 = [0, 91605668374, 568927036857, 860270435636, 269105615296, 9599137095, 0, 0] := by
  rw [show D2M8K2.u2309 = KTree.node D2M8K2.t2312 (nat_lit 5529034) (nat_lit 2140057378) (nat_lit 0) D2M8K2.t2313 from rfl, totK_node, tot2312, tot2313]
  decide +kernel

theorem arows2310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2310 = true := by
  rw [show D2M8K2.u2310 = KTree.node D2M8K2.t2314 (nat_lit 5533930) (nat_lit 3878709408) (nat_lit 0) D2M8K2.t2315 from rfl, allE_node, rows2314, irow2310, rows2315]
  all_goals rfl

theorem atot2310 : totK PD2M8K2 D2M8K2.u2310 = [0, 336740796139, 900618491017, 538372046375, 51385537626, 0, 0, 0] := by
  rw [show D2M8K2.u2310 = KTree.node D2M8K2.t2314 (nat_lit 5533930) (nat_lit 3878709408) (nat_lit 0) D2M8K2.t2315 from rfl, totK_node, tot2314, tot2315]
  decide +kernel

theorem arows2312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2312 = true := by
  rw [show D2M8K2.u2312 = KTree.node D2M8K2.t2316 (nat_lit 5535566) (nat_lit 2381907441) (nat_lit 0) D2M8K2.t2317 from rfl, allE_node, rows2316, irow2312, rows2317]
  all_goals rfl

theorem atot2312 : totK PD2M8K2 D2M8K2.u2312 = [0, 0, 414873619399, 972964165187, 371261557703, 14952133379, 0, 0] := by
  rw [show D2M8K2.u2312 = KTree.node D2M8K2.t2316 (nat_lit 5535566) (nat_lit 2381907441) (nat_lit 0) D2M8K2.t2317 from rfl, totK_node, tot2316, tot2317]
  decide +kernel

theorem arows2313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2313 = true := by
  rw [show D2M8K2.u2313 = KTree.node D2M8K2.t2318 (nat_lit 5540786) (nat_lit 3969009105) (nat_lit 0) D2M8K2.t2319 from rfl, allE_node, rows2318, irow2313, rows2319]
  all_goals rfl

theorem atot2313 : totK PD2M8K2 D2M8K2.u2313 = [0, 0, 373893088149, 930298090288, 502736803365, 41644078143, 0, 0] := by
  rw [show D2M8K2.u2313 = KTree.node D2M8K2.t2318 (nat_lit 5540786) (nat_lit 3969009105) (nat_lit 0) D2M8K2.t2319 from rfl, totK_node, tot2318, tot2319]
  decide +kernel

theorem arows2317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2317 = true := by
  rw [show D2M8K2.u2317 = KTree.node D2M8K2.t2320 (nat_lit 5543846) (nat_lit 4041768059) (nat_lit 0) D2M8K2.t2321 from rfl, allE_node, rows2320, irow2317, rows2321]
  all_goals rfl

theorem atot2317 : totK PD2M8K2 D2M8K2.u2317 = [0, 0, 370859029186, 919008263008, 488400423868, 40870948458, 0, 0] := by
  rw [show D2M8K2.u2317 = KTree.node D2M8K2.t2320 (nat_lit 5543846) (nat_lit 4041768059) (nat_lit 0) D2M8K2.t2321 from rfl, totK_node, tot2320, tot2321]
  decide +kernel

theorem arows2318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2318 = true := by
  rw [show D2M8K2.u2318 = KTree.node D2M8K2.t2322 (nat_lit 5545578) (nat_lit 3164994452) (nat_lit 512) D2M8K2.t2323 from rfl, allE_node, rows2322, irow2318, rows2323]
  all_goals rfl

theorem atot2318 : totK PD2M8K2 D2M8K2.u2318 = [0, 0, 136840327874, 745223900521, 793714234563, 125420603567, 1547833102, 0] := by
  rw [show D2M8K2.u2318 = KTree.node D2M8K2.t2322 (nat_lit 5545578) (nat_lit 3164994452) (nat_lit 512) D2M8K2.t2323 from rfl, totK_node, tot2322, tot2323]
  decide +kernel

theorem arows2320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2320 = true := by
  rw [show D2M8K2.u2320 = KTree.node D2M8K2.t2324 (nat_lit 5547883) (nat_lit 1622503264) (nat_lit 0) D2M8K2.t2325 from rfl, allE_node, rows2324, irow2320, rows2325]
  all_goals rfl

theorem atot2320 : totK PD2M8K2 D2M8K2.u2320 = [0, 0, 353280657490, 936194569006, 497300648130, 35305627027, 0, 0] := by
  rw [show D2M8K2.u2320 = KTree.node D2M8K2.t2324 (nat_lit 5547883) (nat_lit 1622503264) (nat_lit 0) D2M8K2.t2325 from rfl, totK_node, tot2324, tot2325]
  decide +kernel

theorem arows2321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2321 = true := by
  rw [show D2M8K2.u2321 = KTree.node D2M8K2.t2326 (nat_lit 5549874) (nat_lit 3106512463) (nat_lit 2048) D2M8K2.t2327 from rfl, allE_node, rows2326, irow2321, rows2327]
  all_goals rfl

theorem atot2321 : totK PD2M8K2 D2M8K2.u2321 = [0, 0, 161394240974, 770019161657, 757346331709, 131582671470, 1557581783, 0] := by
  rw [show D2M8K2.u2321 = KTree.node D2M8K2.t2326 (nat_lit 5549874) (nat_lit 3106512463) (nat_lit 2048) D2M8K2.t2327 from rfl, totK_node, tot2326, tot2327]
  decide +kernel

theorem arows2324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2324 = true := by
  rw [show D2M8K2.u2324 = KTree.node D2M8K2.t2328 (nat_lit 5554884) (nat_lit 3007680835) (nat_lit 0) D2M8K2.t2329 from rfl, allE_node, rows2328, irow2324, rows2329]
  all_goals rfl

theorem atot2324 : totK PD2M8K2 D2M8K2.u2324 = [0, 0, 265132370958, 891863287463, 624157465263, 51119603372, 0, 0] := by
  rw [show D2M8K2.u2324 = KTree.node D2M8K2.t2328 (nat_lit 5554884) (nat_lit 3007680835) (nat_lit 0) D2M8K2.t2329 from rfl, totK_node, tot2328, tot2329]
  decide +kernel

theorem arows2325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2325 = true := by
  rw [show D2M8K2.u2325 = KTree.node D2M8K2.t2330 (nat_lit 5557081) (nat_lit 1454072130) (nat_lit 0) D2M8K2.t2331 from rfl, allE_node, rows2330, irow2325, rows2331]
  all_goals rfl

theorem atot2325 : totK PD2M8K2 D2M8K2.u2325 = [0, 178250561612, 377095042706, 365451266817, 620015128138, 229781561536, 9302370699, 0] := by
  rw [show D2M8K2.u2325 = KTree.node D2M8K2.t2330 (nat_lit 5557081) (nat_lit 1454072130) (nat_lit 0) D2M8K2.t2331 from rfl, totK_node, tot2330, tot2331]
  decide +kernel

theorem arows2327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2327 = true := by
  rw [show D2M8K2.u2327 = KTree.node D2M8K2.t2332 (nat_lit 5558660) (nat_lit 3610902744) (nat_lit 0) D2M8K2.t2333 from rfl, allE_node, rows2332, irow2327, rows2333]
  all_goals rfl

theorem atot2327 : totK PD2M8K2 D2M8K2.u2327 = [0, 232257346384, 774479459763, 651944586262, 110764090360, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2327 = KTree.node D2M8K2.t2332 (nat_lit 5558660) (nat_lit 3610902744) (nat_lit 0) D2M8K2.t2333 from rfl, totK_node, tot2332, tot2333]
  decide +kernel

theorem arows2328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2328 = true := by
  rw [show D2M8K2.u2328 = KTree.node D2M8K2.t2334 (nat_lit 5561049) (nat_lit 1821840459) (nat_lit 0) D2M8K2.t2335 from rfl, allE_node, rows2334, irow2328, rows2335]
  all_goals rfl

theorem atot2328 : totK PD2M8K2 D2M8K2.u2328 = [0, 198589163527, 781580063813, 753344022980, 94005336057, 0, 0, 0] := by
  rw [show D2M8K2.u2328 = KTree.node D2M8K2.t2334 (nat_lit 5561049) (nat_lit 1821840459) (nat_lit 0) D2M8K2.t2335 from rfl, totK_node, tot2334, tot2335]
  decide +kernel

theorem arows2333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2333 = true := by
  rw [show D2M8K2.u2333 = KTree.node D2M8K2.t2336 (nat_lit 5562366) (nat_lit 3949347901) (nat_lit 0) D2M8K2.t2337 from rfl, allE_node, rows2336, irow2333, rows2337]
  all_goals rfl

theorem atot2333 : totK PD2M8K2 D2M8K2.u2333 = [0, 189447561880, 696296573939, 686899264803, 228793529806, 19862268668, 0, 0] := by
  rw [show D2M8K2.u2333 = KTree.node D2M8K2.t2336 (nat_lit 5562366) (nat_lit 3949347901) (nat_lit 0) D2M8K2.t2337 from rfl, totK_node, tot2336, tot2337]
  decide +kernel

theorem arows2334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2334 = true := by
  rw [show D2M8K2.u2334 = KTree.node D2M8K2.t2338 (nat_lit 5564010) (nat_lit 3742543915) (nat_lit 0) D2M8K2.t2339 from rfl, allE_node, rows2338, irow2334, rows2339]
  all_goals rfl

theorem atot2334 : totK PD2M8K2 D2M8K2.u2334 = [0, 173426155916, 596218477891, 710373291978, 310941185703, 13718290542, 0, 0] := by
  rw [show D2M8K2.u2334 = KTree.node D2M8K2.t2338 (nat_lit 5564010) (nat_lit 3742543915) (nat_lit 0) D2M8K2.t2339 from rfl, totK_node, tot2338, tot2339]
  decide +kernel

theorem arows2336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2336 = true := by
  rw [show D2M8K2.u2336 = KTree.node D2M8K2.t2340 (nat_lit 5565485) (nat_lit 2029103234) (nat_lit 0) D2M8K2.t2341 from rfl, allE_node, rows2340, irow2336, rows2341]
  all_goals rfl

theorem atot2336 : totK PD2M8K2 D2M8K2.u2336 = [0, 264714149185, 815841876125, 630690436014, 86933728881, 1164319620, 0, 0] := by
  rw [show D2M8K2.u2336 = KTree.node D2M8K2.t2340 (nat_lit 5565485) (nat_lit 2029103234) (nat_lit 0) D2M8K2.t2341 from rfl, totK_node, tot2340, tot2341]
  decide +kernel

theorem arows2337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2337 = true := by
  rw [show D2M8K2.u2337 = KTree.node D2M8K2.t2342 (nat_lit 5567137) (nat_lit 1469771105) (nat_lit 0) D2M8K2.t2343 from rfl, allE_node, rows2342, irow2337, rows2343]
  all_goals rfl

theorem atot2337 : totK PD2M8K2 D2M8K2.u2337 = [0, 119372288294, 596087510947, 820292002320, 243083506544, 11885407614, 0, 0] := by
  rw [show D2M8K2.u2337 = KTree.node D2M8K2.t2342 (nat_lit 5567137) (nat_lit 1469771105) (nat_lit 0) D2M8K2.t2343 from rfl, totK_node, tot2342, tot2343]
  decide +kernel

theorem arows2340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2340 = true := by
  rw [show D2M8K2.u2340 = KTree.node D2M8K2.t2344 (nat_lit 5572326) (nat_lit 3631260407) (nat_lit 0) D2M8K2.t2345 from rfl, allE_node, rows2344, irow2340, rows2345]
  all_goals rfl

theorem atot2340 : totK PD2M8K2 D2M8K2.u2340 = [0, 206948841793, 792813540883, 691200248477, 104328728561, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2340 = KTree.node D2M8K2.t2344 (nat_lit 5572326) (nat_lit 3631260407) (nat_lit 0) D2M8K2.t2345 from rfl, totK_node, tot2344, tot2345]
  decide +kernel

theorem arows2341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2341 = true := by
  rw [show D2M8K2.u2341 = KTree.node D2M8K2.t2346 (nat_lit 5574857) (nat_lit 1796373502) (nat_lit 0) D2M8K2.t2347 from rfl, allE_node, rows2346, irow2341, rows2347]
  all_goals rfl

theorem atot2341 : totK PD2M8K2 D2M8K2.u2341 = [0, 271672666917, 783939190146, 616099712547, 120684796936, 3884009855, 0, 0] := by
  rw [show D2M8K2.u2341 = KTree.node D2M8K2.t2346 (nat_lit 5574857) (nat_lit 1796373502) (nat_lit 0) D2M8K2.t2347 from rfl, totK_node, tot2346, tot2347]
  decide +kernel

theorem arows2343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2343 = true := by
  rw [show D2M8K2.u2343 = KTree.node D2M8K2.t2348 (nat_lit 5576324) (nat_lit 2858580865) (nat_lit 0) D2M8K2.t2349 from rfl, allE_node, rows2348, irow2343, rows2349]
  all_goals rfl

theorem atot2343 : totK PD2M8K2 D2M8K2.u2343 = [0, 152199982118, 678609241624, 778472558390, 189208337718, 4967996017, 0, 0] := by
  rw [show D2M8K2.u2343 = KTree.node D2M8K2.t2348 (nat_lit 5576324) (nat_lit 2858580865) (nat_lit 0) D2M8K2.t2349 from rfl, totK_node, tot2348, tot2349]
  decide +kernel

theorem arows2344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2344 = true := by
  rw [show D2M8K2.u2344 = KTree.node D2M8K2.t2350 (nat_lit 5577997) (nat_lit 1391987541) (nat_lit 0) D2M8K2.t2351 from rfl, allE_node, rows2350, irow2344, rows2351]
  all_goals rfl

theorem atot2344 : totK PD2M8K2 D2M8K2.u2344 = [0, 0, 377568134010, 944008845764, 430464111974, 26915935669, 0, 0] := by
  rw [show D2M8K2.u2344 = KTree.node D2M8K2.t2350 (nat_lit 5577997) (nat_lit 1391987541) (nat_lit 0) D2M8K2.t2351 from rfl, totK_node, tot2350, tot2351]
  decide +kernel

theorem arows2348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2348 = true := by
  rw [show D2M8K2.u2348 = KTree.node D2M8K2.t2352 (nat_lit 5579616) (nat_lit 3427134575) (nat_lit 0) D2M8K2.t2353 from rfl, allE_node, rows2352, irow2348, rows2353]
  all_goals rfl

theorem atot2348 : totK PD2M8K2 D2M8K2.u2348 = [0, 0, 195922672640, 790313079081, 661786690709, 86240537152, 1206465782, 0] := by
  rw [show D2M8K2.u2348 = KTree.node D2M8K2.t2352 (nat_lit 5579616) (nat_lit 3427134575) (nat_lit 0) D2M8K2.t2353 from rfl, totK_node, tot2352, tot2353]
  decide +kernel

theorem arows2349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2349 = true := by
  rw [show D2M8K2.u2349 = KTree.node D2M8K2.t2354 (nat_lit 5582061) (nat_lit 1480570842) (nat_lit 0) D2M8K2.t2355 from rfl, allE_node, rows2354, irow2349, rows2355]
  all_goals rfl

theorem atot2349 : totK PD2M8K2 D2M8K2.u2349 = [0, 0, 299664142884, 902084451959, 561482472086, 48690107863, 0, 0] := by
  rw [show D2M8K2.u2349 = KTree.node D2M8K2.t2354 (nat_lit 5582061) (nat_lit 1480570842) (nat_lit 0) D2M8K2.t2355 from rfl, totK_node, tot2354, tot2355]
  decide +kernel

theorem arows2351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2351 = true := by
  rw [show D2M8K2.u2351 = KTree.node D2M8K2.t2356 (nat_lit 5585233) (nat_lit 1286755871) (nat_lit 0) D2M8K2.t2357 from rfl, allE_node, rows2356, irow2351, rows2357]
  all_goals rfl

theorem atot2351 : totK PD2M8K2 D2M8K2.u2351 = [0, 0, 371209546150, 928006048220, 475074370419, 34290996991, 0, 0] := by
  rw [show D2M8K2.u2351 = KTree.node D2M8K2.t2356 (nat_lit 5585233) (nat_lit 1286755871) (nat_lit 0) D2M8K2.t2357 from rfl, totK_node, tot2356, tot2357]
  decide +kernel

theorem arows2352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2352 = true := by
  rw [show D2M8K2.u2352 = KTree.node D2M8K2.t2358 (nat_lit 5586707) (nat_lit 1800228814) (nat_lit 0) D2M8K2.t2359 from rfl, allE_node, rows2358, irow2352, rows2359]
  all_goals rfl

theorem atot2352 : totK PD2M8K2 D2M8K2.u2352 = [0, 0, 149747826631, 691524391377, 745763414520, 166447293104, 5395128787, 0] := by
  rw [show D2M8K2.u2352 = KTree.node D2M8K2.t2358 (nat_lit 5586707) (nat_lit 1800228814) (nat_lit 0) D2M8K2.t2359 from rfl, totK_node, tot2358, tot2359]
  decide +kernel

theorem arows2355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2355 = true := by
  rw [show D2M8K2.u2355 = KTree.node D2M8K2.t2360 (nat_lit 5592267) (nat_lit 3773144805) (nat_lit 0) D2M8K2.t2361 from rfl, allE_node, rows2360, irow2355, rows2361]
  all_goals rfl

theorem atot2355 : totK PD2M8K2 D2M8K2.u2355 = [0, 0, 324964146307, 912296807434, 510777276891, 37772234209, 0, 0] := by
  rw [show D2M8K2.u2355 = KTree.node D2M8K2.t2360 (nat_lit 5592267) (nat_lit 3773144805) (nat_lit 0) D2M8K2.t2361 from rfl, totK_node, tot2360, tot2361]
  decide +kernel

theorem arows2356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2356 = true := by
  rw [show D2M8K2.u2356 = KTree.node D2M8K2.t2362 (nat_lit 5595817) (nat_lit 1237989483) (nat_lit 0) D2M8K2.t2363 from rfl, allE_node, rows2362, irow2356, rows2363]
  all_goals rfl

theorem atot2356 : totK PD2M8K2 D2M8K2.u2356 = [0, 0, 368893669074, 935153099722, 467420786290, 28227965347, 0, 0] := by
  rw [show D2M8K2.u2356 = KTree.node D2M8K2.t2362 (nat_lit 5595817) (nat_lit 1237989483) (nat_lit 0) D2M8K2.t2363 from rfl, totK_node, tot2362, tot2363]
  decide +kernel

theorem arows2358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2358 = true := by
  rw [show D2M8K2.u2358 = KTree.node D2M8K2.t2364 (nat_lit 5599397) (nat_lit 2283242543) (nat_lit 0) D2M8K2.t2365 from rfl, allE_node, rows2364, irow2358, rows2365]
  all_goals rfl

theorem atot2358 : totK PD2M8K2 D2M8K2.u2358 = [0, 323472498165, 800218543473, 508122028166, 154170215986, 13566920432, 0, 0] := by
  rw [show D2M8K2.u2358 = KTree.node D2M8K2.t2364 (nat_lit 5599397) (nat_lit 2283242543) (nat_lit 0) D2M8K2.t2365 from rfl, totK_node, tot2364, tot2365]
  decide +kernel

theorem arows2359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2359 = true := by
  rw [show D2M8K2.u2359 = KTree.node D2M8K2.t2366 (nat_lit 5600608) (nat_lit 2744360005) (nat_lit 0) D2M8K2.t2367 from rfl, allE_node, rows2366, irow2359, rows2367]
  all_goals rfl

theorem atot2359 : totK PD2M8K2 D2M8K2.u2359 = [0, 87093597246, 680765889132, 868927718122, 147239455685, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2359 = KTree.node D2M8K2.t2366 (nat_lit 5600608) (nat_lit 2744360005) (nat_lit 0) D2M8K2.t2367 from rfl, totK_node, tot2366, tot2367]
  decide +kernel

theorem arows2365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2365 = true := by
  rw [show D2M8K2.u2365 = KTree.node D2M8K2.t2368 (nat_lit 5603072) (nat_lit 3748618600) (nat_lit 0) D2M8K2.t2369 from rfl, allE_node, rows2368, irow2365, rows2369]
  all_goals rfl

theorem atot2365 : totK PD2M8K2 D2M8K2.u2365 = [0, 383943773090, 910751064165, 497638029964, 47708167084, 0, 0, 0] := by
  rw [show D2M8K2.u2365 = KTree.node D2M8K2.t2368 (nat_lit 5603072) (nat_lit 3748618600) (nat_lit 0) D2M8K2.t2369 from rfl, totK_node, tot2368, tot2369]
  decide +kernel

theorem arows2366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2366 = true := by
  rw [show D2M8K2.u2366 = KTree.node D2M8K2.t2370 (nat_lit 5604622) (nat_lit 3978198139) (nat_lit 0) D2M8K2.t2371 from rfl, allE_node, rows2370, irow2366, rows2371]
  all_goals rfl

theorem atot2366 : totK PD2M8K2 D2M8K2.u2366 = [0, 0, 441216004988, 926101460687, 416915930223, 26856412781, 0, 0] := by
  rw [show D2M8K2.u2366 = KTree.node D2M8K2.t2370 (nat_lit 5604622) (nat_lit 3978198139) (nat_lit 0) D2M8K2.t2371 from rfl, totK_node, tot2370, tot2371]
  decide +kernel

theorem arows2368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2368 = true := by
  rw [show D2M8K2.u2368 = KTree.node D2M8K2.t2372 (nat_lit 5609480) (nat_lit 3887359301) (nat_lit 0) D2M8K2.t2373 from rfl, allE_node, rows2372, irow2368, rows2373]
  all_goals rfl

theorem atot2368 : totK PD2M8K2 D2M8K2.u2368 = [0, 311863256778, 806584189473, 554305219827, 134245381787, 6799735859, 0, 0] := by
  rw [show D2M8K2.u2368 = KTree.node D2M8K2.t2372 (nat_lit 5609480) (nat_lit 3887359301) (nat_lit 0) D2M8K2.t2373 from rfl, totK_node, tot2372, tot2373]
  decide +kernel

theorem arows2369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2369 = true := by
  rw [show D2M8K2.u2369 = KTree.node D2M8K2.t2374 (nat_lit 5610936) (nat_lit 3616749085) (nat_lit 0) D2M8K2.t2375 from rfl, allE_node, rows2374, irow2369, rows2375]
  all_goals rfl

theorem atot2369 : totK PD2M8K2 D2M8K2.u2369 = [0, 122942284081, 643620533446, 803385668817, 217652763790, 9668735432, 0, 0] := by
  rw [show D2M8K2.u2369 = KTree.node D2M8K2.t2374 (nat_lit 5610936) (nat_lit 3616749085) (nat_lit 0) D2M8K2.t2375 from rfl, totK_node, tot2374, tot2375]
  decide +kernel

theorem arows2372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2372 = true := by
  rw [show D2M8K2.u2372 = KTree.node D2M8K2.t2376 (nat_lit 5612747) (nat_lit 2011072533) (nat_lit 0) D2M8K2.t2377 from rfl, allE_node, rows2376, irow2372, rows2377]
  all_goals rfl

theorem atot2372 : totK PD2M8K2 D2M8K2.u2372 = [0, 257184741326, 796746105423, 630730646851, 115491085632, 3581949829, 0, 0] := by
  rw [show D2M8K2.u2372 = KTree.node D2M8K2.t2376 (nat_lit 5612747) (nat_lit 2011072533) (nat_lit 0) D2M8K2.t2377 from rfl, totK_node, tot2376, tot2377]
  decide +kernel

theorem arows2373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2373 = true := by
  rw [show D2M8K2.u2373 = KTree.node D2M8K2.t2378 (nat_lit 5614699) (nat_lit 1188470258) (nat_lit 0) D2M8K2.t2379 from rfl, allE_node, rows2378, irow2373, rows2379]
  all_goals rfl

theorem atot2373 : totK PD2M8K2 D2M8K2.u2373 = [0, 150246515999, 661895009475, 776518750106, 181439449565, 4980514959, 0, 0] := by
  rw [show D2M8K2.u2373 = KTree.node D2M8K2.t2378 (nat_lit 5614699) (nat_lit 1188470258) (nat_lit 0) D2M8K2.t2379 from rfl, totK_node, tot2378, tot2379]
  decide +kernel

theorem arows2375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2375 = true := by
  rw [show D2M8K2.u2375 = KTree.node D2M8K2.t2380 (nat_lit 5616772) (nat_lit 4034614820) (nat_lit 0) D2M8K2.t2381 from rfl, allE_node, rows2380, irow2375, rows2381]
  all_goals rfl

theorem atot2375 : totK PD2M8K2 D2M8K2.u2375 = [0, 341231344346, 921484169085, 523578822543, 40449030187, 0, 0, 0] := by
  rw [show D2M8K2.u2375 = KTree.node D2M8K2.t2380 (nat_lit 5616772) (nat_lit 4034614820) (nat_lit 0) D2M8K2.t2381 from rfl, totK_node, tot2380, tot2381]
  decide +kernel

theorem arows2376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2376 = true := by
  rw [show D2M8K2.u2376 = KTree.node D2M8K2.t2382 (nat_lit 5618442) (nat_lit 3208515040) (nat_lit 0) D2M8K2.t2383 from rfl, allE_node, rows2382, irow2376, rows2383]
  all_goals rfl

theorem atot2376 : totK PD2M8K2 D2M8K2.u2376 = [0, 0, 443404830997, 988363689365, 337718269679, 9935930005, 0, 0] := by
  rw [show D2M8K2.u2376 = KTree.node D2M8K2.t2382 (nat_lit 5618442) (nat_lit 3208515040) (nat_lit 0) D2M8K2.t2383 from rfl, totK_node, tot2382, tot2383]
  decide +kernel

theorem arows2380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2380 = true := by
  rw [show D2M8K2.u2380 = KTree.node D2M8K2.t2384 (nat_lit 5620353) (nat_lit 1702359462) (nat_lit 0) D2M8K2.t2385 from rfl, allE_node, rows2384, irow2380, rows2385]
  all_goals rfl

theorem atot2380 : totK PD2M8K2 D2M8K2.u2380 = [0, 0, 379336175431, 935532223697, 425970415769, 26986547656, 0, 0] := by
  rw [show D2M8K2.u2380 = KTree.node D2M8K2.t2384 (nat_lit 5620353) (nat_lit 1702359462) (nat_lit 0) D2M8K2.t2385 from rfl, totK_node, tot2384, tot2385]
  decide +kernel

theorem arows2381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2381 = true := by
  rw [show D2M8K2.u2381 = KTree.node D2M8K2.t2386 (nat_lit 5622130) (nat_lit 3882307045) (nat_lit 0) D2M8K2.t2387 from rfl, allE_node, rows2386, irow2381, rows2387]
  all_goals rfl

theorem atot2381 : totK PD2M8K2 D2M8K2.u2381 = [0, 0, 121397590414, 736179509692, 794475147822, 115610105222, 1239866073, 0] := by
  rw [show D2M8K2.u2381 = KTree.node D2M8K2.t2386 (nat_lit 5622130) (nat_lit 3882307045) (nat_lit 0) D2M8K2.t2387 from rfl, totK_node, tot2386, tot2387]
  decide +kernel

theorem arows2383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2383 = true := by
  rw [show D2M8K2.u2383 = KTree.node D2M8K2.t2388 (nat_lit 5624149) (nat_lit 1179199144) (nat_lit 0) D2M8K2.t2389 from rfl, allE_node, rows2388, irow2383, rows2389]
  all_goals rfl

theorem atot2383 : totK PD2M8K2 D2M8K2.u2383 = [0, 0, 381795503782, 941336235239, 465811907979, 30182319090, 0, 0] := by
  rw [show D2M8K2.u2383 = KTree.node D2M8K2.t2388 (nat_lit 5624149) (nat_lit 1179199144) (nat_lit 0) D2M8K2.t2389 from rfl, totK_node, tot2388, tot2389]
  decide +kernel

theorem arows2384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2384 = true := by
  rw [show D2M8K2.u2384 = KTree.node D2M8K2.t2390 (nat_lit 5630854) (nat_lit 2481510429) (nat_lit 0) D2M8K2.t2391 from rfl, allE_node, rows2390, irow2384, rows2391]
  all_goals rfl

theorem atot2384 : totK PD2M8K2 D2M8K2.u2384 = [0, 0, 351169685097, 930887142389, 491817471152, 30122517916, 0, 0] := by
  rw [show D2M8K2.u2384 = KTree.node D2M8K2.t2390 (nat_lit 5630854) (nat_lit 2481510429) (nat_lit 0) D2M8K2.t2391 from rfl, totK_node, tot2390, tot2391]
  decide +kernel

theorem arows2387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2387 = true := by
  rw [show D2M8K2.u2387 = KTree.node D2M8K2.t2392 (nat_lit 5632565) (nat_lit 911823418) (nat_lit 0) D2M8K2.t2393 from rfl, allE_node, rows2392, irow2387, rows2393]
  all_goals rfl

theorem atot2387 : totK PD2M8K2 D2M8K2.u2387 = [0, 0, 81275040639, 648261169305, 840920941529, 188956385580, 5425831197, 0] := by
  rw [show D2M8K2.u2387 = KTree.node D2M8K2.t2392 (nat_lit 5632565) (nat_lit 911823418) (nat_lit 0) D2M8K2.t2393 from rfl, totK_node, tot2392, tot2393]
  decide +kernel

theorem arows2388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2388 = true := by
  rw [show D2M8K2.u2388 = KTree.node D2M8K2.t2394 (nat_lit 5634481) (nat_lit 1420411585) (nat_lit 0) D2M8K2.t2395 from rfl, allE_node, rows2394, irow2388, rows2395]
  all_goals rfl

theorem atot2388 : totK PD2M8K2 D2M8K2.u2388 = [0, 0, 403693469199, 960966851737, 411048839321, 18154218163, 0, 0] := by
  rw [show D2M8K2.u2388 = KTree.node D2M8K2.t2394 (nat_lit 5634481) (nat_lit 1420411585) (nat_lit 0) D2M8K2.t2395 from rfl, totK_node, tot2394, tot2395]
  decide +kernel

theorem arows2390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2390 = true := by
  rw [show D2M8K2.u2390 = KTree.node D2M8K2.t2396 (nat_lit 5637764) (nat_lit 2680467627) (nat_lit 0) D2M8K2.t2397 from rfl, allE_node, rows2396, irow2390, rows2397]
  all_goals rfl

theorem atot2390 : totK PD2M8K2 D2M8K2.u2390 = [0, 90585905067, 419701659741, 791078824809, 483055761320, 38663154929, 0, 0] := by
  rw [show D2M8K2.u2390 = KTree.node D2M8K2.t2396 (nat_lit 5637764) (nat_lit 2680467627) (nat_lit 0) D2M8K2.t2397 from rfl, totK_node, tot2396, tot2397]
  decide +kernel

theorem arows2391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2391 = true := by
  rw [show D2M8K2.u2391 = KTree.node D2M8K2.t2398 (nat_lit 5682756) (nat_lit 3062633191) (nat_lit 0) D2M8K2.t2399 from rfl, allE_node, rows2398, irow2391, rows2399]
  all_goals rfl

theorem atot2391 : totK PD2M8K2 D2M8K2.u2391 = [0, 327680244160, 921491516175, 506869547794, 35976288522, 0, 0, 0] := by
  rw [show D2M8K2.u2391 = KTree.node D2M8K2.t2398 (nat_lit 5682756) (nat_lit 3062633191) (nat_lit 0) D2M8K2.t2399 from rfl, totK_node, tot2398, tot2399]
  decide +kernel

end QECKChecks.D2M8K2
