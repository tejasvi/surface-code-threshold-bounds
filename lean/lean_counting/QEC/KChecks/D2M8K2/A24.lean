import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A23

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows1037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1037 = true := by
  rw [show D2M8K2.u1037 = KTree.node D2M8K2.u1029 (nat_lit 2160789) (nat_lit 1457963607) (nat_lit 0) D2M8K2.u1036 from rfl, allE_node, arows1029, irow1037, arows1036]
  all_goals rfl

theorem atot1037 : totK PD2M8K2 D2M8K2.u1037 = [1324954268589, 4880046995265, 5590974213276, 2254826886846, 247702221761, 4720618446, 0, 0] := by
  rw [show D2M8K2.u1037 = KTree.node D2M8K2.u1029 (nat_lit 2160789) (nat_lit 1457963607) (nat_lit 0) D2M8K2.u1036 from rfl, totK_node, atot1029, atot1036]
  decide +kernel

theorem arows1052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1052 = true := by
  rw [show D2M8K2.u1052 = KTree.node D2M8K2.u1044 (nat_lit 2177348) (nat_lit 3308106591) (nat_lit 0) D2M8K2.u1051 from rfl, allE_node, arows1044, irow1052, arows1051]
  all_goals rfl

theorem atot1052 : totK PD2M8K2 D2M8K2.u1052 = [777451607106, 4212795883833, 6473929760157, 2657641190990, 198277481621, 1138244013, 0, 0] := by
  rw [show D2M8K2.u1052 = KTree.node D2M8K2.u1044 (nat_lit 2177348) (nat_lit 3308106591) (nat_lit 0) D2M8K2.u1051 from rfl, totK_node, atot1044, atot1051]
  decide +kernel

theorem arows1068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1068 = true := by
  rw [show D2M8K2.u1068 = KTree.node D2M8K2.u1060 (nat_lit 2240984) (nat_lit 2838887159) (nat_lit 0) D2M8K2.u1067 from rfl, allE_node, arows1060, irow1068, arows1067]
  all_goals rfl

theorem atot1068 : totK PD2M8K2 D2M8K2.u1068 = [0, 2047687544491, 6535584815053, 4953892781957, 746860346665, 19329714611, 0, 0] := by
  rw [show D2M8K2.u1068 = KTree.node D2M8K2.u1060 (nat_lit 2240984) (nat_lit 2838887159) (nat_lit 0) D2M8K2.u1067 from rfl, totK_node, atot1060, atot1067]
  decide +kernel

theorem arows1083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1083 = true := by
  rw [show D2M8K2.u1083 = KTree.node D2M8K2.u1075 (nat_lit 2258766) (nat_lit 3505153862) (nat_lit 0) D2M8K2.u1082 from rfl, allE_node, arows1075, irow1083, arows1082]
  all_goals rfl

theorem atot1083 : totK PD2M8K2 D2M8K2.u1083 = [0, 763385201231, 4444144646998, 6596316840232, 2209899668924, 156126487842, 1209030869, 0] := by
  rw [show D2M8K2.u1083 = KTree.node D2M8K2.u1075 (nat_lit 2258766) (nat_lit 3505153862) (nat_lit 0) D2M8K2.u1082 from rfl, totK_node, atot1075, atot1082]
  decide +kernel

theorem arows1100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1100 = true := by
  rw [show D2M8K2.u1100 = KTree.node D2M8K2.u1092 (nat_lit 2287986) (nat_lit 2690749060) (nat_lit 0) D2M8K2.u1099 from rfl, allE_node, arows1092, irow1100, arows1099]
  all_goals rfl

theorem atot1100 : totK PD2M8K2 D2M8K2.u1100 = [0, 1341181739728, 5305819250932, 5961907439941, 1721611929691, 86101066146, 0, 0] := by
  rw [show D2M8K2.u1100 = KTree.node D2M8K2.u1092 (nat_lit 2287986) (nat_lit 2690749060) (nat_lit 0) D2M8K2.u1099 from rfl, totK_node, atot1092, atot1099]
  decide +kernel

theorem arows1115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1115 = true := by
  rw [show D2M8K2.u1115 = KTree.node D2M8K2.u1107 (nat_lit 2326799) (nat_lit 2053410530) (nat_lit 0) D2M8K2.u1114 from rfl, allE_node, arows1107, irow1115, arows1114]
  all_goals rfl

theorem atot1115 : totK PD2M8K2 D2M8K2.u1115 = [0, 1715865626836, 6054937454189, 5556298866097, 1089558487261, 33254599591, 0, 0] := by
  rw [show D2M8K2.u1115 = KTree.node D2M8K2.u1107 (nat_lit 2326799) (nat_lit 2053410530) (nat_lit 0) D2M8K2.u1114 from rfl, totK_node, atot1107, atot1114]
  decide +kernel

theorem arows1131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1131 = true := by
  rw [show D2M8K2.u1131 = KTree.node D2M8K2.u1123 (nat_lit 2365383) (nat_lit 2926209066) (nat_lit 0) D2M8K2.u1130 from rfl, allE_node, arows1123, irow1131, arows1130]
  all_goals rfl

theorem atot1131 : totK PD2M8K2 D2M8K2.u1131 = [0, 1811456292653, 6148581065180, 5442949055173, 1025542396838, 26238259976, 0, 0] := by
  rw [show D2M8K2.u1131 = KTree.node D2M8K2.u1123 (nat_lit 2365383) (nat_lit 2926209066) (nat_lit 0) D2M8K2.u1130 from rfl, totK_node, atot1123, atot1130]
  decide +kernel

theorem arows1146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1146 = true := by
  rw [show D2M8K2.u1146 = KTree.node D2M8K2.u1138 (nat_lit 2383074) (nat_lit 2567541942) (nat_lit 0) D2M8K2.u1145 from rfl, allE_node, arows1138, irow1146, arows1145]
  all_goals rfl

theorem atot1146 : totK PD2M8K2 D2M8K2.u1146 = [0, 1567728562222, 5811991988926, 5709214706537, 1194779979858, 42729965530, 0, 0] := by
  rw [show D2M8K2.u1146 = KTree.node D2M8K2.u1138 (nat_lit 2383074) (nat_lit 2567541942) (nat_lit 0) D2M8K2.u1145 from rfl, totK_node, atot1138, atot1145]
  decide +kernel

theorem arows1164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1164 = true := by
  rw [show D2M8K2.u1164 = KTree.node D2M8K2.u1156 (nat_lit 2417872) (nat_lit 3114739077) (nat_lit 0) D2M8K2.u1163 from rfl, allE_node, arows1156, irow1164, arows1163]
  all_goals rfl

theorem atot1164 : totK PD2M8K2 D2M8K2.u1164 = [0, 1275019031443, 5124218489284, 5967250062158, 1724233546518, 121602704732, 1138244013, 0] := by
  rw [show D2M8K2.u1164 = KTree.node D2M8K2.u1156 (nat_lit 2417872) (nat_lit 3114739077) (nat_lit 0) D2M8K2.u1163 from rfl, totK_node, atot1156, atot1163]
  decide +kernel

theorem arows1179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1179 = true := by
  rw [show D2M8K2.u1179 = KTree.node D2M8K2.u1171 (nat_lit 2440720) (nat_lit 3551478235) (nat_lit 0) D2M8K2.u1178 from rfl, allE_node, arows1171, irow1179, arows1178]
  all_goals rfl

theorem atot1179 : totK PD2M8K2 D2M8K2.u1179 = [751404570366, 2275484782191, 3315200535270, 4862338133317, 2719895564894, 322383848345, 4977114383, 0] := by
  rw [show D2M8K2.u1179 = KTree.node D2M8K2.u1171 (nat_lit 2440720) (nat_lit 3551478235) (nat_lit 0) D2M8K2.u1178 from rfl, totK_node, atot1171, atot1178]
  decide +kernel

theorem arows1195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1195 = true := by
  rw [show D2M8K2.u1195 = KTree.node D2M8K2.u1187 (nat_lit 2503302) (nat_lit 3737681614) (nat_lit 0) D2M8K2.u1194 from rfl, allE_node, arows1187, irow1195, arows1194]
  all_goals rfl

theorem atot1195 : totK PD2M8K2 D2M8K2.u1195 = [1276388165891, 5274247260606, 6045763886995, 1658960051326, 72413804504, 0, 0, 0] := by
  rw [show D2M8K2.u1195 = KTree.node D2M8K2.u1187 (nat_lit 2503302) (nat_lit 3737681614) (nat_lit 0) D2M8K2.u1194 from rfl, totK_node, atot1187, atot1194]
  decide +kernel

theorem arows1210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1210 = true := by
  rw [show D2M8K2.u1210 = KTree.node D2M8K2.u1202 (nat_lit 2524122) (nat_lit 3878802952) (nat_lit 0) D2M8K2.u1209 from rfl, allE_node, arows1202, irow1210, arows1209]
  all_goals rfl

theorem atot1210 : totK PD2M8K2 D2M8K2.u1210 = [587208211945, 3566329178232, 6592945296687, 3359492623675, 287994352960, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1210 = KTree.node D2M8K2.u1202 (nat_lit 2524122) (nat_lit 3878802952) (nat_lit 0) D2M8K2.u1209 from rfl, totK_node, atot1202, atot1209]
  decide +kernel

theorem arows1227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1227 = true := by
  rw [show D2M8K2.u1227 = KTree.node D2M8K2.u1219 (nat_lit 2547572) (nat_lit 3052916419) (nat_lit 0) D2M8K2.u1226 from rfl, allE_node, arows1219, irow1227, arows1226]
  all_goals rfl

theorem atot1227 : totK PD2M8K2 D2M8K2.u1227 = [1079223068082, 4481426269496, 5775719306734, 2601255566700, 518102838912, 30397782892, 0, 0] := by
  rw [show D2M8K2.u1227 = KTree.node D2M8K2.u1219 (nat_lit 2547572) (nat_lit 3052916419) (nat_lit 0) D2M8K2.u1226 from rfl, totK_node, atot1219, atot1226]
  decide +kernel

theorem arows1242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1242 = true := by
  rw [show D2M8K2.u1242 = KTree.node D2M8K2.u1234 (nat_lit 2567894) (nat_lit 3216338093) (nat_lit 0) D2M8K2.u1241 from rfl, allE_node, arows1234, irow1242, arows1241]
  all_goals rfl

theorem atot1242 : totK PD2M8K2 D2M8K2.u1242 = [501701010607, 2868124337760, 5736549211062, 4383555185986, 911753368698, 26205202981, 0, 0] := by
  rw [show D2M8K2.u1242 = KTree.node D2M8K2.u1234 (nat_lit 2567894) (nat_lit 3216338093) (nat_lit 0) D2M8K2.u1241 from rfl, totK_node, atot1234, atot1241]
  decide +kernel

theorem arows1258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1258 = true := by
  rw [show D2M8K2.u1258 = KTree.node D2M8K2.u1250 (nat_lit 2581377) (nat_lit 1301426750) (nat_lit 0) D2M8K2.u1257 from rfl, allE_node, arows1250, irow1258, arows1257]
  all_goals rfl

theorem atot1258 : totK PD2M8K2 D2M8K2.u1258 = [1487692789937, 5522046217437, 5785781059368, 1573122920512, 76351608088, 0, 0, 0] := by
  rw [show D2M8K2.u1258 = KTree.node D2M8K2.u1250 (nat_lit 2581377) (nat_lit 1301426750) (nat_lit 0) D2M8K2.u1257 from rfl, totK_node, atot1250, atot1257]
  decide +kernel

theorem arows1273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1273 = true := by
  rw [show D2M8K2.u1273 = KTree.node D2M8K2.u1265 (nat_lit 2600802) (nat_lit 1490272098) (nat_lit 0) D2M8K2.u1272 from rfl, allE_node, arows1265, irow1273, arows1272]
  all_goals rfl

theorem atot1273 : totK PD2M8K2 D2M8K2.u1273 = [245750340552, 2449544572826, 6272561451486, 4570512544777, 686947595134, 18797058808, 0, 0] := by
  rw [show D2M8K2.u1273 = KTree.node D2M8K2.u1265 (nat_lit 2600802) (nat_lit 1490272098) (nat_lit 0) D2M8K2.u1272 from rfl, totK_node, atot1265, atot1272]
  decide +kernel

theorem arows1292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1292 = true := by
  rw [show D2M8K2.u1292 = KTree.node D2M8K2.u1284 (nat_lit 2624078) (nat_lit 3794609127) (nat_lit 0) D2M8K2.u1291 from rfl, allE_node, arows1284, irow1292, arows1291]
  all_goals rfl

theorem atot1292 : totK PD2M8K2 D2M8K2.u1292 = [1651237732455, 5834597484451, 5617011813058, 1326551780723, 55909369426, 0, 0, 0] := by
  rw [show D2M8K2.u1292 = KTree.node D2M8K2.u1284 (nat_lit 2624078) (nat_lit 3794609127) (nat_lit 0) D2M8K2.u1291 from rfl, totK_node, atot1284, atot1291]
  decide +kernel

theorem arows1307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1307 = true := by
  rw [show D2M8K2.u1307 = KTree.node D2M8K2.u1299 (nat_lit 2638490) (nat_lit 4100404273) (nat_lit 0) D2M8K2.u1306 from rfl, allE_node, arows1299, irow1307, arows1306]
  all_goals rfl

theorem atot1307 : totK PD2M8K2 D2M8K2.u1307 = [92934196222, 2350426557329, 6518846506081, 4597548483083, 684210414058, 19065934916, 0, 0] := by
  rw [show D2M8K2.u1307 = KTree.node D2M8K2.u1299 (nat_lit 2638490) (nat_lit 4100404273) (nat_lit 0) D2M8K2.u1306 from rfl, totK_node, atot1299, atot1306]
  decide +kernel

theorem arows1323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1323 = true := by
  rw [show D2M8K2.u1323 = KTree.node D2M8K2.u1315 (nat_lit 2701225) (nat_lit 908120066) (nat_lit 0) D2M8K2.u1322 from rfl, allE_node, arows1315, irow1323, arows1322]
  all_goals rfl

theorem atot1323 : totK PD2M8K2 D2M8K2.u1323 = [1574756246961, 5564754892932, 5592348780882, 1604793026401, 95540655422, 0, 0, 0] := by
  rw [show D2M8K2.u1323 = KTree.node D2M8K2.u1315 (nat_lit 2701225) (nat_lit 908120066) (nat_lit 0) D2M8K2.u1322 from rfl, totK_node, atot1315, atot1322]
  decide +kernel

theorem arows1338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1338 = true := by
  rw [show D2M8K2.u1338 = KTree.node D2M8K2.u1330 (nat_lit 2717361) (nat_lit 1808443868) (nat_lit 0) D2M8K2.u1337 from rfl, allE_node, arows1330, irow1338, arows1337]
  all_goals rfl

theorem atot1338 : totK PD2M8K2 D2M8K2.u1338 = [537563995491, 3509627914061, 6521673664903, 3495922166725, 336616682993, 2385942608, 0, 0] := by
  rw [show D2M8K2.u1338 = KTree.node D2M8K2.u1330 (nat_lit 2717361) (nat_lit 1808443868) (nat_lit 0) D2M8K2.u1337 from rfl, totK_node, atot1330, atot1337]
  decide +kernel

theorem arows1355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1355 = true := by
  rw [show D2M8K2.u1355 = KTree.node D2M8K2.u1347 (nat_lit 2736274) (nat_lit 4075430489) (nat_lit 0) D2M8K2.u1354 from rfl, allE_node, arows1347, irow1355, arows1354]
  all_goals rfl

theorem atot1355 : totK PD2M8K2 D2M8K2.u1355 = [0, 1713129277899, 6050864681644, 5481583337669, 1055060975520, 33020226125, 0, 0] := by
  rw [show D2M8K2.u1355 = KTree.node D2M8K2.u1347 (nat_lit 2736274) (nat_lit 4075430489) (nat_lit 0) D2M8K2.u1354 from rfl, totK_node, atot1347, atot1354]
  decide +kernel

theorem arows1370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1370 = true := by
  rw [show D2M8K2.u1370 = KTree.node D2M8K2.u1362 (nat_lit 2754770) (nat_lit 4063615147) (nat_lit 0) D2M8K2.u1369 from rfl, allE_node, arows1362, irow1370, arows1369]
  all_goals rfl

theorem atot1370 : totK PD2M8K2 D2M8K2.u1370 = [0, 1181412729800, 4869256893363, 5963455789358, 2050141125487, 158655580780, 1369150432, 0] := by
  rw [show D2M8K2.u1370 = KTree.node D2M8K2.u1362 (nat_lit 2754770) (nat_lit 4063615147) (nat_lit 0) D2M8K2.u1369 from rfl, totK_node, atot1362, atot1369]
  decide +kernel

theorem arows1386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1386 = true := by
  rw [show D2M8K2.u1386 = KTree.node D2M8K2.u1378 (nat_lit 2782450) (nat_lit 3938046735) (nat_lit 0) D2M8K2.u1385 from rfl, allE_node, arows1378, irow1386, arows1385]
  all_goals rfl

theorem atot1386 : totK PD2M8K2 D2M8K2.u1386 = [0, 834008456277, 4352054490942, 6636016546920, 2420338177690, 111664256654, 0, 0] := by
  rw [show D2M8K2.u1386 = KTree.node D2M8K2.u1378 (nat_lit 2782450) (nat_lit 3938046735) (nat_lit 0) D2M8K2.u1385 from rfl, totK_node, atot1378, atot1385]
  decide +kernel

theorem arows1401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1401 = true := by
  rw [show D2M8K2.u1401 = KTree.node D2M8K2.u1393 (nat_lit 2798518) (nat_lit 3482303441) (nat_lit 0) D2M8K2.u1400 from rfl, allE_node, arows1393, irow1401, arows1400]
  all_goals rfl

theorem atot1401 : totK PD2M8K2 D2M8K2.u1401 = [0, 1629635826015, 5765831312424, 5618591441402, 1366597980590, 58360019077, 0, 0] := by
  rw [show D2M8K2.u1401 = KTree.node D2M8K2.u1393 (nat_lit 2798518) (nat_lit 3482303441) (nat_lit 0) D2M8K2.u1400 from rfl, totK_node, atot1393, atot1400]
  decide +kernel

theorem arows1419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1419 = true := by
  rw [show D2M8K2.u1419 = KTree.node D2M8K2.u1411 (nat_lit 2836954) (nat_lit 2105558474) (nat_lit 0) D2M8K2.u1418 from rfl, allE_node, arows1411, irow1419, arows1418]
  all_goals rfl

theorem atot1419 : totK PD2M8K2 D2M8K2.u1419 = [0, 1189186924194, 4817852757469, 6000449217312, 2114557523372, 137532757213, 1166720416, 0] := by
  rw [show D2M8K2.u1419 = KTree.node D2M8K2.u1411 (nat_lit 2836954) (nat_lit 2105558474) (nat_lit 0) D2M8K2.u1418 from rfl, totK_node, atot1411, atot1418]
  decide +kernel

theorem arows1434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1434 = true := by
  rw [show D2M8K2.u1434 = KTree.node D2M8K2.u1426 (nat_lit 2858798) (nat_lit 3506040643) (nat_lit 0) D2M8K2.u1433 from rfl, allE_node, arows1426, irow1434, arows1433]
  all_goals rfl

theorem atot1434 : totK PD2M8K2 D2M8K2.u1434 = [0, 798159910373, 4179115028427, 6307447706902, 2747272748378, 282224266110, 5134755853, 0] := by
  rw [show D2M8K2.u1434 = KTree.node D2M8K2.u1426 (nat_lit 2858798) (nat_lit 3506040643) (nat_lit 0) D2M8K2.u1433 from rfl, totK_node, atot1426, atot1433]
  decide +kernel

theorem arows1450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1450 = true := by
  rw [show D2M8K2.u1450 = KTree.node D2M8K2.u1442 (nat_lit 2878279) (nat_lit 2327385968) (nat_lit 0) D2M8K2.u1449 from rfl, allE_node, arows1442, irow1450, arows1449]
  all_goals rfl

theorem atot1450 : totK PD2M8K2 D2M8K2.u1450 = [0, 1189558360385, 4803937598849, 6005810009292, 2130552666148, 136757966536, 1200365979, 0] := by
  rw [show D2M8K2.u1450 = KTree.node D2M8K2.u1442 (nat_lit 2878279) (nat_lit 2327385968) (nat_lit 0) D2M8K2.u1449 from rfl, totK_node, atot1442, atot1449]
  decide +kernel

theorem arows1465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1465 = true := by
  rw [show D2M8K2.u1465 = KTree.node D2M8K2.u1457 (nat_lit 2900210) (nat_lit 4005384254) (nat_lit 0) D2M8K2.u1464 from rfl, allE_node, arows1457, irow1465, arows1464]
  all_goals rfl

theorem atot1465 : totK PD2M8K2 D2M8K2.u1465 = [0, 825501190029, 4244356551313, 6252038450367, 2727280634975, 287617328647, 5163565574, 0] := by
  rw [show D2M8K2.u1465 = KTree.node D2M8K2.u1457 (nat_lit 2900210) (nat_lit 4005384254) (nat_lit 0) D2M8K2.u1464 from rfl, totK_node, atot1457, atot1464]
  decide +kernel

theorem arows1482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1482 = true := by
  rw [show D2M8K2.u1482 = KTree.node D2M8K2.u1474 (nat_lit 2956702) (nat_lit 3663598015) (nat_lit 0) D2M8K2.u1481 from rfl, allE_node, arows1474, irow1482, arows1481]
  all_goals rfl

theorem atot1482 : totK PD2M8K2 D2M8K2.u1482 = [0, 1284915497782, 5169215879804, 6076544948846, 1711973942257, 61267281524, 0, 0] := by
  rw [show D2M8K2.u1482 = KTree.node D2M8K2.u1474 (nat_lit 2956702) (nat_lit 3663598015) (nat_lit 0) D2M8K2.u1481 from rfl, totK_node, atot1474, atot1481]
  decide +kernel

theorem arows1497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1497 = true := by
  rw [show D2M8K2.u1497 = KTree.node D2M8K2.u1489 (nat_lit 2975974) (nat_lit 3721287516) (nat_lit 0) D2M8K2.u1496 from rfl, allE_node, arows1489, irow1497, arows1496]
  all_goals rfl

theorem atot1497 : totK PD2M8K2 D2M8K2.u1497 = [0, 92342479873, 1946548674086, 6044189454846, 5077411725839, 936549121004, 32664957003, 0] := by
  rw [show D2M8K2.u1497 = KTree.node D2M8K2.u1489 (nat_lit 2975974) (nat_lit 3721287516) (nat_lit 0) D2M8K2.u1496 from rfl, totK_node, atot1489, atot1496]
  decide +kernel

theorem arows1513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1513 = true := by
  rw [show D2M8K2.u1513 = KTree.node D2M8K2.u1505 (nat_lit 2996666) (nat_lit 3511244622) (nat_lit 0) D2M8K2.u1512 from rfl, allE_node, arows1505, irow1513, arows1512]
  all_goals rfl

theorem atot1513 : totK PD2M8K2 D2M8K2.u1513 = [0, 1698646649597, 6014926361548, 5569051265063, 1070747309760, 32650077886, 0, 0] := by
  rw [show D2M8K2.u1513 = KTree.node D2M8K2.u1505 (nat_lit 2996666) (nat_lit 3511244622) (nat_lit 0) D2M8K2.u1512 from rfl, totK_node, atot1505, atot1512]
  decide +kernel

theorem arows1528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1528 = true := by
  rw [show D2M8K2.u1528 = KTree.node D2M8K2.u1520 (nat_lit 3013746) (nat_lit 2999309062) (nat_lit 0) D2M8K2.u1527 from rfl, allE_node, arows1520, irow1528, arows1527]
  all_goals rfl

theorem atot1528 : totK PD2M8K2 D2M8K2.u1528 = [0, 334814008584, 3293700608751, 6945991798778, 3356549968994, 275524509557, 1369150432, 0] := by
  rw [show D2M8K2.u1528 = KTree.node D2M8K2.u1520 (nat_lit 3013746) (nat_lit 2999309062) (nat_lit 0) D2M8K2.u1527 from rfl, totK_node, atot1520, atot1527]
  decide +kernel

theorem arows1548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1548 = true := by
  rw [show D2M8K2.u1548 = KTree.node D2M8K2.u1540 (nat_lit 3075819) (nat_lit 3482221614) (nat_lit 0) D2M8K2.u1547 from rfl, allE_node, arows1540, irow1548, arows1547]
  all_goals rfl

theorem atot1548 : totK PD2M8K2 D2M8K2.u1548 = [0, 1598824971763, 5786227861664, 5659903725220, 1304031370677, 46592418318, 0, 0] := by
  rw [show D2M8K2.u1548 = KTree.node D2M8K2.u1540 (nat_lit 3075819) (nat_lit 3482221614) (nat_lit 0) D2M8K2.u1547 from rfl, totK_node, atot1540, atot1547]
  decide +kernel

theorem arows1563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1563 = true := by
  rw [show D2M8K2.u1563 = KTree.node D2M8K2.u1555 (nat_lit 3092969) (nat_lit 1549733194) (nat_lit 0) D2M8K2.u1562 from rfl, allE_node, arows1555, irow1563, arows1562]
  all_goals rfl

theorem atot1563 : totK PD2M8K2 D2M8K2.u1563 = [0, 414661219762, 3066820119238, 6475772191049, 3736598740039, 460232711689, 14222663156, 0] := by
  rw [show D2M8K2.u1563 = KTree.node D2M8K2.u1555 (nat_lit 3092969) (nat_lit 1549733194) (nat_lit 0) D2M8K2.u1562 from rfl, totK_node, atot1555, atot1562]
  decide +kernel

theorem arows1579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1579 = true := by
  rw [show D2M8K2.u1579 = KTree.node D2M8K2.u1571 (nat_lit 3114853) (nat_lit 1275912670) (nat_lit 0) D2M8K2.u1578 from rfl, allE_node, arows1571, irow1579, arows1578]
  all_goals rfl

theorem atot1579 : totK PD2M8K2 D2M8K2.u1579 = [0, 1352788905415, 5033687400325, 5678015521469, 2068938824761, 192455118918, 4574395652, 0] := by
  rw [show D2M8K2.u1579 = KTree.node D2M8K2.u1571 (nat_lit 3114853) (nat_lit 1275912670) (nat_lit 0) D2M8K2.u1578 from rfl, totK_node, atot1571, atot1578]
  decide +kernel

theorem arows1594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1594 = true := by
  rw [show D2M8K2.u1594 = KTree.node D2M8K2.u1586 (nat_lit 3131866) (nat_lit 3706278502) (nat_lit 0) D2M8K2.u1593 from rfl, allE_node, arows1586, irow1594, arows1593]
  all_goals rfl

theorem atot1594 : totK PD2M8K2 D2M8K2.u1594 = [0, 661179783291, 3705888795693, 6353123260427, 3181328247762, 362927011697, 9422004229, 0] := by
  rw [show D2M8K2.u1594 = KTree.node D2M8K2.u1586 (nat_lit 3131866) (nat_lit 3706278502) (nat_lit 0) D2M8K2.u1593 from rfl, totK_node, atot1586, atot1593]
  decide +kernel

theorem arows1611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1611 = true := by
  rw [show D2M8K2.u1611 = KTree.node D2M8K2.u1603 (nat_lit 3153050) (nat_lit 3868958215) (nat_lit 0) D2M8K2.u1610 from rfl, allE_node, arows1603, irow1611, arows1610]
  all_goals rfl

theorem atot1611 : totK PD2M8K2 D2M8K2.u1611 = [0, 1159456936068, 4529945841008, 5680172974131, 2528713889819, 295343735172, 8192806269, 0] := by
  rw [show D2M8K2.u1611 = KTree.node D2M8K2.u1603 (nat_lit 3153050) (nat_lit 3868958215) (nat_lit 0) D2M8K2.u1610 from rfl, totK_node, atot1603, atot1610]
  decide +kernel

theorem arows1626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1626 = true := by
  rw [show D2M8K2.u1626 = KTree.node D2M8K2.u1618 (nat_lit 3166939) (nat_lit 2238416565) (nat_lit 0) D2M8K2.u1625 from rfl, allE_node, arows1618, irow1626, arows1625]
  all_goals rfl

theorem atot1626 : totK PD2M8K2 D2M8K2.u1626 = [0, 848891489137, 4344342458681, 6458125141763, 2417608818929, 162568230629, 1138244013, 0] := by
  rw [show D2M8K2.u1626 = KTree.node D2M8K2.u1618 (nat_lit 3166939) (nat_lit 2238416565) (nat_lit 0) D2M8K2.u1625 from rfl, totK_node, atot1618, atot1625]
  decide +kernel

theorem arows1642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1642 = true := by
  rw [show D2M8K2.u1642 = KTree.node D2M8K2.u1634 (nat_lit 3194068) (nat_lit 3765632296) (nat_lit 0) D2M8K2.u1641 from rfl, allE_node, arows1634, irow1642, arows1641]
  all_goals rfl

theorem atot1642 : totK PD2M8K2 D2M8K2.u1642 = [0, 1015529940449, 4387256114305, 6038917662423, 2591988699331, 253292564948, 4977114383, 0] := by
  rw [show D2M8K2.u1642 = KTree.node D2M8K2.u1634 (nat_lit 3194068) (nat_lit 3765632296) (nat_lit 0) D2M8K2.u1641 from rfl, totK_node, atot1634, atot1641]
  decide +kernel

theorem arows1657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1657 = true := by
  rw [show D2M8K2.u1657 = KTree.node D2M8K2.u1649 (nat_lit 3211375) (nat_lit 1478740401) (nat_lit 0) D2M8K2.u1656 from rfl, allE_node, arows1649, irow1657, arows1656]
  all_goals rfl

theorem atot1657 : totK PD2M8K2 D2M8K2.u1657 = [0, 1000987240365, 4503333602242, 6177084194742, 2485862404344, 190269000975, 1310285577, 0] := by
  rw [show D2M8K2.u1657 = KTree.node D2M8K2.u1649 (nat_lit 3211375) (nat_lit 1478740401) (nat_lit 0) D2M8K2.u1656 from rfl, totK_node, atot1649, atot1656]
  decide +kernel

theorem arows1675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1675 = true := by
  rw [show D2M8K2.u1675 = KTree.node D2M8K2.u1667 (nat_lit 3231382) (nat_lit 3553329980) (nat_lit 0) D2M8K2.u1674 from rfl, allE_node, arows1667, irow1675, arows1674]
  all_goals rfl

theorem atot1675 : totK PD2M8K2 D2M8K2.u1675 = [0, 0, 1791473639162, 6239454397219, 5223083537474, 919650801618, 32931563536, 0] := by
  rw [show D2M8K2.u1675 = KTree.node D2M8K2.u1667 (nat_lit 3231382) (nat_lit 3553329980) (nat_lit 0) D2M8K2.u1674 from rfl, totK_node, atot1667, atot1674]
  decide +kernel

theorem arows1690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1690 = true := by
  rw [show D2M8K2.u1690 = KTree.node D2M8K2.u1682 (nat_lit 3248359) (nat_lit 2353804635) (nat_lit 0) D2M8K2.u1689 from rfl, allE_node, arows1682, irow1690, arows1689]
  all_goals rfl

theorem atot1690 : totK PD2M8K2 D2M8K2.u1690 = [0, 0, 1657034836166, 5818289581732, 5435533425273, 1079560028540, 39550270370, 0] := by
  rw [show D2M8K2.u1690 = KTree.node D2M8K2.u1682 (nat_lit 3248359) (nat_lit 2353804635) (nat_lit 0) D2M8K2.u1689 from rfl, totK_node, atot1682, atot1689]
  decide +kernel

theorem arows1706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1706 = true := by
  rw [show D2M8K2.u1706 = KTree.node D2M8K2.u1698 (nat_lit 3267629) (nat_lit 1690571457) (nat_lit 0) D2M8K2.u1705 from rfl, allE_node, arows1698, irow1706, arows1705]
  all_goals rfl

theorem atot1706 : totK PD2M8K2 D2M8K2.u1706 = [0, 0, 491039836135, 3687886065180, 6676416609249, 2897322050694, 267632442297, 1369150432] := by
  rw [show D2M8K2.u1706 = KTree.node D2M8K2.u1698 (nat_lit 3267629) (nat_lit 1690571457) (nat_lit 0) D2M8K2.u1705 from rfl, totK_node, atot1698, atot1705]
  decide +kernel

theorem arows1721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1721 = true := by
  rw [show D2M8K2.u1721 = KTree.node D2M8K2.u1713 (nat_lit 3333396) (nat_lit 3186693439) (nat_lit 0) D2M8K2.u1720 from rfl, allE_node, arows1713, irow1721, arows1720]
  all_goals rfl

theorem atot1721 : totK PD2M8K2 D2M8K2.u1721 = [0, 0, 1927685108315, 6275241698895, 5098329098173, 895370399380, 33020449330, 0] := by
  rw [show D2M8K2.u1721 = KTree.node D2M8K2.u1713 (nat_lit 3333396) (nat_lit 3186693439) (nat_lit 0) D2M8K2.u1720 from rfl, totK_node, atot1713, atot1720]
  decide +kernel

theorem arows1738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1738 = true := by
  rw [show D2M8K2.u1738 = KTree.node D2M8K2.u1730 (nat_lit 3373835) (nat_lit 2127296640) (nat_lit 0) D2M8K2.u1737 from rfl, allE_node, arows1730, irow1738, arows1737]
  all_goals rfl

theorem atot1738 : totK PD2M8K2 D2M8K2.u1738 = [0, 0, 1916457618947, 6306055425208, 5164406303295, 868376680114, 31803026613, 0] := by
  rw [show D2M8K2.u1738 = KTree.node D2M8K2.u1730 (nat_lit 3373835) (nat_lit 2127296640) (nat_lit 0) D2M8K2.u1737 from rfl, totK_node, atot1730, atot1737]
  decide +kernel

theorem arows1753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1753 = true := by
  rw [show D2M8K2.u1753 = KTree.node D2M8K2.u1745 (nat_lit 3411265) (nat_lit 1490793551) (nat_lit 0) D2M8K2.u1752 from rfl, allE_node, arows1745, irow1753, arows1752]
  all_goals rfl

theorem atot1753 : totK PD2M8K2 D2M8K2.u1753 = [0, 0, 1782124144152, 6170705501004, 5267733501470, 914846034470, 32517432587, 0] := by
  rw [show D2M8K2.u1753 = KTree.node D2M8K2.u1745 (nat_lit 3411265) (nat_lit 1490793551) (nat_lit 0) D2M8K2.u1752 from rfl, totK_node, atot1745, atot1752]
  decide +kernel

theorem arows1769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1769 = true := by
  rw [show D2M8K2.u1769 = KTree.node D2M8K2.u1761 (nat_lit 3451530) (nat_lit 3029610563) (nat_lit 0) D2M8K2.u1768 from rfl, allE_node, arows1761, irow1769, arows1768]
  all_goals rfl

theorem atot1769 : totK PD2M8K2 D2M8K2.u1769 = [0, 0, 1884613387020, 6384448861420, 5281767583218, 800757378150, 16583824438, 0] := by
  rw [show D2M8K2.u1769 = KTree.node D2M8K2.u1761 (nat_lit 3451530) (nat_lit 3029610563) (nat_lit 0) D2M8K2.u1768 from rfl, totK_node, atot1761, atot1768]
  decide +kernel

theorem arows1784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1784 = true := by
  rw [show D2M8K2.u1784 = KTree.node D2M8K2.u1776 (nat_lit 3991104) (nat_lit 3677347549) (nat_lit 0) D2M8K2.u1783 from rfl, allE_node, arows1776, irow1784, arows1783]
  all_goals rfl

theorem atot1784 : totK PD2M8K2 D2M8K2.u1784 = [0, 1636922335308, 5736831952914, 5359454526101, 1352544584054, 215723930195, 17014456371, 0] := by
  rw [show D2M8K2.u1784 = KTree.node D2M8K2.u1776 (nat_lit 3991104) (nat_lit 3677347549) (nat_lit 0) D2M8K2.u1783 from rfl, totK_node, atot1776, atot1783]
  decide +kernel

theorem arows1803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1803 = true := by
  rw [show D2M8K2.u1803 = KTree.node D2M8K2.u1795 (nat_lit 4005337) (nat_lit 1514506762) (nat_lit 0) D2M8K2.u1802 from rfl, allE_node, arows1795, irow1803, arows1802]
  all_goals rfl

theorem atot1803 : totK PD2M8K2 D2M8K2.u1803 = [0, 392661349882, 3377740336315, 6850485497257, 3310272584895, 272658312056, 1369150432, 0] := by
  rw [show D2M8K2.u1803 = KTree.node D2M8K2.u1795 (nat_lit 4005337) (nat_lit 1514506762) (nat_lit 0) D2M8K2.u1802 from rfl, totK_node, atot1795, atot1802]
  decide +kernel

theorem arows1818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1818 = true := by
  rw [show D2M8K2.u1818 = KTree.node D2M8K2.u1810 (nat_lit 4031689) (nat_lit 1426063987) (nat_lit 0) D2M8K2.u1817 from rfl, allE_node, arows1810, irow1818, arows1817]
  all_goals rfl

theorem atot1818 : totK PD2M8K2 D2M8K2.u1818 = [0, 1662554230251, 5729489854998, 5574368183847, 1460717846189, 70359145423, 0, 0] := by
  rw [show D2M8K2.u1818 = KTree.node D2M8K2.u1810 (nat_lit 4031689) (nat_lit 1426063987) (nat_lit 0) D2M8K2.u1817 from rfl, totK_node, atot1810, atot1817]
  decide +kernel

theorem arows1834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1834 = true := by
  rw [show D2M8K2.u1834 = KTree.node D2M8K2.u1826 (nat_lit 4057685) (nat_lit 2377552506) (nat_lit 0) D2M8K2.u1833 from rfl, allE_node, arows1826, irow1834, arows1833]
  all_goals rfl

theorem atot1834 : totK PD2M8K2 D2M8K2.u1834 = [0, 417704280416, 3138027266458, 6515009563878, 3899227427675, 454927043662, 6575010705, 0] := by
  rw [show D2M8K2.u1834 = KTree.node D2M8K2.u1826 (nat_lit 4057685) (nat_lit 2377552506) (nat_lit 0) D2M8K2.u1833 from rfl, totK_node, atot1826, atot1833]
  decide +kernel

theorem arows1849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1849 = true := by
  rw [show D2M8K2.u1849 = KTree.node D2M8K2.u1841 (nat_lit 4073006) (nat_lit 2627248755) (nat_lit 0) D2M8K2.u1848 from rfl, allE_node, arows1841, irow1849, arows1848]
  all_goals rfl

theorem atot1849 : totK PD2M8K2 D2M8K2.u1849 = [0, 1689392225582, 5884274992355, 5562663640286, 1258463499360, 49082224604, 0, 0] := by
  rw [show D2M8K2.u1849 = KTree.node D2M8K2.u1841 (nat_lit 4073006) (nat_lit 2627248755) (nat_lit 0) D2M8K2.u1848 from rfl, totK_node, atot1841, atot1848]
  decide +kernel

theorem arows1866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1866 = true := by
  rw [show D2M8K2.u1866 = KTree.node D2M8K2.u1858 (nat_lit 4092105) (nat_lit 1730719016) (nat_lit 0) D2M8K2.u1865 from rfl, allE_node, arows1858, irow1866, arows1865]
  all_goals rfl

theorem atot1866 : totK PD2M8K2 D2M8K2.u1866 = [0, 0, 2178483999295, 6667022710397, 4588408106782, 658851886053, 18797058808, 0] := by
  rw [show D2M8K2.u1866 = KTree.node D2M8K2.u1858 (nat_lit 4092105) (nat_lit 1730719016) (nat_lit 0) D2M8K2.u1865 from rfl, totK_node, atot1858, atot1865]
  decide +kernel

theorem arows1881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1881 = true := by
  rw [show D2M8K2.u1881 = KTree.node D2M8K2.u1873 (nat_lit 4152867) (nat_lit 3687294742) (nat_lit 0) D2M8K2.u1880 from rfl, allE_node, arows1873, irow1881, arows1880]
  all_goals rfl

theorem atot1881 : totK PD2M8K2 D2M8K2.u1881 = [0, 1545881644484, 5552693205883, 5613625681873, 1585621193745, 81260203616, 0, 0] := by
  rw [show D2M8K2.u1881 = KTree.node D2M8K2.u1873 (nat_lit 4152867) (nat_lit 3687294742) (nat_lit 0) D2M8K2.u1880 from rfl, totK_node, atot1873, atot1880]
  decide +kernel

theorem arows1897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1897 = true := by
  rw [show D2M8K2.u1897 = KTree.node D2M8K2.u1889 (nat_lit 4170535) (nat_lit 2391034705) (nat_lit 0) D2M8K2.u1896 from rfl, allE_node, arows1889, irow1897, arows1896]
  all_goals rfl

theorem atot1897 : totK PD2M8K2 D2M8K2.u1897 = [0, 435809923056, 3593381959863, 6924244563105, 3080064470434, 213814958016, 1138244013, 0] := by
  rw [show D2M8K2.u1897 = KTree.node D2M8K2.u1889 (nat_lit 4170535) (nat_lit 2391034705) (nat_lit 0) D2M8K2.u1896 from rfl, totK_node, atot1889, atot1896]
  decide +kernel

theorem arows1912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1912 = true := by
  rw [show D2M8K2.u1912 = KTree.node D2M8K2.u1904 (nat_lit 4193700) (nat_lit 3185211542) (nat_lit 0) D2M8K2.u1911 from rfl, allE_node, arows1904, irow1912, arows1911]
  all_goals rfl

theorem atot1912 : totK PD2M8K2 D2M8K2.u1912 = [0, 1526487146035, 5219455583955, 5438458677710, 1975733248827, 230640292269, 4977114383, 0] := by
  rw [show D2M8K2.u1912 = KTree.node D2M8K2.u1904 (nat_lit 4193700) (nat_lit 3185211542) (nat_lit 0) D2M8K2.u1911 from rfl, totK_node, atot1904, atot1911]
  decide +kernel

theorem arows1930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1930 = true := by
  rw [show D2M8K2.u1930 = KTree.node D2M8K2.u1922 (nat_lit 4210898) (nat_lit 3701083268) (nat_lit 0) D2M8K2.u1929 from rfl, allE_node, arows1922, irow1930, arows1929]
  all_goals rfl

theorem atot1930 : totK PD2M8K2 D2M8K2.u1930 = [0, 463775079688, 3336056726094, 6500849039802, 3648321226418, 401698801376, 6190125969, 0] := by
  rw [show D2M8K2.u1930 = KTree.node D2M8K2.u1922 (nat_lit 4210898) (nat_lit 3701083268) (nat_lit 0) D2M8K2.u1929 from rfl, totK_node, atot1922, atot1929]
  decide +kernel

theorem arows1945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1945 = true := by
  rw [show D2M8K2.u1945 = KTree.node D2M8K2.u1937 (nat_lit 4480762) (nat_lit 3869045902) (nat_lit 0) D2M8K2.u1944 from rfl, allE_node, arows1937, irow1945, arows1944]
  all_goals rfl

theorem atot1945 : totK PD2M8K2 D2M8K2.u1945 = [0, 1205065575347, 4763331309197, 5717026317127, 2376668949732, 342865036601, 13786494048, 0] := by
  rw [show D2M8K2.u1945 = KTree.node D2M8K2.u1937 (nat_lit 4480762) (nat_lit 3869045902) (nat_lit 0) D2M8K2.u1944 from rfl, totK_node, atot1937, atot1944]
  decide +kernel

theorem arows1961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1961 = true := by
  rw [show D2M8K2.u1961 = KTree.node D2M8K2.u1953 (nat_lit 4498694) (nat_lit 3759565223) (nat_lit 0) D2M8K2.u1960 from rfl, allE_node, arows1953, irow1961, arows1960]
  all_goals rfl

theorem atot1961 : totK PD2M8K2 D2M8K2.u1961 = [0, 824665215328, 4131867979019, 6331486080203, 2692726430726, 237561039321, 1369150432, 0] := by
  rw [show D2M8K2.u1961 = KTree.node D2M8K2.u1953 (nat_lit 4498694) (nat_lit 3759565223) (nat_lit 0) D2M8K2.u1960 from rfl, totK_node, atot1953, atot1960]
  decide +kernel

theorem arows1976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1976 = true := by
  rw [show D2M8K2.u1976 = KTree.node D2M8K2.u1968 (nat_lit 4526011) (nat_lit 2124549723) (nat_lit 0) D2M8K2.u1975 from rfl, allE_node, arows1968, irow1976, arows1975]
  all_goals rfl

theorem atot1976 : totK PD2M8K2 D2M8K2.u1976 = [0, 1166537124850, 4810862747959, 6131581282959, 2190760628918, 116476399482, 0, 0] := by
  rw [show D2M8K2.u1976 = KTree.node D2M8K2.u1968 (nat_lit 4526011) (nat_lit 2124549723) (nat_lit 0) D2M8K2.u1975 from rfl, totK_node, atot1968, atot1975]
  decide +kernel

theorem arows1993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1993 = true := by
  rw [show D2M8K2.u1993 = KTree.node D2M8K2.u1985 (nat_lit 4545944) (nat_lit 3613870797) (nat_lit 0) D2M8K2.u1992 from rfl, allE_node, arows1985, irow1993, arows1992]
  all_goals rfl

theorem atot1993 : totK PD2M8K2 D2M8K2.u1993 = [0, 496343452152, 3409294717637, 6497537029950, 3619625291553, 426420287897, 6634014755, 0] := by
  rw [show D2M8K2.u1993 = KTree.node D2M8K2.u1985 (nat_lit 4545944) (nat_lit 3613870797) (nat_lit 0) D2M8K2.u1992 from rfl, totK_node, atot1985, atot1992]
  decide +kernel

theorem arows2008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2008 = true := by
  rw [show D2M8K2.u2008 = KTree.node D2M8K2.u2000 (nat_lit 4608506) (nat_lit 3995047236) (nat_lit 0) D2M8K2.u2007 from rfl, allE_node, arows2000, irow2008, arows2007]
  all_goals rfl

theorem atot2008 : totK PD2M8K2 D2M8K2.u2008 = [0, 1506038846336, 5469989467898, 5710272752187, 1685557121481, 91682070631, 0, 0] := by
  rw [show D2M8K2.u2008 = KTree.node D2M8K2.u2000 (nat_lit 4608506) (nat_lit 3995047236) (nat_lit 0) D2M8K2.u2007 from rfl, totK_node, atot2000, atot2007]
  decide +kernel

theorem arows2024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2024 = true := by
  rw [show D2M8K2.u2024 = KTree.node D2M8K2.u2016 (nat_lit 4625146) (nat_lit 3783264946) (nat_lit 0) D2M8K2.u2023 from rfl, allE_node, arows2016, irow2024, arows2023]
  all_goals rfl

theorem atot2024 : totK PD2M8K2 D2M8K2.u2024 = [0, 601477597467, 3635845014210, 6470808987277, 3309146701581, 321678084209, 2410950632, 0] := by
  rw [show D2M8K2.u2024 = KTree.node D2M8K2.u2016 (nat_lit 4625146) (nat_lit 3783264946) (nat_lit 0) D2M8K2.u2023 from rfl, totK_node, atot2016, atot2023]
  decide +kernel

theorem arows2039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2039 = true := by
  rw [show D2M8K2.u2039 = KTree.node D2M8K2.u2031 (nat_lit 4645845) (nat_lit 1733370660) (nat_lit 0) D2M8K2.u2038 from rfl, allE_node, arows2031, irow2039, arows2038]
  all_goals rfl

theorem atot2039 : totK PD2M8K2 D2M8K2.u2039 = [0, 1034528657818, 4232653590510, 5686003083114, 2857460246031, 427848883581, 16654984284, 0] := by
  rw [show D2M8K2.u2039 = KTree.node D2M8K2.u2031 (nat_lit 4645845) (nat_lit 1733370660) (nat_lit 0) D2M8K2.u2038 from rfl, totK_node, atot2031, atot2038]
  decide +kernel

theorem arows2061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2061 = true := by
  rw [show D2M8K2.u2061 = KTree.node D2M8K2.u2053 (nat_lit 4659714) (nat_lit 3303510607) (nat_lit 0) D2M8K2.u2060 from rfl, allE_node, arows2053, irow2061, arows2060]
  all_goals rfl

theorem atot2061 : totK PD2M8K2 D2M8K2.u2061 = [0, 947355682671, 4499358084647, 6295163334664, 2352097063251, 167757895637, 1138244013, 0] := by
  rw [show D2M8K2.u2061 = KTree.node D2M8K2.u2053 (nat_lit 4659714) (nat_lit 3303510607) (nat_lit 0) D2M8K2.u2060 from rfl, totK_node, atot2053, atot2060]
  decide +kernel

theorem arows2076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2076 = true := by
  rw [show D2M8K2.u2076 = KTree.node D2M8K2.u2068 (nat_lit 4686932) (nat_lit 3035596756) (nat_lit 0) D2M8K2.u2075 from rfl, allE_node, arows2068, irow2076, arows2075]
  all_goals rfl

theorem atot2076 : totK PD2M8K2 D2M8K2.u2076 = [0, 922805259068, 4211017411060, 6159437203865, 2765083323601, 278209111759, 4977114383, 0] := by
  rw [show D2M8K2.u2076 = KTree.node D2M8K2.u2068 (nat_lit 4686932) (nat_lit 3035596756) (nat_lit 0) D2M8K2.u2075 from rfl, totK_node, atot2068, atot2075]
  decide +kernel

theorem arows2092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2092 = true := by
  rw [show D2M8K2.u2092 = KTree.node D2M8K2.u2084 (nat_lit 4704341) (nat_lit 2301362647) (nat_lit 0) D2M8K2.u2091 from rfl, allE_node, arows2084, irow2092, arows2091]
  all_goals rfl

theorem atot2092 : totK PD2M8K2 D2M8K2.u2092 = [0, 1070669122766, 4630609680671, 6116258395208, 2417576547362, 191264720662, 1310285577, 0] := by
  rw [show D2M8K2.u2092 = KTree.node D2M8K2.u2084 (nat_lit 4704341) (nat_lit 2301362647) (nat_lit 0) D2M8K2.u2091 from rfl, totK_node, atot2084, atot2091]
  decide +kernel

theorem arows2107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2107 = true := by
  rw [show D2M8K2.u2107 = KTree.node D2M8K2.u2099 (nat_lit 4725254) (nat_lit 4125181146) (nat_lit 0) D2M8K2.u2106 from rfl, allE_node, arows2099, irow2107, arows2106]
  all_goals rfl

theorem atot2107 : totK PD2M8K2 D2M8K2.u2107 = [0, 736522448081, 3589814010905, 5958206228233, 3562397315681, 554739898519, 18783708550, 0] := by
  rw [show D2M8K2.u2107 = KTree.node D2M8K2.u2099 (nat_lit 4725254) (nat_lit 4125181146) (nat_lit 0) D2M8K2.u2106 from rfl, totK_node, atot2099, atot2106]
  decide +kernel

theorem arows2124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2124 = true := by
  rw [show D2M8K2.u2124 = KTree.node D2M8K2.u2116 (nat_lit 4991308) (nat_lit 3867017944) (nat_lit 0) D2M8K2.u2123 from rfl, allE_node, arows2116, irow2124, arows2123]
  all_goals rfl

theorem atot2124 : totK PD2M8K2 D2M8K2.u2124 = [0, 1287841965954, 5270273930632, 6003980380708, 1622805135082, 72413804504, 0, 0] := by
  rw [show D2M8K2.u2124 = KTree.node D2M8K2.u2116 (nat_lit 4991308) (nat_lit 3867017944) (nat_lit 0) D2M8K2.u2123 from rfl, totK_node, atot2116, atot2123]
  decide +kernel

theorem arows2139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2139 = true := by
  rw [show D2M8K2.u2139 = KTree.node D2M8K2.u2131 (nat_lit 5012220) (nat_lit 3168264063) (nat_lit 0) D2M8K2.u2138 from rfl, allE_node, arows2131, irow2139, arows2138]
  all_goals rfl

theorem atot2139 : totK PD2M8K2 D2M8K2.u2139 = [0, 586310880811, 3571990179352, 6581702424031, 3275833700600, 282409521591, 1369150432, 0] := by
  rw [show D2M8K2.u2139 = KTree.node D2M8K2.u2131 (nat_lit 5012220) (nat_lit 3168264063) (nat_lit 0) D2M8K2.u2138 from rfl, totK_node, atot2131, atot2138]
  decide +kernel

theorem arows2155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2155 = true := by
  rw [show D2M8K2.u2155 = KTree.node D2M8K2.u2147 (nat_lit 5032461) (nat_lit 1159574512) (nat_lit 0) D2M8K2.u2154 from rfl, allE_node, arows2147, irow2155, arows2154]
  all_goals rfl

theorem atot2155 : totK PD2M8K2 D2M8K2.u2155 = [0, 1072806435095, 4917933323353, 6310991864409, 2018953472721, 105111894130, 0, 0] := by
  rw [show D2M8K2.u2155 = KTree.node D2M8K2.u2147 (nat_lit 5032461) (nat_lit 1159574512) (nat_lit 0) D2M8K2.u2154 from rfl, totK_node, atot2147, atot2154]
  decide +kernel

theorem arows2170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2170 = true := by
  rw [show D2M8K2.u2170 = KTree.node D2M8K2.u2162 (nat_lit 5061467) (nat_lit 2675870981) (nat_lit 0) D2M8K2.u2169 from rfl, allE_node, arows2162, irow2170, arows2169]
  all_goals rfl

theorem atot2170 : totK PD2M8K2 D2M8K2.u2170 = [0, 1234168024777, 4750186488676, 5786971002568, 2419483262892, 225094014191, 1415142070, 0] := by
  rw [show D2M8K2.u2170 = KTree.node D2M8K2.u2162 (nat_lit 5061467) (nat_lit 2675870981) (nat_lit 0) D2M8K2.u2169 from rfl, totK_node, atot2162, atot2169]
  decide +kernel

theorem arows2188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2188 = true := by
  rw [show D2M8K2.u2188 = KTree.node D2M8K2.u2180 (nat_lit 5079173) (nat_lit 2339102798) (nat_lit 0) D2M8K2.u2187 from rfl, allE_node, arows2180, irow2188, arows2187]
  all_goals rfl

theorem atot2188 : totK PD2M8K2 D2M8K2.u2188 = [0, 751044334138, 4144030699675, 6523022457330, 2693144775115, 197027246390, 1206465782, 0] := by
  rw [show D2M8K2.u2188 = KTree.node D2M8K2.u2180 (nat_lit 5079173) (nat_lit 2339102798) (nat_lit 0) D2M8K2.u2187 from rfl, totK_node, atot2180, atot2187]
  decide +kernel

theorem arows2203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2203 = true := by
  rw [show D2M8K2.u2203 = KTree.node D2M8K2.u2195 (nat_lit 5101112) (nat_lit 3588980262) (nat_lit 0) D2M8K2.u2202 from rfl, allE_node, arows2195, irow2203, arows2202]
  all_goals rfl

theorem atot2203 : totK PD2M8K2 D2M8K2.u2203 = [0, 846988453904, 3748423211112, 5852384529486, 3257596748403, 493880448981, 17590593026, 0] := by
  rw [show D2M8K2.u2203 = KTree.node D2M8K2.u2195 (nat_lit 5101112) (nat_lit 3588980262) (nat_lit 0) D2M8K2.u2202 from rfl, totK_node, atot2195, atot2202]
  decide +kernel

theorem arows2219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2219 = true := by
  rw [show D2M8K2.u2219 = KTree.node D2M8K2.u2211 (nat_lit 5117954) (nat_lit 3601791850) (nat_lit 0) D2M8K2.u2218 from rfl, allE_node, arows2211, irow2219, arows2218]
  all_goals rfl

theorem atot2219 : totK PD2M8K2 D2M8K2.u2219 = [0, 1138735407626, 4803422188458, 6026981313281, 2215913350357, 167011866463, 1239866073, 0] := by
  rw [show D2M8K2.u2219 = KTree.node D2M8K2.u2211 (nat_lit 5117954) (nat_lit 3601791850) (nat_lit 0) D2M8K2.u2218 from rfl, totK_node, atot2211, atot2218]
  decide +kernel

theorem arows2234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2234 = true := by
  rw [show D2M8K2.u2234 = KTree.node D2M8K2.u2226 (nat_lit 5138023) (nat_lit 1931367881) (nat_lit 0) D2M8K2.u2233 from rfl, allE_node, arows2226, irow2234, arows2233]
  all_goals rfl

theorem atot2234 : totK PD2M8K2 D2M8K2.u2234 = [0, 769924568502, 3641631652282, 5967982877195, 3356831841823, 504144254219, 17826068843, 0] := by
  rw [show D2M8K2.u2234 = KTree.node D2M8K2.u2226 (nat_lit 5138023) (nat_lit 1931367881) (nat_lit 0) D2M8K2.u2233 from rfl, totK_node, atot2226, atot2233]
  decide +kernel

theorem arows2251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2251 = true := by
  rw [show D2M8K2.u2251 = KTree.node D2M8K2.u2243 (nat_lit 5153877) (nat_lit 1734347021) (nat_lit 0) D2M8K2.u2250 from rfl, allE_node, arows2243, irow2251, arows2250]
  all_goals rfl

theorem atot2251 : totK PD2M8K2 D2M8K2.u2251 = [0, 1332481307193, 5345293175206, 5963784475128, 1630726699426, 71758298328, 0, 0] := by
  rw [show D2M8K2.u2251 = KTree.node D2M8K2.u2243 (nat_lit 5153877) (nat_lit 1734347021) (nat_lit 0) D2M8K2.u2250 from rfl, totK_node, atot2243, atot2250]
  decide +kernel

theorem arows2266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2266 = true := by
  rw [show D2M8K2.u2266 = KTree.node D2M8K2.u2258 (nat_lit 5174610) (nat_lit 3480840810) (nat_lit 0) D2M8K2.u2265 from rfl, allE_node, arows2258, irow2266, arows2265]
  all_goals rfl

theorem atot2266 : totK PD2M8K2 D2M8K2.u2266 = [0, 437509666450, 3153084590436, 6511774989375, 3694414035055, 414570013515, 6115358396, 0] := by
  rw [show D2M8K2.u2266 = KTree.node D2M8K2.u2258 (nat_lit 5174610) (nat_lit 3480840810) (nat_lit 0) D2M8K2.u2265 from rfl, totK_node, atot2258, atot2265]
  decide +kernel

theorem arows2282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2282 = true := by
  rw [show D2M8K2.u2282 = KTree.node D2M8K2.u2274 (nat_lit 5487304) (nat_lit 2358948951) (nat_lit 0) D2M8K2.u2281 from rfl, allE_node, arows2274, irow2282, arows2281]
  all_goals rfl

theorem atot2282 : totK PD2M8K2 D2M8K2.u2282 = [0, 1594108439370, 5843768744658, 5679702377933, 1179342705751, 36248923471, 0, 0] := by
  rw [show D2M8K2.u2282 = KTree.node D2M8K2.u2274 (nat_lit 5487304) (nat_lit 2358948951) (nat_lit 0) D2M8K2.u2281 from rfl, totK_node, atot2274, atot2281]
  decide +kernel

theorem arows2297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2297 = true := by
  rw [show D2M8K2.u2297 = KTree.node D2M8K2.u2289 (nat_lit 5506590) (nat_lit 3835758609) (nat_lit 0) D2M8K2.u2296 from rfl, allE_node, arows2289, irow2297, arows2296]
  all_goals rfl

theorem atot2297 : totK PD2M8K2 D2M8K2.u2297 = [0, 430753227105, 3345281163024, 6761130499478, 3450716588391, 302759396490, 1369150432, 0] := by
  rw [show D2M8K2.u2297 = KTree.node D2M8K2.u2289 (nat_lit 5506590) (nat_lit 3835758609) (nat_lit 0) D2M8K2.u2296 from rfl, totK_node, atot2289, atot2296]
  decide +kernel

theorem arows2316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2316 = true := by
  rw [show D2M8K2.u2316 = KTree.node D2M8K2.u2308 (nat_lit 5527971) (nat_lit 1162029249) (nat_lit 136) D2M8K2.u2315 from rfl, allE_node, arows2308, irow2316, arows2315]
  all_goals rfl

theorem atot2316 : totK PD2M8K2 D2M8K2.u2316 = [0, 1235678052922, 5086141830233, 6143420175443, 1948591404407, 91884135291, 0, 0] := by
  rw [show D2M8K2.u2316 = KTree.node D2M8K2.u2308 (nat_lit 5527971) (nat_lit 1162029249) (nat_lit 136) D2M8K2.u2315 from rfl, totK_node, atot2308, atot2315]
  decide +kernel

theorem arows2331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2331 = true := by
  rw [show D2M8K2.u2331 = KTree.node D2M8K2.u2323 (nat_lit 5554292) (nat_lit 2983399814) (nat_lit 0) D2M8K2.u2330 from rfl, allE_node, arows2323, irow2331, arows2330]
  all_goals rfl

theorem atot2331 : totK PD2M8K2 D2M8K2.u2331 = [0, 609097071523, 3220661192764, 6041134034911, 3995142107594, 615450165862, 12407785584, 0] := by
  rw [show D2M8K2.u2331 = KTree.node D2M8K2.u2323 (nat_lit 5554292) (nat_lit 2983399814) (nat_lit 0) D2M8K2.u2330 from rfl, totK_node, atot2323, atot2330]
  decide +kernel

theorem arows2347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2347 = true := by
  rw [show D2M8K2.u2347 = KTree.node D2M8K2.u2339 (nat_lit 5571419) (nat_lit 2600224738) (nat_lit 0) D2M8K2.u2346 from rfl, allE_node, arows2339, irow2347, arows2346]
  all_goals rfl

theorem atot2347 : totK PD2M8K2 D2M8K2.u2347 = [0, 1380296729021, 5343842768735, 5890476395197, 1714437926123, 83494733089, 0, 0] := by
  rw [show D2M8K2.u2347 = KTree.node D2M8K2.u2339 (nat_lit 5571419) (nat_lit 2600224738) (nat_lit 0) D2M8K2.u2346 from rfl, totK_node, atot2339, atot2346]
  decide +kernel

theorem arows2362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2362 = true := by
  rw [show D2M8K2.u2362 = KTree.node D2M8K2.u2354 (nat_lit 5587810) (nat_lit 2588681854) (nat_lit 0) D2M8K2.u2361 from rfl, allE_node, arows2354, irow2362, arows2361]
  all_goals rfl

theorem atot2362 : totK PD2M8K2 D2M8K2.u2362 = [0, 410566095411, 3198546320977, 6550455878809, 3725491344148, 416605205530, 6601594569, 0] := by
  rw [show D2M8K2.u2362 = KTree.node D2M8K2.u2354 (nat_lit 5587810) (nat_lit 2588681854) (nat_lit 0) D2M8K2.u2361 from rfl, totK_node, atot2354, atot2361]
  decide +kernel

theorem arows2379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2379 = true := by
  rw [show D2M8K2.u2379 = KTree.node D2M8K2.u2371 (nat_lit 5611976) (nat_lit 3687855684) (nat_lit 0) D2M8K2.u2378 from rfl, allE_node, arows2371, irow2379, arows2378]
  all_goals rfl

theorem atot2379 : totK PD2M8K2 D2M8K2.u2379 = [0, 1579356173818, 5637238802550, 5700622288160, 1492909986041, 61823278865, 0, 0] := by
  rw [show D2M8K2.u2379 = KTree.node D2M8K2.u2371 (nat_lit 5611976) (nat_lit 3687855684) (nat_lit 0) D2M8K2.u2378 from rfl, totK_node, atot2371, atot2378]
  decide +kernel

theorem arows2394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2394 = true := by
  rw [show D2M8K2.u2394 = KTree.node D2M8K2.u2386 (nat_lit 5631472) (nat_lit 1694802602) (nat_lit 0) D2M8K2.u2393 from rfl, allE_node, arows2386, irow2394, arows2393]
  all_goals rfl

theorem atot2394 : totK PD2M8K2 D2M8K2.u2394 = [0, 418266149227, 3063665179447, 6461548560091, 3956090542611, 448675248556, 6665697270, 0] := by
  rw [show D2M8K2.u2394 = KTree.node D2M8K2.u2386 (nat_lit 5631472) (nat_lit 1694802602) (nat_lit 0) D2M8K2.u2393 from rfl, totK_node, atot2386, atot2393]
  decide +kernel

theorem arows2410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2410 = true := by
  rw [show D2M8K2.u2410 = KTree.node D2M8K2.u2402 (nat_lit 5690150) (nat_lit 4005219356) (nat_lit 0) D2M8K2.u2409 from rfl, allE_node, arows2402, irow2410, arows2409]
  all_goals rfl

theorem atot2410 : totK PD2M8K2 D2M8K2.u2410 = [0, 1600130086905, 5711353955343, 5690971888810, 1381515818521, 50489373762, 0, 0] := by
  rw [show D2M8K2.u2410 = KTree.node D2M8K2.u2402 (nat_lit 5690150) (nat_lit 4005219356) (nat_lit 0) D2M8K2.u2409 from rfl, totK_node, atot2402, atot2409]
  decide +kernel

theorem arows2425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2425 = true := by
  rw [show D2M8K2.u2425 = KTree.node D2M8K2.u2417 (nat_lit 5707185) (nat_lit 1413195099) (nat_lit 0) D2M8K2.u2424 from rfl, allE_node, arows2417, irow2425, arows2424]
  all_goals rfl

theorem atot2425 : totK PD2M8K2 D2M8K2.u2425 = [0, 93924006320, 2374938819762, 6636614414215, 4586016422395, 578559290055, 11121530615, 0] := by
  rw [show D2M8K2.u2425 = KTree.node D2M8K2.u2417 (nat_lit 5707185) (nat_lit 1413195099) (nat_lit 0) D2M8K2.u2424 from rfl, totK_node, atot2417, atot2424]
  decide +kernel

theorem arows2443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2443 = true := by
  rw [show D2M8K2.u2443 = KTree.node D2M8K2.u2435 (nat_lit 6517110) (nat_lit 2703972300) (nat_lit 0) D2M8K2.u2442 from rfl, allE_node, arows2435, irow2443, arows2442]
  all_goals rfl

theorem atot2443 : totK PD2M8K2 D2M8K2.u2443 = [1295660981603, 4228664336853, 4332096431262, 2595033402340, 1650248410528, 420987221683, 21751168066, 0] := by
  rw [show D2M8K2.u2443 = KTree.node D2M8K2.u2435 (nat_lit 6517110) (nat_lit 2703972300) (nat_lit 0) D2M8K2.u2442 from rfl, totK_node, atot2435, atot2442]
  decide +kernel

theorem arows2458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2458 = true := by
  rw [show D2M8K2.u2458 = KTree.node D2M8K2.u2450 (nat_lit 6530118) (nat_lit 3665721244) (nat_lit 0) D2M8K2.u2457 from rfl, allE_node, arows2450, irow2458, arows2457]
  all_goals rfl

theorem atot2458 : totK PD2M8K2 D2M8K2.u2458 = [845744674632, 4097440798384, 5938935680133, 2969296886625, 641049043265, 36921873854, 0, 0] := by
  rw [show D2M8K2.u2458 = KTree.node D2M8K2.u2450 (nat_lit 6530118) (nat_lit 3665721244) (nat_lit 0) D2M8K2.u2457 from rfl, totK_node, atot2450, atot2457]
  decide +kernel

theorem arows2474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2474 = true := by
  rw [show D2M8K2.u2474 = KTree.node D2M8K2.u2466 (nat_lit 6546538) (nat_lit 2555460052) (nat_lit 0) D2M8K2.u2473 from rfl, allE_node, arows2466, irow2474, arows2473]
  all_goals rfl

theorem atot2474 : totK PD2M8K2 D2M8K2.u2474 = [322854152712, 2203141518068, 5746295543835, 5165996223397, 973747860912, 21096254089, 0, 0] := by
  rw [show D2M8K2.u2474 = KTree.node D2M8K2.u2466 (nat_lit 6546538) (nat_lit 2555460052) (nat_lit 0) D2M8K2.u2473 from rfl, totK_node, atot2466, atot2473]
  decide +kernel

theorem arows2489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2489 = true := by
  rw [show D2M8K2.u2489 = KTree.node D2M8K2.u2481 (nat_lit 6560963) (nat_lit 2891196513) (nat_lit 0) D2M8K2.u2488 from rfl, allE_node, arows2481, irow2489, arows2488]
  all_goals rfl

theorem atot2489 : totK PD2M8K2 D2M8K2.u2489 = [1631269590558, 5798352232843, 5670546992563, 1357674536780, 56996509442, 0, 0, 0] := by
  rw [show D2M8K2.u2489 = KTree.node D2M8K2.u2481 (nat_lit 6560963) (nat_lit 2891196513) (nat_lit 0) D2M8K2.u2488 from rfl, totK_node, atot2481, atot2488]
  decide +kernel

theorem arows2506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2506 = true := by
  rw [show D2M8K2.u2506 = KTree.node D2M8K2.u2498 (nat_lit 6580466) (nat_lit 3028779004) (nat_lit 0) D2M8K2.u2505 from rfl, allE_node, arows2498, irow2506, arows2505]
  all_goals rfl

theorem atot2506 : totK PD2M8K2 D2M8K2.u2506 = [63020407318, 2350223710775, 6597341966565, 4524473186369, 664858758575, 18797058808, 0, 0] := by
  rw [show D2M8K2.u2506 = KTree.node D2M8K2.u2498 (nat_lit 6580466) (nat_lit 3028779004) (nat_lit 0) D2M8K2.u2505 from rfl, totK_node, atot2498, atot2505]
  decide +kernel

theorem arows2521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2521 = true := by
  rw [show D2M8K2.u2521 = KTree.node D2M8K2.u2513 (nat_lit 6600107) (nat_lit 2349605741) (nat_lit 0) D2M8K2.u2520 from rfl, allE_node, arows2513, irow2521, arows2520]
  all_goals rfl

theorem atot2521 : totK PD2M8K2 D2M8K2.u2521 = [1605088555492, 5614351850112, 5600037990988, 1620006145832, 94970166976, 0, 0, 0] := by
  rw [show D2M8K2.u2521 = KTree.node D2M8K2.u2513 (nat_lit 6600107) (nat_lit 2349605741) (nat_lit 0) D2M8K2.u2520 from rfl, totK_node, atot2513, atot2520]
  decide +kernel

theorem arows2537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2537 = true := by
  rw [show D2M8K2.u2537 = KTree.node D2M8K2.u2529 (nat_lit 6617420) (nat_lit 3131037683) (nat_lit 0) D2M8K2.u2536 from rfl, allE_node, arows2529, irow2537, arows2536]
  all_goals rfl

theorem atot2537 : totK PD2M8K2 D2M8K2.u2537 = [416383101368, 3216424926678, 6474111363497, 3732173536377, 512159311431, 14345316470, 0, 0] := by
  rw [show D2M8K2.u2537 = KTree.node D2M8K2.u2529 (nat_lit 6617420) (nat_lit 3131037683) (nat_lit 0) D2M8K2.u2536 from rfl, totK_node, atot2529, atot2536]
  decide +kernel

theorem arows2552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2552 = true := by
  rw [show D2M8K2.u2552 = KTree.node D2M8K2.u2544 (nat_lit 6638510) (nat_lit 3338863658) (nat_lit 0) D2M8K2.u2551 from rfl, allE_node, arows2544, irow2552, arows2551]
  all_goals rfl

theorem atot2552 : totK PD2M8K2 D2M8K2.u2552 = [1164514063787, 4645430111289, 5822655125826, 2501072105717, 259437585434, 4720618446, 0, 0] := by
  rw [show D2M8K2.u2552 = KTree.node D2M8K2.u2544 (nat_lit 6638510) (nat_lit 3338863658) (nat_lit 0) D2M8K2.u2551 from rfl, totK_node, atot2544, atot2551]
  decide +kernel

theorem arows2572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2572 = true := by
  rw [show D2M8K2.u2572 = KTree.node D2M8K2.u2564 (nat_lit 6651648) (nat_lit 3679542835) (nat_lit 0) D2M8K2.u2571 from rfl, allE_node, arows2564, irow2572, arows2571]
  all_goals rfl

theorem atot2572 : totK PD2M8K2 D2M8K2.u2572 = [850908763291, 4300454592123, 6381734172728, 2609321565573, 205577544139, 1138244013, 0, 0] := by
  rw [show D2M8K2.u2572 = KTree.node D2M8K2.u2564 (nat_lit 6651648) (nat_lit 3679542835) (nat_lit 0) D2M8K2.u2571 from rfl, totK_node, atot2564, atot2571]
  decide +kernel

theorem arows2587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2587 = true := by
  rw [show D2M8K2.u2587 = KTree.node D2M8K2.u2579 (nat_lit 6678568) (nat_lit 3801061395) (nat_lit 0) D2M8K2.u2586 from rfl, allE_node, arows2579, irow2587, arows2586]
  all_goals rfl

theorem atot2587 : totK PD2M8K2 D2M8K2.u2587 = [1117085192851, 4462311411849, 5902375965385, 2662034409688, 293747375782, 4977114383, 0, 0] := by
  rw [show D2M8K2.u2587 = KTree.node D2M8K2.u2579 (nat_lit 6678568) (nat_lit 3801061395) (nat_lit 0) D2M8K2.u2586 from rfl, totK_node, atot2579, atot2586]
  decide +kernel

theorem arows2603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2603 = true := by
  rw [show D2M8K2.u2603 = KTree.node D2M8K2.u2595 (nat_lit 6695293) (nat_lit 1183270411) (nat_lit 0) D2M8K2.u2602 from rfl, allE_node, arows2595, irow2603, arows2602]
  all_goals rfl

theorem atot2603 : totK PD2M8K2 D2M8K2.u2603 = [910074444546, 4395890071491, 6329826336005, 2633299107520, 211025148977, 1310285577, 0, 0] := by
  rw [show D2M8K2.u2603 = KTree.node D2M8K2.u2595 (nat_lit 6695293) (nat_lit 1183270411) (nat_lit 0) D2M8K2.u2602 from rfl, totK_node, atot2595, atot2602]
  decide +kernel

theorem arows2618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2618 = true := by
  rw [show D2M8K2.u2618 = KTree.node D2M8K2.u2610 (nat_lit 6715335) (nat_lit 3638037327) (nat_lit 0) D2M8K2.u2617 from rfl, allE_node, arows2610, irow2618, arows2617]
  all_goals rfl

theorem atot2618 : totK PD2M8K2 D2M8K2.u2618 = [0, 1716760398754, 5912791140064, 5446254008930, 1260168090285, 60957305749, 0, 0] := by
  rw [show D2M8K2.u2618 = KTree.node D2M8K2.u2610 (nat_lit 6715335) (nat_lit 3638037327) (nat_lit 0) D2M8K2.u2617 from rfl, totK_node, atot2610, atot2617]
  decide +kernel

theorem arows2635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2635 = true := by
  rw [show D2M8K2.u2635 = KTree.node D2M8K2.u2627 (nat_lit 6772935) (nat_lit 3424066818) (nat_lit 0) D2M8K2.u2634 from rfl, allE_node, arows2627, irow2635, arows2634]
  all_goals rfl

theorem atot2635 : totK PD2M8K2 D2M8K2.u2635 = [0, 1691470793519, 5947106884755, 5636466025005, 1191731893951, 28244065751, 0, 0] := by
  rw [show D2M8K2.u2635 = KTree.node D2M8K2.u2627 (nat_lit 6772935) (nat_lit 3424066818) (nat_lit 0) D2M8K2.u2634 from rfl, totK_node, atot2627, atot2634]
  decide +kernel

theorem arows2650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2650 = true := by
  rw [show D2M8K2.u2650 = KTree.node D2M8K2.u2642 (nat_lit 6789054) (nat_lit 3612017109) (nat_lit 0) D2M8K2.u2649 from rfl, allE_node, arows2642, irow2650, arows2649]
  all_goals rfl

theorem atot2650 : totK PD2M8K2 D2M8K2.u2650 = [0, 0, 1925935500024, 6146985927342, 5136740872936, 1073904060367, 47116249314, 0] := by
  rw [show D2M8K2.u2650 = KTree.node D2M8K2.u2642 (nat_lit 6789054) (nat_lit 3612017109) (nat_lit 0) D2M8K2.u2649 from rfl, totK_node, atot2642, atot2649]
  decide +kernel

theorem arows2666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2666 = true := by
  rw [show D2M8K2.u2666 = KTree.node D2M8K2.u2658 (nat_lit 6804611) (nat_lit 2875366070) (nat_lit 0) D2M8K2.u2665 from rfl, allE_node, arows2658, irow2666, arows2665]
  all_goals rfl

theorem atot2666 : totK PD2M8K2 D2M8K2.u2666 = [0, 1193966426631, 4393642262527, 5447161363795, 2917257098937, 456626673912, 10531122277, 0] := by
  rw [show D2M8K2.u2666 = KTree.node D2M8K2.u2658 (nat_lit 6804611) (nat_lit 2875366070) (nat_lit 0) D2M8K2.u2665 from rfl, totK_node, atot2658, atot2665]
  decide +kernel

theorem arows2681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2681 = true := by
  rw [show D2M8K2.u2681 = KTree.node D2M8K2.u2673 (nat_lit 6820841) (nat_lit 1594357550) (nat_lit 0) D2M8K2.u2680 from rfl, allE_node, arows2673, irow2681, arows2680]
  all_goals rfl

theorem atot2681 : totK PD2M8K2 D2M8K2.u2681 = [0, 826993596608, 4381193581534, 6524774456032, 2462839644310, 145533704117, 0, 0] := by
  rw [show D2M8K2.u2681 = KTree.node D2M8K2.u2673 (nat_lit 6820841) (nat_lit 1594357550) (nat_lit 0) D2M8K2.u2680 from rfl, totK_node, atot2673, atot2680]
  decide +kernel

theorem arows2699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2699 = true := by
  rw [show D2M8K2.u2699 = KTree.node D2M8K2.u2691 (nat_lit 6844367) (nat_lit 2139344255) (nat_lit 0) D2M8K2.u2698 from rfl, allE_node, arows2691, irow2699, arows2698]
  all_goals rfl

theorem atot2699 : totK PD2M8K2 D2M8K2.u2699 = [0, 1105944731453, 4350414059798, 5732760716635, 2816457364332, 354666089273, 6546549506, 0] := by
  rw [show D2M8K2.u2699 = KTree.node D2M8K2.u2691 (nat_lit 6844367) (nat_lit 2139344255) (nat_lit 0) D2M8K2.u2698 from rfl, totK_node, atot2691, atot2698]
  decide +kernel

theorem arows2714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2714 = true := by
  rw [show D2M8K2.u2714 = KTree.node D2M8K2.u2706 (nat_lit 6861243) (nat_lit 3437358801) (nat_lit 0) D2M8K2.u2713 from rfl, allE_node, arows2706, irow2714, arows2713]
  all_goals rfl

theorem atot2714 : totK PD2M8K2 D2M8K2.u2714 = [0, 915526925407, 4747688990245, 6484311757160, 2130719403604, 112516812781, 0, 0] := by
  rw [show D2M8K2.u2714 = KTree.node D2M8K2.u2706 (nat_lit 6861243) (nat_lit 3437358801) (nat_lit 0) D2M8K2.u2713 from rfl, totK_node, atot2706, atot2713]
  decide +kernel

theorem arows2730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2730 = true := by
  rw [show D2M8K2.u2730 = KTree.node D2M8K2.u2722 (nat_lit 6884466) (nat_lit 3384579950) (nat_lit 0) D2M8K2.u2729 from rfl, allE_node, arows2722, irow2730, arows2729]
  all_goals rfl

theorem atot2730 : totK PD2M8K2 D2M8K2.u2730 = [0, 912103719410, 3886542236929, 5850612932929, 3242586470813, 397558222755, 6624648996, 0] := by
  rw [show D2M8K2.u2730 = KTree.node D2M8K2.u2722 (nat_lit 6884466) (nat_lit 3384579950) (nat_lit 0) D2M8K2.u2729 from rfl, totK_node, atot2722, atot2729]
  decide +kernel

theorem arows2745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2745 = true := by
  rw [show D2M8K2.u2745 = KTree.node D2M8K2.u2737 (nat_lit 6898502) (nat_lit 4180150381) (nat_lit 0) D2M8K2.u2744 from rfl, allE_node, arows2737, irow2745, arows2744]
  all_goals rfl

theorem atot2745 : totK PD2M8K2 D2M8K2.u2745 = [0, 1099257716134, 5012558959709, 6287829408757, 1830075254773, 81727764077, 0, 0] := by
  rw [show D2M8K2.u2745 = KTree.node D2M8K2.u2737 (nat_lit 6898502) (nat_lit 4180150381) (nat_lit 0) D2M8K2.u2744 from rfl, totK_node, atot2737, atot2744]
  decide +kernel

theorem arows2762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2762 = true := by
  rw [show D2M8K2.u2762 = KTree.node D2M8K2.u2754 (nat_lit 6926042) (nat_lit 3055630840) (nat_lit 0) D2M8K2.u2761 from rfl, allE_node, arows2754, irow2762, arows2761]
  all_goals rfl

theorem atot2762 : totK PD2M8K2 D2M8K2.u2762 = [0, 921525837735, 4212708989687, 6199825432450, 2826115700338, 255491369361, 1429815836, 0] := by
  rw [show D2M8K2.u2762 = KTree.node D2M8K2.u2754 (nat_lit 6926042) (nat_lit 3055630840) (nat_lit 0) D2M8K2.u2761 from rfl, totK_node, atot2754, atot2761]
  decide +kernel

theorem arows2777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2777 = true := by
  rw [show D2M8K2.u2777 = KTree.node D2M8K2.u2769 (nat_lit 6943512) (nat_lit 3029888638) (nat_lit 0) D2M8K2.u2776 from rfl, allE_node, arows2769, irow2777, arows2776]
  all_goals rfl

theorem atot2777 : totK PD2M8K2 D2M8K2.u2777 = [0, 1105633799662, 5071938723065, 6313286521969, 1898914811664, 87558697786, 0, 0] := by
  rw [show D2M8K2.u2777 = KTree.node D2M8K2.u2769 (nat_lit 6943512) (nat_lit 3029888638) (nat_lit 0) D2M8K2.u2776 from rfl, totK_node, atot2769, atot2776]
  decide +kernel

theorem arows2793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2793 = true := by
  rw [show D2M8K2.u2793 = KTree.node D2M8K2.u2785 (nat_lit 6964968) (nat_lit 3356095581) (nat_lit 0) D2M8K2.u2792 from rfl, allE_node, arows2785, irow2793, arows2792]
  all_goals rfl

theorem atot2793 : totK PD2M8K2 D2M8K2.u2793 = [806087225585, 2413993407010, 2799869191941, 4172883937154, 3563423471618, 570427857385, 12189850367, 0] := by
  rw [show D2M8K2.u2793 = KTree.node D2M8K2.u2785 (nat_lit 6964968) (nat_lit 3356095581) (nat_lit 0) D2M8K2.u2792 from rfl, totK_node, atot2785, atot2792]
  decide +kernel

theorem arows2808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2808 = true := by
  rw [show D2M8K2.u2808 = KTree.node D2M8K2.u2800 (nat_lit 6986180) (nat_lit 2038720100) (nat_lit 0) D2M8K2.u2807 from rfl, allE_node, arows2800, irow2808, arows2807]
  all_goals rfl

theorem atot2808 : totK PD2M8K2 D2M8K2.u2808 = [841462763533, 4271207110688, 6330349217095, 2569328888396, 223480545436, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2808 = KTree.node D2M8K2.u2800 (nat_lit 6986180) (nat_lit 2038720100) (nat_lit 0) D2M8K2.u2807 from rfl, totK_node, atot2800, atot2807]
  decide +kernel

theorem arows2827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2827 = true := by
  rw [show D2M8K2.u2827 = KTree.node D2M8K2.u2819 (nat_lit 7014847) (nat_lit 2369880789) (nat_lit 0) D2M8K2.u2826 from rfl, allE_node, arows2819, irow2827, arows2826]
  all_goals rfl

theorem atot2827 : totK PD2M8K2 D2M8K2.u2827 = [1218829956258, 4978435495955, 6159564164318, 2100570698792, 111493038792, 0, 0, 0] := by
  rw [show D2M8K2.u2827 = KTree.node D2M8K2.u2819 (nat_lit 7014847) (nat_lit 2369880789) (nat_lit 0) D2M8K2.u2826 from rfl, totK_node, atot2819, atot2826]
  decide +kernel

theorem arows2842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2842 = true := by
  rw [show D2M8K2.u2842 = KTree.node D2M8K2.u2834 (nat_lit 7028547) (nat_lit 2387195009) (nat_lit 0) D2M8K2.u2841 from rfl, allE_node, arows2834, irow2842, arows2841]
  all_goals rfl

theorem atot2842 : totK PD2M8K2 D2M8K2.u2842 = [829302901382, 3993141264569, 5920261236854, 3087559725960, 652054035455, 36921873854, 0, 0] := by
  rw [show D2M8K2.u2842 = KTree.node D2M8K2.u2834 (nat_lit 7028547) (nat_lit 2387195009) (nat_lit 0) D2M8K2.u2841 from rfl, totK_node, atot2834, atot2841]
  decide +kernel

theorem arows2858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2858 = true := by
  rw [show D2M8K2.u2858 = KTree.node D2M8K2.u2850 (nat_lit 7045752) (nat_lit 2527698381) (nat_lit 0) D2M8K2.u2857 from rfl, allE_node, arows2850, irow2858, arows2857]
  all_goals rfl

theorem atot2858 : totK PD2M8K2 D2M8K2.u2858 = [397470960283, 2492366714105, 5677112553313, 4889176155091, 957042805227, 21096254089, 0, 0] := by
  rw [show D2M8K2.u2858 = KTree.node D2M8K2.u2850 (nat_lit 7045752) (nat_lit 2527698381) (nat_lit 0) D2M8K2.u2857 from rfl, totK_node, atot2850, atot2857]
  decide +kernel

theorem arows2873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2873 = true := by
  rw [show D2M8K2.u2873 = KTree.node D2M8K2.u2865 (nat_lit 7059268) (nat_lit 3798767105) (nat_lit 0) D2M8K2.u2872 from rfl, allE_node, arows2865, irow2873, arows2872]
  all_goals rfl

theorem atot2873 : totK PD2M8K2 D2M8K2.u2873 = [1709657750004, 5851204485132, 5557026392087, 1328753043340, 56839787771, 0, 0, 0] := by
  rw [show D2M8K2.u2873 = KTree.node D2M8K2.u2865 (nat_lit 7059268) (nat_lit 3798767105) (nat_lit 0) D2M8K2.u2872 from rfl, totK_node, atot2865, atot2872]
  decide +kernel

theorem arows2890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2890 = true := by
  rw [show D2M8K2.u2890 = KTree.node D2M8K2.u2882 (nat_lit 7078303) (nat_lit 2002054972) (nat_lit 0) D2M8K2.u2889 from rfl, allE_node, arows2882, irow2890, arows2889]
  all_goals rfl

theorem atot2890 : totK PD2M8K2 D2M8K2.u2890 = [0, 2164945667045, 6622937966940, 4680669395366, 683609171688, 18797058808, 0, 0] := by
  rw [show D2M8K2.u2890 = KTree.node D2M8K2.u2882 (nat_lit 7078303) (nat_lit 2002054972) (nat_lit 0) D2M8K2.u2889 from rfl, totK_node, atot2882, atot2889]
  decide +kernel

theorem arows2905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2905 = true := by
  rw [show D2M8K2.u2905 = KTree.node D2M8K2.u2897 (nat_lit 7139040) (nat_lit 3176974630) (nat_lit 0) D2M8K2.u2904 from rfl, allE_node, arows2897, irow2905, arows2904]
  all_goals rfl

theorem atot2905 : totK PD2M8K2 D2M8K2.u2905 = [1547471583796, 5538570352143, 5646320239302, 1630153213712, 86161412225, 0, 0, 0] := by
  rw [show D2M8K2.u2905 = KTree.node D2M8K2.u2897 (nat_lit 7139040) (nat_lit 3176974630) (nat_lit 0) D2M8K2.u2904 from rfl, totK_node, atot2897, atot2904]
  decide +kernel

theorem arows2921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2921 = true := by
  rw [show D2M8K2.u2921 = KTree.node D2M8K2.u2913 (nat_lit 7156852) (nat_lit 3944550691) (nat_lit 0) D2M8K2.u2920 from rfl, allE_node, arows2913, irow2921, arows2920]
  all_goals rfl

theorem atot2921 : totK PD2M8K2 D2M8K2.u2921 = [435720955444, 3551906834991, 6861615207460, 3229084001920, 249232217546, 1138244013, 0, 0] := by
  rw [show D2M8K2.u2921 = KTree.node D2M8K2.u2913 (nat_lit 7156852) (nat_lit 3944550691) (nat_lit 0) D2M8K2.u2920 from rfl, totK_node, atot2913, atot2920]
  decide +kernel

theorem arows2936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2936 = true := by
  rw [show D2M8K2.u2936 = KTree.node D2M8K2.u2928 (nat_lit 7179685) (nat_lit 1323729655) (nat_lit 0) D2M8K2.u2935 from rfl, allE_node, arows2928, irow2936, arows2935]
  all_goals rfl

theorem atot2936 : totK PD2M8K2 D2M8K2.u2936 = [1465810826858, 5139079673755, 5505194695583, 2077536480526, 252609785729, 4977114383, 0, 0] := by
  rw [show D2M8K2.u2936 = KTree.node D2M8K2.u2928 (nat_lit 7179685) (nat_lit 1323729655) (nat_lit 0) D2M8K2.u2935 from rfl, totK_node, atot2928, atot2935]
  decide +kernel

theorem arows2954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2954 = true := by
  rw [show D2M8K2.u2954 = KTree.node D2M8K2.u2946 (nat_lit 7196843) (nat_lit 2942248401) (nat_lit 0) D2M8K2.u2953 from rfl, allE_node, arows2946, irow2954, arows2953]
  all_goals rfl

theorem atot2954 : totK PD2M8K2 D2M8K2.u2954 = [529390851355, 3391370118773, 6386573749292, 3677206356076, 424784410309, 6190125969, 0, 0] := by
  rw [show D2M8K2.u2954 = KTree.node D2M8K2.u2946 (nat_lit 7196843) (nat_lit 2942248401) (nat_lit 0) D2M8K2.u2953 from rfl, totK_node, atot2946, atot2953]
  decide +kernel

theorem arows2969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2969 = true := by
  rw [show D2M8K2.u2969 = KTree.node D2M8K2.u2961 (nat_lit 7216738) (nat_lit 3795593382) (nat_lit 0) D2M8K2.u2968 from rfl, allE_node, arows2961, irow2969, arows2968]
  all_goals rfl

theorem atot2969 : totK PD2M8K2 D2M8K2.u2969 = [0, 1739041771110, 6000978675940, 5449308597327, 1112139826253, 41101450378, 0, 0] := by
  rw [show D2M8K2.u2969 = KTree.node D2M8K2.u2961 (nat_lit 7216738) (nat_lit 3795593382) (nat_lit 0) D2M8K2.u2968 from rfl, totK_node, atot2961, atot2968]
  decide +kernel

theorem arows2985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2985 = true := by
  rw [show D2M8K2.u2985 = KTree.node D2M8K2.u2977 (nat_lit 7237711) (nat_lit 1100539348) (nat_lit 0) D2M8K2.u2984 from rfl, allE_node, arows2977, irow2985, arows2984]
  all_goals rfl

theorem atot2985 : totK PD2M8K2 D2M8K2.u2985 = [0, 645998611296, 4009854242044, 6685893869198, 2589123862702, 182393935443, 1275377855, 0] := by
  rw [show D2M8K2.u2985 = KTree.node D2M8K2.u2977 (nat_lit 7237711) (nat_lit 1100539348) (nat_lit 0) D2M8K2.u2984 from rfl, totK_node, atot2977, atot2984]
  decide +kernel

theorem arows3000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3000 = true := by
  rw [show D2M8K2.u3000 = KTree.node D2M8K2.u2992 (nat_lit 7266366) (nat_lit 2977357217) (nat_lit 0) D2M8K2.u2999 from rfl, allE_node, arows2992, irow3000, arows2999]
  all_goals rfl

theorem atot3000 : totK PD2M8K2 D2M8K2.u3000 = [0, 1628330673402, 5838065990755, 5705513730516, 1377981144024, 63671365337, 0, 0] := by
  rw [show D2M8K2.u3000 = KTree.node D2M8K2.u2992 (nat_lit 7266366) (nat_lit 2977357217) (nat_lit 0) D2M8K2.u2999 from rfl, totK_node, atot2992, atot2999]
  decide +kernel

theorem arows3017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3017 = true := by
  rw [show D2M8K2.u3017 = KTree.node D2M8K2.u3009 (nat_lit 7302048) (nat_lit 3577290238) (nat_lit 0) D2M8K2.u3016 from rfl, allE_node, arows3009, irow3017, arows3016]
  all_goals rfl

theorem atot3017 : totK PD2M8K2 D2M8K2.u3017 = [0, 1685427389511, 5865480204389, 5594541143915, 1283001923919, 48259591619, 0, 0] := by
  rw [show D2M8K2.u3017 = KTree.node D2M8K2.u3009 (nat_lit 7302048) (nat_lit 3577290238) (nat_lit 0) D2M8K2.u3016 from rfl, totK_node, atot3009, atot3016]
  decide +kernel

theorem arows3032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3032 = true := by
  rw [show D2M8K2.u3032 = KTree.node D2M8K2.u3024 (nat_lit 7318676) (nat_lit 2769115098) (nat_lit 0) D2M8K2.u3031 from rfl, allE_node, arows3024, irow3032, arows3031]
  all_goals rfl

theorem atot3032 : totK PD2M8K2 D2M8K2.u3032 = [0, 835662425276, 4276098040788, 6360481787804, 2525555452928, 204031726371, 1206465782, 0] := by
  rw [show D2M8K2.u3032 = KTree.node D2M8K2.u3024 (nat_lit 7318676) (nat_lit 2769115098) (nat_lit 0) D2M8K2.u3031 from rfl, totK_node, atot3024, atot3031]
  decide +kernel

theorem arows3048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3048 = true := by
  rw [show D2M8K2.u3048 = KTree.node D2M8K2.u3040 (nat_lit 7338575) (nat_lit 2161348375) (nat_lit 0) D2M8K2.u3047 from rfl, allE_node, arows3040, irow3048, arows3047]
  all_goals rfl

theorem atot3048 : totK PD2M8K2 D2M8K2.u3048 = [0, 828694701111, 3839953214381, 5873802845852, 3101397266433, 497902686461, 17590593026, 0] := by
  rw [show D2M8K2.u3048 = KTree.node D2M8K2.u3040 (nat_lit 7338575) (nat_lit 2161348375) (nat_lit 0) D2M8K2.u3047 from rfl, totK_node, atot3040, atot3047]
  decide +kernel

theorem arows3063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3063 = true := by
  rw [show D2M8K2.u3063 = KTree.node D2M8K2.u3055 (nat_lit 7396372) (nat_lit 3771586279) (nat_lit 0) D2M8K2.u3062 from rfl, allE_node, arows3055, irow3063, arows3062]
  all_goals rfl

theorem atot3063 : totK PD2M8K2 D2M8K2.u3063 = [0, 1152398660830, 4967371911650, 6063579714214, 1945263564168, 123662190982, 1103454931, 0] := by
  rw [show D2M8K2.u3063 = KTree.node D2M8K2.u3055 (nat_lit 7396372) (nat_lit 3771586279) (nat_lit 0) D2M8K2.u3062 from rfl, totK_node, atot3055, atot3062]
  decide +kernel

theorem arows3084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3084 = true := by
  rw [show D2M8K2.u3084 = KTree.node D2M8K2.u3076 (nat_lit 7424272) (nat_lit 3688143879) (nat_lit 0) D2M8K2.u3083 from rfl, allE_node, arows3076, irow3084, arows3083]
  all_goals rfl

theorem atot3084 : totK PD2M8K2 D2M8K2.u3084 = [0, 970210877997, 4405779369893, 6123848267367, 2486323890194, 239704369493, 4779662215, 0] := by
  rw [show D2M8K2.u3084 = KTree.node D2M8K2.u3076 (nat_lit 7424272) (nat_lit 3688143879) (nat_lit 0) D2M8K2.u3083 from rfl, totK_node, atot3076, atot3083]
  decide +kernel

theorem arows3099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3099 = true := by
  rw [show D2M8K2.u3099 = KTree.node D2M8K2.u3091 (nat_lit 7441785) (nat_lit 1002487381) (nat_lit 0) D2M8K2.u3098 from rfl, allE_node, arows3091, irow3099, arows3098]
  all_goals rfl

theorem atot3099 : totK PD2M8K2 D2M8K2.u3099 = [709127292956, 3197109166474, 5439447837830, 4172048847415, 933413939969, 36795064199, 0, 0] := by
  rw [show D2M8K2.u3099 = KTree.node D2M8K2.u3091 (nat_lit 7441785) (nat_lit 1002487381) (nat_lit 0) D2M8K2.u3098 from rfl, totK_node, atot3091, atot3098]
  decide +kernel

theorem arows3115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3115 = true := by
  rw [show D2M8K2.u3115 = KTree.node D2M8K2.u3107 (nat_lit 7483254) (nat_lit 3812646336) (nat_lit 0) D2M8K2.u3114 from rfl, allE_node, arows3107, irow3115, arows3114]
  all_goals rfl

theorem atot3115 : totK PD2M8K2 D2M8K2.u3115 = [938717892041, 4428234118940, 6202339252533, 2466491681496, 218815006142, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3115 = KTree.node D2M8K2.u3107 (nat_lit 7483254) (nat_lit 3812646336) (nat_lit 0) D2M8K2.u3114 from rfl, totK_node, atot3107, atot3114]
  decide +kernel

theorem arows3130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3130 = true := by
  rw [show D2M8K2.u3130 = KTree.node D2M8K2.u3122 (nat_lit 7512184) (nat_lit 3391799479) (nat_lit 0) D2M8K2.u3129 from rfl, allE_node, arows3122, irow3130, arows3129]
  all_goals rfl

theorem atot3130 : totK PD2M8K2 D2M8K2.u3130 = [1218909925012, 4914091929393, 6138262938823, 2168386043097, 116289367802, 0, 0, 0] := by
  rw [show D2M8K2.u3130 = KTree.node D2M8K2.u3122 (nat_lit 7512184) (nat_lit 3391799479) (nat_lit 0) D2M8K2.u3129 from rfl, totK_node, atot3122, atot3129]
  decide +kernel

theorem arows3147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3147 = true := by
  rw [show D2M8K2.u3147 = KTree.node D2M8K2.u3139 (nat_lit 7525796) (nat_lit 2936503469) (nat_lit 0) D2M8K2.u3146 from rfl, allE_node, arows3139, irow3147, arows3146]
  all_goals rfl

theorem atot3147 : totK PD2M8K2 D2M8K2.u3147 = [829394532047, 4050605339137, 5932006607795, 3039773236499, 650691209727, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3147 = KTree.node D2M8K2.u3139 (nat_lit 7525796) (nat_lit 2936503469) (nat_lit 0) D2M8K2.u3146 from rfl, totK_node, atot3139, atot3146]
  decide +kernel

theorem arows3162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3162 = true := by
  rw [show D2M8K2.u3162 = KTree.node D2M8K2.u3154 (nat_lit 7542828) (nat_lit 3176313661) (nat_lit 0) D2M8K2.u3161 from rfl, allE_node, arows3154, irow3162, arows3161]
  all_goals rfl

theorem atot3162 : totK PD2M8K2 D2M8K2.u3162 = [397564749128, 2421752229859, 5675192518880, 4941572103737, 958454160237, 21096254089, 0, 0] := by
  rw [show D2M8K2.u3162 = KTree.node D2M8K2.u3154 (nat_lit 7542828) (nat_lit 3176313661) (nat_lit 0) D2M8K2.u3161 from rfl, totK_node, atot3154, atot3161]
  decide +kernel

theorem arows3178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3178 = true := by
  rw [show D2M8K2.u3178 = KTree.node D2M8K2.u3170 (nat_lit 7601542) (nat_lit 3357770078) (nat_lit 0) D2M8K2.u3177 from rfl, allE_node, arows3170, irow3178, arows3177]
  all_goals rfl

theorem atot3178 : totK PD2M8K2 D2M8K2.u3178 = [1709996110766, 5904702077867, 5567260017819, 1297061511570, 55768132743, 0, 0, 0] := by
  rw [show D2M8K2.u3178 = KTree.node D2M8K2.u3170 (nat_lit 7601542) (nat_lit 3357770078) (nat_lit 0) D2M8K2.u3177 from rfl, totK_node, atot3170, atot3177]
  decide +kernel

theorem arows3193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3193 = true := by
  rw [show D2M8K2.u3193 = KTree.node D2M8K2.u3185 (nat_lit 7620571) (nat_lit 2241137686) (nat_lit 0) D2M8K2.u3192 from rfl, allE_node, arows3185, irow3193, arows3192]
  all_goals rfl

theorem atot3193 : totK PD2M8K2 D2M8K2.u3193 = [0, 2180943044689, 6592313233681, 4705113470328, 692871656064, 19065934916, 0, 0] := by
  rw [show D2M8K2.u3193 = KTree.node D2M8K2.u3185 (nat_lit 7620571) (nat_lit 2241137686) (nat_lit 0) D2M8K2.u3192 from rfl, totK_node, atot3185, atot3192]
  decide +kernel

theorem arows3211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3211 = true := by
  rw [show D2M8K2.u3211 = KTree.node D2M8K2.u3203 (nat_lit 7636384) (nat_lit 3746813931) (nat_lit 0) D2M8K2.u3210 from rfl, allE_node, arows3203, irow3211, arows3210]
  all_goals rfl

theorem atot3211 : totK PD2M8K2 D2M8K2.u3211 = [1547648331122, 5499854283530, 5635400688366, 1683792282680, 98629672030, 0, 0, 0] := by
  rw [show D2M8K2.u3211 = KTree.node D2M8K2.u3203 (nat_lit 7636384) (nat_lit 3746813931) (nat_lit 0) D2M8K2.u3210 from rfl, totK_node, atot3203, atot3210]
  decide +kernel

theorem arows3226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3226 = true := by
  rw [show D2M8K2.u3226 = KTree.node D2M8K2.u3218 (nat_lit 7653463) (nat_lit 2073151362) (nat_lit 0) D2M8K2.u3225 from rfl, allE_node, arows3218, irow3226, arows3225]
  all_goals rfl

theorem atot3226 : totK PD2M8K2 D2M8K2.u3226 = [435739754619, 3612518503164, 6906742164402, 3141748847205, 235155792858, 1138244013, 0, 0] := by
  rw [show D2M8K2.u3226 = KTree.node D2M8K2.u3218 (nat_lit 7653463) (nat_lit 2073151362) (nat_lit 0) D2M8K2.u3225 from rfl, totK_node, atot3218, atot3225]
  decide +kernel

theorem arows3242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3242 = true := by
  rw [show D2M8K2.u3242 = KTree.node D2M8K2.u3234 (nat_lit 7676908) (nat_lit 3120397441) (nat_lit 0) D2M8K2.u3241 from rfl, allE_node, arows3234, irow3242, arows3241]
  all_goals rfl

theorem atot3242 : totK PD2M8K2 D2M8K2.u3242 = [1465379111097, 5068828651893, 5507457414032, 2171539982676, 264348702963, 4977114383, 0, 0] := by
  rw [show D2M8K2.u3242 = KTree.node D2M8K2.u3234 (nat_lit 7676908) (nat_lit 3120397441) (nat_lit 0) D2M8K2.u3241 from rfl, totK_node, atot3234, atot3241]
  decide +kernel

theorem arows3257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3257 = true := by
  rw [show D2M8K2.u3257 = KTree.node D2M8K2.u3249 (nat_lit 7694006) (nat_lit 3720341711) (nat_lit 0) D2M8K2.u3256 from rfl, allE_node, arows3249, irow3257, arows3256]
  all_goals rfl

theorem atot3257 : totK PD2M8K2 D2M8K2.u3257 = [530041065405, 3502222746326, 6414574541785, 3562811339542, 412506345352, 6190125969, 0, 0] := by
  rw [show D2M8K2.u3257 = KTree.node D2M8K2.u3249 (nat_lit 7694006) (nat_lit 3720341711) (nat_lit 0) D2M8K2.u3256 from rfl, totK_node, atot3249, atot3256]
  decide +kernel

theorem arows3274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3274 = true := by
  rw [show D2M8K2.u3274 = KTree.node D2M8K2.u3266 (nat_lit 7713732) (nat_lit 2792823884) (nat_lit 0) D2M8K2.u3273 from rfl, allE_node, arows3266, irow3274, arows3273]
  all_goals rfl

theorem atot3274 : totK PD2M8K2 D2M8K2.u3274 = [0, 1635908418547, 5933019504761, 5548746873686, 1139916041965, 41241721652, 0, 0] := by
  rw [show D2M8K2.u3274 = KTree.node D2M8K2.u3266 (nat_lit 7713732) (nat_lit 2792823884) (nat_lit 0) D2M8K2.u3273 from rfl, totK_node, atot3266, atot3273]
  decide +kernel

theorem arows3289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3289 = true := by
  rw [show D2M8K2.u3289 = KTree.node D2M8K2.u3281 (nat_lit 7734672) (nat_lit 3743040523) (nat_lit 0) D2M8K2.u3288 from rfl, allE_node, arows3281, irow3289, arows3288]
  all_goals rfl

theorem atot3289 : totK PD2M8K2 D2M8K2.u3289 = [0, 792969625575, 4175638187200, 6459107302115, 2517206518662, 181944714232, 1310517177, 0] := by
  rw [show D2M8K2.u3289 = KTree.node D2M8K2.u3281 (nat_lit 7734672) (nat_lit 3743040523) (nat_lit 0) D2M8K2.u3288 from rfl, totK_node, atot3281, atot3288]
  decide +kernel

theorem arows3305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3305 = true := by
  rw [show D2M8K2.u3305 = KTree.node D2M8K2.u3297 (nat_lit 7763846) (nat_lit 2599633717) (nat_lit 0) D2M8K2.u3304 from rfl, allE_node, arows3297, irow3305, arows3304]
  all_goals rfl

theorem atot3305 : totK PD2M8K2 D2M8K2.u3305 = [0, 1629098077863, 5726893308834, 5661474131629, 1484279192952, 68863650852, 0, 0] := by
  rw [show D2M8K2.u3305 = KTree.node D2M8K2.u3297 (nat_lit 7763846) (nat_lit 2599633717) (nat_lit 0) D2M8K2.u3304 from rfl, totK_node, atot3297, atot3304]
  decide +kernel

theorem arows3320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3320 = true := by
  rw [show D2M8K2.u3320 = KTree.node D2M8K2.u3312 (nat_lit 7840044) (nat_lit 3202353509) (nat_lit 0) D2M8K2.u3319 from rfl, allE_node, arows3312, irow3320, arows3319]
  all_goals rfl

theorem atot3320 : totK PD2M8K2 D2M8K2.u3320 = [0, 1685940700765, 5830270195927, 5580451859581, 1322134966948, 53227534193, 0, 0] := by
  rw [show D2M8K2.u3320 = KTree.node D2M8K2.u3312 (nat_lit 7840044) (nat_lit 3202353509) (nat_lit 0) D2M8K2.u3319 from rfl, totK_node, atot3312, atot3319]
  decide +kernel

theorem arows3339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3339 = true := by
  rw [show D2M8K2.u3339 = KTree.node D2M8K2.u3331 (nat_lit 7857002) (nat_lit 4027373349) (nat_lit 0) D2M8K2.u3338 from rfl, allE_node, arows3331, irow3339, arows3338]
  all_goals rfl

theorem atot3339 : totK PD2M8K2 D2M8K2.u3339 = [0, 835812598805, 4395049051743, 6383788300402, 2395385956484, 186159370636, 1217496766, 0] := by
  rw [show D2M8K2.u3339 = KTree.node D2M8K2.u3331 (nat_lit 7857002) (nat_lit 4027373349) (nat_lit 0) D2M8K2.u3338 from rfl, totK_node, atot3331, atot3338]
  decide +kernel

theorem arows3354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3354 = true := by
  rw [show D2M8K2.u3354 = KTree.node D2M8K2.u3346 (nat_lit 7876494) (nat_lit 3819441806) (nat_lit 0) D2M8K2.u3353 from rfl, allE_node, arows3346, irow3354, arows3353]
  all_goals rfl

theorem atot3354 : totK PD2M8K2 D2M8K2.u3354 = [0, 796577075393, 3744601141086, 5859737606342, 3247675180356, 522086058514, 17736366219, 0] := by
  rw [show D2M8K2.u3354 = KTree.node D2M8K2.u3346 (nat_lit 7876494) (nat_lit 3819441806) (nat_lit 0) D2M8K2.u3353 from rfl, totK_node, atot3346, atot3353]
  decide +kernel

theorem arows3370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3370 = true := by
  rw [show D2M8K2.u3370 = KTree.node D2M8K2.u3362 (nat_lit 7893073) (nat_lit 1470127818) (nat_lit 0) D2M8K2.u3369 from rfl, allE_node, arows3362, irow3370, arows3369]
  all_goals rfl

theorem atot3370 : totK PD2M8K2 D2M8K2.u3370 = [0, 1186293100505, 4934818059937, 6037411330032, 1970650823067, 125398277341, 1138244013, 0] := by
  rw [show D2M8K2.u3370 = KTree.node D2M8K2.u3362 (nat_lit 7893073) (nat_lit 1470127818) (nat_lit 0) D2M8K2.u3369 from rfl, totK_node, atot3362, atot3369]
  decide +kernel

theorem arows3385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3385 = true := by
  rw [show D2M8K2.u3385 = KTree.node D2M8K2.u3377 (nat_lit 7916645) (nat_lit 2343298695) (nat_lit 0) D2M8K2.u3384 from rfl, allE_node, arows3377, irow3385, arows3384]
  all_goals rfl

theorem atot3385 : totK PD2M8K2 D2M8K2.u3385 = [0, 799596199567, 4218575556411, 6329458038526, 2629279981767, 249500340565, 4914284239, 0] := by
  rw [show D2M8K2.u3385 = KTree.node D2M8K2.u3377 (nat_lit 7916645) (nat_lit 2343298695) (nat_lit 0) D2M8K2.u3384 from rfl, totK_node, atot3377, atot3384]
  decide +kernel

theorem arows3402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3402 = true := by
  rw [show D2M8K2.u3402 = KTree.node D2M8K2.u3394 (nat_lit 7934825) (nat_lit 1540344693) (nat_lit 0) D2M8K2.u3401 from rfl, allE_node, arows3394, irow3402, arows3401]
  all_goals rfl

theorem atot3402 : totK PD2M8K2 D2M8K2.u3402 = [421562263945, 2593485725677, 5470881672446, 4717599404267, 1179527251349, 48416804685, 0, 0] := by
  rw [show D2M8K2.u3402 = KTree.node D2M8K2.u3394 (nat_lit 7934825) (nat_lit 1540344693) (nat_lit 0) D2M8K2.u3401 from rfl, totK_node, atot3394, atot3401]
  decide +kernel

theorem arows3417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3417 = true := by
  rw [show D2M8K2.u3417 = KTree.node D2M8K2.u3409 (nat_lit 7976114) (nat_lit 3618023715) (nat_lit 0) D2M8K2.u3416 from rfl, allE_node, arows3409, irow3417, arows3416]
  all_goals rfl

theorem atot3417 : totK PD2M8K2 D2M8K2.u3417 = [1222764302083, 4896981887675, 5860861939184, 2078566037599, 195766461262, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3417 = KTree.node D2M8K2.u3409 (nat_lit 7976114) (nat_lit 3618023715) (nat_lit 0) D2M8K2.u3416 from rfl, totK_node, atot3409, atot3416]
  decide +kernel

theorem arows3433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3433 = true := by
  rw [show D2M8K2.u3433 = KTree.node D2M8K2.u3425 (nat_lit 8008734) (nat_lit 3869046296) (nat_lit 0) D2M8K2.u3432 from rfl, allE_node, arows3425, irow3433, arows3432]
  all_goals rfl

theorem atot3433 : totK PD2M8K2 D2M8K2.u3433 = [1014651670594, 4560580783604, 6360690809389, 2403247206914, 127336974035, 0, 0, 0] := by
  rw [show D2M8K2.u3433 = KTree.node D2M8K2.u3425 (nat_lit 8008734) (nat_lit 3869046296) (nat_lit 0) D2M8K2.u3432 from rfl, totK_node, atot3425, atot3432]
  decide +kernel

theorem arows3448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3448 = true := by
  rw [show D2M8K2.u3448 = KTree.node D2M8K2.u3440 (nat_lit 8022002) (nat_lit 4057746016) (nat_lit 0) D2M8K2.u3447 from rfl, allE_node, arows3440, irow3448, arows3447]
  all_goals rfl

theorem atot3448 : totK PD2M8K2 D2M8K2.u3448 = [1031320007119, 4409921379155, 5733396043397, 2715350323052, 616503634093, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3448 = KTree.node D2M8K2.u3440 (nat_lit 8022002) (nat_lit 4057746016) (nat_lit 0) D2M8K2.u3447 from rfl, totK_node, atot3440, atot3447]
  decide +kernel

theorem arows3466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3466 = true := by
  rw [show D2M8K2.u3466 = KTree.node D2M8K2.u3458 (nat_lit 8039046) (nat_lit 3797779054) (nat_lit 0) D2M8K2.u3465 from rfl, allE_node, arows3458, irow3466, arows3465]
  all_goals rfl

theorem atot3466 : totK PD2M8K2 D2M8K2.u3466 = [244726993122, 2128573270563, 5829751233014, 5266472798414, 992347428509, 21096254089, 0, 0] := by
  rw [show D2M8K2.u3466 = KTree.node D2M8K2.u3458 (nat_lit 8039046) (nat_lit 3797779054) (nat_lit 0) D2M8K2.u3465 from rfl, totK_node, atot3458, atot3465]
  decide +kernel

theorem arows3481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3481 = true := by
  rw [show D2M8K2.u3481 = KTree.node D2M8K2.u3473 (nat_lit 8053212) (nat_lit 3149023000) (nat_lit 0) D2M8K2.u3480 from rfl, allE_node, arows3473, irow3481, arows3480]
  all_goals rfl

theorem atot3481 : totK PD2M8K2 D2M8K2.u3481 = [1634972009204, 5787610777643, 5672428287288, 1355105433905, 56963931958, 0, 0, 0] := by
  rw [show D2M8K2.u3481 = KTree.node D2M8K2.u3473 (nat_lit 8053212) (nat_lit 3149023000) (nat_lit 0) D2M8K2.u3480 from rfl, totK_node, atot3473, atot3480]
  decide +kernel

theorem arows3497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3497 = true := by
  rw [show D2M8K2.u3497 = KTree.node D2M8K2.u3489 (nat_lit 8073281) (nat_lit 2222245322) (nat_lit 0) D2M8K2.u3496 from rfl, allE_node, arows3489, irow3497, arows3496]
  all_goals rfl

theorem atot3497 : totK PD2M8K2 D2M8K2.u3497 = [103540504535, 2389641730622, 6487004566373, 4517959488231, 669890727226, 18797058808, 0, 0] := by
  rw [show D2M8K2.u3497 = KTree.node D2M8K2.u3489 (nat_lit 8073281) (nat_lit 2222245322) (nat_lit 0) D2M8K2.u3496 from rfl, totK_node, atot3489, atot3496]
  decide +kernel

theorem arows3512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3512 = true := by
  rw [show D2M8K2.u3512 = KTree.node D2M8K2.u3504 (nat_lit 8092857) (nat_lit 1801243202) (nat_lit 0) D2M8K2.u3511 from rfl, allE_node, arows3504, irow3512, arows3511]
  all_goals rfl

theorem atot3512 : totK PD2M8K2 D2M8K2.u3512 = [1637971470198, 5611787329210, 5564456333293, 1600785296771, 92435036048, 0, 0, 0] := by
  rw [show D2M8K2.u3512 = KTree.node D2M8K2.u3504 (nat_lit 8092857) (nat_lit 1801243202) (nat_lit 0) D2M8K2.u3511 from rfl, totK_node, atot3504, atot3511]
  decide +kernel

theorem arows3529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3529 = true := by
  rw [show D2M8K2.u3529 = KTree.node D2M8K2.u3521 (nat_lit 8110458) (nat_lit 3903481145) (nat_lit 0) D2M8K2.u3528 from rfl, allE_node, arows3521, irow3529, arows3528]
  all_goals rfl

theorem atot3529 : totK PD2M8K2 D2M8K2.u3529 = [349342976169, 3125561058121, 6492052503698, 3833200157660, 523493382278, 14345316470, 0, 0] := by
  rw [show D2M8K2.u3529 = KTree.node D2M8K2.u3521 (nat_lit 8110458) (nat_lit 3903481145) (nat_lit 0) D2M8K2.u3528 from rfl, totK_node, atot3521, atot3528]
  decide +kernel

theorem arows3544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3544 = true := by
  rw [show D2M8K2.u3544 = KTree.node D2M8K2.u3536 (nat_lit 8131486) (nat_lit 2584078875) (nat_lit 0) D2M8K2.u3543 from rfl, allE_node, arows3536, irow3544, arows3543]
  all_goals rfl

theorem atot3544 : totK PD2M8K2 D2M8K2.u3544 = [1240272955867, 4770101644059, 5710095606372, 2378576302934, 254758083222, 4720618446, 0, 0] := by
  rw [show D2M8K2.u3544 = KTree.node D2M8K2.u3536 (nat_lit 8131486) (nat_lit 2584078875) (nat_lit 0) D2M8K2.u3543 from rfl, totK_node, atot3536, atot3543]
  decide +kernel

theorem arows3560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3560 = true := by
  rw [show D2M8K2.u3560 = KTree.node D2M8K2.u3552 (nat_lit 8144329) (nat_lit 1361328263) (nat_lit 0) D2M8K2.u3559 from rfl, allE_node, arows3552, irow3560, arows3559]
  all_goals rfl

theorem atot3560 : totK PD2M8K2 D2M8K2.u3560 = [862019888459, 4315884892996, 6375250800974, 2570361220369, 198594411518, 1138244013, 0, 0] := by
  rw [show D2M8K2.u3560 = KTree.node D2M8K2.u3552 (nat_lit 8144329) (nat_lit 1361328263) (nat_lit 0) D2M8K2.u3559 from rfl, totK_node, atot3552, atot3559]
  decide +kernel

theorem arows3575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3575 = true := by
  rw [show D2M8K2.u3575 = KTree.node D2M8K2.u3567 (nat_lit 8212136) (nat_lit 3868830926) (nat_lit 0) D2M8K2.u3574 from rfl, allE_node, arows3567, irow3575, arows3574]
  all_goals rfl

theorem atot3575 : totK PD2M8K2 D2M8K2.u3575 = [0, 2065708601077, 6509093484712, 4923458481034, 748014378423, 19329714611, 0, 0] := by
  rw [show D2M8K2.u3575 = KTree.node D2M8K2.u3567 (nat_lit 8212136) (nat_lit 3868830926) (nat_lit 0) D2M8K2.u3574 from rfl, totK_node, atot3567, atot3574]
  decide +kernel

theorem arows3595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3595 = true := by
  rw [show D2M8K2.u3595 = KTree.node D2M8K2.u3587 (nat_lit 8233187) (nat_lit 2952672172) (nat_lit 0) D2M8K2.u3594 from rfl, allE_node, arows3587, irow3595, arows3594]
  all_goals rfl

theorem atot3595 : totK PD2M8K2 D2M8K2.u3595 = [0, 613905356233, 4065820738627, 6729875162391, 2494986100369, 176450728702, 1209030869, 0] := by
  rw [show D2M8K2.u3595 = KTree.node D2M8K2.u3587 (nat_lit 8233187) (nat_lit 2952672172) (nat_lit 0) D2M8K2.u3594 from rfl, totK_node, atot3587, atot3594]
  decide +kernel

theorem arows3610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3610 = true := by
  rw [show D2M8K2.u3610 = KTree.node D2M8K2.u3602 (nat_lit 8262358) (nat_lit 2930599450) (nat_lit 0) D2M8K2.u3609 from rfl, allE_node, arows3602, irow3610, arows3609]
  all_goals rfl

theorem atot3610 : totK PD2M8K2 D2M8K2.u3610 = [0, 1695114697396, 5946285408400, 5576203611122, 1296605319981, 63138498046, 0, 0] := by
  rw [show D2M8K2.u3610 = KTree.node D2M8K2.u3602 (nat_lit 8262358) (nat_lit 2930599450) (nat_lit 0) D2M8K2.u3609 from rfl, totK_node, atot3602, atot3609]
  decide +kernel

theorem arows3626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3626 = true := by
  rw [show D2M8K2.u3626 = KTree.node D2M8K2.u3618 (nat_lit 8298470) (nat_lit 4150634215) (nat_lit 0) D2M8K2.u3625 from rfl, allE_node, arows3618, irow3626, arows3625]
  all_goals rfl

theorem atot3626 : totK PD2M8K2 D2M8K2.u3626 = [0, 1651284162237, 5808475878860, 5721524972488, 1287277452632, 42985142146, 0, 0] := by
  rw [show D2M8K2.u3626 = KTree.node D2M8K2.u3618 (nat_lit 8298470) (nat_lit 4150634215) (nat_lit 0) D2M8K2.u3625 from rfl, totK_node, atot3618, atot3625]
  decide +kernel

theorem arows3641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3641 = true := by
  rw [show D2M8K2.u3641 = KTree.node D2M8K2.u3633 (nat_lit 8336959) (nat_lit 2438329483) (nat_lit 0) D2M8K2.u3640 from rfl, allE_node, arows3633, irow3641, arows3640]
  all_goals rfl

theorem atot3641 : totK PD2M8K2 D2M8K2.u3641 = [0, 1779723513400, 6135461650511, 5521393125619, 1044448482552, 26238259976, 0, 0] := by
  rw [show D2M8K2.u3641 = KTree.node D2M8K2.u3633 (nat_lit 8336959) (nat_lit 2438329483) (nat_lit 0) D2M8K2.u3640 from rfl, totK_node, atot3633, atot3640]
  decide +kernel

theorem arows3658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3658 = true := by
  rw [show D2M8K2.u3658 = KTree.node D2M8K2.u3650 (nat_lit 8354602) (nat_lit 4022249060) (nat_lit 0) D2M8K2.u3657 from rfl, allE_node, arows3650, irow3658, arows3657]
  all_goals rfl

theorem atot3658 : totK PD2M8K2 D2M8K2.u3658 = [0, 1705807456108, 6063738505101, 5578348215064, 1010848269265, 24412392811, 0, 0] := by
  rw [show D2M8K2.u3658 = KTree.node D2M8K2.u3650 (nat_lit 8354602) (nat_lit 4022249060) (nat_lit 0) D2M8K2.u3657 from rfl, totK_node, atot3650, atot3657]
  decide +kernel

theorem arows3673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3673 = true := by
  rw [show D2M8K2.u3673 = KTree.node D2M8K2.u3665 (nat_lit 8389301) (nat_lit 1281360470) (nat_lit 0) D2M8K2.u3672 from rfl, allE_node, arows3665, irow3673, arows3672]
  all_goals rfl

theorem atot3673 : totK PD2M8K2 D2M8K2.u3673 = [0, 1277026380148, 5247749977179, 6067869938932, 1610548275956, 76661592109, 0, 0] := by
  rw [show D2M8K2.u3673 = KTree.node D2M8K2.u3665 (nat_lit 8389301) (nat_lit 1281360470) (nat_lit 0) D2M8K2.u3672 from rfl, totK_node, atot3665, atot3672]
  decide +kernel

theorem arows3689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3689 = true := by
  rw [show D2M8K2.u3689 = KTree.node D2M8K2.u3681 (nat_lit 8412285) (nat_lit 1547845720) (nat_lit 0) D2M8K2.u3688 from rfl, allE_node, arows3681, irow3689, arows3688]
  all_goals rfl

theorem atot3689 : totK PD2M8K2 D2M8K2.u3689 = [608919996772, 1926999465553, 3162254536287, 5056123733312, 3017280006077, 385642533687, 6115358396, 0] := by
  rw [show D2M8K2.u3689 = KTree.node D2M8K2.u3681 (nat_lit 8412285) (nat_lit 1547845720) (nat_lit 0) D2M8K2.u3688 from rfl, totK_node, atot3681, atot3688]
  decide +kernel

theorem arows3704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3704 = true := by
  rw [show D2M8K2.u3704 = KTree.node D2M8K2.u3696 (nat_lit 8478175) (nat_lit 1299735129) (nat_lit 0) D2M8K2.u3703 from rfl, allE_node, arows3696, irow3704, arows3703]
  all_goals rfl

theorem atot3704 : totK PD2M8K2 D2M8K2.u3704 = [1038357545186, 4517629603784, 6065368660185, 2421359762589, 218281491955, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3704 = KTree.node D2M8K2.u3696 (nat_lit 8478175) (nat_lit 1299735129) (nat_lit 0) D2M8K2.u3703 from rfl, totK_node, atot3696, atot3703]
  decide +kernel

theorem arows3722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3722 = true := by
  rw [show D2M8K2.u3722 = KTree.node D2M8K2.u3714 (nat_lit 8506780) (nat_lit 3899941549) (nat_lit 0) D2M8K2.u3721 from rfl, allE_node, arows3714, irow3722, arows3721]
  all_goals rfl

theorem atot3722 : totK PD2M8K2 D2M8K2.u3722 = [1108540680398, 4737427812910, 6258726673033, 2309703978335, 127918768682, 0, 0, 0] := by
  rw [show D2M8K2.u3722 = KTree.node D2M8K2.u3714 (nat_lit 8506780) (nat_lit 3899941549) (nat_lit 0) D2M8K2.u3721 from rfl, totK_node, atot3714, atot3721]
  decide +kernel

theorem arows3737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3737 = true := by
  rw [show D2M8K2.u3737 = KTree.node D2M8K2.u3729 (nat_lit 8520564) (nat_lit 3138777480) (nat_lit 0) D2M8K2.u3736 from rfl, allE_node, arows3729, irow3737, arows3736]
  all_goals rfl

theorem atot3737 : totK PD2M8K2 D2M8K2.u3737 = [942024337442, 4242681038087, 5830982762175, 2877838766399, 635344873356, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3737 = KTree.node D2M8K2.u3729 (nat_lit 8520564) (nat_lit 3138777480) (nat_lit 0) D2M8K2.u3736 from rfl, totK_node, atot3729, atot3736]
  decide +kernel

theorem arows3753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3753 = true := by
  rw [show D2M8K2.u3753 = KTree.node D2M8K2.u3745 (nat_lit 8537281) (nat_lit 1382604159) (nat_lit 0) D2M8K2.u3752 from rfl, allE_node, arows3745, irow3753, arows3752]
  all_goals rfl

theorem atot3753 : totK PD2M8K2 D2M8K2.u3753 = [378822834728, 2377994620701, 5718928712664, 5024181680272, 971046163011, 21096254089, 0, 0] := by
  rw [show D2M8K2.u3753 = KTree.node D2M8K2.u3745 (nat_lit 8537281) (nat_lit 1382604159) (nat_lit 0) D2M8K2.u3752 from rfl, totK_node, atot3745, atot3752]
  decide +kernel

theorem arows3768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3768 = true := by
  rw [show D2M8K2.u3768 = KTree.node D2M8K2.u3760 (nat_lit 8551604) (nat_lit 2556837670) (nat_lit 0) D2M8K2.u3767 from rfl, allE_node, arows3760, irow3768, arows3767]
  all_goals rfl

theorem atot3768 : totK PD2M8K2 D2M8K2.u3768 = [1612429219327, 5800741972691, 5706332467609, 1353419494521, 56960261517, 0, 0, 0] := by
  rw [show D2M8K2.u3768 = KTree.node D2M8K2.u3760 (nat_lit 8551604) (nat_lit 2556837670) (nat_lit 0) D2M8K2.u3767 from rfl, totK_node, atot3760, atot3767]
  decide +kernel

theorem arows3785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3785 = true := by
  rw [show D2M8K2.u3785 = KTree.node D2M8K2.u3777 (nat_lit 8571272) (nat_lit 3887263102) (nat_lit 0) D2M8K2.u3784 from rfl, allE_node, arows3777, irow3785, arows3784]
  all_goals rfl

theorem atot3785 : totK PD2M8K2 D2M8K2.u3785 = [0, 2190242336810, 6665707638872, 4695664000419, 685511190137, 18797058808, 0, 0] := by
  rw [show D2M8K2.u3785 = KTree.node D2M8K2.u3777 (nat_lit 8571272) (nat_lit 3887263102) (nat_lit 0) D2M8K2.u3784 from rfl, totK_node, atot3777, atot3784]
  decide +kernel

theorem arows3800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3800 = true := by
  rw [show D2M8K2.u3800 = KTree.node D2M8K2.u3792 (nat_lit 8591040) (nat_lit 2809461567) (nat_lit 0) D2M8K2.u3799 from rfl, allE_node, arows3792, irow3800, arows3799]
  all_goals rfl

theorem atot3800 : totK PD2M8K2 D2M8K2.u3800 = [1565372783170, 5692163555387, 5720687016256, 1483591589220, 70751761620, 0, 0, 0] := by
  rw [show D2M8K2.u3800 = KTree.node D2M8K2.u3792 (nat_lit 8591040) (nat_lit 2809461567) (nat_lit 0) D2M8K2.u3799 from rfl, totK_node, atot3792, atot3799]
  decide +kernel

theorem arows3816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3816 = true := by
  rw [show D2M8K2.u3816 = KTree.node D2M8K2.u3808 (nat_lit 8609233) (nat_lit 675720631) (nat_lit 0) D2M8K2.u3815 from rfl, allE_node, arows3808, irow3816, arows3815]
  all_goals rfl

theorem atot3816 : totK PD2M8K2 D2M8K2.u3816 = [426423859968, 3095842807267, 6384325631334, 3906248586348, 531773506215, 14345316470, 0, 0] := by
  rw [show D2M8K2.u3816 = KTree.node D2M8K2.u3808 (nat_lit 8609233) (nat_lit 675720631) (nat_lit 0) D2M8K2.u3815 from rfl, totK_node, atot3808, atot3815]
  decide +kernel

theorem arows3831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3831 = true := by
  rw [show D2M8K2.u3831 = KTree.node D2M8K2.u3823 (nat_lit 8671714) (nat_lit 3994981239) (nat_lit 0) D2M8K2.u3830 from rfl, allE_node, arows3823, irow3831, arows3830]
  all_goals rfl

theorem atot3831 : totK PD2M8K2 D2M8K2.u3831 = [1245443753883, 4801952043932, 5761353382972, 2324442854506, 246284638342, 4720618446, 0, 0] := by
  rw [show D2M8K2.u3831 = KTree.node D2M8K2.u3823 (nat_lit 8671714) (nat_lit 3994981239) (nat_lit 0) D2M8K2.u3830 from rfl, totK_node, atot3823, atot3830]
  decide +kernel

theorem arows3850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3850 = true := by
  rw [show D2M8K2.u3850 = KTree.node D2M8K2.u3842 (nat_lit 8687536) (nat_lit 2436775918) (nat_lit 0) D2M8K2.u3849 from rfl, allE_node, arows3842, irow3850, arows3849]
  all_goals rfl

theorem atot3850 : totK PD2M8K2 D2M8K2.u3850 = [867070346516, 4228113358388, 6285158210036, 2827263238807, 237433379967, 1310285577, 0, 0] := by
  rw [show D2M8K2.u3850 = KTree.node D2M8K2.u3842 (nat_lit 8687536) (nat_lit 2436775918) (nat_lit 0) D2M8K2.u3849 from rfl, totK_node, atot3842, atot3849]
  decide +kernel

theorem arows3865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3865 = true := by
  rw [show D2M8K2.u3865 = KTree.node D2M8K2.u3857 (nat_lit 8706619) (nat_lit 2241272188) (nat_lit 0) D2M8K2.u3864 from rfl, allE_node, arows3857, irow3865, arows3864]
  all_goals rfl

theorem atot3865 : totK PD2M8K2 D2M8K2.u3865 = [0, 1693337380435, 6071849982569, 5459829087780, 1023578744322, 32931563536, 0, 0] := by
  rw [show D2M8K2.u3865 = KTree.node D2M8K2.u3857 (nat_lit 8706619) (nat_lit 2241272188) (nat_lit 0) D2M8K2.u3864 from rfl, totK_node, atot3857, atot3864]
  decide +kernel

theorem arows3881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3881 = true := by
  rw [show D2M8K2.u3881 = KTree.node D2M8K2.u3873 (nat_lit 8727506) (nat_lit 3151079878) (nat_lit 0) D2M8K2.u3880 from rfl, allE_node, arows3873, irow3881, arows3880]
  all_goals rfl

theorem atot3881 : totK PD2M8K2 D2M8K2.u3881 = [0, 975799054933, 4521999423059, 6252215249756, 2291742297251, 166341871127, 1369150432, 0] := by
  rw [show D2M8K2.u3881 = KTree.node D2M8K2.u3873 (nat_lit 8727506) (nat_lit 3151079878) (nat_lit 0) D2M8K2.u3880 from rfl, totK_node, atot3873, atot3880]
  decide +kernel

theorem arows3896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3896 = true := by
  rw [show D2M8K2.u3896 = KTree.node D2M8K2.u3888 (nat_lit 8756500) (nat_lit 3630739068) (nat_lit 0) D2M8K2.u3895 from rfl, allE_node, arows3888, irow3896, arows3895]
  all_goals rfl

theorem atot3896 : totK PD2M8K2 D2M8K2.u3896 = [0, 1275471623115, 5033354118897, 6058653602905, 2011168532548, 101568600511, 0, 0] := by
  rw [show D2M8K2.u3896 = KTree.node D2M8K2.u3888 (nat_lit 8756500) (nat_lit 3630739068) (nat_lit 0) D2M8K2.u3895 from rfl, totK_node, atot3888, atot3895]
  decide +kernel

theorem arows3913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3913 = true := by
  rw [show D2M8K2.u3913 = KTree.node D2M8K2.u3905 (nat_lit 8770331) (nat_lit 2322485156) (nat_lit 0) D2M8K2.u3912 from rfl, allE_node, arows3905, irow3913, arows3912]
  all_goals rfl

theorem atot3913 : totK PD2M8K2 D2M8K2.u3913 = [0, 1573751611393, 5773957812310, 5739358776837, 1371185692638, 57237736717, 0, 0] := by
  rw [show D2M8K2.u3913 = KTree.node D2M8K2.u3905 (nat_lit 8770331) (nat_lit 2322485156) (nat_lit 0) D2M8K2.u3912 from rfl, totK_node, atot3905, atot3912]
  decide +kernel

theorem arows3928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3928 = true := by
  rw [show D2M8K2.u3928 = KTree.node D2M8K2.u3920 (nat_lit 8808794) (nat_lit 4217839901) (nat_lit 0) D2M8K2.u3927 from rfl, allE_node, arows3920, irow3928, arows3927]
  all_goals rfl

theorem atot3928 : totK PD2M8K2 D2M8K2.u3928 = [0, 1190892928414, 4810211766827, 6005937164904, 2135318759085, 138894878934, 1166720416, 0] := by
  rw [show D2M8K2.u3928 = KTree.node D2M8K2.u3920 (nat_lit 8808794) (nat_lit 4217839901) (nat_lit 0) D2M8K2.u3927 from rfl, totK_node, atot3920, atot3927]
  decide +kernel

theorem arows3944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3944 = true := by
  rw [show D2M8K2.u3944 = KTree.node D2M8K2.u3936 (nat_lit 8830715) (nat_lit 2879332006) (nat_lit 0) D2M8K2.u3943 from rfl, allE_node, arows3936, irow3944, arows3943]
  all_goals rfl

theorem atot3944 : totK PD2M8K2 D2M8K2.u3944 = [0, 799500920788, 4202438884713, 6300167978997, 2740962165463, 282224266110, 5134755853, 0] := by
  rw [show D2M8K2.u3944 = KTree.node D2M8K2.u3936 (nat_lit 8830715) (nat_lit 2879332006) (nat_lit 0) D2M8K2.u3943 from rfl, totK_node, atot3936, atot3943]
  decide +kernel

theorem arows3959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3959 = true := by
  rw [show D2M8K2.u3959 = KTree.node D2M8K2.u3951 (nat_lit 8850053) (nat_lit 1527955085) (nat_lit 0) D2M8K2.u3958 from rfl, allE_node, arows3951, irow3959, arows3958]
  all_goals rfl

theorem atot3959 : totK PD2M8K2 D2M8K2.u3959 = [0, 1191276516249, 4811791942622, 6014914054110, 2136041175016, 136757966536, 1200365979, 0] := by
  rw [show D2M8K2.u3959 = KTree.node D2M8K2.u3951 (nat_lit 8850053) (nat_lit 1527955085) (nat_lit 0) D2M8K2.u3958 from rfl, totK_node, atot3951, atot3958]
  decide +kernel

theorem arows3977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3977 = true := by
  rw [show D2M8K2.u3977 = KTree.node D2M8K2.u3969 (nat_lit 8872259) (nat_lit 2964435455) (nat_lit 0) D2M8K2.u3976 from rfl, allE_node, arows3969, irow3977, arows3976]
  all_goals rfl

theorem atot3977 : totK PD2M8K2 D2M8K2.u3977 = [0, 825969492826, 4278256977214, 6240003674647, 2710272089450, 287617328647, 5163565574, 0] := by
  rw [show D2M8K2.u3977 = KTree.node D2M8K2.u3969 (nat_lit 8872259) (nat_lit 2964435455) (nat_lit 0) D2M8K2.u3976 from rfl, totK_node, atot3969, atot3976]
  decide +kernel

theorem arows3992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3992 = true := by
  rw [show D2M8K2.u3992 = KTree.node D2M8K2.u3984 (nat_lit 8928686) (nat_lit 2071299541) (nat_lit 0) D2M8K2.u3991 from rfl, allE_node, arows3984, irow3992, arows3991]
  all_goals rfl

theorem atot3992 : totK PD2M8K2 D2M8K2.u3992 = [0, 1285435583121, 5189940421785, 6074556111203, 1702229872917, 61267281524, 0, 0] := by
  rw [show D2M8K2.u3992 = KTree.node D2M8K2.u3984 (nat_lit 8928686) (nat_lit 2071299541) (nat_lit 0) D2M8K2.u3991 from rfl, totK_node, atot3984, atot3991]
  decide +kernel

theorem arows4008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4008 = true := by
  rw [show D2M8K2.u4008 = KTree.node D2M8K2.u4000 (nat_lit 8947992) (nat_lit 2873806957) (nat_lit 0) D2M8K2.u4007 from rfl, allE_node, arows4000, irow4008, arows4007]
  all_goals rfl

theorem atot4008 : totK PD2M8K2 D2M8K2.u4008 = [0, 94445126902, 1948553916943, 6053956208462, 5067575442263, 936549121004, 32664957003, 0] := by
  rw [show D2M8K2.u4008 = KTree.node D2M8K2.u4000 (nat_lit 8947992) (nat_lit 2873806957) (nat_lit 0) D2M8K2.u4007 from rfl, totK_node, atot4000, atot4007]
  decide +kernel

theorem arows4023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4023 = true := by
  rw [show D2M8K2.u4023 = KTree.node D2M8K2.u4015 (nat_lit 9506983) (nat_lit 2233358517) (nat_lit 0) D2M8K2.u4022 from rfl, allE_node, arows4015, irow4023, arows4022]
  all_goals rfl

theorem atot4023 : totK PD2M8K2 D2M8K2.u4023 = [0, 1621584730183, 5772867316516, 5691280253795, 1416223443013, 60507770964, 0, 0] := by
  rw [show D2M8K2.u4023 = KTree.node D2M8K2.u4015 (nat_lit 9506983) (nat_lit 2233358517) (nat_lit 0) D2M8K2.u4022 from rfl, totK_node, atot4015, atot4022]
  decide +kernel

theorem arows4040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4040 = true := by
  rw [show D2M8K2.u4040 = KTree.node D2M8K2.u4032 (nat_lit 9523625) (nat_lit 1809120448) (nat_lit 0) D2M8K2.u4039 from rfl, allE_node, arows4032, irow4040, arows4039]
  all_goals rfl

theorem atot4040 : totK PD2M8K2 D2M8K2.u4040 = [0, 425375799150, 2906681959121, 6026982078251, 4242217263870, 886532541574, 42081742489, 0] := by
  rw [show D2M8K2.u4040 = KTree.node D2M8K2.u4032 (nat_lit 9523625) (nat_lit 1809120448) (nat_lit 0) D2M8K2.u4039 from rfl, totK_node, atot4032, atot4039]
  decide +kernel

theorem arows4055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4055 = true := by
  rw [show D2M8K2.u4055 = KTree.node D2M8K2.u4047 (nat_lit 9537443) (nat_lit 2837822155) (nat_lit 0) D2M8K2.u4054 from rfl, allE_node, arows4047, irow4055, arows4054]
  all_goals rfl

theorem atot4055 : totK PD2M8K2 D2M8K2.u4055 = [0, 753865312788, 3422743037497, 5636271470139, 3952384993180, 722544797507, 15936385454, 0] := by
  rw [show D2M8K2.u4055 = KTree.node D2M8K2.u4047 (nat_lit 9537443) (nat_lit 2837822155) (nat_lit 0) D2M8K2.u4054 from rfl, totK_node, atot4047, atot4054]
  decide +kernel

theorem arows4071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4071 = true := by
  rw [show D2M8K2.u4071 = KTree.node D2M8K2.u4063 (nat_lit 9554749) (nat_lit 1211979237) (nat_lit 0) D2M8K2.u4070 from rfl, allE_node, arows4063, irow4071, arows4070]
  all_goals rfl

theorem atot4071 : totK PD2M8K2 D2M8K2.u4071 = [0, 1267094710451, 5022030100319, 6003308068369, 2026188419141, 114087352796, 0, 0] := by
  rw [show D2M8K2.u4071 = KTree.node D2M8K2.u4063 (nat_lit 9554749) (nat_lit 1211979237) (nat_lit 0) D2M8K2.u4070 from rfl, totK_node, atot4063, atot4070]
  decide +kernel

theorem arows4086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4086 = true := by
  rw [show D2M8K2.u4086 = KTree.node D2M8K2.u4078 (nat_lit 9574298) (nat_lit 4225304539) (nat_lit 0) D2M8K2.u4085 from rfl, allE_node, arows4078, irow4086, arows4085]
  all_goals rfl

theorem atot4086 : totK PD2M8K2 D2M8K2.u4086 = [0, 564060001896, 3290052855473, 6211641659436, 3788335886236, 532350342008, 11412527294, 0] := by
  rw [show D2M8K2.u4086 = KTree.node D2M8K2.u4078 (nat_lit 9574298) (nat_lit 4225304539) (nat_lit 0) D2M8K2.u4085 from rfl, totK_node, atot4078, atot4085]
  decide +kernel

theorem arows4109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4109 = true := by
  rw [show D2M8K2.u4109 = KTree.node D2M8K2.u4101 (nat_lit 9593954) (nat_lit 3266617108) (nat_lit 0) D2M8K2.u4108 from rfl, allE_node, arows4101, irow4109, arows4108]
  all_goals rfl

theorem atot4109 : totK PD2M8K2 D2M8K2.u4109 = [0, 1457411654964, 5516847565600, 5854412992567, 1600224163372, 76365995811, 0, 0] := by
  rw [show D2M8K2.u4109 = KTree.node D2M8K2.u4101 (nat_lit 9593954) (nat_lit 3266617108) (nat_lit 0) D2M8K2.u4108 from rfl, totK_node, atot4101, atot4108]
  decide +kernel

theorem arows4124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4124 = true := by
  rw [show D2M8K2.u4124 = KTree.node D2M8K2.u4116 (nat_lit 9613291) (nat_lit 1538705123) (nat_lit 0) D2M8K2.u4123 from rfl, allE_node, arows4116, irow4124, arows4123]
  all_goals rfl

theorem atot4124 : totK PD2M8K2 D2M8K2.u4124 = [0, 190813401391, 2438693473795, 6463260296951, 4620781611416, 617138098160, 11552853615, 0] := by
  rw [show D2M8K2.u4124 = KTree.node D2M8K2.u4116 (nat_lit 9613291) (nat_lit 1538705123) (nat_lit 0) D2M8K2.u4123 from rfl, totK_node, atot4116, atot4123]
  decide +kernel

theorem arows4140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4140 = true := by
  rw [show D2M8K2.u4140 = KTree.node D2M8K2.u4132 (nat_lit 9629597) (nat_lit 2300477759) (nat_lit 0) D2M8K2.u4139 from rfl, allE_node, arows4132, irow4140, arows4139]
  all_goals rfl

theorem atot4140 : totK PD2M8K2 D2M8K2.u4140 = [0, 1640354367397, 5793333211529, 5615356113376, 1374690434085, 63902120717, 0, 0] := by
  rw [show D2M8K2.u4140 = KTree.node D2M8K2.u4132 (nat_lit 9629597) (nat_lit 2300477759) (nat_lit 0) D2M8K2.u4139 from rfl, totK_node, atot4132, atot4139]
  decide +kernel

theorem arows4155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4155 = true := by
  rw [show D2M8K2.u4155 = KTree.node D2M8K2.u4147 (nat_lit 9649420) (nat_lit 3757131422) (nat_lit 0) D2M8K2.u4154 from rfl, allE_node, arows4147, irow4155, arows4154]
  all_goals rfl

theorem atot4155 : totK PD2M8K2 D2M8K2.u4155 = [0, 209025771284, 2966013078395, 6945477161805, 3841499198474, 377182676110, 2586295899, 0] := by
  rw [show D2M8K2.u4155 = KTree.node D2M8K2.u4147 (nat_lit 9649420) (nat_lit 3757131422) (nat_lit 0) D2M8K2.u4154 from rfl, totK_node, atot4147, atot4154]
  decide +kernel

theorem arows4172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4172 = true := by
  rw [show D2M8K2.u4172 = KTree.node D2M8K2.u4164 (nat_lit 9670284) (nat_lit 1843411315) (nat_lit 0) D2M8K2.u4171 from rfl, allE_node, arows4164, irow4172, arows4171]
  all_goals rfl

theorem atot4172 : totK PD2M8K2 D2M8K2.u4172 = [0, 1655401455820, 5855560474716, 5628220376303, 1357889810322, 60980018079, 0, 0] := by
  rw [show D2M8K2.u4172 = KTree.node D2M8K2.u4164 (nat_lit 9670284) (nat_lit 1843411315) (nat_lit 0) D2M8K2.u4171 from rfl, totK_node, atot4164, atot4171]
  decide +kernel

theorem arows4187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4187 = true := by
  rw [show D2M8K2.u4187 = KTree.node D2M8K2.u4179 (nat_lit 9688148) (nat_lit 3547396218) (nat_lit 0) D2M8K2.u4186 from rfl, allE_node, arows4179, irow4187, arows4186]
  all_goals rfl

theorem atot4187 : totK PD2M8K2 D2M8K2.u4187 = [0, 340088530745, 2911963958739, 6562987430460, 4216643003493, 453755073160, 2516941024, 0] := by
  rw [show D2M8K2.u4187 = KTree.node D2M8K2.u4179 (nat_lit 9688148) (nat_lit 3547396218) (nat_lit 0) D2M8K2.u4186 from rfl, totK_node, atot4179, atot4186]
  decide +kernel

theorem arows4203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4203 = true := by
  rw [show D2M8K2.u4203 = KTree.node D2M8K2.u4195 (nat_lit 9751673) (nat_lit 1111686198) (nat_lit 0) D2M8K2.u4202 from rfl, allE_node, arows4195, irow4203, arows4202]
  all_goals rfl

theorem atot4203 : totK PD2M8K2 D2M8K2.u4203 = [0, 0, 1736433043429, 5804351847682, 5483779944326, 1409219257174, 64961201698, 0] := by
  rw [show D2M8K2.u4203 = KTree.node D2M8K2.u4195 (nat_lit 9751673) (nat_lit 1111686198) (nat_lit 0) D2M8K2.u4202 from rfl, totK_node, atot4195, atot4202]
  decide +kernel

theorem arows4218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4218 = true := by
  rw [show D2M8K2.u4218 = KTree.node D2M8K2.u4210 (nat_lit 9764800) (nat_lit 2974643527) (nat_lit 0) D2M8K2.u4217 from rfl, allE_node, arows4210, irow4218, arows4217]
  all_goals rfl

theorem atot4218 : totK PD2M8K2 D2M8K2.u4218 = [0, 0, 845744674632, 4165031081143, 5906379223907, 2865814815035, 626025011558, 36921873854] := by
  rw [show D2M8K2.u4218 = KTree.node D2M8K2.u4210 (nat_lit 9764800) (nat_lit 2974643527) (nat_lit 0) D2M8K2.u4217 from rfl, totK_node, atot4210, atot4217]
  decide +kernel

theorem arows4236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4236 = true := by
  rw [show D2M8K2.u4236 = KTree.node D2M8K2.u4228 (nat_lit 9781385) (nat_lit 1624211620) (nat_lit 0) D2M8K2.u4235 from rfl, allE_node, arows4228, irow4236, arows4235]
  all_goals rfl

theorem atot4236 : totK PD2M8K2 D2M8K2.u4236 = [0, 0, 320804550429, 2308159706043, 5773018547435, 4935033154667, 875901843406, 20725497737] := by
  rw [show D2M8K2.u4236 = KTree.node D2M8K2.u4228 (nat_lit 9781385) (nat_lit 1624211620) (nat_lit 0) D2M8K2.u4235 from rfl, totK_node, atot4228, atot4235]
  decide +kernel

theorem arows4251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4251 = true := by
  rw [show D2M8K2.u4251 = KTree.node D2M8K2.u4243 (nat_lit 9796169) (nat_lit 1614614815) (nat_lit 0) D2M8K2.u4250 from rfl, allE_node, arows4243, irow4251, arows4250]
  all_goals rfl

theorem atot4251 : totK PD2M8K2 D2M8K2.u4251 = [0, 0, 1696433788837, 5905151913887, 5586946978873, 1280603053933, 49168253304, 0] := by
  rw [show D2M8K2.u4251 = KTree.node D2M8K2.u4243 (nat_lit 9796169) (nat_lit 1614614815) (nat_lit 0) D2M8K2.u4250 from rfl, totK_node, atot4243, atot4250]
  decide +kernel

theorem arows4267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4267 = true := by
  rw [show D2M8K2.u4267 = KTree.node D2M8K2.u4259 (nat_lit 9817458) (nat_lit 2279335593) (nat_lit 0) D2M8K2.u4266 from rfl, allE_node, arows4259, irow4267, arows4266]
  all_goals rfl

theorem atot4267 : totK PD2M8K2 D2M8K2.u4267 = [0, 0, 320954541705, 3116614658857, 6698332608514, 3727098849592, 394651216547, 6546549506] := by
  rw [show D2M8K2.u4267 = KTree.node D2M8K2.u4259 (nat_lit 9817458) (nat_lit 2279335593) (nat_lit 0) D2M8K2.u4266 from rfl, totK_node, atot4259, atot4266]
  decide +kernel

theorem arows4282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4282 = true := by
  rw [show D2M8K2.u4282 = KTree.node D2M8K2.u4274 (nat_lit 9841057) (nat_lit 1503344942) (nat_lit 0) D2M8K2.u4281 from rfl, allE_node, arows4274, irow4282, arows4281]
  all_goals rfl

theorem atot4282 : totK PD2M8K2 D2M8K2.u4282 = [0, 0, 1696793673390, 5921029534960, 5591705066992, 1271333216029, 49270026795, 0] := by
  rw [show D2M8K2.u4282 = KTree.node D2M8K2.u4274 (nat_lit 9841057) (nat_lit 1503344942) (nat_lit 0) D2M8K2.u4281 from rfl, totK_node, atot4274, atot4281]
  decide +kernel

theorem arows4299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4299 = true := by
  rw [show D2M8K2.u4299 = KTree.node D2M8K2.u4291 (nat_lit 9862686) (nat_lit 3970774059) (nat_lit 0) D2M8K2.u4298 from rfl, allE_node, arows4291, irow4299, arows4298]
  all_goals rfl

theorem atot4299 : totK PD2M8K2 D2M8K2.u4299 = [0, 0, 319053168236, 3115745958455, 6637403683068, 3782587347439, 404426695628, 6624648996] := by
  rw [show D2M8K2.u4299 = KTree.node D2M8K2.u4291 (nat_lit 9862686) (nat_lit 3970774059) (nat_lit 0) D2M8K2.u4298 from rfl, totK_node, atot4291, atot4298]
  decide +kernel

theorem arows4314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4314 = true := by
  rw [show D2M8K2.u4314 = KTree.node D2M8K2.u4306 (nat_lit 9879168) (nat_lit 3480946997) (nat_lit 0) D2M8K2.u4313 from rfl, allE_node, arows4306, irow4314, arows4313]
  all_goals rfl

theorem atot4314 : totK PD2M8K2 D2M8K2.u4314 = [0, 0, 1692589357523, 5873077944341, 5523030843924, 1310490973683, 55802001651, 0] := by
  rw [show D2M8K2.u4314 = KTree.node D2M8K2.u4306 (nat_lit 9879168) (nat_lit 3480946997) (nat_lit 0) D2M8K2.u4313 from rfl, totK_node, atot4306, atot4313]
  decide +kernel

theorem arows4330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4330 = true := by
  rw [show D2M8K2.u4330 = KTree.node D2M8K2.u4322 (nat_lit 9901922) (nat_lit 4045297904) (nat_lit 0) D2M8K2.u4329 from rfl, allE_node, arows4322, irow4330, arows4329]
  all_goals rfl

theorem atot4330 : totK PD2M8K2 D2M8K2.u4330 = [0, 0, 416375132788, 3672478721098, 7019153302771, 3050841323398, 236174558708, 1429815836] := by
  rw [show D2M8K2.u4330 = KTree.node D2M8K2.u4322 (nat_lit 9901922) (nat_lit 4045297904) (nat_lit 0) D2M8K2.u4329 from rfl, totK_node, atot4322, atot4329]
  decide +kernel

theorem arows4345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4345 = true := by
  rw [show D2M8K2.u4345 = KTree.node D2M8K2.u4337 (nat_lit 9921932) (nat_lit 2922854944) (nat_lit 0) D2M8K2.u4344 from rfl, allE_node, arows4337, irow4345, arows4344]
  all_goals rfl

theorem atot4345 : totK PD2M8K2 D2M8K2.u4345 = [0, 0, 1607119128169, 5716247542090, 5709417714543, 1432988234925, 53136258667, 0] := by
  rw [show D2M8K2.u4345 = KTree.node D2M8K2.u4337 (nat_lit 9921932) (nat_lit 2922854944) (nat_lit 0) D2M8K2.u4344 from rfl, totK_node, atot4337, atot4344]
  decide +kernel

theorem arows4364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4364 = true := by
  rw [show D2M8K2.u4364 = KTree.node D2M8K2.u4356 (nat_lit 9943803) (nat_lit 3755701842) (nat_lit 0) D2M8K2.u4363 from rfl, allE_node, arows4356, irow4364, arows4363]
  all_goals rfl

theorem atot4364 : totK PD2M8K2 D2M8K2.u4364 = [0, 327677273344, 744594656918, 2389302696014, 5991732799485, 4297544856751, 575351781357, 12189850367] := by
  rw [show D2M8K2.u4364 = KTree.node D2M8K2.u4356 (nat_lit 9943803) (nat_lit 3755701842) (nat_lit 0) D2M8K2.u4363 from rfl, totK_node, atot4356, atot4363]
  decide +kernel

theorem arows4379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4379 = true := by
  rw [show D2M8K2.u4379 = KTree.node D2M8K2.u4371 (nat_lit 9968211) (nat_lit 2493610216) (nat_lit 0) D2M8K2.u4378 from rfl, allE_node, arows4371, irow4379, arows4378]
  all_goals rfl

theorem atot4379 : totK PD2M8K2 D2M8K2.u4379 = [0, 1319872715774, 5501333457608, 6088237222888, 1404463580389, 47960113529, 0, 0] := by
  rw [show D2M8K2.u4379 = KTree.node D2M8K2.u4371 (nat_lit 9968211) (nat_lit 2493610216) (nat_lit 0) D2M8K2.u4378 from rfl, totK_node, atot4371, atot4378]
  decide +kernel

theorem arows4395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4395 = true := by
  rw [show D2M8K2.u4395 = KTree.node D2M8K2.u4387 (nat_lit 9993000) (nat_lit 3442028263) (nat_lit 0) D2M8K2.u4394 from rfl, allE_node, arows4387, irow4395, arows4394]
  all_goals rfl

theorem atot4395 : totK PD2M8K2 D2M8K2.u4395 = [0, 871790450706, 4128467898264, 6369273723028, 2849826967922, 217814875096, 1369150432, 0] := by
  rw [show D2M8K2.u4395 = KTree.node D2M8K2.u4387 (nat_lit 9993000) (nat_lit 3442028263) (nat_lit 0) D2M8K2.u4394 from rfl, totK_node, atot4387, atot4394]
  decide +kernel

theorem arows4410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4410 = true := by
  rw [show D2M8K2.u4410 = KTree.node D2M8K2.u4402 (nat_lit 10011559) (nat_lit 2363600661) (nat_lit 0) D2M8K2.u4409 from rfl, allE_node, arows4402, irow4410, arows4409]
  all_goals rfl

theorem atot4410 : totK PD2M8K2 D2M8K2.u4410 = [0, 1176342406934, 4853640714896, 5959440870909, 2231357358126, 349459002256, 25191558099, 0] := by
  rw [show D2M8K2.u4410 = KTree.node D2M8K2.u4402 (nat_lit 10011559) (nat_lit 2363600661) (nat_lit 0) D2M8K2.u4409 from rfl, totK_node, atot4402, atot4409]
  decide +kernel

theorem arows4427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4427 = true := by
  rw [show D2M8K2.u4427 = KTree.node D2M8K2.u4419 (nat_lit 10028793) (nat_lit 1838625188) (nat_lit 0) D2M8K2.u4426 from rfl, allE_node, arows4419, irow4427, arows4426]
  all_goals rfl

theorem atot4427 : totK PD2M8K2 D2M8K2.u4427 = [0, 0, 1598247734793, 5919623454103, 5817925255141, 1168732586928, 26008278002, 0] := by
  rw [show D2M8K2.u4427 = KTree.node D2M8K2.u4419 (nat_lit 10028793) (nat_lit 1838625188) (nat_lit 0) D2M8K2.u4426 from rfl, totK_node, atot4419, atot4426]
  decide +kernel

theorem arows4442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4442 = true := by
  rw [show D2M8K2.u4442 = KTree.node D2M8K2.u4434 (nat_lit 10042891) (nat_lit 1745920199) (nat_lit 0) D2M8K2.u4441 from rfl, allE_node, arows4434, irow4442, arows4441]
  all_goals rfl

theorem atot4442 : totK PD2M8K2 D2M8K2.u4442 = [0, 1686323782831, 5864900645037, 5489894137212, 1284925484308, 124994030231, 6818291842, 0] := by
  rw [show D2M8K2.u4442 = KTree.node D2M8K2.u4434 (nat_lit 10042891) (nat_lit 1745920199) (nat_lit 0) D2M8K2.u4441 from rfl, totK_node, atot4434, atot4441]
  decide +kernel

theorem arows4458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4458 = true := by
  rw [show D2M8K2.u4458 = KTree.node D2M8K2.u4450 (nat_lit 10059889) (nat_lit 1482546899) (nat_lit 0) D2M8K2.u4457 from rfl, allE_node, arows4450, irow4458, arows4457]
  all_goals rfl

theorem atot4458 : totK PD2M8K2 D2M8K2.u4458 = [0, 420804927456, 3125489150106, 6420679663308, 3783445474697, 511632190206, 14222663156, 0] := by
  rw [show D2M8K2.u4458 = KTree.node D2M8K2.u4450 (nat_lit 10059889) (nat_lit 1482546899) (nat_lit 0) D2M8K2.u4457 from rfl, totK_node, atot4450, atot4457]
  decide +kernel

theorem arows4473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4473 = true := by
  rw [show D2M8K2.u4473 = KTree.node D2M8K2.u4465 (nat_lit 10122120) (nat_lit 3530775930) (nat_lit 0) D2M8K2.u4472 from rfl, allE_node, arows4465, irow4473, arows4472]
  all_goals rfl

theorem atot4473 : totK PD2M8K2 D2M8K2.u4473 = [0, 1220255049712, 4715000171913, 5761824214906, 2397817135379, 247445387878, 4574395652, 0] := by
  rw [show D2M8K2.u4473 = KTree.node D2M8K2.u4465 (nat_lit 10122120) (nat_lit 3530775930) (nat_lit 0) D2M8K2.u4472 from rfl, totK_node, atot4465, atot4472]
  decide +kernel

theorem arows4491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4491 = true := by
  rw [show D2M8K2.u4491 = KTree.node D2M8K2.u4483 (nat_lit 10135966) (nat_lit 2520911516) (nat_lit 0) D2M8K2.u4490 from rfl, allE_node, arows4483, irow4491, arows4490]
  all_goals rfl

theorem atot4491 : totK PD2M8K2 D2M8K2.u4491 = [0, 762937489528, 4153603921347, 6506731008610, 2709696324589, 204304531880, 1138244013, 0] := by
  rw [show D2M8K2.u4491 = KTree.node D2M8K2.u4483 (nat_lit 10135966) (nat_lit 2520911516) (nat_lit 0) D2M8K2.u4490 from rfl, totK_node, atot4483, atot4490]
  decide +kernel

theorem arows4506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4506 = true := by
  rw [show D2M8K2.u4506 = KTree.node D2M8K2.u4498 (nat_lit 10162518) (nat_lit 3524409613) (nat_lit 0) D2M8K2.u4505 from rfl, allE_node, arows4498, irow4506, arows4505]
  all_goals rfl

theorem atot4506 : totK PD2M8K2 D2M8K2.u4506 = [0, 1224639651131, 4697157722060, 5758305865779, 2472047999337, 287195922215, 4977114383, 0] := by
  rw [show D2M8K2.u4506 = KTree.node D2M8K2.u4498 (nat_lit 10162518) (nat_lit 3524409613) (nat_lit 0) D2M8K2.u4505 from rfl, totK_node, atot4498, atot4505]
  decide +kernel

theorem arows4522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4522 = true := by
  rw [show D2M8K2.u4522 = KTree.node D2M8K2.u4514 (nat_lit 10180038) (nat_lit 3471070035) (nat_lit 0) D2M8K2.u4521 from rfl, allE_node, arows4514, irow4522, arows4521]
  all_goals rfl

theorem atot4522 : totK PD2M8K2 D2M8K2.u4522 = [0, 770562027082, 4122250461324, 6490090020222, 2871848676182, 228847280669, 1310285577, 0] := by
  rw [show D2M8K2.u4522 = KTree.node D2M8K2.u4514 (nat_lit 10180038) (nat_lit 3471070035) (nat_lit 0) D2M8K2.u4521 from rfl, totK_node, atot4514, atot4521]
  decide +kernel

theorem arows4537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4537 = true := by
  rw [show D2M8K2.u4537 = KTree.node D2M8K2.u4529 (nat_lit 10200253) (nat_lit 1260441193) (nat_lit 0) D2M8K2.u4536 from rfl, allE_node, arows4529, irow4537, arows4536]
  all_goals rfl

theorem atot4537 : totK PD2M8K2 D2M8K2.u4537 = [0, 0, 1861281734593, 6281907401608, 5298594541444, 893949154387, 25707704229, 0] := by
  rw [show D2M8K2.u4537 = KTree.node D2M8K2.u4529 (nat_lit 10200253) (nat_lit 1260441193) (nat_lit 0) D2M8K2.u4536 from rfl, totK_node, atot4529, atot4536]
  decide +kernel

theorem arows4554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4554 = true := by
  rw [show D2M8K2.u4554 = KTree.node D2M8K2.u4546 (nat_lit 10247948) (nat_lit 3713158409) (nat_lit 0) D2M8K2.u4553 from rfl, allE_node, arows4546, irow4554, arows4553]
  all_goals rfl

theorem atot4554 : totK PD2M8K2 D2M8K2.u4554 = [0, 0, 1758774283632, 6054601767834, 5493210728191, 1147040980391, 48847743377, 0] := by
  rw [show D2M8K2.u4554 = KTree.node D2M8K2.u4546 (nat_lit 10247948) (nat_lit 3713158409) (nat_lit 0) D2M8K2.u4553 from rfl, totK_node, atot4546, atot4553]
  decide +kernel

theorem arows4569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4569 = true := by
  rw [show D2M8K2.u4569 = KTree.node D2M8K2.u4561 (nat_lit 10261767) (nat_lit 3618891798) (nat_lit 0) D2M8K2.u4568 from rfl, allE_node, arows4561, irow4569, arows4568]
  all_goals rfl

theorem atot4569 : totK PD2M8K2 D2M8K2.u4569 = [0, 0, 1814806356745, 6209041966690, 5465445262454, 992239926265, 22993077838, 0] := by
  rw [show D2M8K2.u4569 = KTree.node D2M8K2.u4561 (nat_lit 10261767) (nat_lit 3618891798) (nat_lit 0) D2M8K2.u4568 from rfl, totK_node, atot4561, atot4568]
  decide +kernel

theorem arows4585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4585 = true := by
  rw [show D2M8K2.u4585 = KTree.node D2M8K2.u4577 (nat_lit 10299482) (nat_lit 4211462680) (nat_lit 0) D2M8K2.u4584 from rfl, allE_node, arows4577, irow4585, arows4584]
  all_goals rfl

theorem atot4585 : totK PD2M8K2 D2M8K2.u4585 = [0, 0, 1365059291899, 5445844772250, 5980868150657, 1535817335017, 60423218448, 0] := by
  rw [show D2M8K2.u4585 = KTree.node D2M8K2.u4577 (nat_lit 10299482) (nat_lit 4211462680) (nat_lit 0) D2M8K2.u4584 from rfl, totK_node, atot4577, atot4584]
  decide +kernel

theorem arows4600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4600 = true := by
  rw [show D2M8K2.u4600 = KTree.node D2M8K2.u4592 (nat_lit 10320347) (nat_lit 2197773163) (nat_lit 0) D2M8K2.u4599 from rfl, allE_node, arows4592, irow4600, arows4599]
  all_goals rfl

theorem atot4600 : totK PD2M8K2 D2M8K2.u4600 = [0, 0, 478410727792, 3380452035039, 6503411618686, 3372494091344, 404365534648, 7048116272] := by
  rw [show D2M8K2.u4600 = KTree.node D2M8K2.u4592 (nat_lit 10320347) (nat_lit 2197773163) (nat_lit 0) D2M8K2.u4599 from rfl, totK_node, atot4592, atot4599]
  decide +kernel

theorem arows4620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4620 = true := by
  rw [show D2M8K2.u4620 = KTree.node D2M8K2.u4612 (nat_lit 10378570) (nat_lit 1641333621) (nat_lit 2048) D2M8K2.u4619 from rfl, allE_node, arows4612, irow4620, arows4619]
  all_goals rfl

theorem atot4620 : totK PD2M8K2 D2M8K2.u4620 = [0, 0, 1498235114484, 5759110680869, 5826370375050, 1298096625426, 40160882355, 0] := by
  rw [show D2M8K2.u4620 = KTree.node D2M8K2.u4612 (nat_lit 10378570) (nat_lit 1641333621) (nat_lit 2048) D2M8K2.u4619 from rfl, totK_node, atot4612, atot4619]
  decide +kernel

theorem arows4635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4635 = true := by
  rw [show D2M8K2.u4635 = KTree.node D2M8K2.u4627 (nat_lit 10404916) (nat_lit 4062894510) (nat_lit 0) D2M8K2.u4634 from rfl, allE_node, arows4627, irow4635, arows4634]
  all_goals rfl

theorem atot4635 : totK PD2M8K2 D2M8K2.u4635 = [0, 0, 797685631964, 4333355219202, 6525770324708, 2511105193299, 187111843998, 1394496256] := by
  rw [show D2M8K2.u4635 = KTree.node D2M8K2.u4627 (nat_lit 10404916) (nat_lit 4062894510) (nat_lit 0) D2M8K2.u4634 from rfl, totK_node, atot4627, atot4634]
  decide +kernel

theorem arows4651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4651 = true := by
  rw [show D2M8K2.u4651 = KTree.node D2M8K2.u4643 (nat_lit 10427389) (nat_lit 1219182911) (nat_lit 0) D2M8K2.u4650 from rfl, allE_node, arows4643, irow4651, arows4650]
  all_goals rfl

theorem atot4651 : totK PD2M8K2 D2M8K2.u4651 = [0, 599936696520, 3112118638803, 5623335117884, 4214987459912, 947364755782, 34695865467, 0] := by
  rw [show D2M8K2.u4651 = KTree.node D2M8K2.u4643 (nat_lit 10427389) (nat_lit 1219182911) (nat_lit 0) D2M8K2.u4650 from rfl, totK_node, atot4643, atot4650]
  decide +kernel

theorem arows4666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4666 = true := by
  rw [show D2M8K2.u4666 = KTree.node D2M8K2.u4658 (nat_lit 10468930) (nat_lit 4141143164) (nat_lit 0) D2M8K2.u4665 from rfl, allE_node, arows4658, irow4666, arows4665]
  all_goals rfl

theorem atot4666 : totK PD2M8K2 D2M8K2.u4666 = [0, 1047908488477, 4659777281368, 6179303828563, 2243797676322, 168476070741, 1369150432, 0] := by
  rw [show D2M8K2.u4666 = KTree.node D2M8K2.u4658 (nat_lit 10468930) (nat_lit 4141143164) (nat_lit 0) D2M8K2.u4665 from rfl, totK_node, atot4658, atot4665]
  decide +kernel

theorem arows4683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4683 = true := by
  rw [show D2M8K2.u4683 = KTree.node D2M8K2.u4675 (nat_lit 10498153) (nat_lit 798911842) (nat_lit 0) D2M8K2.u4682 from rfl, allE_node, arows4675, irow4683, arows4682]
  all_goals rfl

theorem atot4683 : totK PD2M8K2 D2M8K2.u4683 = [0, 1218909925012, 4932827397094, 6185588520579, 2122695758988, 108949740395, 0, 0] := by
  rw [show D2M8K2.u4683 = KTree.node D2M8K2.u4675 (nat_lit 10498153) (nat_lit 798911842) (nat_lit 0) D2M8K2.u4682 from rfl, totK_node, atot4675, atot4682]
  decide +kernel

theorem arows4698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4698 = true := by
  rw [show D2M8K2.u4698 = KTree.node D2M8K2.u4690 (nat_lit 10511794) (nat_lit 3952244273) (nat_lit 0) D2M8K2.u4697 from rfl, allE_node, arows4690, irow4698, arows4697]
  all_goals rfl

theorem atot4698 : totK PD2M8K2 D2M8K2.u4698 = [0, 829394532047, 4066489750560, 5959054653198, 3032957516262, 646676829040, 36921873854, 0] := by
  rw [show D2M8K2.u4698 = KTree.node D2M8K2.u4690 (nat_lit 10511794) (nat_lit 3952244273) (nat_lit 0) D2M8K2.u4697 from rfl, totK_node, atot4690, atot4697]
  decide +kernel

theorem arows4714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4714 = true := by
  rw [show D2M8K2.u4714 = KTree.node D2M8K2.u4706 (nat_lit 10529043) (nat_lit 3699449802) (nat_lit 0) D2M8K2.u4713 from rfl, allE_node, arows4706, irow4714, arows4713]
  all_goals rfl

theorem atot4714 : totK PD2M8K2 D2M8K2.u4714 = [0, 397564749128, 2454413291548, 5709368273149, 4923359865654, 934882846918, 21096254089, 0] := by
  rw [show D2M8K2.u4714 = KTree.node D2M8K2.u4706 (nat_lit 10529043) (nat_lit 3699449802) (nat_lit 0) D2M8K2.u4713 from rfl, totK_node, atot4706, atot4713]
  decide +kernel

theorem arows4729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4729 = true := by
  rw [show D2M8K2.u4729 = KTree.node D2M8K2.u4721 (nat_lit 10587586) (nat_lit 4092315088) (nat_lit 0) D2M8K2.u4728 from rfl, allE_node, arows4721, irow4729, arows4728]
  all_goals rfl

theorem atot4729 : totK PD2M8K2 D2M8K2.u4729 = [0, 1709996110766, 5908847031831, 5572777927911, 1286253410392, 55768132743, 0, 0] := by
  rw [show D2M8K2.u4729 = KTree.node D2M8K2.u4721 (nat_lit 10587586) (nat_lit 4092315088) (nat_lit 0) D2M8K2.u4728 from rfl, totK_node, atot4721, atot4728]
  decide +kernel

theorem arows4747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4747 = true := by
  rw [show D2M8K2.u4747 = KTree.node D2M8K2.u4739 (nat_lit 10606630) (nat_lit 2752155445) (nat_lit 0) D2M8K2.u4746 from rfl, allE_node, arows4739, irow4747, arows4746]
  all_goals rfl

theorem atot4747 : totK PD2M8K2 D2M8K2.u4747 = [0, 0, 2147119197581, 6612023646091, 4721896757833, 688696670054, 19065934916, 0] := by
  rw [show D2M8K2.u4747 = KTree.node D2M8K2.u4739 (nat_lit 10606630) (nat_lit 2752155445) (nat_lit 0) D2M8K2.u4746 from rfl, totK_node, atot4739, atot4746]
  decide +kernel

theorem arows4762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4762 = true := by
  rw [show D2M8K2.u4762 = KTree.node D2M8K2.u4754 (nat_lit 10622491) (nat_lit 1698073983) (nat_lit 0) D2M8K2.u4761 from rfl, allE_node, arows4754, irow4762, arows4761]
  all_goals rfl

theorem atot4762 : totK PD2M8K2 D2M8K2.u4762 = [0, 1547648331122, 5549721249147, 5656565903520, 1641395938191, 95923307335, 0, 0] := by
  rw [show D2M8K2.u4762 = KTree.node D2M8K2.u4754 (nat_lit 10622491) (nat_lit 1698073983) (nat_lit 0) D2M8K2.u4761 from rfl, totK_node, atot4754, atot4761]
  decide +kernel

theorem arows4778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4778 = true := by
  rw [show D2M8K2.u4778 = KTree.node D2M8K2.u4770 (nat_lit 10640252) (nat_lit 3298592629) (nat_lit 0) D2M8K2.u4777 from rfl, allE_node, arows4770, irow4778, arows4777]
  all_goals rfl

theorem atot4778 : totK PD2M8K2 D2M8K2.u4778 = [0, 435739754619, 3625818150472, 6903037730366, 3134241096057, 233281056795, 1138244013, 0] := by
  rw [show D2M8K2.u4778 = KTree.node D2M8K2.u4770 (nat_lit 10640252) (nat_lit 3298592629) (nat_lit 0) D2M8K2.u4777 from rfl, totK_node, atot4770, atot4777]
  decide +kernel

theorem arows4793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4793 = true := by
  rw [show D2M8K2.u4793 = KTree.node D2M8K2.u4785 (nat_lit 10663247) (nat_lit 2159978722) (nat_lit 0) D2M8K2.u4792 from rfl, allE_node, arows4785, irow4793, arows4792]
  all_goals rfl

theorem atot4793 : totK PD2M8K2 D2M8K2.u4793 = [0, 1555132162393, 5230722927526, 5410529619007, 2049262459914, 254932209829, 4977114383, 0] := by
  rw [show D2M8K2.u4793 = KTree.node D2M8K2.u4785 (nat_lit 10663247) (nat_lit 2159978722) (nat_lit 0) D2M8K2.u4792 from rfl, totK_node, atot4785, atot4792]
  decide +kernel

theorem arows4810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4810 = true := by
  rw [show D2M8K2.u4810 = KTree.node D2M8K2.u4802 (nat_lit 10680348) (nat_lit 3072718538) (nat_lit 0) D2M8K2.u4809 from rfl, allE_node, arows4802, irow4810, arows4809]
  all_goals rfl

theorem atot4810 : totK PD2M8K2 D2M8K2.u4810 = [0, 440288014109, 3357919511928, 6636115551787, 3664125238403, 365358832393, 2745449626, 0] := by
  rw [show D2M8K2.u4810 = KTree.node D2M8K2.u4802 (nat_lit 10680348) (nat_lit 3072718538) (nat_lit 0) D2M8K2.u4809 from rfl, totK_node, atot4802, atot4809]
  decide +kernel

theorem arows4825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4825 = true := by
  rw [show D2M8K2.u4825 = KTree.node D2M8K2.u4817 (nat_lit 10700545) (nat_lit 1427048294) (nat_lit 0) D2M8K2.u4824 from rfl, allE_node, arows4817, irow4825, arows4824]
  all_goals rfl

theorem atot4825 : totK PD2M8K2 D2M8K2.u4825 = [0, 0, 1929938640965, 6342233538374, 5125463460510, 848896680940, 25481384243, 0] := by
  rw [show D2M8K2.u4825 = KTree.node D2M8K2.u4817 (nat_lit 10700545) (nat_lit 1427048294) (nat_lit 0) D2M8K2.u4824 from rfl, totK_node, atot4817, atot4824]
  decide +kernel

theorem arows4841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4841 = true := by
  rw [show D2M8K2.u4841 = KTree.node D2M8K2.u4833 (nat_lit 10748747) (nat_lit 2448180828) (nat_lit 0) D2M8K2.u4840 from rfl, allE_node, arows4833, irow4841, arows4840]
  all_goals rfl

theorem atot4841 : totK PD2M8K2 D2M8K2.u4841 = [0, 0, 1851675726186, 6052035037369, 5407657712780, 1246107756673, 52061150024, 0] := by
  rw [show D2M8K2.u4841 = KTree.node D2M8K2.u4833 (nat_lit 10748747) (nat_lit 2448180828) (nat_lit 0) D2M8K2.u4840 from rfl, totK_node, atot4833, atot4840]
  decide +kernel

theorem arows4856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4856 = true := by
  rw [show D2M8K2.u4856 = KTree.node D2M8K2.u4848 (nat_lit 10825495) (nat_lit 2226047669) (nat_lit 0) D2M8K2.u4855 from rfl, allE_node, arows4848, irow4856, arows4855]
  all_goals rfl

theorem atot4856 : totK PD2M8K2 D2M8K2.u4856 = [0, 0, 1682559368640, 5868613269652, 5589842947189, 1288246482018, 47756256245, 0] := by
  rw [show D2M8K2.u4856 = KTree.node D2M8K2.u4848 (nat_lit 10825495) (nat_lit 2226047669) (nat_lit 0) D2M8K2.u4855 from rfl, totK_node, atot4848, atot4855]
  decide +kernel

theorem arows4875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4875 = true := by
  rw [show D2M8K2.u4875 = KTree.node D2M8K2.u4867 (nat_lit 10842256) (nat_lit 3614977210) (nat_lit 0) D2M8K2.u4874 from rfl, allE_node, arows4867, irow4875, arows4874]
  all_goals rfl

theorem atot4875 : totK PD2M8K2 D2M8K2.u4875 = [0, 0, 1007165001149, 4901050399575, 6427463630698, 1900642778579, 86484849529, 0] := by
  rw [show D2M8K2.u4875 = KTree.node D2M8K2.u4867 (nat_lit 10842256) (nat_lit 3614977210) (nat_lit 0) D2M8K2.u4874 from rfl, totK_node, atot4867, atot4874]
  decide +kernel

theorem arows4890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4890 = true := by
  rw [show D2M8K2.u4890 = KTree.node D2M8K2.u4882 (nat_lit 10863802) (nat_lit 3946002751) (nat_lit 0) D2M8K2.u4889 from rfl, allE_node, arows4882, irow4890, arows4889]
  all_goals rfl

theorem atot4890 : totK PD2M8K2 D2M8K2.u4890 = [0, 0, 901689708030, 4034487703020, 5978380818970, 2966401819048, 374651049054, 7105533120] := by
  rw [show D2M8K2.u4890 = KTree.node D2M8K2.u4882 (nat_lit 10863802) (nat_lit 3946002751) (nat_lit 0) D2M8K2.u4889 from rfl, totK_node, atot4882, atot4889]
  decide +kernel

theorem arows4906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4906 = true := by
  rw [show D2M8K2.u4906 = KTree.node D2M8K2.u4898 (nat_lit 10880361) (nat_lit 1829442760) (nat_lit 0) D2M8K2.u4905 from rfl, allE_node, arows4898, irow4906, arows4905]
  all_goals rfl

theorem atot4906 : totK PD2M8K2 D2M8K2.u4906 = [0, 0, 1074912440347, 5226750244608, 6362094121234, 1633985334031, 55347602865, 0] := by
  rw [show D2M8K2.u4906 = KTree.node D2M8K2.u4898 (nat_lit 10880361) (nat_lit 1829442760) (nat_lit 0) D2M8K2.u4905 from rfl, totK_node, atot4898, atot4905]
  decide +kernel

theorem arows4921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4921 = true := by
  rw [show D2M8K2.u4921 = KTree.node D2M8K2.u4913 (nat_lit 10911002) (nat_lit 4144112085) (nat_lit 0) D2M8K2.u4920 from rfl, allE_node, arows4913, irow4921, arows4920]
  all_goals rfl

theorem atot4921 : totK PD2M8K2 D2M8K2.u4921 = [0, 0, 1313970028509, 4898235976216, 5897601778964, 2160167052748, 170525942102, 1430229726] := by
  rw [show D2M8K2.u4921 = KTree.node D2M8K2.u4913 (nat_lit 10911002) (nat_lit 4144112085) (nat_lit 0) D2M8K2.u4920 from rfl, totK_node, atot4913, atot4920]
  decide +kernel

theorem arows4938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4938 = true := by
  rw [show D2M8K2.u4938 = KTree.node D2M8K2.u4930 (nat_lit 10948874) (nat_lit 2375474857) (nat_lit 0) D2M8K2.u4937 from rfl, allE_node, arows4930, irow4938, arows4937]
  all_goals rfl

theorem atot4938 : totK PD2M8K2 D2M8K2.u4938 = [0, 976195357934, 3946009715123, 5409503232816, 3304077538957, 744413044381, 27852771540, 0] := by
  rw [show D2M8K2.u4938 = KTree.node D2M8K2.u4930 (nat_lit 10948874) (nat_lit 2375474857) (nat_lit 0) D2M8K2.u4937 from rfl, totK_node, atot4930, atot4937]
  decide +kernel

theorem arows4953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4953 = true := by
  rw [show D2M8K2.u4953 = KTree.node D2M8K2.u4945 (nat_lit 10970187) (nat_lit 1247752670) (nat_lit 2048) D2M8K2.u4952 from rfl, allE_node, arows4945, irow4953, arows4952]
  all_goals rfl

theorem atot4953 : totK PD2M8K2 D2M8K2.u4953 = [0, 668131208094, 4014773402482, 6700238846711, 2670527793392, 181336677148, 1369150432, 0] := by
  rw [show D2M8K2.u4953 = KTree.node D2M8K2.u4945 (nat_lit 10970187) (nat_lit 1247752670) (nat_lit 2048) D2M8K2.u4952 from rfl, totK_node, atot4945, atot4952]
  decide +kernel

theorem arows4969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4969 = true := by
  rw [show D2M8K2.u4969 = KTree.node D2M8K2.u4961 (nat_lit 10998629) (nat_lit 2374331571) (nat_lit 0) D2M8K2.u4968 from rfl, allE_node, arows4961, irow4969, arows4968]
  all_goals rfl

theorem atot4969 : totK PD2M8K2 D2M8K2.u4969 = [0, 1663405509495, 5658232692337, 5615518234977, 1538241151549, 77758698482, 0, 0] := by
  rw [show D2M8K2.u4969 = KTree.node D2M8K2.u4961 (nat_lit 10998629) (nat_lit 2374331571) (nat_lit 0) D2M8K2.u4968 from rfl, totK_node, atot4961, atot4968]
  decide +kernel

theorem arows4984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4984 = true := by
  rw [show D2M8K2.u4984 = KTree.node D2M8K2.u4976 (nat_lit 11016346) (nat_lit 3900895255) (nat_lit 0) D2M8K2.u4983 from rfl, allE_node, arows4976, irow4984, arows4983]
  all_goals rfl

theorem atot4984 : totK PD2M8K2 D2M8K2.u4984 = [0, 378543555504, 3035391022321, 6149787139962, 4098944388139, 875186404466, 42081742489, 0] := by
  rw [show D2M8K2.u4984 = KTree.node D2M8K2.u4976 (nat_lit 11016346) (nat_lit 3900895255) (nat_lit 0) D2M8K2.u4983 from rfl, totK_node, atot4976, atot4983]
  decide +kernel

theorem arows5002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5002 = true := by
  rw [show D2M8K2.u5002 = KTree.node D2M8K2.u4994 (nat_lit 11030462) (nat_lit 3856813025) (nat_lit 0) D2M8K2.u5001 from rfl, allE_node, arows4994, irow5002, arows5001]
  all_goals rfl

theorem atot5002 : totK PD2M8K2 D2M8K2.u5002 = [0, 797183534328, 3473147637085, 5586312391140, 3943062218781, 718306033451, 15936385454, 0] := by
  rw [show D2M8K2.u5002 = KTree.node D2M8K2.u4994 (nat_lit 11030462) (nat_lit 3856813025) (nat_lit 0) D2M8K2.u5001 from rfl, totK_node, atot4994, atot5001]
  decide +kernel

theorem arows5017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5017 = true := by
  rw [show D2M8K2.u5017 = KTree.node D2M8K2.u5009 (nat_lit 11047296) (nat_lit 3458864538) (nat_lit 0) D2M8K2.u5016 from rfl, allE_node, arows5009, irow5017, arows5016]
  all_goals rfl

theorem atot5017 : totK PD2M8K2 D2M8K2.u5017 = [0, 1189599119018, 4821784628684, 5992287103154, 2190896104270, 155990244956, 1206465782, 0] := by
  rw [show D2M8K2.u5017 = KTree.node D2M8K2.u5009 (nat_lit 11047296) (nat_lit 3458864538) (nat_lit 0) D2M8K2.u5016 from rfl, totK_node, atot5009, atot5016]
  decide +kernel

theorem arows5033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5033 = true := by
  rw [show D2M8K2.u5033 = KTree.node D2M8K2.u5025 (nat_lit 11067130) (nat_lit 1715016117) (nat_lit 0) D2M8K2.u5032 from rfl, allE_node, arows5025, irow5033, arows5032]
  all_goals rfl

theorem atot5033 : totK PD2M8K2 D2M8K2.u5033 = [0, 536102949317, 3233566570455, 6200413312349, 3757100112757, 570253733622, 17590593026, 0] := by
  rw [show D2M8K2.u5033 = KTree.node D2M8K2.u5025 (nat_lit 11067130) (nat_lit 1715016117) (nat_lit 0) D2M8K2.u5032 from rfl, totK_node, atot5025, atot5032]
  decide +kernel

theorem arows5048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5048 = true := by
  rw [show D2M8K2.u5048 = KTree.node D2M8K2.u5040 (nat_lit 11086609) (nat_lit 1160266509) (nat_lit 0) D2M8K2.u5047 from rfl, allE_node, arows5040, irow5048, arows5047]
  all_goals rfl

theorem atot5048 : totK PD2M8K2 D2M8K2.u5048 = [0, 1451211497050, 5519135126178, 5865441683973, 1587906222029, 74065330209, 0, 0] := by
  rw [show D2M8K2.u5048 = KTree.node D2M8K2.u5040 (nat_lit 11086609) (nat_lit 1160266509) (nat_lit 0) D2M8K2.u5047 from rfl, totK_node, atot5040, atot5047]
  decide +kernel

theorem arows5065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5065 = true := by
  rw [show D2M8K2.u5065 = KTree.node D2M8K2.u5057 (nat_lit 11106254) (nat_lit 3600097380) (nat_lit 0) D2M8K2.u5064 from rfl, allE_node, arows5057, irow5065, arows5064]
  all_goals rfl

theorem atot5065 : totK PD2M8K2 D2M8K2.u5065 = [0, 257732979108, 2437997532075, 6216285372071, 4633765697981, 698565658775, 19065934916, 0] := by
  rw [show D2M8K2.u5065 = KTree.node D2M8K2.u5057 (nat_lit 11106254) (nat_lit 3600097380) (nat_lit 0) D2M8K2.u5064 from rfl, totK_node, atot5057, atot5064]
  decide +kernel

theorem arows5080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5080 = true := by
  rw [show D2M8K2.u5080 = KTree.node D2M8K2.u5072 (nat_lit 11121989) (nat_lit 2348298599) (nat_lit 0) D2M8K2.u5079 from rfl, allE_node, arows5072, irow5080, arows5079]
  all_goals rfl

theorem atot5080 : totK PD2M8K2 D2M8K2.u5080 = [0, 1575440801162, 5663712961833, 5670975257003, 1410454439677, 65228958717, 0, 0] := by
  rw [show D2M8K2.u5080 = KTree.node D2M8K2.u5072 (nat_lit 11121989) (nat_lit 2348298599) (nat_lit 0) D2M8K2.u5079 from rfl, totK_node, atot5072, atot5079]
  decide +kernel

theorem arows5096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5096 = true := by
  rw [show D2M8K2.u5096 = KTree.node D2M8K2.u5088 (nat_lit 11139723) (nat_lit 3736031856) (nat_lit 0) D2M8K2.u5095 from rfl, allE_node, arows5088, irow5096, arows5095]
  all_goals rfl

theorem atot5096 : totK PD2M8K2 D2M8K2.u5096 = [0, 269119064056, 3310220863299, 7079454102725, 3390386097576, 259346015708, 1138244013, 0] := by
  rw [show D2M8K2.u5096 = KTree.node D2M8K2.u5088 (nat_lit 11139723) (nat_lit 3736031856) (nat_lit 0) D2M8K2.u5095 from rfl, totK_node, atot5088, atot5095]
  decide +kernel

theorem arows5111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5111 = true := by
  rw [show D2M8K2.u5111 = KTree.node D2M8K2.u5103 (nat_lit 11206720) (nat_lit 3775464034) (nat_lit 0) D2M8K2.u5110 from rfl, allE_node, arows5103, irow5111, arows5110]
  all_goals rfl

theorem atot5111 : totK PD2M8K2 D2M8K2.u5111 = [0, 0, 1733337577865, 6342055839433, 5533655001686, 707531983016, 9805162931, 0] := by
  rw [show D2M8K2.u5111 = KTree.node D2M8K2.u5103 (nat_lit 11206720) (nat_lit 3775464034) (nat_lit 0) D2M8K2.u5110 from rfl, totK_node, atot5103, atot5110]
  decide +kernel

theorem arows5132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5132 = true := by
  rw [show D2M8K2.u5132 = KTree.node D2M8K2.u5124 (nat_lit 11248864) (nat_lit 2331873750) (nat_lit 0) D2M8K2.u5131 from rfl, allE_node, arows5124, irow5132, arows5131]
  all_goals rfl

theorem atot5132 : totK PD2M8K2 D2M8K2.u5132 = [0, 0, 1600809343301, 5862417890617, 5716873626783, 1331900123052, 55795070353, 0] := by
  rw [show D2M8K2.u5132 = KTree.node D2M8K2.u5124 (nat_lit 11248864) (nat_lit 2331873750) (nat_lit 0) D2M8K2.u5131 from rfl, totK_node, atot5124, atot5131]
  decide +kernel

theorem arows5147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5147 = true := by
  rw [show D2M8K2.u5147 = KTree.node D2M8K2.u5139 (nat_lit 11284803) (nat_lit 3663281937) (nat_lit 0) D2M8K2.u5146 from rfl, allE_node, arows5139, irow5147, arows5146]
  all_goals rfl

theorem atot5147 : totK PD2M8K2 D2M8K2.u5147 = [0, 0, 1751310855095, 5990623819331, 5564380180903, 1188186135194, 41689458424, 0] := by
  rw [show D2M8K2.u5147 = KTree.node D2M8K2.u5139 (nat_lit 11284803) (nat_lit 3663281937) (nat_lit 0) D2M8K2.u5146 from rfl, totK_node, atot5139, atot5146]
  decide +kernel

theorem arows5163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5163 = true := by
  rw [show D2M8K2.u5163 = KTree.node D2M8K2.u5155 (nat_lit 11323456) (nat_lit 2514174589) (nat_lit 0) D2M8K2.u5162 from rfl, allE_node, arows5155, irow5163, arows5162]
  all_goals rfl

theorem atot5163 : totK PD2M8K2 D2M8K2.u5163 = [0, 0, 1814812031445, 6256291430067, 5486879809916, 961267435551, 22748491686, 0] := by
  rw [show D2M8K2.u5163 = KTree.node D2M8K2.u5155 (nat_lit 11323456) (nat_lit 2514174589) (nat_lit 0) D2M8K2.u5162 from rfl, totK_node, atot5155, atot5162]
  decide +kernel

theorem arows5178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5178 = true := by
  rw [show D2M8K2.u5178 = KTree.node D2M8K2.u5170 (nat_lit 11341728) (nat_lit 3686859352) (nat_lit 0) D2M8K2.u5177 from rfl, allE_node, arows5170, irow5178, arows5177]
  all_goals rfl

theorem atot5178 : totK PD2M8K2 D2M8K2.u5178 = [0, 0, 1570692245205, 5845805910011, 5731117518529, 1199946566028, 43177996296, 0] := by
  rw [show D2M8K2.u5178 = KTree.node D2M8K2.u5170 (nat_lit 11341728) (nat_lit 3686859352) (nat_lit 0) D2M8K2.u5177 from rfl, totK_node, atot5170, atot5177]
  decide +kernel

theorem arows5195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5195 = true := by
  rw [show D2M8K2.u5195 = KTree.node D2M8K2.u5187 (nat_lit 11376466) (nat_lit 3539172207) (nat_lit 0) D2M8K2.u5194 from rfl, allE_node, arows5187, irow5195, arows5194]
  all_goals rfl

theorem atot5195 : totK PD2M8K2 D2M8K2.u5195 = [0, 0, 1277026380148, 5313758688188, 6097977347252, 1559228820591, 62312501687, 0] := by
  rw [show D2M8K2.u5195 = KTree.node D2M8K2.u5187 (nat_lit 11376466) (nat_lit 3539172207) (nat_lit 0) D2M8K2.u5194 from rfl, totK_node, atot5187, atot5194]
  decide +kernel

theorem arows5210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5210 = true := by
  rw [show D2M8K2.u5210 = KTree.node D2M8K2.u5202 (nat_lit 11400522) (nat_lit 3593985643) (nat_lit 0) D2M8K2.u5209 from rfl, allE_node, arows5202, irow5210, arows5209]
  all_goals rfl

theorem atot5210 : totK PD2M8K2 D2M8K2.u5210 = [0, 823190571224, 2899267794075, 3963374386975, 4255547257065, 2132135135938, 224015957599, 1493059870] := by
  rw [show D2M8K2.u5210 = KTree.node D2M8K2.u5202 (nat_lit 11400522) (nat_lit 3593985643) (nat_lit 0) D2M8K2.u5209 from rfl, totK_node, atot5202, atot5209]
  decide +kernel

theorem arows5226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5226 = true := by
  rw [show D2M8K2.u5226 = KTree.node D2M8K2.u5218 (nat_lit 11466811) (nat_lit 2065085402) (nat_lit 0) D2M8K2.u5225 from rfl, allE_node, arows5218, irow5226, arows5225]
  all_goals rfl

theorem atot5226 : totK PD2M8K2 D2M8K2.u5226 = [0, 828007217789, 4188360898465, 6422694371311, 2679254544016, 201089798254, 1369150432, 0] := by
  rw [show D2M8K2.u5226 = KTree.node D2M8K2.u5218 (nat_lit 11466811) (nat_lit 2065085402) (nat_lit 0) D2M8K2.u5225 from rfl, totK_node, atot5218, atot5225]
  decide +kernel

theorem arows5241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5241 = true := by
  rw [show D2M8K2.u5241 = KTree.node D2M8K2.u5233 (nat_lit 11495141) (nat_lit 2379592452) (nat_lit 0) D2M8K2.u5240 from rfl, allE_node, arows5233, irow5241, arows5240]
  all_goals rfl

theorem atot5241 : totK PD2M8K2 D2M8K2.u5241 = [0, 1379284446059, 5222279654312, 5986684765248, 1902929132801, 98327707665, 0, 0] := by
  rw [show D2M8K2.u5241 = KTree.node D2M8K2.u5233 (nat_lit 11495141) (nat_lit 2379592452) (nat_lit 0) D2M8K2.u5240 from rfl, totK_node, atot5233, atot5240]
  decide +kernel

theorem arows5259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5259 = true := by
  rw [show D2M8K2.u5259 = KTree.node D2M8K2.u5251 (nat_lit 11512781) (nat_lit 1998270282) (nat_lit 0) D2M8K2.u5258 from rfl, allE_node, arows5251, irow5259, arows5258]
  all_goals rfl

theorem atot5259 : totK PD2M8K2 D2M8K2.u5259 = [0, 671280571781, 3467138421967, 5798827708471, 3741522673479, 840236317277, 42081742489, 0] := by
  rw [show D2M8K2.u5259 = KTree.node D2M8K2.u5251 (nat_lit 11512781) (nat_lit 1998270282) (nat_lit 0) D2M8K2.u5258 from rfl, totK_node, atot5251, atot5258]
  decide +kernel

theorem arows5274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5274 = true := by
  rw [show D2M8K2.u5274 = KTree.node D2M8K2.u5266 (nat_lit 11526720) (nat_lit 2590544078) (nat_lit 0) D2M8K2.u5273 from rfl, allE_node, arows5266, irow5274, arows5273]
  all_goals rfl

theorem atot5274 : totK PD2M8K2 D2M8K2.u5274 = [0, 795345281950, 3403948708573, 5636789773167, 3984201599574, 726500818460, 15936385454, 0] := by
  rw [show D2M8K2.u5274 = KTree.node D2M8K2.u5266 (nat_lit 11526720) (nat_lit 2590544078) (nat_lit 0) D2M8K2.u5273 from rfl, totK_node, atot5266, atot5273]
  decide +kernel

theorem arows5290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5290 = true := by
  rw [show D2M8K2.u5290 = KTree.node D2M8K2.u5282 (nat_lit 11543794) (nat_lit 3704410632) (nat_lit 0) D2M8K2.u5289 from rfl, allE_node, arows5282, irow5290, arows5289]
  all_goals rfl

theorem atot5290 : totK PD2M8K2 D2M8K2.u5290 = [0, 1191711924137, 5142368556370, 6187849749097, 1854153100461, 91357530760, 0, 0] := by
  rw [show D2M8K2.u5290 = KTree.node D2M8K2.u5282 (nat_lit 11543794) (nat_lit 3704410632) (nat_lit 0) D2M8K2.u5289 from rfl, totK_node, atot5282, atot5289]
  decide +kernel

theorem arows5305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5305 = true := by
  rw [show D2M8K2.u5305 = KTree.node D2M8K2.u5297 (nat_lit 11563909) (nat_lit 1348569712) (nat_lit 0) D2M8K2.u5304 from rfl, allE_node, arows5297, irow5305, arows5304]
  all_goals rfl

theorem atot5305 : totK PD2M8K2 D2M8K2.u5305 = [0, 378914462040, 2848553649001, 6269841415219, 4240890093743, 594631308531, 12004276665, 0] := by
  rw [show D2M8K2.u5305 = KTree.node D2M8K2.u5297 (nat_lit 11563909) (nat_lit 1348569712) (nat_lit 0) D2M8K2.u5304 from rfl, totK_node, atot5297, atot5304]
  decide +kernel

theorem arows5322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5322 = true := by
  rw [show D2M8K2.u5322 = KTree.node D2M8K2.u5314 (nat_lit 11583198) (nat_lit 3902705292) (nat_lit 0) D2M8K2.u5321 from rfl, allE_node, arows5314, irow5322, arows5321]
  all_goals rfl

theorem atot5322 : totK PD2M8K2 D2M8K2.u5322 = [0, 1612882181098, 5756540822666, 5713613376020, 1428635208414, 60724014930, 0, 0] := by
  rw [show D2M8K2.u5322 = KTree.node D2M8K2.u5314 (nat_lit 11583198) (nat_lit 3902705292) (nat_lit 0) D2M8K2.u5321 from rfl, totK_node, atot5314, atot5321]
  decide +kernel

theorem arows5337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5337 = true := by
  rw [show D2M8K2.u5337 = KTree.node D2M8K2.u5329 (nat_lit 11603184) (nat_lit 3349984854) (nat_lit 0) D2M8K2.u5336 from rfl, allE_node, arows5329, irow5337, arows5336]
  all_goals rfl

theorem atot5337 : totK PD2M8K2 D2M8K2.u5337 = [0, 121950136720, 2345963176188, 6544401302681, 4709061786395, 641928119846, 12143333308, 0] := by
  rw [show D2M8K2.u5337 = KTree.node D2M8K2.u5329 (nat_lit 11603184) (nat_lit 3349984854) (nat_lit 0) D2M8K2.u5336 from rfl, totK_node, atot5329, atot5336]
  decide +kernel

theorem arows5353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5353 = true := by
  rw [show D2M8K2.u5353 = KTree.node D2M8K2.u5345 (nat_lit 11660706) (nat_lit 2747552504) (nat_lit 0) D2M8K2.u5352 from rfl, allE_node, arows5345, irow5353, arows5352]
  all_goals rfl

theorem atot5353 : totK PD2M8K2 D2M8K2.u5353 = [0, 1561483868831, 5680496112635, 5732171165257, 1412218499464, 62294247539, 0, 0] := by
  rw [show D2M8K2.u5353 = KTree.node D2M8K2.u5345 (nat_lit 11660706) (nat_lit 2747552504) (nat_lit 0) D2M8K2.u5352 from rfl, totK_node, atot5345, atot5352]
  decide +kernel

theorem arows5368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5368 = true := by
  rw [show D2M8K2.u5368 = KTree.node D2M8K2.u5360 (nat_lit 11677678) (nat_lit 4028020860) (nat_lit 0) D2M8K2.u5367 from rfl, allE_node, arows5360, irow5368, arows5367]
  all_goals rfl

theorem atot5368 : totK PD2M8K2 D2M8K2.u5368 = [0, 429080094848, 3139697362463, 6460043629589, 3903165446317, 441605310945, 6190125969, 0] := by
  rw [show D2M8K2.u5368 = KTree.node D2M8K2.u5360 (nat_lit 11677678) (nat_lit 4028020860) (nat_lit 0) D2M8K2.u5367 from rfl, totK_node, atot5360, atot5367]
  decide +kernel

theorem arows5387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5387 = true := by
  rw [show D2M8K2.u5387 = KTree.node D2M8K2.u5379 (nat_lit 11696352) (nat_lit 3577290238) (nat_lit 0) D2M8K2.u5386 from rfl, allE_node, arows5379, irow5387, arows5386]
  all_goals rfl

theorem atot5387 : totK PD2M8K2 D2M8K2.u5387 = [0, 0, 2143523762210, 6484240583568, 4878578307295, 816716300104, 28051723144, 0] := by
  rw [show D2M8K2.u5387 = KTree.node D2M8K2.u5379 (nat_lit 11696352) (nat_lit 3577290238) (nat_lit 0) D2M8K2.u5386 from rfl, totK_node, atot5379, atot5386]
  decide +kernel

theorem arows5402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5402 = true := by
  rw [show D2M8K2.u5402 = KTree.node D2M8K2.u5394 (nat_lit 11745799) (nat_lit 665061746) (nat_lit 2) D2M8K2.u5401 from rfl, allE_node, arows5394, irow5402, arows5401]
  all_goals rfl

theorem atot5402 : totK PD2M8K2 D2M8K2.u5402 = [0, 0, 1638608123021, 5880386726997, 5699978610509, 1337077828734, 50740826632, 0] := by
  rw [show D2M8K2.u5402 = KTree.node D2M8K2.u5394 (nat_lit 11745799) (nat_lit 665061746) (nat_lit 2) D2M8K2.u5401 from rfl, totK_node, atot5394, atot5401]
  decide +kernel

theorem arows5418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5418 = true := by
  rw [show D2M8K2.u5418 = KTree.node D2M8K2.u5410 (nat_lit 11782113) (nat_lit 1816062054) (nat_lit 0) D2M8K2.u5417 from rfl, allE_node, arows5410, irow5418, arows5417]
  all_goals rfl

theorem atot5418 : totK PD2M8K2 D2M8K2.u5418 = [0, 0, 1658333523483, 5692625847436, 5594358732567, 1450585023023, 61299256340, 0] := by
  rw [show D2M8K2.u5418 = KTree.node D2M8K2.u5410 (nat_lit 11782113) (nat_lit 1816062054) (nat_lit 0) D2M8K2.u5417 from rfl, totK_node, atot5410, atot5417]
  decide +kernel

theorem arows5433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5433 = true := by
  rw [show D2M8K2.u5433 = KTree.node D2M8K2.u5425 (nat_lit 11799635) (nat_lit 2588572441) (nat_lit 128) D2M8K2.u5432 from rfl, allE_node, arows5425, irow5433, arows5432]
  all_goals rfl

theorem atot5433 : totK PD2M8K2 D2M8K2.u5433 = [0, 0, 748124445496, 4313253052813, 6610233465633, 2509671737490, 184684965383, 1501162176] := by
  rw [show D2M8K2.u5433 = KTree.node D2M8K2.u5425 (nat_lit 11799635) (nat_lit 2588572441) (nat_lit 128) D2M8K2.u5432 from rfl, totK_node, atot5425, atot5432]
  decide +kernel

theorem arows5450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5450 = true := by
  rw [show D2M8K2.u5450 = KTree.node D2M8K2.u5442 (nat_lit 11825842) (nat_lit 4038837434) (nat_lit 0) D2M8K2.u5449 from rfl, allE_node, arows5442, irow5450, arows5449]
  all_goals rfl

theorem atot5450 : totK PD2M8K2 D2M8K2.u5450 = [0, 0, 1636843322157, 5671888460408, 5650580003092, 1482521330167, 66951847472, 0] := by
  rw [show D2M8K2.u5450 = KTree.node D2M8K2.u5442 (nat_lit 11825842) (nat_lit 4038837434) (nat_lit 0) D2M8K2.u5449 from rfl, totK_node, atot5442, atot5449]
  decide +kernel

theorem arows5465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5465 = true := by
  rw [show D2M8K2.u5465 = KTree.node D2M8K2.u5457 (nat_lit 11851029) (nat_lit 1685304700) (nat_lit 0) D2M8K2.u5464 from rfl, allE_node, arows5457, irow5465, arows5464]
  all_goals rfl

theorem atot5465 : totK PD2M8K2 D2M8K2.u5465 = [0, 0, 736328767137, 4211986758978, 6503357455060, 2703156347312, 205067973630, 1510868091] := by
  rw [show D2M8K2.u5465 = KTree.node D2M8K2.u5457 (nat_lit 11851029) (nat_lit 1685304700) (nat_lit 0) D2M8K2.u5464 from rfl, totK_node, atot5457, atot5464]
  decide +kernel

theorem arows5481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5481 = true := by
  rw [show D2M8K2.u5481 = KTree.node D2M8K2.u5473 (nat_lit 11910902) (nat_lit 3839867497) (nat_lit 0) D2M8K2.u5480 from rfl, allE_node, arows5473, irow5481, arows5480]
  all_goals rfl

theorem atot5481 : totK PD2M8K2 D2M8K2.u5481 = [0, 0, 1643075604358, 5810173726419, 5660031860862, 1295457165459, 44801438457, 0] := by
  rw [show D2M8K2.u5481 = KTree.node D2M8K2.u5473 (nat_lit 11910902) (nat_lit 3839867497) (nat_lit 0) D2M8K2.u5480 from rfl, totK_node, atot5473, atot5480]
  decide +kernel

theorem arows5496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5496 = true := by
  rw [show D2M8K2.u5496 = KTree.node D2M8K2.u5488 (nat_lit 11931408) (nat_lit 3633748302) (nat_lit 0) D2M8K2.u5495 from rfl, allE_node, arows5488, irow5496, arows5495]
  all_goals rfl

theorem atot5496 : totK PD2M8K2 D2M8K2.u5496 = [0, 0, 56835226932, 2718691716919, 7136722970448, 3973937983336, 376917499220, 2822133622] := by
  rw [show D2M8K2.u5496 = KTree.node D2M8K2.u5488 (nat_lit 11931408) (nat_lit 3633748302) (nat_lit 0) D2M8K2.u5495 from rfl, totK_node, atot5488, atot5495]
  decide +kernel

theorem arows5514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5514 = true := by
  rw [show D2M8K2.u5514 = KTree.node D2M8K2.u5506 (nat_lit 11952978) (nat_lit 2594351957) (nat_lit 0) D2M8K2.u5513 from rfl, allE_node, arows5506, irow5514, arows5513]
  all_goals rfl

theorem atot5514 : totK PD2M8K2 D2M8K2.u5514 = [1677758805620, 5635396619706, 4931604527265, 936023002434, 276607535354, 617659404114, 235492752849, 10297110227] := by
  rw [show D2M8K2.u5514 = KTree.node D2M8K2.u5506 (nat_lit 11952978) (nat_lit 2594351957) (nat_lit 0) D2M8K2.u5513 from rfl, totK_node, atot5506, atot5513]
  decide +kernel

theorem arows5529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5529 = true := by
  rw [show D2M8K2.u5529 = KTree.node D2M8K2.u5521 (nat_lit 11966422) (nat_lit 3483849128) (nat_lit 0) D2M8K2.u5528 from rfl, allE_node, arows5521, irow5529, arows5528]
  all_goals rfl

theorem atot5529 : totK PD2M8K2 D2M8K2.u5529 = [419234341778, 3473020677011, 6813288317898, 3215869225255, 265382812261, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5529 = KTree.node D2M8K2.u5521 (nat_lit 11966422) (nat_lit 3483849128) (nat_lit 0) D2M8K2.u5528 from rfl, totK_node, atot5521, atot5528]
  decide +kernel

theorem arows5545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5545 = true := by
  rw [show D2M8K2.u5545 = KTree.node D2M8K2.u5537 (nat_lit 12032391) (nat_lit 3639394546) (nat_lit 0) D2M8K2.u5544 from rfl, allE_node, arows5537, irow5545, arows5544]
  all_goals rfl

theorem atot5545 : totK PD2M8K2 D2M8K2.u5545 = [1564648449603, 5578526980801, 5706154490518, 1583651394095, 77469930052, 0, 0, 0] := by
  rw [show D2M8K2.u5545 = KTree.node D2M8K2.u5537 (nat_lit 12032391) (nat_lit 3639394546) (nat_lit 0) D2M8K2.u5544 from rfl, totK_node, atot5537, atot5544]
  decide +kernel

theorem arows5560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5560 = true := by
  rw [show D2M8K2.u5560 = KTree.node D2M8K2.u5552 (nat_lit 12049014) (nat_lit 3587483302) (nat_lit 0) D2M8K2.u5559 from rfl, allE_node, arows5552, irow5560, arows5559]
  all_goals rfl

theorem atot5560 : totK PD2M8K2 D2M8K2.u5560 = [469810943695, 3310704804627, 6390346287378, 3628583108103, 498833748719, 14222663156, 0, 0] := by
  rw [show D2M8K2.u5560 = KTree.node D2M8K2.u5552 (nat_lit 12049014) (nat_lit 3587483302) (nat_lit 0) D2M8K2.u5559 from rfl, totK_node, atot5552, atot5559]
  decide +kernel

theorem arows5577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5577 = true := by
  rw [show D2M8K2.u5577 = KTree.node D2M8K2.u5569 (nat_lit 12069993) (nat_lit 1232835762) (nat_lit 0) D2M8K2.u5576 from rfl, allE_node, arows5569, irow5577, arows5576]
  all_goals rfl

theorem atot5577 : totK PD2M8K2 D2M8K2.u5577 = [1244827890181, 4820496202763, 5717943077987, 2288241386555, 234437290401, 4574395652, 0, 0] := by
  rw [show D2M8K2.u5577 = KTree.node D2M8K2.u5569 (nat_lit 12069993) (nat_lit 1232835762) (nat_lit 0) D2M8K2.u5576 from rfl, totK_node, atot5569, atot5576]
  decide +kernel

theorem arows5592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5592 = true := by
  rw [show D2M8K2.u5592 = KTree.node D2M8K2.u5584 (nat_lit 12090826) (nat_lit 3865669943) (nat_lit 0) D2M8K2.u5591 from rfl, allE_node, arows5584, irow5592, arows5591]
  all_goals rfl

theorem atot5592 : totK PD2M8K2 D2M8K2.u5592 = [403614254217, 3054071001115, 6346797067429, 3839436199860, 543339181400, 15398727635, 0, 0] := by
  rw [show D2M8K2.u5592 = KTree.node D2M8K2.u5584 (nat_lit 12090826) (nat_lit 3865669943) (nat_lit 0) D2M8K2.u5591 from rfl, totK_node, atot5584, atot5591]
  decide +kernel

theorem arows5608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5608 = true := by
  rw [show D2M8K2.u5608 = KTree.node D2M8K2.u5600 (nat_lit 12114144) (nat_lit 3548378307) (nat_lit 0) D2M8K2.u5607 from rfl, allE_node, arows5600, irow5608, arows5607]
  all_goals rfl

theorem atot5608 : totK PD2M8K2 D2M8K2.u5608 = [1402070926798, 5123451303040, 5636227857208, 2038294385797, 196849251593, 3667207281, 0, 0] := by
  rw [show D2M8K2.u5608 = KTree.node D2M8K2.u5600 (nat_lit 12114144) (nat_lit 3548378307) (nat_lit 0) D2M8K2.u5607 from rfl, totK_node, atot5600, atot5607]
  decide +kernel

theorem arows5623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5623 = true := by
  rw [show D2M8K2.u5623 = KTree.node D2M8K2.u5615 (nat_lit 12131725) (nat_lit 1385917071) (nat_lit 0) D2M8K2.u5622 from rfl, allE_node, arows5615, irow5623, arows5622]
  all_goals rfl

theorem atot5623 : totK PD2M8K2 D2M8K2.u5623 = [575779815503, 3828606983997, 6705604594252, 2936732533860, 220436865229, 1138244013, 0, 0] := by
  rw [show D2M8K2.u5623 = KTree.node D2M8K2.u5615 (nat_lit 12131725) (nat_lit 1385917071) (nat_lit 0) D2M8K2.u5622 from rfl, totK_node, atot5615, atot5622]
  decide +kernel

theorem arows5643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5643 = true := by
  rw [show D2M8K2.u5643 = KTree.node D2M8K2.u5635 (nat_lit 12155166) (nat_lit 3885041401) (nat_lit 0) D2M8K2.u5642 from rfl, allE_node, arows5635, irow5643, arows5642]
  all_goals rfl

theorem atot5643 : totK PD2M8K2 D2M8K2.u5643 = [1270720670091, 4810700141624, 5706618605547, 2323477472560, 276649411061, 4977114383, 0, 0] := by
  rw [show D2M8K2.u5643 = KTree.node D2M8K2.u5635 (nat_lit 12155166) (nat_lit 3885041401) (nat_lit 0) D2M8K2.u5642 from rfl, totK_node, atot5635, atot5642]
  decide +kernel

theorem arows5658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5658 = true := by
  rw [show D2M8K2.u5658 = KTree.node D2M8K2.u5650 (nat_lit 12172093) (nat_lit 1231020925) (nat_lit 0) D2M8K2.u5657 from rfl, allE_node, arows5650, irow5658, arows5657]
  all_goals rfl

theorem atot5658 : totK PD2M8K2 D2M8K2.u5658 = [718275913541, 3862426227069, 6361323317909, 3170397679509, 286342231436, 2385942608, 0, 0] := by
  rw [show D2M8K2.u5658 = KTree.node D2M8K2.u5650 (nat_lit 12172093) (nat_lit 1231020925) (nat_lit 0) D2M8K2.u5657 from rfl, totK_node, atot5650, atot5657]
  decide +kernel

theorem arows5674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5674 = true := by
  rw [show D2M8K2.u5674 = KTree.node D2M8K2.u5666 (nat_lit 12191686) (nat_lit 3792466461) (nat_lit 0) D2M8K2.u5673 from rfl, allE_node, arows5666, irow5674, arows5673]
  all_goals rfl

theorem atot5674 : totK PD2M8K2 D2M8K2.u5674 = [0, 1678564025503, 6005167785430, 5542050971513, 1057590368189, 33020226125, 0, 0] := by
  rw [show D2M8K2.u5674 = KTree.node D2M8K2.u5666 (nat_lit 12191686) (nat_lit 3792466461) (nat_lit 0) D2M8K2.u5673 from rfl, totK_node, atot5666, atot5673]
  decide +kernel

theorem arows5689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5689 = true := by
  rw [show D2M8K2.u5689 = KTree.node D2M8K2.u5681 (nat_lit 12208724) (nat_lit 3681043666) (nat_lit 0) D2M8K2.u5688 from rfl, allE_node, arows5681, irow5689, arows5688]
  all_goals rfl

theorem atot5689 : totK PD2M8K2 D2M8K2.u5689 = [0, 1227546631610, 5038897691596, 5953383783581, 1738639721336, 133512840001, 1369150432, 0] := by
  rw [show D2M8K2.u5689 = KTree.node D2M8K2.u5681 (nat_lit 12208724) (nat_lit 3681043666) (nat_lit 0) D2M8K2.u5688 from rfl, totK_node, atot5681, atot5688]
  decide +kernel

theorem arows5706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5706 = true := by
  rw [show D2M8K2.u5706 = KTree.node D2M8K2.u5698 (nat_lit 12231504) (nat_lit 3669348837) (nat_lit 0) D2M8K2.u5705 from rfl, allE_node, arows5698, irow5706, arows5705]
  all_goals rfl

theorem atot5706 : totK PD2M8K2 D2M8K2.u5706 = [0, 766109221512, 4292761126136, 6562437563316, 2393924403040, 177789902111, 0, 0] := by
  rw [show D2M8K2.u5706 = KTree.node D2M8K2.u5698 (nat_lit 12231504) (nat_lit 3669348837) (nat_lit 0) D2M8K2.u5705 from rfl, totK_node, atot5698, atot5705]
  decide +kernel

theorem arows5721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5721 = true := by
  rw [show D2M8K2.u5721 = KTree.node D2M8K2.u5713 (nat_lit 12292512) (nat_lit 3528398759) (nat_lit 0) D2M8K2.u5720 from rfl, allE_node, arows5713, irow5721, arows5720]
  all_goals rfl

theorem atot5721 : totK PD2M8K2 D2M8K2.u5721 = [0, 1682389258941, 5998148741221, 5609366982424, 1071765451241, 33020449330, 0, 0] := by
  rw [show D2M8K2.u5721 = KTree.node D2M8K2.u5713 (nat_lit 12292512) (nat_lit 3528398759) (nat_lit 0) D2M8K2.u5720 from rfl, totK_node, atot5713, atot5720]
  decide +kernel

theorem arows5737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5737 = true := by
  rw [show D2M8K2.u5737 = KTree.node D2M8K2.u5729 (nat_lit 12334482) (nat_lit 3395057874) (nat_lit 0) D2M8K2.u5736 from rfl, allE_node, arows5729, irow5737, arows5736]
  all_goals rfl

theorem atot5737 : totK PD2M8K2 D2M8K2.u5737 = [0, 1730745851501, 5995045074150, 5504020892885, 1075649721420, 33172177045, 0, 0] := by
  rw [show D2M8K2.u5737 = KTree.node D2M8K2.u5729 (nat_lit 12334482) (nat_lit 3395057874) (nat_lit 0) D2M8K2.u5736 from rfl, totK_node, atot5729, atot5736]
  decide +kernel

theorem arows5752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5752 = true := by
  rw [show D2M8K2.u5752 = KTree.node D2M8K2.u5744 (nat_lit 12370131) (nat_lit 2578489642) (nat_lit 0) D2M8K2.u5751 from rfl, allE_node, arows5744, irow5752, arows5751]
  all_goals rfl

theorem atot5752 : totK PD2M8K2 D2M8K2.u5752 = [0, 1745536369554, 6042696248824, 5495225493806, 1036941316657, 32557842968, 0, 0] := by
  rw [show D2M8K2.u5752 = KTree.node D2M8K2.u5744 (nat_lit 12370131) (nat_lit 2578489642) (nat_lit 0) D2M8K2.u5751 from rfl, totK_node, atot5744, atot5751]
  decide +kernel

theorem arows5770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5770 = true := by
  rw [show D2M8K2.u5770 = KTree.node D2M8K2.u5762 (nat_lit 12408818) (nat_lit 3169187984) (nat_lit 0) D2M8K2.u5769 from rfl, allE_node, arows5762, irow5770, arows5769]
  all_goals rfl

theorem atot5770 : totK PD2M8K2 D2M8K2.u5770 = [0, 1707812174480, 6024231131093, 5675984345126, 1077098913303, 22526258662, 0, 0] := by
  rw [show D2M8K2.u5770 = KTree.node D2M8K2.u5762 (nat_lit 12408818) (nat_lit 3169187984) (nat_lit 0) D2M8K2.u5769 from rfl, totK_node, atot5762, atot5769]
  decide +kernel

theorem arows5785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5785 = true := by
  rw [show D2M8K2.u5785 = KTree.node D2M8K2.u5777 (nat_lit 12491162) (nat_lit 4210137328) (nat_lit 0) D2M8K2.u5784 from rfl, allE_node, arows5777, irow5785, arows5784]
  all_goals rfl

theorem atot5785 : totK PD2M8K2 D2M8K2.u5785 = [1518795441172, 5152170650552, 5327382865688, 2098201234296, 390350146336, 20647649770, 0, 0] := by
  rw [show D2M8K2.u5785 = KTree.node D2M8K2.u5777 (nat_lit 12491162) (nat_lit 4210137328) (nat_lit 0) D2M8K2.u5784 from rfl, totK_node, atot5777, atot5784]
  decide +kernel

theorem arows5801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5801 = true := by
  rw [show D2M8K2.u5801 = KTree.node D2M8K2.u5793 (nat_lit 12508098) (nat_lit 1394728616) (nat_lit 0) D2M8K2.u5800 from rfl, allE_node, arows5793, irow5801, arows5800]
  all_goals rfl

theorem atot5801 : totK PD2M8K2 D2M8K2.u5801 = [598912855043, 3333821731419, 5843818020283, 3790902139070, 849760049476, 42081742489, 0, 0] := by
  rw [show D2M8K2.u5801 = KTree.node D2M8K2.u5793 (nat_lit 12508098) (nat_lit 1394728616) (nat_lit 0) D2M8K2.u5800 from rfl, totK_node, atot5793, atot5800]
  decide +kernel

theorem arows5816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5816 = true := by
  rw [show D2M8K2.u5816 = KTree.node D2M8K2.u5808 (nat_lit 12521634) (nat_lit 3150305727) (nat_lit 0) D2M8K2.u5815 from rfl, allE_node, arows5808, irow5816, arows5815]
  all_goals rfl

theorem atot5816 : totK PD2M8K2 D2M8K2.u5816 = [683873556944, 3180260174529, 5686588267421, 4131782322494, 750159029011, 15936385454, 0, 0] := by
  rw [show D2M8K2.u5816 = KTree.node D2M8K2.u5808 (nat_lit 12521634) (nat_lit 3150305727) (nat_lit 0) D2M8K2.u5815 from rfl, totK_node, atot5808, atot5815]
  decide +kernel

theorem arows5833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5833 = true := by
  rw [show D2M8K2.u5833 = KTree.node D2M8K2.u5825 (nat_lit 12538840) (nat_lit 3667199931) (nat_lit 0) D2M8K2.u5832 from rfl, allE_node, arows5825, irow5833, arows5832]
  all_goals rfl

theorem atot5833 : totK PD2M8K2 D2M8K2.u5833 = [1358473379673, 5368993723652, 5989202476416, 1687903260786, 78875564335, 0, 0, 0] := by
  rw [show D2M8K2.u5833 = KTree.node D2M8K2.u5825 (nat_lit 12538840) (nat_lit 3667199931) (nat_lit 0) D2M8K2.u5832 from rfl, totK_node, atot5825, atot5832]
  decide +kernel

theorem arows5848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5848 = true := by
  rw [show D2M8K2.u5848 = KTree.node D2M8K2.u5840 (nat_lit 12554618) (nat_lit 3952272856) (nat_lit 0) D2M8K2.u5847 from rfl, allE_node, arows5840, irow5848, arows5847]
  all_goals rfl

theorem atot5848 : totK PD2M8K2 D2M8K2.u5848 = [229587690250, 2436091559129, 6367891813495, 4594987416398, 690451348303, 18797058808, 0, 0] := by
  rw [show D2M8K2.u5848 = KTree.node D2M8K2.u5840 (nat_lit 12554618) (nat_lit 3952272856) (nat_lit 0) D2M8K2.u5847 from rfl, totK_node, atot5840, atot5847]
  decide +kernel

theorem arows5864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5864 = true := by
  rw [show D2M8K2.u5864 = KTree.node D2M8K2.u5856 (nat_lit 12579988) (nat_lit 3319630704) (nat_lit 0) D2M8K2.u5863 from rfl, allE_node, arows5856, irow5864, arows5863]
  all_goals rfl

theorem atot5864 : totK PD2M8K2 D2M8K2.u5864 = [1432753651953, 5479295408824, 5869182588605, 1627762149651, 77833014165, 0, 0, 0] := by
  rw [show D2M8K2.u5864 = KTree.node D2M8K2.u5856 (nat_lit 12579988) (nat_lit 3319630704) (nat_lit 0) D2M8K2.u5863 from rfl, totK_node, atot5856, atot5863]
  decide +kernel

theorem arows5879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5879 = true := by
  rw [show D2M8K2.u5879 = KTree.node D2M8K2.u5871 (nat_lit 12601763) (nat_lit 2110080437) (nat_lit 0) D2M8K2.u5878 from rfl, allE_node, arows5871, irow5879, arows5878]
  all_goals rfl

theorem atot5879 : totK PD2M8K2 D2M8K2.u5879 = [510813857819, 3191761222803, 6175955183653, 3869036141774, 589098835383, 17826068843, 0, 0] := by
  rw [show D2M8K2.u5879 = KTree.node D2M8K2.u5871 (nat_lit 12601763) (nat_lit 2110080437) (nat_lit 0) D2M8K2.u5878 from rfl, totK_node, atot5871, atot5878]
  decide +kernel

theorem arows5898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5898 = true := by
  rw [show D2M8K2.u5898 = KTree.node D2M8K2.u5890 (nat_lit 12618012) (nat_lit 3509774347) (nat_lit 0) D2M8K2.u5897 from rfl, allE_node, arows5890, irow5898, arows5897]
  all_goals rfl

theorem atot5898 : totK PD2M8K2 D2M8K2.u5898 = [1473074727243, 5529203804898, 5798581581776, 1554381764980, 70252456129, 0, 0, 0] := by
  rw [show D2M8K2.u5898 = KTree.node D2M8K2.u5890 (nat_lit 12618012) (nat_lit 3509774347) (nat_lit 0) D2M8K2.u5897 from rfl, totK_node, atot5890, atot5897]
  decide +kernel

theorem arows5913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5913 = true := by
  rw [show D2M8K2.u5913 = KTree.node D2M8K2.u5905 (nat_lit 12639556) (nat_lit 2942825675) (nat_lit 0) D2M8K2.u5912 from rfl, allE_node, arows5905, irow5913, arows5912]
  all_goals rfl

theorem atot5913 : totK PD2M8K2 D2M8K2.u5913 = [353677020485, 3098525826676, 6637434270848, 3801285694722, 432749150432, 6115358396, 0, 0] := by
  rw [show D2M8K2.u5913 = KTree.node D2M8K2.u5905 (nat_lit 12639556) (nat_lit 2942825675) (nat_lit 0) D2M8K2.u5912 from rfl, totK_node, atot5905, atot5912]
  decide +kernel

theorem arows5929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5929 = true := by
  rw [show D2M8K2.u5929 = KTree.node D2M8K2.u5921 (nat_lit 12658381) (nat_lit 1189397663) (nat_lit 0) D2M8K2.u5928 from rfl, allE_node, arows5921, irow5929, arows5928]
  all_goals rfl

theorem atot5929 : totK PD2M8K2 D2M8K2.u5929 = [1641561038001, 5744921399683, 5647333976933, 1445324013787, 64960004693, 0, 0, 0] := by
  rw [show D2M8K2.u5929 = KTree.node D2M8K2.u5921 (nat_lit 12658381) (nat_lit 1189397663) (nat_lit 0) D2M8K2.u5928 from rfl, totK_node, atot5921, atot5928]
  decide +kernel

theorem arows5944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5944 = true := by
  rw [show D2M8K2.u5944 = KTree.node D2M8K2.u5936 (nat_lit 12677926) (nat_lit 1190110765) (nat_lit 0) D2M8K2.u5943 from rfl, allE_node, arows5936, irow5944, arows5943]
  all_goals rfl

theorem atot5944 : totK PD2M8K2 D2M8K2.u5944 = [0, 2171336290324, 6684117294324, 4902971454210, 656306932776, 11121530615, 0, 0] := by
  rw [show D2M8K2.u5944 = KTree.node D2M8K2.u5936 (nat_lit 12677926) (nat_lit 1190110765) (nat_lit 0) D2M8K2.u5943 from rfl, totK_node, atot5936, atot5943]
  decide +kernel

theorem arows5961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5961 = true := by
  rw [show D2M8K2.u5961 = KTree.node D2M8K2.u5953 (nat_lit 12739508) (nat_lit 3664909440) (nat_lit 0) D2M8K2.u5960 from rfl, allE_node, arows5953, irow5961, arows5960]
  all_goals rfl

theorem atot5961 : totK PD2M8K2 D2M8K2.u5961 = [0, 1478539050594, 5436638403220, 5814110799388, 1634835310092, 76891303080, 0, 0] := by
  rw [show D2M8K2.u5961 = KTree.node D2M8K2.u5953 (nat_lit 12739508) (nat_lit 3664909440) (nat_lit 0) D2M8K2.u5960 from rfl, totK_node, atot5953, atot5960]
  decide +kernel

theorem arows5976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5976 = true := by
  rw [show D2M8K2.u5976 = KTree.node D2M8K2.u5968 (nat_lit 12756788) (nat_lit 3657104338) (nat_lit 0) D2M8K2.u5975 from rfl, allE_node, arows5968, irow5976, arows5975]
  all_goals rfl

theorem atot5976 : totK PD2M8K2 D2M8K2.u5976 = [0, 639169245621, 3443911227259, 5774239886048, 3661855233472, 814384546566, 41989737272, 0] := by
  rw [show D2M8K2.u5976 = KTree.node D2M8K2.u5968 (nat_lit 12756788) (nat_lit 3657104338) (nat_lit 0) D2M8K2.u5975 from rfl, totK_node, atot5968, atot5975]
  decide +kernel

theorem arows5992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5992 = true := by
  rw [show D2M8K2.u5992 = KTree.node D2M8K2.u5984 (nat_lit 12770478) (nat_lit 3835554828) (nat_lit 0) D2M8K2.u5991 from rfl, allE_node, arows5984, irow5992, arows5991]
  all_goals rfl

theorem atot5992 : totK PD2M8K2 D2M8K2.u5992 = [0, 683873556944, 3254462821202, 5681812747116, 4012528854939, 679993365293, 15657634319, 0] := by
  rw [show D2M8K2.u5992 = KTree.node D2M8K2.u5984 (nat_lit 12770478) (nat_lit 3835554828) (nat_lit 0) D2M8K2.u5991 from rfl, totK_node, atot5984, atot5991]
  decide +kernel

theorem arows6007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6007 = true := by
  rw [show D2M8K2.u6007 = KTree.node D2M8K2.u5999 (nat_lit 12787729) (nat_lit 1164044700) (nat_lit 0) D2M8K2.u6006 from rfl, allE_node, arows5999, irow6007, arows6006]
  all_goals rfl

theorem atot6007 : totK PD2M8K2 D2M8K2.u6007 = [0, 1358473379673, 5349775362875, 5985096787751, 1664347153402, 74688269714, 0, 0] := by
  rw [show D2M8K2.u6007 = KTree.node D2M8K2.u5999 (nat_lit 12787729) (nat_lit 1164044700) (nat_lit 0) D2M8K2.u6006 from rfl, totK_node, atot5999, atot6006]
  decide +kernel

theorem arows6025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6025 = true := by
  rw [show D2M8K2.u6025 = KTree.node D2M8K2.u6017 (nat_lit 12808534) (nat_lit 2947991516) (nat_lit 0) D2M8K2.u6024 from rfl, allE_node, arows6017, irow6025, arows6024]
  all_goals rfl

theorem atot6025 : totK PD2M8K2 D2M8K2.u6025 = [0, 429562897600, 3122058355039, 6468612082517, 3865562879836, 450665784078, 6546549506, 0] := by
  rw [show D2M8K2.u6025 = KTree.node D2M8K2.u6017 (nat_lit 12808534) (nat_lit 2947991516) (nat_lit 0) D2M8K2.u6024 from rfl, totK_node, atot6017, atot6024]
  decide +kernel

theorem arows6040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6040 = true := by
  rw [show D2M8K2.u6040 = KTree.node D2M8K2.u6032 (nat_lit 12830545) (nat_lit 1532351776) (nat_lit 0) D2M8K2.u6039 from rfl, allE_node, arows6032, irow6040, arows6039]
  all_goals rfl

theorem atot6040 : totK PD2M8K2 D2M8K2.u6040 = [0, 1232778444603, 5116154977543, 6101038263691, 1903601647560, 92771897657, 0, 0] := by
  rw [show D2M8K2.u6040 = KTree.node D2M8K2.u6032 (nat_lit 12830545) (nat_lit 1532351776) (nat_lit 0) D2M8K2.u6039 from rfl, totK_node, atot6032, atot6039]
  decide +kernel

theorem arows6056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6056 = true := by
  rw [show D2M8K2.u6056 = KTree.node D2M8K2.u6048 (nat_lit 12853471) (nat_lit 1727009054) (nat_lit 0) D2M8K2.u6055 from rfl, allE_node, arows6048, irow6056, arows6055]
  all_goals rfl

theorem atot6056 : totK PD2M8K2 D2M8K2.u6056 = [0, 752141467331, 3689558883003, 6029641484554, 3415572431252, 418938724471, 6624648996, 0] := by
  rw [show D2M8K2.u6056 = KTree.node D2M8K2.u6048 (nat_lit 12853471) (nat_lit 1727009054) (nat_lit 0) D2M8K2.u6055 from rfl, totK_node, atot6048, atot6055]
  decide +kernel

theorem arows6071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6071 = true := by
  rw [show D2M8K2.u6071 = KTree.node D2M8K2.u6063 (nat_lit 12869433) (nat_lit 1673183251) (nat_lit 0) D2M8K2.u6070 from rfl, allE_node, arows6063, irow6071, arows6070]
  all_goals rfl

theorem atot6071 : totK PD2M8K2 D2M8K2.u6071 = [0, 1235283130001, 5153424969766, 6111960995066, 1753029951939, 79190299505, 0, 0] := by
  rw [show D2M8K2.u6071 = KTree.node D2M8K2.u6063 (nat_lit 12869433) (nat_lit 1673183251) (nat_lit 0) D2M8K2.u6070 from rfl, totK_node, atot6063, atot6070]
  decide +kernel

theorem arows6088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6088 = true := by
  rw [show D2M8K2.u6088 = KTree.node D2M8K2.u6080 (nat_lit 12893228) (nat_lit 3666751273) (nat_lit 0) D2M8K2.u6087 from rfl, allE_node, arows6080, irow6088, arows6087]
  all_goals rfl

theorem atot6088 : totK PD2M8K2 D2M8K2.u6088 = [0, 756190395948, 3984981412695, 6415251261505, 2963268917008, 259324067152, 1429815836, 0] := by
  rw [show D2M8K2.u6088 = KTree.node D2M8K2.u6080 (nat_lit 12893228) (nat_lit 3666751273) (nat_lit 0) D2M8K2.u6087 from rfl, totK_node, atot6080, atot6087]
  decide +kernel

theorem arows6103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6103 = true := by
  rw [show D2M8K2.u6103 = KTree.node D2M8K2.u6095 (nat_lit 12911336) (nat_lit 1701119228) (nat_lit 0) D2M8K2.u6102 from rfl, allE_node, arows6095, irow6103, arows6102]
  all_goals rfl

theorem atot6103 : totK PD2M8K2 D2M8K2.u6103 = [0, 1243078453338, 5223307797376, 6145325794186, 1800446894334, 81955449487, 0, 0] := by
  rw [show D2M8K2.u6103 = KTree.node D2M8K2.u6095 (nat_lit 12911336) (nat_lit 1701119228) (nat_lit 0) D2M8K2.u6102 from rfl, totK_node, atot6095, atot6102]
  decide +kernel

theorem arows6119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6119 = true := by
  rw [show D2M8K2.u6119 = KTree.node D2M8K2.u6111 (nat_lit 12936431) (nat_lit 2147319959) (nat_lit 0) D2M8K2.u6118 from rfl, allE_node, arows6111, irow6119, arows6118]
  all_goals rfl

theorem atot6119 : totK PD2M8K2 D2M8K2.u6119 = [666037732093, 2046136657624, 2779519045278, 4549508538952, 3760879697927, 582836050331, 12189850367, 0] := by
  rw [show D2M8K2.u6119 = KTree.node D2M8K2.u6111 (nat_lit 12936431) (nat_lit 2147319959) (nat_lit 0) D2M8K2.u6118 from rfl, totK_node, atot6111, atot6118]
  decide +kernel

theorem arows6134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6134 = true := by
  rw [show D2M8K2.u6134 = KTree.node D2M8K2.u6126 (nat_lit 12954112) (nat_lit 1763908411) (nat_lit 0) D2M8K2.u6133 from rfl, allE_node, arows6126, irow6134, arows6133]
  all_goals rfl

theorem atot6134 : totK PD2M8K2 D2M8K2.u6134 = [1339611989931, 5339380598490, 5913834446796, 1588043582198, 71332521192, 0, 0, 0] := by
  rw [show D2M8K2.u6134 = KTree.node D2M8K2.u6126 (nat_lit 12954112) (nat_lit 1763908411) (nat_lit 0) D2M8K2.u6133 from rfl, totK_node, atot6126, atot6133]
  decide +kernel

theorem arows6156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6156 = true := by
  rw [show D2M8K2.u6156 = KTree.node D2M8K2.u6148 (nat_lit 12974932) (nat_lit 2797886101) (nat_lit 0) D2M8K2.u6155 from rfl, allE_node, arows6148, irow6156, arows6155]
  all_goals rfl

theorem atot6156 : totK PD2M8K2 D2M8K2.u6156 = [535074504078, 3496716835111, 6661063384569, 3363268666154, 286200420925, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6156 = KTree.node D2M8K2.u6148 (nat_lit 12974932) (nat_lit 2797886101) (nat_lit 0) D2M8K2.u6155 from rfl, totK_node, atot6148, atot6155]
  decide +kernel

theorem arows6171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6171 = true := by
  rw [show D2M8K2.u6171 = KTree.node D2M8K2.u6163 (nat_lit 12995185) (nat_lit 1464506414) (nat_lit 0) D2M8K2.u6170 from rfl, allE_node, arows6163, irow6171, arows6170]
  all_goals rfl

theorem atot6171 : totK PD2M8K2 D2M8K2.u6171 = [1493809749896, 5639807423767, 5858711017359, 1471388605411, 72653062958, 0, 0, 0] := by
  rw [show D2M8K2.u6171 = KTree.node D2M8K2.u6163 (nat_lit 12995185) (nat_lit 1464506414) (nat_lit 0) D2M8K2.u6170 from rfl, totK_node, atot6163, atot6170]
  decide +kernel

theorem arows6187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6187 = true := by
  rw [show D2M8K2.u6187 = KTree.node D2M8K2.u6179 (nat_lit 13012206) (nat_lit 4050905317) (nat_lit 0) D2M8K2.u6186 from rfl, allE_node, arows6179, irow6187, arows6186]
  all_goals rfl

theorem atot6187 : totK PD2M8K2 D2M8K2.u6187 = [0, 1669107986993, 5916475397992, 5610235852358, 1244692964987, 48715757244, 0, 0] := by
  rw [show D2M8K2.u6187 = KTree.node D2M8K2.u6179 (nat_lit 13012206) (nat_lit 4050905317) (nat_lit 0) D2M8K2.u6186 from rfl, totK_node, atot6179, atot6186]
  decide +kernel

theorem arows6202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6202 = true := by
  rw [show D2M8K2.u6202 = KTree.node D2M8K2.u6194 (nat_lit 13026884) (nat_lit 3388110699) (nat_lit 0) D2M8K2.u6201 from rfl, allE_node, arows6194, irow6202, arows6201]
  all_goals rfl

theorem atot6202 : totK PD2M8K2 D2M8K2.u6202 = [1425524695379, 5036515775507, 5463079134180, 2213164494843, 343530792075, 9302370699, 0, 0] := by
  rw [show D2M8K2.u6202 = KTree.node D2M8K2.u6194 (nat_lit 13026884) (nat_lit 3388110699) (nat_lit 0) D2M8K2.u6201 from rfl, totK_node, atot6194, atot6201]
  decide +kernel

theorem arows6219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6219 = true := by
  rw [show D2M8K2.u6219 = KTree.node D2M8K2.u6211 (nat_lit 13043087) (nat_lit 2754186090) (nat_lit 0) D2M8K2.u6218 from rfl, allE_node, arows6211, irow6219, arows6218]
  all_goals rfl

theorem atot6219 : totK PD2M8K2 D2M8K2.u6219 = [707482735916, 3997488816668, 6535753392117, 2931249416842, 232961699112, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6219 = KTree.node D2M8K2.u6211 (nat_lit 13043087) (nat_lit 2754186090) (nat_lit 0) D2M8K2.u6218 from rfl, totK_node, atot6211, atot6218]
  decide +kernel

theorem arows6234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6234 = true := by
  rw [show D2M8K2.u6234 = KTree.node D2M8K2.u6226 (nat_lit 13105274) (nat_lit 2254471687) (nat_lit 0) D2M8K2.u6233 from rfl, allE_node, arows6226, irow6234, arows6233]
  all_goals rfl

theorem atot6234 : totK PD2M8K2 D2M8K2.u6234 = [823639008143, 3766474805741, 5831225455932, 3312467320078, 524023714321, 17590593026, 0, 0] := by
  rw [show D2M8K2.u6234 = KTree.node D2M8K2.u6226 (nat_lit 13105274) (nat_lit 2254471687) (nat_lit 0) D2M8K2.u6233 from rfl, totK_node, atot6226, atot6233]
  decide +kernel

theorem arows6250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6250 = true := by
  rw [show D2M8K2.u6250 = KTree.node D2M8K2.u6242 (nat_lit 13119303) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u6249 from rfl, allE_node, arows6242, irow6250, arows6249]
  all_goals rfl

theorem atot6250 : totK PD2M8K2 D2M8K2.u6250 = [1187868158725, 4810967822452, 5956647260912, 2179150861577, 175972352607, 1138244013, 0, 0] := by
  rw [show D2M8K2.u6250 = KTree.node D2M8K2.u6242 (nat_lit 13119303) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u6249 from rfl, totK_node, atot6242, atot6249]
  decide +kernel

theorem arows6265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6265 = true := by
  rw [show D2M8K2.u6265 = KTree.node D2M8K2.u6257 (nat_lit 13141689) (nat_lit 1862393421) (nat_lit 0) D2M8K2.u6264 from rfl, allE_node, arows6257, irow6265, arows6264]
  all_goals rfl

theorem atot6265 : totK PD2M8K2 D2M8K2.u6265 = [826693180625, 4107303224707, 6229087441356, 2898541867288, 314989365462, 4977114383, 0, 0] := by
  rw [show D2M8K2.u6265 = KTree.node D2M8K2.u6257 (nat_lit 13141689) (nat_lit 1862393421) (nat_lit 0) D2M8K2.u6264 from rfl, totK_node, atot6257, atot6264]
  decide +kernel

theorem arows6283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6283 = true := by
  rw [show D2M8K2.u6283 = KTree.node D2M8K2.u6275 (nat_lit 13159093) (nat_lit 900128744) (nat_lit 0) D2M8K2.u6282 from rfl, allE_node, arows6275, irow6283, arows6282]
  all_goals rfl

theorem atot6283 : totK PD2M8K2 D2M8K2.u6283 = [1195523425885, 4901835685442, 6093994446447, 2103635113460, 145774220025, 1310285577, 0, 0] := by
  rw [show D2M8K2.u6283 = KTree.node D2M8K2.u6275 (nat_lit 13159093) (nat_lit 900128744) (nat_lit 0) D2M8K2.u6282 from rfl, totK_node, atot6275, atot6282]
  decide +kernel

theorem arows6298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6298 = true := by
  rw [show D2M8K2.u6298 = KTree.node D2M8K2.u6290 (nat_lit 13178604) (nat_lit 3550672013) (nat_lit 0) D2M8K2.u6297 from rfl, allE_node, arows6290, irow6298, arows6297]
  all_goals rfl

theorem atot6298 : totK PD2M8K2 D2M8K2.u6298 = [0, 1888002214876, 6242389703437, 5268248195347, 936875235461, 31562413104, 0, 0] := by
  rw [show D2M8K2.u6298 = KTree.node D2M8K2.u6290 (nat_lit 13178604) (nat_lit 3550672013) (nat_lit 0) D2M8K2.u6297 from rfl, totK_node, atot6290, atot6297]
  decide +kernel

theorem arows6314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6314 = true := by
  rw [show D2M8K2.u6314 = KTree.node D2M8K2.u6306 (nat_lit 13199997) (nat_lit 1229347320) (nat_lit 0) D2M8K2.u6313 from rfl, allE_node, arows6306, irow6314, arows6313]
  all_goals rfl

theorem atot6314 : totK PD2M8K2 D2M8K2.u6314 = [0, 1722076450022, 6112325060422, 5513601011202, 940960807008, 21802959708, 0, 0] := by
  rw [show D2M8K2.u6314 = KTree.node D2M8K2.u6306 (nat_lit 13199997) (nat_lit 1229347320) (nat_lit 0) D2M8K2.u6313 from rfl, totK_node, atot6306, atot6313]
  decide +kernel

theorem arows6329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6329 = true := by
  rw [show D2M8K2.u6329 = KTree.node D2M8K2.u6321 (nat_lit 13220545) (nat_lit 1373760810) (nat_lit 0) D2M8K2.u6328 from rfl, allE_node, arows6321, irow6329, arows6328]
  all_goals rfl

theorem atot6329 : totK PD2M8K2 D2M8K2.u6329 = [0, 443708700729, 3673615438118, 6940634678656, 2910004217019, 212888670955, 1275377855, 0] := by
  rw [show D2M8K2.u6329 = KTree.node D2M8K2.u6321 (nat_lit 13220545) (nat_lit 1373760810) (nat_lit 0) D2M8K2.u6328 from rfl, totK_node, atot6321, atot6328]
  decide +kernel

theorem arows6346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6346 = true := by
  rw [show D2M8K2.u6346 = KTree.node D2M8K2.u6338 (nat_lit 13243116) (nat_lit 3213900580) (nat_lit 0) D2M8K2.u6345 from rfl, allE_node, arows6338, irow6346, arows6345]
  all_goals rfl

theorem atot6346 : totK PD2M8K2 D2M8K2.u6346 = [0, 1581812230928, 5808343449933, 5776474365976, 1303522050782, 39535503103, 0, 0] := by
  rw [show D2M8K2.u6346 = KTree.node D2M8K2.u6338 (nat_lit 13243116) (nat_lit 3213900580) (nat_lit 0) D2M8K2.u6345 from rfl, totK_node, atot6338, atot6345]
  decide +kernel

theorem arows6361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6361 = true := by
  rw [show D2M8K2.u6361 = KTree.node D2M8K2.u6353 (nat_lit 13277725) (nat_lit 1130557898) (nat_lit 0) D2M8K2.u6360 from rfl, allE_node, arows6353, irow6361, arows6360]
  all_goals rfl

theorem atot6361 : totK PD2M8K2 D2M8K2.u6361 = [0, 1704983820121, 5955204943747, 5543320936714, 1202971825194, 51110278496, 0, 0] := by
  rw [show D2M8K2.u6361 = KTree.node D2M8K2.u6353 (nat_lit 13277725) (nat_lit 1130557898) (nat_lit 0) D2M8K2.u6360 from rfl, totK_node, atot6353, atot6360]
  decide +kernel

theorem arows6377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6377 = true := by
  rw [show D2M8K2.u6377 = KTree.node D2M8K2.u6369 (nat_lit 13294997) (nat_lit 2375234260) (nat_lit 0) D2M8K2.u6376 from rfl, allE_node, arows6369, irow6377, arows6376]
  all_goals rfl

theorem atot6377 : totK PD2M8K2 D2M8K2.u6377 = [0, 422956155823, 3186482202297, 6448559385909, 3588517542443, 494188701296, 14222663156, 0] := by
  rw [show D2M8K2.u6377 = KTree.node D2M8K2.u6369 (nat_lit 13294997) (nat_lit 2375234260) (nat_lit 0) D2M8K2.u6376 from rfl, totK_node, atot6369, atot6376]
  decide +kernel

theorem arows6392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6392 = true := by
  rw [show D2M8K2.u6392 = KTree.node D2M8K2.u6384 (nat_lit 13357937) (nat_lit 1737104167) (nat_lit 0) D2M8K2.u6391 from rfl, allE_node, arows6384, irow6392, arows6391]
  all_goals rfl

theorem atot6392 : totK PD2M8K2 D2M8K2.u6392 = [0, 1272691481212, 4958584500099, 5775694746819, 2055403997464, 207847104650, 4574395652, 0] := by
  rw [show D2M8K2.u6392 = KTree.node D2M8K2.u6384 (nat_lit 13357937) (nat_lit 1737104167) (nat_lit 0) D2M8K2.u6391 from rfl, totK_node, atot6384, atot6391]
  decide +kernel

theorem arows6411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6411 = true := by
  rw [show D2M8K2.u6411 = KTree.node D2M8K2.u6403 (nat_lit 13375656) (nat_lit 3591921269) (nat_lit 0) D2M8K2.u6410 from rfl, allE_node, arows6403, irow6411, arows6410]
  all_goals rfl

theorem atot6411 : totK PD2M8K2 D2M8K2.u6411 = [0, 734555081128, 4318239618006, 6589199218060, 2360956484103, 143897592751, 1103454931, 0] := by
  rw [show D2M8K2.u6411 = KTree.node D2M8K2.u6403 (nat_lit 13375656) (nat_lit 3591921269) (nat_lit 0) D2M8K2.u6410 from rfl, totK_node, atot6403, atot6410]
  decide +kernel

theorem arows6426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6426 = true := by
  rw [show D2M8K2.u6426 = KTree.node D2M8K2.u6418 (nat_lit 13399874) (nat_lit 4005993202) (nat_lit 0) D2M8K2.u6425 from rfl, allE_node, arows6418, irow6426, arows6425]
  all_goals rfl

theorem atot6426 : totK PD2M8K2 D2M8K2.u6426 = [0, 1403531216313, 5070626068612, 5592454271566, 2026835797464, 216002912521, 4779662215, 0] := by
  rw [show D2M8K2.u6426 = KTree.node D2M8K2.u6418 (nat_lit 13399874) (nat_lit 4005993202) (nat_lit 0) D2M8K2.u6425 from rfl, totK_node, atot6418, atot6425]
  decide +kernel

theorem arows6442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6442 = true := by
  rw [show D2M8K2.u6442 = KTree.node D2M8K2.u6434 (nat_lit 13935465) (nat_lit 1821247968) (nat_lit 0) D2M8K2.u6441 from rfl, allE_node, arows6434, irow6442, arows6441]
  all_goals rfl

theorem atot6442 : totK PD2M8K2 D2M8K2.u6442 = [1075962641304, 4110424161104, 5360748356152, 3173189610908, 685292424600, 27211392168, 0, 0] := by
  rw [show D2M8K2.u6442 = KTree.node D2M8K2.u6434 (nat_lit 13935465) (nat_lit 1821247968) (nat_lit 0) D2M8K2.u6441 from rfl, totK_node, atot6434, atot6441]
  decide +kernel

theorem arows6457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6457 = true := by
  rw [show D2M8K2.u6457 = KTree.node D2M8K2.u6449 (nat_lit 13953319) (nat_lit 2348484743) (nat_lit 0) D2M8K2.u6456 from rfl, allE_node, arows6449, irow6457, arows6456]
  all_goals rfl

theorem atot6457 : totK PD2M8K2 D2M8K2.u6457 = [897892356107, 4334415544925, 6217936938603, 2510760372294, 222472945493, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6457 = KTree.node D2M8K2.u6449 (nat_lit 13953319) (nat_lit 2348484743) (nat_lit 0) D2M8K2.u6456 from rfl, totK_node, atot6449, atot6456]
  decide +kernel

theorem arows6474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6474 = true := by
  rw [show D2M8K2.u6474 = KTree.node D2M8K2.u6466 (nat_lit 13980768) (nat_lit 3257669455) (nat_lit 0) D2M8K2.u6473 from rfl, allE_node, arows6466, irow6474, arows6473]
  all_goals rfl

theorem atot6474 : totK PD2M8K2 D2M8K2.u6474 = [1008894295652, 4554000463268, 6354089541821, 2394356990815, 132337519166, 0, 0, 0] := by
  rw [show D2M8K2.u6474 = KTree.node D2M8K2.u6466 (nat_lit 13980768) (nat_lit 3257669455) (nat_lit 0) D2M8K2.u6473 from rfl, totK_node, atot6466, atot6473]
  decide +kernel

theorem arows6489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6489 = true := by
  rw [show D2M8K2.u6489 = KTree.node D2M8K2.u6481 (nat_lit 13994282) (nat_lit 4059456874) (nat_lit 0) D2M8K2.u6488 from rfl, allE_node, arows6481, irow6489, arows6488]
  all_goals rfl

theorem atot6489 : totK PD2M8K2 D2M8K2.u6489 = [985613685759, 4293407430147, 5733748350938, 2831583313871, 633368935680, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6489 = KTree.node D2M8K2.u6481 (nat_lit 13994282) (nat_lit 4059456874) (nat_lit 0) D2M8K2.u6488 from rfl, totK_node, atot6481, atot6488]
  decide +kernel

theorem arows6505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6505 = true := by
  rw [show D2M8K2.u6505 = KTree.node D2M8K2.u6497 (nat_lit 14011464) (nat_lit 2413133877) (nat_lit 0) D2M8K2.u6504 from rfl, allE_node, arows6497, irow6505, arows6504]
  all_goals rfl

theorem atot6505 : totK PD2M8K2 D2M8K2.u6505 = [407232325195, 2432676006766, 5636241371439, 4978920517241, 964900254553, 21096254089, 0, 0] := by
  rw [show D2M8K2.u6505 = KTree.node D2M8K2.u6497 (nat_lit 14011464) (nat_lit 2413133877) (nat_lit 0) D2M8K2.u6504 from rfl, totK_node, atot6497, atot6504]
  decide +kernel

theorem arows6520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6520 = true := by
  rw [show D2M8K2.u6520 = KTree.node D2M8K2.u6512 (nat_lit 14025906) (nat_lit 2751315386) (nat_lit 0) D2M8K2.u6519 from rfl, allE_node, arows6512, irow6520, arows6519]
  all_goals rfl

theorem atot6520 : totK PD2M8K2 D2M8K2.u6520 = [1629225747626, 5798991649921, 5703452053343, 1358517792132, 56813280013, 0, 0, 0] := by
  rw [show D2M8K2.u6520 = KTree.node D2M8K2.u6512 (nat_lit 14025906) (nat_lit 2751315386) (nat_lit 0) D2M8K2.u6519 from rfl, totK_node, atot6512, atot6519]
  decide +kernel

theorem arows6538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6538 = true := by
  rw [show D2M8K2.u6538 = KTree.node D2M8K2.u6530 (nat_lit 14045506) (nat_lit 4035474104) (nat_lit 0) D2M8K2.u6537 from rfl, allE_node, arows6530, irow6538, arows6537]
  all_goals rfl

theorem atot6538 : totK PD2M8K2 D2M8K2.u6538 = [0, 2215444181497, 6659640246196, 4639852791072, 671232143431, 18797058808, 0, 0] := by
  rw [show D2M8K2.u6538 = KTree.node D2M8K2.u6530 (nat_lit 14045506) (nat_lit 4035474104) (nat_lit 0) D2M8K2.u6537 from rfl, totK_node, atot6530, atot6537]
  decide +kernel

theorem arows6553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6553 = true := by
  rw [show D2M8K2.u6553 = KTree.node D2M8K2.u6545 (nat_lit 14064970) (nat_lit 3653547740) (nat_lit 0) D2M8K2.u6552 from rfl, allE_node, arows6545, irow6553, arows6552]
  all_goals rfl

theorem atot6553 : totK PD2M8K2 D2M8K2.u6553 = [1651943885261, 5692290746913, 5503891513528, 1541123382901, 90959688806, 0, 0, 0] := by
  rw [show D2M8K2.u6553 = KTree.node D2M8K2.u6545 (nat_lit 14064970) (nat_lit 3653547740) (nat_lit 0) D2M8K2.u6552 from rfl, totK_node, atot6545, atot6552]
  decide +kernel

theorem arows6569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6569 = true := by
  rw [show D2M8K2.u6569 = KTree.node D2M8K2.u6561 (nat_lit 14090623) (nat_lit 2420449048) (nat_lit 0) D2M8K2.u6568 from rfl, allE_node, arows6561, irow6569, arows6568]
  all_goals rfl

theorem atot6569 : totK PD2M8K2 D2M8K2.u6569 = [190180602404, 2483887198863, 6371236232888, 4458019058907, 675092347094, 19065934916, 0, 0] := by
  rw [show D2M8K2.u6569 = KTree.node D2M8K2.u6561 (nat_lit 14090623) (nat_lit 2420449048) (nat_lit 0) D2M8K2.u6568 from rfl, totK_node, atot6561, atot6568]
  decide +kernel

theorem arows6584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6584 = true := by
  rw [show D2M8K2.u6584 = KTree.node D2M8K2.u6576 (nat_lit 14107761) (nat_lit 1786854237) (nat_lit 0) D2M8K2.u6583 from rfl, allE_node, arows6576, irow6584, arows6583]
  all_goals rfl

theorem atot6584 : totK PD2M8K2 D2M8K2.u6584 = [1550565395410, 5638425881994, 5657797785542, 1431079326698, 65080049256, 0, 0, 0] := by
  rw [show D2M8K2.u6584 = KTree.node D2M8K2.u6576 (nat_lit 14107761) (nat_lit 1786854237) (nat_lit 0) D2M8K2.u6583 from rfl, totK_node, atot6576, atot6583]
  decide +kernel

theorem arows6601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6601 = true := by
  rw [show D2M8K2.u6601 = KTree.node D2M8K2.u6593 (nat_lit 14125456) (nat_lit 3682693711) (nat_lit 0) D2M8K2.u6600 from rfl, allE_node, arows6593, irow6601, arows6600]
  all_goals rfl

theorem atot6601 : totK PD2M8K2 D2M8K2.u6601 = [357800183586, 3462190533706, 6975467600298, 3293427695446, 249297394877, 1138244013, 0, 0] := by
  rw [show D2M8K2.u6601 = KTree.node D2M8K2.u6593 (nat_lit 14125456) (nat_lit 3682693711) (nat_lit 0) D2M8K2.u6600 from rfl, totK_node, atot6593, atot6600]
  decide +kernel

theorem arows6616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6616 = true := by
  rw [show D2M8K2.u6616 = KTree.node D2M8K2.u6608 (nat_lit 14192160) (nat_lit 3592768262) (nat_lit 0) D2M8K2.u6615 from rfl, allE_node, arows6608, irow6616, arows6615]
  all_goals rfl

theorem atot6616 : totK PD2M8K2 D2M8K2.u6616 = [0, 1643121645208, 6012462518818, 5498758481585, 1026717836165, 33610537115, 0, 0] := by
  rw [show D2M8K2.u6616 = KTree.node D2M8K2.u6608 (nat_lit 14192160) (nat_lit 3592768262) (nat_lit 0) D2M8K2.u6615 from rfl, totK_node, atot6608, atot6615]
  decide +kernel

theorem arows6632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6632 = true := by
  rw [show D2M8K2.u6632 = KTree.node D2M8K2.u6624 (nat_lit 14211340) (nat_lit 3805558280) (nat_lit 0) D2M8K2.u6631 from rfl, allE_node, arows6624, irow6632, arows6631]
  all_goals rfl

theorem atot6632 : totK PD2M8K2 D2M8K2.u6632 = [0, 627376420780, 4151896475388, 6772880930102, 2436506077424, 166534454115, 1209030869, 0] := by
  rw [show D2M8K2.u6632 = KTree.node D2M8K2.u6624 (nat_lit 14211340) (nat_lit 3805558280) (nat_lit 0) D2M8K2.u6631 from rfl, totK_node, atot6624, atot6631]
  decide +kernel

theorem arows6647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6647 = true := by
  rw [show D2M8K2.u6647 = KTree.node D2M8K2.u6639 (nat_lit 14236156) (nat_lit 3259818342) (nat_lit 0) D2M8K2.u6646 from rfl, allE_node, arows6639, irow6647, arows6646]
  all_goals rfl

theorem atot6647 : totK PD2M8K2 D2M8K2.u6647 = [0, 1604486176769, 5812487070773, 5685715440995, 1367805590979, 65292993516, 0, 0] := by
  rw [show D2M8K2.u6647 = KTree.node D2M8K2.u6639 (nat_lit 14236156) (nat_lit 3259818342) (nat_lit 0) D2M8K2.u6646 from rfl, totK_node, atot6639, atot6646]
  decide +kernel

theorem arows6667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6667 = true := by
  rw [show D2M8K2.u6667 = KTree.node D2M8K2.u6659 (nat_lit 14271891) (nat_lit 3716614309) (nat_lit 0) D2M8K2.u6666 from rfl, allE_node, arows6659, irow6667, arows6666]
  all_goals rfl

theorem atot6667 : totK PD2M8K2 D2M8K2.u6667 = [0, 1717032020073, 5948985676533, 5582132518250, 1199621932154, 39104425999, 0, 0] := by
  rw [show D2M8K2.u6667 = KTree.node D2M8K2.u6659 (nat_lit 14271891) (nat_lit 3716614309) (nat_lit 0) D2M8K2.u6666 from rfl, totK_node, atot6659, atot6666]
  decide +kernel

theorem arows6682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6682 = true := by
  rw [show D2M8K2.u6682 = KTree.node D2M8K2.u6674 (nat_lit 14310276) (nat_lit 3223530506) (nat_lit 0) D2M8K2.u6681 from rfl, allE_node, arows6674, irow6682, arows6681]
  all_goals rfl

theorem atot6682 : totK PD2M8K2 D2M8K2.u6682 = [0, 1622623263931, 5977452227783, 5720854503349, 1120744585880, 27417010778, 0, 0] := by
  rw [show D2M8K2.u6682 = KTree.node D2M8K2.u6674 (nat_lit 14310276) (nat_lit 3223530506) (nat_lit 0) D2M8K2.u6681 from rfl, totK_node, atot6674, atot6681]
  decide +kernel

theorem arows6698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6698 = true := by
  rw [show D2M8K2.u6698 = KTree.node D2M8K2.u6690 (nat_lit 14351995) (nat_lit 2240577022) (nat_lit 0) D2M8K2.u6697 from rfl, allE_node, arows6690, irow6698, arows6697]
  all_goals rfl

theorem atot6698 : totK PD2M8K2 D2M8K2.u6698 = [0, 1673537483443, 5893499910821, 5541354605133, 1167978115846, 43139184878, 0, 0] := by
  rw [show D2M8K2.u6698 = KTree.node D2M8K2.u6690 (nat_lit 14351995) (nat_lit 2240577022) (nat_lit 0) D2M8K2.u6697 from rfl, totK_node, atot6690, atot6697]
  decide +kernel

theorem arows6713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6713 = true := by
  rw [show D2M8K2.u6713 = KTree.node D2M8K2.u6705 (nat_lit 14365221) (nat_lit 1441766414) (nat_lit 0) D2M8K2.u6712 from rfl, allE_node, arows6705, irow6713, arows6712]
  all_goals rfl

theorem atot6713 : totK PD2M8K2 D2M8K2.u6713 = [0, 843162022478, 4335701436540, 6417612249820, 2377271081883, 186040814264, 1138244013, 0] := by
  rw [show D2M8K2.u6713 = KTree.node D2M8K2.u6705 (nat_lit 14365221) (nat_lit 1441766414) (nat_lit 0) D2M8K2.u6712 from rfl, totK_node, atot6705, atot6712]
  decide +kernel

theorem arows6730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6730 = true := by
  rw [show D2M8K2.u6730 = KTree.node D2M8K2.u6722 (nat_lit 14433465) (nat_lit 1855267513) (nat_lit 0) D2M8K2.u6729 from rfl, allE_node, arows6722, irow6730, arows6729]
  all_goals rfl

theorem atot6730 : totK PD2M8K2 D2M8K2.u6730 = [1142044767870, 3752516479122, 4057639523313, 3282204959442, 1770361599913, 251423214348, 4977114383, 0] := by
  rw [show D2M8K2.u6730 = KTree.node D2M8K2.u6722 (nat_lit 14433465) (nat_lit 1855267513) (nat_lit 0) D2M8K2.u6729 from rfl, totK_node, atot6722, atot6729]
  decide +kernel

theorem arows6745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6745 = true := by
  rw [show D2M8K2.u6745 = KTree.node D2M8K2.u6737 (nat_lit 14451483) (nat_lit 1112978752) (nat_lit 0) D2M8K2.u6744 from rfl, allE_node, arows6737, irow6745, arows6744]
  all_goals rfl

theorem atot6745 : totK PD2M8K2 D2M8K2.u6745 = [836559489246, 4191582621736, 6310085951428, 2643487636830, 231263781900, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6745 = KTree.node D2M8K2.u6737 (nat_lit 14451483) (nat_lit 1112978752) (nat_lit 0) D2M8K2.u6744 from rfl, totK_node, atot6737, atot6744]
  decide +kernel

theorem arows6761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6761 = true := by
  rw [show D2M8K2.u6761 = KTree.node D2M8K2.u6753 (nat_lit 14478751) (nat_lit 2316705358) (nat_lit 0) D2M8K2.u6760 from rfl, allE_node, arows6753, irow6761, arows6760]
  all_goals rfl

theorem atot6761 : totK PD2M8K2 D2M8K2.u6761 = [1092452440725, 4689802869245, 6259520983331, 2310418484154, 127767200308, 0, 0, 0] := by
  rw [show D2M8K2.u6761 = KTree.node D2M8K2.u6753 (nat_lit 14478751) (nat_lit 2316705358) (nat_lit 0) D2M8K2.u6760 from rfl, totK_node, atot6753, atot6760]
  decide +kernel

theorem arows6776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6776 = true := by
  rw [show D2M8K2.u6776 = KTree.node D2M8K2.u6768 (nat_lit 14492806) (nat_lit 3703103347) (nat_lit 0) D2M8K2.u6775 from rfl, allE_node, arows6768, irow6776, arows6775]
  all_goals rfl

theorem atot6776 : totK PD2M8K2 D2M8K2.u6776 = [911046264957, 4190318216992, 5850800861981, 2924220599872, 638695093322, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6776 = KTree.node D2M8K2.u6768 (nat_lit 14492806) (nat_lit 3703103347) (nat_lit 0) D2M8K2.u6775 from rfl, totK_node, atot6768, atot6775]
  decide +kernel

theorem arows6794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6794 = true := by
  rw [show D2M8K2.u6794 = KTree.node D2M8K2.u6786 (nat_lit 14510331) (nat_lit 3784810785) (nat_lit 0) D2M8K2.u6793 from rfl, allE_node, arows6786, irow6794, arows6793]
  all_goals rfl

theorem atot6794 : totK PD2M8K2 D2M8K2.u6794 = [407993187048, 2469339063770, 5712612976835, 4900217378406, 956010354246, 21096254089, 0, 0] := by
  rw [show D2M8K2.u6794 = KTree.node D2M8K2.u6786 (nat_lit 14510331) (nat_lit 3784810785) (nat_lit 0) D2M8K2.u6793 from rfl, totK_node, atot6786, atot6793]
  decide +kernel

theorem arows6809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6809 = true := by
  rw [show D2M8K2.u6809 = KTree.node D2M8K2.u6801 (nat_lit 14523902) (nat_lit 3059222678) (nat_lit 0) D2M8K2.u6808 from rfl, allE_node, arows6801, irow6809, arows6808]
  all_goals rfl

theorem atot6809 : totK PD2M8K2 D2M8K2.u6809 = [1631731780418, 5817740966944, 5695040907333, 1359166520079, 56709236099, 0, 0, 0] := by
  rw [show D2M8K2.u6809 = KTree.node D2M8K2.u6801 (nat_lit 14523902) (nat_lit 3059222678) (nat_lit 0) D2M8K2.u6808 from rfl, totK_node, atot6801, atot6808]
  decide +kernel

theorem arows6825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6825 = true := by
  rw [show D2M8K2.u6825 = KTree.node D2M8K2.u6817 (nat_lit 14543349) (nat_lit 1127558416) (nat_lit 0) D2M8K2.u6824 from rfl, allE_node, arows6817, irow6825, arows6824]
  all_goals rfl

theorem atot6825 : totK PD2M8K2 D2M8K2.u6825 = [0, 2179112284621, 6647326137293, 4733628700516, 691589230610, 18797058808, 0, 0] := by
  rw [show D2M8K2.u6825 = KTree.node D2M8K2.u6817 (nat_lit 14543349) (nat_lit 1127558416) (nat_lit 0) D2M8K2.u6824 from rfl, totK_node, atot6817, atot6824]
  decide +kernel

theorem arows6840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6840 = true := by
  rw [show D2M8K2.u6840 = KTree.node D2M8K2.u6832 (nat_lit 14562980) (nat_lit 3195830551) (nat_lit 0) D2M8K2.u6839 from rfl, allE_node, arows6832, irow6840, arows6839]
  all_goals rfl

theorem atot6840 : totK PD2M8K2 D2M8K2.u6840 = [1658021316512, 5736264369539, 5568036960435, 1466143639851, 70923995819, 0, 0, 0] := by
  rw [show D2M8K2.u6840 = KTree.node D2M8K2.u6832 (nat_lit 14562980) (nat_lit 3195830551) (nat_lit 0) D2M8K2.u6839 from rfl, totK_node, atot6832, atot6839]
  decide +kernel

theorem arows6857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6857 = true := by
  rw [show D2M8K2.u6857 = KTree.node D2M8K2.u6849 (nat_lit 14588301) (nat_lit 1157334358) (nat_lit 0) D2M8K2.u6856 from rfl, allE_node, arows6849, irow6857, arows6856]
  all_goals rfl

theorem atot6857 : totK PD2M8K2 D2M8K2.u6857 = [414024072134, 3038113902677, 6317378185681, 3986460931470, 549520148901, 14345316470, 0, 0] := by
  rw [show D2M8K2.u6857 = KTree.node D2M8K2.u6849 (nat_lit 14588301) (nat_lit 1157334358) (nat_lit 0) D2M8K2.u6856 from rfl, totK_node, atot6849, atot6856]
  decide +kernel

theorem arows6872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6872 = true := by
  rw [show D2M8K2.u6872 = KTree.node D2M8K2.u6864 (nat_lit 14648036) (nat_lit 2787046522) (nat_lit 0) D2M8K2.u6871 from rfl, allE_node, arows6864, irow6872, arows6871]
  all_goals rfl

theorem atot6872 : totK PD2M8K2 D2M8K2.u6872 = [1603957370944, 5718354881673, 5685110011846, 1411012755676, 62332196746, 0, 0, 0] := by
  rw [show D2M8K2.u6872 = KTree.node D2M8K2.u6864 (nat_lit 14648036) (nat_lit 2787046522) (nat_lit 0) D2M8K2.u6871 from rfl, totK_node, atot6864, atot6871]
  decide +kernel

theorem arows6888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6888 = true := by
  rw [show D2M8K2.u6888 = KTree.node D2M8K2.u6880 (nat_lit 14665065) (nat_lit 1868732786) (nat_lit 0) D2M8K2.u6887 from rfl, allE_node, arows6880, irow6888, arows6887]
  all_goals rfl

theorem atot6888 : totK PD2M8K2 D2M8K2.u6888 = [93924006320, 2360664656485, 6584802489324, 4630994497700, 612347283716, 11121530615, 0, 0] := by
  rw [show D2M8K2.u6888 = KTree.node D2M8K2.u6880 (nat_lit 14665065) (nat_lit 1868732786) (nat_lit 0) D2M8K2.u6887 from rfl, totK_node, atot6880, atot6887]
  decide +kernel

theorem arows6903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6903 = true := by
  rw [show D2M8K2.u6903 = KTree.node D2M8K2.u6895 (nat_lit 14683996) (nat_lit 3427498986) (nat_lit 0) D2M8K2.u6902 from rfl, allE_node, arows6895, irow6903, arows6902]
  all_goals rfl

theorem atot6903 : totK PD2M8K2 D2M8K2.u6903 = [0, 1686044634044, 5978104890199, 5560995017030, 1100417851067, 33522066156, 0, 0] := by
  rw [show D2M8K2.u6903 = KTree.node D2M8K2.u6895 (nat_lit 14683996) (nat_lit 3427498986) (nat_lit 0) D2M8K2.u6902 from rfl, totK_node, atot6895, atot6902]
  decide +kernel

theorem arows6922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6922 = true := by
  rw [show D2M8K2.u6922 = KTree.node D2M8K2.u6914 (nat_lit 14702550) (nat_lit 2776089533) (nat_lit 0) D2M8K2.u6921 from rfl, allE_node, arows6914, irow6922, arows6921]
  all_goals rfl

theorem atot6922 : totK PD2M8K2 D2M8K2.u6922 = [0, 734385748217, 4077183071323, 6498243895429, 2615199358796, 184992446542, 1369150432, 0] := by
  rw [show D2M8K2.u6922 = KTree.node D2M8K2.u6914 (nat_lit 14702550) (nat_lit 2776089533) (nat_lit 0) D2M8K2.u6921 from rfl, totK_node, atot6914, atot6921]
  decide +kernel

theorem arows6937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6937 = true := by
  rw [show D2M8K2.u6937 = KTree.node D2M8K2.u6929 (nat_lit 14729609) (nat_lit 1632094417) (nat_lit 0) D2M8K2.u6936 from rfl, allE_node, arows6929, irow6937, arows6936]
  all_goals rfl

theorem atot6937 : totK PD2M8K2 D2M8K2.u6937 = [0, 1335153552673, 5161335965414, 6023905015699, 1876452126672, 87571071927, 0, 0] := by
  rw [show D2M8K2.u6937 = KTree.node D2M8K2.u6929 (nat_lit 14729609) (nat_lit 1632094417) (nat_lit 0) D2M8K2.u6936 from rfl, totK_node, atot6929, atot6936]
  decide +kernel

theorem arows6953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6953 = true := by
  rw [show D2M8K2.u6953 = KTree.node D2M8K2.u6945 (nat_lit 14764912) (nat_lit 2745989462) (nat_lit 0) D2M8K2.u6952 from rfl, allE_node, arows6945, irow6953, arows6952]
  all_goals rfl

theorem atot6953 : totK PD2M8K2 D2M8K2.u6953 = [0, 1669372594892, 5847320158249, 5559882573658, 1342405576867, 57494380141, 0, 0] := by
  rw [show D2M8K2.u6953 = KTree.node D2M8K2.u6945 (nat_lit 14764912) (nat_lit 2745989462) (nat_lit 0) D2M8K2.u6952 from rfl, totK_node, atot6945, atot6952]
  decide +kernel

theorem arows6968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6968 = true := by
  rw [show D2M8K2.u6968 = KTree.node D2M8K2.u6960 (nat_lit 14782096) (nat_lit 3686599679) (nat_lit 0) D2M8K2.u6967 from rfl, allE_node, arows6960, irow6968, arows6967]
  all_goals rfl

theorem atot6968 : totK PD2M8K2 D2M8K2.u6968 = [0, 1035653956085, 4720641879889, 6239459793757, 2188333417051, 142591000593, 1166720416, 0] := by
  rw [show D2M8K2.u6968 = KTree.node D2M8K2.u6960 (nat_lit 14782096) (nat_lit 3686599679) (nat_lit 0) D2M8K2.u6967 from rfl, totK_node, atot6960, atot6967]
  decide +kernel

theorem arows6985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6985 = true := by
  rw [show D2M8K2.u6985 = KTree.node D2M8K2.u6977 (nat_lit 14805643) (nat_lit 1615827190) (nat_lit 0) D2M8K2.u6984 from rfl, allE_node, arows6977, irow6985, arows6984]
  all_goals rfl

theorem atot6985 : totK PD2M8K2 D2M8K2.u6985 = [0, 888158569935, 4185299936706, 6177716319772, 2742029855362, 281168356484, 5134755853, 0] := by
  rw [show D2M8K2.u6985 = KTree.node D2M8K2.u6977 (nat_lit 14805643) (nat_lit 1615827190) (nat_lit 0) D2M8K2.u6984 from rfl, totK_node, atot6977, atot6984]
  decide +kernel

theorem arows7000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7000 = true := by
  rw [show D2M8K2.u7000 = KTree.node D2M8K2.u6992 (nat_lit 14826026) (nat_lit 4015477221) (nat_lit 0) D2M8K2.u6999 from rfl, allE_node, arows6992, irow7000, arows6999]
  all_goals rfl

theorem atot7000 : totK PD2M8K2 D2M8K2.u7000 = [0, 768514840026, 4116031820987, 6411461276677, 2775092100107, 220447812545, 2335892675, 0] := by
  rw [show D2M8K2.u7000 = KTree.node D2M8K2.u6992 (nat_lit 14826026) (nat_lit 4015477221) (nat_lit 0) D2M8K2.u6999 from rfl, totK_node, atot6992, atot6999]
  decide +kernel

theorem arows7016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7016 = true := by
  rw [show D2M8K2.u7016 = KTree.node D2M8K2.u7008 (nat_lit 14892684) (nat_lit 2936342548) (nat_lit 0) D2M8K2.u7015 from rfl, allE_node, arows7008, irow7016, arows7015]
  all_goals rfl

theorem atot7016 : totK PD2M8K2 D2M8K2.u7016 = [0, 1324760789560, 4989378823405, 5746551725054, 2078363413761, 202154252232, 4028038878, 0] := by
  rw [show D2M8K2.u7016 = KTree.node D2M8K2.u7008 (nat_lit 14892684) (nat_lit 2936342548) (nat_lit 0) D2M8K2.u7015 from rfl, totK_node, atot7008, atot7015]
  decide +kernel

theorem arows7031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7031 = true := by
  rw [show D2M8K2.u7031 = KTree.node D2M8K2.u7023 (nat_lit 14908965) (nat_lit 889790766) (nat_lit 0) D2M8K2.u7030 from rfl, allE_node, arows7023, irow7031, arows7030]
  all_goals rfl

theorem atot7031 : totK PD2M8K2 D2M8K2.u7031 = [0, 785303906976, 4176576362034, 6415324817627, 2697075282241, 212163327372, 1288491354, 0] := by
  rw [show D2M8K2.u7031 = KTree.node D2M8K2.u7023 (nat_lit 14908965) (nat_lit 889790766) (nat_lit 0) D2M8K2.u7030 from rfl, totK_node, atot7023, atot7030]
  decide +kernel

theorem arows7049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7049 = true := by
  rw [show D2M8K2.u7049 = KTree.node D2M8K2.u7041 (nat_lit 14928417) (nat_lit 980666555) (nat_lit 0) D2M8K2.u7048 from rfl, allE_node, arows7041, irow7049, arows7048]
  all_goals rfl

theorem atot7049 : totK PD2M8K2 D2M8K2.u7049 = [0, 863604381076, 3533020071328, 5364674539230, 3670209786322, 766781368486, 31376465649, 0] := by
  rw [show D2M8K2.u7049 = KTree.node D2M8K2.u7041 (nat_lit 14928417) (nat_lit 980666555) (nat_lit 0) D2M8K2.u7048 from rfl, totK_node, atot7041, atot7048]
  decide +kernel

theorem arows7064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7064 = true := by
  rw [show D2M8K2.u7064 = KTree.node D2M8K2.u7056 (nat_lit 14945490) (nat_lit 3332132333) (nat_lit 0) D2M8K2.u7063 from rfl, allE_node, arows7056, irow7064, arows7063]
  all_goals rfl

theorem atot7064 : totK PD2M8K2 D2M8K2.u7064 = [0, 1233388766322, 5154971206701, 6081954309547, 1663469097455, 75146767824, 0, 0] := by
  rw [show D2M8K2.u7064 = KTree.node D2M8K2.u7056 (nat_lit 14945490) (nat_lit 3332132333) (nat_lit 0) D2M8K2.u7063 from rfl, totK_node, atot7056, atot7063]
  decide +kernel

theorem arows7080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7080 = true := by
  rw [show D2M8K2.u7080 = KTree.node D2M8K2.u7072 (nat_lit 14965688) (nat_lit 3820835085) (nat_lit 0) D2M8K2.u7079 from rfl, allE_node, arows7072, irow7080, arows7079]
  all_goals rfl

theorem atot7080 : totK PD2M8K2 D2M8K2.u7080 = [0, 768819602542, 3958485635540, 6408651831656, 2869043796834, 243629770180, 1369150432, 0] := by
  rw [show D2M8K2.u7080 = KTree.node D2M8K2.u7072 (nat_lit 14965688) (nat_lit 3820835085) (nat_lit 0) D2M8K2.u7079 from rfl, totK_node, atot7072, atot7079]
  decide +kernel

theorem arows7095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7095 = true := by
  rw [show D2M8K2.u7095 = KTree.node D2M8K2.u7087 (nat_lit 15027726) (nat_lit 3042133327) (nat_lit 0) D2M8K2.u7094 from rfl, allE_node, arows7087, irow7095, arows7094]
  all_goals rfl

theorem atot7095 : totK PD2M8K2 D2M8K2.u7095 = [0, 1265639790756, 5272415958070, 6125886375947, 1700877573095, 71287159929, 0, 0] := by
  rw [show D2M8K2.u7095 = KTree.node D2M8K2.u7087 (nat_lit 15027726) (nat_lit 3042133327) (nat_lit 0) D2M8K2.u7094 from rfl, totK_node, atot7087, atot7094]
  decide +kernel

theorem arows7112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7112 = true := by
  rw [show D2M8K2.u7112 = KTree.node D2M8K2.u7104 (nat_lit 15043817) (nat_lit 1598410014) (nat_lit 0) D2M8K2.u7111 from rfl, allE_node, arows7104, irow7112, arows7111]
  all_goals rfl

theorem atot7112 : totK PD2M8K2 D2M8K2.u7112 = [0, 420970288622, 2698664800164, 6074931620047, 4343482998009, 661182833310, 18797058808, 0] := by
  rw [show D2M8K2.u7112 = KTree.node D2M8K2.u7104 (nat_lit 15043817) (nat_lit 1598410014) (nat_lit 0) D2M8K2.u7111 from rfl, totK_node, atot7104, atot7111]
  decide +kernel

theorem arows7127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7127 = true := by
  rw [show D2M8K2.u7127 = KTree.node D2M8K2.u7119 (nat_lit 15069893) (nat_lit 2261504021) (nat_lit 0) D2M8K2.u7126 from rfl, allE_node, arows7119, irow7127, arows7126]
  all_goals rfl

theorem atot7127 : totK PD2M8K2 D2M8K2.u7127 = [0, 1227471855776, 5259725799910, 6165036104953, 1619970096918, 67393583639, 0, 0] := by
  rw [show D2M8K2.u7127 = KTree.node D2M8K2.u7119 (nat_lit 15069893) (nat_lit 2261504021) (nat_lit 0) D2M8K2.u7126 from rfl, totK_node, atot7119, atot7126]
  decide +kernel

theorem arows7143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7143 = true := by
  rw [show D2M8K2.u7143 = KTree.node D2M8K2.u7135 (nat_lit 15096073) (nat_lit 1508690721) (nat_lit 0) D2M8K2.u7142 from rfl, allE_node, arows7135, irow7143, arows7142]
  all_goals rfl

theorem atot7143 : totK PD2M8K2 D2M8K2.u7143 = [0, 1005462154882, 4460442455544, 6200545144362, 2513531555420, 179275303879, 1239866073, 0] := by
  rw [show D2M8K2.u7143 = KTree.node D2M8K2.u7135 (nat_lit 15096073) (nat_lit 1508690721) (nat_lit 0) D2M8K2.u7142 from rfl, totK_node, atot7135, atot7142]
  decide +kernel

theorem arows7158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7158 = true := by
  rw [show D2M8K2.u7158 = KTree.node D2M8K2.u7150 (nat_lit 15110455) (nat_lit 1537070281) (nat_lit 0) D2M8K2.u7157 from rfl, allE_node, arows7150, irow7158, arows7157]
  all_goals rfl

theorem atot7158 : totK PD2M8K2 D2M8K2.u7158 = [0, 972388587419, 4582858663627, 6276912445646, 2251150708292, 165154089148, 1138244013, 0] := by
  rw [show D2M8K2.u7158 = KTree.node D2M8K2.u7150 (nat_lit 15110455) (nat_lit 1537070281) (nat_lit 0) D2M8K2.u7157 from rfl, totK_node, atot7150, atot7157]
  decide +kernel

theorem arows7179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7179 = true := by
  rw [show D2M8K2.u7179 = KTree.node D2M8K2.u7171 (nat_lit 15137371) (nat_lit 2238932575) (nat_lit 0) D2M8K2.u7178 from rfl, allE_node, arows7171, irow7179, arows7178]
  all_goals rfl

theorem atot7179 : totK PD2M8K2 D2M8K2.u7179 = [0, 918483516923, 4213187844437, 6177766772576, 2753821283543, 277858922785, 4977114383, 0] := by
  rw [show D2M8K2.u7179 = KTree.node D2M8K2.u7171 (nat_lit 15137371) (nat_lit 2238932575) (nat_lit 0) D2M8K2.u7178 from rfl, totK_node, atot7171, atot7178]
  decide +kernel

theorem arows7194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7194 = true := by
  rw [show D2M8K2.u7194 = KTree.node D2M8K2.u7186 (nat_lit 15155178) (nat_lit 3070046354) (nat_lit 0) D2M8K2.u7193 from rfl, allE_node, arows7186, irow7194, arows7193]
  all_goals rfl

theorem atot7194 : totK PD2M8K2 D2M8K2.u7194 = [0, 1070513066709, 4607603098798, 6106021596641, 2403369531576, 194050748596, 1310285577, 0] := by
  rw [show D2M8K2.u7194 = KTree.node D2M8K2.u7186 (nat_lit 15155178) (nat_lit 3070046354) (nat_lit 0) D2M8K2.u7193 from rfl, totK_node, atot7186, atot7193]
  decide +kernel

theorem arows7210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7210 = true := by
  rw [show D2M8K2.u7210 = KTree.node D2M8K2.u7202 (nat_lit 15176047) (nat_lit 1467490262) (nat_lit 0) D2M8K2.u7209 from rfl, allE_node, arows7202, irow7210, arows7209]
  all_goals rfl

theorem atot7210 : totK PD2M8K2 D2M8K2.u7210 = [0, 0, 2076529550695, 6580312196173, 4971659886828, 743010010536, 20035484872, 0] := by
  rw [show D2M8K2.u7210 = KTree.node D2M8K2.u7202 (nat_lit 15176047) (nat_lit 1467490262) (nat_lit 0) D2M8K2.u7209 from rfl, totK_node, atot7202, atot7209]
  decide +kernel

theorem arows7225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7225 = true := by
  rw [show D2M8K2.u7225 = KTree.node D2M8K2.u7217 (nat_lit 15193784) (nat_lit 3820835085) (nat_lit 0) D2M8K2.u7224 from rfl, allE_node, arows7217, irow7225, arows7224]
  all_goals rfl

theorem atot7225 : totK PD2M8K2 D2M8K2.u7225 = [0, 0, 1385189973695, 5514065569848, 5854358607297, 1290611538250, 51248927348, 0] := by
  rw [show D2M8K2.u7225 = KTree.node D2M8K2.u7217 (nat_lit 15193784) (nat_lit 3820835085) (nat_lit 0) D2M8K2.u7224 from rfl, totK_node, atot7217, atot7224]
  decide +kernel

theorem arows7242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7242 = true := by
  rw [show D2M8K2.u7242 = KTree.node D2M8K2.u7234 (nat_lit 15218250) (nat_lit 3776999835) (nat_lit 0) D2M8K2.u7241 from rfl, allE_node, arows7234, irow7242, arows7241]
  all_goals rfl

theorem atot7242 : totK PD2M8K2 D2M8K2.u7242 = [0, 0, 933377859072, 4679110921383, 6356802562616, 2072083721563, 160285602492, 1369150432] := by
  rw [show D2M8K2.u7242 = KTree.node D2M8K2.u7234 (nat_lit 15218250) (nat_lit 3776999835) (nat_lit 0) D2M8K2.u7241 from rfl, totK_node, atot7234, atot7241]
  decide +kernel

theorem arows7257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7257 = true := by
  rw [show D2M8K2.u7257 = KTree.node D2M8K2.u7249 (nat_lit 15279450) (nat_lit 2697751778) (nat_lit 640) D2M8K2.u7256 from rfl, allE_node, arows7249, irow7257, arows7256]
  all_goals rfl

theorem atot7257 : totK PD2M8K2 D2M8K2.u7257 = [0, 0, 1756300787725, 6089105906931, 5475365858725, 973498448964, 33020449330, 0] := by
  rw [show D2M8K2.u7257 = KTree.node D2M8K2.u7249 (nat_lit 15279450) (nat_lit 2697751778) (nat_lit 640) D2M8K2.u7256 from rfl, totK_node, atot7249, atot7256]
  decide +kernel

theorem arows7273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7273 = true := by
  rw [show D2M8K2.u7273 = KTree.node D2M8K2.u7265 (nat_lit 15345832) (nat_lit 3645917015) (nat_lit 0) D2M8K2.u7272 from rfl, allE_node, arows7265, irow7273, arows7272]
  all_goals rfl

theorem atot7273 : totK PD2M8K2 D2M8K2.u7273 = [0, 0, 2123243616093, 6725319106530, 4903625506851, 566821999564, 5039535969, 0] := by
  rw [show D2M8K2.u7273 = KTree.node D2M8K2.u7265 (nat_lit 15345832) (nat_lit 3645917015) (nat_lit 0) D2M8K2.u7272 from rfl, totK_node, atot7265, atot7272]
  decide +kernel

theorem arows7288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7288 = true := by
  rw [show D2M8K2.u7288 = KTree.node D2M8K2.u7280 (nat_lit 15361593) (nat_lit 1899350950) (nat_lit 0) D2M8K2.u7287 from rfl, allE_node, arows7280, irow7288, arows7287]
  all_goals rfl

theorem atot7288 : totK PD2M8K2 D2M8K2.u7288 = [0, 0, 1973392541412, 6466003775230, 5150111153884, 741578229334, 19366868959, 0] := by
  rw [show D2M8K2.u7288 = KTree.node D2M8K2.u7280 (nat_lit 15361593) (nat_lit 1899350950) (nat_lit 0) D2M8K2.u7287 from rfl, totK_node, atot7280, atot7287]
  decide +kernel

theorem arows7306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7306 = true := by
  rw [show D2M8K2.u7306 = KTree.node D2M8K2.u7298 (nat_lit 15473074) (nat_lit 4137157413) (nat_lit 0) D2M8K2.u7305 from rfl, allE_node, arows7298, irow7306, arows7305]
  all_goals rfl

theorem atot7306 : totK PD2M8K2 D2M8K2.u7306 = [0, 872868330901, 3841756495764, 5824980582635, 3476436347503, 576190768851, 19002749436, 0] := by
  rw [show D2M8K2.u7306 = KTree.node D2M8K2.u7298 (nat_lit 15473074) (nat_lit 4137157413) (nat_lit 0) D2M8K2.u7305 from rfl, totK_node, atot7298, atot7305]
  decide +kernel

theorem arows7321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7321 = true := by
  rw [show D2M8K2.u7321 = KTree.node D2M8K2.u7313 (nat_lit 15485829) (nat_lit 1513247326) (nat_lit 0) D2M8K2.u7320 from rfl, allE_node, arows7313, irow7321, arows7320]
  all_goals rfl

theorem atot7321 : totK PD2M8K2 D2M8K2.u7321 = [0, 1244839965314, 4970200211810, 5897713546514, 2072228416582, 269976654850, 21385604922, 0] := by
  rw [show D2M8K2.u7321 = KTree.node D2M8K2.u7313 (nat_lit 15485829) (nat_lit 1513247326) (nat_lit 0) D2M8K2.u7320 from rfl, totK_node, atot7313, atot7320]
  decide +kernel

theorem arows7337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7337 = true := by
  rw [show D2M8K2.u7337 = KTree.node D2M8K2.u7329 (nat_lit 15502319) (nat_lit 2534836222) (nat_lit 0) D2M8K2.u7336 from rfl, allE_node, arows7329, irow7337, arows7336]
  all_goals rfl

theorem atot7337 : totK PD2M8K2 D2M8K2.u7337 = [0, 0, 1660568285098, 5985323734254, 5621447295026, 1137683891322, 28568825804, 0] := by
  rw [show D2M8K2.u7337 = KTree.node D2M8K2.u7329 (nat_lit 15502319) (nat_lit 2534836222) (nat_lit 0) D2M8K2.u7336 from rfl, totK_node, atot7329, atot7336]
  decide +kernel

theorem arows7352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7352 = true := by
  rw [show D2M8K2.u7352 = KTree.node D2M8K2.u7344 (nat_lit 15517081) (nat_lit 1030447029) (nat_lit 0) D2M8K2.u7351 from rfl, allE_node, arows7344, irow7352, arows7351]
  all_goals rfl

theorem atot7352 : totK PD2M8K2 D2M8K2.u7352 = [0, 1625231011170, 5614439229541, 5404347510011, 1625840737825, 224510986854, 8063697217, 0] := by
  rw [show D2M8K2.u7352 = KTree.node D2M8K2.u7344 (nat_lit 15517081) (nat_lit 1030447029) (nat_lit 0) D2M8K2.u7351 from rfl, totK_node, atot7344, atot7351]
  decide +kernel

theorem arows7369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7369 = true := by
  rw [show D2M8K2.u7369 = KTree.node D2M8K2.u7361 (nat_lit 15535701) (nat_lit 1713959946) (nat_lit 0) D2M8K2.u7368 from rfl, allE_node, arows7361, irow7369, arows7368]
  all_goals rfl

theorem atot7369 : totK PD2M8K2 D2M8K2.u7369 = [0, 417115925447, 3262262503789, 6576830037247, 3610697899642, 479281326000, 14037798012, 0] := by
  rw [show D2M8K2.u7369 = KTree.node D2M8K2.u7361 (nat_lit 15535701) (nat_lit 1713959946) (nat_lit 0) D2M8K2.u7368 from rfl, totK_node, atot7361, atot7368]
  decide +kernel

theorem arows7384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7384 = true := by
  rw [show D2M8K2.u7384 = KTree.node D2M8K2.u7376 (nat_lit 15562462) (nat_lit 3827692668) (nat_lit 0) D2M8K2.u7383 from rfl, allE_node, arows7376, irow7384, arows7383]
  all_goals rfl

theorem atot7384 : totK PD2M8K2 D2M8K2.u7384 = [0, 1324552879557, 5043112510869, 5791400076027, 2111408415189, 190869039481, 3552795014, 0] := by
  rw [show D2M8K2.u7384 = KTree.node D2M8K2.u7376 (nat_lit 15562462) (nat_lit 3827692668) (nat_lit 0) D2M8K2.u7383 from rfl, totK_node, atot7376, atot7383]
  decide +kernel

theorem arows7400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7400 = true := by
  rw [show D2M8K2.u7400 = KTree.node D2M8K2.u7392 (nat_lit 15584452) (nat_lit 2768622093) (nat_lit 0) D2M8K2.u7399 from rfl, allE_node, arows7392, irow7400, arows7399]
  all_goals rfl

theorem atot7400 : totK PD2M8K2 D2M8K2.u7400 = [0, 422934678092, 3094893779435, 6522570121235, 3936362796525, 461969989699, 7133208874, 0] := by
  rw [show D2M8K2.u7400 = KTree.node D2M8K2.u7392 (nat_lit 15584452) (nat_lit 2768622093) (nat_lit 0) D2M8K2.u7399 from rfl, totK_node, atot7392, atot7399]
  decide +kernel

theorem arows7415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7415 = true := by
  rw [show D2M8K2.u7415 = KTree.node D2M8K2.u7407 (nat_lit 15600864) (nat_lit 2748177743) (nat_lit 0) D2M8K2.u7414 from rfl, allE_node, arows7407, irow7415, arows7414]
  all_goals rfl

theorem atot7415 : totK PD2M8K2 D2M8K2.u7415 = [0, 1636592219690, 5795149129293, 5572730306453, 1376726797599, 64073197757, 0, 0] := by
  rw [show D2M8K2.u7415 = KTree.node D2M8K2.u7407 (nat_lit 15600864) (nat_lit 2748177743) (nat_lit 0) D2M8K2.u7414 from rfl, totK_node, atot7407, atot7414]
  decide +kernel

theorem arows7434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7434 = true := by
  rw [show D2M8K2.u7434 = KTree.node D2M8K2.u7426 (nat_lit 15621675) (nat_lit 3654424576) (nat_lit 0) D2M8K2.u7433 from rfl, allE_node, arows7426, irow7434, arows7433]
  all_goals rfl

theorem atot7434 : totK PD2M8K2 D2M8K2.u7434 = [0, 435292570012, 3441246175209, 6739478266271, 3375052345017, 342789252381, 4977114383, 0] := by
  rw [show D2M8K2.u7434 = KTree.node D2M8K2.u7426 (nat_lit 15621675) (nat_lit 3654424576) (nat_lit 0) D2M8K2.u7433 from rfl, totK_node, atot7426, atot7433]
  decide +kernel

theorem arows7449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7449 = true := by
  rw [show D2M8K2.u7449 = KTree.node D2M8K2.u7441 (nat_lit 15642490) (nat_lit 3956944184) (nat_lit 0) D2M8K2.u7448 from rfl, allE_node, arows7441, irow7449, arows7448]
  all_goals rfl

theorem atot7449 : totK PD2M8K2 D2M8K2.u7449 = [0, 1649474601595, 5794024891933, 5675525244557, 1390415985863, 60594078068, 0, 0] := by
  rw [show D2M8K2.u7449 = KTree.node D2M8K2.u7441 (nat_lit 15642490) (nat_lit 3956944184) (nat_lit 0) D2M8K2.u7448 from rfl, totK_node, atot7441, atot7448]
  decide +kernel

theorem arows7465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7465 = true := by
  rw [show D2M8K2.u7465 = KTree.node D2M8K2.u7457 (nat_lit 15660542) (nat_lit 2979313159) (nat_lit 0) D2M8K2.u7464 from rfl, allE_node, arows7457, irow7465, arows7464]
  all_goals rfl

theorem atot7465 : totK PD2M8K2 D2M8K2.u7465 = [0, 180187839875, 2636451584244, 6670700648362, 4412152906404, 542746129297, 7634686733, 0] := by
  rw [show D2M8K2.u7465 = KTree.node D2M8K2.u7457 (nat_lit 15660542) (nat_lit 2979313159) (nat_lit 0) D2M8K2.u7464 from rfl, totK_node, atot7457, atot7464]
  decide +kernel

theorem arows7480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7480 = true := by
  rw [show D2M8K2.u7480 = KTree.node D2M8K2.u7472 (nat_lit 15932304) (nat_lit 3736141441) (nat_lit 0) D2M8K2.u7479 from rfl, allE_node, arows7472, irow7480, arows7479]
  all_goals rfl

theorem atot7480 : totK PD2M8K2 D2M8K2.u7480 = [0, 1425350884279, 5035270239760, 5301217006860, 2173926160949, 411765085359, 18014152641, 0] := by
  rw [show D2M8K2.u7480 = KTree.node D2M8K2.u7472 (nat_lit 15932304) (nat_lit 3736141441) (nat_lit 0) D2M8K2.u7479 from rfl, totK_node, atot7472, atot7479]
  decide +kernel

theorem arows7497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7497 = true := by
  rw [show D2M8K2.u7497 = KTree.node D2M8K2.u7489 (nat_lit 15946864) (nat_lit 2745989462) (nat_lit 0) D2M8K2.u7496 from rfl, allE_node, arows7489, irow7497, arows7496]
  all_goals rfl

theorem atot7497 : totK PD2M8K2 D2M8K2.u7497 = [0, 580298837745, 3844840081747, 6687548537119, 2843315440837, 211578023390, 1369150432, 0] := by
  rw [show D2M8K2.u7497 = KTree.node D2M8K2.u7489 (nat_lit 15946864) (nat_lit 2745989462) (nat_lit 0) D2M8K2.u7496 from rfl, totK_node, atot7489, atot7496]
  decide +kernel

theorem arows7512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7512 = true := by
  rw [show D2M8K2.u7512 = KTree.node D2M8K2.u7504 (nat_lit 15973749) (nat_lit 1734059043) (nat_lit 0) D2M8K2.u7511 from rfl, allE_node, arows7504, irow7512, arows7511]
  all_goals rfl

theorem atot7512 : totK PD2M8K2 D2M8K2.u7512 = [0, 1356483584364, 5213662097284, 6015868633157, 1872212615849, 87659341292, 0, 0] := by
  rw [show D2M8K2.u7512 = KTree.node D2M8K2.u7504 (nat_lit 15973749) (nat_lit 1734059043) (nat_lit 0) D2M8K2.u7511 from rfl, totK_node, atot7504, atot7511]
  decide +kernel

theorem arows7528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7528 = true := by
  rw [show D2M8K2.u7528 = KTree.node D2M8K2.u7520 (nat_lit 15991540) (nat_lit 4069852912) (nat_lit 0) D2M8K2.u7527 from rfl, allE_node, arows7520, irow7528, arows7527]
  all_goals rfl

theorem atot7528 : totK PD2M8K2 D2M8K2.u7528 = [0, 672400669610, 3525168083954, 5912340969980, 3643228198357, 726291579330, 29441591382, 0] := by
  rw [show D2M8K2.u7528 = KTree.node D2M8K2.u7520 (nat_lit 15991540) (nat_lit 4069852912) (nat_lit 0) D2M8K2.u7527 from rfl, totK_node, atot7520, atot7527]
  decide +kernel

theorem arows7543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7543 = true := by
  rw [show D2M8K2.u7543 = KTree.node D2M8K2.u7535 (nat_lit 16007100) (nat_lit 3025922233) (nat_lit 0) D2M8K2.u7542 from rfl, allE_node, arows7535, irow7543, arows7542]
  all_goals rfl

theorem atot7543 : totK PD2M8K2 D2M8K2.u7543 = [0, 843193660764, 3819025912300, 5931620909693, 3410163988437, 474867840093, 6925813083, 0] := by
  rw [show D2M8K2.u7543 = KTree.node D2M8K2.u7535 (nat_lit 16007100) (nat_lit 3025922233) (nat_lit 0) D2M8K2.u7542 from rfl, totK_node, atot7535, atot7542]
  decide +kernel

theorem arows7561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7561 = true := by
  rw [show D2M8K2.u7561 = KTree.node D2M8K2.u7553 (nat_lit 16023800) (nat_lit 3682233856) (nat_lit 0) D2M8K2.u7560 from rfl, allE_node, arows7553, irow7561, arows7560]
  all_goals rfl

theorem atot7561 : totK PD2M8K2 D2M8K2.u7561 = [0, 1289813770531, 5238453524722, 6119426150852, 1721295743892, 64323739117, 0, 0] := by
  rw [show D2M8K2.u7561 = KTree.node D2M8K2.u7553 (nat_lit 16023800) (nat_lit 3682233856) (nat_lit 0) D2M8K2.u7560 from rfl, totK_node, atot7553, atot7560]
  decide +kernel

theorem arows7576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7576 = true := by
  rw [show D2M8K2.u7576 = KTree.node D2M8K2.u7568 (nat_lit 16042812) (nat_lit 3236655436) (nat_lit 0) D2M8K2.u7575 from rfl, allE_node, arows7568, irow7576, arows7575]
  all_goals rfl

theorem atot7576 : totK PD2M8K2 D2M8K2.u7576 = [0, 406174846124, 2690528490547, 6065230886875, 4373879255642, 673097151760, 18797058808, 0] := by
  rw [show D2M8K2.u7576 = KTree.node D2M8K2.u7568 (nat_lit 16042812) (nat_lit 3236655436) (nat_lit 0) D2M8K2.u7575 from rfl, totK_node, atot7568, atot7575]
  decide +kernel

theorem arows7592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7592 = true := by
  rw [show D2M8K2.u7592 = KTree.node D2M8K2.u7584 (nat_lit 16099403) (nat_lit 1610666417) (nat_lit 0) D2M8K2.u7591 from rfl, allE_node, arows7584, irow7592, arows7591]
  all_goals rfl

theorem atot7592 : totK PD2M8K2 D2M8K2.u7592 = [0, 1605332320744, 5801454981945, 5655152369179, 1326896979743, 55100561279, 0, 0] := by
  rw [show D2M8K2.u7592 = KTree.node D2M8K2.u7584 (nat_lit 16099403) (nat_lit 1610666417) (nat_lit 0) D2M8K2.u7591 from rfl, totK_node, atot7584, atot7591]
  decide +kernel

theorem arows7607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7607 = true := by
  rw [show D2M8K2.u7607 = KTree.node D2M8K2.u7599 (nat_lit 16119428) (nat_lit 3374714680) (nat_lit 0) D2M8K2.u7606 from rfl, allE_node, arows7599, irow7607, arows7606]
  all_goals rfl

theorem atot7607 : totK PD2M8K2 D2M8K2.u7607 = [0, 252651705119, 2957105249988, 6848524620880, 3768258431408, 374780758149, 6115358396, 0] := by
  rw [show D2M8K2.u7607 = KTree.node D2M8K2.u7599 (nat_lit 16119428) (nat_lit 3374714680) (nat_lit 0) D2M8K2.u7606 from rfl, totK_node, atot7599, atot7606]
  decide +kernel

theorem arows7624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7624 = true := by
  rw [show D2M8K2.u7624 = KTree.node D2M8K2.u7616 (nat_lit 16140114) (nat_lit 2550211321) (nat_lit 0) D2M8K2.u7623 from rfl, allE_node, arows7616, irow7624, arows7623]
  all_goals rfl

theorem atot7624 : totK PD2M8K2 D2M8K2.u7624 = [0, 1675801577782, 5822889269983, 5627630387710, 1347447437461, 55876723884, 0, 0] := by
  rw [show D2M8K2.u7624 = KTree.node D2M8K2.u7616 (nat_lit 16140114) (nat_lit 2550211321) (nat_lit 0) D2M8K2.u7623 from rfl, totK_node, atot7616, atot7623]
  decide +kernel

theorem arows7639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7639 = true := by
  rw [show D2M8K2.u7639 = KTree.node D2M8K2.u7631 (nat_lit 16158128) (nat_lit 3738675224) (nat_lit 0) D2M8K2.u7638 from rfl, allE_node, arows7631, irow7639, arows7638]
  all_goals rfl

theorem atot7639 : totK PD2M8K2 D2M8K2.u7639 = [0, 93763323609, 2691160875963, 6894705470355, 4241031196861, 456535344237, 6190125969, 0] := by
  rw [show D2M8K2.u7639 = KTree.node D2M8K2.u7631 (nat_lit 16158128) (nat_lit 3738675224) (nat_lit 0) D2M8K2.u7638 from rfl, totK_node, atot7631, atot7638]
  decide +kernel

theorem arows7655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7655 = true := by
  rw [show D2M8K2.u7655 = KTree.node D2M8K2.u7647 (nat_lit 16182337) (nat_lit 1407260867) (nat_lit 0) D2M8K2.u7654 from rfl, allE_node, arows7647, irow7655, arows7654]
  all_goals rfl

theorem atot7655 : totK PD2M8K2 D2M8K2.u7655 = [0, 0, 1678603622558, 6122263089059, 5433780508969, 945524441410, 30499950210, 0] := by
  rw [show D2M8K2.u7655 = KTree.node D2M8K2.u7647 (nat_lit 16182337) (nat_lit 1407260867) (nat_lit 0) D2M8K2.u7654 from rfl, totK_node, atot7647, atot7654]
  decide +kernel

theorem arows7670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7670 = true := by
  rw [show D2M8K2.u7670 = KTree.node D2M8K2.u7662 (nat_lit 16198000) (nat_lit 3204291088) (nat_lit 0) D2M8K2.u7669 from rfl, allE_node, arows7662, irow7670, arows7669]
  all_goals rfl

theorem atot7670 : totK PD2M8K2 D2M8K2.u7670 = [0, 0, 506077909534, 3847778854986, 6881199426756, 2653566992710, 192604386134, 1275377855] := by
  rw [show D2M8K2.u7670 = KTree.node D2M8K2.u7662 (nat_lit 16198000) (nat_lit 3204291088) (nat_lit 0) D2M8K2.u7669 from rfl, totK_node, atot7662, atot7669]
  decide +kernel

theorem arows7690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7690 = true := by
  rw [show D2M8K2.u7690 = KTree.node D2M8K2.u7682 (nat_lit 16226278) (nat_lit 3699209951) (nat_lit 0) D2M8K2.u7689 from rfl, allE_node, arows7682, irow7690, arows7689]
  all_goals rfl

theorem atot7690 : totK PD2M8K2 D2M8K2.u7690 = [0, 0, 1927235245099, 6340772840221, 5320157747442, 997588804390, 38281525860, 0] := by
  rw [show D2M8K2.u7690 = KTree.node D2M8K2.u7682 (nat_lit 16226278) (nat_lit 3699209951) (nat_lit 0) D2M8K2.u7689 from rfl, totK_node, atot7682, atot7689]
  decide +kernel

theorem arows7705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7705 = true := by
  rw [show D2M8K2.u7705 = KTree.node D2M8K2.u7697 (nat_lit 16263421) (nat_lit 1155422673) (nat_lit 0) D2M8K2.u7704 from rfl, allE_node, arows7697, irow7705, arows7704]
  all_goals rfl

theorem atot7705 : totK PD2M8K2 D2M8K2.u7705 = [0, 0, 1699439756178, 5934107871871, 5502128687684, 1192650170818, 51104841184, 0] := by
  rw [show D2M8K2.u7705 = KTree.node D2M8K2.u7697 (nat_lit 16263421) (nat_lit 1155422673) (nat_lit 0) D2M8K2.u7704 from rfl, totK_node, atot7697, atot7704]
  decide +kernel

theorem arows7721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7721 = true := by
  rw [show D2M8K2.u7721 = KTree.node D2M8K2.u7713 (nat_lit 16280656) (nat_lit 3297802379) (nat_lit 0) D2M8K2.u7720 from rfl, allE_node, arows7713, irow7721, arows7720]
  all_goals rfl

theorem atot7721 : totK PD2M8K2 D2M8K2.u7721 = [0, 0, 420582282504, 3235385745429, 6448324702449, 3542246375440, 490055135529, 14222663156] := by
  rw [show D2M8K2.u7721 = KTree.node D2M8K2.u7713 (nat_lit 16280656) (nat_lit 3297802379) (nat_lit 0) D2M8K2.u7720 from rfl, totK_node, atot7713, atot7720]
  decide +kernel

theorem arows7736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7736 = true := by
  rw [show D2M8K2.u7736 = KTree.node D2M8K2.u7728 (nat_lit 16343813) (nat_lit 2303445012) (nat_lit 0) D2M8K2.u7735 from rfl, allE_node, arows7728, irow7736, arows7735]
  all_goals rfl

theorem atot7736 : totK PD2M8K2 D2M8K2.u7736 = [0, 0, 1289337982078, 4995045972515, 5706785348528, 1996354495982, 208547430265, 4574395652] := by
  rw [show D2M8K2.u7736 = KTree.node D2M8K2.u7728 (nat_lit 16343813) (nat_lit 2303445012) (nat_lit 0) D2M8K2.u7735 from rfl, totK_node, atot7728, atot7735]
  decide +kernel

theorem arows7753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7753 = true := by
  rw [show D2M8K2.u7753 = KTree.node D2M8K2.u7745 (nat_lit 16361869) (nat_lit 1385917071) (nat_lit 0) D2M8K2.u7752 from rfl, allE_node, arows7745, irow7753, arows7752]
  all_goals rfl

theorem atot7753 : totK PD2M8K2 D2M8K2.u7753 = [0, 0, 710647103964, 4370012333802, 6519946770823, 2287696721792, 152572531167, 1103454931] := by
  rw [show D2M8K2.u7753 = KTree.node D2M8K2.u7745 (nat_lit 16361869) (nat_lit 1385917071) (nat_lit 0) D2M8K2.u7752 from rfl, totK_node, atot7745, atot7752]
  decide +kernel

theorem arows7768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7768 = true := by
  rw [show D2M8K2.u7768 = KTree.node D2M8K2.u7760 (nat_lit 16386392) (nat_lit 2928664041) (nat_lit 0) D2M8K2.u7767 from rfl, allE_node, arows7760, irow7768, arows7767]
  all_goals rfl

theorem atot7768 : totK PD2M8K2 D2M8K2.u7768 = [0, 0, 1659532645333, 5529978605121, 5300741860100, 1659354316474, 187555041181, 4779662215] := by
  rw [show D2M8K2.u7768 = KTree.node D2M8K2.u7760 (nat_lit 16386392) (nat_lit 2928664041) (nat_lit 0) D2M8K2.u7767 from rfl, totK_node, atot7760, atot7767]
  decide +kernel

theorem arows7784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7784 = true := by
  rw [show D2M8K2.u7784 = KTree.node D2M8K2.u7776 (nat_lit 16927682) (nat_lit 3327575100) (nat_lit 0) D2M8K2.u7783 from rfl, allE_node, arows7776, irow7784, arows7783]
  all_goals rfl

theorem atot7784 : totK PD2M8K2 D2M8K2.u7784 = [0, 1333051552145, 4934101525552, 5503827152199, 2242377211320, 360072966176, 13949453364, 0] := by
  rw [show D2M8K2.u7784 = KTree.node D2M8K2.u7776 (nat_lit 16927682) (nat_lit 3327575100) (nat_lit 0) D2M8K2.u7783 from rfl, totK_node, atot7776, atot7783]
  decide +kernel

theorem arows7799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7799 = true := by
  rw [show D2M8K2.u7799 = KTree.node D2M8K2.u7791 (nat_lit 16942404) (nat_lit 3062633191) (nat_lit 0) D2M8K2.u7798 from rfl, allE_node, arows7791, irow7799, arows7798]
  all_goals rfl

theorem atot7799 : totK PD2M8K2 D2M8K2.u7799 = [0, 640803445266, 3925287908893, 6596197788346, 2802904838255, 216507279383, 1369150432, 0] := by
  rw [show D2M8K2.u7799 = KTree.node D2M8K2.u7791 (nat_lit 16942404) (nat_lit 3062633191) (nat_lit 0) D2M8K2.u7798 from rfl, totK_node, atot7791, atot7798]
  decide +kernel

theorem arows7817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7817 = true := by
  rw [show D2M8K2.u7817 = KTree.node D2M8K2.u7809 (nat_lit 16969437) (nat_lit 1403827604) (nat_lit 0) D2M8K2.u7816 from rfl, allE_node, arows7809, irow7817, arows7816]
  all_goals rfl

theorem atot7817 : totK PD2M8K2 D2M8K2.u7817 = [0, 1402624645947, 5287465150444, 5932490257862, 1798970219860, 90554021347, 0, 0] := by
  rw [show D2M8K2.u7817 = KTree.node D2M8K2.u7809 (nat_lit 16969437) (nat_lit 1403827604) (nat_lit 0) D2M8K2.u7816 from rfl, totK_node, atot7809, atot7816]
  decide +kernel

theorem arows7832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7832 = true := by
  rw [show D2M8K2.u7832 = KTree.node D2M8K2.u7824 (nat_lit 16987419) (nat_lit 3766489105) (nat_lit 0) D2M8K2.u7831 from rfl, allE_node, arows7824, irow7832, arows7831]
  all_goals rfl

theorem atot7832 : totK PD2M8K2 D2M8K2.u7832 = [0, 595440974875, 3435963422326, 6118370343605, 3727342268015, 657638864258, 20248977901, 0] := by
  rw [show D2M8K2.u7832 = KTree.node D2M8K2.u7824 (nat_lit 16987419) (nat_lit 3766489105) (nat_lit 0) D2M8K2.u7831 from rfl, totK_node, atot7824, atot7831]
  decide +kernel

theorem arows7848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7848 = true := by
  rw [show D2M8K2.u7848 = KTree.node D2M8K2.u7840 (nat_lit 17004973) (nat_lit 1386666610) (nat_lit 0) D2M8K2.u7847 from rfl, allE_node, arows7840, irow7848, arows7847]
  all_goals rfl

theorem atot7848 : totK PD2M8K2 D2M8K2.u7848 = [0, 1130337466147, 4509826966491, 5895056223704, 2722371463608, 267037155873, 1415142070, 0] := by
  rw [show D2M8K2.u7848 = KTree.node D2M8K2.u7840 (nat_lit 17004973) (nat_lit 1386666610) (nat_lit 0) D2M8K2.u7847 from rfl, totK_node, atot7840, atot7847]
  decide +kernel

theorem arows7863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7863 = true := by
  rw [show D2M8K2.u7863 = KTree.node D2M8K2.u7855 (nat_lit 17021642) (nat_lit 4001677110) (nat_lit 0) D2M8K2.u7862 from rfl, allE_node, arows7855, irow7863, arows7862]
  all_goals rfl

theorem atot7863 : totK PD2M8K2 D2M8K2.u7863 = [0, 906120606674, 4446852428706, 6341746776541, 2488122098566, 194020781418, 1206465782, 0] := by
  rw [show D2M8K2.u7863 = KTree.node D2M8K2.u7855 (nat_lit 17021642) (nat_lit 4001677110) (nat_lit 0) D2M8K2.u7862 from rfl, totK_node, atot7855, atot7862]
  decide +kernel

theorem arows7880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7880 = true := by
  rw [show D2M8K2.u7880 = KTree.node D2M8K2.u7872 (nat_lit 17041728) (nat_lit 3564380604) (nat_lit 0) D2M8K2.u7879 from rfl, allE_node, arows7872, irow7880, arows7879]
  all_goals rfl

theorem atot7880 : totK PD2M8K2 D2M8K2.u7880 = [0, 802680951956, 3729798226255, 5890754108854, 3353655405925, 526970491015, 17590593026, 0] := by
  rw [show D2M8K2.u7880 = KTree.node D2M8K2.u7872 (nat_lit 17041728) (nat_lit 3564380604) (nat_lit 0) D2M8K2.u7879 from rfl, totK_node, atot7872, atot7879]
  decide +kernel

theorem arows7895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7895 = true := by
  rw [show D2M8K2.u7895 = KTree.node D2M8K2.u7887 (nat_lit 17060740) (nat_lit 3745079207) (nat_lit 0) D2M8K2.u7894 from rfl, allE_node, arows7887, irow7895, arows7894]
  all_goals rfl

theorem atot7895 : totK PD2M8K2 D2M8K2.u7895 = [0, 849262933305, 4335069311418, 6463483870453, 2548461707028, 168432143439, 1239866073, 0] := by
  rw [show D2M8K2.u7895 = KTree.node D2M8K2.u7887 (nat_lit 17060740) (nat_lit 3745079207) (nat_lit 0) D2M8K2.u7894 from rfl, totK_node, atot7887, atot7894]
  decide +kernel

theorem arows7911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7911 = true := by
  rw [show D2M8K2.u7911 = KTree.node D2M8K2.u7903 (nat_lit 17089374) (nat_lit 3684030413) (nat_lit 0) D2M8K2.u7910 from rfl, allE_node, arows7903, irow7911, arows7910]
  all_goals rfl

theorem atot7911 : totK PD2M8K2 D2M8K2.u7911 = [0, 1256885138224, 4779032519733, 5721184160790, 2301920198191, 233886780151, 4720618446, 0] := by
  rw [show D2M8K2.u7911 = KTree.node D2M8K2.u7903 (nat_lit 17089374) (nat_lit 3684030413) (nat_lit 0) D2M8K2.u7910 from rfl, totK_node, atot7903, atot7910]
  decide +kernel

theorem arows7926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7926 = true := by
  rw [show D2M8K2.u7926 = KTree.node D2M8K2.u7918 (nat_lit 17102264) (nat_lit 3823380090) (nat_lit 0) D2M8K2.u7925 from rfl, allE_node, arows7918, irow7926, arows7925]
  all_goals rfl

theorem atot7926 : totK PD2M8K2 D2M8K2.u7926 = [0, 845448351338, 4302087027246, 6420345287912, 2522527200876, 192653565734, 1138244013, 0] := by
  rw [show D2M8K2.u7926 = KTree.node D2M8K2.u7918 (nat_lit 17102264) (nat_lit 3823380090) (nat_lit 0) D2M8K2.u7925 from rfl, totK_node, atot7918, atot7925]
  decide +kernel

theorem arows7945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7945 = true := by
  rw [show D2M8K2.u7945 = KTree.node D2M8K2.u7937 (nat_lit 17170108) (nat_lit 3930662508) (nat_lit 0) D2M8K2.u7944 from rfl, allE_node, arows7937, irow7945, arows7944]
  all_goals rfl

theorem atot7945 : totK PD2M8K2 D2M8K2.u7945 = [0, 0, 2114845564817, 6543309810419, 4818338017777, 719964585554, 19329714611, 0] := by
  rw [show D2M8K2.u7945 = KTree.node D2M8K2.u7937 (nat_lit 17170108) (nat_lit 3930662508) (nat_lit 0) D2M8K2.u7944 from rfl, totK_node, atot7937, atot7944]
  decide +kernel

theorem arows7960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7960 = true := by
  rw [show D2M8K2.u7960 = KTree.node D2M8K2.u7952 (nat_lit 17188612) (nat_lit 3925108956) (nat_lit 0) D2M8K2.u7959 from rfl, allE_node, arows7952, irow7960, arows7959]
  all_goals rfl

theorem atot7960 : totK PD2M8K2 D2M8K2.u7960 = [0, 0, 892524332014, 4845141647070, 6342539606404, 1833094461126, 110940001447, 1209030869] := by
  rw [show D2M8K2.u7960 = KTree.node D2M8K2.u7952 (nat_lit 17188612) (nat_lit 3925108956) (nat_lit 0) D2M8K2.u7959 from rfl, totK_node, atot7952, atot7959]
  decide +kernel

theorem arows7976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7976 = true := by
  rw [show D2M8K2.u7976 = KTree.node D2M8K2.u7968 (nat_lit 17219004) (nat_lit 3113581972) (nat_lit 0) D2M8K2.u7975 from rfl, allE_node, arows7968, irow7976, arows7975]
  all_goals rfl

theorem atot7976 : totK PD2M8K2 D2M8K2.u7976 = [0, 0, 1746232340101, 6015794248857, 5603254099206, 1156220636630, 42546298739, 0] := by
  rw [show D2M8K2.u7976 = KTree.node D2M8K2.u7968 (nat_lit 17219004) (nat_lit 3113581972) (nat_lit 0) D2M8K2.u7975 from rfl, totK_node, atot7968, atot7975]
  decide +kernel

theorem arows7991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7991 = true := by
  rw [show D2M8K2.u7991 = KTree.node D2M8K2.u7983 (nat_lit 17258380) (nat_lit 3874081756) (nat_lit 0) D2M8K2.u7990 from rfl, allE_node, arows7983, irow7991, arows7990]
  all_goals rfl

theorem atot7991 : totK PD2M8K2 D2M8K2.u7991 = [0, 0, 1918872349634, 6282950532422, 5264231690931, 944733008289, 30470388548, 0] := by
  rw [show D2M8K2.u7991 = KTree.node D2M8K2.u7983 (nat_lit 17258380) (nat_lit 3874081756) (nat_lit 0) D2M8K2.u7990 from rfl, totK_node, atot7983, atot7990]
  decide +kernel

theorem arows8008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8008 = true := by
  rw [show D2M8K2.u8008 = KTree.node D2M8K2.u8000 (nat_lit 17297925) (nat_lit 1241669168) (nat_lit 2) D2M8K2.u8007 from rfl, allE_node, arows8000, irow8008, arows8007]
  all_goals rfl

theorem atot8008 : totK PD2M8K2 D2M8K2.u8008 = [0, 0, 2159836455866, 6669308304879, 4875326435104, 675226762453, 15055937158, 0] := by
  rw [show D2M8K2.u8008 = KTree.node D2M8K2.u8000 (nat_lit 17297925) (nat_lit 1241669168) (nat_lit 2) D2M8K2.u8007 from rfl, totK_node, atot8000, atot8007]
  decide +kernel

theorem arows8023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8023 = true := by
  rw [show D2M8K2.u8023 = KTree.node D2M8K2.u8015 (nat_lit 17342946) (nat_lit 1439148997) (nat_lit 0) D2M8K2.u8022 from rfl, allE_node, arows8015, irow8023, arows8022]
  all_goals rfl

theorem atot8023 : totK PD2M8K2 D2M8K2.u8023 = [0, 0, 1808861928787, 6103891656037, 5312950384527, 978995146363, 34015997121, 0] := by
  rw [show D2M8K2.u8023 = KTree.node D2M8K2.u8015 (nat_lit 17342946) (nat_lit 1439148997) (nat_lit 0) D2M8K2.u8022 from rfl, totK_node, atot8015, atot8022]
  decide +kernel

theorem arows8039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8039 = true := by
  rw [show D2M8K2.u8039 = KTree.node D2M8K2.u8031 (nat_lit 17363472) (nat_lit 2614093090) (nat_lit 0) D2M8K2.u8038 from rfl, allE_node, arows8031, irow8039, arows8038]
  all_goals rfl

theorem atot8039 : totK PD2M8K2 D2M8K2.u8039 = [0, 344808557977, 874936881643, 3119191983643, 6352106360220, 3022020996278, 312110578983, 6115358396] := by
  rw [show D2M8K2.u8039 = KTree.node D2M8K2.u8031 (nat_lit 17363472) (nat_lit 2614093090) (nat_lit 0) D2M8K2.u8038 from rfl, totK_node, atot8031, atot8038]
  decide +kernel

theorem arows8054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8054 = true := by
  rw [show D2M8K2.u8054 = KTree.node D2M8K2.u8046 (nat_lit 17430098) (nat_lit 3366414338) (nat_lit 0) D2M8K2.u8053 from rfl, allE_node, arows8046, irow8054, arows8053]
  all_goals rfl

theorem atot8054 : totK PD2M8K2 D2M8K2.u8054 = [0, 1633795699139, 5993966754838, 5628179668614, 1076705426880, 26123779468, 0, 0] := by
  rw [show D2M8K2.u8054 = KTree.node D2M8K2.u8046 (nat_lit 17430098) (nat_lit 3366414338) (nat_lit 0) D2M8K2.u8053 from rfl, totK_node, atot8046, atot8053]
  decide +kernel

theorem arows8072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8072 = true := by
  rw [show D2M8K2.u8072 = KTree.node D2M8K2.u8064 (nat_lit 17450218) (nat_lit 3891519254) (nat_lit 0) D2M8K2.u8071 from rfl, allE_node, arows8064, irow8072, arows8071]
  all_goals rfl

theorem atot8072 : totK PD2M8K2 D2M8K2.u8072 = [0, 442886995791, 3433274800631, 6837577009943, 3291779427389, 257717877756, 1369150432, 0] := by
  rw [show D2M8K2.u8072 = KTree.node D2M8K2.u8064 (nat_lit 17450218) (nat_lit 3891519254) (nat_lit 0) D2M8K2.u8071 from rfl, totK_node, atot8064, atot8071]
  decide +kernel

theorem arows8087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8087 = true := by
  rw [show D2M8K2.u8087 = KTree.node D2M8K2.u8079 (nat_lit 17471641) (nat_lit 1477434269) (nat_lit 0) D2M8K2.u8086 from rfl, allE_node, arows8079, irow8087, arows8086]
  all_goals rfl

theorem atot8087 : totK PD2M8K2 D2M8K2.u8087 = [0, 1560611709891, 5695320588179, 5811113501094, 1470873083208, 63313237103, 0, 0] := by
  rw [show D2M8K2.u8087 = KTree.node D2M8K2.u8079 (nat_lit 17471641) (nat_lit 1477434269) (nat_lit 0) D2M8K2.u8086 from rfl, totK_node, atot8079, atot8086]
  decide +kernel

theorem arows8103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8103 = true := by
  rw [show D2M8K2.u8103 = KTree.node D2M8K2.u8095 (nat_lit 17488884) (nat_lit 2495343493) (nat_lit 0) D2M8K2.u8102 from rfl, allE_node, arows8095, irow8103, arows8102]
  all_goals rfl

theorem atot8103 : totK PD2M8K2 D2M8K2.u8103 = [0, 0, 1786080078750, 6168888619189, 5449335433127, 1107345580154, 39732786462, 0] := by
  rw [show D2M8K2.u8103 = KTree.node D2M8K2.u8095 (nat_lit 17488884) (nat_lit 2495343493) (nat_lit 0) D2M8K2.u8102 from rfl, totK_node, atot8095, atot8102]
  decide +kernel

theorem arows8118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8118 = true := by
  rw [show D2M8K2.u8118 = KTree.node D2M8K2.u8110 (nat_lit 17505066) (nat_lit 3731193238) (nat_lit 0) D2M8K2.u8117 from rfl, allE_node, arows8110, irow8118, arows8117]
  all_goals rfl

theorem atot8118 : totK PD2M8K2 D2M8K2.u8118 = [0, 1268633329011, 4792747643260, 5616570439082, 2429946629811, 372420630152, 10717512769, 0] := by
  rw [show D2M8K2.u8118 = KTree.node D2M8K2.u8110 (nat_lit 17505066) (nat_lit 3731193238) (nat_lit 0) D2M8K2.u8117 from rfl, totK_node, atot8110, atot8117]
  decide +kernel

theorem arows8135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8135 = true := by
  rw [show D2M8K2.u8135 = KTree.node D2M8K2.u8127 (nat_lit 17521780) (nat_lit 3507837981) (nat_lit 0) D2M8K2.u8134 from rfl, allE_node, arows8127, irow8135, arows8134]
  all_goals rfl

theorem atot8135 : totK PD2M8K2 D2M8K2.u8135 = [0, 771091638455, 4121071523407, 6490944814200, 2791265507866, 221571858809, 1206465782, 0] := by
  rw [show D2M8K2.u8135 = KTree.node D2M8K2.u8127 (nat_lit 17521780) (nat_lit 3507837981) (nat_lit 0) D2M8K2.u8134 from rfl, totK_node, atot8127, atot8134]
  decide +kernel

theorem arows8150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8150 = true := by
  rw [show D2M8K2.u8150 = KTree.node D2M8K2.u8142 (nat_lit 17544144) (nat_lit 3514992200) (nat_lit 0) D2M8K2.u8149 from rfl, allE_node, arows8142, irow8150, arows8149]
  all_goals rfl

theorem atot8150 : totK PD2M8K2 D2M8K2.u8150 = [0, 1141755840040, 4475060328749, 5741268281248, 2672514703182, 380309023983, 13016197374, 0] := by
  rw [show D2M8K2.u8150 = KTree.node D2M8K2.u8142 (nat_lit 17544144) (nat_lit 3514992200) (nat_lit 0) D2M8K2.u8149 from rfl, totK_node, atot8142, atot8149]
  decide +kernel

theorem arows8166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8166 = true := by
  rw [show D2M8K2.u8166 = KTree.node D2M8K2.u8158 (nat_lit 17564481) (nat_lit 1773166599) (nat_lit 0) D2M8K2.u8165 from rfl, allE_node, arows8158, irow8166, arows8165]
  all_goals rfl

theorem atot8166 : totK PD2M8K2 D2M8K2.u8166 = [0, 516265476472, 3436847510076, 6510233304994, 3516686049388, 375782670738, 6665697270, 0] := by
  rw [show D2M8K2.u8166 = KTree.node D2M8K2.u8158 (nat_lit 17564481) (nat_lit 1773166599) (nat_lit 0) D2M8K2.u8165 from rfl, totK_node, atot8158, atot8165]
  decide +kernel

theorem arows8181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8181 = true := by
  rw [show D2M8K2.u8181 = KTree.node D2M8K2.u8173 (nat_lit 17630387) (nat_lit 2076161299) (nat_lit 0) D2M8K2.u8180 from rfl, allE_node, arows8173, irow8181, arows8180]
  all_goals rfl

theorem atot8181 : totK PD2M8K2 D2M8K2.u8181 = [0, 1432018244124, 5350791662797, 5795933510170, 1776542244809, 105318886958, 0, 0] := by
  rw [show D2M8K2.u8181 = KTree.node D2M8K2.u8173 (nat_lit 17630387) (nat_lit 2076161299) (nat_lit 0) D2M8K2.u8180 from rfl, totK_node, atot8173, atot8180]
  decide +kernel

theorem arows8205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8205 = true := by
  rw [show D2M8K2.u8205 = KTree.node D2M8K2.u8197 (nat_lit 17646583) (nat_lit 1832058094) (nat_lit 512) D2M8K2.u8204 from rfl, allE_node, arows8197, irow8205, arows8204]
  all_goals rfl

theorem atot8205 : totK PD2M8K2 D2M8K2.u8205 = [0, 679887205274, 3845194324533, 6479753874830, 3136835921857, 261240182790, 1310285577, 0] := by
  rw [show D2M8K2.u8205 = KTree.node D2M8K2.u8197 (nat_lit 17646583) (nat_lit 1832058094) (nat_lit 512) D2M8K2.u8204 from rfl, totK_node, atot8197, atot8204]
  decide +kernel

theorem arows8220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8220 = true := by
  rw [show D2M8K2.u8220 = KTree.node D2M8K2.u8212 (nat_lit 17665734) (nat_lit 3505825553) (nat_lit 0) D2M8K2.u8219 from rfl, allE_node, arows8212, irow8220, arows8219]
  all_goals rfl

theorem atot8220 : totK PD2M8K2 D2M8K2.u8220 = [842186864805, 2693244393491, 2933273724974, 3618816450556, 3420215934803, 776273311324, 31562413104, 0] := by
  rw [show D2M8K2.u8220 = KTree.node D2M8K2.u8212 (nat_lit 17665734) (nat_lit 3505825553) (nat_lit 0) D2M8K2.u8219 from rfl, totK_node, atot8212, atot8219]
  decide +kernel

theorem arows8236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8236 = true := by
  rw [show D2M8K2.u8236 = KTree.node D2M8K2.u8228 (nat_lit 17931600) (nat_lit 3700418224) (nat_lit 0) D2M8K2.u8235 from rfl, allE_node, arows8228, irow8236, arows8235]
  all_goals rfl

theorem atot8236 : totK PD2M8K2 D2M8K2.u8236 = [1254830561438, 5180094998327, 6064230615912, 1701152139181, 75244342264, 0, 0, 0] := by
  rw [show D2M8K2.u8236 = KTree.node D2M8K2.u8228 (nat_lit 17931600) (nat_lit 3700418224) (nat_lit 0) D2M8K2.u8235 from rfl, totK_node, atot8228, atot8235]
  decide +kernel

theorem arows8251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8251 = true := by
  rw [show D2M8K2.u8251 = KTree.node D2M8K2.u8243 (nat_lit 17951765) (nat_lit 2194618788) (nat_lit 0) D2M8K2.u8250 from rfl, allE_node, arows8243, irow8251, arows8250]
  all_goals rfl

theorem atot8251 : totK PD2M8K2 D2M8K2.u8251 = [759475109194, 3992559376788, 6345185816491, 2906448572363, 249199459107, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8251 = KTree.node D2M8K2.u8243 (nat_lit 17951765) (nat_lit 2194618788) (nat_lit 0) D2M8K2.u8250 from rfl, totK_node, atot8243, atot8250]
  decide +kernel

theorem arows8268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8268 = true := by
  rw [show D2M8K2.u8268 = KTree.node D2M8K2.u8260 (nat_lit 18017633) (nat_lit 2207073867) (nat_lit 0) D2M8K2.u8267 from rfl, allE_node, arows8260, irow8268, arows8267]
  all_goals rfl

theorem atot8268 : totK PD2M8K2 D2M8K2.u8268 = [888676620544, 4346925129162, 6336189435508, 2520223654424, 188555931907, 1206465782, 0, 0] := by
  rw [show D2M8K2.u8268 = KTree.node D2M8K2.u8260 (nat_lit 18017633) (nat_lit 2207073867) (nat_lit 0) D2M8K2.u8267 from rfl, totK_node, atot8260, atot8267]
  decide +kernel

theorem arows8283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8283 = true := by
  rw [show D2M8K2.u8283 = KTree.node D2M8K2.u8275 (nat_lit 18040432) (nat_lit 3275640970) (nat_lit 0) D2M8K2.u8282 from rfl, allE_node, arows8275, irow8283, arows8282]
  all_goals rfl

theorem atot8283 : totK PD2M8K2 D2M8K2.u8283 = [937309973630, 3867257274936, 5672932096332, 3296907331814, 533415093246, 17590593026, 0, 0] := by
  rw [show D2M8K2.u8283 = KTree.node D2M8K2.u8275 (nat_lit 18040432) (nat_lit 3275640970) (nat_lit 0) D2M8K2.u8282 from rfl, totK_node, atot8275, atot8282]
  decide +kernel

theorem arows8299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8299 = true := by
  rw [show D2M8K2.u8299 = KTree.node D2M8K2.u8291 (nat_lit 18057949) (nat_lit 884821004) (nat_lit 0) D2M8K2.u8298 from rfl, allE_node, arows8291, irow8299, arows8298]
  all_goals rfl

theorem atot8299 : totK PD2M8K2 D2M8K2.u8299 = [1097552001031, 4711068540718, 6078465365923, 2323522998275, 185379036328, 1239866073, 0, 0] := by
  rw [show D2M8K2.u8299 = KTree.node D2M8K2.u8291 (nat_lit 18057949) (nat_lit 884821004) (nat_lit 0) D2M8K2.u8298 from rfl, totK_node, atot8291, atot8298]
  decide +kernel

theorem arows8314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8314 = true := by
  rw [show D2M8K2.u8314 = KTree.node D2M8K2.u8306 (nat_lit 18076804) (nat_lit 3349328130) (nat_lit 0) D2M8K2.u8313 from rfl, allE_node, arows8306, irow8314, arows8313]
  all_goals rfl

theorem atot8314 : totK PD2M8K2 D2M8K2.u8314 = [576001265953, 3314779310251, 6106350483263, 3731161932956, 571004178927, 17826068843, 0, 0] := by
  rw [show D2M8K2.u8314 = KTree.node D2M8K2.u8306 (nat_lit 18076804) (nat_lit 3349328130) (nat_lit 0) D2M8K2.u8313 from rfl, totK_node, atot8306, atot8313]
  decide +kernel

theorem arows8332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8332 = true := by
  rw [show D2M8K2.u8332 = KTree.node D2M8K2.u8324 (nat_lit 18093265) (nat_lit 1405126266) (nat_lit 0) D2M8K2.u8331 from rfl, allE_node, arows8324, irow8332, arows8331]
  all_goals rfl

theorem atot8332 : totK PD2M8K2 D2M8K2.u8332 = [1401911212590, 5437659876000, 5883359625360, 1569994619622, 72906104184, 0, 0, 0] := by
  rw [show D2M8K2.u8332 = KTree.node D2M8K2.u8324 (nat_lit 18093265) (nat_lit 1405126266) (nat_lit 0) D2M8K2.u8331 from rfl, totK_node, atot8324, atot8331]
  decide +kernel

theorem arows8347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8347 = true := by
  rw [show D2M8K2.u8347 = KTree.node D2M8K2.u8339 (nat_lit 18114371) (nat_lit 2811277729) (nat_lit 0) D2M8K2.u8346 from rfl, allE_node, arows8339, irow8347, arows8346]
  all_goals rfl

theorem atot8347 : totK PD2M8K2 D2M8K2.u8347 = [439315660877, 3206290921835, 6505199419324, 3666390442272, 420049724689, 6115358396, 0, 0] := by
  rw [show D2M8K2.u8347 = KTree.node D2M8K2.u8339 (nat_lit 18114371) (nat_lit 2811277729) (nat_lit 0) D2M8K2.u8346 from rfl, totK_node, atot8339, atot8346]
  decide +kernel

theorem arows8363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8363 = true := by
  rw [show D2M8K2.u8363 = KTree.node D2M8K2.u8355 (nat_lit 18133990) (nat_lit 3721287516) (nat_lit 0) D2M8K2.u8362 from rfl, allE_node, arows8355, irow8363, arows8362]
  all_goals rfl

theorem atot8363 : totK PD2M8K2 D2M8K2.u8363 = [1549751495390, 5581458429664, 5741918623609, 1549773159251, 72095655603, 0, 0, 0] := by
  rw [show D2M8K2.u8363 = KTree.node D2M8K2.u8355 (nat_lit 18133990) (nat_lit 3721287516) (nat_lit 0) D2M8K2.u8362 from rfl, totK_node, atot8355, atot8362]
  decide +kernel

theorem arows8378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8378 = true := by
  rw [show D2M8K2.u8378 = KTree.node D2M8K2.u8370 (nat_lit 18152777) (nat_lit 1565893680) (nat_lit 0) D2M8K2.u8377 from rfl, allE_node, arows8370, irow8378, arows8377]
  all_goals rfl

theorem atot8378 : totK PD2M8K2 D2M8K2.u8378 = [0, 1982147157957, 6449701880411, 5147322301238, 739581734232, 12363669215, 0, 0] := by
  rw [show D2M8K2.u8378 = KTree.node D2M8K2.u8370 (nat_lit 18152777) (nat_lit 1565893680) (nat_lit 0) D2M8K2.u8377 from rfl, totK_node, atot8370, atot8377]
  decide +kernel

theorem arows8395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8395 = true := by
  rw [show D2M8K2.u8395 = KTree.node D2M8K2.u8387 (nat_lit 18173772) (nat_lit 2434694499) (nat_lit 0) D2M8K2.u8394 from rfl, allE_node, arows8387, irow8395, arows8394]
  all_goals rfl

theorem atot8395 : totK PD2M8K2 D2M8K2.u8395 = [0, 1669885235143, 5862309337627, 5484949988464, 1143140565714, 48958722816, 0, 0] := by
  rw [show D2M8K2.u8395 = KTree.node D2M8K2.u8387 (nat_lit 18173772) (nat_lit 2434694499) (nat_lit 0) D2M8K2.u8394 from rfl, totK_node, atot8387, atot8394]
  decide +kernel

theorem arows8410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8410 = true := by
  rw [show D2M8K2.u8410 = KTree.node D2M8K2.u8402 (nat_lit 18187280) (nat_lit 3549448492) (nat_lit 0) D2M8K2.u8409 from rfl, allE_node, arows8402, irow8410, arows8409]
  all_goals rfl

theorem atot8410 : totK PD2M8K2 D2M8K2.u8410 = [0, 417516665105, 3626135991462, 6871328416627, 2878986328116, 257677705735, 1369150432, 0] := by
  rw [show D2M8K2.u8410 = KTree.node D2M8K2.u8402 (nat_lit 18187280) (nat_lit 3549448492) (nat_lit 0) D2M8K2.u8409 from rfl, totK_node, atot8402, atot8409]
  decide +kernel

theorem arows8426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8426 = true := by
  rw [show D2M8K2.u8426 = KTree.node D2M8K2.u8418 (nat_lit 18256731) (nat_lit 3684992843) (nat_lit 0) D2M8K2.u8425 from rfl, allE_node, arows8418, irow8426, arows8425]
  all_goals rfl

theorem atot8426 : totK PD2M8K2 D2M8K2.u8426 = [0, 1643381371285, 5880927836748, 5589231824796, 1151170315565, 41623858916, 0, 0] := by
  rw [show D2M8K2.u8426 = KTree.node D2M8K2.u8418 (nat_lit 18256731) (nat_lit 3684992843) (nat_lit 0) D2M8K2.u8425 from rfl, totK_node, atot8418, atot8425]
  decide +kernel

theorem arows8441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8441 = true := by
  rw [show D2M8K2.u8441 = KTree.node D2M8K2.u8433 (nat_lit 18295919) (nat_lit 2777346994) (nat_lit 0) D2M8K2.u8440 from rfl, allE_node, arows8433, irow8441, arows8440]
  all_goals rfl

theorem atot8441 : totK PD2M8K2 D2M8K2.u8441 = [0, 1615487347652, 5908616056987, 5741658637225, 1145021136413, 34506455890, 0, 0] := by
  rw [show D2M8K2.u8441 = KTree.node D2M8K2.u8433 (nat_lit 18295919) (nat_lit 2777346994) (nat_lit 0) D2M8K2.u8440 from rfl, totK_node, atot8433, atot8440]
  decide +kernel

theorem arows8460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8460 = true := by
  rw [show D2M8K2.u8460 = KTree.node D2M8K2.u8452 (nat_lit 18334419) (nat_lit 3716614309) (nat_lit 0) D2M8K2.u8459 from rfl, allE_node, arows8452, irow8460, arows8459]
  all_goals rfl

theorem atot8460 : totK PD2M8K2 D2M8K2.u8460 = [0, 1796840919348, 6067354746895, 5438935398677, 1041424125859, 32228593784, 0, 0] := by
  rw [show D2M8K2.u8460 = KTree.node D2M8K2.u8452 (nat_lit 18334419) (nat_lit 3716614309) (nat_lit 0) D2M8K2.u8459 from rfl, totK_node, atot8452, atot8459]
  decide +kernel

theorem arows8475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8475 = true := by
  rw [show D2M8K2.u8475 = KTree.node D2M8K2.u8467 (nat_lit 18373122) (nat_lit 3308958700) (nat_lit 0) D2M8K2.u8474 from rfl, allE_node, arows8467, irow8475, arows8474]
  all_goals rfl

theorem atot8475 : totK PD2M8K2 D2M8K2.u8475 = [0, 1723659727833, 6041763223148, 5570659619069, 1058707358807, 29109610414, 0, 0] := by
  rw [show D2M8K2.u8475 = KTree.node D2M8K2.u8467 (nat_lit 18373122) (nat_lit 3308958700) (nat_lit 0) D2M8K2.u8474 from rfl, totK_node, atot8467, atot8474]
  decide +kernel

theorem arows8491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8491 = true := by
  rw [show D2M8K2.u8491 = KTree.node D2M8K2.u8483 (nat_lit 18391216) (nat_lit 2999372223) (nat_lit 0) D2M8K2.u8490 from rfl, allE_node, arows8483, irow8491, arows8490]
  all_goals rfl

theorem atot8491 : totK PD2M8K2 D2M8K2.u8491 = [682467312879, 3019809550819, 5491733144326, 4402606976578, 925272093689, 32229130377, 0, 0] := by
  rw [show D2M8K2.u8491 = KTree.node D2M8K2.u8483 (nat_lit 18391216) (nat_lit 2999372223) (nat_lit 0) D2M8K2.u8490 from rfl, totK_node, atot8483, atot8490]
  decide +kernel

theorem arows8506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8506 = true := by
  rw [show D2M8K2.u8506 = KTree.node D2M8K2.u8498 (nat_lit 18469550) (nat_lit 3801943950) (nat_lit 0) D2M8K2.u8505 from rfl, allE_node, arows8498, irow8506, arows8505]
  all_goals rfl

theorem atot8506 : totK PD2M8K2 D2M8K2.u8506 = [1435267010713, 5547519951984, 5879066846805, 1496824767303, 73729059226, 0, 0, 0] := by
  rw [show D2M8K2.u8506 = KTree.node D2M8K2.u8498 (nat_lit 18469550) (nat_lit 3801943950) (nat_lit 0) D2M8K2.u8505 from rfl, totK_node, atot8498, atot8505]
  decide +kernel

theorem arows8523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8523 = true := by
  rw [show D2M8K2.u8523 = KTree.node D2M8K2.u8515 (nat_lit 18486286) (nat_lit 3901049706) (nat_lit 0) D2M8K2.u8522 from rfl, allE_node, arows8515, irow8523, arows8522]
  all_goals rfl

theorem atot8523 : totK PD2M8K2 D2M8K2.u8523 = [0, 1669399761188, 5928159215186, 5556885527902, 1229207287244, 48715757244, 0, 0] := by
  rw [show D2M8K2.u8523 = KTree.node D2M8K2.u8515 (nat_lit 18486286) (nat_lit 3901049706) (nat_lit 0) D2M8K2.u8522 from rfl, totK_node, atot8515, atot8522]
  decide +kernel

theorem arows8538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8538 = true := by
  rw [show D2M8K2.u8538 = KTree.node D2M8K2.u8530 (nat_lit 18503280) (nat_lit 2774806457) (nat_lit 0) D2M8K2.u8537 from rfl, allE_node, arows8530, irow8538, arows8537]
  all_goals rfl

theorem atot8538 : totK PD2M8K2 D2M8K2.u8538 = [1256250740985, 4734833304077, 5626249473947, 2476762246359, 373229440530, 9302370699, 0, 0] := by
  rw [show D2M8K2.u8538 = KTree.node D2M8K2.u8530 (nat_lit 18503280) (nat_lit 2774806457) (nat_lit 0) D2M8K2.u8537 from rfl, totK_node, atot8530, atot8537]
  decide +kernel

theorem arows8554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8554 = true := by
  rw [show D2M8K2.u8554 = KTree.node D2M8K2.u8546 (nat_lit 18524942) (nat_lit 3067749570) (nat_lit 0) D2M8K2.u8553 from rfl, allE_node, arows8546, irow8554, arows8553]
  all_goals rfl

theorem atot8554 : totK PD2M8K2 D2M8K2.u8554 = [405776974296, 3014998644439, 6366347549791, 3958995370847, 579419906856, 17590593026, 0, 0] := by
  rw [show D2M8K2.u8554 = KTree.node D2M8K2.u8546 (nat_lit 18524942) (nat_lit 3067749570) (nat_lit 0) D2M8K2.u8553 from rfl, totK_node, atot8546, atot8553]
  decide +kernel

theorem arows8569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8569 = true := by
  rw [show D2M8K2.u8569 = KTree.node D2M8K2.u8561 (nat_lit 18544678) (nat_lit 3815620521) (nat_lit 0) D2M8K2.u8568 from rfl, allE_node, arows8561, irow8569, arows8568]
  all_goals rfl

theorem atot8569 : totK PD2M8K2 D2M8K2.u8569 = [1625578240171, 5781024990490, 5658787519809, 1421137670112, 66864050511, 0, 0, 0] := by
  rw [show D2M8K2.u8569 = KTree.node D2M8K2.u8561 (nat_lit 18544678) (nat_lit 3815620521) (nat_lit 0) D2M8K2.u8568 from rfl, totK_node, atot8561, atot8568]
  decide +kernel

theorem arows8587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8587 = true := by
  rw [show D2M8K2.u8587 = KTree.node D2M8K2.u8579 (nat_lit 18562598) (nat_lit 4060571057) (nat_lit 0) D2M8K2.u8586 from rfl, allE_node, arows8579, irow8587, arows8586]
  all_goals rfl

theorem atot8587 : totK PD2M8K2 D2M8K2.u8587 = [417183842111, 3106697864603, 6431464656940, 3896145158067, 530781648796, 14345316470, 0, 0] := by
  rw [show D2M8K2.u8587 = KTree.node D2M8K2.u8579 (nat_lit 18562598) (nat_lit 4060571057) (nat_lit 0) D2M8K2.u8586 from rfl, totK_node, atot8579, atot8586]
  decide +kernel

theorem arows8602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8602 = true := by
  rw [show D2M8K2.u8602 = KTree.node D2M8K2.u8594 (nat_lit 18583637) (nat_lit 2297038368) (nat_lit 0) D2M8K2.u8601 from rfl, allE_node, arows8594, irow8602, arows8601]
  all_goals rfl

theorem atot8602 : totK PD2M8K2 D2M8K2.u8602 = [1213366772640, 4678016746881, 5751562289206, 2458990403697, 259441814943, 4720618446, 0, 0] := by
  rw [show D2M8K2.u8602 = KTree.node D2M8K2.u8594 (nat_lit 18583637) (nat_lit 2297038368) (nat_lit 0) D2M8K2.u8601 from rfl, totK_node, atot8594, atot8601]
  decide +kernel

theorem arows8618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8618 = true := by
  rw [show D2M8K2.u8618 = KTree.node D2M8K2.u8610 (nat_lit 18600278) (nat_lit 2838136929) (nat_lit 0) D2M8K2.u8617 from rfl, allE_node, arows8610, irow8618, arows8617]
  all_goals rfl

theorem atot8618 : totK PD2M8K2 D2M8K2.u8618 = [774117690643, 4201944925776, 6479707444610, 2721670587333, 210136293603, 1138244013, 0, 0] := by
  rw [show D2M8K2.u8618 = KTree.node D2M8K2.u8610 (nat_lit 18600278) (nat_lit 2838136929) (nat_lit 0) D2M8K2.u8617 from rfl, totK_node, atot8610, atot8617]
  decide +kernel

theorem arows8633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8633 = true := by
  rw [show D2M8K2.u8633 = KTree.node D2M8K2.u8625 (nat_lit 18624154) (nat_lit 3987642373) (nat_lit 0) D2M8K2.u8632 from rfl, allE_node, arows8625, irow8633, arows8632]
  all_goals rfl

theorem atot8633 : totK PD2M8K2 D2M8K2.u8633 = [1141605925976, 4595723615117, 5897468391414, 2524355548976, 282140963655, 4977114383, 0, 0] := by
  rw [show D2M8K2.u8633 = KTree.node D2M8K2.u8625 (nat_lit 18624154) (nat_lit 3987642373) (nat_lit 0) D2M8K2.u8632 from rfl, totK_node, atot8625, atot8632]
  decide +kernel

theorem arows8650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8650 = true := by
  rw [show D2M8K2.u8650 = KTree.node D2M8K2.u8642 (nat_lit 18640571) (nat_lit 2879332006) (nat_lit 0) D2M8K2.u8649 from rfl, allE_node, arows8642, irow8650, arows8649]
  all_goals rfl

theorem atot8650 : totK PD2M8K2 D2M8K2.u8650 = [857731848908, 4226936985321, 6317787586710, 2846703612384, 248327103102, 1310285577, 0, 0] := by
  rw [show D2M8K2.u8650 = KTree.node D2M8K2.u8642 (nat_lit 18640571) (nat_lit 2879332006) (nat_lit 0) D2M8K2.u8649 from rfl, totK_node, atot8642, atot8649]
  decide +kernel

theorem arows8665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8665 = true := by
  rw [show D2M8K2.u8665 = KTree.node D2M8K2.u8657 (nat_lit 18660536) (nat_lit 2351323859) (nat_lit 0) D2M8K2.u8664 from rfl, allE_node, arows8657, irow8665, arows8664]
  all_goals rfl

theorem atot8665 : totK PD2M8K2 D2M8K2.u8665 = [0, 1576125031654, 5705886345128, 5648141493888, 1437033661495, 69171811209, 0, 0] := by
  rw [show D2M8K2.u8665 = KTree.node D2M8K2.u8657 (nat_lit 18660536) (nat_lit 2351323859) (nat_lit 0) D2M8K2.u8664 from rfl, totK_node, atot8657, atot8664]
  decide +kernel

theorem arows8681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8681 = true := by
  rw [show D2M8K2.u8681 = KTree.node D2M8K2.u8673 (nat_lit 18718226) (nat_lit 4099311819) (nat_lit 0) D2M8K2.u8680 from rfl, allE_node, arows8673, irow8681, arows8680]
  all_goals rfl

theorem atot8681 : totK PD2M8K2 D2M8K2.u8681 = [0, 1499167729953, 5635670706465, 5790507084148, 1423825462406, 53246198005, 0, 0] := by
  rw [show D2M8K2.u8681 = KTree.node D2M8K2.u8673 (nat_lit 18718226) (nat_lit 4099311819) (nat_lit 0) D2M8K2.u8680 from rfl, totK_node, atot8673, atot8680]
  decide +kernel

theorem arows8696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8696 = true := by
  rw [show D2M8K2.u8696 = KTree.node D2M8K2.u8688 (nat_lit 18734977) (nat_lit 1532573537) (nat_lit 0) D2M8K2.u8695 from rfl, allE_node, arows8688, irow8696, arows8695]
  all_goals rfl

theorem atot8696 : totK PD2M8K2 D2M8K2.u8696 = [0, 0, 1738280747560, 5938910546813, 5429884020496, 1162030521956, 48508304344, 0] := by
  rw [show D2M8K2.u8696 = KTree.node D2M8K2.u8688 (nat_lit 18734977) (nat_lit 1532573537) (nat_lit 0) D2M8K2.u8695 from rfl, totK_node, atot8688, atot8695]
  decide +kernel

theorem arows8716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8716 = true := by
  rw [show D2M8K2.u8716 = KTree.node D2M8K2.u8708 (nat_lit 18752177) (nat_lit 1185978409) (nat_lit 0) D2M8K2.u8715 from rfl, allE_node, arows8708, irow8716, arows8715]
  all_goals rfl

theorem atot8716 : totK PD2M8K2 D2M8K2.u8716 = [0, 1256250740985, 4728852497562, 5612735864120, 2442646929458, 346876611316, 9139067247, 0] := by
  rw [show D2M8K2.u8716 = KTree.node D2M8K2.u8708 (nat_lit 18752177) (nat_lit 1185978409) (nat_lit 0) D2M8K2.u8715 from rfl, totK_node, atot8708, atot8715]
  decide +kernel

theorem arows8731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8731 = true := by
  rw [show D2M8K2.u8731 = KTree.node D2M8K2.u8723 (nat_lit 18774160) (nat_lit 3357963893) (nat_lit 0) D2M8K2.u8730 from rfl, allE_node, arows8723, irow8731, arows8730]
  all_goals rfl

theorem atot8731 : totK PD2M8K2 D2M8K2.u8731 = [0, 438307432569, 3135533314563, 6466765736877, 3845772720219, 443748582804, 6546549506, 0] := by
  rw [show D2M8K2.u8731 = KTree.node D2M8K2.u8723 (nat_lit 18774160) (nat_lit 3357963893) (nat_lit 0) D2M8K2.u8730 from rfl, totK_node, atot8723, atot8730]
  decide +kernel

theorem arows8747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8747 = true := by
  rw [show D2M8K2.u8747 = KTree.node D2M8K2.u8739 (nat_lit 18797427) (nat_lit 1287749372) (nat_lit 0) D2M8K2.u8746 from rfl, allE_node, arows8739, irow8747, arows8746]
  all_goals rfl

theorem atot8747 : totK PD2M8K2 D2M8K2.u8747 = [0, 1671899029652, 5847657113429, 5578054298396, 1324598136440, 56972831658, 0, 0] := by
  rw [show D2M8K2.u8747 = KTree.node D2M8K2.u8739 (nat_lit 18797427) (nat_lit 1287749372) (nat_lit 0) D2M8K2.u8746 from rfl, totK_node, atot8739, atot8746]
  decide +kernel

theorem arows8762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8762 = true := by
  rw [show D2M8K2.u8762 = KTree.node D2M8K2.u8754 (nat_lit 18818063) (nat_lit 2366670848) (nat_lit 0) D2M8K2.u8761 from rfl, allE_node, arows8754, irow8762, arows8761]
  all_goals rfl

theorem atot8762 : totK PD2M8K2 D2M8K2.u8762 = [0, 338332594357, 3156248068941, 6609106074162, 3780939024043, 433309015487, 6624648996, 0] := by
  rw [show D2M8K2.u8762 = KTree.node D2M8K2.u8754 (nat_lit 18818063) (nat_lit 2366670848) (nat_lit 0) D2M8K2.u8761 from rfl, totK_node, atot8754, atot8761]
  decide +kernel

theorem arows8779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8779 = true := by
  rw [show D2M8K2.u8779 = KTree.node D2M8K2.u8771 (nat_lit 18834600) (nat_lit 1951829061) (nat_lit 0) D2M8K2.u8778 from rfl, allE_node, arows8771, irow8779, arows8778]
  all_goals rfl

theorem atot8779 : totK PD2M8K2 D2M8K2.u8779 = [0, 1551173690002, 5577129507097, 5638032634416, 1542722615194, 73987572345, 0, 0] := by
  rw [show D2M8K2.u8779 = KTree.node D2M8K2.u8771 (nat_lit 18834600) (nat_lit 1951829061) (nat_lit 0) D2M8K2.u8778 from rfl, totK_node, atot8771, atot8778]
  decide +kernel

theorem arows8794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8794 = true := by
  rw [show D2M8K2.u8794 = KTree.node D2M8K2.u8786 (nat_lit 18853659) (nat_lit 3766489105) (nat_lit 0) D2M8K2.u8793 from rfl, allE_node, arows8786, irow8794, arows8793]
  all_goals rfl

theorem atot8794 : totK PD2M8K2 D2M8K2.u8794 = [0, 436310773281, 3685036773595, 6999957090276, 3001728012698, 180695429905, 0, 0] := by
  rw [show D2M8K2.u8794 = KTree.node D2M8K2.u8786 (nat_lit 18853659) (nat_lit 3766489105) (nat_lit 0) D2M8K2.u8793 from rfl, totK_node, atot8786, atot8793]
  decide +kernel

theorem arows8810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8810 = true := by
  rw [show D2M8K2.u8810 = KTree.node D2M8K2.u8802 (nat_lit 18876402) (nat_lit 3239204917) (nat_lit 0) D2M8K2.u8809 from rfl, allE_node, arows8802, irow8810, arows8809]
  all_goals rfl

theorem atot8810 : totK PD2M8K2 D2M8K2.u8810 = [0, 1558569039215, 5466530609611, 5563782665362, 1731465747930, 157699582453, 1429815836, 0] := by
  rw [show D2M8K2.u8810 = KTree.node D2M8K2.u8802 (nat_lit 18876402) (nat_lit 3239204917) (nat_lit 0) D2M8K2.u8809 from rfl, totK_node, atot8802, atot8809]
  decide +kernel

theorem arows8825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8825 = true := by
  rw [show D2M8K2.u8825 = KTree.node D2M8K2.u8817 (nat_lit 18895482) (nat_lit 3902394119) (nat_lit 0) D2M8K2.u8824 from rfl, allE_node, arows8817, irow8825, arows8824]
  all_goals rfl

theorem atot8825 : totK PD2M8K2 D2M8K2.u8825 = [0, 440768735669, 3390383680230, 6605700794134, 3646356818231, 364137431823, 2656098521, 0] := by
  rw [show D2M8K2.u8825 = KTree.node D2M8K2.u8817 (nat_lit 18895482) (nat_lit 3902394119) (nat_lit 0) D2M8K2.u8824 from rfl, totK_node, atot8817, atot8824]
  decide +kernel

theorem arows8843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8843 = true := by
  rw [show D2M8K2.u8843 = KTree.node D2M8K2.u8835 (nat_lit 19417068) (nat_lit 3167458472) (nat_lit 0) D2M8K2.u8842 from rfl, allE_node, arows8835, irow8843, arows8842]
  all_goals rfl

theorem atot8843 : totK PD2M8K2 D2M8K2.u8843 = [1501302504637, 4935640509446, 4493471114636, 1868373794976, 1222602753904, 275600791882, 9533751846, 0] := by
  rw [show D2M8K2.u8843 = KTree.node D2M8K2.u8835 (nat_lit 19417068) (nat_lit 3167458472) (nat_lit 0) D2M8K2.u8842 from rfl, totK_node, atot8835, atot8842]
  decide +kernel

theorem arows8858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8858 = true := by
  rw [show D2M8K2.u8858 = KTree.node D2M8K2.u8850 (nat_lit 19430795) (nat_lit 2634223692) (nat_lit 0) D2M8K2.u8857 from rfl, allE_node, arows8850, irow8858, arows8857]
  all_goals rfl

theorem atot8858 : totK PD2M8K2 D2M8K2.u8858 = [504505778244, 3672339829066, 6715452009951, 3061476423284, 257673568768, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8858 = KTree.node D2M8K2.u8850 (nat_lit 19430795) (nat_lit 2634223692) (nat_lit 0) D2M8K2.u8857 from rfl, totK_node, atot8850, atot8857]
  decide +kernel

theorem arows8874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8874 = true := by
  rw [show D2M8K2.u8874 = KTree.node D2M8K2.u8866 (nat_lit 19457782) (nat_lit 3556643814) (nat_lit 0) D2M8K2.u8873 from rfl, allE_node, arows8866, irow8874, arows8873]
  all_goals rfl

theorem atot8874 : totK PD2M8K2 D2M8K2.u8874 = [1394058052078, 5237780678603, 5956491539865, 1880972324477, 97375865135, 0, 0, 0] := by
  rw [show D2M8K2.u8874 = KTree.node D2M8K2.u8866 (nat_lit 19457782) (nat_lit 3556643814) (nat_lit 0) D2M8K2.u8873 from rfl, totK_node, atot8866, atot8873]
  decide +kernel

theorem arows8889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8889 = true := by
  rw [show D2M8K2.u8889 = KTree.node D2M8K2.u8881 (nat_lit 19475284) (nat_lit 3173992397) (nat_lit 0) D2M8K2.u8888 from rfl, allE_node, arows8881, irow8889, arows8888]
  all_goals rfl

theorem atot8889 : totK PD2M8K2 D2M8K2.u8889 = [635013582905, 3429880897130, 5815618853728, 3740327988067, 851487556748, 42081742489, 0, 0] := by
  rw [show D2M8K2.u8889 = KTree.node D2M8K2.u8881 (nat_lit 19475284) (nat_lit 3173992397) (nat_lit 0) D2M8K2.u8888 from rfl, totK_node, atot8881, atot8888]
  decide +kernel

theorem arows8906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8906 = true := by
  rw [show D2M8K2.u8906 = KTree.node D2M8K2.u8898 (nat_lit 19489229) (nat_lit 2002711666) (nat_lit 0) D2M8K2.u8905 from rfl, allE_node, arows8898, irow8906, arows8905]
  all_goals rfl

theorem atot8906 : totK PD2M8K2 D2M8K2.u8906 = [721462360444, 3297206976445, 5673259139528, 4010149129581, 732509837862, 15936385454, 0, 0] := by
  rw [show D2M8K2.u8906 = KTree.node D2M8K2.u8898 (nat_lit 19489229) (nat_lit 2002711666) (nat_lit 0) D2M8K2.u8905 from rfl, totK_node, atot8898, atot8905]
  decide +kernel

theorem arows8921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8921 = true := by
  rw [show D2M8K2.u8921 = KTree.node D2M8K2.u8913 (nat_lit 19547505) (nat_lit 1835327690) (nat_lit 0) D2M8K2.u8920 from rfl, allE_node, arows8913, irow8921, arows8920]
  all_goals rfl

theorem atot8921 : totK PD2M8K2 D2M8K2.u8921 = [1407814604715, 5470108176880, 5927212159982, 1624253120280, 77434547949, 0, 0, 0] := by
  rw [show D2M8K2.u8921 = KTree.node D2M8K2.u8913 (nat_lit 19547505) (nat_lit 1835327690) (nat_lit 0) D2M8K2.u8920 from rfl, totK_node, atot8913, atot8920]
  decide +kernel

theorem arows8937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8937 = true := by
  rw [show D2M8K2.u8937 = KTree.node D2M8K2.u8929 (nat_lit 19566133) (nat_lit 1282024378) (nat_lit 0) D2M8K2.u8936 from rfl, allE_node, arows8929, irow8937, arows8936]
  all_goals rfl

theorem atot8937 : totK PD2M8K2 D2M8K2.u8937 = [36508988125, 2089304813734, 6522372168549, 4906297637708, 718830550625, 19065934916, 0, 0] := by
  rw [show D2M8K2.u8937 = KTree.node D2M8K2.u8929 (nat_lit 19566133) (nat_lit 1282024378) (nat_lit 0) D2M8K2.u8936 from rfl, totK_node, atot8929, atot8936]
  decide +kernel

theorem arows8952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8952 = true := by
  rw [show D2M8K2.u8952 = KTree.node D2M8K2.u8944 (nat_lit 19581583) (nat_lit 2088394035) (nat_lit 0) D2M8K2.u8951 from rfl, allE_node, arows8944, irow8952, arows8951]
  all_goals rfl

theorem atot8952 : totK PD2M8K2 D2M8K2.u8952 = [1619370160385, 5702017977386, 5580700667084, 1410509482826, 65086375411, 0, 0, 0] := by
  rw [show D2M8K2.u8952 = KTree.node D2M8K2.u8944 (nat_lit 19581583) (nat_lit 2088394035) (nat_lit 0) D2M8K2.u8951 from rfl, totK_node, atot8944, atot8951]
  decide +kernel

theorem arows8971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8971 = true := by
  rw [show D2M8K2.u8971 = KTree.node D2M8K2.u8963 (nat_lit 19599800) (nat_lit 3865940388) (nat_lit 0) D2M8K2.u8970 from rfl, allE_node, arows8963, irow8971, arows8970]
  all_goals rfl

theorem atot8971 : totK PD2M8K2 D2M8K2.u8971 = [352152937815, 3387465626343, 6932216625199, 3388727768002, 263892108140, 1138244013, 0, 0] := by
  rw [show D2M8K2.u8971 = KTree.node D2M8K2.u8963 (nat_lit 19599800) (nat_lit 3865940388) (nat_lit 0) D2M8K2.u8970 from rfl, totK_node, atot8963, atot8970]
  decide +kernel

theorem arows8986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8986 = true := by
  rw [show D2M8K2.u8986 = KTree.node D2M8K2.u8978 (nat_lit 19622078) (nat_lit 3915131715) (nat_lit 0) D2M8K2.u8985 from rfl, allE_node, arows8978, irow8986, arows8985]
  all_goals rfl

theorem atot8986 : totK PD2M8K2 D2M8K2.u8986 = [1580538349891, 5461938326965, 5433019363130, 1779753676813, 219187105360, 4977114383, 0, 0] := by
  rw [show D2M8K2.u8986 = KTree.node D2M8K2.u8978 (nat_lit 19622078) (nat_lit 3915131715) (nat_lit 0) D2M8K2.u8985 from rfl, totK_node, atot8978, atot8985]
  decide +kernel

theorem arows9002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9002 = true := by
  rw [show D2M8K2.u9002 = KTree.node D2M8K2.u8994 (nat_lit 19638960) (nat_lit 3537119443) (nat_lit 0) D2M8K2.u9001 from rfl, allE_node, arows8994, irow9002, arows9001]
  all_goals rfl

theorem atot9002 : totK PD2M8K2 D2M8K2.u9002 = [441860355822, 3212076033474, 6485488351960, 3830850927549, 437602075646, 6190125969, 0, 0] := by
  rw [show D2M8K2.u9002 = KTree.node D2M8K2.u8994 (nat_lit 19638960) (nat_lit 3537119443) (nat_lit 0) D2M8K2.u9001 from rfl, totK_node, atot8994, atot9001]
  decide +kernel

theorem arows9017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9017 = true := by
  rw [show D2M8K2.u9017 = KTree.node D2M8K2.u9009 (nat_lit 19658840) (nat_lit 3849273495) (nat_lit 0) D2M8K2.u9016 from rfl, allE_node, arows9009, irow9017, arows9016]
  all_goals rfl

theorem atot9017 : totK PD2M8K2 D2M8K2.u9017 = [0, 1722107486139, 6137317480071, 5431735509607, 981949456195, 30414116156, 0, 0] := by
  rw [show D2M8K2.u9017 = KTree.node D2M8K2.u9009 (nat_lit 19658840) (nat_lit 3849273495) (nat_lit 0) D2M8K2.u9016 from rfl, totK_node, atot9009, atot9016]
  decide +kernel

theorem arows9034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9034 = true := by
  rw [show D2M8K2.u9034 = KTree.node D2M8K2.u9026 (nat_lit 19677000) (nat_lit 3521745760) (nat_lit 0) D2M8K2.u9033 from rfl, allE_node, arows9026, irow9034, arows9033]
  all_goals rfl

theorem atot9034 : totK PD2M8K2 D2M8K2.u9034 = [0, 821375927406, 4327250629685, 6454825057647, 2352641639386, 167659278068, 1310517177, 0] := by
  rw [show D2M8K2.u9034 = KTree.node D2M8K2.u9026 (nat_lit 19677000) (nat_lit 3521745760) (nat_lit 0) D2M8K2.u9033 from rfl, totK_node, atot9026, atot9033]
  decide +kernel

theorem arows9049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9049 = true := by
  rw [show D2M8K2.u9049 = KTree.node D2M8K2.u9041 (nat_lit 19705208) (nat_lit 3845934591) (nat_lit 0) D2M8K2.u9048 from rfl, allE_node, arows9041, irow9049, arows9048]
  all_goals rfl

theorem atot9049 : totK PD2M8K2 D2M8K2.u9049 = [0, 1198898452510, 5001720504640, 6203513631489, 1957340663868, 92765482980, 0, 0] := by
  rw [show D2M8K2.u9049 = KTree.node D2M8K2.u9041 (nat_lit 19705208) (nat_lit 3845934591) (nat_lit 0) D2M8K2.u9048 from rfl, totK_node, atot9041, atot9048]
  decide +kernel

theorem arows9065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9065 = true := by
  rw [show D2M8K2.u9065 = KTree.node D2M8K2.u9057 (nat_lit 19719193) (nat_lit 1456287306) (nat_lit 0) D2M8K2.u9064 from rfl, allE_node, arows9057, irow9065, arows9064]
  all_goals rfl

theorem atot9065 : totK PD2M8K2 D2M8K2.u9065 = [0, 1668831184555, 5933350484687, 5588399971135, 1206641438135, 48621984810, 0, 0] := by
  rw [show D2M8K2.u9065 = KTree.node D2M8K2.u9057 (nat_lit 19719193) (nat_lit 1456287306) (nat_lit 0) D2M8K2.u9064 from rfl, totK_node, atot9057, atot9064]
  decide +kernel

theorem arows9080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9080 = true := by
  rw [show D2M8K2.u9080 = KTree.node D2M8K2.u9072 (nat_lit 19797919) (nat_lit 2163906303) (nat_lit 0) D2M8K2.u9079 from rfl, allE_node, arows9072, irow9080, arows9079]
  all_goals rfl

theorem atot9080 : totK PD2M8K2 D2M8K2.u9080 = [0, 1287100024205, 5153903889932, 6037473727051, 1761720747274, 79495611348, 0, 0] := by
  rw [show D2M8K2.u9080 = KTree.node D2M8K2.u9072 (nat_lit 19797919) (nat_lit 2163906303) (nat_lit 0) D2M8K2.u9079 from rfl, totK_node, atot9072, atot9079]
  decide +kernel

theorem arows9098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9098 = true := by
  rw [show D2M8K2.u9098 = KTree.node D2M8K2.u9090 (nat_lit 19817176) (nat_lit 1935967148) (nat_lit 0) D2M8K2.u9097 from rfl, allE_node, arows9090, irow9098, arows9097]
  all_goals rfl

theorem atot9098 : totK PD2M8K2 D2M8K2.u9098 = [0, 405454907483, 2941306266659, 6146050248475, 3960788469876, 629673642580, 18953862985, 0] := by
  rw [show D2M8K2.u9098 = KTree.node D2M8K2.u9090 (nat_lit 19817176) (nat_lit 1935967148) (nat_lit 0) D2M8K2.u9097 from rfl, totK_node, atot9090, atot9097]
  decide +kernel

theorem arows9113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9113 = true := by
  rw [show D2M8K2.u9113 = KTree.node D2M8K2.u9105 (nat_lit 19834115) (nat_lit 2857493614) (nat_lit 0) D2M8K2.u9112 from rfl, allE_node, arows9105, irow9113, arows9112]
  all_goals rfl

theorem atot9113 : totK PD2M8K2 D2M8K2.u9113 = [0, 1603540413216, 5882472801135, 5719935746057, 1201371947909, 37830337538, 0, 0] := by
  rw [show D2M8K2.u9113 = KTree.node D2M8K2.u9105 (nat_lit 19834115) (nat_lit 2857493614) (nat_lit 0) D2M8K2.u9112 from rfl, totK_node, atot9105, atot9112]
  decide +kernel

theorem arows9129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9129 = true := by
  rw [show D2M8K2.u9129 = KTree.node D2M8K2.u9121 (nat_lit 19855933) (nat_lit 1136744894) (nat_lit 0) D2M8K2.u9128 from rfl, allE_node, arows9121, irow9129, arows9128]
  all_goals rfl

theorem atot9129 : totK PD2M8K2 D2M8K2.u9129 = [0, 406958004779, 3378500599674, 6629297712602, 3245555692667, 321996550199, 6052528252, 0] := by
  rw [show D2M8K2.u9129 = KTree.node D2M8K2.u9121 (nat_lit 19855933) (nat_lit 1136744894) (nat_lit 0) D2M8K2.u9128 from rfl, totK_node, atot9121, atot9128]
  decide +kernel

theorem arows9144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9144 = true := by
  rw [show D2M8K2.u9144 = KTree.node D2M8K2.u9136 (nat_lit 19875589) (nat_lit 1372969938) (nat_lit 0) D2M8K2.u9143 from rfl, allE_node, arows9136, irow9144, arows9143]
  all_goals rfl

theorem atot9144 : totK PD2M8K2 D2M8K2.u9144 = [0, 1612242912583, 5686438709345, 5684084128642, 1450130569777, 59805190679, 0, 0] := by
  rw [show D2M8K2.u9144 = KTree.node D2M8K2.u9136 (nat_lit 19875589) (nat_lit 1372969938) (nat_lit 0) D2M8K2.u9143 from rfl, totK_node, atot9136, atot9143]
  decide +kernel

theorem arows9161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9161 = true := by
  rw [show D2M8K2.u9161 = KTree.node D2M8K2.u9153 (nat_lit 19916691) (nat_lit 3036317301) (nat_lit 0) D2M8K2.u9160 from rfl, allE_node, arows9153, irow9161, arows9160]
  all_goals rfl

theorem atot9161 : totK PD2M8K2 D2M8K2.u9161 = [1647457354325, 5832170984153, 5433184566261, 1245626012514, 162533727996, 13338039113, 0, 0] := by
  rw [show D2M8K2.u9161 = KTree.node D2M8K2.u9153 (nat_lit 19916691) (nat_lit 3036317301) (nat_lit 0) D2M8K2.u9160 from rfl, totK_node, atot9153, atot9160]
  decide +kernel

theorem arows9176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9176 = true := by
  rw [show D2M8K2.u9176 = KTree.node D2M8K2.u9168 (nat_lit 19934600) (nat_lit 3865834180) (nat_lit 0) D2M8K2.u9175 from rfl, allE_node, arows9168, irow9176, arows9175]
  all_goals rfl

theorem atot9176 : totK PD2M8K2 D2M8K2.u9176 = [420768193827, 3281924229316, 6763892818850, 3445511100324, 288747597543, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9176 = KTree.node D2M8K2.u9168 (nat_lit 19934600) (nat_lit 3865834180) (nat_lit 0) D2M8K2.u9175 from rfl, totK_node, atot9168, atot9175]
  decide +kernel

theorem arows9192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9192 = true := by
  rw [show D2M8K2.u9192 = KTree.node D2M8K2.u9184 (nat_lit 19957977) (nat_lit 1747276272) (nat_lit 0) D2M8K2.u9191 from rfl, allE_node, arows9184, irow9192, arows9191]
  all_goals rfl

theorem atot9192 : totK PD2M8K2 D2M8K2.u9192 = [1570762549278, 5721723995456, 5719713646319, 1430277204369, 64980090578, 0, 0, 0] := by
  rw [show D2M8K2.u9192 = KTree.node D2M8K2.u9184 (nat_lit 19957977) (nat_lit 1747276272) (nat_lit 0) D2M8K2.u9191 from rfl, totK_node, atot9184, atot9191]
  decide +kernel

theorem arows9207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9207 = true := by
  rw [show D2M8K2.u9207 = KTree.node D2M8K2.u9199 (nat_lit 19975248) (nat_lit 2122598951) (nat_lit 0) D2M8K2.u9206 from rfl, allE_node, arows9199, irow9207, arows9206]
  all_goals rfl

theorem atot9207 : totK PD2M8K2 D2M8K2.u9207 = [333067881029, 2487685879607, 5823083935743, 4733739726555, 1081076458004, 47300615174, 0, 0] := by
  rw [show D2M8K2.u9207 = KTree.node D2M8K2.u9199 (nat_lit 19975248) (nat_lit 2122598951) (nat_lit 0) D2M8K2.u9206 from rfl, totK_node, atot9199, atot9206]
  decide +kernel

theorem arows9228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9228 = true := by
  rw [show D2M8K2.u9228 = KTree.node D2M8K2.u9220 (nat_lit 19990257) (nat_lit 1540848676) (nat_lit 0) D2M8K2.u9227 from rfl, allE_node, arows9220, irow9228, arows9227]
  all_goals rfl

theorem atot9228 : totK PD2M8K2 D2M8K2.u9228 = [974978340058, 3966142937255, 5633757468571, 3352180335352, 541981455696, 10717512769, 0, 0] := by
  rw [show D2M8K2.u9228 = KTree.node D2M8K2.u9220 (nat_lit 19990257) (nat_lit 1540848676) (nat_lit 0) D2M8K2.u9227 from rfl, totK_node, atot9220, atot9227]
  decide +kernel

theorem arows9243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9243 = true := by
  rw [show D2M8K2.u9243 = KTree.node D2M8K2.u9235 (nat_lit 20010885) (nat_lit 1508921502) (nat_lit 0) D2M8K2.u9242 from rfl, allE_node, arows9235, irow9243, arows9242]
  all_goals rfl

theorem atot9243 : totK PD2M8K2 D2M8K2.u9243 = [676680577296, 3870015835486, 6421196876843, 3038167742509, 297637236387, 2369401571, 0, 0] := by
  rw [show D2M8K2.u9243 = KTree.node D2M8K2.u9235 (nat_lit 20010885) (nat_lit 1508921502) (nat_lit 0) D2M8K2.u9242 from rfl, totK_node, atot9235, atot9242]
  decide +kernel

theorem arows9259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9259 = true := by
  rw [show D2M8K2.u9259 = KTree.node D2M8K2.u9251 (nat_lit 20033863) (nat_lit 2336060891) (nat_lit 0) D2M8K2.u9258 from rfl, allE_node, arows9251, irow9259, arows9258]
  all_goals rfl

theorem atot9259 : totK PD2M8K2 D2M8K2.u9259 = [1267036828086, 4605697473028, 5459239252673, 2590209045887, 410931382195, 16427657237, 0, 0] := by
  rw [show D2M8K2.u9259 = KTree.node D2M8K2.u9251 (nat_lit 20033863) (nat_lit 2336060891) (nat_lit 0) D2M8K2.u9258 from rfl, totK_node, atot9251, atot9258]
  decide +kernel

theorem arows9274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9274 = true := by
  rw [show D2M8K2.u9274 = KTree.node D2M8K2.u9266 (nat_lit 20050887) (nat_lit 3466768630) (nat_lit 0) D2M8K2.u9273 from rfl, allE_node, arows9266, irow9274, arows9273]
  all_goals rfl

theorem atot9274 : totK PD2M8K2 D2M8K2.u9274 = [769828837225, 4147303548999, 6478182395901, 2813830542201, 228356039193, 1239866073, 0, 0] := by
  rw [show D2M8K2.u9274 = KTree.node D2M8K2.u9266 (nat_lit 20050887) (nat_lit 3466768630) (nat_lit 0) D2M8K2.u9273 from rfl, totK_node, atot9266, atot9273]
  decide +kernel

theorem arows9291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9291 = true := by
  rw [show D2M8K2.u9291 = KTree.node D2M8K2.u9283 (nat_lit 20070125) (nat_lit 1557856815) (nat_lit 0) D2M8K2.u9290 from rfl, allE_node, arows9283, irow9291, arows9290]
  all_goals rfl

theorem atot9291 : totK PD2M8K2 D2M8K2.u9291 = [835159654126, 3748244775701, 5759896511122, 3383059642127, 551422644673, 17826068843, 0, 0] := by
  rw [show D2M8K2.u9291 = KTree.node D2M8K2.u9283 (nat_lit 20070125) (nat_lit 1557856815) (nat_lit 0) D2M8K2.u9290 from rfl, totK_node, atot9283, atot9290]
  decide +kernel

theorem arows9306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9306 = true := by
  rw [show D2M8K2.u9306 = KTree.node D2M8K2.u9298 (nat_lit 20085443) (nat_lit 2743764568) (nat_lit 0) D2M8K2.u9305 from rfl, allE_node, arows9298, irow9306, arows9305]
  all_goals rfl

theorem atot9306 : totK PD2M8K2 D2M8K2.u9306 = [1267195954010, 5063089769178, 5947602961216, 1903883271269, 127641916310, 1138244013, 0, 0] := by
  rw [show D2M8K2.u9306 = KTree.node D2M8K2.u9298 (nat_lit 20085443) (nat_lit 2743764568) (nat_lit 0) D2M8K2.u9305 from rfl, totK_node, atot9298, atot9305]
  decide +kernel

theorem arows9322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9322 = true := by
  rw [show D2M8K2.u9322 = KTree.node D2M8K2.u9314 (nat_lit 20107434) (nat_lit 3651520621) (nat_lit 0) D2M8K2.u9321 from rfl, allE_node, arows9314, irow9322, arows9321]
  all_goals rfl

theorem atot9322 : totK PD2M8K2 D2M8K2.u9322 = [0, 2309383843438, 6891133813662, 4569927480866, 534450528606, 6346264815, 0, 0] := by
  rw [show D2M8K2.u9322 = KTree.node D2M8K2.u9314 (nat_lit 20107434) (nat_lit 3651520621) (nat_lit 0) D2M8K2.u9321 from rfl, totK_node, atot9314, atot9321]
  decide +kernel

theorem arows9337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9337 = true := by
  rw [show D2M8K2.u9337 = KTree.node D2M8K2.u9329 (nat_lit 20169935) (nat_lit 2056206736) (nat_lit 0) D2M8K2.u9336 from rfl, allE_node, arows9329, irow9337, arows9336]
  all_goals rfl

theorem atot9337 : totK PD2M8K2 D2M8K2.u9337 = [0, 1342270722016, 5415735665915, 5941312023585, 1438503969316, 61428349899, 0, 0] := by
  rw [show D2M8K2.u9337 = KTree.node D2M8K2.u9329 (nat_lit 20169935) (nat_lit 2056206736) (nat_lit 0) D2M8K2.u9336 from rfl, totK_node, atot9329, atot9336]
  decide +kernel

theorem arows9355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9355 = true := by
  rw [show D2M8K2.u9355 = KTree.node D2M8K2.u9347 (nat_lit 20200682) (nat_lit 4139872233) (nat_lit 0) D2M8K2.u9354 from rfl, allE_node, arows9347, irow9355, arows9354]
  all_goals rfl

theorem atot9355 : totK PD2M8K2 D2M8K2.u9355 = [0, 825375348391, 4391844410384, 6480507651056, 2410922061049, 177023667282, 1209030869, 0] := by
  rw [show D2M8K2.u9355 = KTree.node D2M8K2.u9347 (nat_lit 20200682) (nat_lit 4139872233) (nat_lit 0) D2M8K2.u9354 from rfl, totK_node, atot9347, atot9354]
  decide +kernel

theorem arows9370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9370 = true := by
  rw [show D2M8K2.u9370 = KTree.node D2M8K2.u9362 (nat_lit 20213762) (nat_lit 3625604421) (nat_lit 0) D2M8K2.u9369 from rfl, allE_node, arows9362, irow9370, arows9369]
  all_goals rfl

theorem atot9370 : totK PD2M8K2 D2M8K2.u9370 = [0, 1744181968102, 6074834275284, 5559585992100, 1066933856728, 30417640612, 0, 0] := by
  rw [show D2M8K2.u9370 = KTree.node D2M8K2.u9362 (nat_lit 20213762) (nat_lit 3625604421) (nat_lit 0) D2M8K2.u9369 from rfl, totK_node, atot9362, atot9369]
  decide +kernel

theorem arows9386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9386 = true := by
  rw [show D2M8K2.u9386 = KTree.node D2M8K2.u9378 (nat_lit 20252642) (nat_lit 4094362655) (nat_lit 0) D2M8K2.u9385 from rfl, allE_node, arows9378, irow9386, arows9385]
  all_goals rfl

theorem atot9386 : totK PD2M8K2 D2M8K2.u9386 = [0, 1729481171938, 6016797347811, 5548020149414, 1113765326470, 34354748642, 0, 0] := by
  rw [show D2M8K2.u9386 = KTree.node D2M8K2.u9378 (nat_lit 20252642) (nat_lit 4094362655) (nat_lit 0) D2M8K2.u9385 from rfl, totK_node, atot9378, atot9385]
  decide +kernel

theorem arows9401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9401 = true := by
  rw [show D2M8K2.u9401 = KTree.node D2M8K2.u9393 (nat_lit 20294126) (nat_lit 3837962760) (nat_lit 0) D2M8K2.u9400 from rfl, allE_node, arows9393, irow9401, arows9400]
  all_goals rfl

theorem atot9401 : totK PD2M8K2 D2M8K2.u9401 = [0, 1696187798203, 5936295252434, 5609921495410, 1205006899189, 38152077865, 0, 0] := by
  rw [show D2M8K2.u9401 = KTree.node D2M8K2.u9393 (nat_lit 20294126) (nat_lit 3837962760) (nat_lit 0) D2M8K2.u9400 from rfl, totK_node, atot9393, atot9400]
  decide +kernel

theorem arows9418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9418 = true := by
  rw [show D2M8K2.u9418 = KTree.node D2M8K2.u9410 (nat_lit 20329362) (nat_lit 3101459682) (nat_lit 0) D2M8K2.u9417 from rfl, allE_node, arows9410, irow9418, arows9417]
  all_goals rfl

theorem atot9418 : totK PD2M8K2 D2M8K2.u9418 = [0, 1593960421889, 5774136376411, 5648637917067, 1236225082625, 51057111145, 0, 0] := by
  rw [show D2M8K2.u9418 = KTree.node D2M8K2.u9410 (nat_lit 20329362) (nat_lit 3101459682) (nat_lit 0) D2M8K2.u9417 from rfl, totK_node, atot9410, atot9417]
  decide +kernel

theorem arows9433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9433 = true := by
  rw [show D2M8K2.u9433 = KTree.node D2M8K2.u9425 (nat_lit 20348932) (nat_lit 3807881487) (nat_lit 0) D2M8K2.u9432 from rfl, allE_node, arows9425, irow9433, arows9432]
  all_goals rfl

theorem atot9433 : totK PD2M8K2 D2M8K2.u9433 = [18947402031, 195402256576, 2973225131948, 6882677606151, 3610057179591, 412573662270, 6115358396, 0] := by
  rw [show D2M8K2.u9433 = KTree.node D2M8K2.u9425 (nat_lit 20348932) (nat_lit 3807881487) (nat_lit 0) D2M8K2.u9432 from rfl, totK_node, atot9425, atot9432]
  decide +kernel

theorem arows9449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9449 = true := by
  rw [show D2M8K2.u9449 = KTree.node D2M8K2.u9441 (nat_lit 20414839) (nat_lit 2231357424) (nat_lit 0) D2M8K2.u9448 from rfl, allE_node, arows9441, irow9449, arows9448]
  all_goals rfl

theorem atot9449 : totK PD2M8K2 D2M8K2.u9449 = [1779847692453, 6063904778953, 5393032555064, 1065264761454, 32650077886, 0, 0, 0] := by
  rw [show D2M8K2.u9449 = KTree.node D2M8K2.u9441 (nat_lit 20414839) (nat_lit 2231357424) (nat_lit 0) D2M8K2.u9448 from rfl, totK_node, atot9441, atot9448]
  decide +kernel

theorem arows9464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9464 = true := by
  rw [show D2M8K2.u9464 = KTree.node D2M8K2.u9456 (nat_lit 20432601) (nat_lit 1729926509) (nat_lit 0) D2M8K2.u9463 from rfl, allE_node, arows9456, irow9464, arows9463]
  all_goals rfl

theorem atot9464 : totK PD2M8K2 D2M8K2.u9464 = [325349082814, 3214418060462, 6935357709866, 3487679694473, 290220860675, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9464 = KTree.node D2M8K2.u9456 (nat_lit 20432601) (nat_lit 1729926509) (nat_lit 0) D2M8K2.u9463 from rfl, totK_node, atot9456, atot9463]
  decide +kernel

theorem arows9483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9483 = true := by
  rw [show D2M8K2.u9483 = KTree.node D2M8K2.u9475 (nat_lit 20456156) (nat_lit 3231565442) (nat_lit 0) D2M8K2.u9482 from rfl, allE_node, arows9475, irow9483, arows9482]
  all_goals rfl

theorem atot9483 : totK PD2M8K2 D2M8K2.u9483 = [1627026869248, 5776960205532, 5698525149315, 1437397128973, 66568656805, 0, 0, 0] := by
  rw [show D2M8K2.u9483 = KTree.node D2M8K2.u9475 (nat_lit 20456156) (nat_lit 3231565442) (nat_lit 0) D2M8K2.u9482 from rfl, totK_node, atot9475, atot9482]
  decide +kernel

theorem arows9498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9498 = true := by
  rw [show D2M8K2.u9498 = KTree.node D2M8K2.u9490 (nat_lit 20473186) (nat_lit 4194847968) (nat_lit 0) D2M8K2.u9497 from rfl, allE_node, arows9490, irow9498, arows9497]
  all_goals rfl

theorem atot9498 : totK PD2M8K2 D2M8K2.u9498 = [231056150071, 2389192352229, 5929839236555, 4794247061098, 1094457773523, 47300615174, 0, 0] := by
  rw [show D2M8K2.u9498 = KTree.node D2M8K2.u9490 (nat_lit 20473186) (nat_lit 4194847968) (nat_lit 0) D2M8K2.u9497 from rfl, totK_node, atot9490, atot9497]
  decide +kernel

theorem arows9514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9514 = true := by
  rw [show D2M8K2.u9514 = KTree.node D2M8K2.u9506 (nat_lit 20488292) (nat_lit 3249980346) (nat_lit 0) D2M8K2.u9513 from rfl, allE_node, arows9506, irow9514, arows9513]
  all_goals rfl

theorem atot9514 : totK PD2M8K2 D2M8K2.u9514 = [1065396631801, 4095588950110, 5599990611111, 3216812845448, 521819865534, 10717512769, 0, 0] := by
  rw [show D2M8K2.u9514 = KTree.node D2M8K2.u9506 (nat_lit 20488292) (nat_lit 3249980346) (nat_lit 0) D2M8K2.u9513 from rfl, totK_node, atot9506, atot9513]
  decide +kernel

theorem arows9529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9529 = true := by
  rw [show D2M8K2.u9529 = KTree.node D2M8K2.u9521 (nat_lit 20508576) (nat_lit 3528681453) (nat_lit 0) D2M8K2.u9528 from rfl, allE_node, arows9521, irow9529, arows9528]
  all_goals rfl

theorem atot9529 : totK PD2M8K2 D2M8K2.u9529 = [588190532914, 3697867071680, 6508030302732, 3232140720699, 314163959227, 2369401571, 0, 0] := by
  rw [show D2M8K2.u9529 = KTree.node D2M8K2.u9521 (nat_lit 20508576) (nat_lit 3528681453) (nat_lit 0) D2M8K2.u9528 from rfl, totK_node, atot9521, atot9528]
  decide +kernel

theorem arows9546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9546 = true := by
  rw [show D2M8K2.u9546 = KTree.node D2M8K2.u9538 (nat_lit 20532942) (nat_lit 3186916348) (nat_lit 0) D2M8K2.u9545 from rfl, allE_node, arows9538, irow9546, arows9545]
  all_goals rfl

theorem atot9546 : totK PD2M8K2 D2M8K2.u9546 = [1279891971725, 4945114136606, 5759363052385, 2195207501385, 286081923702, 11853261585, 0, 0] := by
  rw [show D2M8K2.u9546 = KTree.node D2M8K2.u9538 (nat_lit 20532942) (nat_lit 3186916348) (nat_lit 0) D2M8K2.u9545 from rfl, totK_node, atot9538, atot9545]
  decide +kernel

theorem arows9561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9561 = true := by
  rw [show D2M8K2.u9561 = KTree.node D2M8K2.u9553 (nat_lit 20549593) (nat_lit 1504782725) (nat_lit 0) D2M8K2.u9560 from rfl, allE_node, arows9553, irow9561, arows9560]
  all_goals rfl

theorem atot9561 : totK PD2M8K2 D2M8K2.u9561 = [756603494842, 4003404724677, 6416730570759, 3011257467793, 249863636039, 1239866073, 0, 0] := by
  rw [show D2M8K2.u9561 = KTree.node D2M8K2.u9553 (nat_lit 20549593) (nat_lit 1504782725) (nat_lit 0) D2M8K2.u9560 from rfl, totK_node, atot9553, atot9560]
  decide +kernel

theorem arows9577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9577 = true := by
  rw [show D2M8K2.u9577 = KTree.node D2M8K2.u9569 (nat_lit 20612420) (nat_lit 2398721148) (nat_lit 0) D2M8K2.u9576 from rfl, allE_node, arows9569, irow9577, arows9576]
  all_goals rfl

theorem atot9577 : totK PD2M8K2 D2M8K2.u9577 = [948697751437, 4002754970886, 5691863921306, 3172138206331, 524647816261, 17826068843, 0, 0] := by
  rw [show D2M8K2.u9577 = KTree.node D2M8K2.u9569 (nat_lit 20612420) (nat_lit 2398721148) (nat_lit 0) D2M8K2.u9576 from rfl, totK_node, atot9569, atot9576]
  decide +kernel

theorem arows9592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9592 = true := by
  rw [show D2M8K2.u9592 = KTree.node D2M8K2.u9584 (nat_lit 20629111) (nat_lit 2170659497) (nat_lit 0) D2M8K2.u9591 from rfl, allE_node, arows9584, irow9592, arows9591]
  all_goals rfl

theorem atot9592 : totK PD2M8K2 D2M8K2.u9592 = [1159193629323, 4769448822448, 5993109173700, 2291277774602, 178297807383, 1310285577, 0, 0] := by
  rw [show D2M8K2.u9592 = KTree.node D2M8K2.u9584 (nat_lit 20629111) (nat_lit 2170659497) (nat_lit 0) D2M8K2.u9591 from rfl, totK_node, atot9584, atot9591]
  decide +kernel

theorem arows9610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9610 = true := by
  rw [show D2M8K2.u9610 = KTree.node D2M8K2.u9602 (nat_lit 20644302) (nat_lit 3851888000) (nat_lit 0) D2M8K2.u9609 from rfl, allE_node, arows9602, irow9610, arows9609]
  all_goals rfl

theorem atot9610 : totK PD2M8K2 D2M8K2.u9610 = [0, 1968060878212, 6333733072836, 5074721722721, 909322388012, 31562413104, 0, 0] := by
  rw [show D2M8K2.u9610 = KTree.node D2M8K2.u9602 (nat_lit 20644302) (nat_lit 3851888000) (nat_lit 0) D2M8K2.u9609 from rfl, totK_node, atot9602, atot9609]
  decide +kernel

theorem arows9625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9625 = true := by
  rw [show D2M8K2.u9625 = KTree.node D2M8K2.u9617 (nat_lit 20665236) (nat_lit 3260124361) (nat_lit 0) D2M8K2.u9624 from rfl, allE_node, arows9617, irow9625, arows9624]
  all_goals rfl

theorem atot9625 : totK PD2M8K2 D2M8K2.u9625 = [0, 1622585794533, 6012377980544, 5679577200825, 1004355061651, 17769335896, 0, 0] := by
  rw [show D2M8K2.u9625 = KTree.node D2M8K2.u9617 (nat_lit 20665236) (nat_lit 3260124361) (nat_lit 0) D2M8K2.u9624 from rfl, totK_node, atot9617, atot9624]
  decide +kernel

theorem arows9641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9641 = true := by
  rw [show D2M8K2.u9641 = KTree.node D2M8K2.u9633 (nat_lit 20685529) (nat_lit 1409730240) (nat_lit 0) D2M8K2.u9640 from rfl, allE_node, arows9633, irow9641, arows9640]
  all_goals rfl

theorem atot9641 : totK PD2M8K2 D2M8K2.u9641 = [0, 442893429356, 3423494906575, 6852517691559, 3211469695181, 236148482480, 1369150432, 0] := by
  rw [show D2M8K2.u9641 = KTree.node D2M8K2.u9633 (nat_lit 20685529) (nat_lit 1409730240) (nat_lit 0) D2M8K2.u9640 from rfl, totK_node, atot9633, atot9640]
  decide +kernel

theorem arows9656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9656 = true := by
  rw [show D2M8K2.u9656 = KTree.node D2M8K2.u9648 (nat_lit 20707501) (nat_lit 1301917714) (nat_lit 0) D2M8K2.u9655 from rfl, allE_node, arows9648, irow9656, arows9655]
  all_goals rfl

theorem atot9656 : totK PD2M8K2 D2M8K2.u9656 = [0, 1559838129390, 5704142279183, 5822211404991, 1397699387497, 40447645384, 0, 0] := by
  rw [show D2M8K2.u9656 = KTree.node D2M8K2.u9648 (nat_lit 20707501) (nat_lit 1301917714) (nat_lit 0) D2M8K2.u9655 from rfl, totK_node, atot9648, atot9655]
  decide +kernel

theorem arows9673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9673 = true := by
  rw [show D2M8K2.u9673 = KTree.node D2M8K2.u9665 (nat_lit 20742580) (nat_lit 3692344773) (nat_lit 0) D2M8K2.u9672 from rfl, allE_node, arows9665, irow9673, arows9672]
  all_goals rfl

theorem atot9673 : totK PD2M8K2 D2M8K2.u9673 = [0, 1656353084401, 5809440504064, 5563019228047, 1348962142366, 61781799477, 0, 0] := by
  rw [show D2M8K2.u9673 = KTree.node D2M8K2.u9665 (nat_lit 20742580) (nat_lit 3692344773) (nat_lit 0) D2M8K2.u9672 from rfl, totK_node, atot9665, atot9672]
  decide +kernel

theorem arows9688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9688 = true := by
  rw [show D2M8K2.u9688 = KTree.node D2M8K2.u9680 (nat_lit 20765128) (nat_lit 3841397406) (nat_lit 0) D2M8K2.u9687 from rfl, allE_node, arows9680, irow9688, arows9687]
  all_goals rfl

theorem atot9688 : totK PD2M8K2 D2M8K2.u9688 = [0, 496401116654, 3371533963006, 6511248891251, 3439246238763, 363311904978, 6301476269, 0] := by
  rw [show D2M8K2.u9688 = KTree.node D2M8K2.u9680 (nat_lit 20765128) (nat_lit 3841397406) (nat_lit 0) D2M8K2.u9687 from rfl, totK_node, atot9680, atot9687]
  decide +kernel

theorem arows9704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9704 = true := by
  rw [show D2M8K2.u9704 = KTree.node D2M8K2.u9696 (nat_lit 20790758) (nat_lit 4113698729) (nat_lit 0) D2M8K2.u9703 from rfl, allE_node, arows9696, irow9704, arows9703]
  all_goals rfl

theorem atot9704 : totK PD2M8K2 D2M8K2.u9704 = [0, 1537374448220, 5671225172831, 5757192890690, 1458403796849, 60783135348, 0, 0] := by
  rw [show D2M8K2.u9704 = KTree.node D2M8K2.u9696 (nat_lit 20790758) (nat_lit 4113698729) (nat_lit 0) D2M8K2.u9703 from rfl, totK_node, atot9696, atot9703]
  decide +kernel

theorem arows9719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9719 = true := by
  rw [show D2M8K2.u9719 = KTree.node D2M8K2.u9711 (nat_lit 20810578) (nat_lit 3829599236) (nat_lit 0) D2M8K2.u9718 from rfl, allE_node, arows9711, irow9719, arows9718]
  all_goals rfl

theorem atot9719 : totK PD2M8K2 D2M8K2.u9719 = [0, 413512698075, 3356735902451, 6569903329399, 3454066731673, 365597728921, 6363931553, 0] := by
  rw [show D2M8K2.u9719 = KTree.node D2M8K2.u9711 (nat_lit 20810578) (nat_lit 3829599236) (nat_lit 0) D2M8K2.u9718 from rfl, totK_node, atot9711, atot9718]
  decide +kernel

theorem arows9739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9739 = true := by
  rw [show D2M8K2.u9739 = KTree.node D2M8K2.u9731 (nat_lit 20869663) (nat_lit 1608211527) (nat_lit 0) D2M8K2.u9738 from rfl, allE_node, arows9731, irow9739, arows9738]
  all_goals rfl

theorem atot9739 : totK PD2M8K2 D2M8K2.u9739 = [0, 1696578666752, 5812641492764, 5567435377553, 1319853484057, 48890456903, 0, 0] := by
  rw [show D2M8K2.u9739 = KTree.node D2M8K2.u9731 (nat_lit 20869663) (nat_lit 1608211527) (nat_lit 0) D2M8K2.u9738 from rfl, totK_node, atot9731, atot9738]
  decide +kernel

theorem arows9754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9754 = true := by
  rw [show D2M8K2.u9754 = KTree.node D2M8K2.u9746 (nat_lit 20888538) (nat_lit 2752150154) (nat_lit 0) D2M8K2.u9753 from rfl, allE_node, arows9746, irow9754, arows9753]
  all_goals rfl

theorem atot9754 : totK PD2M8K2 D2M8K2.u9754 = [0, 0, 2278010689100, 6725060447272, 4502540433491, 580752741443, 10913788937, 0] := by
  rw [show D2M8K2.u9754 = KTree.node D2M8K2.u9746 (nat_lit 20888538) (nat_lit 2752150154) (nat_lit 0) D2M8K2.u9753 from rfl, totK_node, atot9746, atot9753]
  decide +kernel

theorem arows9770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9770 = true := by
  rw [show D2M8K2.u9770 = KTree.node D2M8K2.u9762 (nat_lit 20909623) (nat_lit 1455307149) (nat_lit 0) D2M8K2.u9769 from rfl, allE_node, arows9762, irow9770, arows9769]
  all_goals rfl

theorem atot9770 : totK PD2M8K2 D2M8K2.u9770 = [0, 1487083484424, 5116932158132, 5229042914897, 2037958833342, 414566938184, 21751168066, 0] := by
  rw [show D2M8K2.u9770 = KTree.node D2M8K2.u9762 (nat_lit 20909623) (nat_lit 1455307149) (nat_lit 0) D2M8K2.u9769 from rfl, totK_node, atot9762, atot9769]
  decide +kernel

theorem arows9785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9785 = true := by
  rw [show D2M8K2.u9785 = KTree.node D2M8K2.u9777 (nat_lit 20923373) (nat_lit 1934743799) (nat_lit 0) D2M8K2.u9784 from rfl, allE_node, arows9777, irow9785, arows9784]
  all_goals rfl

theorem atot9785 : totK PD2M8K2 D2M8K2.u9785 = [0, 609933941819, 3864637052791, 6607082169519, 2860931229485, 241949966194, 1369150432, 0] := by
  rw [show D2M8K2.u9785 = KTree.node D2M8K2.u9777 (nat_lit 20923373) (nat_lit 1934743799) (nat_lit 0) D2M8K2.u9784 from rfl, totK_node, atot9777, atot9784]
  decide +kernel

theorem arows9802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9802 = true := by
  rw [show D2M8K2.u9802 = KTree.node D2M8K2.u9794 (nat_lit 20992009) (nat_lit 1502541031) (nat_lit 0) D2M8K2.u9801 from rfl, allE_node, arows9794, irow9802, arows9801]
  all_goals rfl

theorem atot9802 : totK PD2M8K2 D2M8K2.u9802 = [0, 1373416991479, 5364577263541, 5918588705331, 1582530970686, 68587185284, 0, 0] := by
  rw [show D2M8K2.u9802 = KTree.node D2M8K2.u9794 (nat_lit 20992009) (nat_lit 1502541031) (nat_lit 0) D2M8K2.u9801 from rfl, totK_node, atot9794, atot9801]
  decide +kernel

theorem arows9817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9817 = true := by
  rw [show D2M8K2.u9817 = KTree.node D2M8K2.u9809 (nat_lit 21013179) (nat_lit 3621598718) (nat_lit 0) D2M8K2.u9816 from rfl, allE_node, arows9809, irow9817, arows9816]
  all_goals rfl

theorem atot9817 : totK PD2M8K2 D2M8K2.u9817 = [0, 696237288013, 3947847380791, 6564372887312, 2855917447035, 205402285779, 1206465782, 0] := by
  rw [show D2M8K2.u9817 = KTree.node D2M8K2.u9809 (nat_lit 21013179) (nat_lit 3621598718) (nat_lit 0) D2M8K2.u9816 from rfl, totK_node, atot9809, atot9816]
  decide +kernel

theorem arows9833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9833 = true := by
  rw [show D2M8K2.u9833 = KTree.node D2M8K2.u9825 (nat_lit 21038790) (nat_lit 3813637487) (nat_lit 0) D2M8K2.u9832 from rfl, allE_node, arows9825, irow9833, arows9832]
  all_goals rfl

theorem atot9833 : totK PD2M8K2 D2M8K2.u9833 = [0, 1613359424907, 5805125869278, 5736386248260, 1329057504762, 50803385535, 0, 0] := by
  rw [show D2M8K2.u9833 = KTree.node D2M8K2.u9825 (nat_lit 21038790) (nat_lit 3813637487) (nat_lit 0) D2M8K2.u9832 from rfl, totK_node, atot9825, atot9832]
  decide +kernel

theorem arows9848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9848 = true := by
  rw [show D2M8K2.u9848 = KTree.node D2M8K2.u9840 (nat_lit 21058373) (nat_lit 1818399411) (nat_lit 0) D2M8K2.u9847 from rfl, allE_node, arows9840, irow9848, arows9847]
  all_goals rfl

theorem atot9848 : totK PD2M8K2 D2M8K2.u9848 = [0, 0, 2128673121237, 6622820192909, 4767444489449, 689542522038, 19065934916, 0] := by
  rw [show D2M8K2.u9848 = KTree.node D2M8K2.u9840 (nat_lit 21058373) (nat_lit 1818399411) (nat_lit 0) D2M8K2.u9847 from rfl, totK_node, atot9840, atot9847]
  decide +kernel

theorem arows9866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9866 = true := by
  rw [show D2M8K2.u9866 = KTree.node D2M8K2.u9858 (nat_lit 21074222) (nat_lit 3854375359) (nat_lit 0) D2M8K2.u9865 from rfl, allE_node, arows9858, irow9866, arows9865]
  all_goals rfl

theorem atot9866 : totK PD2M8K2 D2M8K2.u9866 = [0, 1542562582913, 5628829942672, 5714299246062, 1456454182843, 64439056800, 0, 0] := by
  rw [show D2M8K2.u9866 = KTree.node D2M8K2.u9858 (nat_lit 21074222) (nat_lit 3854375359) (nat_lit 0) D2M8K2.u9865 from rfl, totK_node, atot9858, atot9865]
  decide +kernel

theorem arows9881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9881 = true := by
  rw [show D2M8K2.u9881 = KTree.node D2M8K2.u9873 (nat_lit 21092548) (nat_lit 3810772178) (nat_lit 0) D2M8K2.u9880 from rfl, allE_node, arows9873, irow9881, arows9880]
  all_goals rfl

theorem atot9881 : totK PD2M8K2 D2M8K2.u9881 = [0, 435349895630, 3517951867904, 6902313060941, 3163255004830, 227778260402, 1138244013, 0] := by
  rw [show D2M8K2.u9881 = KTree.node D2M8K2.u9873 (nat_lit 21092548) (nat_lit 3810772178) (nat_lit 0) D2M8K2.u9880 from rfl, totK_node, atot9873, atot9880]
  decide +kernel

theorem arows9897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9897 = true := by
  rw [show D2M8K2.u9897 = KTree.node D2M8K2.u9889 (nat_lit 21115430) (nat_lit 3974806121) (nat_lit 0) D2M8K2.u9896 from rfl, allE_node, arows9889, irow9897, arows9896]
  all_goals rfl

theorem atot9897 : totK PD2M8K2 D2M8K2.u9897 = [0, 1549356641525, 5425843624928, 5500728469583, 1764589730849, 205386045301, 4977114383, 0] := by
  rw [show D2M8K2.u9897 = KTree.node D2M8K2.u9889 (nat_lit 21115430) (nat_lit 3974806121) (nat_lit 0) D2M8K2.u9896 from rfl, totK_node, atot9889, atot9896]
  decide +kernel

theorem arows9912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9912 = true := by
  rw [show D2M8K2.u9912 = KTree.node D2M8K2.u9904 (nat_lit 21132684) (nat_lit 2939251914) (nat_lit 0) D2M8K2.u9911 from rfl, allE_node, arows9904, irow9912, arows9911]
  all_goals rfl

theorem atot9912 : totK PD2M8K2 D2M8K2.u9912 = [0, 439710514742, 3198222493779, 6522004153706, 3790110132996, 408868700809, 6241690223, 0] := by
  rw [show D2M8K2.u9912 = KTree.node D2M8K2.u9904 (nat_lit 21132684) (nat_lit 2939251914) (nat_lit 0) D2M8K2.u9911 from rfl, totK_node, atot9904, atot9911]
  decide +kernel

theorem arows9929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9929 = true := by
  rw [show D2M8K2.u9929 = KTree.node D2M8K2.u9921 (nat_lit 21153941) (nat_lit 2375234260) (nat_lit 0) D2M8K2.u9928 from rfl, allE_node, arows9921, irow9929, arows9928]
  all_goals rfl

theorem atot9929 : totK PD2M8K2 D2M8K2.u9929 = [0, 0, 1776638835223, 6189052879912, 5405140945051, 917823209872, 29478153761, 0] := by
  rw [show D2M8K2.u9929 = KTree.node D2M8K2.u9921 (nat_lit 21153941) (nat_lit 2375234260) (nat_lit 0) D2M8K2.u9928 from rfl, totK_node, atot9921, atot9928]
  decide +kernel

theorem arows9944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9944 = true := by
  rw [show D2M8K2.u9944 = KTree.node D2M8K2.u9936 (nat_lit 21172155) (nat_lit 2481221143) (nat_lit 640) D2M8K2.u9943 from rfl, allE_node, arows9936, irow9944, arows9943]
  all_goals rfl

theorem atot9944 : totK PD2M8K2 D2M8K2.u9944 = [0, 0, 737384741921, 4250968573223, 6559399807449, 2303191620513, 177694038662, 1369150432] := by
  rw [show D2M8K2.u9944 = KTree.node D2M8K2.u9936 (nat_lit 21172155) (nat_lit 2481221143) (nat_lit 640) D2M8K2.u9943 from rfl, totK_node, atot9936, atot9943]
  decide +kernel

theorem arows9960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9960 = true := by
  rw [show D2M8K2.u9960 = KTree.node D2M8K2.u9952 (nat_lit 21242224) (nat_lit 3512545649) (nat_lit 0) D2M8K2.u9959 from rfl, allE_node, arows9952, irow9960, arows9959]
  all_goals rfl

theorem atot9960 : totK PD2M8K2 D2M8K2.u9960 = [0, 0, 1887516517373, 6348116534716, 5275227148027, 790521353448, 21726857718, 0] := by
  rw [show D2M8K2.u9960 = KTree.node D2M8K2.u9952 (nat_lit 21242224) (nat_lit 3512545649) (nat_lit 0) D2M8K2.u9959 from rfl, totK_node, atot9952, atot9959]
  decide +kernel

theorem arows9975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9975 = true := by
  rw [show D2M8K2.u9975 = KTree.node D2M8K2.u9967 (nat_lit 21287122) (nat_lit 4052852322) (nat_lit 0) D2M8K2.u9974 from rfl, allE_node, arows9967, irow9975, arows9974]
  all_goals rfl

theorem atot9975 : totK PD2M8K2 D2M8K2.u9975 = [0, 0, 1774005882674, 6165617448887, 5537239841398, 948157117815, 24806318757, 0] := by
  rw [show D2M8K2.u9975 = KTree.node D2M8K2.u9967 (nat_lit 21287122) (nat_lit 4052852322) (nat_lit 0) D2M8K2.u9974 from rfl, totK_node, atot9967, atot9974]
  decide +kernel

theorem arows9994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9994 = true := by
  rw [show D2M8K2.u9994 = KTree.node D2M8K2.u9986 (nat_lit 21323048) (nat_lit 3942464715) (nat_lit 0) D2M8K2.u9993 from rfl, allE_node, arows9986, irow9994, arows9993]
  all_goals rfl

theorem atot9994 : totK PD2M8K2 D2M8K2.u9994 = [0, 0, 1674762899518, 6102971601963, 5542947382544, 950852820993, 30842014145, 0] := by
  rw [show D2M8K2.u9994 = KTree.node D2M8K2.u9986 (nat_lit 21323048) (nat_lit 3942464715) (nat_lit 0) D2M8K2.u9993 from rfl, totK_node, atot9986, atot9993]
  decide +kernel

theorem arows10009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10009 = true := by
  rw [show D2M8K2.u10009 = KTree.node D2M8K2.u10001 (nat_lit 21362432) (nat_lit 3481338763) (nat_lit 0) D2M8K2.u10008 from rfl, allE_node, arows10001, irow10009, arows10008]
  all_goals rfl

theorem atot10009 : totK PD2M8K2 D2M8K2.u10009 = [0, 0, 2096388131836, 6571101629377, 5109508940511, 710083276557, 11543047308, 0] := by
  rw [show D2M8K2.u10009 = KTree.node D2M8K2.u10001 (nat_lit 21362432) (nat_lit 3481338763) (nat_lit 0) D2M8K2.u10008 from rfl, totK_node, atot10001, atot10008]
  decide +kernel

theorem arows10025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10025 = true := by
  rw [show D2M8K2.u10025 = KTree.node D2M8K2.u10017 (nat_lit 21448206) (nat_lit 3046409677) (nat_lit 0) D2M8K2.u10024 from rfl, allE_node, arows10017, irow10025, arows10024]
  all_goals rfl

theorem atot10025 : totK PD2M8K2 D2M8K2.u10025 = [0, 1324170613788, 4799068789414, 5604968389626, 2426902668699, 365121365906, 13930390162, 0] := by
  rw [show D2M8K2.u10025 = KTree.node D2M8K2.u10017 (nat_lit 21448206) (nat_lit 3046409677) (nat_lit 0) D2M8K2.u10024 from rfl, totK_node, atot10017, atot10024]
  decide +kernel

theorem arows10040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10040 = true := by
  rw [show D2M8K2.u10040 = KTree.node D2M8K2.u10032 (nat_lit 21461677) (nat_lit 788509023) (nat_lit 2) D2M8K2.u10039 from rfl, allE_node, arows10032, irow10040, arows10039]
  all_goals rfl

theorem atot10040 : totK PD2M8K2 D2M8K2.u10040 = [0, 793563709804, 3774066313834, 5770872707239, 3366833695187, 749102604007, 40931783143, 0] := by
  rw [show D2M8K2.u10040 = KTree.node D2M8K2.u10032 (nat_lit 21461677) (nat_lit 788509023) (nat_lit 2) D2M8K2.u10039 from rfl, totK_node, atot10032, atot10039]
  decide +kernel

theorem arows10057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10057 = true := by
  rw [show D2M8K2.u10057 = KTree.node D2M8K2.u10049 (nat_lit 21478555) (nat_lit 2118184586) (nat_lit 0) D2M8K2.u10056 from rfl, allE_node, arows10049, irow10057, arows10056]
  all_goals rfl

theorem atot10057 : totK PD2M8K2 D2M8K2.u10057 = [0, 429522638084, 2619176886691, 5853803440964, 4725290825038, 844025719822, 17086344800, 0] := by
  rw [show D2M8K2.u10057 = KTree.node D2M8K2.u10049 (nat_lit 21478555) (nat_lit 2118184586) (nat_lit 0) D2M8K2.u10056 from rfl, totK_node, atot10049, atot10056]
  decide +kernel

theorem arows10072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10072 = true := by
  rw [show D2M8K2.u10072 = KTree.node D2M8K2.u10064 (nat_lit 21498942) (nat_lit 3894796625) (nat_lit 0) D2M8K2.u10071 from rfl, allE_node, arows10064, irow10072, arows10071]
  all_goals rfl

theorem atot10072 : totK PD2M8K2 D2M8K2.u10072 = [0, 1232505077197, 5144594467650, 6126765010468, 1910683289825, 101883565951, 0, 0] := by
  rw [show D2M8K2.u10072 = KTree.node D2M8K2.u10064 (nat_lit 21498942) (nat_lit 3894796625) (nat_lit 0) D2M8K2.u10071 from rfl, totK_node, atot10064, atot10071]
  decide +kernel

theorem arows10088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10088 = true := by
  rw [show D2M8K2.u10088 = KTree.node D2M8K2.u10080 (nat_lit 21521641) (nat_lit 1381672875) (nat_lit 0) D2M8K2.u10087 from rfl, allE_node, arows10080, irow10088, arows10087]
  all_goals rfl

theorem atot10088 : totK PD2M8K2 D2M8K2.u10088 = [0, 772198506418, 3796324581068, 6121538614168, 3323196834475, 405111293907, 7048116272, 0] := by
  rw [show D2M8K2.u10088 = KTree.node D2M8K2.u10080 (nat_lit 21521641) (nat_lit 1381672875) (nat_lit 0) D2M8K2.u10087 from rfl, totK_node, atot10080, atot10087]
  decide +kernel

theorem arows10103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10103 = true := by
  rw [show D2M8K2.u10103 = KTree.node D2M8K2.u10095 (nat_lit 21540694) (nat_lit 2080839580) (nat_lit 0) D2M8K2.u10102 from rfl, allE_node, arows10095, irow10103, arows10102]
  all_goals rfl

theorem atot10103 : totK PD2M8K2 D2M8K2.u10103 = [0, 1270563575864, 4969270798429, 5923731194325, 2114557127790, 169755052204, 1239866073, 0] := by
  rw [show D2M8K2.u10103 = KTree.node D2M8K2.u10095 (nat_lit 21540694) (nat_lit 2080839580) (nat_lit 0) D2M8K2.u10102 from rfl, totK_node, atot10095, atot10102]
  decide +kernel

theorem arows10121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10121 = true := by
  rw [show D2M8K2.u10121 = KTree.node D2M8K2.u10113 (nat_lit 21559706) (nat_lit 4225304539) (nat_lit 0) D2M8K2.u10120 from rfl, allE_node, arows10113, irow10121, arows10120]
  all_goals rfl

theorem atot10121 : totK PD2M8K2 D2M8K2.u10121 = [0, 502750546267, 3187952717501, 6189858624269, 3877535956586, 584085088014, 17826068843, 0] := by
  rw [show D2M8K2.u10121 = KTree.node D2M8K2.u10113 (nat_lit 21559706) (nat_lit 4225304539) (nat_lit 0) D2M8K2.u10120 from rfl, totK_node, atot10113, atot10120]
  decide +kernel

theorem arows10136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10136 = true := by
  rw [show D2M8K2.u10136 = KTree.node D2M8K2.u10128 (nat_lit 21576201) (nat_lit 1895681444) (nat_lit 0) D2M8K2.u10135 from rfl, allE_node, arows10128, irow10136, arows10135]
  all_goals rfl

theorem atot10136 : totK PD2M8K2 D2M8K2.u10136 = [0, 1484733917016, 5569473921612, 5807158954473, 1523212239005, 69088136509, 0, 0] := by
  rw [show D2M8K2.u10136 = KTree.node D2M8K2.u10128 (nat_lit 21576201) (nat_lit 1895681444) (nat_lit 0) D2M8K2.u10135 from rfl, totK_node, atot10128, atot10135]
  decide +kernel

theorem arows10152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10152 = true := by
  rw [show D2M8K2.u10152 = KTree.node D2M8K2.u10144 (nat_lit 21600083) (nat_lit 2344752133) (nat_lit 0) D2M8K2.u10151 from rfl, allE_node, arows10144, irow10152, arows10151]
  all_goals rfl

theorem atot10152 : totK PD2M8K2 D2M8K2.u10152 = [0, 593742132755, 3646977470849, 6561697186693, 3255265180262, 339000737446, 4977114383, 0] := by
  rw [show D2M8K2.u10152 = KTree.node D2M8K2.u10144 (nat_lit 21600083) (nat_lit 2344752133) (nat_lit 0) D2M8K2.u10151 from rfl, totK_node, atot10144, atot10151]
  decide +kernel

theorem arows10167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10167 = true := by
  rw [show D2M8K2.u10167 = KTree.node D2M8K2.u10159 (nat_lit 21617814) (nat_lit 3776270647) (nat_lit 0) D2M8K2.u10166 from rfl, allE_node, arows10159, irow10167, arows10166]
  all_goals rfl

theorem atot10167 : totK PD2M8K2 D2M8K2.u10167 = [0, 1405595642129, 5428125977587, 5930038730721, 1671987014015, 82327748537, 0, 0] := by
  rw [show D2M8K2.u10167 = KTree.node D2M8K2.u10159 (nat_lit 21617814) (nat_lit 3776270647) (nat_lit 0) D2M8K2.u10166 from rfl, totK_node, atot10159, atot10166]
  decide +kernel

theorem arows10184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10184 = true := by
  rw [show D2M8K2.u10184 = KTree.node D2M8K2.u10176 (nat_lit 21637509) (nat_lit 1265713983) (nat_lit 2) D2M8K2.u10183 from rfl, allE_node, arows10176, irow10184, arows10183]
  all_goals rfl

theorem atot10184 : totK PD2M8K2 D2M8K2.u10184 = [0, 0, 1921796583250, 6455228902292, 5264671942935, 791259095289, 13867621213, 0] := by
  rw [show D2M8K2.u10184 = KTree.node D2M8K2.u10176 (nat_lit 21637509) (nat_lit 1265713983) (nat_lit 2) D2M8K2.u10183 from rfl, totK_node, atot10176, atot10183]
  decide +kernel

theorem arows10199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10199 = true := by
  rw [show D2M8K2.u10199 = KTree.node D2M8K2.u10191 (nat_lit 22405760) (nat_lit 3651216029) (nat_lit 0) D2M8K2.u10198 from rfl, allE_node, arows10191, irow10199, arows10198]
  all_goals rfl

theorem atot10199 : totK PD2M8K2 D2M8K2.u10199 = [0, 1749318396885, 5995208992901, 5298918294911, 1143228282399, 151712150595, 11893557120, 0] := by
  rw [show D2M8K2.u10199 = KTree.node D2M8K2.u10191 (nat_lit 22405760) (nat_lit 3651216029) (nat_lit 0) D2M8K2.u10198 from rfl, totK_node, atot10191, atot10198]
  decide +kernel

theorem arows10215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10215 = true := by
  rw [show D2M8K2.u10215 = KTree.node D2M8K2.u10207 (nat_lit 22423304) (nat_lit 3634870933) (nat_lit 0) D2M8K2.u10214 from rfl, allE_node, arows10207, irow10215, arows10214]
  all_goals rfl

theorem atot10215 : totK PD2M8K2 D2M8K2.u10215 = [0, 350798175759, 3294135100887, 6986686357455, 3333173399454, 241123210049, 1369150432, 0] := by
  rw [show D2M8K2.u10215 = KTree.node D2M8K2.u10207 (nat_lit 22423304) (nat_lit 3634870933) (nat_lit 0) D2M8K2.u10214 from rfl, totK_node, atot10207, atot10214]
  decide +kernel

theorem arows10230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10230 = true := by
  rw [show D2M8K2.u10230 = KTree.node D2M8K2.u10222 (nat_lit 22447064) (nat_lit 3632739509) (nat_lit 0) D2M8K2.u10229 from rfl, allE_node, arows10222, irow10230, arows10229]
  all_goals rfl

theorem atot10230 : totK PD2M8K2 D2M8K2.u10230 = [0, 1616091591990, 5766541087739, 5713931572713, 1410834687392, 62734004424, 0, 0] := by
  rw [show D2M8K2.u10230 = KTree.node D2M8K2.u10222 (nat_lit 22447064) (nat_lit 3632739509) (nat_lit 0) D2M8K2.u10229 from rfl, totK_node, atot10222, atot10229]
  decide +kernel

theorem arows10252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10252 = true := by
  rw [show D2M8K2.u10252 = KTree.node D2M8K2.u10244 (nat_lit 22463540) (nat_lit 3703361260) (nat_lit 0) D2M8K2.u10251 from rfl, allE_node, arows10244, irow10252, arows10251]
  all_goals rfl

theorem atot10252 : totK PD2M8K2 D2M8K2.u10252 = [0, 318671753230, 2627965667495, 6029818359844, 4566265426734, 938887288577, 36939166207, 0] := by
  rw [show D2M8K2.u10252 = KTree.node D2M8K2.u10244 (nat_lit 22463540) (nat_lit 3703361260) (nat_lit 0) D2M8K2.u10251 from rfl, totK_node, atot10244, atot10251]
  decide +kernel

theorem arows10267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10267 = true := by
  rw [show D2M8K2.u10267 = KTree.node D2M8K2.u10259 (nat_lit 22520287) (nat_lit 2358555796) (nat_lit 0) D2M8K2.u10266 from rfl, allE_node, arows10259, irow10267, arows10266]
  all_goals rfl

theorem atot10267 : totK PD2M8K2 D2M8K2.u10267 = [0, 1019893117282, 4022073894454, 5661868375595, 3300130738925, 482719921206, 8087477235, 0] := by
  rw [show D2M8K2.u10267 = KTree.node D2M8K2.u10259 (nat_lit 22520287) (nat_lit 2358555796) (nat_lit 0) D2M8K2.u10266 from rfl, totK_node, atot10259, atot10266]
  decide +kernel

theorem arows10283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10283 = true := by
  rw [show D2M8K2.u10283 = KTree.node D2M8K2.u10275 (nat_lit 22536899) (nat_lit 2876481568) (nat_lit 0) D2M8K2.u10282 from rfl, allE_node, arows10275, irow10283, arows10282]
  all_goals rfl

theorem atot10283 : totK PD2M8K2 D2M8K2.u10283 = [0, 1113432628050, 4736142501349, 6075418233937, 2291225121658, 183168041580, 1239866073, 0] := by
  rw [show D2M8K2.u10283 = KTree.node D2M8K2.u10275 (nat_lit 22536899) (nat_lit 2876481568) (nat_lit 0) D2M8K2.u10282 from rfl, totK_node, atot10275, atot10282]
  decide +kernel

theorem arows10298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10298 = true := by
  rw [show D2M8K2.u10298 = KTree.node D2M8K2.u10290 (nat_lit 22555101) (nat_lit 1571021645) (nat_lit 0) D2M8K2.u10297 from rfl, allE_node, arows10290, irow10298, arows10297]
  all_goals rfl

theorem atot10298 : totK PD2M8K2 D2M8K2.u10298 = [0, 499131794211, 3200783301725, 6208961853599, 3802046260871, 570957342331, 17826068843, 0] := by
  rw [show D2M8K2.u10298 = KTree.node D2M8K2.u10290 (nat_lit 22555101) (nat_lit 1571021645) (nat_lit 0) D2M8K2.u10297 from rfl, totK_node, atot10290, atot10297]
  decide +kernel

theorem arows10315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10315 = true := by
  rw [show D2M8K2.u10315 = KTree.node D2M8K2.u10307 (nat_lit 22571560) (nat_lit 2978323691) (nat_lit 0) D2M8K2.u10314 from rfl, allE_node, arows10307, irow10315, arows10314]
  all_goals rfl

theorem atot10315 : totK PD2M8K2 D2M8K2.u10315 = [0, 1512531208039, 5644430067980, 5782654819040, 1455525987138, 60130503646, 0, 0] := by
  rw [show D2M8K2.u10315 = KTree.node D2M8K2.u10307 (nat_lit 22571560) (nat_lit 2978323691) (nat_lit 0) D2M8K2.u10314 from rfl, totK_node, atot10307, atot10314]
  decide +kernel

theorem arows10330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10330 = true := by
  rw [show D2M8K2.u10330 = KTree.node D2M8K2.u10322 (nat_lit 22592872) (nat_lit 2389613731) (nat_lit 0) D2M8K2.u10329 from rfl, allE_node, arows10322, irow10330, arows10329]
  all_goals rfl

theorem atot10330 : totK PD2M8K2 D2M8K2.u10330 = [0, 407653508827, 3148597289668, 6583359431824, 3675771471680, 381371077536, 6115358396, 0] := by
  rw [show D2M8K2.u10330 = KTree.node D2M8K2.u10322 (nat_lit 22592872) (nat_lit 2389613731) (nat_lit 0) D2M8K2.u10329 from rfl, totK_node, atot10322, atot10329]
  decide +kernel

theorem arows10346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10346 = true := by
  rw [show D2M8K2.u10346 = KTree.node D2M8K2.u10338 (nat_lit 22611652) (nat_lit 4016555572) (nat_lit 0) D2M8K2.u10345 from rfl, allE_node, arows10338, irow10346, arows10345]
  all_goals rfl

theorem atot10346 : totK PD2M8K2 D2M8K2.u10346 = [0, 1614745196886, 5770013347463, 5729823481594, 1397919529795, 56963622407, 0, 0] := by
  rw [show D2M8K2.u10346 = KTree.node D2M8K2.u10338 (nat_lit 22611652) (nat_lit 4016555572) (nat_lit 0) D2M8K2.u10345 from rfl, totK_node, atot10338, atot10345]
  decide +kernel

theorem arows10361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10361 = true := by
  rw [show D2M8K2.u10361 = KTree.node D2M8K2.u10353 (nat_lit 22630601) (nat_lit 1634859943) (nat_lit 0) D2M8K2.u10360 from rfl, allE_node, arows10353, irow10361, arows10360]
  all_goals rfl

theorem atot10361 : totK PD2M8K2 D2M8K2.u10361 = [0, 0, 2196366504224, 6818414516482, 4830050660228, 545467506974, 7317347254, 0] := by
  rw [show D2M8K2.u10361 = KTree.node D2M8K2.u10353 (nat_lit 22630601) (nat_lit 1634859943) (nat_lit 0) D2M8K2.u10360 from rfl, totK_node, atot10353, atot10360]
  decide +kernel

theorem arows10379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10379 = true := by
  rw [show D2M8K2.u10379 = KTree.node D2M8K2.u10371 (nat_lit 22653576) (nat_lit 3309413533) (nat_lit 0) D2M8K2.u10378 from rfl, allE_node, arows10371, irow10379, arows10378]
  all_goals rfl

theorem atot10379 : totK PD2M8K2 D2M8K2.u10379 = [0, 0, 1586390311655, 5968059686577, 5583430375648, 1026502067663, 34189567282, 0] := by
  rw [show D2M8K2.u10379 = KTree.node D2M8K2.u10371 (nat_lit 22653576) (nat_lit 3309413533) (nat_lit 0) D2M8K2.u10378 from rfl, totK_node, atot10371, atot10378]
  decide +kernel

theorem arows10394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10394 = true := by
  rw [show D2M8K2.u10394 = KTree.node D2M8K2.u10386 (nat_lit 22671936) (nat_lit 3705351137) (nat_lit 0) D2M8K2.u10393 from rfl, allE_node, arows10386, irow10394, arows10393]
  all_goals rfl

theorem atot10394 : totK PD2M8K2 D2M8K2.u10394 = [0, 0, 623860576530, 3930843886223, 6746150176229, 2655041776400, 193408750559, 1310517177] := by
  rw [show D2M8K2.u10394 = KTree.node D2M8K2.u10386 (nat_lit 22671936) (nat_lit 3705351137) (nat_lit 0) D2M8K2.u10393 from rfl, totK_node, atot10386, atot10393]
  decide +kernel

theorem arows10410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10410 = true := by
  rw [show D2M8K2.u10410 = KTree.node D2M8K2.u10402 (nat_lit 22698264) (nat_lit 3445379399) (nat_lit 0) D2M8K2.u10409 from rfl, allE_node, arows10402, irow10410, arows10409]
  all_goals rfl

theorem atot10410 : totK PD2M8K2 D2M8K2.u10410 = [0, 0, 1811008507396, 6242725867451, 5438631865429, 1090842434090, 42288492385, 0] := by
  rw [show D2M8K2.u10410 = KTree.node D2M8K2.u10402 (nat_lit 22698264) (nat_lit 3445379399) (nat_lit 0) D2M8K2.u10409 from rfl, totK_node, atot10402, atot10409]
  decide +kernel

theorem arows10425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10425 = true := by
  rw [show D2M8K2.u10425 = KTree.node D2M8K2.u10417 (nat_lit 22774875) (nat_lit 3668430525) (nat_lit 0) D2M8K2.u10424 from rfl, allE_node, arows10417, irow10425, arows10424]
  all_goals rfl

theorem atot10425 : totK PD2M8K2 D2M8K2.u10425 = [0, 0, 1699823517277, 5934929316402, 5527537586732, 1185797246962, 49373026444, 0] := by
  rw [show D2M8K2.u10425 = KTree.node D2M8K2.u10417 (nat_lit 22774875) (nat_lit 3668430525) (nat_lit 0) D2M8K2.u10424 from rfl, totK_node, atot10417, atot10424]
  decide +kernel

theorem arows10442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10442 = true := by
  rw [show D2M8K2.u10442 = KTree.node D2M8K2.u10434 (nat_lit 22792652) (nat_lit 3749249132) (nat_lit 0) D2M8K2.u10441 from rfl, allE_node, arows10434, irow10442, arows10441]
  all_goals rfl

theorem atot10442 : totK PD2M8K2 D2M8K2.u10442 = [0, 0, 420691460119, 3182656968930, 6433488118891, 3613235171450, 497307447699, 14322947163] := by
  rw [show D2M8K2.u10442 = KTree.node D2M8K2.u10434 (nat_lit 22792652) (nat_lit 3749249132) (nat_lit 0) D2M8K2.u10441 from rfl, totK_node, atot10434, atot10441]
  decide +kernel

theorem arows10457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10457 = true := by
  rw [show D2M8K2.u10457 = KTree.node D2M8K2.u10449 (nat_lit 22813684) (nat_lit 4069852912) (nat_lit 0) D2M8K2.u10456 from rfl, allE_node, arows10449, irow10457, arows10456]
  all_goals rfl

theorem atot10457 : totK PD2M8K2 D2M8K2.u10457 = [0, 0, 1495933934069, 5363479685747, 5399780195056, 1779570127413, 197875623094, 4630915822] := by
  rw [show D2M8K2.u10457 = KTree.node D2M8K2.u10449 (nat_lit 22813684) (nat_lit 4069852912) (nat_lit 0) D2M8K2.u10456 from rfl, totK_node, atot10449, atot10456]
  decide +kernel

theorem arows10473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10473 = true := by
  rw [show D2M8K2.u10473 = KTree.node D2M8K2.u10465 (nat_lit 22831780) (nat_lit 3476854304) (nat_lit 0) D2M8K2.u10472 from rfl, allE_node, arows10465, irow10473, arows10472]
  all_goals rfl

theorem atot10473 : totK PD2M8K2 D2M8K2.u10473 = [0, 0, 508530557913, 3986947478011, 6864507143256, 2550341543747, 165366657204, 1138244013] := by
  rw [show D2M8K2.u10473 = KTree.node D2M8K2.u10465 (nat_lit 22831780) (nat_lit 3476854304) (nat_lit 0) D2M8K2.u10472 from rfl, totK_node, atot10465, atot10472]
  decide +kernel

theorem arows10488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10488 = true := by
  rw [show D2M8K2.u10488 = KTree.node D2M8K2.u10480 (nat_lit 22856579) (nat_lit 2848308795) (nat_lit 0) D2M8K2.u10487 from rfl, allE_node, arows10480, irow10488, arows10487]
  all_goals rfl

theorem atot10488 : totK PD2M8K2 D2M8K2.u10488 = [0, 0, 1749520505646, 5653288581670, 5181082531801, 1631036218094, 187724908170, 4914284239] := by
  rw [show D2M8K2.u10488 = KTree.node D2M8K2.u10480 (nat_lit 22856579) (nat_lit 2848308795) (nat_lit 0) D2M8K2.u10487 from rfl, totK_node, atot10480, atot10487]
  decide +kernel

theorem arows10507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10507 = true := by
  rw [show D2M8K2.u10507 = KTree.node D2M8K2.u10499 (nat_lit 22899938) (nat_lit 4082836940) (nat_lit 0) D2M8K2.u10506 from rfl, allE_node, arows10499, irow10507, arows10506]
  all_goals rfl

theorem atot10507 : totK PD2M8K2 D2M8K2.u10507 = [0, 1385741874981, 4993567361626, 5402484905778, 2203935338541, 372238808617, 14338667495, 0] := by
  rw [show D2M8K2.u10507 = KTree.node D2M8K2.u10499 (nat_lit 22899938) (nat_lit 4082836940) (nat_lit 0) D2M8K2.u10506 from rfl, totK_node, atot10499, atot10506]
  decide +kernel

theorem arows10522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10522 = true := by
  rw [show D2M8K2.u10522 = KTree.node D2M8K2.u10514 (nat_lit 22914534) (nat_lit 3793660679) (nat_lit 0) D2M8K2.u10521 from rfl, allE_node, arows10514, irow10522, arows10521]
  all_goals rfl

theorem atot10522 : totK PD2M8K2 D2M8K2.u10522 = [0, 588178319076, 3817899155485, 6656602330308, 2888377613859, 225151772725, 1369150432, 0] := by
  rw [show D2M8K2.u10522 = KTree.node D2M8K2.u10514 (nat_lit 22914534) (nat_lit 3793660679) (nat_lit 0) D2M8K2.u10521 from rfl, totK_node, atot10514, atot10521]
  decide +kernel

theorem arows10538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10538 = true := by
  rw [show D2M8K2.u10538 = KTree.node D2M8K2.u10530 (nat_lit 22941613) (nat_lit 1104181896) (nat_lit 0) D2M8K2.u10537 from rfl, allE_node, arows10530, irow10538, arows10537]
  all_goals rfl

theorem atot10538 : totK PD2M8K2 D2M8K2.u10538 = [0, 1487019530621, 5410392935969, 5855955384725, 1712352823007, 82128970039, 0, 0] := by
  rw [show D2M8K2.u10538 = KTree.node D2M8K2.u10530 (nat_lit 22941613) (nat_lit 1104181896) (nat_lit 0) D2M8K2.u10537 from rfl, totK_node, atot10530, atot10537]
  decide +kernel

theorem arows10553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10553 = true := by
  rw [show D2M8K2.u10553 = KTree.node D2M8K2.u10545 (nat_lit 22959578) (nat_lit 4004871190) (nat_lit 0) D2M8K2.u10552 from rfl, allE_node, arows10545, irow10553, arows10552]
  all_goals rfl

theorem atot10553 : totK PD2M8K2 D2M8K2.u10553 = [0, 511116253781, 3359722659397, 6286972999979, 3773485972114, 631211886786, 19209646827, 0] := by
  rw [show D2M8K2.u10553 = KTree.node D2M8K2.u10545 (nat_lit 22959578) (nat_lit 4004871190) (nat_lit 0) D2M8K2.u10552 from rfl, totK_node, atot10545, atot10552]
  decide +kernel

theorem arows10570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10570 = true := by
  rw [show D2M8K2.u10570 = KTree.node D2M8K2.u10562 (nat_lit 22977196) (nat_lit 3802030753) (nat_lit 0) D2M8K2.u10569 from rfl, allE_node, arows10562, irow10570, arows10569]
  all_goals rfl

theorem atot10570 : totK PD2M8K2 D2M8K2.u10570 = [0, 1228371848836, 4759665021945, 5744525418287, 2513934835239, 278895641841, 2602082993, 0] := by
  rw [show D2M8K2.u10570 = KTree.node D2M8K2.u10562 (nat_lit 22977196) (nat_lit 3802030753) (nat_lit 0) D2M8K2.u10569 from rfl, totK_node, atot10562, atot10569]
  decide +kernel

theorem arows10585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10585 = true := by
  rw [show D2M8K2.u10585 = KTree.node D2M8K2.u10577 (nat_lit 22998217) (nat_lit 1448625263) (nat_lit 0) D2M8K2.u10584 from rfl, allE_node, arows10577, irow10585, arows10584]
  all_goals rfl

theorem atot10585 : totK PD2M8K2 D2M8K2.u10585 = [0, 423287068518, 3498139837328, 6859517472123, 3212373955594, 255203495599, 2228066420, 0] := by
  rw [show D2M8K2.u10585 = KTree.node D2M8K2.u10577 (nat_lit 22998217) (nat_lit 1448625263) (nat_lit 0) D2M8K2.u10584 from rfl, totK_node, atot10577, atot10584]
  decide +kernel

theorem arows10601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10601 = true := by
  rw [show D2M8K2.u10601 = KTree.node D2M8K2.u10593 (nat_lit 23023106) (nat_lit 4027104210) (nat_lit 0) D2M8K2.u10600 from rfl, allE_node, arows10593, irow10601, arows10600]
  all_goals rfl

theorem atot10601 : totK PD2M8K2 D2M8K2.u10601 = [0, 1691140256646, 5657328487059, 5372172266766, 1583528142670, 142465634175, 3552795014, 0] := by
  rw [show D2M8K2.u10601 = KTree.node D2M8K2.u10593 (nat_lit 23023106) (nat_lit 4027104210) (nat_lit 0) D2M8K2.u10600 from rfl, totK_node, atot10593, atot10600]
  decide +kernel

theorem arows10616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10616 = true := by
  rw [show D2M8K2.u10616 = KTree.node D2M8K2.u10608 (nat_lit 23040605) (nat_lit 1472381966) (nat_lit 0) D2M8K2.u10615 from rfl, allE_node, arows10608, irow10616, arows10615]
  all_goals rfl

theorem atot10616 : totK PD2M8K2 D2M8K2.u10616 = [0, 345725408665, 3084495539073, 6554224694646, 3837237952346, 515333997023, 14345316470, 0] := by
  rw [show D2M8K2.u10616 = KTree.node D2M8K2.u10608 (nat_lit 23040605) (nat_lit 1472381966) (nat_lit 0) D2M8K2.u10615 from rfl, totK_node, atot10608, atot10615]
  decide +kernel

end QECKChecks.D2M8K2
