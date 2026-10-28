import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A0

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows1196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1196 = true := by
  rw [show A10K2.u1196 = KTree.node A10K2.t1200 (nat_lit 17100166) (nat_lit 16058976194) (nat_lit 0) A10K2.t1201 from rfl, allE_node, rows1200, irow1196, rows1201]
  all_goals rfl

theorem atot1196 : totK PA10K2 A10K2.u1196 = [0, 0, 323447547955, 1902017578254, 3806506977148, 2918123253956, 872360365927, 137477593114, 5528811039, 0] := by
  rw [show A10K2.u1196 = KTree.node A10K2.t1200 (nat_lit 17100166) (nat_lit 16058976194) (nat_lit 0) A10K2.t1201 from rfl, totK_node, tot1200, tot1201]
  decide +kernel

theorem arows1197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1197 = true := by
  rw [show A10K2.u1197 = KTree.node A10K2.t1202 (nat_lit 17174542) (nat_lit 13887827825) (nat_lit 0) A10K2.t1203 from rfl, allE_node, rows1202, irow1197, rows1203]
  all_goals rfl

theorem atot1197 : totK PA10K2 A10K2.u1197 = [0, 0, 477695379004, 2365246070410, 3932981179312, 2359334277648, 451317249814, 25371180993, 0, 0] := by
  rw [show A10K2.u1197 = KTree.node A10K2.t1202 (nat_lit 17174542) (nat_lit 13887827825) (nat_lit 0) A10K2.t1203 from rfl, totK_node, tot1202, tot1203]
  decide +kernel

theorem arows1199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1199 = true := by
  rw [show A10K2.u1199 = KTree.node A10K2.t1204 (nat_lit 17181341) (nat_lit 5871199034) (nat_lit 0) A10K2.t1205 from rfl, allE_node, rows1204, irow1199, rows1205]
  all_goals rfl

theorem atot1199 : totK PA10K2 A10K2.u1199 = [0, 0, 636214540601, 2702507677686, 3728961924224, 1859902325392, 258643005977, 11494708454, 0, 0] := by
  rw [show A10K2.u1199 = KTree.node A10K2.t1204 (nat_lit 17181341) (nat_lit 5871199034) (nat_lit 0) A10K2.t1205 from rfl, totK_node, tot1204, tot1205]
  decide +kernel

theorem arows1200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1200 = true := by
  rw [show A10K2.u1200 = KTree.node A10K2.t1206 (nat_lit 17189082) (nat_lit 13738595369) (nat_lit 0) A10K2.t1207 from rfl, allE_node, rows1206, irow1200, rows1207]
  all_goals rfl

theorem atot1200 : totK PA10K2 A10K2.u1200 = [0, 0, 562075759590, 2827709549247, 4110250886086, 1533690068418, 102977770523, 0, 0, 0] := by
  rw [show A10K2.u1200 = KTree.node A10K2.t1206 (nat_lit 17189082) (nat_lit 13738595369) (nat_lit 0) A10K2.t1207 from rfl, totK_node, tot1206, tot1207]
  decide +kernel

theorem arows1203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1203 = true := by
  rw [show A10K2.u1203 = KTree.node A10K2.t1208 (nat_lit 17204064) (nat_lit 12641673887) (nat_lit 0) A10K2.t1209 from rfl, allE_node, rows1208, irow1203, rows1209]
  all_goals rfl

theorem atot1203 : totK PA10K2 A10K2.u1203 = [0, 0, 0, 1038424569945, 3773825229612, 3705676700836, 891839910560, 44905858284, 0, 0] := by
  rw [show A10K2.u1203 = KTree.node A10K2.t1208 (nat_lit 17204064) (nat_lit 12641673887) (nat_lit 0) A10K2.t1209 from rfl, totK_node, tot1208, tot1209]
  decide +kernel

theorem arows1204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1204 = true := by
  rw [show A10K2.u1204 = KTree.node A10K2.t1210 (nat_lit 17220151) (nat_lit 11315197261) (nat_lit 0) A10K2.t1211 from rfl, allE_node, rows1210, irow1204, rows1211]
  all_goals rfl

theorem atot1204 : totK PA10K2 A10K2.u1204 = [0, 0, 0, 1140875167124, 3890015141811, 3346093654483, 639482980963, 36877445968, 0, 0] := by
  rw [show A10K2.u1204 = KTree.node A10K2.t1210 (nat_lit 17220151) (nat_lit 11315197261) (nat_lit 0) A10K2.t1211 from rfl, totK_node, tot1210, tot1211]
  decide +kernel

theorem arows1206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1206 = true := by
  rw [show A10K2.u1206 = KTree.node A10K2.t1212 (nat_lit 17226529) (nat_lit 9254403485) (nat_lit 0) A10K2.t1213 from rfl, allE_node, rows1212, irow1206, rows1213]
  all_goals rfl

theorem atot1206 : totK PA10K2 A10K2.u1206 = [0, 0, 509695482927, 1852428605178, 2663846531091, 2749658074067, 1327393222235, 192289909650, 5676195732, 0] := by
  rw [show A10K2.u1206 = KTree.node A10K2.t1212 (nat_lit 17226529) (nat_lit 9254403485) (nat_lit 0) A10K2.t1213 from rfl, totK_node, tot1212, tot1213]
  decide +kernel

theorem arows1207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1207 = true := by
  rw [show A10K2.u1207 = KTree.node A10K2.t1214 (nat_lit 17240518) (nat_lit 15443883701) (nat_lit 0) A10K2.t1215 from rfl, allE_node, rows1214, irow1207, rows1215]
  all_goals rfl

theorem atot1207 : totK PA10K2 A10K2.u1207 = [0, 0, 489744119901, 2350632034662, 4070062852350, 2519856409390, 464423159166, 25313348169, 0, 0] := by
  rw [show A10K2.u1207 = KTree.node A10K2.t1214 (nat_lit 17240518) (nat_lit 15443883701) (nat_lit 0) A10K2.t1215 from rfl, totK_node, tot1214, tot1215]
  decide +kernel

theorem arows1213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1213 = true := by
  rw [show A10K2.u1213 = KTree.node A10K2.t1216 (nat_lit 17249751) (nat_lit 13842018497) (nat_lit 0) A10K2.t1217 from rfl, allE_node, rows1216, irow1213, rows1217]
  all_goals rfl

theorem atot1213 : totK PA10K2 A10K2.u1213 = [0, 0, 664848264673, 3055284640580, 4334180623249, 1893974331297, 168824033057, 0, 0, 0] := by
  rw [show A10K2.u1213 = KTree.node A10K2.t1216 (nat_lit 17249751) (nat_lit 13842018497) (nat_lit 0) A10K2.t1217 from rfl, totK_node, tot1216, tot1217]
  decide +kernel

theorem arows1214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1214 = true := by
  rw [show A10K2.u1214 = KTree.node A10K2.t1218 (nat_lit 17264571) (nat_lit 6741306537) (nat_lit 0) A10K2.t1219 from rfl, allE_node, rows1218, irow1214, rows1219]
  all_goals rfl

theorem atot1214 : totK PA10K2 A10K2.u1214 = [0, 0, 459692373802, 2372101946903, 4079549448009, 2616470274476, 444591122451, 6853348008, 0, 0] := by
  rw [show A10K2.u1214 = KTree.node A10K2.t1218 (nat_lit 17264571) (nat_lit 6741306537) (nat_lit 0) A10K2.t1219 from rfl, totK_node, tot1218, tot1219]
  decide +kernel

theorem arows1216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1216 = true := by
  rw [show A10K2.u1216 = KTree.node A10K2.t1220 (nat_lit 17826262) (nat_lit 13992184684) (nat_lit 0) A10K2.t1221 from rfl, allE_node, rows1220, irow1216, rows1221]
  all_goals rfl

theorem atot1216 : totK PA10K2 A10K2.u1216 = [0, 771441390893, 2571280111629, 2720920599695, 1748248417493, 1407706502292, 524050951125, 41417404726, 0, 0] := by
  rw [show A10K2.u1216 = KTree.node A10K2.t1220 (nat_lit 17826262) (nat_lit 13992184684) (nat_lit 0) A10K2.t1221 from rfl, totK_node, tot1220, tot1221]
  decide +kernel

theorem arows1217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1217 = true := by
  rw [show A10K2.u1217 = KTree.node A10K2.t1222 (nat_lit 17830834) (nat_lit 10256844461) (nat_lit 0) A10K2.t1223 from rfl, allE_node, rows1222, irow1217, rows1223]
  all_goals rfl

theorem atot1217 : totK PA10K2 A10K2.u1217 = [0, 282968503005, 1860443540091, 3919073897858, 2901046370837, 592000020531, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1217 = KTree.node A10K2.t1222 (nat_lit 17830834) (nat_lit 10256844461) (nat_lit 0) A10K2.t1223 from rfl, totK_node, tot1222, tot1223]
  decide +kernel

theorem arows1220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1220 = true := by
  rw [show A10K2.u1220 = KTree.node A10K2.t1224 (nat_lit 17844460) (nat_lit 12052466929) (nat_lit 0) A10K2.t1225 from rfl, allE_node, rows1224, irow1220, rows1225]
  all_goals rfl

theorem atot1220 : totK PA10K2 A10K2.u1220 = [0, 546825224965, 2839113027497, 4178903136566, 1688351641829, 139111221237, 0, 0, 0, 0] := by
  rw [show A10K2.u1220 = KTree.node A10K2.t1224 (nat_lit 17844460) (nat_lit 12052466929) (nat_lit 0) A10K2.t1225 from rfl, totK_node, tot1224, tot1225]
  decide +kernel

theorem arows1221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1221 = true := by
  rw [show A10K2.u1221 = KTree.node A10K2.t1226 (nat_lit 17853446) (nat_lit 15385015361) (nat_lit 0) A10K2.t1227 from rfl, allE_node, rows1226, irow1221, rows1227]
  all_goals rfl

theorem atot1221 : totK PA10K2 A10K2.u1221 = [0, 590238606807, 2612315177432, 4068713054364, 2290530767806, 340970510390, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1221 = KTree.node A10K2.t1226 (nat_lit 17853446) (nat_lit 15385015361) (nat_lit 0) A10K2.t1227 from rfl, totK_node, tot1226, tot1227]
  decide +kernel

theorem arows1223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1223 = true := by
  rw [show A10K2.u1223 = KTree.node A10K2.t1228 (nat_lit 17858915) (nat_lit 6661633067) (nat_lit 0) A10K2.t1229 from rfl, allE_node, rows1228, irow1223, rows1229]
  all_goals rfl

theorem atot1223 : totK PA10K2 A10K2.u1223 = [0, 0, 981740253274, 3595822532669, 3958023508417, 1203324317649, 79386959837, 0, 0, 0] := by
  rw [show A10K2.u1223 = KTree.node A10K2.t1228 (nat_lit 17858915) (nat_lit 6661633067) (nat_lit 0) A10K2.t1229 from rfl, totK_node, tot1228, tot1229]
  decide +kernel

theorem arows1224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1224 = true := by
  rw [show A10K2.u1224 = KTree.node A10K2.t1230 (nat_lit 17863521) (nat_lit 8982664201) (nat_lit 0) A10K2.t1231 from rfl, allE_node, rows1230, irow1224, rows1231]
  all_goals rfl

theorem atot1224 : totK PA10K2 A10K2.u1224 = [0, 0, 360245241240, 2010691114975, 3883324788057, 2634206961147, 549802920840, 30650496230, 0, 0] := by
  rw [show A10K2.u1224 = KTree.node A10K2.t1230 (nat_lit 17863521) (nat_lit 8982664201) (nat_lit 0) A10K2.t1231 from rfl, totK_node, tot1230, tot1231]
  decide +kernel

theorem arows1228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1228 = true := by
  rw [show A10K2.u1228 = KTree.node A10K2.t1232 (nat_lit 17877271) (nat_lit 5581823672) (nat_lit 0) A10K2.t1233 from rfl, allE_node, rows1232, irow1228, rows1233]
  all_goals rfl

theorem atot1228 : totK PA10K2 A10K2.u1228 = [0, 0, 545857178586, 2978661264060, 4245400172489, 1496861243137, 102848315895, 0, 0, 0] := by
  rw [show A10K2.u1228 = KTree.node A10K2.t1232 (nat_lit 17877271) (nat_lit 5581823672) (nat_lit 0) A10K2.t1233 from rfl, totK_node, tot1232, tot1233]
  decide +kernel

theorem arows1229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1229 = true := by
  rw [show A10K2.u1229 = KTree.node A10K2.t1234 (nat_lit 17886592) (nat_lit 14919532568) (nat_lit 0) A10K2.t1235 from rfl, allE_node, rows1234, irow1229, rows1235]
  all_goals rfl

theorem atot1229 : totK PA10K2 A10K2.u1229 = [0, 293929698888, 1596585936268, 3232077817044, 3175844925275, 1380360628982, 190464261206, 5546304973, 0, 0] := by
  rw [show A10K2.u1229 = KTree.node A10K2.t1234 (nat_lit 17886592) (nat_lit 14919532568) (nat_lit 0) A10K2.t1235 from rfl, totK_node, tot1234, tot1235]
  decide +kernel

theorem arows1231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1231 = true := by
  rw [show A10K2.u1231 = KTree.node A10K2.t1236 (nat_lit 17905876) (nat_lit 11753543645) (nat_lit 0) A10K2.t1237 from rfl, allE_node, rows1236, irow1231, rows1237]
  all_goals rfl

theorem atot1231 : totK PA10K2 A10K2.u1231 = [0, 678735690341, 2861841423190, 3910385429513, 1858920976876, 235547541850, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u1231 = KTree.node A10K2.t1236 (nat_lit 17905876) (nat_lit 11753543645) (nat_lit 0) A10K2.t1237 from rfl, totK_node, tot1236, tot1237]
  decide +kernel

theorem arows1232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1232 = true := by
  rw [show A10K2.u1232 = KTree.node A10K2.t1238 (nat_lit 17912083) (nat_lit 9464056751) (nat_lit 0) A10K2.t1239 from rfl, allE_node, rows1238, irow1232, rows1239]
  all_goals rfl

theorem atot1232 : totK PA10K2 A10K2.u1232 = [0, 329238616492, 2278298615501, 4238387574269, 2236626087963, 316607650388, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1232 = KTree.node A10K2.t1238 (nat_lit 17912083) (nat_lit 9464056751) (nat_lit 0) A10K2.t1239 from rfl, totK_node, tot1238, tot1239]
  decide +kernel

theorem arows1235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1235 = true := by
  rw [show A10K2.u1235 = KTree.node A10K2.t1240 (nat_lit 17940512) (nat_lit 14065094096) (nat_lit 0) A10K2.t1241 from rfl, allE_node, rows1240, irow1235, rows1241]
  all_goals rfl

theorem atot1235 : totK PA10K2 A10K2.u1235 = [0, 0, 1053619390080, 3690145107041, 3750400331754, 998023199056, 64459640452, 0, 0, 0] := by
  rw [show A10K2.u1235 = KTree.node A10K2.t1240 (nat_lit 17940512) (nat_lit 14065094096) (nat_lit 0) A10K2.t1241 from rfl, totK_node, tot1240, tot1241]
  decide +kernel

theorem arows1236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1236 = true := by
  rw [show A10K2.u1236 = KTree.node A10K2.t1242 (nat_lit 17946797) (nat_lit 6561767260) (nat_lit 0) A10K2.t1243 from rfl, allE_node, rows1242, irow1236, rows1243]
  all_goals rfl

theorem atot1236 : totK PA10K2 A10K2.u1236 = [0, 313543329064, 1227219839368, 2649939318843, 3353144739137, 1582195641156, 212595162053, 6121173289, 0, 0] := by
  rw [show A10K2.u1236 = KTree.node A10K2.t1242 (nat_lit 17946797) (nat_lit 6561767260) (nat_lit 0) A10K2.t1243 from rfl, totK_node, tot1242, tot1243]
  decide +kernel

theorem arows1238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1238 = true := by
  rw [show A10K2.u1238 = KTree.node A10K2.t1244 (nat_lit 17961022) (nat_lit 14150203385) (nat_lit 0) A10K2.t1245 from rfl, allE_node, rows1244, irow1238, rows1245]
  all_goals rfl

theorem atot1238 : totK PA10K2 A10K2.u1238 = [0, 440075106148, 2270976363113, 3909606068919, 2475365446695, 472742670267, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u1238 = KTree.node A10K2.t1244 (nat_lit 17961022) (nat_lit 14150203385) (nat_lit 0) A10K2.t1245 from rfl, totK_node, tot1244, tot1245]
  decide +kernel

theorem arows1239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1239 = true := by
  rw [show A10K2.u1239 = KTree.node A10K2.t1246 (nat_lit 17967383) (nat_lit 8624196181) (nat_lit 0) A10K2.t1247 from rfl, allE_node, rows1246, irow1239, rows1247]
  all_goals rfl

theorem atot1239 : totK PA10K2 A10K2.u1239 = [0, 584952430844, 2623204235436, 3759222948256, 1995344538407, 432028250086, 31195026185, 0, 0, 0] := by
  rw [show A10K2.u1239 = KTree.node A10K2.t1246 (nat_lit 17967383) (nat_lit 8624196181) (nat_lit 0) A10K2.t1247 from rfl, totK_node, tot1246, tot1247]
  decide +kernel

theorem arows1244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1244 = true := by
  rw [show A10K2.u1244 = KTree.node A10K2.t1248 (nat_lit 17974084) (nat_lit 12255445192) (nat_lit 0) A10K2.t1249 from rfl, allE_node, rows1248, irow1244, rows1249]
  all_goals rfl

theorem atot1244 : totK PA10K2 A10K2.u1244 = [0, 821967029087, 3022215162724, 3581206715377, 1638503520348, 233868385437, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u1244 = KTree.node A10K2.t1248 (nat_lit 17974084) (nat_lit 12255445192) (nat_lit 0) A10K2.t1249 from rfl, totK_node, tot1248, tot1249]
  decide +kernel

theorem arows1245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1245 = true := by
  rw [show A10K2.u1245 = KTree.node A10K2.t1250 (nat_lit 17979635) (nat_lit 8121274932) (nat_lit 0) A10K2.t1251 from rfl, allE_node, rows1250, irow1245, rows1251]
  all_goals rfl

theorem atot1245 : totK PA10K2 A10K2.u1245 = [0, 0, 1448812578123, 4191772140526, 3088813094132, 629633242198, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u1245 = KTree.node A10K2.t1250 (nat_lit 17979635) (nat_lit 8121274932) (nat_lit 0) A10K2.t1251 from rfl, totK_node, tot1250, tot1251]
  decide +kernel

theorem arows1247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1247 = true := by
  rw [show A10K2.u1247 = KTree.node A10K2.t1252 (nat_lit 17999137) (nat_lit 8174694861) (nat_lit 0) A10K2.t1253 from rfl, allE_node, rows1252, irow1247, rows1253]
  all_goals rfl

theorem atot1247 : totK PA10K2 A10K2.u1247 = [0, 0, 987482676082, 3713724004071, 3849303720166, 968989178119, 45620856191, 0, 0, 0] := by
  rw [show A10K2.u1247 = KTree.node A10K2.t1252 (nat_lit 17999137) (nat_lit 8174694861) (nat_lit 0) A10K2.t1253 from rfl, totK_node, tot1252, tot1253]
  decide +kernel

theorem arows1248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1248 = true := by
  rw [show A10K2.u1248 = KTree.node A10K2.t1254 (nat_lit 18007873) (nat_lit 5727824131) (nat_lit 0) A10K2.t1255 from rfl, allE_node, rows1254, irow1248, rows1255]
  all_goals rfl

theorem atot1248 : totK PA10K2 A10K2.u1248 = [0, 0, 762234110722, 3258110748886, 3891595257127, 1198092230462, 96882734594, 0, 0, 0] := by
  rw [show A10K2.u1248 = KTree.node A10K2.t1254 (nat_lit 18007873) (nat_lit 5727824131) (nat_lit 0) A10K2.t1255 from rfl, totK_node, tot1254, tot1255]
  decide +kernel

theorem arows1251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1251 = true := by
  rw [show A10K2.u1251 = KTree.node A10K2.t1256 (nat_lit 18088392) (nat_lit 14209543142) (nat_lit 0) A10K2.t1257 from rfl, allE_node, rows1256, irow1251, rows1257]
  all_goals rfl

theorem atot1251 : totK PA10K2 A10K2.u1251 = [0, 0, 755503307546, 2963398154783, 3814238205741, 1672123917472, 251198587141, 6354482628, 0, 0] := by
  rw [show A10K2.u1251 = KTree.node A10K2.t1256 (nat_lit 18088392) (nat_lit 14209543142) (nat_lit 0) A10K2.t1257 from rfl, totK_node, tot1256, tot1257]
  decide +kernel

theorem arows1252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1252 = true := by
  rw [show A10K2.u1252 = KTree.node A10K2.t1258 (nat_lit 18092946) (nat_lit 5197191211) (nat_lit 0) A10K2.t1259 from rfl, allE_node, rows1258, irow1252, rows1259]
  all_goals rfl

theorem atot1252 : totK PA10K2 A10K2.u1252 = [0, 0, 298906586352, 1896511767424, 3922541278543, 2824233710363, 567976604687, 30818366867, 0, 0] := by
  rw [show A10K2.u1252 = KTree.node A10K2.t1258 (nat_lit 18092946) (nat_lit 5197191211) (nat_lit 0) A10K2.t1259 from rfl, totK_node, tot1258, tot1259]
  decide +kernel

theorem arows1254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1254 = true := by
  rw [show A10K2.u1254 = KTree.node A10K2.t1260 (nat_lit 18106636) (nat_lit 12145468572) (nat_lit 0) A10K2.t1261 from rfl, allE_node, rows1260, irow1254, rows1261]
  all_goals rfl

theorem atot1254 : totK PA10K2 A10K2.u1254 = [0, 0, 546825224965, 2871102749682, 4227481928718, 1610348201588, 108474275087, 0, 0, 0] := by
  rw [show A10K2.u1254 = KTree.node A10K2.t1260 (nat_lit 18106636) (nat_lit 12145468572) (nat_lit 0) A10K2.t1261 from rfl, totK_node, tot1260, tot1261]
  decide +kernel

theorem arows1255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1255 = true := by
  rw [show A10K2.u1255 = KTree.node A10K2.t1262 (nat_lit 18115639) (nat_lit 14949959527) (nat_lit 0) A10K2.t1263 from rfl, allE_node, rows1262, irow1255, rows1263]
  all_goals rfl

theorem atot1255 : totK PA10K2 A10K2.u1255 = [0, 0, 590238606807, 2570860655186, 3962055110452, 2316041202306, 387886415507, 13207830636, 0, 0] := by
  rw [show A10K2.u1255 = KTree.node A10K2.t1262 (nat_lit 18115639) (nat_lit 14949959527) (nat_lit 0) A10K2.t1263 from rfl, totK_node, tot1262, tot1263]
  decide +kernel

theorem arows1259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1259 = true := by
  rw [show A10K2.u1259 = KTree.node A10K2.t1264 (nat_lit 18163641) (nat_lit 3471457099) (nat_lit 2) A10K2.t1265 from rfl, allE_node, rows1264, irow1259, rows1265]
  all_goals rfl

theorem atot1259 : totK PA10K2 A10K2.u1259 = [0, 0, 562065748622, 2805060775408, 4265132147174, 1976524597174, 195593285781, 0, 0, 0] := by
  rw [show A10K2.u1259 = KTree.node A10K2.t1264 (nat_lit 18163641) (nat_lit 3471457099) (nat_lit 2) A10K2.t1265 from rfl, totK_node, tot1264, tot1265]
  decide +kernel

theorem arows1260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1260 = true := by
  rw [show A10K2.u1260 = KTree.node A10K2.t1266 (nat_lit 18171538) (nat_lit 15737539539) (nat_lit 0) A10K2.t1267 from rfl, allE_node, rows1266, irow1260, rows1267]
  all_goals rfl

theorem atot1260 : totK PA10K2 A10K2.u1260 = [0, 0, 737208611425, 2964848511249, 3828007927680, 1616026974346, 207568035328, 5718040558, 0, 0] := by
  rw [show A10K2.u1260 = KTree.node A10K2.t1266 (nat_lit 18171538) (nat_lit 15737539539) (nat_lit 0) A10K2.t1267 from rfl, totK_node, tot1266, tot1267]
  decide +kernel

theorem arows1262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1262 = true := by
  rw [show A10K2.u1262 = KTree.node A10K2.t1268 (nat_lit 18219304) (nat_lit 12390657786) (nat_lit 0) A10K2.t1269 from rfl, allE_node, rows1268, irow1262, rows1269]
  all_goals rfl

theorem atot1262 : totK PA10K2 A10K2.u1262 = [0, 0, 648110547450, 2748175185553, 3882629197545, 1859378226827, 273760533875, 6354482628, 0, 0] := by
  rw [show A10K2.u1262 = KTree.node A10K2.t1268 (nat_lit 18219304) (nat_lit 12390657786) (nat_lit 0) A10K2.t1269 from rfl, totK_node, tot1268, tot1269]
  decide +kernel

theorem arows1263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1263 = true := by
  rw [show A10K2.u1263 = KTree.node A10K2.t1270 (nat_lit 18225230) (nat_lit 8851361322) (nat_lit 0) A10K2.t1271 from rfl, allE_node, rows1270, irow1263, rows1271]
  all_goals rfl

theorem atot1263 : totK PA10K2 A10K2.u1263 = [0, 0, 343634230019, 2073806561604, 3928559750016, 2548239552930, 481563738380, 30074883546, 0, 0] := by
  rw [show A10K2.u1263 = KTree.node A10K2.t1270 (nat_lit 18225230) (nat_lit 8851361322) (nat_lit 0) A10K2.t1271 from rfl, totK_node, tot1270, tot1271]
  decide +kernel

theorem arows1266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1266 = true := by
  rw [show A10K2.u1266 = KTree.node A10K2.t1272 (nat_lit 18232677) (nat_lit 7099444323) (nat_lit 0) A10K2.t1273 from rfl, allE_node, rows1272, irow1266, rows1273]
  all_goals rfl

theorem atot1266 : totK PA10K2 A10K2.u1266 = [0, 0, 615448890063, 2778462698667, 3994845994913, 1744389824541, 209001777357, 6034215561, 0, 0] := by
  rw [show A10K2.u1266 = KTree.node A10K2.t1272 (nat_lit 18232677) (nat_lit 7099444323) (nat_lit 0) A10K2.t1273 from rfl, totK_node, tot1272, tot1273]
  decide +kernel

theorem arows1267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1267 = true := by
  rw [show A10K2.u1267 = KTree.node A10K2.t1274 (nat_lit 18237726) (nat_lit 8876014452) (nat_lit 0) A10K2.t1275 from rfl, allE_node, rows1274, irow1267, rows1275]
  all_goals rfl

theorem atot1267 : totK PA10K2 A10K2.u1267 = [0, 0, 548444900956, 2796796261749, 4053824668547, 1611536794268, 137779122608, 0, 0, 0] := by
  rw [show A10K2.u1267 = KTree.node A10K2.t1274 (nat_lit 18237726) (nat_lit 8876014452) (nat_lit 0) A10K2.t1275 from rfl, totK_node, tot1274, tot1275]
  decide +kernel

theorem arows1269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1269 = true := by
  rw [show A10K2.u1269 = KTree.node A10K2.t1276 (nat_lit 18252684) (nat_lit 8615425820) (nat_lit 0) A10K2.t1277 from rfl, allE_node, rows1276, irow1269, rows1277]
  all_goals rfl

theorem atot1269 : totK PA10K2 A10K2.u1269 = [0, 0, 0, 1168081593940, 4006383668402, 3412018326585, 720473990939, 37547833973, 0, 0] := by
  rw [show A10K2.u1269 = KTree.node A10K2.t1276 (nat_lit 18252684) (nat_lit 8615425820) (nat_lit 0) A10K2.t1277 from rfl, totK_node, tot1276, tot1277]
  decide +kernel

theorem arows1270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1270 = true := by
  rw [show A10K2.u1270 = KTree.node A10K2.t1278 (nat_lit 18268928) (nat_lit 14679419171) (nat_lit 0) A10K2.t1279 from rfl, allE_node, rows1278, irow1270, rows1279]
  all_goals rfl

theorem atot1270 : totK PA10K2 A10K2.u1270 = [0, 0, 0, 1143865946332, 3871859422564, 3355479679510, 741104360264, 36913694812, 0, 0] := by
  rw [show A10K2.u1270 = KTree.node A10K2.t1278 (nat_lit 18268928) (nat_lit 14679419171) (nat_lit 0) A10K2.t1279 from rfl, totK_node, tot1278, tot1279]
  decide +kernel

theorem arows1278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1278 = true := by
  rw [show A10K2.u1278 = KTree.node A10K2.t1280 (nat_lit 18275108) (nat_lit 14092073173) (nat_lit 0) A10K2.t1281 from rfl, allE_node, rows1280, irow1278, rows1281]
  all_goals rfl

theorem atot1278 : totK PA10K2 A10K2.u1278 = [0, 548282633765, 1844443093740, 1712622297553, 1318843696470, 2322693914226, 1329129686197, 195382007035, 6354482628, 0] := by
  rw [show A10K2.u1278 = KTree.node A10K2.t1280 (nat_lit 18275108) (nat_lit 14092073173) (nat_lit 0) A10K2.t1281 from rfl, totK_node, tot1280, tot1281]
  decide +kernel

theorem arows1279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1279 = true := by
  rw [show A10K2.u1279 = KTree.node A10K2.t1282 (nat_lit 18354533) (nat_lit 7092176176) (nat_lit 0) A10K2.t1283 from rfl, allE_node, rows1282, irow1279, rows1283]
  all_goals rfl

theorem atot1279 : totK PA10K2 A10K2.u1279 = [0, 295901161011, 1968991100761, 4040853397429, 2792282324948, 567144434603, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1279 = KTree.node A10K2.t1282 (nat_lit 18354533) (nat_lit 7092176176) (nat_lit 0) A10K2.t1283 from rfl, totK_node, tot1282, tot1283]
  decide +kernel

theorem arows1281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1281 = true := by
  rw [show A10K2.u1281 = KTree.node A10K2.t1284 (nat_lit 18368803) (nat_lit 9840604099) (nat_lit 0) A10K2.t1285 from rfl, allE_node, rows1284, irow1281, rows1285]
  all_goals rfl

theorem atot1281 : totK PA10K2 A10K2.u1281 = [0, 554944724842, 2683522878792, 4137210013564, 1968855173375, 195385351232, 0, 0, 0, 0] := by
  rw [show A10K2.u1281 = KTree.node A10K2.t1284 (nat_lit 18368803) (nat_lit 9840604099) (nat_lit 0) A10K2.t1285 from rfl, totK_node, tot1284, tot1285]
  decide +kernel

theorem arows1282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1282 = true := by
  rw [show A10K2.u1282 = KTree.node A10K2.t1286 (nat_lit 18376595) (nat_lit 10520589214) (nat_lit 0) A10K2.t1287 from rfl, allE_node, rows1286, irow1282, rows1287]
  all_goals rfl

theorem atot1282 : totK PA10K2 A10K2.u1282 = [0, 814265487113, 3287513832823, 4082294322699, 1647713815748, 214692128814, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1282 = KTree.node A10K2.t1286 (nat_lit 18376595) (nat_lit 10520589214) (nat_lit 0) A10K2.t1287 from rfl, totK_node, tot1286, tot1287]
  decide +kernel

theorem arows1285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1285 = true := by
  rw [show A10K2.u1285 = KTree.node A10K2.t1288 (nat_lit 18382340) (nat_lit 8872588359) (nat_lit 0) A10K2.t1289 from rfl, allE_node, rows1288, irow1285, rows1289]
  all_goals rfl

theorem atot1285 : totK PA10K2 A10K2.u1285 = [0, 0, 909765577924, 3548000296177, 4176424510945, 1309774131878, 88646843074, 0, 0, 0] := by
  rw [show A10K2.u1285 = KTree.node A10K2.t1288 (nat_lit 18382340) (nat_lit 8872588359) (nat_lit 0) A10K2.t1289 from rfl, totK_node, tot1288, tot1289]
  decide +kernel

theorem arows1286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1286 = true := by
  rw [show A10K2.u1286 = KTree.node A10K2.t1290 (nat_lit 18386938) (nat_lit 8352407585) (nat_lit 0) A10K2.t1291 from rfl, allE_node, rows1290, irow1286, rows1291]
  all_goals rfl

theorem atot1286 : totK PA10K2 A10K2.u1286 = [0, 0, 452231967901, 2345664683283, 3916420599497, 2263155049064, 444418152781, 25239774317, 0, 0] := by
  rw [show A10K2.u1286 = KTree.node A10K2.t1290 (nat_lit 18386938) (nat_lit 8352407585) (nat_lit 0) A10K2.t1291 from rfl, totK_node, tot1290, tot1291]
  decide +kernel

theorem arows1288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1288 = true := by
  rw [show A10K2.u1288 = KTree.node A10K2.t1292 (nat_lit 18401356) (nat_lit 10973051743) (nat_lit 0) A10K2.t1293 from rfl, allE_node, rows1292, irow1288, rows1293]
  all_goals rfl

theorem atot1288 : totK PA10K2 A10K2.u1288 = [0, 0, 552700695999, 2844518621897, 4159211979114, 1720394213700, 201345643143, 5410721913, 0, 0] := by
  rw [show A10K2.u1288 = KTree.node A10K2.t1292 (nat_lit 18401356) (nat_lit 10973051743) (nat_lit 0) A10K2.t1293 from rfl, totK_node, tot1292, tot1293]
  decide +kernel

theorem arows1289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1289 = true := by
  rw [show A10K2.u1289 = KTree.node A10K2.t1294 (nat_lit 18409111) (nat_lit 13435479642) (nat_lit 0) A10K2.t1295 from rfl, allE_node, rows1294, irow1289, rows1295]
  all_goals rfl

theorem atot1289 : totK PA10K2 A10K2.u1289 = [0, 190213598080, 1270686735599, 3211987692497, 3596925555631, 1521056191305, 205449251158, 5546304973, 0, 0] := by
  rw [show A10K2.u1289 = KTree.node A10K2.t1294 (nat_lit 18409111) (nat_lit 13435479642) (nat_lit 0) A10K2.t1295 from rfl, totK_node, tot1294, tot1295]
  decide +kernel

theorem arows1293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1293 = true := by
  rw [show A10K2.u1293 = KTree.node A10K2.t1296 (nat_lit 18427854) (nat_lit 14481618790) (nat_lit 0) A10K2.t1297 from rfl, allE_node, rows1296, irow1293, rows1297]
  all_goals rfl

theorem atot1293 : totK PA10K2 A10K2.u1293 = [0, 524134067440, 2600785977389, 4313790536931, 2446712682603, 355952243221, 8047840951, 0, 0, 0] := by
  rw [show A10K2.u1293 = KTree.node A10K2.t1296 (nat_lit 18427854) (nat_lit 14481618790) (nat_lit 0) A10K2.t1297 from rfl, totK_node, tot1296, tot1297]
  decide +kernel

theorem arows1294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1294 = true := by
  rw [show A10K2.u1294 = KTree.node A10K2.t1298 (nat_lit 18443504) (nat_lit 11169766110) (nat_lit 0) A10K2.t1299 from rfl, allE_node, rows1298, irow1294, rows1299]
  all_goals rfl

theorem atot1294 : totK PA10K2 A10K2.u1294 = [0, 674389369392, 2964228728323, 4195487331397, 2119661303140, 322894314079, 6851704726, 0, 0, 0] := by
  rw [show A10K2.u1294 = KTree.node A10K2.t1298 (nat_lit 18443504) (nat_lit 11169766110) (nat_lit 0) A10K2.t1299 from rfl, totK_node, tot1298, tot1299]
  decide +kernel

theorem arows1296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1296 = true := by
  rw [show A10K2.u1296 = KTree.node A10K2.t1300 (nat_lit 18448370) (nat_lit 13452139763) (nat_lit 0) A10K2.t1301 from rfl, allE_node, rows1300, irow1296, rows1301]
  all_goals rfl

theorem atot1296 : totK PA10K2 A10K2.u1296 = [0, 0, 1059760332455, 3831214418671, 4045652278408, 1224908986948, 82605879954, 0, 0, 0] := by
  rw [show A10K2.u1296 = KTree.node A10K2.t1300 (nat_lit 18448370) (nat_lit 13452139763) (nat_lit 0) A10K2.t1301 from rfl, totK_node, tot1300, tot1301]
  decide +kernel

theorem arows1297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1297 = true := by
  rw [show A10K2.u1297 = KTree.node A10K2.t1302 (nat_lit 18464254) (nat_lit 15270425772) (nat_lit 0) A10K2.t1303 from rfl, allE_node, rows1302, irow1297, rows1303]
  all_goals rfl

theorem atot1297 : totK PA10K2 A10K2.u1297 = [0, 0, 585758096377, 2782803073120, 4292698615220, 2169378289176, 303111133536, 8047840951, 0, 0] := by
  rw [show A10K2.u1297 = KTree.node A10K2.t1302 (nat_lit 18464254) (nat_lit 15270425772) (nat_lit 0) A10K2.t1303 from rfl, totK_node, tot1302, tot1303]
  decide +kernel

theorem arows1300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1300 = true := by
  rw [show A10K2.u1300 = KTree.node A10K2.t1304 (nat_lit 18547268) (nat_lit 11033807994) (nat_lit 0) A10K2.t1305 from rfl, allE_node, rows1304, irow1300, rows1305]
  all_goals rfl

theorem atot1300 : totK PA10K2 A10K2.u1300 = [0, 781939065379, 2921721692607, 3622640195625, 1989131475755, 583166193425, 50555834002, 0, 0, 0] := by
  rw [show A10K2.u1300 = KTree.node A10K2.t1304 (nat_lit 18547268) (nat_lit 11033807994) (nat_lit 0) A10K2.t1305 from rfl, totK_node, tot1304, tot1305]
  decide +kernel

theorem arows1301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1301 = true := by
  rw [show A10K2.u1301 = KTree.node A10K2.t1306 (nat_lit 18553356) (nat_lit 11035756339) (nat_lit 0) A10K2.t1307 from rfl, allE_node, rows1306, irow1301, rows1307]
  all_goals rfl

theorem atot1301 : totK PA10K2 A10K2.u1301 = [0, 323829410999, 1992313542835, 4058005393514, 2853746865667, 582290410113, 30749153377, 0, 0, 0] := by
  rw [show A10K2.u1301 = KTree.node A10K2.t1306 (nat_lit 18553356) (nat_lit 11035756339) (nat_lit 0) A10K2.t1307 from rfl, totK_node, tot1306, tot1307]
  decide +kernel

theorem arows1303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1303 = true := by
  rw [show A10K2.u1303 = KTree.node A10K2.t1308 (nat_lit 18560506) (nat_lit 13255435599) (nat_lit 0) A10K2.t1309 from rfl, allE_node, rows1308, irow1303, rows1309]
  all_goals rfl

theorem atot1303 : totK PA10K2 A10K2.u1303 = [0, 586563934629, 2673700095175, 4106129629025, 2370528129506, 404237299695, 13572172291, 0, 0, 0] := by
  rw [show A10K2.u1303 = KTree.node A10K2.t1308 (nat_lit 18560506) (nat_lit 13255435599) (nat_lit 0) A10K2.t1309 from rfl, totK_node, tot1308, tot1309]
  decide +kernel

theorem arows1304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1304 = true := by
  rw [show A10K2.u1304 = KTree.node A10K2.t1310 (nat_lit 18574732) (nat_lit 7168323857) (nat_lit 0) A10K2.t1311 from rfl, allE_node, rows1310, irow1304, rows1311]
  all_goals rfl

theorem atot1304 : totK PA10K2 A10K2.u1304 = [0, 591413386567, 2705423681053, 4073909057742, 2188726518647, 333109507456, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u1304 = KTree.node A10K2.t1310 (nat_lit 18574732) (nat_lit 7168323857) (nat_lit 0) A10K2.t1311 from rfl, totK_node, tot1310, tot1311]
  decide +kernel

theorem arows1309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1309 = true := by
  rw [show A10K2.u1309 = KTree.node A10K2.t1312 (nat_lit 18579135) (nat_lit 14105813498) (nat_lit 0) A10K2.t1313 from rfl, allE_node, rows1312, irow1309, rows1313]
  all_goals rfl

theorem atot1309 : totK PA10K2 A10K2.u1309 = [0, 0, 1036441888081, 3734822260202, 3835660262304, 1146624484528, 81606090030, 0, 0, 0] := by
  rw [show A10K2.u1309 = KTree.node A10K2.t1312 (nat_lit 18579135) (nat_lit 14105813498) (nat_lit 0) A10K2.t1313 from rfl, totK_node, tot1312, tot1313]
  decide +kernel

theorem arows1310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1310 = true := by
  rw [show A10K2.u1310 = KTree.node A10K2.t1314 (nat_lit 18583916) (nat_lit 10934813971) (nat_lit 0) A10K2.t1315 from rfl, allE_node, rows1314, irow1310, rows1315]
  all_goals rfl

theorem atot1310 : totK PA10K2 A10K2.u1310 = [0, 0, 450930281612, 2423893265158, 4214126762752, 2395813839747, 341679780790, 6904928264, 0, 0] := by
  rw [show A10K2.u1310 = KTree.node A10K2.t1314 (nat_lit 18583916) (nat_lit 10934813971) (nat_lit 0) A10K2.t1315 from rfl, totK_node, tot1314, tot1315]
  decide +kernel

theorem arows1312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1312 = true := by
  rw [show A10K2.u1312 = KTree.node A10K2.t1316 (nat_lit 18591635) (nat_lit 10351364632) (nat_lit 0) A10K2.t1317 from rfl, allE_node, rows1316, irow1312, rows1317]
  all_goals rfl

theorem atot1312 : totK PA10K2 A10K2.u1312 = [0, 0, 580749757853, 2692349719759, 4227910431820, 2307736758758, 299707325676, 7047025452, 0, 0] := by
  rw [show A10K2.u1312 = KTree.node A10K2.t1316 (nat_lit 18591635) (nat_lit 10351364632) (nat_lit 0) A10K2.t1317 from rfl, totK_node, tot1316, tot1317]
  decide +kernel

theorem arows1313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1313 = true := by
  rw [show A10K2.u1313 = KTree.node A10K2.t1318 (nat_lit 18606001) (nat_lit 7628858159) (nat_lit 0) A10K2.t1319 from rfl, allE_node, rows1318, irow1313, rows1319]
  all_goals rfl

theorem atot1313 : totK PA10K2 A10K2.u1313 = [0, 0, 763097835557, 3323993759484, 4180611992934, 1494533772526, 93017162919, 0, 0, 0] := by
  rw [show A10K2.u1313 = KTree.node A10K2.t1318 (nat_lit 18606001) (nat_lit 7628858159) (nat_lit 0) A10K2.t1319 from rfl, totK_node, tot1318, tot1319]
  decide +kernel

theorem arows1316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1316 = true := by
  rw [show A10K2.u1316 = KTree.node A10K2.t1320 (nat_lit 18611648) (nat_lit 14542778814) (nat_lit 0) A10K2.t1321 from rfl, allE_node, rows1320, irow1316, rows1321]
  all_goals rfl

theorem atot1316 : totK PA10K2 A10K2.u1316 = [0, 0, 315335427872, 1664317838848, 3549717223387, 3245513808148, 925453115492, 61110126106, 0, 0] := by
  rw [show A10K2.u1316 = KTree.node A10K2.t1320 (nat_lit 18611648) (nat_lit 14542778814) (nat_lit 0) A10K2.t1321 from rfl, totK_node, tot1320, tot1321]
  decide +kernel

theorem arows1317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1317 = true := by
  rw [show A10K2.u1317 = KTree.node A10K2.t1322 (nat_lit 18616199) (nat_lit 14605439975) (nat_lit 0) A10K2.t1323 from rfl, allE_node, rows1322, irow1317, rows1323]
  all_goals rfl

theorem atot1317 : totK PA10K2 A10K2.u1317 = [0, 0, 528848366904, 2539163122874, 3973589057237, 2164463347986, 412289321733, 25333254304, 0, 0] := by
  rw [show A10K2.u1317 = KTree.node A10K2.t1322 (nat_lit 18616199) (nat_lit 14605439975) (nat_lit 0) A10K2.t1323 from rfl, totK_node, tot1322, tot1323]
  decide +kernel

theorem arows1319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1319 = true := by
  rw [show A10K2.u1319 = KTree.node A10K2.t1324 (nat_lit 18629409) (nat_lit 9826277981) (nat_lit 0) A10K2.t1325 from rfl, allE_node, rows1324, irow1319, rows1325]
  all_goals rfl

theorem atot1319 : totK PA10K2 A10K2.u1319 = [0, 0, 554944724842, 2698062712501, 4060867278165, 2006978389369, 270257946632, 5447185874, 0, 0] := by
  rw [show A10K2.u1319 = KTree.node A10K2.t1324 (nat_lit 18629409) (nat_lit 9826277981) (nat_lit 0) A10K2.t1325 from rfl, totK_node, tot1324, tot1325]
  decide +kernel

theorem arows1320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1320 = true := by
  rw [show A10K2.u1320 = KTree.node A10K2.t1326 (nat_lit 18637979) (nat_lit 10015508161) (nat_lit 0) A10K2.t1327 from rfl, allE_node, rows1326, irow1320, rows1327]
  all_goals rfl

theorem atot1320 : totK PA10K2 A10K2.u1320 = [0, 0, 814265487113, 3153083825884, 4001152884887, 1692038657180, 192779988089, 5705019915, 0, 0] := by
  rw [show A10K2.u1320 = KTree.node A10K2.t1326 (nat_lit 18637979) (nat_lit 10015508161) (nat_lit 0) A10K2.t1327 from rfl, totK_node, tot1326, tot1327]
  decide +kernel

theorem arows1324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1324 = true := by
  rw [show A10K2.u1324 = KTree.node A10K2.t1328 (nat_lit 18644031) (nat_lit 14216893575) (nat_lit 0) A10K2.t1329 from rfl, allE_node, rows1328, irow1324, rows1329]
  all_goals rfl

theorem atot1324 : totK PA10K2 A10K2.u1324 = [0, 0, 0, 1125156873022, 3935249623847, 3943604718000, 1022913575792, 48261347678, 0, 0] := by
  rw [show A10K2.u1324 = KTree.node A10K2.t1328 (nat_lit 18644031) (nat_lit 14216893575) (nat_lit 0) A10K2.t1329 from rfl, totK_node, tot1328, tot1329]
  decide +kernel

theorem arows1325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1325 = true := by
  rw [show A10K2.u1325 = KTree.node A10K2.t1330 (nat_lit 18648566) (nat_lit 16824835909) (nat_lit 0) A10K2.t1331 from rfl, allE_node, rows1330, irow1325, rows1331]
  all_goals rfl

theorem atot1325 : totK PA10K2 A10K2.u1325 = [0, 0, 0, 527472828986, 2650133292170, 4095466973568, 1987322949491, 291179317473, 7007974415, 0] := by
  rw [show A10K2.u1325 = KTree.node A10K2.t1330 (nat_lit 18648566) (nat_lit 16824835909) (nat_lit 0) A10K2.t1331 from rfl, totK_node, tot1330, tot1331]
  decide +kernel

theorem arows1327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1327 = true := by
  rw [show A10K2.u1327 = KTree.node A10K2.t1332 (nat_lit 18663636) (nat_lit 11800462688) (nat_lit 0) A10K2.t1333 from rfl, allE_node, rows1332, irow1327, rows1333]
  all_goals rfl

theorem atot1327 : totK PA10K2 A10K2.u1327 = [0, 0, 0, 962885469432, 3671264211474, 3871187794644, 1063527404870, 60624848455, 0, 0] := by
  rw [show A10K2.u1327 = KTree.node A10K2.t1332 (nat_lit 18663636) (nat_lit 11800462688) (nat_lit 0) A10K2.t1333 from rfl, totK_node, tot1332, tot1333]
  decide +kernel

theorem arows1328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1328 = true := by
  rw [show A10K2.u1328 = KTree.node A10K2.t1334 (nat_lit 18687212) (nat_lit 11668619388) (nat_lit 0) A10K2.t1335 from rfl, allE_node, rows1334, irow1328, rows1335]
  all_goals rfl

theorem atot1328 : totK PA10K2 A10K2.u1328 = [0, 0, 593578530300, 2523726908311, 3861533641267, 2527302468512, 677890054729, 42549660646, 0, 0] := by
  rw [show A10K2.u1328 = KTree.node A10K2.t1334 (nat_lit 18687212) (nat_lit 11668619388) (nat_lit 0) A10K2.t1335 from rfl, totK_node, tot1334, tot1335]
  decide +kernel

theorem arows1331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1331 = true := by
  rw [show A10K2.u1331 = KTree.node A10K2.t1336 (nat_lit 18702400) (nat_lit 15440360366) (nat_lit 0) A10K2.t1337 from rfl, allE_node, rows1336, irow1331, rows1337]
  all_goals rfl

theorem atot1331 : totK PA10K2 A10K2.u1331 = [0, 0, 672014362747, 2812883294923, 4155922010594, 2276132803412, 333564526097, 8047840951, 0, 0] := by
  rw [show A10K2.u1331 = KTree.node A10K2.t1336 (nat_lit 18702400) (nat_lit 15440360366) (nat_lit 0) A10K2.t1337 from rfl, totK_node, tot1336, tot1337]
  decide +kernel

theorem arows1332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1332 = true := by
  rw [show A10K2.u1332 = KTree.node A10K2.t1338 (nat_lit 18707674) (nat_lit 14138365153) (nat_lit 0) A10K2.t1339 from rfl, allE_node, rows1338, irow1332, rows1339]
  all_goals rfl

theorem atot1332 : totK PA10K2 A10K2.u1332 = [0, 0, 121146523123, 1535395647732, 4109466642537, 3617790451952, 843038405060, 25050591743, 0, 0] := by
  rw [show A10K2.u1332 = KTree.node A10K2.t1338 (nat_lit 18707674) (nat_lit 14138365153) (nat_lit 0) A10K2.t1339 from rfl, totK_node, tot1338, tot1339]
  decide +kernel

theorem arows1334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1334 = true := by
  rw [show A10K2.u1334 = KTree.node A10K2.t1340 (nat_lit 18811954) (nat_lit 11212630704) (nat_lit 0) A10K2.t1341 from rfl, allE_node, rows1340, irow1334, rows1341]
  all_goals rfl

theorem atot1334 : totK PA10K2 A10K2.u1334 = [0, 0, 781939065379, 3159310406990, 3970688378518, 1660181055742, 290685490051, 31684545675, 0, 0] := by
  rw [show A10K2.u1334 = KTree.node A10K2.t1340 (nat_lit 18811954) (nat_lit 11212630704) (nat_lit 0) A10K2.t1341 from rfl, totK_node, tot1340, tot1341]
  decide +kernel

theorem arows1335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1335 = true := by
  rw [show A10K2.u1335 = KTree.node A10K2.t1342 (nat_lit 18818450) (nat_lit 15599343304) (nat_lit 0) A10K2.t1343 from rfl, allE_node, rows1342, irow1335, rows1343]
  all_goals rfl

theorem atot1335 : totK PA10K2 A10K2.u1335 = [0, 0, 627685622554, 2752386360747, 4033312010553, 2182735948111, 372543788936, 11991740650, 0, 0] := by
  rw [show A10K2.u1335 = KTree.node A10K2.t1342 (nat_lit 18818450) (nat_lit 15599343304) (nat_lit 0) A10K2.t1343 from rfl, totK_node, tot1342, tot1343]
  decide +kernel

theorem arows1341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1341 = true := by
  rw [show A10K2.u1341 = KTree.node A10K2.t1344 (nat_lit 18833445) (nat_lit 5514511882) (nat_lit 0) A10K2.t1345 from rfl, allE_node, rows1344, irow1341, rows1345]
  all_goals rfl

theorem atot1341 : totK PA10K2 A10K2.u1341 = [0, 0, 542276403629, 2578917136300, 4133504573988, 2373215290021, 328608056233, 7834437697, 0, 0] := by
  rw [show A10K2.u1341 = KTree.node A10K2.t1344 (nat_lit 18833445) (nat_lit 5514511882) (nat_lit 0) A10K2.t1345 from rfl, totK_node, tot1344, tot1345]
  decide +kernel

theorem arows1342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1342 = true := by
  rw [show A10K2.u1342 = KTree.node A10K2.t1346 (nat_lit 18837937) (nat_lit 9522431131) (nat_lit 0) A10K2.t1347 from rfl, allE_node, rows1346, irow1342, rows1347]
  all_goals rfl

theorem atot1342 : totK PA10K2 A10K2.u1342 = [0, 0, 330354438850, 2082453345855, 4191149994244, 2921156295318, 502866782674, 13653259670, 0, 0] := by
  rw [show A10K2.u1342 = KTree.node A10K2.t1346 (nat_lit 18837937) (nat_lit 9522431131) (nat_lit 0) A10K2.t1347 from rfl, totK_node, tot1346, tot1347]
  decide +kernel

theorem arows1344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1344 = true := by
  rw [show A10K2.u1344 = KTree.node A10K2.t1348 (nat_lit 18842504) (nat_lit 14261625976) (nat_lit 0) A10K2.t1349 from rfl, allE_node, rows1348, irow1344, rows1349]
  all_goals rfl

theorem atot1344 : totK PA10K2 A10K2.u1344 = [0, 0, 0, 859315277729, 3407980900479, 4095242458126, 1448850615991, 103725971212, 0, 0] := by
  rw [show A10K2.u1344 = KTree.node A10K2.t1348 (nat_lit 18842504) (nat_lit 14261625976) (nat_lit 0) A10K2.t1349 from rfl, totK_node, tot1348, tot1349]
  decide +kernel

theorem arows1345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1345 = true := by
  rw [show A10K2.u1345 = KTree.node A10K2.t1350 (nat_lit 18851035) (nat_lit 9773256128) (nat_lit 0) A10K2.t1351 from rfl, allE_node, rows1350, irow1345, rows1351]
  all_goals rfl

theorem atot1345 : totK PA10K2 A10K2.u1345 = [0, 0, 0, 769441670379, 2889321984903, 3992872790685, 2014286583223, 264812669342, 6318667960, 0] := by
  rw [show A10K2.u1345 = KTree.node A10K2.t1350 (nat_lit 18851035) (nat_lit 9773256128) (nat_lit 0) A10K2.t1351 from rfl, totK_node, tot1350, tot1351]
  decide +kernel

theorem arows1348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1348 = true := by
  rw [show A10K2.u1348 = KTree.node A10K2.t1352 (nat_lit 18869435) (nat_lit 7104203533) (nat_lit 0) A10K2.t1353 from rfl, allE_node, rows1352, irow1348, rows1353]
  all_goals rfl

theorem atot1348 : totK PA10K2 A10K2.u1348 = [0, 0, 0, 704569041799, 3037536926908, 4079701004037, 1837232950168, 224969046794, 6021244195, 0] := by
  rw [show A10K2.u1348 = KTree.node A10K2.t1352 (nat_lit 18869435) (nat_lit 7104203533) (nat_lit 0) A10K2.t1353 from rfl, totK_node, tot1352, tot1353]
  decide +kernel

theorem arows1349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1349 = true := by
  rw [show A10K2.u1349 = KTree.node A10K2.t1354 (nat_lit 18874661) (nat_lit 7314703828) (nat_lit 0) A10K2.t1355 from rfl, allE_node, rows1354, irow1349, rows1355]
  all_goals rfl

theorem atot1349 : totK PA10K2 A10K2.u1349 = [0, 0, 650522015057, 2199416383490, 2776430636511, 2205428851674, 1553678187919, 445414575463, 29541060178, 0] := by
  rw [show A10K2.u1349 = KTree.node A10K2.t1354 (nat_lit 18874661) (nat_lit 7314703828) (nat_lit 0) A10K2.t1355 from rfl, totK_node, tot1354, tot1355]
  decide +kernel

theorem arows1351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1351 = true := by
  rw [show A10K2.u1351 = KTree.node A10K2.t1356 (nat_lit 18879030) (nat_lit 15422050937) (nat_lit 0) A10K2.t1357 from rfl, allE_node, rows1356, irow1351, rows1357]
  all_goals rfl

theorem atot1351 : totK PA10K2 A10K2.u1351 = [0, 0, 220242025791, 1840013774170, 4078507959544, 2921134493745, 569109472716, 30831673886, 0, 0] := by
  rw [show A10K2.u1351 = KTree.node A10K2.t1356 (nat_lit 18879030) (nat_lit 15422050937) (nat_lit 0) A10K2.t1357 from rfl, totK_node, tot1356, tot1357]
  decide +kernel

theorem arows1352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1352 = true := by
  rw [show A10K2.u1352 = KTree.node A10K2.t1358 (nat_lit 18892856) (nat_lit 13939855257) (nat_lit 0) A10K2.t1359 from rfl, allE_node, rows1358, irow1352, rows1359]
  all_goals rfl

theorem atot1352 : totK PA10K2 A10K2.u1352 = [0, 0, 719208477760, 3082447323503, 3928927468504, 1451330540066, 115260672501, 0, 0, 0] := by
  rw [show A10K2.u1352 = KTree.node A10K2.t1358 (nat_lit 18892856) (nat_lit 13939855257) (nat_lit 0) A10K2.t1359 from rfl, totK_node, tot1358, tot1359]
  decide +kernel

theorem arows1356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1356 = true := by
  rw [show A10K2.u1356 = KTree.node A10K2.t1360 (nat_lit 18899749) (nat_lit 7171887086) (nat_lit 0) A10K2.t1361 from rfl, allE_node, rows1360, irow1356, rows1361]
  all_goals rfl

theorem atot1356 : totK PA10K2 A10K2.u1356 = [0, 0, 777444773176, 3062058001155, 3929310360438, 1691450267575, 218967116117, 6354482628, 0, 0] := by
  rw [show A10K2.u1356 = KTree.node A10K2.t1360 (nat_lit 18899749) (nat_lit 7171887086) (nat_lit 0) A10K2.t1361 from rfl, totK_node, tot1360, tot1361]
  decide +kernel

theorem arows1357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1357 = true := by
  rw [show A10K2.u1357 = KTree.node A10K2.t1362 (nat_lit 18906267) (nat_lit 8001797837) (nat_lit 0) A10K2.t1363 from rfl, allE_node, rows1362, irow1357, rows1363]
  all_goals rfl

theorem atot1357 : totK PA10K2 A10K2.u1357 = [0, 0, 0, 1093844444191, 3875079776882, 3909152080823, 1030832629279, 57613254745, 0, 0] := by
  rw [show A10K2.u1357 = KTree.node A10K2.t1362 (nat_lit 18906267) (nat_lit 8001797837) (nat_lit 0) A10K2.t1363 from rfl, totK_node, tot1362, tot1363]
  decide +kernel

theorem arows1359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1359 = true := by
  rw [show A10K2.u1359 = KTree.node A10K2.t1364 (nat_lit 18910733) (nat_lit 5432516544) (nat_lit 0) A10K2.t1365 from rfl, allE_node, rows1364, irow1359, rows1365]
  all_goals rfl

theorem atot1359 : totK PA10K2 A10K2.u1359 = [0, 0, 0, 547558173663, 2660120247869, 3950503037032, 1980819619126, 390807134767, 25239774317, 0] := by
  rw [show A10K2.u1359 = KTree.node A10K2.t1364 (nat_lit 18910733) (nat_lit 5432516544) (nat_lit 0) A10K2.t1365 from rfl, totK_node, tot1364, tot1365]
  decide +kernel

theorem arows1360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1360 = true := by
  rw [show A10K2.u1360 = KTree.node A10K2.t1366 (nat_lit 18924100) (nat_lit 11135578240) (nat_lit 0) A10K2.t1367 from rfl, allE_node, rows1366, irow1360, rows1367]
  all_goals rfl

theorem atot1360 : totK PA10K2 A10K2.u1360 = [0, 0, 0, 716370652278, 2971868077389, 3762719240638, 1530741036206, 201172776175, 5410721913, 0] := by
  rw [show A10K2.u1360 = KTree.node A10K2.t1366 (nat_lit 18924100) (nat_lit 11135578240) (nat_lit 0) A10K2.t1367 from rfl, totK_node, tot1366, tot1367]
  decide +kernel

theorem arows1363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1363 = true := by
  rw [show A10K2.u1363 = KTree.node A10K2.t1368 (nat_lit 18931724) (nat_lit 10934062318) (nat_lit 0) A10K2.t1369 from rfl, allE_node, rows1368, irow1363, rows1369]
  all_goals rfl

theorem atot1363 : totK PA10K2 A10K2.u1363 = [0, 0, 0, 655315752332, 2889810704687, 3998959573497, 1722268795294, 219178372242, 5546304973, 0] := by
  rw [show A10K2.u1363 = KTree.node A10K2.t1368 (nat_lit 18931724) (nat_lit 10934062318) (nat_lit 0) A10K2.t1369 from rfl, totK_node, tot1368, tot1369]
  decide +kernel

theorem arows1364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1364 = true := by
  rw [show A10K2.u1364 = KTree.node A10K2.t1370 (nat_lit 19006307) (nat_lit 4947214961) (nat_lit 0) A10K2.t1371 from rfl, allE_node, rows1370, irow1364, rows1371]
  all_goals rfl

theorem atot1364 : totK PA10K2 A10K2.u1364 = [0, 0, 798070509296, 3032233761847, 3680689706668, 1834315247141, 499792521920, 36938587266, 0, 0] := by
  rw [show A10K2.u1364 = KTree.node A10K2.t1370 (nat_lit 19006307) (nat_lit 4947214961) (nat_lit 0) A10K2.t1371 from rfl, totK_node, tot1370, tot1371]
  decide +kernel

theorem arows1366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1366 = true := by
  rw [show A10K2.u1366 = KTree.node A10K2.t1372 (nat_lit 19012132) (nat_lit 13357059197) (nat_lit 0) A10K2.t1373 from rfl, allE_node, rows1372, irow1366, rows1373]
  all_goals rfl

theorem atot1366 : totK PA10K2 A10K2.u1366 = [0, 0, 425141663883, 2069785271286, 3662491968243, 2667688203875, 578589686393, 30831673886, 0, 0] := by
  rw [show A10K2.u1366 = KTree.node A10K2.t1372 (nat_lit 19012132) (nat_lit 13357059197) (nat_lit 0) A10K2.t1373 from rfl, totK_node, tot1372, tot1373]
  decide +kernel

theorem arows1367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1367 = true := by
  rw [show A10K2.u1367 = KTree.node A10K2.t1374 (nat_lit 19022087) (nat_lit 9278242836) (nat_lit 0) A10K2.t1375 from rfl, allE_node, rows1374, irow1367, rows1375]
  all_goals rfl

theorem atot1367 : totK PA10K2 A10K2.u1367 = [0, 0, 575216889217, 2660858197703, 3912535045645, 1739391473661, 176556250022, 6034215561, 0, 0] := by
  rw [show A10K2.u1367 = KTree.node A10K2.t1374 (nat_lit 19022087) (nat_lit 9278242836) (nat_lit 0) A10K2.t1375 from rfl, totK_node, tot1374, tot1375]
  decide +kernel

theorem arows1372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1372 = true := by
  rw [show A10K2.u1372 = KTree.node A10K2.t1376 (nat_lit 19027977) (nat_lit 9744604236) (nat_lit 0) A10K2.t1377 from rfl, allE_node, rows1376, irow1372, rows1377]
  all_goals rfl

theorem atot1372 : totK PA10K2 A10K2.u1372 = [0, 0, 182725438514, 1890946882451, 4116983658770, 2586239160163, 455573029461, 26601763172, 0, 0] := by
  rw [show A10K2.u1372 = KTree.node A10K2.t1376 (nat_lit 19027977) (nat_lit 9744604236) (nat_lit 0) A10K2.t1377 from rfl, totK_node, tot1376, tot1377]
  decide +kernel

theorem arows1373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1373 = true := by
  rw [show A10K2.u1373 = KTree.node A10K2.t1378 (nat_lit 19041905) (nat_lit 7534219356) (nat_lit 0) A10K2.t1379 from rfl, allE_node, rows1378, irow1373, rows1379]
  all_goals rfl

theorem atot1373 : totK PA10K2 A10K2.u1373 = [0, 0, 0, 1018676802828, 3753537957428, 3756422336376, 825056298220, 30417306269, 0, 0] := by
  rw [show A10K2.u1373 = KTree.node A10K2.t1378 (nat_lit 19041905) (nat_lit 7534219356) (nat_lit 0) A10K2.t1379 from rfl, totK_node, tot1378, tot1379]
  decide +kernel

theorem arows1375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1375 = true := by
  rw [show A10K2.u1375 = KTree.node A10K2.t1380 (nat_lit 19056819) (nat_lit 8895581923) (nat_lit 0) A10K2.t1381 from rfl, allE_node, rows1380, irow1375, rows1381]
  all_goals rfl

theorem atot1375 : totK PA10K2 A10K2.u1375 = [0, 0, 0, 661333042657, 3135304095302, 4000736304364, 1157666681827, 88572674970, 0, 0] := by
  rw [show A10K2.u1375 = KTree.node A10K2.t1380 (nat_lit 19056819) (nat_lit 8895581923) (nat_lit 0) A10K2.t1381 from rfl, totK_node, tot1380, tot1381]
  decide +kernel

theorem arows1376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1376 = true := by
  rw [show A10K2.u1376 = KTree.node A10K2.t1382 (nat_lit 19073068) (nat_lit 12902780331) (nat_lit 0) A10K2.t1383 from rfl, allE_node, rows1382, irow1376, rows1383]
  all_goals rfl

theorem atot1376 : totK PA10K2 A10K2.u1376 = [0, 0, 811506918617, 2967639947446, 3376968962889, 1712471743468, 690365722486, 135599603508, 5976421810, 0] := by
  rw [show A10K2.u1376 = KTree.node A10K2.t1382 (nat_lit 19073068) (nat_lit 12902780331) (nat_lit 0) A10K2.t1383 from rfl, totK_node, tot1382, tot1383]
  decide +kernel

theorem arows1379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1379 = true := by
  rw [show A10K2.u1379 = KTree.node A10K2.t1384 (nat_lit 19078180) (nat_lit 10617444664) (nat_lit 0) A10K2.t1385 from rfl, allE_node, rows1384, irow1379, rows1385]
  all_goals rfl

theorem atot1379 : totK PA10K2 A10K2.u1379 = [0, 0, 477479145708, 2284927164015, 3998233118414, 2660735676848, 547845164527, 30810868011, 0, 0] := by
  rw [show A10K2.u1379 = KTree.node A10K2.t1384 (nat_lit 19078180) (nat_lit 10617444664) (nat_lit 0) A10K2.t1385 from rfl, totK_node, tot1384, tot1385]
  decide +kernel

theorem arows1380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1380 = true := by
  rw [show A10K2.u1380 = KTree.node A10K2.t1386 (nat_lit 19096497) (nat_lit 9081975783) (nat_lit 0) A10K2.t1387 from rfl, allE_node, rows1386, irow1380, rows1387]
  all_goals rfl

theorem atot1380 : totK PA10K2 A10K2.u1380 = [0, 0, 834236330125, 3388881248144, 4231644433855, 1558392341922, 135366806654, 0, 0, 0] := by
  rw [show A10K2.u1380 = KTree.node A10K2.t1386 (nat_lit 19096497) (nat_lit 9081975783) (nat_lit 0) A10K2.t1387 from rfl, totK_node, tot1386, tot1387]
  decide +kernel

theorem arows1382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1382 = true := by
  rw [show A10K2.u1382 = KTree.node A10K2.t1388 (nat_lit 19102724) (nat_lit 9167801129) (nat_lit 0) A10K2.t1389 from rfl, allE_node, rows1388, irow1382, rows1389]
  all_goals rfl

theorem atot1382 : totK PA10K2 A10K2.u1382 = [0, 0, 0, 1241637112424, 4076083080320, 3724969617249, 948615261807, 48270752734, 0, 0] := by
  rw [show A10K2.u1382 = KTree.node A10K2.t1388 (nat_lit 19102724) (nat_lit 9167801129) (nat_lit 0) A10K2.t1389 from rfl, totK_node, tot1388, tot1389]
  decide +kernel

theorem arows1383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1383 = true := by
  rw [show A10K2.u1383 = KTree.node A10K2.t1390 (nat_lit 19107323) (nat_lit 6145254905) (nat_lit 0) A10K2.t1391 from rfl, allE_node, rows1390, irow1383, rows1391]
  all_goals rfl

theorem atot1383 : totK PA10K2 A10K2.u1383 = [0, 0, 0, 500650867142, 2656064329422, 4226011234942, 2105012522006, 291427014532, 6904928264, 0] := by
  rw [show A10K2.u1383 = KTree.node A10K2.t1390 (nat_lit 19107323) (nat_lit 6145254905) (nat_lit 0) A10K2.t1391 from rfl, totK_node, tot1390, tot1391]
  decide +kernel

theorem arows1387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1387 = true := by
  rw [show A10K2.u1387 = KTree.node A10K2.t1392 (nat_lit 19116018) (nat_lit 13590868588) (nat_lit 0) A10K2.t1393 from rfl, allE_node, rows1392, irow1387, rows1393]
  all_goals rfl

theorem atot1387 : totK PA10K2 A10K2.u1387 = [0, 0, 0, 1093163502979, 3885112881002, 3970142920641, 1218198779768, 84377215878, 0, 0] := by
  rw [show A10K2.u1387 = KTree.node A10K2.t1392 (nat_lit 19116018) (nat_lit 13590868588) (nat_lit 0) A10K2.t1393 from rfl, totK_node, tot1392, tot1393]
  decide +kernel

theorem arows1388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1388 = true := by
  rw [show A10K2.u1388 = KTree.node A10K2.t1394 (nat_lit 19133192) (nat_lit 12303251501) (nat_lit 0) A10K2.t1395 from rfl, allE_node, rows1394, irow1388, rows1395]
  all_goals rfl

theorem atot1388 : totK PA10K2 A10K2.u1388 = [0, 0, 0, 413816137730, 2237461967404, 3935163694588, 2664005439926, 561473595622, 34570548376, 0] := by
  rw [show A10K2.u1388 = KTree.node A10K2.t1394 (nat_lit 19133192) (nat_lit 12303251501) (nat_lit 0) A10K2.t1395 from rfl, totK_node, tot1394, tot1395]
  decide +kernel

theorem arows1390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1390 = true := by
  rw [show A10K2.u1390 = KTree.node A10K2.t1396 (nat_lit 19139653) (nat_lit 5640347444) (nat_lit 0) A10K2.t1397 from rfl, allE_node, rows1396, irow1390, rows1397]
  all_goals rfl

theorem atot1390 : totK PA10K2 A10K2.u1390 = [0, 0, 0, 653021486781, 2926359371670, 4074979910179, 1750380914455, 268605452692, 20070762815, 0] := by
  rw [show A10K2.u1390 = KTree.node A10K2.t1396 (nat_lit 19139653) (nat_lit 5640347444) (nat_lit 0) A10K2.t1397 from rfl, totK_node, tot1396, tot1397]
  decide +kernel

theorem arows1391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1391 = true := by
  rw [show A10K2.u1391 = KTree.node A10K2.t1398 (nat_lit 19152952) (nat_lit 14799186804) (nat_lit 0) A10K2.t1399 from rfl, allE_node, rows1398, irow1391, rows1399]
  all_goals rfl

theorem atot1391 : totK PA10K2 A10K2.u1391 = [0, 0, 0, 609852292078, 2513662758377, 3698900918406, 2106383385482, 370036886534, 10760911071, 0] := by
  rw [show A10K2.u1391 = KTree.node A10K2.t1398 (nat_lit 19152952) (nat_lit 14799186804) (nat_lit 0) A10K2.t1399 from rfl, totK_node, tot1398, tot1399]
  decide +kernel

theorem arows1394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1394 = true := by
  rw [show A10K2.u1394 = KTree.node A10K2.t1400 (nat_lit 19159202) (nat_lit 12511127108) (nat_lit 0) A10K2.t1401 from rfl, allE_node, rows1400, irow1394, rows1401]
  all_goals rfl

theorem atot1394 : totK PA10K2 A10K2.u1394 = [0, 0, 0, 503562995086, 2521875586108, 4096673604561, 1908370978233, 231334588170, 5705019915, 0] := by
  rw [show A10K2.u1394 = KTree.node A10K2.t1400 (nat_lit 19159202) (nat_lit 12511127108) (nat_lit 0) A10K2.t1401 from rfl, totK_node, tot1400, tot1401]
  decide +kernel

theorem arows1395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1395 = true := by
  rw [show A10K2.u1395 = KTree.node A10K2.t1402 (nat_lit 19165482) (nat_lit 6454379497) (nat_lit 0) A10K2.t1403 from rfl, allE_node, rows1402, irow1395, rows1403]
  all_goals rfl

theorem atot1395 : totK PA10K2 A10K2.u1395 = [0, 0, 0, 380040883308, 2285075626938, 4165102367436, 2635027862764, 453432751350, 12746179907, 0] := by
  rw [show A10K2.u1395 = KTree.node A10K2.t1402 (nat_lit 19165482) (nat_lit 6454379497) (nat_lit 0) A10K2.t1403 from rfl, totK_node, tot1402, tot1403]
  decide +kernel

theorem arows1397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1397 = true := by
  rw [show A10K2.u1397 = KTree.node A10K2.t1404 (nat_lit 19171845) (nat_lit 6721246945) (nat_lit 0) A10K2.t1405 from rfl, allE_node, rows1404, irow1397, rows1405]
  all_goals rfl

theorem atot1397 : totK PA10K2 A10K2.u1397 = [0, 0, 0, 0, 853063987824, 3310092787720, 3871168855509, 1319224768475, 108141186763, 0] := by
  rw [show A10K2.u1397 = KTree.node A10K2.t1404 (nat_lit 19171845) (nat_lit 6721246945) (nat_lit 0) A10K2.t1405 from rfl, totK_node, tot1404, tot1405]
  decide +kernel

theorem arows1398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1398 = true := by
  rw [show A10K2.u1398 = KTree.node A10K2.t1406 (nat_lit 19176852) (nat_lit 850311514) (nat_lit 0) A10K2.t1407 from rfl, allE_node, rows1406, irow1398, rows1407]
  all_goals rfl

theorem atot1398 : totK PA10K2 A10K2.u1398 = [0, 0, 0, 0, 496338503450, 2210379343961, 3551207515980, 2299890356916, 519994217521, 30605747850] := by
  rw [show A10K2.u1398 = KTree.node A10K2.t1406 (nat_lit 19176852) (nat_lit 850311514) (nat_lit 0) A10K2.t1407 from rfl, totK_node, tot1406, tot1407]
  decide +kernel

theorem arows1405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1405 = true := by
  rw [show A10K2.u1405 = KTree.node A10K2.t1408 (nat_lit 19191871) (nat_lit 5214921240) (nat_lit 0) A10K2.t1409 from rfl, allE_node, rows1408, irow1405, rows1409]
  all_goals rfl

theorem atot1405 : totK PA10K2 A10K2.u1405 = [0, 0, 0, 0, 562885936698, 2735601231272, 3895839491813, 1644121326721, 202478167619, 5528811039] := by
  rw [show A10K2.u1405 = KTree.node A10K2.t1408 (nat_lit 19191871) (nat_lit 5214921240) (nat_lit 0) A10K2.t1409 from rfl, totK_node, tot1408, tot1409]
  decide +kernel

theorem arows1406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1406 = true := by
  rw [show A10K2.u1406 = KTree.node A10K2.t1410 (nat_lit 19268088) (nat_lit 13324120295) (nat_lit 0) A10K2.t1411 from rfl, allE_node, rows1410, irow1406, rows1411]
  all_goals rfl

theorem atot1406 : totK PA10K2 A10K2.u1406 = [0, 0, 0, 794671563991, 3013703670505, 3754205395460, 1770813391990, 372675102565, 29010686974, 0] := by
  rw [show A10K2.u1406 = KTree.node A10K2.t1410 (nat_lit 19268088) (nat_lit 13324120295) (nat_lit 0) A10K2.t1411 from rfl, totK_node, tot1410, tot1411]
  decide +kernel

theorem arows1408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1408 = true := by
  rw [show A10K2.u1408 = KTree.node A10K2.t1412 (nat_lit 19273896) (nat_lit 8751241636) (nat_lit 0) A10K2.t1413 from rfl, allE_node, rows1412, irow1408, rows1413]
  all_goals rfl

theorem atot1408 : totK PA10K2 A10K2.u1408 = [0, 0, 0, 297214783146, 1920617276318, 3929459604697, 2701757932852, 570067975628, 30831673886, 0] := by
  rw [show A10K2.u1408 = KTree.node A10K2.t1412 (nat_lit 19273896) (nat_lit 8751241636) (nat_lit 0) A10K2.t1413 from rfl, totK_node, tot1412, tot1413]
  decide +kernel

theorem arows1409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1409 = true := by
  rw [show A10K2.u1409 = KTree.node A10K2.t1414 (nat_lit 19284001) (nat_lit 10156744321) (nat_lit 0) A10K2.t1415 from rfl, allE_node, rows1414, irow1409, rows1415]
  all_goals rfl

theorem atot1409 : totK PA10K2 A10K2.u1409 = [0, 0, 0, 629963341795, 2810646962716, 3843632411337, 1493771391647, 163020077454, 5656154743, 0] := by
  rw [show A10K2.u1409 = KTree.node A10K2.t1414 (nat_lit 19284001) (nat_lit 10156744321) (nat_lit 0) A10K2.t1415 from rfl, totK_node, tot1414, tot1415]
  decide +kernel

theorem arows1412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1412 = true := by
  rw [show A10K2.u1412 = KTree.node A10K2.t1416 (nat_lit 19289377) (nat_lit 8763170745) (nat_lit 0) A10K2.t1417 from rfl, allE_node, rows1416, irow1412, rows1417]
  all_goals rfl

theorem atot1412 : totK PA10K2 A10K2.u1412 = [0, 0, 0, 257913039921, 2131167064561, 4194353031947, 2292649854388, 286625562673, 6354482628, 0] := by
  rw [show A10K2.u1412 = KTree.node A10K2.t1416 (nat_lit 19289377) (nat_lit 8763170745) (nat_lit 0) A10K2.t1417 from rfl, totK_node, tot1416, tot1417]
  decide +kernel

theorem arows1413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1413 = true := by
  rw [show A10K2.u1413 = KTree.node A10K2.t1418 (nat_lit 19303968) (nat_lit 14106041371) (nat_lit 0) A10K2.t1419 from rfl, allE_node, rows1418, irow1413, rows1419]
  all_goals rfl

theorem atot1413 : totK PA10K2 A10K2.u1413 = [0, 0, 0, 0, 1181848812250, 3853773193282, 3410221655708, 823196967384, 44413115047, 0] := by
  rw [show A10K2.u1413 = KTree.node A10K2.t1418 (nat_lit 19303968) (nat_lit 14106041371) (nat_lit 0) A10K2.t1419 from rfl, totK_node, tot1418, tot1419]
  decide +kernel

theorem arows1415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1415 = true := by
  rw [show A10K2.u1415 = KTree.node A10K2.t1420 (nat_lit 19319331) (nat_lit 8217222220) (nat_lit 0) A10K2.t1421 from rfl, allE_node, rows1420, irow1415, rows1421]
  all_goals rfl

theorem atot1415 : totK PA10K2 A10K2.u1415 = [0, 0, 0, 0, 489192519076, 2788357925946, 4034300545822, 1459607615989, 127212348620, 0] := by
  rw [show A10K2.u1415 = KTree.node A10K2.t1420 (nat_lit 19319331) (nat_lit 8217222220) (nat_lit 0) A10K2.t1421 from rfl, totK_node, tot1420, tot1421]
  decide +kernel

theorem arows1416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1416 = true := by
  rw [show A10K2.u1416 = KTree.node A10K2.t1422 (nat_lit 19335949) (nat_lit 5806744952) (nat_lit 0) A10K2.t1423 from rfl, allE_node, rows1422, irow1416, rows1423]
  all_goals rfl

theorem atot1416 : totK PA10K2 A10K2.u1416 = [0, 0, 0, 808333325195, 3249836426584, 3921307058051, 1398338571778, 290040496151, 87067426044, 5676195732] := by
  rw [show A10K2.u1416 = KTree.node A10K2.t1422 (nat_lit 19335949) (nat_lit 5806744952) (nat_lit 0) A10K2.t1423 from rfl, totK_node, tot1422, tot1423]
  decide +kernel

theorem arows1420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1420 = true := by
  rw [show A10K2.u1420 = KTree.node A10K2.t1424 (nat_lit 19344497) (nat_lit 8085531748) (nat_lit 0) A10K2.t1425 from rfl, allE_node, rows1424, irow1420, rows1425]
  all_goals rfl

theorem atot1420 : totK PA10K2 A10K2.u1420 = [0, 0, 0, 800579792243, 3080813626488, 3952054760050, 1970091150576, 307815338637, 14941726116, 0] := by
  rw [show A10K2.u1420 = KTree.node A10K2.t1424 (nat_lit 19344497) (nat_lit 8085531748) (nat_lit 0) A10K2.t1425 from rfl, totK_node, tot1424, tot1425]
  decide +kernel

theorem arows1421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1421 = true := by
  rw [show A10K2.u1421 = KTree.node A10K2.t1426 (nat_lit 19361801) (nat_lit 9788426220) (nat_lit 0) A10K2.t1427 from rfl, allE_node, rows1426, irow1421, rows1427]
  all_goals rfl

theorem atot1421 : totK PA10K2 A10K2.u1421 = [0, 0, 0, 499381935060, 2686125990150, 4275475085764, 2295094482942, 309305393927, 6853348008, 0] := by
  rw [show A10K2.u1421 = KTree.node A10K2.t1426 (nat_lit 19361801) (nat_lit 9788426220) (nat_lit 0) A10K2.t1427 from rfl, totK_node, tot1426, tot1427]
  decide +kernel

theorem arows1423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1423 = true := by
  rw [show A10K2.u1423 = KTree.node A10K2.t1428 (nat_lit 19925211) (nat_lit 5925846400) (nat_lit 8) A10K2.t1429 from rfl, allE_node, rows1428, irow1423, rows1429]
  all_goals rfl

theorem atot1423 : totK PA10K2 A10K2.u1423 = [0, 0, 836324140249, 3167472891097, 3533599537762, 1307227395535, 551674958673, 265789631412, 28650013862, 0] := by
  rw [show A10K2.u1423 = KTree.node A10K2.t1428 (nat_lit 19925211) (nat_lit 5925846400) (nat_lit 8) A10K2.t1429 from rfl, totK_node, tot1428, tot1429]
  decide +kernel

theorem arows1424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1424 = true := by
  rw [show A10K2.u1424 = KTree.node A10K2.t1430 (nat_lit 19929953) (nat_lit 8396116917) (nat_lit 0) A10K2.t1431 from rfl, allE_node, rows1430, irow1424, rows1431]
  all_goals rfl

theorem atot1424 : totK PA10K2 A10K2.u1424 = [0, 0, 392187269560, 1981825466437, 3800464917953, 2674188172446, 558388016715, 30831673886, 0, 0] := by
  rw [show A10K2.u1424 = KTree.node A10K2.t1430 (nat_lit 19929953) (nat_lit 8396116917) (nat_lit 0) A10K2.t1431 from rfl, totK_node, tot1430, tot1431]
  decide +kernel

theorem arows1427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1427 = true := by
  rw [show A10K2.u1427 = KTree.node A10K2.t1432 (nat_lit 19943712) (nat_lit 13375405213) (nat_lit 0) A10K2.t1433 from rfl, allE_node, rows1432, irow1427, rows1433]
  all_goals rfl

theorem atot1427 : totK PA10K2 A10K2.u1427 = [0, 0, 480442038098, 2529615259610, 4047734580585, 2017778786356, 248800751202, 6354482628, 0, 0] := by
  rw [show A10K2.u1427 = KTree.node A10K2.t1432 (nat_lit 19943712) (nat_lit 13375405213) (nat_lit 0) A10K2.t1433 from rfl, totK_node, tot1432, tot1433]
  decide +kernel

theorem arows1428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1428 = true := by
  rw [show A10K2.u1428 = KTree.node A10K2.t1434 (nat_lit 19951606) (nat_lit 16720836805) (nat_lit 0) A10K2.t1435 from rfl, allE_node, rows1434, irow1428, rows1435]
  all_goals rfl

theorem atot1428 : totK PA10K2 A10K2.u1428 = [0, 0, 472246657175, 2396246884512, 4125349267052, 2629119810778, 469589328067, 12746179907, 0, 0] := by
  rw [show A10K2.u1428 = KTree.node A10K2.t1434 (nat_lit 19951606) (nat_lit 16720836805) (nat_lit 0) A10K2.t1435 from rfl, totK_node, tot1434, tot1435]
  decide +kernel

theorem arows1430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1430 = true := by
  rw [show A10K2.u1430 = KTree.node A10K2.t1436 (nat_lit 19958103) (nat_lit 1174248817) (nat_lit 0) A10K2.t1437 from rfl, allE_node, rows1436, irow1430, rows1437]
  all_goals rfl

theorem atot1430 : totK PA10K2 A10K2.u1430 = [0, 0, 0, 832682785970, 3337282302613, 3956409287904, 1335378095062, 108968725391, 0, 0] := by
  rw [show A10K2.u1430 = KTree.node A10K2.t1436 (nat_lit 19958103) (nat_lit 1174248817) (nat_lit 0) A10K2.t1437 from rfl, totK_node, tot1436, tot1437]
  decide +kernel

theorem arows1431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1431 = true := by
  rw [show A10K2.u1431 = KTree.node A10K2.t1438 (nat_lit 19963273) (nat_lit 8696006851) (nat_lit 0) A10K2.t1439 from rfl, allE_node, rows1438, irow1431, rows1439]
  all_goals rfl

theorem atot1431 : totK PA10K2 A10K2.u1431 = [0, 0, 0, 464878800056, 2253397428425, 3739752933455, 2314853683909, 520524378838, 30650496230, 0] := by
  rw [show A10K2.u1431 = KTree.node A10K2.t1438 (nat_lit 19963273) (nat_lit 8696006851) (nat_lit 0) A10K2.t1439 from rfl, totK_node, tot1438, tot1439]
  decide +kernel

theorem arows1436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1436 = true := by
  rw [show A10K2.u1436 = KTree.node A10K2.t1440 (nat_lit 19977540) (nat_lit 12578999037) (nat_lit 0) A10K2.t1441 from rfl, allE_node, rows1440, irow1436, rows1441]
  all_goals rfl

theorem atot1436 : totK PA10K2 A10K2.u1436 = [0, 0, 0, 585514307514, 2732129320048, 4012322381948, 1787318438999, 225076579657, 5546304973, 0] := by
  rw [show A10K2.u1436 = KTree.node A10K2.t1440 (nat_lit 19977540) (nat_lit 12578999037) (nat_lit 0) A10K2.t1441 from rfl, totK_node, tot1440, tot1441]
  decide +kernel

theorem arows1437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1437 = true := by
  rw [show A10K2.u1437 = KTree.node A10K2.t1442 (nat_lit 19998380) (nat_lit 11716372436) (nat_lit 0) A10K2.t1443 from rfl, allE_node, rows1442, irow1437, rows1443]
  all_goals rfl

theorem atot1437 : totK PA10K2 A10K2.u1437 = [0, 0, 560899012013, 2624816075938, 3925483663888, 2246433220673, 478096973130, 29791859037, 0, 0] := by
  rw [show A10K2.u1437 = KTree.node A10K2.t1442 (nat_lit 19998380) (nat_lit 11716372436) (nat_lit 0) A10K2.t1443 from rfl, totK_node, tot1442, tot1443]
  decide +kernel

theorem arows1439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1439 = true := by
  rw [show A10K2.u1439 = KTree.node A10K2.t1444 (nat_lit 20006058) (nat_lit 12978655923) (nat_lit 0) A10K2.t1445 from rfl, allE_node, rows1444, irow1439, rows1445]
  all_goals rfl

theorem atot1439 : totK PA10K2 A10K2.u1439 = [0, 0, 738658298461, 2950488883146, 3826983621518, 1687646837683, 228049469997, 6034215561, 0, 0] := by
  rw [show A10K2.u1439 = KTree.node A10K2.t1444 (nat_lit 20006058) (nat_lit 12978655923) (nat_lit 0) A10K2.t1445 from rfl, totK_node, tot1444, tot1445]
  decide +kernel

theorem arows1440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1440 = true := by
  rw [show A10K2.u1440 = KTree.node A10K2.t1446 (nat_lit 20011811) (nat_lit 9660572677) (nat_lit 0) A10K2.t1447 from rfl, allE_node, rows1446, irow1440, rows1447]
  all_goals rfl

theorem atot1440 : totK PA10K2 A10K2.u1440 = [0, 0, 0, 1445360811694, 4349740164531, 3108411864050, 499899631533, 12398919031, 0, 0] := by
  rw [show A10K2.u1440 = KTree.node A10K2.t1446 (nat_lit 20011811) (nat_lit 9660572677) (nat_lit 0) A10K2.t1447 from rfl, totK_node, tot1446, tot1447]
  decide +kernel

theorem arows1443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1443 = true := by
  rw [show A10K2.u1443 = KTree.node A10K2.t1448 (nat_lit 20040225) (nat_lit 9727951846) (nat_lit 0) A10K2.t1449 from rfl, allE_node, rows1448, irow1443, rows1449]
  all_goals rfl

theorem atot1443 : totK PA10K2 A10K2.u1443 = [0, 0, 0, 583442077426, 3013070803923, 4199170545122, 1469242378540, 82775502960, 0, 0] := by
  rw [show A10K2.u1443 = KTree.node A10K2.t1448 (nat_lit 20040225) (nat_lit 9727951846) (nat_lit 0) A10K2.t1449 from rfl, totK_node, tot1448, tot1449]
  decide +kernel

theorem arows1444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1444 = true := by
  rw [show A10K2.u1444 = KTree.node A10K2.t1450 (nat_lit 20056589) (nat_lit 5792982411) (nat_lit 0) A10K2.t1451 from rfl, allE_node, rows1450, irow1444, rows1451]
  all_goals rfl

theorem atot1444 : totK PA10K2 A10K2.u1444 = [0, 0, 762134139439, 3069625064652, 3869296853590, 1569259624077, 290523059023, 69316020384, 6121173289, 0] := by
  rw [show A10K2.u1444 = KTree.node A10K2.t1450 (nat_lit 20056589) (nat_lit 5792982411) (nat_lit 0) A10K2.t1451 from rfl, totK_node, tot1450, tot1451]
  decide +kernel

theorem arows1446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1446 = true := by
  rw [show A10K2.u1446 = KTree.node A10K2.t1452 (nat_lit 20063460) (nat_lit 13087499283) (nat_lit 0) A10K2.t1453 from rfl, allE_node, rows1452, irow1446, rows1453]
  all_goals rfl

theorem atot1446 : totK PA10K2 A10K2.u1446 = [0, 0, 584952430844, 2498294933652, 3675660964252, 2162683010290, 465466650612, 30831673886, 0, 0] := by
  rw [show A10K2.u1446 = KTree.node A10K2.t1452 (nat_lit 20063460) (nat_lit 13087499283) (nat_lit 0) A10K2.t1453 from rfl, totK_node, tot1452, tot1453]
  decide +kernel

theorem arows1447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1447 = true := by
  rw [show A10K2.u1447 = KTree.node A10K2.t1454 (nat_lit 20069218) (nat_lit 11477959185) (nat_lit 0) A10K2.t1455 from rfl, allE_node, rows1454, irow1447, rows1455]
  all_goals rfl

theorem atot1447 : totK PA10K2 A10K2.u1447 = [0, 0, 512579146014, 2377866464646, 3832208391101, 2176826394941, 346773441448, 11427838733, 0, 0] := by
  rw [show A10K2.u1447 = KTree.node A10K2.t1454 (nat_lit 20069218) (nat_lit 11477959185) (nat_lit 0) A10K2.t1455 from rfl, totK_node, tot1454, tot1455]
  decide +kernel

theorem arows1451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1451 = true := by
  rw [show A10K2.u1451 = KTree.node A10K2.t1456 (nat_lit 20074881) (nat_lit 10262273138) (nat_lit 0) A10K2.t1457 from rfl, allE_node, rows1456, irow1451, rows1457]
  all_goals rfl

theorem atot1451 : totK PA10K2 A10K2.u1451 = [0, 0, 308781236982, 2191219538873, 4188681726684, 2297590717450, 317253512015, 6354482628, 0, 0] := by
  rw [show A10K2.u1451 = KTree.node A10K2.t1456 (nat_lit 20074881) (nat_lit 10262273138) (nat_lit 0) A10K2.t1457 from rfl, totK_node, tot1456, tot1457]
  decide +kernel

theorem arows1452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1452 = true := by
  rw [show A10K2.u1452 = KTree.node A10K2.t1458 (nat_lit 20089664) (nat_lit 13576200573) (nat_lit 0) A10K2.t1459 from rfl, allE_node, rows1458, irow1452, rows1459]
  all_goals rfl

theorem atot1452 : totK PA10K2 A10K2.u1452 = [0, 0, 0, 1055945433768, 3802055331975, 3761031406704, 907646288875, 44309977711, 0, 0] := by
  rw [show A10K2.u1452 = KTree.node A10K2.t1458 (nat_lit 20089664) (nat_lit 13576200573) (nat_lit 0) A10K2.t1459 from rfl, totK_node, tot1458, tot1459]
  decide +kernel

theorem arows1454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1454 = true := by
  rw [show A10K2.u1454 = KTree.node A10K2.t1460 (nat_lit 20104126) (nat_lit 10561467277) (nat_lit 0) A10K2.t1461 from rfl, allE_node, rows1460, irow1454, rows1461]
  all_goals rfl

theorem atot1454 : totK PA10K2 A10K2.u1454 = [0, 0, 0, 989275823522, 3780905458590, 3697202742583, 767500628806, 36992254861, 0, 0] := by
  rw [show A10K2.u1454 = KTree.node A10K2.t1460 (nat_lit 20104126) (nat_lit 10561467277) (nat_lit 0) A10K2.t1461 from rfl, totK_node, tot1460, tot1461]
  decide +kernel

theorem arows1455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1455 = true := by
  rw [show A10K2.u1455 = KTree.node A10K2.t1462 (nat_lit 20110112) (nat_lit 12125212889) (nat_lit 0) A10K2.t1463 from rfl, allE_node, rows1462, irow1455, rows1463]
  all_goals rfl

theorem atot1455 : totK PA10K2 A10K2.u1455 = [0, 0, 0, 582206494532, 2650914025921, 3975850718470, 1826275096132, 240928176614, 6354482628, 0] := by
  rw [show A10K2.u1455 = KTree.node A10K2.t1462 (nat_lit 20110112) (nat_lit 12125212889) (nat_lit 0) A10K2.t1463 from rfl, totK_node, tot1462, tot1463]
  decide +kernel

theorem arows1458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1458 = true := by
  rw [show A10K2.u1458 = KTree.node A10K2.t1464 (nat_lit 20189576) (nat_lit 14332909434) (nat_lit 0) A10K2.t1465 from rfl, allE_node, rows1464, irow1458, rows1465]
  all_goals rfl

theorem atot1458 : totK PA10K2 A10K2.u1458 = [0, 0, 0, 252968100394, 1915558382962, 4066323964388, 2666370056524, 545465524902, 30818366867, 0] := by
  rw [show A10K2.u1458 = KTree.node A10K2.t1464 (nat_lit 20189576) (nat_lit 14332909434) (nat_lit 0) A10K2.t1465 from rfl, totK_node, tot1464, tot1465]
  decide +kernel

theorem arows1459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1459 = true := by
  rw [show A10K2.u1459 = KTree.node A10K2.t1466 (nat_lit 20203282) (nat_lit 14771366141) (nat_lit 0) A10K2.t1467 from rfl, allE_node, rows1466, irow1459, rows1467]
  all_goals rfl

theorem atot1459 : totK PA10K2 A10K2.u1459 = [0, 0, 0, 755705679480, 3194653793186, 3964312501181, 1348172398514, 100773681532, 0, 0] := by
  rw [show A10K2.u1459 = KTree.node A10K2.t1466 (nat_lit 20203282) (nat_lit 14771366141) (nat_lit 0) A10K2.t1467 from rfl, totK_node, tot1466, tot1467]
  decide +kernel

theorem arows1461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1461 = true := by
  rw [show A10K2.u1461 = KTree.node A10K2.t1468 (nat_lit 20210185) (nat_lit 9769058977) (nat_lit 0) A10K2.t1469 from rfl, allE_node, rows1468, irow1461, rows1469]
  all_goals rfl

theorem atot1461 : totK PA10K2 A10K2.u1461 = [0, 0, 0, 585800132002, 2684012158422, 4082982906528, 2013628767785, 262085470598, 6354482628, 0] := by
  rw [show A10K2.u1461 = KTree.node A10K2.t1468 (nat_lit 20210185) (nat_lit 9769058977) (nat_lit 0) A10K2.t1469 from rfl, totK_node, tot1468, tot1469]
  decide +kernel

theorem arows1462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1462 = true := by
  rw [show A10K2.u1462 = KTree.node A10K2.t1470 (nat_lit 20260650) (nat_lit 12526482812) (nat_lit 0) A10K2.t1471 from rfl, allE_node, rows1470, irow1462, rows1471]
  all_goals rfl

theorem atot1462 : totK PA10K2 A10K2.u1462 = [0, 0, 0, 805380299588, 3195260432193, 3863882744444, 1589588896360, 241067139098, 6853348008, 0] := by
  rw [show A10K2.u1462 = KTree.node A10K2.t1470 (nat_lit 20260650) (nat_lit 12526482812) (nat_lit 0) A10K2.t1471 from rfl, totK_node, tot1470, tot1471]
  decide +kernel

theorem arows1468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1468 = true := by
  rw [show A10K2.u1468 = KTree.node A10K2.t1472 (nat_lit 20271117) (nat_lit 5771049398) (nat_lit 0) A10K2.t1473 from rfl, allE_node, rows1472, irow1468, rows1473]
  all_goals rfl

theorem atot1468 : totK PA10K2 A10K2.u1468 = [0, 0, 0, 604972014896, 2785681469437, 4019441659087, 1705437341200, 184952456427, 6354482628, 0] := by
  rw [show A10K2.u1468 = KTree.node A10K2.t1472 (nat_lit 20271117) (nat_lit 5771049398) (nat_lit 0) A10K2.t1473 from rfl, totK_node, tot1472, tot1473]
  decide +kernel

theorem arows1469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1469 = true := by
  rw [show A10K2.u1469 = KTree.node A10K2.t1474 (nat_lit 20318999) (nat_lit 3819192609) (nat_lit 0) A10K2.t1475 from rfl, allE_node, rows1474, irow1469, rows1475]
  all_goals rfl

theorem atot1469 : totK PA10K2 A10K2.u1469 = [0, 0, 0, 647206446184, 2868833211267, 3877190537995, 1725538996697, 308675878207, 24614390653, 0] := by
  rw [show A10K2.u1469 = KTree.node A10K2.t1474 (nat_lit 20318999) (nat_lit 3819192609) (nat_lit 0) A10K2.t1475 from rfl, totK_node, tot1474, tot1475]
  decide +kernel

theorem arows1471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1471 = true := by
  rw [show A10K2.u1471 = KTree.node A10K2.t1476 (nat_lit 20326045) (nat_lit 6072068473) (nat_lit 0) A10K2.t1477 from rfl, allE_node, rows1476, irow1471, rows1477]
  all_goals rfl

theorem atot1471 : totK PA10K2 A10K2.u1471 = [0, 0, 0, 584334959235, 2784988212717, 4063696647182, 1734840244867, 208152863209, 5460492893, 0] := by
  rw [show A10K2.u1471 = KTree.node A10K2.t1476 (nat_lit 20326045) (nat_lit 6072068473) (nat_lit 0) A10K2.t1477 from rfl, totK_node, tot1476, tot1477]
  decide +kernel

theorem arows1472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1472 = true := by
  rw [show A10K2.u1472 = KTree.node A10K2.t1478 (nat_lit 20333409) (nat_lit 8989251321) (nat_lit 0) A10K2.t1479 from rfl, allE_node, rows1478, irow1472, rows1479]
  all_goals rfl

theorem atot1472 : totK PA10K2 A10K2.u1472 = [0, 0, 0, 817731798921, 3101973613401, 3688021777276, 1429644396136, 164652317932, 6034215561, 0] := by
  rw [show A10K2.u1472 = KTree.node A10K2.t1478 (nat_lit 20333409) (nat_lit 8989251321) (nat_lit 0) A10K2.t1479 from rfl, totK_node, tot1478, tot1479]
  decide +kernel

theorem arows1475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1475 = true := by
  rw [show A10K2.u1475 = KTree.node A10K2.t1480 (nat_lit 20339028) (nat_lit 13140071320) (nat_lit 0) A10K2.t1481 from rfl, allE_node, rows1480, irow1475, rows1481]
  all_goals rfl

theorem atot1475 : totK PA10K2 A10K2.u1475 = [0, 0, 0, 0, 1406115045142, 4230536003326, 2934495473385, 539353630464, 31193230065, 0] := by
  rw [show A10K2.u1475 = KTree.node A10K2.t1480 (nat_lit 20339028) (nat_lit 13140071320) (nat_lit 0) A10K2.t1481 from rfl, totK_node, tot1480, tot1481]
  decide +kernel

theorem arows1476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1476 = true := by
  rw [show A10K2.u1476 = KTree.node A10K2.t1482 (nat_lit 20359447) (nat_lit 8624196181) (nat_lit 0) A10K2.t1483 from rfl, allE_node, rows1482, irow1476, rows1483]
  all_goals rfl

theorem atot1476 : totK PA10K2 A10K2.u1476 = [0, 0, 0, 0, 1294823559450, 3998509176677, 3191359893958, 667475397705, 37364482810, 0] := by
  rw [show A10K2.u1476 = KTree.node A10K2.t1482 (nat_lit 20359447) (nat_lit 8624196181) (nat_lit 0) A10K2.t1483 from rfl, totK_node, tot1482, tot1483]
  decide +kernel

theorem arows1478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1478 = true := by
  rw [show A10K2.u1478 = KTree.node A10K2.t1484 (nat_lit 20369734) (nat_lit 8806607160) (nat_lit 0) A10K2.t1485 from rfl, allE_node, rows1484, irow1478, rows1485]
  all_goals rfl

theorem atot1478 : totK PA10K2 A10K2.u1478 = [0, 0, 287182759341, 667055252272, 685868721693, 2321266317901, 3406967008721, 1480202533688, 199159747666, 5976421810] := by
  rw [show A10K2.u1478 = KTree.node A10K2.t1484 (nat_lit 20369734) (nat_lit 8806607160) (nat_lit 0) A10K2.t1485 from rfl, totK_node, tot1484, tot1485]
  decide +kernel

theorem arows1479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1479 = true := by
  rw [show A10K2.u1479 = KTree.node A10K2.t1486 (nat_lit 20450547) (nat_lit 8397455708) (nat_lit 0) A10K2.t1487 from rfl, allE_node, rows1486, irow1479, rows1487]
  all_goals rfl

theorem atot1479 : totK PA10K2 A10K2.u1479 = [0, 0, 543519865748, 2723896792750, 4067002551269, 2027782847427, 339054551345, 20070762815, 0, 0] := by
  rw [show A10K2.u1479 = KTree.node A10K2.t1486 (nat_lit 20450547) (nat_lit 8397455708) (nat_lit 0) A10K2.t1487 from rfl, totK_node, tot1486, tot1487]
  decide +kernel

theorem arows1483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1483 = true := by
  rw [show A10K2.u1483 = KTree.node A10K2.t1488 (nat_lit 20463898) (nat_lit 6773941848) (nat_lit 0) A10K2.t1489 from rfl, allE_node, rows1488, irow1483, rows1489]
  all_goals rfl

theorem atot1483 : totK PA10K2 A10K2.u1483 = [0, 0, 553042123750, 2637929287281, 3955950893527, 2015536730917, 315077288706, 10760911071, 0, 0] := by
  rw [show A10K2.u1483 = KTree.node A10K2.t1488 (nat_lit 20463898) (nat_lit 6773941848) (nat_lit 0) A10K2.t1489 from rfl, totK_node, tot1488, tot1489]
  decide +kernel

theorem arows1484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1484 = true := by
  rw [show A10K2.u1484 = KTree.node A10K2.t1490 (nat_lit 20472264) (nat_lit 14136040694) (nat_lit 0) A10K2.t1491 from rfl, allE_node, rows1490, irow1484, rows1491]
  all_goals rfl

theorem atot1484 : totK PA10K2 A10K2.u1484 = [0, 0, 814261798480, 3085295390449, 3927514918429, 1735606188308, 222329045183, 5976421810, 0, 0] := by
  rw [show A10K2.u1484 = KTree.node A10K2.t1490 (nat_lit 20472264) (nat_lit 14136040694) (nat_lit 0) A10K2.t1491 from rfl, totK_node, tot1490, tot1491]
  decide +kernel

theorem arows1486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1486 = true := by
  rw [show A10K2.u1486 = KTree.node A10K2.t1492 (nat_lit 20477331) (nat_lit 10539562850) (nat_lit 0) A10K2.t1493 from rfl, allE_node, rows1492, irow1486, rows1493]
  all_goals rfl

theorem atot1486 : totK PA10K2 A10K2.u1486 = [0, 0, 0, 1263462249244, 4138045528635, 3768266596373, 950164769391, 48261347678, 0, 0] := by
  rw [show A10K2.u1486 = KTree.node A10K2.t1492 (nat_lit 20477331) (nat_lit 10539562850) (nat_lit 0) A10K2.t1493 from rfl, totK_node, tot1492, tot1493]
  decide +kernel

theorem arows1487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1487 = true := by
  rw [show A10K2.u1487 = KTree.node A10K2.t1494 (nat_lit 20483108) (nat_lit 11598947914) (nat_lit 0) A10K2.t1495 from rfl, allE_node, rows1494, irow1487, rows1495]
  all_goals rfl

theorem atot1487 : totK PA10K2 A10K2.u1487 = [0, 0, 0, 724713102053, 3074738484873, 3963432480643, 1594416860066, 252481032254, 14945844243, 0] := by
  rw [show A10K2.u1487 = KTree.node A10K2.t1494 (nat_lit 20483108) (nat_lit 11598947914) (nat_lit 0) A10K2.t1495 from rfl, totK_node, tot1494, tot1495]
  decide +kernel

theorem arows1490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1490 = true := by
  rw [show A10K2.u1490 = KTree.node A10K2.t1496 (nat_lit 20496909) (nat_lit 5631979946) (nat_lit 0) A10K2.t1497 from rfl, allE_node, rows1496, irow1490, rows1497]
  all_goals rfl

theorem atot1490 : totK PA10K2 A10K2.u1490 = [0, 0, 0, 844638339212, 3150669810120, 3718541508708, 1523178940697, 223285592956, 5179162207, 0] := by
  rw [show A10K2.u1490 = KTree.node A10K2.t1496 (nat_lit 20496909) (nat_lit 5631979946) (nat_lit 0) A10K2.t1497 from rfl, totK_node, tot1496, tot1497]
  decide +kernel

theorem arows1491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1491 = true := by
  rw [show A10K2.u1491 = KTree.node A10K2.t1498 (nat_lit 20508225) (nat_lit 10222429166) (nat_lit 0) A10K2.t1499 from rfl, allE_node, rows1498, irow1491, rows1499]
  all_goals rfl

theorem atot1491 : totK PA10K2 A10K2.u1491 = [0, 0, 509119267445, 2102485156251, 3705940833454, 3077805525797, 867343930712, 62694074884, 0, 0] := by
  rw [show A10K2.u1491 = KTree.node A10K2.t1498 (nat_lit 20508225) (nat_lit 10222429166) (nat_lit 0) A10K2.t1499 from rfl, totK_node, tot1498, tot1499]
  decide +kernel

theorem arows1493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1493 = true := by
  rw [show A10K2.u1493 = KTree.node A10K2.t1500 (nat_lit 20538811) (nat_lit 7035925206) (nat_lit 0) A10K2.t1501 from rfl, allE_node, rows1500, irow1493, rows1501]
  all_goals rfl

theorem atot1493 : totK PA10K2 A10K2.u1493 = [0, 0, 878830193257, 3615427106393, 4327525358997, 1435344069716, 109993823561, 0, 0, 0] := by
  rw [show A10K2.u1493 = KTree.node A10K2.t1500 (nat_lit 20538811) (nat_lit 7035925206) (nat_lit 0) A10K2.t1501 from rfl, totK_node, tot1500, tot1501]
  decide +kernel

theorem arows1494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1494 = true := by
  rw [show A10K2.u1494 = KTree.node A10K2.t1502 (nat_lit 20544915) (nat_lit 10231161087) (nat_lit 0) A10K2.t1503 from rfl, allE_node, rows1502, irow1494, rows1503]
  all_goals rfl

theorem atot1494 : totK PA10K2 A10K2.u1494 = [0, 0, 300827602965, 1690661411366, 3718148498835, 3361699509640, 959360353846, 62712130859, 0, 0] := by
  rw [show A10K2.u1494 = KTree.node A10K2.t1502 (nat_lit 20544915) (nat_lit 10231161087) (nat_lit 0) A10K2.t1503 from rfl, totK_node, tot1502, tot1503]
  decide +kernel

theorem arows1499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1499 = true := by
  rw [show A10K2.u1499 = KTree.node A10K2.t1504 (nat_lit 20647884) (nat_lit 4035251865) (nat_lit 0) A10K2.t1505 from rfl, allE_node, rows1504, irow1499, rows1505]
  all_goals rfl

theorem atot1499 : totK PA10K2 A10K2.u1499 = [0, 0, 480154549792, 2432099654867, 4062191234764, 2426990733891, 421891795688, 20029934272, 0, 0] := by
  rw [show A10K2.u1499 = KTree.node A10K2.t1504 (nat_lit 20647884) (nat_lit 4035251865) (nat_lit 0) A10K2.t1505 from rfl, totK_node, tot1504, tot1505]
  decide +kernel

theorem arows1500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1500 = true := by
  rw [show A10K2.u1500 = KTree.node A10K2.t1506 (nat_lit 20655350) (nat_lit 16319387176) (nat_lit 0) A10K2.t1507 from rfl, allE_node, rows1506, irow1500, rows1507]
  all_goals rfl

theorem atot1500 : totK PA10K2 A10K2.u1500 = [0, 0, 628178301765, 2854664709032, 4246350266095, 2229054982007, 308343216006, 8047840951, 0, 0] := by
  rw [show A10K2.u1500 = KTree.node A10K2.t1506 (nat_lit 20655350) (nat_lit 16319387176) (nat_lit 0) A10K2.t1507 from rfl, totK_node, tot1506, tot1507]
  decide +kernel

theorem arows1502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1502 = true := by
  rw [show A10K2.u1502 = KTree.node A10K2.t1508 (nat_lit 20669802) (nat_lit 6003002686) (nat_lit 0) A10K2.t1509 from rfl, allE_node, rows1508, irow1502, rows1509]
  all_goals rfl

theorem atot1502 : totK PA10K2 A10K2.u1502 = [0, 0, 873613144665, 3424880454168, 4127785253531, 1500486848274, 104396973260, 0, 0, 0] := by
  rw [show A10K2.u1502 = KTree.node A10K2.t1508 (nat_lit 20669802) (nat_lit 6003002686) (nat_lit 0) A10K2.t1509 from rfl, totK_node, tot1508, tot1509]
  decide +kernel

theorem arows1503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1503 = true := by
  rw [show A10K2.u1503 = KTree.node A10K2.t1510 (nat_lit 20674441) (nat_lit 5801831120) (nat_lit 0) A10K2.t1511 from rfl, allE_node, rows1510, irow1503, rows1511]
  all_goals rfl

theorem atot1503 : totK PA10K2 A10K2.u1503 = [0, 0, 0, 1127356052156, 3871546445742, 3856730185710, 1040011193758, 62996513375, 0, 0] := by
  rw [show A10K2.u1503 = KTree.node A10K2.t1510 (nat_lit 20674441) (nat_lit 5801831120) (nat_lit 0) A10K2.t1511 from rfl, totK_node, tot1510, tot1511]
  decide +kernel

theorem arows1506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1506 = true := by
  rw [show A10K2.u1506 = KTree.node A10K2.t1512 (nat_lit 20680205) (nat_lit 5328519634) (nat_lit 0) A10K2.t1513 from rfl, allE_node, rows1512, irow1506, rows1513]
  all_goals rfl

theorem atot1506 : totK PA10K2 A10K2.u1506 = [0, 0, 0, 519063809684, 2755826477094, 4276315276998, 2020373296071, 291263372347, 6904928264, 0] := by
  rw [show A10K2.u1506 = KTree.node A10K2.t1512 (nat_lit 20680205) (nat_lit 5328519634) (nat_lit 0) A10K2.t1513 from rfl, totK_node, tot1512, tot1513]
  decide +kernel

theorem arows1507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1507 = true := by
  rw [show A10K2.u1507 = KTree.node A10K2.t1514 (nat_lit 20688787) (nat_lit 10351364632) (nat_lit 0) A10K2.t1515 from rfl, allE_node, rows1514, irow1507, rows1515]
  all_goals rfl

theorem atot1507 : totK PA10K2 A10K2.u1507 = [0, 0, 0, 1165365165952, 3950047375225, 3826586858968, 1228117507983, 92130927703, 0, 0] := by
  rw [show A10K2.u1507 = KTree.node A10K2.t1514 (nat_lit 20688787) (nat_lit 10351364632) (nat_lit 0) A10K2.t1515 from rfl, totK_node, tot1514, tot1515]
  decide +kernel

theorem arows1509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1509 = true := by
  rw [show A10K2.u1509 = KTree.node A10K2.t1516 (nat_lit 20705733) (nat_lit 3864289056) (nat_lit 0) A10K2.t1517 from rfl, allE_node, rows1516, irow1509, rows1517]
  all_goals rfl

theorem atot1509 : totK PA10K2 A10K2.u1509 = [0, 0, 0, 325864898897, 2107005647254, 4120252566910, 2876961366724, 601701167053, 35608018656, 0] := by
  rw [show A10K2.u1509 = KTree.node A10K2.t1516 (nat_lit 20705733) (nat_lit 3864289056) (nat_lit 0) A10K2.t1517 from rfl, totK_node, tot1516, tot1517]
  decide +kernel

theorem arows1510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1510 = true := by
  rw [show A10K2.u1510 = KTree.node A10K2.t1518 (nat_lit 25168530) (nat_lit 9293386232) (nat_lit 0) A10K2.t1519 from rfl, allE_node, rows1518, irow1510, rows1519]
  all_goals rfl

theorem atot1510 : totK PA10K2 A10K2.u1510 = [0, 841923539307, 3393588752070, 4028645656944, 1388912112921, 101395737453, 0, 0, 0, 0] := by
  rw [show A10K2.u1510 = KTree.node A10K2.t1518 (nat_lit 25168530) (nat_lit 9293386232) (nat_lit 0) A10K2.t1519 from rfl, totK_node, tot1518, tot1519]
  decide +kernel

theorem arows1514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1514 = true := by
  rw [show A10K2.u1514 = KTree.node A10K2.t1520 (nat_lit 25173233) (nat_lit 6032858042) (nat_lit 0) A10K2.t1521 from rfl, allE_node, rows1520, irow1514, rows1521]
  all_goals rfl

theorem atot1514 : totK PA10K2 A10K2.u1514 = [0, 456550563288, 2152916231068, 3751478751401, 2599895372182, 563789946659, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1514 = KTree.node A10K2.t1520 (nat_lit 25173233) (nat_lit 6032858042) (nat_lit 0) A10K2.t1521 from rfl, totK_node, tot1520, tot1521]
  decide +kernel

theorem arows1515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1515 = true := by
  rw [show A10K2.u1515 = KTree.node A10K2.t1522 (nat_lit 25187482) (nat_lit 14888248197) (nat_lit 0) A10K2.t1523 from rfl, allE_node, rows1522, irow1515, rows1523]
  all_goals rfl

theorem atot1515 : totK PA10K2 A10K2.u1515 = [0, 583383242649, 2597460700961, 3869250125376, 2017843233289, 286679959898, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1515 = KTree.node A10K2.t1522 (nat_lit 25187482) (nat_lit 14888248197) (nat_lit 0) A10K2.t1523 from rfl, totK_node, tot1522, tot1523]
  decide +kernel

theorem arows1517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1517 = true := by
  rw [show A10K2.u1517 = KTree.node A10K2.t1524 (nat_lit 25194397) (nat_lit 1264520537) (nat_lit 0) A10K2.t1525 from rfl, allE_node, rows1524, irow1517, rows1525]
  all_goals rfl

theorem atot1517 : totK PA10K2 A10K2.u1517 = [0, 395296435550, 2450914560566, 4463885846181, 2657647390850, 392146623281, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u1517 = KTree.node A10K2.t1524 (nat_lit 25194397) (nat_lit 1264520537) (nat_lit 0) A10K2.t1525 from rfl, totK_node, tot1524, tot1525]
  decide +kernel

theorem arows1518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1518 = true := by
  rw [show A10K2.u1518 = KTree.node A10K2.t1526 (nat_lit 25199494) (nat_lit 15551011749) (nat_lit 0) A10K2.t1527 from rfl, allE_node, rows1526, irow1518, rows1527]
  all_goals rfl

theorem atot1518 : totK PA10K2 A10K2.u1518 = [0, 0, 916221627546, 3572602750199, 4016157253543, 1239480578550, 79336601816, 0, 0, 0] := by
  rw [show A10K2.u1518 = KTree.node A10K2.t1526 (nat_lit 25199494) (nat_lit 15551011749) (nat_lit 0) A10K2.t1527 from rfl, totK_node, tot1526, tot1527]
  decide +kernel

theorem arows1521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1521 = true := by
  rw [show A10K2.u1521 = KTree.node A10K2.t1528 (nat_lit 25205093) (nat_lit 7249944786) (nat_lit 0) A10K2.t1529 from rfl, allE_node, rows1528, irow1521, rows1529]
  all_goals rfl

theorem atot1521 : totK PA10K2 A10K2.u1521 = [0, 0, 291230149053, 1892667343067, 3941207816526, 2692014811385, 563298174194, 30650496230, 0, 0] := by
  rw [show A10K2.u1521 = KTree.node A10K2.t1528 (nat_lit 25205093) (nat_lit 7249944786) (nat_lit 0) A10K2.t1529 from rfl, totK_node, tot1528, tot1529]
  decide +kernel

theorem arows1522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1522 = true := by
  rw [show A10K2.u1522 = KTree.node A10K2.t1530 (nat_lit 25219134) (nat_lit 14386157832) (nat_lit 0) A10K2.t1531 from rfl, allE_node, rows1530, irow1522, rows1531]
  all_goals rfl

theorem atot1522 : totK PA10K2 A10K2.u1522 = [0, 0, 561870517921, 2692433855083, 3972521869117, 1768013632341, 210401628521, 5546304973, 0, 0] := by
  rw [show A10K2.u1522 = KTree.node A10K2.t1530 (nat_lit 25219134) (nat_lit 14386157832) (nat_lit 0) A10K2.t1531 from rfl, totK_node, tot1530, tot1531]
  decide +kernel

theorem arows1524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1524 = true := by
  rw [show A10K2.u1524 = KTree.node A10K2.t1532 (nat_lit 25226828) (nat_lit 8034895184) (nat_lit 0) A10K2.t1533 from rfl, allE_node, rows1532, irow1524, rows1533]
  all_goals rfl

theorem atot1524 : totK PA10K2 A10K2.u1524 = [0, 476523753575, 2079390821772, 3678899849224, 2979474109396, 887034653731, 62629001825, 0, 0, 0] := by
  rw [show A10K2.u1524 = KTree.node A10K2.t1532 (nat_lit 25226828) (nat_lit 8034895184) (nat_lit 0) A10K2.t1533 from rfl, totK_node, tot1532, tot1533]
  decide +kernel

theorem arows1525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1525 = true := by
  rw [show A10K2.u1525 = KTree.node A10K2.t1534 (nat_lit 25301318) (nat_lit 11343809899) (nat_lit 0) A10K2.t1535 from rfl, allE_node, rows1534, irow1525, rows1535]
  all_goals rfl

theorem atot1525 : totK PA10K2 A10K2.u1525 = [0, 310356477484, 2040466340581, 4023277877684, 2695757194325, 555865702956, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1525 = KTree.node A10K2.t1534 (nat_lit 25301318) (nat_lit 11343809899) (nat_lit 0) A10K2.t1535 from rfl, totK_node, tot1534, tot1535]
  decide +kernel

theorem arows1534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1534 = true := by
  rw [show A10K2.u1534 = KTree.node A10K2.t1536 (nat_lit 25307690) (nat_lit 8764909657) (nat_lit 0) A10K2.t1537 from rfl, allE_node, rows1536, irow1534, rows1537]
  all_goals rfl

theorem atot1534 : totK PA10K2 A10K2.u1534 = [0, 518135067396, 2496513311181, 3885294697023, 2100448279913, 382333994502, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u1534 = KTree.node A10K2.t1536 (nat_lit 25307690) (nat_lit 8764909657) (nat_lit 0) A10K2.t1537 from rfl, totK_node, tot1536, tot1537]
  decide +kernel

theorem arows1535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1535 = true := by
  rw [show A10K2.u1535 = KTree.node A10K2.t1538 (nat_lit 25314707) (nat_lit 10551655136) (nat_lit 0) A10K2.t1539 from rfl, allE_node, rows1538, irow1535, rows1539]
  all_goals rfl

theorem atot1535 : totK PA10K2 A10K2.u1535 = [0, 809888342482, 3088038804012, 3635271696425, 1575423896552, 222015520115, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u1535 = KTree.node A10K2.t1538 (nat_lit 25314707) (nat_lit 10551655136) (nat_lit 0) A10K2.t1539 from rfl, totK_node, tot1538, tot1539]
  decide +kernel

theorem arows1537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1537 = true := by
  rw [show A10K2.u1537 = KTree.node A10K2.t1540 (nat_lit 25329670) (nat_lit 14536867999) (nat_lit 0) A10K2.t1541 from rfl, allE_node, rows1540, irow1537, rows1541]
  all_goals rfl

theorem atot1537 : totK PA10K2 A10K2.u1537 = [0, 0, 1241894322608, 4060157713337, 3401117943153, 694210178861, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u1537 = KTree.node A10K2.t1540 (nat_lit 25329670) (nat_lit 14536867999) (nat_lit 0) A10K2.t1541 from rfl, totK_node, tot1540, tot1541]
  decide +kernel

theorem arows1538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1538 = true := by
  rw [show A10K2.u1538 = KTree.node A10K2.t1542 (nat_lit 25339795) (nat_lit 10671537095) (nat_lit 0) A10K2.t1543 from rfl, allE_node, rows1542, irow1538, rows1543]
  all_goals rfl

theorem atot1538 : totK PA10K2 A10K2.u1538 = [0, 0, 995536472503, 3645784314753, 3843165116608, 1039217288939, 64934657765, 0, 0, 0] := by
  rw [show A10K2.u1538 = KTree.node A10K2.t1542 (nat_lit 25339795) (nat_lit 10671537095) (nat_lit 0) A10K2.t1543 from rfl, totK_node, tot1542, tot1543]
  decide +kernel

theorem arows1541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1541 = true := by
  rw [show A10K2.u1541 = KTree.node A10K2.t1544 (nat_lit 25348650) (nat_lit 8722866504) (nat_lit 0) A10K2.t1545 from rfl, allE_node, rows1544, irow1541, rows1545]
  all_goals rfl

theorem atot1541 : totK PA10K2 A10K2.u1541 = [0, 0, 529963201293, 2815155785397, 4146438895386, 1532749713074, 128855550409, 0, 0, 0] := by
  rw [show A10K2.u1541 = KTree.node A10K2.t1544 (nat_lit 25348650) (nat_lit 8722866504) (nat_lit 0) A10K2.t1545 from rfl, totK_node, tot1544, tot1545]
  decide +kernel

theorem arows1542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1542 = true := by
  rw [show A10K2.u1542 = KTree.node A10K2.t1546 (nat_lit 25364757) (nat_lit 6868054081) (nat_lit 0) A10K2.t1547 from rfl, allE_node, rows1546, irow1542, rows1547]
  all_goals rfl

theorem atot1542 : totK PA10K2 A10K2.u1542 = [0, 808480932972, 3100919930232, 3581007707548, 1594693391567, 646537699843, 167871307784, 6354482628, 0, 0] := by
  rw [show A10K2.u1542 = KTree.node A10K2.t1546 (nat_lit 25364757) (nat_lit 6868054081) (nat_lit 0) A10K2.t1547 from rfl, totK_node, tot1546, tot1547]
  decide +kernel

theorem arows1544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1544 = true := by
  rw [show A10K2.u1544 = KTree.node A10K2.t1548 (nat_lit 25369846) (nat_lit 16259176042) (nat_lit 0) A10K2.t1549 from rfl, allE_node, rows1548, irow1544, rows1549]
  all_goals rfl

theorem atot1544 : totK PA10K2 A10K2.u1544 = [0, 480589018088, 2324550400181, 4043796286370, 2599982678496, 547057278683, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u1544 = KTree.node A10K2.t1548 (nat_lit 25369846) (nat_lit 16259176042) (nat_lit 0) A10K2.t1549 from rfl, totK_node, tot1548, tot1549]
  decide +kernel

theorem arows1545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1545 = true := by
  rw [show A10K2.u1545 = KTree.node A10K2.t1550 (nat_lit 25391552) (nat_lit 15203328423) (nat_lit 0) A10K2.t1551 from rfl, allE_node, rows1550, irow1545, rows1551]
  all_goals rfl

theorem atot1545 : totK PA10K2 A10K2.u1545 = [0, 316669361890, 2039619073576, 4246772147181, 3056438499070, 558805563470, 12746179907, 0, 0, 0] := by
  rw [show A10K2.u1545 = KTree.node A10K2.t1550 (nat_lit 25391552) (nat_lit 15203328423) (nat_lit 0) A10K2.t1551 from rfl, totK_node, tot1550, tot1551]
  decide +kernel

theorem arows1549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1549 = true := by
  rw [show A10K2.u1549 = KTree.node A10K2.t1552 (nat_lit 25398037) (nat_lit 6851783544) (nat_lit 0) A10K2.t1553 from rfl, allE_node, rows1552, irow1549, rows1553]
  all_goals rfl

theorem atot1549 : totK PA10K2 A10K2.u1549 = [0, 0, 808334140526, 3288478786928, 4139111586493, 1614353582040, 130007473091, 0, 0, 0] := by
  rw [show A10K2.u1549 = KTree.node A10K2.t1552 (nat_lit 25398037) (nat_lit 6851783544) (nat_lit 0) A10K2.t1553 from rfl, totK_node, tot1552, tot1553]
  decide +kernel

theorem arows1550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1550 = true := by
  rw [show A10K2.u1550 = KTree.node A10K2.t1554 (nat_lit 25420223) (nat_lit 14252228148) (nat_lit 0) A10K2.t1555 from rfl, allE_node, rows1554, irow1550, rows1555]
  all_goals rfl

theorem atot1550 : totK PA10K2 A10K2.u1550 = [0, 0, 796458046475, 3106324982390, 4065858764025, 1876971213141, 264637460453, 6904928264, 0, 0] := by
  rw [show A10K2.u1550 = KTree.node A10K2.t1554 (nat_lit 25420223) (nat_lit 14252228148) (nat_lit 0) A10K2.t1555 from rfl, totK_node, tot1554, tot1555]
  decide +kernel

theorem arows1552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1552 = true := by
  rw [show A10K2.u1552 = KTree.node A10K2.t1556 (nat_lit 25425365) (nat_lit 1812634968) (nat_lit 0) A10K2.t1557 from rfl, allE_node, rows1556, irow1552, rows1557]
  all_goals rfl

theorem atot1552 : totK PA10K2 A10K2.u1552 = [0, 0, 318420800840, 1947959917420, 4007618931122, 3080740340745, 666967374361, 35608018656, 0, 0] := by
  rw [show A10K2.u1552 = KTree.node A10K2.t1556 (nat_lit 25425365) (nat_lit 1812634968) (nat_lit 0) A10K2.t1557 from rfl, totK_node, tot1556, tot1557]
  decide +kernel

theorem arows1553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1553 = true := by
  rw [show A10K2.u1553 = KTree.node A10K2.t1558 (nat_lit 25431473) (nat_lit 9345494442) (nat_lit 0) A10K2.t1559 from rfl, allE_node, rows1558, irow1553, rows1559]
  all_goals rfl

theorem atot1553 : totK PA10K2 A10K2.u1553 = [0, 0, 536751374829, 2574336845659, 3984064093220, 2120621295076, 395766045066, 25371180993, 0, 0] := by
  rw [show A10K2.u1553 = KTree.node A10K2.t1558 (nat_lit 25431473) (nat_lit 9345494442) (nat_lit 0) A10K2.t1559 from rfl, totK_node, tot1558, tot1559]
  decide +kernel

theorem arows1556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1556 = true := by
  rw [show A10K2.u1556 = KTree.node A10K2.t1560 (nat_lit 25444708) (nat_lit 13775768551) (nat_lit 0) A10K2.t1561 from rfl, allE_node, rows1560, irow1556, rows1561]
  all_goals rfl

theorem atot1556 : totK PA10K2 A10K2.u1556 = [0, 0, 741477655367, 2879433785723, 3763670381163, 1789779370736, 237786394025, 5460492893, 0, 0] := by
  rw [show A10K2.u1556 = KTree.node A10K2.t1560 (nat_lit 25444708) (nat_lit 13775768551) (nat_lit 0) A10K2.t1561 from rfl, totK_node, tot1560, tot1561]
  decide +kernel

theorem arows1557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1557 = true := by
  rw [show A10K2.u1557 = KTree.node A10K2.t1562 (nat_lit 25450787) (nat_lit 9932902688) (nat_lit 0) A10K2.t1563 from rfl, allE_node, rows1562, irow1557, rows1563]
  all_goals rfl

theorem atot1557 : totK PA10K2 A10K2.u1557 = [0, 0, 398717283765, 2528702939430, 4341740893037, 2049202513768, 231729266272, 5705019915, 0, 0] := by
  rw [show A10K2.u1557 = KTree.node A10K2.t1562 (nat_lit 25450787) (nat_lit 9932902688) (nat_lit 0) A10K2.t1563 from rfl, totK_node, tot1562, tot1563]
  decide +kernel

theorem arows1559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1559 = true := by
  rw [show A10K2.u1559 = KTree.node A10K2.t1564 (nat_lit 25457194) (nat_lit 3360576868) (nat_lit 0) A10K2.t1565 from rfl, allE_node, rows1564, irow1559, rows1565]
  all_goals rfl

theorem atot1559 : totK PA10K2 A10K2.u1559 = [0, 0, 293418347279, 1959579267075, 4116590798942, 3125086754654, 657160020204, 35031173917, 0, 0] := by
  rw [show A10K2.u1559 = KTree.node A10K2.t1564 (nat_lit 25457194) (nat_lit 3360576868) (nat_lit 0) A10K2.t1565 from rfl, totK_node, tot1564, tot1565]
  decide +kernel

theorem arows1560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1560 = true := by
  rw [show A10K2.u1560 = KTree.node A10K2.t1566 (nat_lit 25463858) (nat_lit 10654286037) (nat_lit 0) A10K2.t1567 from rfl, allE_node, rows1566, irow1560, rows1567]
  all_goals rfl

theorem atot1560 : totK PA10K2 A10K2.u1560 = [0, 0, 0, 660298093477, 2947641450769, 3891401992404, 1668849898404, 284733218373, 20060612110, 0] := by
  rw [show A10K2.u1560 = KTree.node A10K2.t1566 (nat_lit 25463858) (nat_lit 10654286037) (nat_lit 0) A10K2.t1567 from rfl, totK_node, tot1566, tot1567]
  decide +kernel

theorem arows1565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1565 = true := by
  rw [show A10K2.u1565 = KTree.node A10K2.t1568 (nat_lit 25477395) (nat_lit 7320338091) (nat_lit 0) A10K2.t1569 from rfl, allE_node, rows1568, irow1565, rows1569]
  all_goals rfl

theorem atot1565 : totK PA10K2 A10K2.u1565 = [0, 0, 0, 695774604560, 2718404714235, 3592190735558, 1825175678066, 317045497243, 10545135740, 0] := by
  rw [show A10K2.u1565 = KTree.node A10K2.t1568 (nat_lit 25477395) (nat_lit 7320338091) (nat_lit 0) A10K2.t1569 from rfl, totK_node, tot1568, tot1569]
  decide +kernel

theorem arows1566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1566 = true := by
  rw [show A10K2.u1566 = KTree.node A10K2.t1570 (nat_lit 25483585) (nat_lit 9660119737) (nat_lit 0) A10K2.t1571 from rfl, allE_node, rows1570, irow1566, rows1571]
  all_goals rfl

theorem atot1566 : totK PA10K2 A10K2.u1566 = [0, 0, 0, 570306846088, 2856168556967, 4089156302198, 1694614435112, 211677635039, 5528811039, 0] := by
  rw [show A10K2.u1566 = KTree.node A10K2.t1570 (nat_lit 25483585) (nat_lit 9660119737) (nat_lit 0) A10K2.t1571 from rfl, totK_node, tot1570, tot1571]
  decide +kernel

theorem arows1568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1568 = true := by
  rw [show A10K2.u1568 = KTree.node A10K2.t1572 (nat_lit 25559943) (nat_lit 14073800591) (nat_lit 0) A10K2.t1573 from rfl, allE_node, rows1572, irow1568, rows1573]
  all_goals rfl

theorem atot1568 : totK PA10K2 A10K2.u1568 = [0, 0, 786704115652, 3029334478915, 3815409121268, 1871859845853, 395163365355, 29010686974, 0, 0] := by
  rw [show A10K2.u1568 = KTree.node A10K2.t1572 (nat_lit 25559943) (nat_lit 14073800591) (nat_lit 0) A10K2.t1573 from rfl, totK_node, tot1572, tot1573]
  decide +kernel

theorem arows1569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1569 = true := by
  rw [show A10K2.u1569 = KTree.node A10K2.t1574 (nat_lit 25565953) (nat_lit 10111568244) (nat_lit 0) A10K2.t1575 from rfl, allE_node, rows1574, irow1569, rows1575]
  all_goals rfl

theorem atot1569 : totK PA10K2 A10K2.u1569 = [0, 0, 410191170018, 2037672092263, 3799550312225, 2642313233673, 561326509195, 30831673886, 0, 0] := by
  rw [show A10K2.u1569 = KTree.node A10K2.t1574 (nat_lit 25565953) (nat_lit 10111568244) (nat_lit 0) A10K2.t1575 from rfl, totK_node, tot1574, tot1575]
  decide +kernel

theorem arows1572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1572 = true := by
  rw [show A10K2.u1572 = KTree.node A10K2.t1576 (nat_lit 25574051) (nat_lit 10475069369) (nat_lit 0) A10K2.t1577 from rfl, allE_node, rows1576, irow1572, rows1577]
  all_goals rfl

theorem atot1572 : totK PA10K2 A10K2.u1572 = [0, 0, 613089487104, 2781449702860, 3893685382107, 1750363993216, 227004417248, 6034215561, 0, 0] := by
  rw [show A10K2.u1572 = KTree.node A10K2.t1576 (nat_lit 25574051) (nat_lit 10475069369) (nat_lit 0) A10K2.t1577 from rfl, totK_node, tot1576, tot1577]
  decide +kernel

theorem arows1573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1573 = true := by
  rw [show A10K2.u1573 = KTree.node A10K2.t1578 (nat_lit 25579873) (nat_lit 9042241876) (nat_lit 0) A10K2.t1579 from rfl, allE_node, rows1578, irow1573, rows1579]
  all_goals rfl

theorem atot1573 : totK PA10K2 A10K2.u1573 = [0, 0, 303792748393, 2185378504086, 4175867273562, 2237678931577, 310009101020, 6354482628, 0, 0] := by
  rw [show A10K2.u1573 = KTree.node A10K2.t1578 (nat_lit 25579873) (nat_lit 9042241876) (nat_lit 0) A10K2.t1579 from rfl, totK_node, tot1578, tot1579]
  decide +kernel

theorem arows1575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1575 = true := by
  rw [show A10K2.u1575 = KTree.node A10K2.t1580 (nat_lit 25594689) (nat_lit 8816870068) (nat_lit 0) A10K2.t1581 from rfl, allE_node, rows1580, irow1575, rows1581]
  all_goals rfl

theorem atot1575 : totK PA10K2 A10K2.u1575 = [0, 0, 0, 1178688236632, 3980681743529, 3537482205380, 776448230009, 38551375656, 0, 0] := by
  rw [show A10K2.u1575 = KTree.node A10K2.t1580 (nat_lit 25594689) (nat_lit 8816870068) (nat_lit 0) A10K2.t1581 from rfl, totK_node, tot1580, tot1581]
  decide +kernel

theorem arows1576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1576 = true := by
  rw [show A10K2.u1576 = KTree.node A10K2.t1582 (nat_lit 25609877) (nat_lit 6416178715) (nat_lit 0) A10K2.t1583 from rfl, allE_node, rows1582, irow1576, rows1583]
  all_goals rfl

theorem atot1576 : totK PA10K2 A10K2.u1576 = [0, 0, 0, 801316010649, 3403646484482, 3848940939582, 1090768282435, 69005204554, 0, 0] := by
  rw [show A10K2.u1576 = KTree.node A10K2.t1582 (nat_lit 25609877) (nat_lit 6416178715) (nat_lit 0) A10K2.t1583 from rfl, totK_node, tot1582, tot1583]
  decide +kernel

theorem arows1580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1580 = true := by
  rw [show A10K2.u1580 = KTree.node A10K2.t1584 (nat_lit 25625081) (nat_lit 6361856814) (nat_lit 0) A10K2.t1585 from rfl, allE_node, rows1584, irow1580, rows1585]
  all_goals rfl

theorem atot1580 : totK PA10K2 A10K2.u1580 = [0, 0, 805307870785, 2688415737271, 2979863595199, 1978753904038, 952376547130, 160162151064, 5676195732, 0] := by
  rw [show A10K2.u1580 = KTree.node A10K2.t1584 (nat_lit 25625081) (nat_lit 6361856814) (nat_lit 0) A10K2.t1585 from rfl, totK_node, tot1584, tot1585]
  decide +kernel

theorem arows1581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1581 = true := by
  rw [show A10K2.u1581 = KTree.node A10K2.t1586 (nat_lit 25630981) (nat_lit 6973973383) (nat_lit 0) A10K2.t1587 from rfl, allE_node, rows1586, irow1581, rows1587]
  all_goals rfl

theorem atot1581 : totK PA10K2 A10K2.u1581 = [0, 0, 368139604616, 2202383651547, 4289467453703, 2622409861492, 466909003102, 25313348169, 0, 0] := by
  rw [show A10K2.u1581 = KTree.node A10K2.t1586 (nat_lit 25630981) (nat_lit 6973973383) (nat_lit 0) A10K2.t1587 from rfl, totK_node, tot1586, tot1587]
  decide +kernel

theorem arows1583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1583 = true := by
  rw [show A10K2.u1583 = KTree.node A10K2.t1588 (nat_lit 25653249) (nat_lit 10590452259) (nat_lit 0) A10K2.t1589 from rfl, allE_node, rows1588, irow1583, rows1589]
  all_goals rfl

theorem atot1583 : totK PA10K2 A10K2.u1583 = [0, 0, 428173725744, 2562653408207, 4442049984594, 2519974883331, 355564555476, 6853348008, 0, 0] := by
  rw [show A10K2.u1583 = KTree.node A10K2.t1588 (nat_lit 25653249) (nat_lit 10590452259) (nat_lit 0) A10K2.t1589 from rfl, totK_node, tot1588, tot1589]
  decide +kernel

theorem arows1584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1584 = true := by
  rw [show A10K2.u1584 = KTree.node A10K2.t1590 (nat_lit 25765930) (nat_lit 9114793847) (nat_lit 0) A10K2.t1591 from rfl, allE_node, rows1590, irow1584, rows1591]
  all_goals rfl

theorem atot1584 : totK PA10K2 A10K2.u1584 = [0, 843291061595, 3089100912431, 3284787057913, 1328658581437, 891793635261, 370422949141, 29687484142, 0, 0] := by
  rw [show A10K2.u1584 = KTree.node A10K2.t1590 (nat_lit 25765930) (nat_lit 9114793847) (nat_lit 0) A10K2.t1591 from rfl, totK_node, tot1590, tot1591]
  decide +kernel

theorem arows1587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1587 = true := by
  rw [show A10K2.u1587 = KTree.node A10K2.t1592 (nat_lit 25770540) (nat_lit 11893281741) (nat_lit 0) A10K2.t1593 from rfl, allE_node, rows1592, irow1587, rows1593]
  all_goals rfl

theorem atot1587 : totK PA10K2 A10K2.u1587 = [0, 345065522154, 1830877047948, 3763732765249, 2955597815134, 639244287116, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1587 = KTree.node A10K2.t1592 (nat_lit 25770540) (nat_lit 11893281741) (nat_lit 0) A10K2.t1593 from rfl, totK_node, tot1592, tot1593]
  decide +kernel

theorem arows1588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1588 = true := by
  rw [show A10K2.u1588 = KTree.node A10K2.t1594 (nat_lit 25776134) (nat_lit 10441194946) (nat_lit 0) A10K2.t1595 from rfl, allE_node, rows1594, irow1588, rows1595]
  all_goals rfl

theorem atot1588 : totK PA10K2 A10K2.u1588 = [0, 401413542662, 2466305591179, 4207738311675, 2128620921223, 225297043004, 0, 0, 0, 0] := by
  rw [show A10K2.u1588 = KTree.node A10K2.t1594 (nat_lit 25776134) (nat_lit 10441194946) (nat_lit 0) A10K2.t1595 from rfl, totK_node, tot1594, tot1595]
  decide +kernel

theorem arows1590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1590 = true := by
  rw [show A10K2.u1590 = KTree.node A10K2.t1596 (nat_lit 25783921) (nat_lit 7516495470) (nat_lit 0) A10K2.t1597 from rfl, allE_node, rows1596, irow1590, rows1597]
  all_goals rfl

theorem atot1590 : totK PA10K2 A10K2.u1590 = [0, 595891457874, 2742025169434, 4156794987976, 2293919783345, 395673403593, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u1590 = KTree.node A10K2.t1596 (nat_lit 25783921) (nat_lit 7516495470) (nat_lit 0) A10K2.t1597 from rfl, totK_node, tot1596, tot1597]
  decide +kernel

theorem arows1591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1591 = true := by
  rw [show A10K2.u1591 = KTree.node A10K2.t1598 (nat_lit 25798550) (nat_lit 15591510911) (nat_lit 0) A10K2.t1599 from rfl, allE_node, rows1598, irow1591, rows1599]
  all_goals rfl

theorem atot1591 : totK PA10K2 A10K2.u1591 = [0, 0, 885770114087, 3534234252241, 4045219579986, 1252632047250, 75304964751, 0, 0, 0] := by
  rw [show A10K2.u1591 = KTree.node A10K2.t1598 (nat_lit 25798550) (nat_lit 15591510911) (nat_lit 0) A10K2.t1599 from rfl, totK_node, tot1598, tot1599]
  decide +kernel

theorem arows1597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1597 = true := by
  rw [show A10K2.u1597 = KTree.node A10K2.t1600 (nat_lit 25803268) (nat_lit 11192108331) (nat_lit 0) A10K2.t1601 from rfl, allE_node, rows1600, irow1597, rows1601]
  all_goals rfl

theorem atot1597 : totK PA10K2 A10K2.u1597 = [0, 0, 382666486117, 2046725730063, 3806884523111, 2621495500019, 566268925200, 31082886609, 0, 0] := by
  rw [show A10K2.u1597 = KTree.node A10K2.t1600 (nat_lit 25803268) (nat_lit 11192108331) (nat_lit 0) A10K2.t1601 from rfl, totK_node, tot1600, tot1601]
  decide +kernel

theorem arows1598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1598 = true := by
  rw [show A10K2.u1598 = KTree.node A10K2.t1602 (nat_lit 25809152) (nat_lit 13759238478) (nat_lit 0) A10K2.t1603 from rfl, allE_node, rows1602, irow1598, rows1603]
  all_goals rfl

theorem atot1598 : totK PA10K2 A10K2.u1598 = [0, 0, 477110768513, 2436179096865, 4088371401523, 2031758334225, 245863934142, 6121173289, 0, 0] := by
  rw [show A10K2.u1598 = KTree.node A10K2.t1602 (nat_lit 25809152) (nat_lit 13759238478) (nat_lit 0) A10K2.t1603 from rfl, totK_node, tot1602, tot1603]
  decide +kernel

theorem arows1600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1600 = true := by
  rw [show A10K2.u1600 = KTree.node A10K2.t1604 (nat_lit 25816805) (nat_lit 4821907243) (nat_lit 0) A10K2.t1605 from rfl, allE_node, rows1604, irow1600, rows1605]
  all_goals rfl

theorem atot1600 : totK PA10K2 A10K2.u1600 = [0, 560298200195, 2164507727307, 3469395392404, 2847504933439, 889254457585, 62919018435, 0, 0, 0] := by
  rw [show A10K2.u1600 = KTree.node A10K2.t1604 (nat_lit 25816805) (nat_lit 4821907243) (nat_lit 0) A10K2.t1605 from rfl, totK_node, tot1604, tot1605]
  decide +kernel

theorem arows1601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1601 = true := by
  rw [show A10K2.u1601 = KTree.node A10K2.t1606 (nat_lit 25827593) (nat_lit 9690107151) (nat_lit 0) A10K2.t1607 from rfl, allE_node, rows1606, irow1601, rows1607]
  all_goals rfl

theorem atot1601 : totK PA10K2 A10K2.u1601 = [0, 369395021760, 2191554321159, 3956989560052, 2434433537244, 471323818339, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1601 = KTree.node A10K2.t1606 (nat_lit 25827593) (nat_lit 9690107151) (nat_lit 0) A10K2.t1607 from rfl, totK_node, tot1606, tot1607]
  decide +kernel

theorem arows1604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1604 = true := by
  rw [show A10K2.u1604 = KTree.node A10K2.t1608 (nat_lit 25834773) (nat_lit 6888461581) (nat_lit 0) A10K2.t1609 from rfl, allE_node, rows1608, irow1604, rows1609]
  all_goals rfl

theorem atot1604 : totK PA10K2 A10K2.u1604 = [0, 400532854576, 2165589604248, 3896332935098, 2656607686195, 566811315053, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1604 = KTree.node A10K2.t1608 (nat_lit 25834773) (nat_lit 6888461581) (nat_lit 0) A10K2.t1609 from rfl, totK_node, tot1608, tot1609]
  decide +kernel

theorem arows1605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1605 = true := by
  rw [show A10K2.u1605 = KTree.node A10K2.t1610 (nat_lit 25839099) (nat_lit 6243864390) (nat_lit 0) A10K2.t1611 from rfl, allE_node, rows1610, irow1605, rows1611]
  all_goals rfl

theorem atot1605 : totK PA10K2 A10K2.u1605 = [0, 818722742184, 3259160404907, 3888938330558, 1408446845668, 130298872857, 0, 0, 0, 0] := by
  rw [show A10K2.u1605 = KTree.node A10K2.t1610 (nat_lit 25839099) (nat_lit 6243864390) (nat_lit 0) A10K2.t1611 from rfl, totK_node, tot1610, tot1611]
  decide +kernel

theorem arows1607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1607 = true := by
  rw [show A10K2.u1607 = KTree.node A10K2.t1612 (nat_lit 25853986) (nat_lit 7237803920) (nat_lit 0) A10K2.t1613 from rfl, allE_node, rows1612, irow1607, rows1613]
  all_goals rfl

theorem atot1607 : totK PA10K2 A10K2.u1607 = [0, 0, 1209562884289, 4078952836188, 3470146080154, 677059867023, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u1607 = KTree.node A10K2.t1612 (nat_lit 25853986) (nat_lit 7237803920) (nat_lit 0) A10K2.t1613 from rfl, totK_node, tot1612, tot1613]
  decide +kernel

theorem arows1608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1608 = true := by
  rw [show A10K2.u1608 = KTree.node A10K2.t1614 (nat_lit 25864709) (nat_lit 6791634080) (nat_lit 0) A10K2.t1615 from rfl, allE_node, rows1614, irow1608, rows1615]
  all_goals rfl

theorem atot1608 : totK PA10K2 A10K2.u1608 = [0, 0, 1006567176081, 3631860609871, 3830466922956, 1077006465417, 65012682590, 0, 0, 0] := by
  rw [show A10K2.u1608 = KTree.node A10K2.t1614 (nat_lit 25864709) (nat_lit 6791634080) (nat_lit 0) A10K2.t1615 from rfl, totK_node, tot1614, tot1615]
  decide +kernel

theorem arows1612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1612 = true := by
  rw [show A10K2.u1612 = KTree.node A10K2.t1616 (nat_lit 25872910) (nat_lit 8179398219) (nat_lit 0) A10K2.t1617 from rfl, allE_node, rows1616, irow1612, rows1617]
  all_goals rfl

theorem atot1612 : totK PA10K2 A10K2.u1612 = [0, 0, 578058941085, 2949913007963, 4211467387419, 1501372327395, 128855550409, 0, 0, 0] := by
  rw [show A10K2.u1612 = KTree.node A10K2.t1616 (nat_lit 25872910) (nat_lit 8179398219) (nat_lit 0) A10K2.t1617 from rfl, totK_node, tot1616, tot1617]
  decide +kernel

theorem arows1613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1613 = true := by
  rw [show A10K2.u1613 = KTree.node A10K2.t1618 (nat_lit 26028194) (nat_lit 14142712800) (nat_lit 0) A10K2.t1619 from rfl, allE_node, rows1618, irow1613, rows1619]
  all_goals rfl

theorem atot1613 : totK PA10K2 A10K2.u1613 = [0, 0, 840796871205, 3125153037681, 3786338534462, 1641866723387, 237392859745, 6354482628, 0, 0] := by
  rw [show A10K2.u1613 = KTree.node A10K2.t1618 (nat_lit 26028194) (nat_lit 14142712800) (nat_lit 0) A10K2.t1619 from rfl, totK_node, tot1618, tot1619]
  decide +kernel

theorem arows1615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1615 = true := by
  rw [show A10K2.u1615 = KTree.node A10K2.t1620 (nat_lit 26032915) (nat_lit 10561199254) (nat_lit 0) A10K2.t1621 from rfl, allE_node, rows1620, irow1615, rows1621]
  all_goals rfl

theorem atot1615 : totK PA10K2 A10K2.u1615 = [0, 0, 460257217030, 2153205979927, 3701945256224, 2613455234177, 565820195343, 31768748853, 0, 0] := by
  rw [show A10K2.u1615 = KTree.node A10K2.t1620 (nat_lit 26032915) (nat_lit 10561199254) (nat_lit 0) A10K2.t1621 from rfl, totK_node, tot1620, tot1621]
  decide +kernel

theorem arows1616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1616 = true := by
  rw [show A10K2.u1616 = KTree.node A10K2.t1622 (nat_lit 26038613) (nat_lit 6898575536) (nat_lit 0) A10K2.t1623 from rfl, allE_node, rows1622, irow1616, rows1623]
  all_goals rfl

theorem atot1616 : totK PA10K2 A10K2.u1616 = [0, 0, 439631338192, 2414275832880, 4140562597035, 2092860962726, 247202306788, 6239673734, 0, 0] := by
  rw [show A10K2.u1616 = KTree.node A10K2.t1622 (nat_lit 26038613) (nat_lit 6898575536) (nat_lit 0) A10K2.t1623 from rfl, totK_node, tot1622, tot1623]
  decide +kernel

theorem arows1619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1619 = true := by
  rw [show A10K2.u1619 = KTree.node A10K2.t1624 (nat_lit 26046393) (nat_lit 6784836980) (nat_lit 0) A10K2.t1625 from rfl, allE_node, rows1624, irow1619, rows1625]
  all_goals rfl

theorem atot1619 : totK PA10K2 A10K2.u1619 = [0, 0, 551218273221, 2658493732417, 4271519691092, 2394271777533, 341068089987, 6962742351, 0, 0] := by
  rw [show A10K2.u1619 = KTree.node A10K2.t1624 (nat_lit 26046393) (nat_lit 6784836980) (nat_lit 0) A10K2.t1625 from rfl, totK_node, tot1624, tot1625]
  decide +kernel

theorem arows1620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1620 = true := by
  rw [show A10K2.u1620 = KTree.node A10K2.t1626 (nat_lit 26087425) (nat_lit 10630474206) (nat_lit 0) A10K2.t1627 from rfl, allE_node, rows1626, irow1620, rows1627]
  all_goals rfl

theorem atot1620 : totK PA10K2 A10K2.u1620 = [0, 0, 663483977473, 2894508747009, 3967184438541, 1734265513616, 218632683327, 5460492893, 0, 0] := by
  rw [show A10K2.u1620 = KTree.node A10K2.t1626 (nat_lit 26087425) (nat_lit 10630474206) (nat_lit 0) A10K2.t1627 from rfl, totK_node, tot1626, tot1627]
  decide +kernel

theorem arows1622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1622 = true := by
  rw [show A10K2.u1622 = KTree.node A10K2.t1628 (nat_lit 26094783) (nat_lit 13834214757) (nat_lit 0) A10K2.t1629 from rfl, allE_node, rows1628, irow1622, rows1629]
  all_goals rfl

theorem atot1622 : totK PA10K2 A10K2.u1622 = [0, 0, 555874964089, 2698858815986, 4059724057343, 2001325013124, 334869284521, 25734533292, 0, 0] := by
  rw [show A10K2.u1622 = KTree.node A10K2.t1628 (nat_lit 26094783) (nat_lit 13834214757) (nat_lit 0) A10K2.t1629 from rfl, totK_node, tot1628, tot1629]
  decide +kernel

theorem arows1623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1623 = true := by
  rw [show A10K2.u1623 = KTree.node A10K2.t1630 (nat_lit 26100487) (nat_lit 7414568227) (nat_lit 0) A10K2.t1631 from rfl, allE_node, rows1630, irow1623, rows1631]
  all_goals rfl

theorem atot1623 : totK PA10K2 A10K2.u1623 = [0, 0, 818358102331, 2955795315553, 3683579164093, 1755520333842, 243955317327, 6034215561, 0, 0] := by
  rw [show A10K2.u1623 = KTree.node A10K2.t1630 (nat_lit 26100487) (nat_lit 7414568227) (nat_lit 0) A10K2.t1631 from rfl, totK_node, tot1630, tot1631]
  decide +kernel

theorem arows1628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1628 = true := by
  rw [show A10K2.u1628 = KTree.node A10K2.t1632 (nat_lit 26106069) (nat_lit 6365199804) (nat_lit 0) A10K2.t1633 from rfl, allE_node, rows1632, irow1628, rows1633]
  all_goals rfl

theorem atot1628 : totK PA10K2 A10K2.u1628 = [0, 0, 0, 1564580140723, 4376548901246, 2914600291703, 463566480176, 11740475125, 0, 0] := by
  rw [show A10K2.u1628 = KTree.node A10K2.t1632 (nat_lit 26106069) (nat_lit 6365199804) (nat_lit 0) A10K2.t1633 from rfl, totK_node, tot1632, tot1633]
  decide +kernel

theorem arows1629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1629 = true := by
  rw [show A10K2.u1629 = KTree.node A10K2.t1634 (nat_lit 26126370) (nat_lit 9239556487) (nat_lit 0) A10K2.t1635 from rfl, allE_node, rows1634, irow1629, rows1635]
  all_goals rfl

theorem atot1629 : totK PA10K2 A10K2.u1629 = [0, 0, 0, 1145895439782, 3972010617926, 3574674977540, 709514479111, 38478929365, 0, 0] := by
  rw [show A10K2.u1629 = KTree.node A10K2.t1634 (nat_lit 26126370) (nat_lit 9239556487) (nat_lit 0) A10K2.t1635 from rfl, totK_node, tot1634, tot1635]
  decide +kernel

theorem arows1631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1631 = true := by
  rw [show A10K2.u1631 = KTree.node A10K2.t1636 (nat_lit 26134870) (nat_lit 8631440058) (nat_lit 0) A10K2.t1637 from rfl, allE_node, rows1636, irow1631, rows1637]
  all_goals rfl

theorem atot1631 : totK PA10K2 A10K2.u1631 = [0, 0, 0, 573215416804, 2995302535186, 4157090520983, 1355742832204, 100662997981, 0, 0] := by
  rw [show A10K2.u1631 = KTree.node A10K2.t1636 (nat_lit 26134870) (nat_lit 8631440058) (nat_lit 0) A10K2.t1637 from rfl, totK_node, tot1636, tot1637]
  decide +kernel

theorem arows1632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1632 = true := by
  rw [show A10K2.u1632 = KTree.node A10K2.t1638 (nat_lit 26216566) (nat_lit 14092359785) (nat_lit 0) A10K2.t1639 from rfl, allE_node, rows1638, irow1632, rows1639]
  all_goals rfl

theorem atot1632 : totK PA10K2 A10K2.u1632 = [0, 812666997328, 3078376079659, 3436726914461, 1089240963754, 437780664131, 557610482693, 144939828619, 6239673734, 0] := by
  rw [show A10K2.u1632 = KTree.node A10K2.t1638 (nat_lit 26216566) (nat_lit 14092359785) (nat_lit 0) A10K2.t1639 from rfl, totK_node, tot1638, tot1639]
  decide +kernel

theorem arows1635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1635 = true := by
  rw [show A10K2.u1635 = KTree.node A10K2.t1640 (nat_lit 26221408) (nat_lit 11322649501) (nat_lit 0) A10K2.t1641 from rfl, allE_node, rows1640, irow1635, rows1641]
  all_goals rfl

theorem atot1635 : totK PA10K2 A10K2.u1635 = [0, 407498917581, 2024534095357, 3771500647006, 2660025545110, 559628740854, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1635 = KTree.node A10K2.t1640 (nat_lit 26221408) (nat_lit 11322649501) (nat_lit 0) A10K2.t1641 from rfl, totK_node, tot1640, tot1641]
  decide +kernel

theorem arows1636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1636 = true := by
  rw [show A10K2.u1636 = KTree.node A10K2.t1642 (nat_lit 26235150) (nat_lit 10208692474) (nat_lit 0) A10K2.t1643 from rfl, allE_node, rows1642, irow1636, rows1643]
  all_goals rfl

theorem atot1636 : totK PA10K2 A10K2.u1636 = [0, 470744247589, 2494597422324, 4068384704661, 2156959739488, 302040533576, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1636 = KTree.node A10K2.t1642 (nat_lit 26235150) (nat_lit 10208692474) (nat_lit 0) A10K2.t1643 from rfl, totK_node, tot1642, tot1643]
  decide +kernel

theorem arows1638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1638 = true := by
  rw [show A10K2.u1638 = KTree.node A10K2.t1644 (nat_lit 26243130) (nat_lit 8129875496) (nat_lit 0) A10K2.t1645 from rfl, allE_node, rows1644, irow1638, rows1645]
  all_goals rfl

theorem atot1638 : totK PA10K2 A10K2.u1638 = [0, 388272196882, 2222404232702, 4095182574757, 2796909920495, 647669334061, 36540832150, 0, 0, 0] := by
  rw [show A10K2.u1638 = KTree.node A10K2.t1644 (nat_lit 26243130) (nat_lit 8129875496) (nat_lit 0) A10K2.t1645 from rfl, totK_node, tot1644, tot1645]
  decide +kernel

theorem arows1639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1639 = true := by
  rw [show A10K2.u1639 = KTree.node A10K2.t1646 (nat_lit 26250069) (nat_lit 6498896228) (nat_lit 0) A10K2.t1647 from rfl, allE_node, rows1646, irow1639, rows1647]
  all_goals rfl

theorem atot1639 : totK PA10K2 A10K2.u1639 = [0, 0, 692344025543, 2976582371470, 3907319172405, 1660261437339, 279292193853, 20060612110, 0, 0] := by
  rw [show A10K2.u1639 = KTree.node A10K2.t1646 (nat_lit 26250069) (nat_lit 6498896228) (nat_lit 0) A10K2.t1647 from rfl, totK_node, tot1646, tot1647]
  decide +kernel

theorem arows1643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1643 = true := by
  rw [show A10K2.u1643 = KTree.node A10K2.t1648 (nat_lit 26263821) (nat_lit 5899193217) (nat_lit 0) A10K2.t1649 from rfl, allE_node, rows1648, irow1643, rows1649]
  all_goals rfl

theorem atot1643 : totK PA10K2 A10K2.u1643 = [0, 0, 669583424523, 2691230023829, 3736723993535, 1965607281586, 333341935828, 10589884120, 0, 0] := by
  rw [show A10K2.u1643 = KTree.node A10K2.t1648 (nat_lit 26263821) (nat_lit 5899193217) (nat_lit 0) A10K2.t1649 from rfl, totK_node, tot1648, tot1649]
  decide +kernel

theorem arows1644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1644 = true := by
  rw [show A10K2.u1644 = KTree.node A10K2.t1650 (nat_lit 26269907) (nat_lit 9232302919) (nat_lit 0) A10K2.t1651 from rfl, allE_node, rows1650, irow1644, rows1651]
  all_goals rfl

theorem atot1644 : totK PA10K2 A10K2.u1644 = [0, 0, 534422975079, 2753276972595, 4175061125756, 1830418724144, 219178372242, 5546304973, 0, 0] := by
  rw [show A10K2.u1644 = KTree.node A10K2.t1650 (nat_lit 26269907) (nat_lit 9232302919) (nat_lit 0) A10K2.t1651 from rfl, totK_node, tot1650, tot1651]
  decide +kernel

theorem arows1646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1646 = true := by
  rw [show A10K2.u1646 = KTree.node A10K2.t1652 (nat_lit 26290241) (nat_lit 9820229035) (nat_lit 0) A10K2.t1653 from rfl, allE_node, rows1652, irow1646, rows1653]
  all_goals rfl

theorem atot1646 : totK PA10K2 A10K2.u1646 = [0, 763974328874, 2984440135723, 3791469650639, 1888691420131, 444927984425, 30829329317, 0, 0, 0] := by
  rw [show A10K2.u1646 = KTree.node A10K2.t1652 (nat_lit 26290241) (nat_lit 9820229035) (nat_lit 0) A10K2.t1653 from rfl, totK_node, tot1652, tot1653]
  decide +kernel

theorem arows1647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1647 = true := by
  rw [show A10K2.u1647 = KTree.node A10K2.t1654 (nat_lit 26295443) (nat_lit 10901359787) (nat_lit 0) A10K2.t1655 from rfl, allE_node, rows1654, irow1647, rows1655]
  all_goals rfl

theorem atot1647 : totK PA10K2 A10K2.u1647 = [0, 482480945578, 2199064227812, 3646552476083, 2589013179651, 579033600936, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1647 = KTree.node A10K2.t1654 (nat_lit 26295443) (nat_lit 10901359787) (nat_lit 0) A10K2.t1655 from rfl, totK_node, tot1654, tot1655]
  decide +kernel

theorem arows1650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1650 = true := by
  rw [show A10K2.u1650 = KTree.node A10K2.t1656 (nat_lit 26300780) (nat_lit 12674247042) (nat_lit 0) A10K2.t1657 from rfl, allE_node, rows1656, irow1650, rows1657]
  all_goals rfl

theorem atot1650 : totK PA10K2 A10K2.u1650 = [0, 448778378692, 2400070984139, 4135205118489, 2208450970268, 302022523840, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1650 = KTree.node A10K2.t1656 (nat_lit 26300780) (nat_lit 12674247042) (nat_lit 0) A10K2.t1657 from rfl, totK_node, tot1656, tot1657]
  decide +kernel

theorem arows1651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1651 = true := by
  rw [show A10K2.u1651 = KTree.node A10K2.t1658 (nat_lit 26322148) (nat_lit 13007097568) (nat_lit 0) A10K2.t1659 from rfl, allE_node, rows1658, irow1651, rows1659]
  all_goals rfl

theorem atot1651 : totK PA10K2 A10K2.u1651 = [0, 117348215122, 1473057244452, 3944125303156, 3319765604969, 740363890070, 33441838611, 0, 0, 0] := by
  rw [show A10K2.u1651 = KTree.node A10K2.t1658 (nat_lit 26322148) (nat_lit 13007097568) (nat_lit 0) A10K2.t1659 from rfl, totK_node, tot1658, tot1659]
  decide +kernel

theorem arows1653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1653 = true := by
  rw [show A10K2.u1653 = KTree.node A10K2.t1660 (nat_lit 26326963) (nat_lit 8272864124) (nat_lit 32) A10K2.t1661 from rfl, allE_node, rows1660, irow1653, rows1661]
  all_goals rfl

theorem atot1653 : totK PA10K2 A10K2.u1653 = [0, 0, 390829351832, 2172571539853, 4021495782721, 2492304261904, 469333573417, 31082886609, 0, 0] := by
  rw [show A10K2.u1653 = KTree.node A10K2.t1660 (nat_lit 26326963) (nat_lit 8272864124) (nat_lit 32) A10K2.t1661 from rfl, totK_node, tot1660, tot1661]
  decide +kernel

theorem arows1654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1654 = true := by
  rw [show A10K2.u1654 = KTree.node A10K2.t1662 (nat_lit 26331795) (nat_lit 10813214428) (nat_lit 0) A10K2.t1663 from rfl, allE_node, rows1662, irow1654, rows1663]
  all_goals rfl

theorem atot1654 : totK PA10K2 A10K2.u1654 = [0, 0, 577819886779, 2875503554137, 4199041787271, 1596486754369, 115691696964, 0, 0, 0] := by
  rw [show A10K2.u1654 = KTree.node A10K2.t1662 (nat_lit 26331795) (nat_lit 10813214428) (nat_lit 0) A10K2.t1663 from rfl, totK_node, tot1662, tot1663]
  decide +kernel

theorem arows1661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1661 = true := by
  rw [show A10K2.u1661 = KTree.node A10K2.t1664 (nat_lit 26345868) (nat_lit 8936853582) (nat_lit 0) A10K2.t1665 from rfl, allE_node, rows1664, irow1661, rows1665]
  all_goals rfl

theorem atot1661 : totK PA10K2 A10K2.u1661 = [0, 679093097446, 2616507582438, 3294205637042, 1927250898553, 856843431972, 161460762868, 6121173289, 0, 0] := by
  rw [show A10K2.u1661 = KTree.node A10K2.t1664 (nat_lit 26345868) (nat_lit 8936853582) (nat_lit 0) A10K2.t1665 from rfl, totK_node, tot1664, tot1665]
  decide +kernel

theorem arows1662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1662 = true := by
  rw [show A10K2.u1662 = KTree.node A10K2.t1666 (nat_lit 26351771) (nat_lit 9945671724) (nat_lit 0) A10K2.t1667 from rfl, allE_node, rows1666, irow1662, rows1667]
  all_goals rfl

theorem atot1662 : totK PA10K2 A10K2.u1662 = [0, 350750747707, 1974426448777, 3826031502905, 2723021479558, 581845305386, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1662 = KTree.node A10K2.t1666 (nat_lit 26351771) (nat_lit 9945671724) (nat_lit 0) A10K2.t1667 from rfl, totK_node, tot1666, tot1667]
  decide +kernel

theorem arows1664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1664 = true := by
  rw [show A10K2.u1664 = KTree.node A10K2.t1668 (nat_lit 26357717) (nat_lit 2562187344) (nat_lit 0) A10K2.t1669 from rfl, allE_node, rows1668, irow1664, rows1669]
  all_goals rfl

theorem atot1664 : totK PA10K2 A10K2.u1664 = [0, 416581648771, 2253415823196, 3922644438899, 2320328063629, 414690145910, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u1664 = KTree.node A10K2.t1668 (nat_lit 26357717) (nat_lit 2562187344) (nat_lit 0) A10K2.t1669 from rfl, totK_node, tot1668, tot1669]
  decide +kernel

theorem arows1665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1665 = true := by
  rw [show A10K2.u1665 = KTree.node A10K2.t1670 (nat_lit 26363149) (nat_lit 5921011772) (nat_lit 0) A10K2.t1671 from rfl, allE_node, rows1670, irow1665, rows1671]
  all_goals rfl

theorem atot1665 : totK PA10K2 A10K2.u1665 = [0, 849905977144, 3219375193865, 3713429757120, 1494810912059, 195279377631, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u1665 = KTree.node A10K2.t1670 (nat_lit 26363149) (nat_lit 5921011772) (nat_lit 0) A10K2.t1671 from rfl, totK_node, tot1670, tot1671]
  decide +kernel

theorem arows1668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1668 = true := by
  rw [show A10K2.u1668 = KTree.node A10K2.t1672 (nat_lit 26368660) (nat_lit 12735388338) (nat_lit 0) A10K2.t1673 from rfl, allE_node, rows1672, irow1668, rows1673]
  all_goals rfl

theorem atot1668 : totK PA10K2 A10K2.u1668 = [0, 0, 1377716775407, 4121637868347, 3242247950710, 662816523127, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u1668 = KTree.node A10K2.t1672 (nat_lit 26368660) (nat_lit 12735388338) (nat_lit 0) A10K2.t1673 from rfl, totK_node, tot1672, tot1673]
  decide +kernel

theorem arows1669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1669 = true := by
  rw [show A10K2.u1669 = KTree.node A10K2.t1674 (nat_lit 26388133) (nat_lit 6969042730) (nat_lit 0) A10K2.t1675 from rfl, allE_node, rows1674, irow1669, rows1675]
  all_goals rfl

theorem atot1669 : totK PA10K2 A10K2.u1669 = [0, 0, 909798315334, 3602826426195, 3895497524425, 1014073785918, 45620856191, 0, 0, 0] := by
  rw [show A10K2.u1669 = KTree.node A10K2.t1674 (nat_lit 26388133) (nat_lit 6969042730) (nat_lit 0) A10K2.t1675 from rfl, totK_node, tot1674, tot1675]
  decide +kernel

theorem arows1671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1671 = true := by
  rw [show A10K2.u1671 = KTree.node A10K2.t1676 (nat_lit 26396381) (nat_lit 5435148625) (nat_lit 0) A10K2.t1677 from rfl, allE_node, rows1676, irow1671, rows1677]
  all_goals rfl

theorem atot1671 : totK PA10K2 A10K2.u1671 = [0, 0, 843656643622, 3361369629356, 3903338321486, 1173665537393, 89385601782, 0, 0, 0] := by
  rw [show A10K2.u1671 = KTree.node A10K2.t1676 (nat_lit 26396381) (nat_lit 5435148625) (nat_lit 0) A10K2.t1677 from rfl, totK_node, tot1676, tot1677]
  decide +kernel

theorem arows1672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1672 = true := by
  rw [show A10K2.u1672 = KTree.node A10K2.t1678 (nat_lit 26476868) (nat_lit 12811252744) (nat_lit 0) A10K2.t1679 from rfl, allE_node, rows1678, irow1672, rows1679]
  all_goals rfl

theorem atot1672 : totK PA10K2 A10K2.u1672 = [0, 0, 671879754400, 2795526514553, 3904403611270, 1764245709630, 265569053098, 6354482628, 0, 0] := by
  rw [show A10K2.u1672 = KTree.node A10K2.t1678 (nat_lit 26476868) (nat_lit 12811252744) (nat_lit 0) A10K2.t1679 from rfl, totK_node, tot1678, tot1679]
  decide +kernel

theorem arows1676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1676 = true := by
  rw [show A10K2.u1676 = KTree.node A10K2.t1680 (nat_lit 26481477) (nat_lit 6297142131) (nat_lit 0) A10K2.t1681 from rfl, allE_node, rows1680, irow1676, rows1681]
  all_goals rfl

theorem atot1676 : totK PA10K2 A10K2.u1676 = [0, 0, 353043710669, 1948336096602, 3895502495729, 2771501515133, 563679832627, 30818366867, 0, 0] := by
  rw [show A10K2.u1676 = KTree.node A10K2.t1680 (nat_lit 26481477) (nat_lit 6297142131) (nat_lit 0) A10K2.t1681 from rfl, totK_node, tot1680, tot1681]
  decide +kernel

theorem arows1677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1677 = true := by
  rw [show A10K2.u1677 = KTree.node A10K2.t1682 (nat_lit 26495148) (nat_lit 13164463702) (nat_lit 0) A10K2.t1683 from rfl, allE_node, rows1682, irow1677, rows1683]
  all_goals rfl

theorem atot1677 : totK PA10K2 A10K2.u1677 = [0, 0, 566317679127, 2980135062299, 4209831261137, 1591673727158, 117993539710, 0, 0, 0] := by
  rw [show A10K2.u1677 = KTree.node A10K2.t1682 (nat_lit 26495148) (nat_lit 13164463702) (nat_lit 0) A10K2.t1683 from rfl, totK_node, tot1682, tot1683]
  decide +kernel

theorem arows1679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1679 = true := by
  rw [show A10K2.u1679 = KTree.node A10K2.t1684 (nat_lit 26502038) (nat_lit 14756709535) (nat_lit 0) A10K2.t1685 from rfl, allE_node, rows1684, irow1679, rows1685]
  all_goals rfl

theorem atot1679 : totK PA10K2 A10K2.u1679 = [0, 0, 500094607715, 2332740212159, 3943014898169, 2554069412245, 477347224563, 13207830636, 0, 0] := by
  rw [show A10K2.u1679 = KTree.node A10K2.t1684 (nat_lit 26502038) (nat_lit 14756709535) (nat_lit 0) A10K2.t1685 from rfl, totK_node, tot1684, tot1685]
  decide +kernel

theorem arows1680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1680 = true := by
  rw [show A10K2.u1680 = KTree.node A10K2.t1686 (nat_lit 26552533) (nat_lit 6347289791) (nat_lit 0) A10K2.t1687 from rfl, allE_node, rows1686, irow1680, rows1687]
  all_goals rfl

theorem atot1680 : totK PA10K2 A10K2.u1680 = [0, 0, 763367913175, 3179440306889, 4146992918960, 1586435885085, 115261396131, 0, 0, 0] := by
  rw [show A10K2.u1680 = KTree.node A10K2.t1686 (nat_lit 26552533) (nat_lit 6347289791) (nat_lit 0) A10K2.t1687 from rfl, totK_node, tot1686, tot1687]
  decide +kernel

theorem arows1683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1683 = true := by
  rw [show A10K2.u1683 = KTree.node A10K2.t1688 (nat_lit 26557887) (nat_lit 14297916367) (nat_lit 0) A10K2.t1689 from rfl, allE_node, rows1688, irow1683, rows1689]
  all_goals rfl

theorem atot1683 : totK PA10K2 A10K2.u1683 = [0, 0, 481676879802, 2228569429062, 3786294045360, 2430484367049, 486374356215, 31452573850, 0, 0] := by
  rw [show A10K2.u1683 = KTree.node A10K2.t1688 (nat_lit 26557887) (nat_lit 14297916367) (nat_lit 0) A10K2.t1689 from rfl, totK_node, tot1688, tot1689]
  decide +kernel

theorem arows1684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1684 = true := by
  rw [show A10K2.u1684 = KTree.node A10K2.t1690 (nat_lit 26563874) (nat_lit 13563626043) (nat_lit 0) A10K2.t1691 from rfl, allE_node, rows1690, irow1684, rows1691]
  all_goals rfl

theorem atot1684 : totK PA10K2 A10K2.u1684 = [0, 0, 564907429615, 2677269024219, 3988519541847, 1978272579637, 280492110081, 6354482628, 0, 0] := by
  rw [show A10K2.u1684 = KTree.node A10K2.t1690 (nat_lit 26563874) (nat_lit 13563626043) (nat_lit 0) A10K2.t1691 from rfl, totK_node, tot1690, tot1691]
  decide +kernel

theorem arows1686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1686 = true := by
  rw [show A10K2.u1686 = KTree.node A10K2.t1692 (nat_lit 26608398) (nat_lit 10072722472) (nat_lit 0) A10K2.t1693 from rfl, allE_node, rows1692, irow1686, rows1693]
  all_goals rfl

theorem atot1686 : totK PA10K2 A10K2.u1686 = [0, 0, 745695674583, 3200166940255, 4108453261924, 1464969808278, 97957461949, 0, 0, 0] := by
  rw [show A10K2.u1686 = KTree.node A10K2.t1692 (nat_lit 26608398) (nat_lit 10072722472) (nat_lit 0) A10K2.t1693 from rfl, totK_node, tot1692, tot1693]
  decide +kernel

theorem arows1687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1687 = true := by
  rw [show A10K2.u1687 = KTree.node A10K2.t1694 (nat_lit 26614535) (nat_lit 6823870474) (nat_lit 0) A10K2.t1695 from rfl, allE_node, rows1694, irow1687, rows1695]
  all_goals rfl

theorem atot1687 : totK PA10K2 A10K2.u1687 = [0, 0, 396445561613, 2033092993897, 3797004703239, 2508223134753, 480657983901, 30074883546, 0, 0] := by
  rw [show A10K2.u1687 = KTree.node A10K2.t1694 (nat_lit 26614535) (nat_lit 6823870474) (nat_lit 0) A10K2.t1695 from rfl, totK_node, tot1694, tot1695]
  decide +kernel

theorem arows1692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1692 = true := by
  rw [show A10K2.u1692 = KTree.node A10K2.t1696 (nat_lit 26621397) (nat_lit 5210693700) (nat_lit 0) A10K2.t1697 from rfl, allE_node, rows1696, irow1692, rows1697]
  all_goals rfl

theorem atot1692 : totK PA10K2 A10K2.u1692 = [0, 0, 400617134700, 2116611851549, 3793399663318, 2375708062678, 481619360790, 31003444686, 0, 0] := by
  rw [show A10K2.u1692 = KTree.node A10K2.t1696 (nat_lit 26621397) (nat_lit 5210693700) (nat_lit 0) A10K2.t1697 from rfl, totK_node, tot1696, tot1697]
  decide +kernel

theorem arows1693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1693 = true := by
  rw [show A10K2.u1693 = KTree.node A10K2.t1698 (nat_lit 26625861) (nat_lit 6315799339) (nat_lit 0) A10K2.t1699 from rfl, allE_node, rows1698, irow1693, rows1699]
  all_goals rfl

theorem atot1693 : totK PA10K2 A10K2.u1693 = [0, 0, 739978143357, 3269789763943, 4011117170189, 1291752305118, 91045417662, 0, 0, 0] := by
  rw [show A10K2.u1693 = KTree.node A10K2.t1698 (nat_lit 26625861) (nat_lit 6315799339) (nat_lit 0) A10K2.t1699 from rfl, totK_node, tot1698, tot1699]
  decide +kernel

theorem arows1695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1695 = true := by
  rw [show A10K2.u1695 = KTree.node A10K2.t1700 (nat_lit 26640711) (nat_lit 6030356493) (nat_lit 0) A10K2.t1701 from rfl, allE_node, rows1700, irow1695, rows1701]
  all_goals rfl

theorem atot1695 : totK PA10K2 A10K2.u1695 = [0, 0, 0, 1137950171751, 3914525773904, 3414775647011, 750796897820, 37547833973, 0, 0] := by
  rw [show A10K2.u1695 = KTree.node A10K2.t1700 (nat_lit 26640711) (nat_lit 6030356493) (nat_lit 0) A10K2.t1701 from rfl, totK_node, tot1700, tot1701]
  decide +kernel

theorem arows1696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1696 = true := by
  rw [show A10K2.u1696 = KTree.node A10K2.t1702 (nat_lit 26651141) (nat_lit 6791634080) (nat_lit 0) A10K2.t1703 from rfl, allE_node, rows1702, irow1696, rows1703]
  all_goals rfl

theorem atot1696 : totK PA10K2 A10K2.u1696 = [0, 0, 0, 1132838237042, 3798811787960, 3380108549264, 822830787056, 56346053544, 0, 0] := by
  rw [show A10K2.u1696 = KTree.node A10K2.t1702 (nat_lit 26651141) (nat_lit 6791634080) (nat_lit 0) A10K2.t1703 from rfl, totK_node, tot1702, tot1703]
  decide +kernel

theorem arows1699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1699 = true := by
  rw [show A10K2.u1699 = KTree.node A10K2.t1704 (nat_lit 26659692) (nat_lit 12608148872) (nat_lit 0) A10K2.t1705 from rfl, allE_node, rows1704, irow1699, rows1705]
  all_goals rfl

theorem atot1699 : totK PA10K2 A10K2.u1699 = [0, 0, 0, 459857692214, 2576736189945, 4023165932556, 1814683378559, 199528122827, 0, 0] := by
  rw [show A10K2.u1699 = KTree.node A10K2.t1704 (nat_lit 26659692) (nat_lit 12608148872) (nat_lit 0) A10K2.t1705 from rfl, totK_node, tot1704, tot1705]
  decide +kernel

theorem arows1700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1700 = true := by
  rw [show A10K2.u1700 = KTree.node A10K2.t1706 (nat_lit 27265544) (nat_lit 14167382902) (nat_lit 0) A10K2.t1707 from rfl, allE_node, rows1706, irow1700, rows1707]
  all_goals rfl

theorem atot1700 : totK PA10K2 A10K2.u1700 = [0, 0, 857716201818, 3345667639104, 3922296876098, 1320540930241, 187590335682, 91540553519, 6354482628, 0] := by
  rw [show A10K2.u1700 = KTree.node A10K2.t1706 (nat_lit 27265544) (nat_lit 14167382902) (nat_lit 0) A10K2.t1707 from rfl, totK_node, tot1706, tot1707]
  decide +kernel

theorem arows1702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1702 = true := by
  rw [show A10K2.u1702 = KTree.node A10K2.t1708 (nat_lit 27270259) (nat_lit 5511017593) (nat_lit 0) A10K2.t1709 from rfl, allE_node, rows1708, irow1702, rows1709]
  all_goals rfl

theorem atot1702 : totK PA10K2 A10K2.u1702 = [0, 0, 453345477736, 2158272863205, 3733815096214, 2585508387077, 551869839786, 30831673886, 0, 0] := by
  rw [show A10K2.u1702 = KTree.node A10K2.t1708 (nat_lit 27270259) (nat_lit 5511017593) (nat_lit 0) A10K2.t1709 from rfl, totK_node, tot1708, tot1709]
  decide +kernel

theorem arows1703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1703 = true := by
  rw [show A10K2.u1703 = KTree.node A10K2.t1710 (nat_lit 27283916) (nat_lit 7250006325) (nat_lit 0) A10K2.t1711 from rfl, allE_node, rows1710, irow1703, rows1711]
  all_goals rfl

theorem atot1703 : totK PA10K2 A10K2.u1703 = [0, 0, 583383242649, 2553073880981, 3882404559333, 2011263713562, 254388343096, 6354482628, 0, 0] := by
  rw [show A10K2.u1703 = KTree.node A10K2.t1710 (nat_lit 27283916) (nat_lit 7250006325) (nat_lit 0) A10K2.t1711 from rfl, totK_node, tot1710, tot1711]
  decide +kernel

theorem arows1707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1707 = true := by
  rw [show A10K2.u1707 = KTree.node A10K2.t1712 (nat_lit 27291534) (nat_lit 15075358843) (nat_lit 0) A10K2.t1713 from rfl, allE_node, rows1712, irow1707, rows1713]
  all_goals rfl

theorem atot1707 : totK PA10K2 A10K2.u1707 = [0, 0, 395296435550, 2492204043948, 4498689421291, 2620916089334, 362372307782, 6853348008, 0, 0] := by
  rw [show A10K2.u1707 = KTree.node A10K2.t1712 (nat_lit 27291534) (nat_lit 15075358843) (nat_lit 0) A10K2.t1713 from rfl, totK_node, tot1712, tot1713]
  decide +kernel

theorem arows1708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1708 = true := by
  rw [show A10K2.u1708 = KTree.node A10K2.t1714 (nat_lit 27296698) (nat_lit 10591280580) (nat_lit 0) A10K2.t1715 from rfl, allE_node, rows1714, irow1708, rows1715]
  all_goals rfl

theorem atot1708 : totK PA10K2 A10K2.u1708 = [0, 0, 0, 932838211237, 3658454256198, 4004135297155, 1095707468219, 67132091768, 0, 0] := by
  rw [show A10K2.u1708 = KTree.node A10K2.t1714 (nat_lit 27296698) (nat_lit 10591280580) (nat_lit 0) A10K2.t1715 from rfl, totK_node, tot1714, tot1715]
  decide +kernel

theorem arows1710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1710 = true := by
  rw [show A10K2.u1710 = KTree.node A10K2.t1716 (nat_lit 27302444) (nat_lit 11861552121) (nat_lit 0) A10K2.t1717 from rfl, allE_node, rows1716, irow1710, rows1717]
  all_goals rfl

theorem atot1710 : totK PA10K2 A10K2.u1710 = [0, 0, 0, 318493191224, 1904321367073, 3917053134502, 2676533219492, 568222152873, 30650496230, 0] := by
  rw [show A10K2.u1710 = KTree.node A10K2.t1716 (nat_lit 27302444) (nat_lit 11861552121) (nat_lit 0) A10K2.t1717 from rfl, totK_node, tot1716, tot1717]
  decide +kernel

theorem arows1711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1711 = true := by
  rw [show A10K2.u1711 = KTree.node A10K2.t1718 (nat_lit 27316486) (nat_lit 10581840730) (nat_lit 0) A10K2.t1719 from rfl, allE_node, rows1718, irow1711, rows1719]
  all_goals rfl

theorem atot1711 : totK PA10K2 A10K2.u1711 = [0, 0, 0, 603180874267, 2773531915501, 3876326557811, 1646898991098, 204889202862, 5546304973, 0] := by
  rw [show A10K2.u1711 = KTree.node A10K2.t1718 (nat_lit 27316486) (nat_lit 10581840730) (nat_lit 0) A10K2.t1719 from rfl, totK_node, tot1718, tot1719]
  decide +kernel

theorem arows1714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1714 = true := by
  rw [show A10K2.u1714 = KTree.node A10K2.t1720 (nat_lit 27324316) (nat_lit 1498513594) (nat_lit 8) A10K2.t1721 from rfl, allE_node, rows1720, irow1714, rows1721]
  all_goals rfl

theorem atot1714 : totK PA10K2 A10K2.u1714 = [0, 0, 582971723811, 2350954568863, 3681194808159, 2740057182424, 690903511534, 49886838448, 0, 0] := by
  rw [show A10K2.u1714 = KTree.node A10K2.t1720 (nat_lit 27324316) (nat_lit 1498513594) (nat_lit 8) A10K2.t1721 from rfl, totK_node, tot1720, tot1721]
  decide +kernel

theorem arows1715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1715 = true := by
  rw [show A10K2.u1715 = KTree.node A10K2.t1722 (nat_lit 27398665) (nat_lit 9781991067) (nat_lit 0) A10K2.t1723 from rfl, allE_node, rows1722, irow1715, rows1723]
  all_goals rfl

theorem atot1715 : totK PA10K2 A10K2.u1715 = [0, 0, 253739115530, 1884681964673, 4136161228128, 2895951297663, 573940204506, 30831673886, 0, 0] := by
  rw [show A10K2.u1715 = KTree.node A10K2.t1722 (nat_lit 27398665) (nat_lit 9781991067) (nat_lit 0) A10K2.t1723 from rfl, totK_node, tot1722, tot1723]
  decide +kernel

theorem arows1717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1717 = true := by
  rw [show A10K2.u1717 = KTree.node A10K2.t1724 (nat_lit 27407584) (nat_lit 6131944339) (nat_lit 0) A10K2.t1725 from rfl, allE_node, rows1724, irow1717, rows1725]
  all_goals rfl

theorem atot1717 : totK PA10K2 A10K2.u1717 = [0, 0, 637372899366, 2659300739252, 3692223172963, 1972739297992, 327875915072, 11427838733, 0, 0] := by
  rw [show A10K2.u1717 = KTree.node A10K2.t1724 (nat_lit 27407584) (nat_lit 6131944339) (nat_lit 0) A10K2.t1725 from rfl, totK_node, tot1724, tot1725]
  decide +kernel

theorem arows1718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1718 = true := by
  rw [show A10K2.u1718 = KTree.node A10K2.t1726 (nat_lit 27412576) (nat_lit 13543058683) (nat_lit 0) A10K2.t1727 from rfl, allE_node, rows1726, irow1718, rows1727]
  all_goals rfl

theorem atot1718 : totK PA10K2 A10K2.u1718 = [0, 0, 617022559529, 2983360717050, 4063712224760, 1502036821031, 113202265745, 0, 0, 0] := by
  rw [show A10K2.u1718 = KTree.node A10K2.t1726 (nat_lit 27412576) (nat_lit 13543058683) (nat_lit 0) A10K2.t1727 from rfl, totK_node, tot1726, tot1727]
  decide +kernel

theorem arows1724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1724 = true := by
  rw [show A10K2.u1724 = KTree.node A10K2.t1728 (nat_lit 27427379) (nat_lit 3282019674) (nat_lit 0) A10K2.t1729 from rfl, allE_node, rows1728, irow1724, rows1729]
  all_goals rfl

theorem atot1724 : totK PA10K2 A10K2.u1724 = [0, 0, 0, 1115441995208, 3888215163527, 3672987457014, 817030514777, 38342359577, 0, 0] := by
  rw [show A10K2.u1724 = KTree.node A10K2.t1728 (nat_lit 27427379) (nat_lit 3282019674) (nat_lit 0) A10K2.t1729 from rfl, totK_node, tot1728, tot1729]
  decide +kernel

theorem arows1725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1725 = true := by
  rw [show A10K2.u1725 = KTree.node A10K2.t1730 (nat_lit 27437864) (nat_lit 11043069918) (nat_lit 0) A10K2.t1731 from rfl, allE_node, rows1730, irow1725, rows1731]
  all_goals rfl

theorem atot1725 : totK PA10K2 A10K2.u1725 = [0, 0, 0, 1010353925099, 3729010192325, 3692813611978, 860640335034, 43410539713, 0, 0] := by
  rw [show A10K2.u1725 = KTree.node A10K2.t1730 (nat_lit 27437864) (nat_lit 11043069918) (nat_lit 0) A10K2.t1731 from rfl, totK_node, tot1730, tot1731]
  decide +kernel

theorem arows1727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1727 = true := by
  rw [show A10K2.u1727 = KTree.node A10K2.t1732 (nat_lit 27448584) (nat_lit 11113279850) (nat_lit 0) A10K2.t1733 from rfl, allE_node, rows1732, irow1727, rows1733]
  all_goals rfl

theorem atot1727 : totK PA10K2 A10K2.u1727 = [0, 0, 310152219116, 1168466612490, 2484489662780, 3452840623714, 1646730100688, 221145934464, 6354482628, 0] := by
  rw [show A10K2.u1727 = KTree.node A10K2.t1732 (nat_lit 27448584) (nat_lit 11113279850) (nat_lit 0) A10K2.t1733 from rfl, totK_node, tot1732, tot1733]
  decide +kernel

theorem arows1728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1728 = true := by
  rw [show A10K2.u1728 = KTree.node A10K2.t1734 (nat_lit 27463224) (nat_lit 14764516676) (nat_lit 0) A10K2.t1735 from rfl, allE_node, rows1734, irow1728, rows1735]
  all_goals rfl

theorem atot1728 : totK PA10K2 A10K2.u1728 = [0, 0, 498328713856, 2563096081937, 4126332673095, 2279943889534, 426887380901, 25351274858, 0, 0] := by
  rw [show A10K2.u1728 = KTree.node A10K2.t1734 (nat_lit 27463224) (nat_lit 14764516676) (nat_lit 0) A10K2.t1735 from rfl, totK_node, tot1734, tot1735]
  decide +kernel

theorem arows1731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1731 = true := by
  rw [show A10K2.u1731 = KTree.node A10K2.t1736 (nat_lit 27484961) (nat_lit 9804255196) (nat_lit 0) A10K2.t1737 from rfl, allE_node, rows1736, irow1731, rows1737]
  all_goals rfl

theorem atot1731 : totK PA10K2 A10K2.u1731 = [0, 0, 797258379978, 3165374050927, 4157595940202, 1822927632254, 222022982410, 5459593153, 0, 0] := by
  rw [show A10K2.u1731 = KTree.node A10K2.t1736 (nat_lit 27484961) (nat_lit 9804255196) (nat_lit 0) A10K2.t1737 from rfl, totK_node, tot1736, tot1737]
  decide +kernel

theorem arows1732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1732 = true := by
  rw [show A10K2.u1732 = KTree.node A10K2.t1738 (nat_lit 27491505) (nat_lit 6696784008) (nat_lit 0) A10K2.t1739 from rfl, allE_node, rows1738, irow1732, rows1739]
  all_goals rfl

theorem atot1732 : totK PA10K2 A10K2.u1732 = [0, 0, 0, 1183981915099, 4029803614427, 3856915561564, 992728772882, 56690162165, 0, 0] := by
  rw [show A10K2.u1732 = KTree.node A10K2.t1738 (nat_lit 27491505) (nat_lit 6696784008) (nat_lit 0) A10K2.t1739 from rfl, totK_node, tot1738, tot1739]
  decide +kernel

theorem arows1734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1734 = true := by
  rw [show A10K2.u1734 = KTree.node A10K2.t1740 (nat_lit 27496448) (nat_lit 15792662511) (nat_lit 0) A10K2.t1741 from rfl, allE_node, rows1740, irow1734, rows1741]
  all_goals rfl

theorem atot1734 : totK PA10K2 A10K2.u1734 = [0, 0, 0, 521849042724, 2690798765912, 4252981973446, 2120248603976, 301056369239, 6904928264, 0] := by
  rw [show A10K2.u1734 = KTree.node A10K2.t1740 (nat_lit 27496448) (nat_lit 15792662511) (nat_lit 0) A10K2.t1741 from rfl, totK_node, tot1740, tot1741]
  decide +kernel

theorem arows1735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1735 = true := by
  rw [show A10K2.u1735 = KTree.node A10K2.t1742 (nat_lit 27520505) (nat_lit 6315597177) (nat_lit 0) A10K2.t1743 from rfl, allE_node, rows1742, irow1735, rows1743]
  all_goals rfl

theorem atot1735 : totK PA10K2 A10K2.u1735 = [0, 0, 414502387968, 2122199344664, 3981955936924, 2901787928753, 676722967157, 42318184600, 0, 0] := by
  rw [show A10K2.u1735 = KTree.node A10K2.t1742 (nat_lit 27520505) (nat_lit 6315597177) (nat_lit 0) A10K2.t1743 from rfl, totK_node, tot1742, tot1743]
  decide +kernel

theorem arows1739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1739 = true := by
  rw [show A10K2.u1739 = KTree.node A10K2.t1744 (nat_lit 27866268) (nat_lit 11506034995) (nat_lit 0) A10K2.t1745 from rfl, allE_node, rows1744, irow1739, rows1745]
  all_goals rfl

theorem atot1739 : totK PA10K2 A10K2.u1739 = [0, 0, 428788673627, 2301660147865, 4005161225205, 2473370248141, 464914252163, 25734533292, 0, 0] := by
  rw [show A10K2.u1739 = KTree.node A10K2.t1744 (nat_lit 27866268) (nat_lit 11506034995) (nat_lit 0) A10K2.t1745 from rfl, totK_node, tot1744, tot1745]
  decide +kernel

theorem arows1740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1740 = true := by
  rw [show A10K2.u1740 = KTree.node A10K2.t1746 (nat_lit 27870675) (nat_lit 10634980942) (nat_lit 0) A10K2.t1747 from rfl, allE_node, rows1746, irow1740, rows1747]
  all_goals rfl

theorem atot1740 : totK PA10K2 A10K2.u1740 = [0, 0, 745125641004, 3132980333293, 3911243919972, 1540016964906, 192686541116, 6034215561, 0, 0] := by
  rw [show A10K2.u1740 = KTree.node A10K2.t1746 (nat_lit 27870675) (nat_lit 10634980942) (nat_lit 0) A10K2.t1747 from rfl, totK_node, tot1746, tot1747]
  decide +kernel

theorem arows1742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1742 = true := by
  rw [show A10K2.u1742 = KTree.node A10K2.t1748 (nat_lit 27878693) (nat_lit 7193019099) (nat_lit 0) A10K2.t1749 from rfl, allE_node, rows1748, irow1742, rows1749]
  all_goals rfl

theorem atot1742 : totK PA10K2 A10K2.u1742 = [0, 0, 595393228060, 2767484243744, 4197830199306, 2041887193707, 246012311497, 6354482628, 0, 0] := by
  rw [show A10K2.u1742 = KTree.node A10K2.t1748 (nat_lit 27878693) (nat_lit 7193019099) (nat_lit 0) A10K2.t1749 from rfl, totK_node, tot1748, tot1749]
  decide +kernel

theorem arows1743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1743 = true := by
  rw [show A10K2.u1743 = KTree.node A10K2.t1750 (nat_lit 27885274) (nat_lit 12559911410) (nat_lit 0) A10K2.t1751 from rfl, allE_node, rows1750, irow1743, rows1751]
  all_goals rfl

theorem atot1743 : totK PA10K2 A10K2.u1743 = [0, 0, 557584295228, 2410762323906, 3843670749553, 2608394403285, 507075225137, 12926121504, 0, 0] := by
  rw [show A10K2.u1743 = KTree.node A10K2.t1750 (nat_lit 27885274) (nat_lit 12559911410) (nat_lit 0) A10K2.t1751 from rfl, totK_node, tot1750, tot1751]
  decide +kernel

theorem arows1746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1746 = true := by
  rw [show A10K2.u1746 = KTree.node A10K2.t1752 (nat_lit 27925027) (nat_lit 6509597216) (nat_lit 0) A10K2.t1753 from rfl, allE_node, rows1752, irow1746, rows1753]
  all_goals rfl

theorem atot1746 : totK PA10K2 A10K2.u1746 = [0, 0, 504418265648, 2340853439861, 3938783606459, 2310396429679, 350552092689, 10760911071, 0, 0] := by
  rw [show A10K2.u1746 = KTree.node A10K2.t1752 (nat_lit 27925027) (nat_lit 6509597216) (nat_lit 0) A10K2.t1753 from rfl, totK_node, tot1752, tot1753]
  decide +kernel

theorem arows1747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1747 = true := by
  rw [show A10K2.u1747 = KTree.node A10K2.t1754 (nat_lit 27932110) (nat_lit 5717270565) (nat_lit 128) A10K2.t1755 from rfl, allE_node, rows1754, irow1747, rows1755]
  all_goals rfl

theorem atot1747 : totK PA10K2 A10K2.u1747 = [0, 0, 265509610688, 1982851627097, 4107622076357, 2803975802464, 518698472431, 31768748853, 0, 0] := by
  rw [show A10K2.u1747 = KTree.node A10K2.t1754 (nat_lit 27932110) (nat_lit 5717270565) (nat_lit 128) A10K2.t1755 from rfl, totK_node, tot1754, tot1755]
  decide +kernel

theorem arows1749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1749 = true := by
  rw [show A10K2.u1749 = KTree.node A10K2.t1756 (nat_lit 27936544) (nat_lit 10850459610) (nat_lit 0) A10K2.t1757 from rfl, allE_node, rows1756, irow1749, rows1757]
  all_goals rfl

theorem atot1749 : totK PA10K2 A10K2.u1749 = [0, 0, 815995094934, 3307428934082, 3878118282312, 1304590708357, 91712056203, 0, 0, 0] := by
  rw [show A10K2.u1749 = KTree.node A10K2.t1756 (nat_lit 27936544) (nat_lit 10850459610) (nat_lit 0) A10K2.t1757 from rfl, totK_node, tot1756, tot1757]
  decide +kernel

theorem arows1750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1750 = true := by
  rw [show A10K2.u1750 = KTree.node A10K2.t1758 (nat_lit 27951431) (nat_lit 5934422843) (nat_lit 0) A10K2.t1759 from rfl, allE_node, rows1758, irow1750, rows1759]
  all_goals rfl

theorem atot1750 : totK PA10K2 A10K2.u1750 = [0, 0, 0, 1138608489662, 3974637120436, 3559421182774, 721261962331, 23367618958, 0, 0] := by
  rw [show A10K2.u1750 = KTree.node A10K2.t1758 (nat_lit 27951431) (nat_lit 5934422843) (nat_lit 0) A10K2.t1759 from rfl, totK_node, tot1758, tot1759]
  decide +kernel

theorem arows1755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1755 = true := by
  rw [show A10K2.u1755 = KTree.node A10K2.t1760 (nat_lit 27962518) (nat_lit 15201631928) (nat_lit 0) A10K2.t1761 from rfl, allE_node, rows1760, irow1755, rows1761]
  all_goals rfl

theorem atot1755 : totK PA10K2 A10K2.u1755 = [0, 0, 0, 1161852761498, 3894090506373, 3621198208148, 768378163831, 43203736937, 0, 0] := by
  rw [show A10K2.u1755 = KTree.node A10K2.t1760 (nat_lit 27962518) (nat_lit 15201631928) (nat_lit 0) A10K2.t1761 from rfl, totK_node, tot1760, tot1761]
  decide +kernel

theorem arows1756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1756 = true := by
  rw [show A10K2.u1756 = KTree.node A10K2.t1762 (nat_lit 27971939) (nat_lit 8473371772) (nat_lit 0) A10K2.t1763 from rfl, allE_node, rows1762, irow1756, rows1763]
  all_goals rfl

theorem atot1756 : totK PA10K2 A10K2.u1756 = [0, 0, 213371739588, 725696074251, 2323548665178, 3821539359268, 1851170310312, 255457917856, 6354482628, 0] := by
  rw [show A10K2.u1756 = KTree.node A10K2.t1762 (nat_lit 27971939) (nat_lit 8473371772) (nat_lit 0) A10K2.t1763 from rfl, totK_node, tot1762, tot1763]
  decide +kernel

theorem arows1758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1758 = true := by
  rw [show A10K2.u1758 = KTree.node A10K2.t1764 (nat_lit 28314661) (nat_lit 6724379814) (nat_lit 0) A10K2.t1765 from rfl, allE_node, rows1764, irow1758, rows1765]
  all_goals rfl

theorem atot1758 : totK PA10K2 A10K2.u1758 = [0, 0, 597963004255, 2829349837424, 3980144231453, 1852546182481, 293760841686, 20070762815, 0, 0] := by
  rw [show A10K2.u1758 = KTree.node A10K2.t1764 (nat_lit 28314661) (nat_lit 6724379814) (nat_lit 0) A10K2.t1765 from rfl, totK_node, tot1764, tot1765]
  decide +kernel

theorem arows1759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1759 = true := by
  rw [show A10K2.u1759 = KTree.node A10K2.t1766 (nat_lit 28328224) (nat_lit 13375405213) (nat_lit 0) A10K2.t1767 from rfl, allE_node, rows1766, irow1759, rows1767]
  all_goals rfl

theorem atot1759 : totK PA10K2 A10K2.u1759 = [0, 0, 626404082296, 2578261678017, 3775870587148, 2120669747738, 351588507275, 10760911071, 0, 0] := by
  rw [show A10K2.u1759 = KTree.node A10K2.t1766 (nat_lit 28328224) (nat_lit 13375405213) (nat_lit 0) A10K2.t1767 from rfl, totK_node, tot1766, tot1767]
  decide +kernel

theorem arows1762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1762 = true := by
  rw [show A10K2.u1762 = KTree.node A10K2.t1768 (nat_lit 28334144) (nat_lit 14686140639) (nat_lit 0) A10K2.t1769 from rfl, allE_node, rows1768, irow1762, rows1769]
  all_goals rfl

theorem atot1762 : totK PA10K2 A10K2.u1762 = [0, 0, 419789149873, 2493300775592, 4153386325321, 2153933494333, 301105607360, 6354482628, 0, 0] := by
  rw [show A10K2.u1762 = KTree.node A10K2.t1768 (nat_lit 28334144) (nat_lit 14686140639) (nat_lit 0) A10K2.t1769 from rfl, totK_node, tot1768, tot1769]
  decide +kernel

theorem arows1763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1763 = true := by
  rw [show A10K2.u1763 = KTree.node A10K2.t1770 (nat_lit 28343364) (nat_lit 9153486125) (nat_lit 0) A10K2.t1771 from rfl, allE_node, rows1770, irow1763, rows1771]
  all_goals rfl

theorem atot1763 : totK PA10K2 A10K2.u1763 = [0, 0, 217158502480, 1766453050689, 4044593442808, 3242114245651, 735783553989, 38413255743, 0, 0] := by
  rw [show A10K2.u1763 = KTree.node A10K2.t1770 (nat_lit 28343364) (nat_lit 9153486125) (nat_lit 0) A10K2.t1771 from rfl, totK_node, tot1770, tot1771]
  decide +kernel

theorem arows1765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1765 = true := by
  rw [show A10K2.u1765 = KTree.node A10K2.t1772 (nat_lit 28348679) (nat_lit 10302674661) (nat_lit 0) A10K2.t1773 from rfl, allE_node, rows1772, irow1765, rows1773]
  all_goals rfl

theorem atot1765 : totK PA10K2 A10K2.u1765 = [0, 0, 0, 394487094067, 2290174143240, 3917651114308, 2204521902057, 447988493724, 30220878370, 0] := by
  rw [show A10K2.u1765 = KTree.node A10K2.t1772 (nat_lit 28348679) (nat_lit 10302674661) (nat_lit 0) A10K2.t1773 from rfl, totK_node, tot1772, tot1773]
  decide +kernel

theorem arows1766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1766 = true := by
  rw [show A10K2.u1766 = KTree.node A10K2.t1774 (nat_lit 28362578) (nat_lit 13933218566) (nat_lit 0) A10K2.t1775 from rfl, allE_node, rows1774, irow1766, rows1775]
  all_goals rfl

theorem atot1766 : totK PA10K2 A10K2.u1766 = [0, 0, 0, 773104585618, 3393294733897, 4050566181986, 1155040091278, 70802926979, 0, 0] := by
  rw [show A10K2.u1766 = KTree.node A10K2.t1774 (nat_lit 28362578) (nat_lit 13933218566) (nat_lit 0) A10K2.t1775 from rfl, totK_node, tot1774, tot1775]
  decide +kernel

theorem arows1770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1770 = true := by
  rw [show A10K2.u1770 = KTree.node A10K2.t1776 (nat_lit 28369700) (nat_lit 13284814556) (nat_lit 0) A10K2.t1777 from rfl, allE_node, rows1776, irow1770, rows1777]
  all_goals rfl

theorem atot1770 : totK PA10K2 A10K2.u1770 = [0, 0, 304031809754, 1521826155184, 3165939268849, 3231911259044, 1327605556635, 181143690987, 5546304973, 0] := by
  rw [show A10K2.u1770 = KTree.node A10K2.t1776 (nat_lit 28369700) (nat_lit 13284814556) (nat_lit 0) A10K2.t1777 from rfl, totK_node, tot1776, tot1777]
  decide +kernel

theorem arows1771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1771 = true := by
  rw [show A10K2.u1771 = KTree.node A10K2.t1778 (nat_lit 28390558) (nat_lit 14766344110) (nat_lit 0) A10K2.t1779 from rfl, allE_node, rows1778, irow1771, rows1779]
  all_goals rfl

theorem atot1771 : totK PA10K2 A10K2.u1771 = [0, 0, 459942519120, 2342828684200, 3998275283070, 2435055912417, 408004987477, 25734533292, 0, 0] := by
  rw [show A10K2.u1771 = KTree.node A10K2.t1778 (nat_lit 28390558) (nat_lit 14766344110) (nat_lit 0) A10K2.t1779 from rfl, totK_node, tot1778, tot1779]
  decide +kernel

theorem arows1773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1773 = true := by
  rw [show A10K2.u1773 = KTree.node A10K2.t1780 (nat_lit 28394994) (nat_lit 14259941014) (nat_lit 0) A10K2.t1781 from rfl, allE_node, rows1780, irow1773, rows1781]
  all_goals rfl

theorem atot1773 : totK PA10K2 A10K2.u1773 = [0, 0, 779179629239, 3207077735325, 3898382675745, 1558716052993, 201185428891, 6034215561, 0, 0] := by
  rw [show A10K2.u1773 = KTree.node A10K2.t1780 (nat_lit 28394994) (nat_lit 14259941014) (nat_lit 0) A10K2.t1781 from rfl, totK_node, tot1780, tot1781]
  decide +kernel

theorem arows1774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1774 = true := by
  rw [show A10K2.u1774 = KTree.node A10K2.t1782 (nat_lit 28402914) (nat_lit 14279361898) (nat_lit 0) A10K2.t1783 from rfl, allE_node, rows1782, irow1774, rows1783]
  all_goals rfl

theorem atot1774 : totK PA10K2 A10K2.u1774 = [0, 0, 268061909688, 1877029449269, 4047894507745, 2866557979895, 525901552406, 26944025047, 0, 0] := by
  rw [show A10K2.u1774 = KTree.node A10K2.t1782 (nat_lit 28402914) (nat_lit 14279361898) (nat_lit 0) A10K2.t1783 from rfl, totK_node, tot1782, tot1783]
  decide +kernel

theorem arows1777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1777 = true := by
  rw [show A10K2.u1777 = KTree.node A10K2.t1784 (nat_lit 28426785) (nat_lit 10101071044) (nat_lit 0) A10K2.t1785 from rfl, allE_node, rows1784, irow1777, rows1785]
  all_goals rfl

theorem atot1777 : totK PA10K2 A10K2.u1777 = [0, 0, 0, 1229535129055, 4047872805943, 3510884802547, 754071367494, 43870098033, 0, 0] := by
  rw [show A10K2.u1777 = KTree.node A10K2.t1784 (nat_lit 28426785) (nat_lit 10101071044) (nat_lit 0) A10K2.t1785 from rfl, totK_node, tot1784, tot1785]
  decide +kernel

theorem arows1778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1778 = true := by
  rw [show A10K2.u1778 = KTree.node A10K2.t1786 (nat_lit 28432901) (nat_lit 6480272069) (nat_lit 0) A10K2.t1787 from rfl, allE_node, rows1786, irow1778, rows1787]
  all_goals rfl

theorem atot1778 : totK PA10K2 A10K2.u1778 = [0, 0, 290234937362, 1246308563201, 2680319891673, 3393263914088, 1570266287291, 212595162053, 6121173289, 0] := by
  rw [show A10K2.u1778 = KTree.node A10K2.t1786 (nat_lit 28432901) (nat_lit 6480272069) (nat_lit 0) A10K2.t1787 from rfl, totK_node, tot1786, tot1787]
  decide +kernel

theorem arows1780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1780 = true := by
  rw [show A10K2.u1780 = KTree.node A10K2.t1788 (nat_lit 28446757) (nat_lit 6984222168) (nat_lit 0) A10K2.t1789 from rfl, allE_node, rows1788, irow1780, rows1789]
  all_goals rfl

theorem atot1780 : totK PA10K2 A10K2.u1780 = [0, 0, 452388186593, 2293335183366, 3904090081523, 2365786030023, 416922764161, 25371180993, 0, 0] := by
  rw [show A10K2.u1780 = KTree.node A10K2.t1788 (nat_lit 28446757) (nat_lit 6984222168) (nat_lit 0) A10K2.t1789 from rfl, totK_node, tot1788, tot1789]
  decide +kernel

theorem arows1781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1781 = true := by
  rw [show A10K2.u1781 = KTree.node A10K2.t1790 (nat_lit 28453054) (nat_lit 11854051487) (nat_lit 0) A10K2.t1791 from rfl, allE_node, rows1790, irow1781, rows1791]
  all_goals rfl

theorem atot1781 : totK PA10K2 A10K2.u1781 = [0, 0, 697537327837, 2958026731059, 3928632386541, 1731172612303, 198251242132, 5460492893, 0, 0] := by
  rw [show A10K2.u1781 = KTree.node A10K2.t1790 (nat_lit 28453054) (nat_lit 11854051487) (nat_lit 0) A10K2.t1791 from rfl, totK_node, tot1790, tot1791]
  decide +kernel

theorem arows1789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1789 = true := by
  rw [show A10K2.u1789 = KTree.node A10K2.t1792 (nat_lit 28459277) (nat_lit 5899193217) (nat_lit 0) A10K2.t1793 from rfl, allE_node, rows1792, irow1789, rows1793]
  all_goals rfl

theorem atot1789 : totK PA10K2 A10K2.u1789 = [0, 0, 549568273929, 2369455172803, 3662801362033, 2267958633523, 476694452721, 31768748853, 0, 0] := by
  rw [show A10K2.u1789 = KTree.node A10K2.t1792 (nat_lit 28459277) (nat_lit 5899193217) (nat_lit 0) A10K2.t1793 from rfl, totK_node, tot1792, tot1793]
  decide +kernel

theorem arows1790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1790 = true := by
  rw [show A10K2.u1790 = KTree.node A10K2.t1794 (nat_lit 28464392) (nat_lit 11720147088) (nat_lit 0) A10K2.t1795 from rfl, allE_node, rows1794, irow1790, rows1795]
  all_goals rfl

theorem atot1790 : totK PA10K2 A10K2.u1790 = [0, 0, 283240155107, 2249873581759, 4276980410174, 2315116294011, 309305900333, 6354482628, 0, 0] := by
  rw [show A10K2.u1790 = KTree.node A10K2.t1794 (nat_lit 28464392) (nat_lit 11720147088) (nat_lit 0) A10K2.t1795 from rfl, totK_node, tot1794, tot1795]
  decide +kernel

theorem arows1792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1792 = true := by
  rw [show A10K2.u1792 = KTree.node A10K2.t1796 (nat_lit 28478904) (nat_lit 13753460251) (nat_lit 0) A10K2.t1797 from rfl, allE_node, rows1796, irow1792, rows1797]
  all_goals rfl

theorem atot1792 : totK PA10K2 A10K2.u1792 = [0, 0, 0, 975288520995, 3592809188459, 3846157917783, 980633506648, 64468465779, 0, 0] := by
  rw [show A10K2.u1792 = KTree.node A10K2.t1796 (nat_lit 28478904) (nat_lit 13753460251) (nat_lit 0) A10K2.t1797 from rfl, totK_node, tot1796, tot1797]
  decide +kernel

theorem arows1793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1793 = true := by
  rw [show A10K2.u1793 = KTree.node A10K2.t1798 (nat_lit 28492676) (nat_lit 8756751404) (nat_lit 0) A10K2.t1799 from rfl, allE_node, rows1798, irow1793, rows1799]
  all_goals rfl

theorem atot1793 : totK PA10K2 A10K2.u1793 = [0, 0, 0, 1009673870921, 3767973090550, 3685679737786, 875027237240, 56621979327, 0, 0] := by
  rw [show A10K2.u1793 = KTree.node A10K2.t1798 (nat_lit 28492676) (nat_lit 8756751404) (nat_lit 0) A10K2.t1799 from rfl, totK_node, tot1798, tot1799]
  decide +kernel

theorem arows1796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1796 = true := by
  rw [show A10K2.u1796 = KTree.node A10K2.t1800 (nat_lit 28498282) (nat_lit 9742220965) (nat_lit 0) A10K2.t1801 from rfl, allE_node, rows1800, irow1796, rows1801]
  all_goals rfl

theorem atot1796 : totK PA10K2 A10K2.u1796 = [0, 0, 0, 474201755587, 2474415533816, 4108459172728, 1979785131586, 291459347602, 6354482628, 0] := by
  rw [show A10K2.u1796 = KTree.node A10K2.t1800 (nat_lit 28498282) (nat_lit 9742220965) (nat_lit 0) A10K2.t1801 from rfl, totK_node, tot1800, tot1801]
  decide +kernel

theorem arows1797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1797 = true := by
  rw [show A10K2.u1797 = KTree.node A10K2.t1802 (nat_lit 28578067) (nat_lit 4711042307) (nat_lit 0) A10K2.t1803 from rfl, allE_node, rows1802, irow1797, rows1803]
  all_goals rfl

theorem atot1797 : totK PA10K2 A10K2.u1797 = [0, 0, 0, 335646020899, 2134168616504, 3998087812239, 2397285818292, 459912132344, 30388749007, 0] := by
  rw [show A10K2.u1797 = KTree.node A10K2.t1802 (nat_lit 28578067) (nat_lit 4711042307) (nat_lit 0) A10K2.t1803 from rfl, totK_node, tot1802, tot1803]
  decide +kernel

theorem arows1799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1799 = true := by
  rw [show A10K2.u1799 = KTree.node A10K2.t1804 (nat_lit 28591902) (nat_lit 7992747596) (nat_lit 0) A10K2.t1805 from rfl, allE_node, rows1804, irow1799, rows1805]
  all_goals rfl

theorem atot1799 : totK PA10K2 A10K2.u1799 = [0, 0, 0, 771381396609, 3277343036110, 4031978373457, 1263834399554, 76590216751, 0, 0] := by
  rw [show A10K2.u1799 = KTree.node A10K2.t1804 (nat_lit 28591902) (nat_lit 7992747596) (nat_lit 0) A10K2.t1805 from rfl, totK_node, tot1804, tot1805]
  decide +kernel

theorem arows1800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1800 = true := by
  rw [show A10K2.u1800 = KTree.node A10K2.t1806 (nat_lit 28598826) (nat_lit 3457869498) (nat_lit 0) A10K2.t1807 from rfl, allE_node, rows1806, irow1800, rows1807]
  all_goals rfl

theorem atot1800 : totK PA10K2 A10K2.u1800 = [0, 0, 0, 804126417469, 3147984818579, 3888782561288, 1654078602820, 229781999042, 6354482628, 0] := by
  rw [show A10K2.u1800 = KTree.node A10K2.t1806 (nat_lit 28598826) (nat_lit 3457869498) (nat_lit 0) A10K2.t1807 from rfl, totK_node, tot1806, tot1807]
  decide +kernel

theorem arows1804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1804 = true := by
  rw [show A10K2.u1804 = KTree.node A10K2.t1808 (nat_lit 28655621) (nat_lit 6691629675) (nat_lit 0) A10K2.t1809 from rfl, allE_node, rows1808, irow1804, rows1809]
  all_goals rfl

theorem atot1804 : totK PA10K2 A10K2.u1804 = [0, 0, 0, 986318394458, 3637832610362, 3875892295981, 1037746793781, 75512977016, 0, 0] := by
  rw [show A10K2.u1804 = KTree.node A10K2.t1808 (nat_lit 28655621) (nat_lit 6691629675) (nat_lit 0) A10K2.t1809 from rfl, totK_node, tot1808, tot1809]
  decide +kernel

theorem arows1805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1805 = true := by
  rw [show A10K2.u1805 = KTree.node A10K2.t1810 (nat_lit 28661760) (nat_lit 14653781292) (nat_lit 0) A10K2.t1811 from rfl, allE_node, rows1810, irow1805, rows1811]
  all_goals rfl

theorem atot1805 : totK PA10K2 A10K2.u1805 = [0, 0, 0, 712132494003, 2904251719414, 3907079524048, 1753860649387, 248759998426, 6354482628, 0] := by
  rw [show A10K2.u1805 = KTree.node A10K2.t1810 (nat_lit 28661760) (nat_lit 14653781292) (nat_lit 0) A10K2.t1811 from rfl, totK_node, tot1810, tot1811]
  decide +kernel

theorem arows1807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1807 = true := by
  rw [show A10K2.u1807 = KTree.node A10K2.t1812 (nat_lit 28707889) (nat_lit 9866223381) (nat_lit 0) A10K2.t1813 from rfl, allE_node, rows1812, irow1807, rows1813]
  all_goals rfl

theorem atot1807 : totK PA10K2 A10K2.u1807 = [0, 0, 0, 528808321452, 2658217386990, 3895662549628, 1805778933591, 332762268406, 24614390653, 0] := by
  rw [show A10K2.u1807 = KTree.node A10K2.t1812 (nat_lit 28707889) (nat_lit 9866223381) (nat_lit 0) A10K2.t1813 from rfl, totK_node, tot1812, tot1813]
  decide +kernel

theorem arows1808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1808 = true := by
  rw [show A10K2.u1808 = KTree.node A10K2.t1814 (nat_lit 28714907) (nat_lit 9807141556) (nat_lit 0) A10K2.t1815 from rfl, allE_node, rows1814, irow1808, rows1815]
  all_goals rfl

theorem atot1808 : totK PA10K2 A10K2.u1808 = [0, 0, 0, 694224835909, 2963096232834, 3989373455208, 1584089396010, 202051498007, 5460492893, 0] := by
  rw [show A10K2.u1808 = KTree.node A10K2.t1814 (nat_lit 28714907) (nat_lit 9807141556) (nat_lit 0) A10K2.t1815 from rfl, totK_node, tot1814, tot1815]
  decide +kernel

theorem arows1811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1811 = true := by
  rw [show A10K2.u1811 = KTree.node A10K2.t1816 (nat_lit 28722002) (nat_lit 12658409085) (nat_lit 0) A10K2.t1817 from rfl, allE_node, rows1816, irow1811, rows1817]
  all_goals rfl

theorem atot1811 : totK PA10K2 A10K2.u1811 = [0, 0, 0, 836866021410, 3149038093124, 3658982337275, 1513119262011, 221486149614, 6034215561, 0] := by
  rw [show A10K2.u1811 = KTree.node A10K2.t1816 (nat_lit 28722002) (nat_lit 12658409085) (nat_lit 0) A10K2.t1817 from rfl, totK_node, tot1816, tot1817]
  decide +kernel

theorem arows1812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1812 = true := by
  rw [show A10K2.u1812 = KTree.node A10K2.t1818 (nat_lit 28727573) (nat_lit 7051909534) (nat_lit 0) A10K2.t1819 from rfl, allE_node, rows1818, irow1812, rows1819]
  all_goals rfl

theorem atot1812 : totK PA10K2 A10K2.u1812 = [0, 0, 0, 0, 1461876646383, 4248727207421, 2887425238780, 568186699180, 31193230065, 0] := by
  rw [show A10K2.u1812 = KTree.node A10K2.t1818 (nat_lit 28727573) (nat_lit 7051909534) (nat_lit 0) A10K2.t1819 from rfl, totK_node, tot1818, tot1819]
  decide +kernel

theorem arows1814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1814 = true := by
  rw [show A10K2.u1814 = KTree.node A10K2.t1820 (nat_lit 28748005) (nat_lit 7119318088) (nat_lit 0) A10K2.t1821 from rfl, allE_node, rows1820, irow1814, rows1821]
  all_goals rfl

theorem atot1814 : totK PA10K2 A10K2.u1814 = [0, 0, 0, 0, 1367872187064, 4026708270691, 3067816637542, 697865781030, 37364482810, 0] := by
  rw [show A10K2.u1814 = KTree.node A10K2.t1820 (nat_lit 28748005) (nat_lit 7119318088) (nat_lit 0) A10K2.t1821 from rfl, totK_node, tot1820, tot1821]
  decide +kernel

theorem arows1815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1815 = true := by
  rw [show A10K2.u1815 = KTree.node A10K2.t1822 (nat_lit 28758084) (nat_lit 11552108224) (nat_lit 0) A10K2.t1823 from rfl, allE_node, rows1822, irow1815, rows1823]
  all_goals rfl

theorem atot1815 : totK PA10K2 A10K2.u1815 = [0, 157526836586, 329480614415, 188003870903, 473514605611, 2575821110018, 3666996688497, 1580256783827, 201285822945, 6354482628] := by
  rw [show A10K2.u1815 = KTree.node A10K2.t1822 (nat_lit 28758084) (nat_lit 11552108224) (nat_lit 0) A10K2.t1823 from rfl, totK_node, tot1822, tot1823]
  decide +kernel

theorem arows1820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1820 = true := by
  rw [show A10K2.u1820 = KTree.node A10K2.t1824 (nat_lit 29363209) (nat_lit 9732766126) (nat_lit 0) A10K2.t1825 from rfl, allE_node, rows1824, irow1820, rows1825]
  all_goals rfl

theorem atot1820 : totK PA10K2 A10K2.u1820 = [0, 701854271825, 3116427778232, 4148753108043, 1675682201648, 146351268385, 0, 0, 0, 0] := by
  rw [show A10K2.u1820 = KTree.node A10K2.t1824 (nat_lit 29363209) (nat_lit 9732766126) (nat_lit 0) A10K2.t1825 from rfl, totK_node, tot1824, tot1825]
  decide +kernel

theorem arows1821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1821 = true := by
  rw [show A10K2.u1821 = KTree.node A10K2.t1826 (nat_lit 29367794) (nat_lit 13055503498) (nat_lit 0) A10K2.t1827 from rfl, allE_node, rows1826, irow1821, rows1827]
  all_goals rfl

theorem atot1821 : totK PA10K2 A10K2.u1821 = [0, 573073781472, 2377728360690, 3667467353054, 2343511562470, 522032986239, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1821 = KTree.node A10K2.t1826 (nat_lit 29367794) (nat_lit 13055503498) (nat_lit 0) A10K2.t1827 from rfl, totK_node, tot1826, tot1827]
  decide +kernel

theorem arows1823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1823 = true := by
  rw [show A10K2.u1823 = KTree.node A10K2.t1828 (nat_lit 29383168) (nat_lit 14966411464) (nat_lit 0) A10K2.t1829 from rfl, allE_node, rows1828, irow1823, rows1829]
  all_goals rfl

theorem atot1823 : totK PA10K2 A10K2.u1823 = [0, 553939909338, 2729016852333, 4109400131068, 1962790891402, 257289443811, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1823 = KTree.node A10K2.t1828 (nat_lit 29383168) (nat_lit 14966411464) (nat_lit 0) A10K2.t1829 from rfl, totK_node, tot1828, tot1829]
  decide +kernel

theorem arows1824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1824 = true := by
  rw [show A10K2.u1824 = KTree.node A10K2.t1830 (nat_lit 29389120) (nat_lit 14723311317) (nat_lit 0) A10K2.t1831 from rfl, allE_node, rows1830, irow1824, rows1831]
  all_goals rfl

theorem atot1824 : totK PA10K2 A10K2.u1824 = [0, 314008318368, 2122281897892, 4253234177006, 2879466696592, 525661186427, 13803657628, 0, 0, 0] := by
  rw [show A10K2.u1824 = KTree.node A10K2.t1830 (nat_lit 29389120) (nat_lit 14723311317) (nat_lit 0) A10K2.t1831 from rfl, totK_node, tot1830, tot1831]
  decide +kernel

theorem arows1827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1827 = true := by
  rw [show A10K2.u1827 = KTree.node A10K2.t1832 (nat_lit 29393814) (nat_lit 14732098858) (nat_lit 0) A10K2.t1833 from rfl, allE_node, rows1832, irow1827, rows1833]
  all_goals rfl

theorem atot1827 : totK PA10K2 A10K2.u1827 = [0, 0, 857619018055, 3477245289208, 4077129038463, 1282744179534, 87129073139, 0, 0, 0] := by
  rw [show A10K2.u1827 = KTree.node A10K2.t1832 (nat_lit 29393814) (nat_lit 14732098858) (nat_lit 0) A10K2.t1833 from rfl, totK_node, tot1832, tot1833]
  decide +kernel

theorem arows1828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1828 = true := by
  rw [show A10K2.u1828 = KTree.node A10K2.t1834 (nat_lit 29399557) (nat_lit 6584847527) (nat_lit 0) A10K2.t1835 from rfl, allE_node, rows1834, irow1828, rows1835]
  all_goals rfl

theorem atot1828 : totK PA10K2 A10K2.u1828 = [0, 0, 290974432811, 1922013481989, 3900825903113, 2696116058332, 568718202469, 30650496230, 0, 0] := by
  rw [show A10K2.u1828 = KTree.node A10K2.t1834 (nat_lit 29399557) (nat_lit 6584847527) (nat_lit 0) A10K2.t1835 from rfl, totK_node, tot1834, tot1835]
  decide +kernel

theorem arows1830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1830 = true := by
  rw [show A10K2.u1830 = KTree.node A10K2.t1836 (nat_lit 29413830) (nat_lit 13745617411) (nat_lit 0) A10K2.t1837 from rfl, allE_node, rows1836, irow1830, rows1837]
  all_goals rfl

theorem atot1830 : totK PA10K2 A10K2.u1830 = [0, 0, 644921811532, 2832246448113, 3979558009952, 1689765524954, 204981600246, 5546304973, 0, 0] := by
  rw [show A10K2.u1830 = KTree.node A10K2.t1836 (nat_lit 29413830) (nat_lit 13745617411) (nat_lit 0) A10K2.t1837 from rfl, totK_node, tot1836, tot1837]
  decide +kernel

theorem arows1831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1831 = true := by
  rw [show A10K2.u1831 = KTree.node A10K2.t1838 (nat_lit 29421246) (nat_lit 16012099655) (nat_lit 0) A10K2.t1839 from rfl, allE_node, rows1838, irow1831, rows1839]
  all_goals rfl

theorem atot1831 : totK PA10K2 A10K2.u1831 = [0, 506452765222, 2111902929013, 3531783341619, 2880991527766, 917665859171, 77578567017, 0, 0, 0] := by
  rw [show A10K2.u1831 = KTree.node A10K2.t1838 (nat_lit 29421246) (nat_lit 16012099655) (nat_lit 0) A10K2.t1839 from rfl, totK_node, tot1838, tot1839]
  decide +kernel

theorem arows1835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1835 = true := by
  rw [show A10K2.u1835 = KTree.node A10K2.t1840 (nat_lit 29495686) (nat_lit 15249561628) (nat_lit 0) A10K2.t1841 from rfl, allE_node, rows1840, irow1835, rows1841]
  all_goals rfl

theorem atot1835 : totK PA10K2 A10K2.u1835 = [0, 275897505342, 2045483247676, 4097099787598, 2722945190950, 559771451961, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1835 = KTree.node A10K2.t1840 (nat_lit 29495686) (nat_lit 15249561628) (nat_lit 0) A10K2.t1841 from rfl, totK_node, tot1840, tot1841]
  decide +kernel

theorem arows1836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1836 = true := by
  rw [show A10K2.u1836 = KTree.node A10K2.t1842 (nat_lit 29509664) (nat_lit 13722426567) (nat_lit 0) A10K2.t1843 from rfl, allE_node, rows1842, irow1836, rows1843]
  all_goals rfl

theorem atot1836 : totK PA10K2 A10K2.u1836 = [0, 741023122864, 3163489989434, 4074104614067, 1541429666412, 113561859360, 0, 0, 0, 0] := by
  rw [show A10K2.u1836 = KTree.node A10K2.t1842 (nat_lit 29509664) (nat_lit 13722426567) (nat_lit 0) A10K2.t1843 from rfl, totK_node, tot1842, tot1843]
  decide +kernel

theorem arows1838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1838 = true := by
  rw [show A10K2.u1838 = KTree.node A10K2.t1844 (nat_lit 29524749) (nat_lit 5851490617) (nat_lit 0) A10K2.t1845 from rfl, allE_node, rows1844, irow1838, rows1845]
  all_goals rfl

theorem atot1838 : totK PA10K2 A10K2.u1838 = [0, 0, 1081214685505, 3853088553342, 3757701323056, 899745940845, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u1838 = KTree.node A10K2.t1844 (nat_lit 29524749) (nat_lit 5851490617) (nat_lit 0) A10K2.t1845 from rfl, totK_node, tot1844, tot1845]
  decide +kernel

theorem arows1839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1839 = true := by
  rw [show A10K2.u1839 = KTree.node A10K2.t1846 (nat_lit 29542478) (nat_lit 8322327484) (nat_lit 0) A10K2.t1847 from rfl, allE_node, rows1846, irow1839, rows1847]
  all_goals rfl

theorem atot1839 : totK PA10K2 A10K2.u1839 = [0, 0, 737179009385, 3281551754170, 4070532891269, 1261709479202, 88572674970, 0, 0, 0] := by
  rw [show A10K2.u1839 = KTree.node A10K2.t1846 (nat_lit 29542478) (nat_lit 8322327484) (nat_lit 0) A10K2.t1847 from rfl, totK_node, tot1846, tot1847]
  decide +kernel

theorem arows1842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1842 = true := by
  rw [show A10K2.u1842 = KTree.node A10K2.t1848 (nat_lit 29558793) (nat_lit 9791040699) (nat_lit 0) A10K2.t1849 from rfl, allE_node, rows1848, irow1842, rows1849]
  all_goals rfl

theorem atot1842 : totK PA10K2 A10K2.u1842 = [0, 801349738877, 2928813590949, 3387989700461, 1788042736404, 718800686891, 137525537872, 6354482628, 0, 0] := by
  rw [show A10K2.u1842 = KTree.node A10K2.t1848 (nat_lit 29558793) (nat_lit 9791040699) (nat_lit 0) A10K2.t1849 from rfl, totK_node, tot1848, tot1849]
  decide +kernel

theorem arows1843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1843 = true := by
  rw [show A10K2.u1843 = KTree.node A10K2.t1850 (nat_lit 29563959) (nat_lit 14838044417) (nat_lit 0) A10K2.t1851 from rfl, allE_node, rows1850, irow1843, rows1851]
  all_goals rfl

theorem atot1843 : totK PA10K2 A10K2.u1843 = [0, 474133625560, 2260863926630, 3911999298182, 2599978407361, 554159702634, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u1843 = KTree.node A10K2.t1850 (nat_lit 29563959) (nat_lit 14838044417) (nat_lit 0) A10K2.t1851 from rfl, totK_node, tot1850, tot1851]
  decide +kernel

theorem arows1845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1845 = true := by
  rw [show A10K2.u1845 = KTree.node A10K2.t1852 (nat_lit 29572167) (nat_lit 11187645446) (nat_lit 0) A10K2.t1853 from rfl, allE_node, rows1852, irow1845, rows1853]
  all_goals rfl

theorem atot1845 : totK PA10K2 A10K2.u1845 = [0, 504651784837, 2539490732555, 4116948661720, 2367355611580, 404513089150, 13561316338, 0, 0, 0] := by
  rw [show A10K2.u1845 = KTree.node A10K2.t1852 (nat_lit 29572167) (nat_lit 11187645446) (nat_lit 0) A10K2.t1853 from rfl, totK_node, tot1852, tot1853]
  decide +kernel

theorem arows1846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1846 = true := by
  rw [show A10K2.u1846 = KTree.node A10K2.t1854 (nat_lit 29585344) (nat_lit 14627760404) (nat_lit 0) A10K2.t1855 from rfl, allE_node, rows1854, irow1846, rows1855]
  all_goals rfl

theorem atot1846 : totK PA10K2 A10K2.u1846 = [0, 441902469423, 2293595887008, 4075934855016, 2624658160345, 490425507483, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u1846 = KTree.node A10K2.t1854 (nat_lit 29585344) (nat_lit 14627760404) (nat_lit 0) A10K2.t1855 from rfl, totK_node, tot1854, tot1855]
  decide +kernel

theorem arows1852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1852 = true := by
  rw [show A10K2.u1852 = KTree.node A10K2.t1856 (nat_lit 29589907) (nat_lit 6470238243) (nat_lit 0) A10K2.t1857 from rfl, allE_node, rows1856, irow1852, rows1857]
  all_goals rfl

theorem atot1852 : totK PA10K2 A10K2.u1852 = [0, 0, 1127692749523, 3809528222643, 3811705269765, 1121568036084, 80261166969, 0, 0, 0] := by
  rw [show A10K2.u1852 = KTree.node A10K2.t1856 (nat_lit 29589907) (nat_lit 6470238243) (nat_lit 0) A10K2.t1857 from rfl, totK_node, tot1856, tot1857]
  decide +kernel

theorem arows1853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1853 = true := by
  rw [show A10K2.u1853 = KTree.node A10K2.t1858 (nat_lit 29595717) (nat_lit 6142726048) (nat_lit 0) A10K2.t1859 from rfl, allE_node, rows1858, irow1853, rows1859]
  all_goals rfl

theorem atot1853 : totK PA10K2 A10K2.u1853 = [0, 0, 335575915953, 2241375291884, 4403580379411, 2557388612105, 349837431481, 6904928264, 0, 0] := by
  rw [show A10K2.u1853 = KTree.node A10K2.t1858 (nat_lit 29595717) (nat_lit 6142726048) (nat_lit 0) A10K2.t1859 from rfl, totK_node, tot1858, tot1859]
  decide +kernel

theorem arows1855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1855 = true := by
  rw [show A10K2.u1855 = KTree.node A10K2.t1860 (nat_lit 29603556) (nat_lit 9240787539) (nat_lit 0) A10K2.t1861 from rfl, allE_node, rows1860, irow1855, rows1861]
  all_goals rfl

theorem atot1855 : totK PA10K2 A10K2.u1855 = [0, 0, 568296378219, 2691651885967, 4160485879744, 2280239312396, 297740868944, 7047025452, 0, 0] := by
  rw [show A10K2.u1855 = KTree.node A10K2.t1860 (nat_lit 29603556) (nat_lit 9240787539) (nat_lit 0) A10K2.t1861 from rfl, totK_node, tot1860, tot1861]
  decide +kernel

theorem arows1856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1856 = true := by
  rw [show A10K2.u1856 = KTree.node A10K2.t1862 (nat_lit 29617850) (nat_lit 14751209857) (nat_lit 0) A10K2.t1863 from rfl, allE_node, rows1862, irow1856, rows1863]
  all_goals rfl

theorem atot1856 : totK PA10K2 A10K2.u1856 = [0, 0, 514979835180, 2562055866837, 4116461527015, 2334049038034, 319277976306, 6066958478, 0, 0] := by
  rw [show A10K2.u1856 = KTree.node A10K2.t1862 (nat_lit 29617850) (nat_lit 14751209857) (nat_lit 0) A10K2.t1863 from rfl, totK_node, tot1862, tot1863]
  decide +kernel

theorem arows1859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1859 = true := by
  rw [show A10K2.u1859 = KTree.node A10K2.t1864 (nat_lit 29622549) (nat_lit 6640078033) (nat_lit 0) A10K2.t1865 from rfl, allE_node, rows1864, irow1859, rows1865]
  all_goals rfl

theorem atot1859 : totK PA10K2 A10K2.u1859 = [0, 0, 635459705908, 2486474900384, 3494415410234, 2310115114351, 693198305626, 55043167628, 0, 0] := by
  rw [show A10K2.u1859 = KTree.node A10K2.t1864 (nat_lit 29622549) (nat_lit 6640078033) (nat_lit 0) A10K2.t1865 from rfl, totK_node, tot1864, tot1865]
  decide +kernel

theorem arows1860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1860 = true := by
  rw [show A10K2.u1860 = KTree.node A10K2.t1866 (nat_lit 29626937) (nat_lit 7115393801) (nat_lit 0) A10K2.t1867 from rfl, allE_node, rows1866, irow1860, rows1867]
  all_goals rfl

theorem atot1860 : totK PA10K2 A10K2.u1860 = [0, 0, 251986493949, 1826621531062, 4075073569765, 2914422355537, 585145896603, 30831673886, 0, 0] := by
  rw [show A10K2.u1860 = KTree.node A10K2.t1866 (nat_lit 29626937) (nat_lit 7115393801) (nat_lit 0) A10K2.t1867 from rfl, totK_node, tot1866, tot1867]
  decide +kernel

theorem arows1862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1862 = true := by
  rw [show A10K2.u1862 = KTree.node A10K2.t1868 (nat_lit 29640994) (nat_lit 12646116095) (nat_lit 0) A10K2.t1869 from rfl, allE_node, rows1868, irow1862, rows1869]
  all_goals rfl

theorem atot1862 : totK PA10K2 A10K2.u1862 = [0, 0, 613731661535, 2946725079396, 4154169796385, 1597853674400, 124045835428, 0, 0, 0] := by
  rw [show A10K2.u1862 = KTree.node A10K2.t1868 (nat_lit 29640994) (nat_lit 12646116095) (nat_lit 0) A10K2.t1869 from rfl, totK_node, tot1868, tot1869]
  decide +kernel

theorem arows1863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1863 = true := by
  rw [show A10K2.u1863 = KTree.node A10K2.t1870 (nat_lit 29648595) (nat_lit 10566627647) (nat_lit 0) A10K2.t1871 from rfl, allE_node, rows1870, irow1863, rows1871]
  all_goals rfl

theorem atot1863 : totK PA10K2 A10K2.u1863 = [0, 0, 799225256197, 3160728687667, 4002811682391, 1728383974947, 217339502986, 5705019915, 0, 0] := by
  rw [show A10K2.u1863 = KTree.node A10K2.t1870 (nat_lit 29648595) (nat_lit 10566627647) (nat_lit 0) A10K2.t1871 from rfl, totK_node, tot1870, tot1871]
  decide +kernel

theorem arows1867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1867 = true := by
  rw [show A10K2.u1867 = KTree.node A10K2.t1872 (nat_lit 29654715) (nat_lit 6438770386) (nat_lit 0) A10K2.t1873 from rfl, allE_node, rows1872, irow1867, rows1873]
  all_goals rfl

theorem atot1867 : totK PA10K2 A10K2.u1867 = [0, 0, 0, 1130379318105, 3854816985438, 3808503568943, 1012064837940, 60698249753, 0, 0] := by
  rw [show A10K2.u1867 = KTree.node A10K2.t1872 (nat_lit 29654715) (nat_lit 6438770386) (nat_lit 0) A10K2.t1873 from rfl, totK_node, tot1872, tot1873]
  decide +kernel

theorem arows1868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1868 = true := by
  rw [show A10K2.u1868 = KTree.node A10K2.t1874 (nat_lit 29659492) (nat_lit 13219278247) (nat_lit 0) A10K2.t1875 from rfl, allE_node, rows1874, irow1868, rows1875]
  all_goals rfl

theorem atot1868 : totK PA10K2 A10K2.u1868 = [0, 0, 0, 286915412457, 2065950387017, 3907105105450, 2490425247171, 527148285369, 30605747850, 0] := by
  rw [show A10K2.u1868 = KTree.node A10K2.t1874 (nat_lit 29659492) (nat_lit 13219278247) (nat_lit 0) A10K2.t1875 from rfl, totK_node, tot1874, tot1875]
  decide +kernel

theorem arows1870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1870 = true := by
  rw [show A10K2.u1870 = KTree.node A10K2.t1876 (nat_lit 29673749) (nat_lit 7051909534) (nat_lit 0) A10K2.t1877 from rfl, allE_node, rows1876, irow1870, rows1877]
  all_goals rfl

theorem atot1870 : totK PA10K2 A10K2.u1870 = [0, 0, 0, 634732661821, 2915006039836, 4027436605257, 1571335744345, 139407627070, 0, 0] := by
  rw [show A10K2.u1870 = KTree.node A10K2.t1876 (nat_lit 29673749) (nat_lit 7051909534) (nat_lit 0) A10K2.t1877 from rfl, totK_node, tot1876, tot1877]
  decide +kernel

theorem arows1871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1871 = true := by
  rw [show A10K2.u1871 = KTree.node A10K2.t1878 (nat_lit 29682870) (nat_lit 16606316129) (nat_lit 0) A10K2.t1879 from rfl, allE_node, rows1878, irow1871, rows1879]
  all_goals rfl

theorem atot1871 : totK PA10K2 A10K2.u1871 = [0, 0, 307513935741, 1819362433894, 3667373123723, 2995784652481, 971107260255, 149834806776, 5528811039, 0] := by
  rw [show A10K2.u1871 = KTree.node A10K2.t1878 (nat_lit 29682870) (nat_lit 16606316129) (nat_lit 0) A10K2.t1879 from rfl, totK_node, tot1878, tot1879]
  decide +kernel

theorem arows1874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1874 = true := by
  rw [show A10K2.u1874 = KTree.node A10K2.t1880 (nat_lit 29757430) (nat_lit 16623752327) (nat_lit 0) A10K2.t1881 from rfl, allE_node, rows1880, irow1874, rows1881]
  all_goals rfl

theorem atot1874 : totK PA10K2 A10K2.u1874 = [0, 0, 486142690369, 2435621585833, 4015364239520, 2315306505661, 442424294309, 25371180993, 0, 0] := by
  rw [show A10K2.u1874 = KTree.node A10K2.t1880 (nat_lit 29757430) (nat_lit 16623752327) (nat_lit 0) A10K2.t1881 from rfl, totK_node, tot1880, tot1881]
  decide +kernel

theorem arows1875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1875 = true := by
  rw [show A10K2.u1875 = KTree.node A10K2.t1882 (nat_lit 29771031) (nat_lit 4303005998) (nat_lit 0) A10K2.t1883 from rfl, allE_node, rows1882, irow1875, rows1883]
  all_goals rfl

theorem atot1875 : totK PA10K2 A10K2.u1875 = [0, 0, 740324425966, 3120903606987, 3924232066870, 1587234273174, 198374363955, 5460492893, 0, 0] := by
  rw [show A10K2.u1875 = KTree.node A10K2.t1882 (nat_lit 29771031) (nat_lit 4303005998) (nat_lit 0) A10K2.t1883 from rfl, totK_node, tot1882, tot1883]
  decide +kernel

theorem arows1877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1877 = true := by
  rw [show A10K2.u1877 = KTree.node A10K2.t1884 (nat_lit 29819277) (nat_lit 4943085759) (nat_lit 0) A10K2.t1885 from rfl, allE_node, rows1884, irow1877, rows1885]
  all_goals rfl

theorem atot1877 : totK PA10K2 A10K2.u1877 = [0, 0, 801349738877, 3019640049852, 3847517878714, 1722074438761, 207324807225, 6354482628, 0, 0] := by
  rw [show A10K2.u1877 = KTree.node A10K2.t1884 (nat_lit 29819277) (nat_lit 4943085759) (nat_lit 0) A10K2.t1885 from rfl, totK_node, tot1884, tot1885]
  decide +kernel

theorem arows1878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1878 = true := by
  rw [show A10K2.u1878 = KTree.node A10K2.t1886 (nat_lit 29825031) (nat_lit 11927655893) (nat_lit 0) A10K2.t1887 from rfl, allE_node, rows1886, irow1878, rows1887]
  all_goals rfl

theorem atot1878 : totK PA10K2 A10K2.u1878 = [0, 0, 254308263408, 2115083486352, 4349283897952, 2664766956493, 476275333742, 25313348169, 0, 0] := by
  rw [show A10K2.u1878 = KTree.node A10K2.t1886 (nat_lit 29825031) (nat_lit 11927655893) (nat_lit 0) A10K2.t1887 from rfl, totK_node, tot1886, tot1887]
  decide +kernel

theorem arows1883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1883 = true := by
  rw [show A10K2.u1883 = KTree.node A10K2.t1888 (nat_lit 29832874) (nat_lit 12753109878) (nat_lit 0) A10K2.t1889 from rfl, allE_node, rows1888, irow1883, rows1889]
  all_goals rfl

theorem atot1883 : totK PA10K2 A10K2.u1883 = [0, 0, 590081868593, 2738480362112, 4224207280577, 2246975677504, 305782583364, 7151180950, 0, 0] := by
  rw [show A10K2.u1883 = KTree.node A10K2.t1888 (nat_lit 29832874) (nat_lit 12753109878) (nat_lit 0) A10K2.t1889 from rfl, totK_node, tot1888, tot1889]
  decide +kernel

theorem arows1884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1884 = true := by
  rw [show A10K2.u1884 = KTree.node A10K2.t1890 (nat_lit 29847187) (nat_lit 10748451029) (nat_lit 0) A10K2.t1891 from rfl, allE_node, rows1890, irow1884, rows1891]
  all_goals rfl

theorem atot1884 : totK PA10K2 A10K2.u1884 = [0, 0, 576020245237, 2651853563681, 4126699855200, 2227301001578, 319601682046, 6853348008, 0, 0] := by
  rw [show A10K2.u1884 = KTree.node A10K2.t1890 (nat_lit 29847187) (nat_lit 10748451029) (nat_lit 0) A10K2.t1891 from rfl, totK_node, tot1890, tot1891]
  decide +kernel

theorem arows1886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1886 = true := by
  rw [show A10K2.u1886 = KTree.node A10K2.t1892 (nat_lit 29959390) (nat_lit 11380694468) (nat_lit 0) A10K2.t1893 from rfl, allE_node, rows1892, irow1886, rows1893]
  all_goals rfl

theorem atot1886 : totK PA10K2 A10K2.u1886 = [0, 554649933044, 2023642877639, 2409535408759, 2007984104925, 1999513966768, 715766245334, 55515214941, 0, 0] := by
  rw [show A10K2.u1886 = KTree.node A10K2.t1892 (nat_lit 29959390) (nat_lit 11380694468) (nat_lit 0) A10K2.t1893 from rfl, totK_node, tot1892, tot1893]
  decide +kernel

theorem arows1887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1887 = true := by
  rw [show A10K2.u1887 = KTree.node A10K2.t1894 (nat_lit 29963925) (nat_lit 6345738522) (nat_lit 0) A10K2.t1895 from rfl, allE_node, rows1894, irow1887, rows1895]
  all_goals rfl

theorem atot1887 : totK PA10K2 A10K2.u1887 = [0, 292708456977, 1922955342444, 4008034529557, 2952398644437, 600742691056, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1887 = KTree.node A10K2.t1894 (nat_lit 29963925) (nat_lit 6345738522) (nat_lit 0) A10K2.t1895 from rfl, totK_node, tot1894, tot1895]
  decide +kernel

theorem arows1890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1890 = true := by
  rw [show A10K2.u1890 = KTree.node A10K2.t1896 (nat_lit 29969059) (nat_lit 10414015437) (nat_lit 0) A10K2.t1897 from rfl, allE_node, rows1896, irow1890, rows1897]
  all_goals rfl

theorem atot1890 : totK PA10K2 A10K2.u1890 = [0, 642365692677, 2781791500132, 3977335422566, 1957373467603, 258287135340, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1890 = KTree.node A10K2.t1896 (nat_lit 29969059) (nat_lit 10414015437) (nat_lit 0) A10K2.t1897 from rfl, totK_node, tot1896, tot1897]
  decide +kernel

theorem arows1891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1891 = true := by
  rw [show A10K2.u1891 = KTree.node A10K2.t1898 (nat_lit 29977764) (nat_lit 9121989017) (nat_lit 0) A10K2.t1899 from rfl, allE_node, rows1898, irow1891, rows1899]
  all_goals rfl

theorem atot1891 : totK PA10K2 A10K2.u1891 = [0, 721502689397, 3079472424428, 4162685440294, 1967150066938, 298097819195, 6840736825, 0, 0, 0] := by
  rw [show A10K2.u1891 = KTree.node A10K2.t1898 (nat_lit 29977764) (nat_lit 9121989017) (nat_lit 0) A10K2.t1899 from rfl, totK_node, tot1898, tot1899]
  decide +kernel

theorem arows1893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1893 = true := by
  rw [show A10K2.u1893 = KTree.node A10K2.t1900 (nat_lit 29982605) (nat_lit 1737148207) (nat_lit 0) A10K2.t1901 from rfl, allE_node, rows1900, irow1893, rows1901]
  all_goals rfl

theorem atot1893 : totK PA10K2 A10K2.u1893 = [0, 0, 1049244037651, 3705977256003, 3826879991174, 1169158061360, 82549656006, 0, 0, 0] := by
  rw [show A10K2.u1893 = KTree.node A10K2.t1900 (nat_lit 29982605) (nat_lit 1737148207) (nat_lit 0) A10K2.t1901 from rfl, totK_node, tot1900, tot1901]
  decide +kernel

theorem arows1894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1894 = true := by
  rw [show A10K2.u1894 = KTree.node A10K2.t1902 (nat_lit 29996317) (nat_lit 6312537687) (nat_lit 0) A10K2.t1903 from rfl, allE_node, rows1902, irow1894, rows1903]
  all_goals rfl

theorem atot1894 : totK PA10K2 A10K2.u1894 = [0, 0, 292243983067, 2088367120970, 4040103454748, 2577041974267, 538907410839, 31082886609, 0, 0] := by
  rw [show A10K2.u1894 = KTree.node A10K2.t1902 (nat_lit 29996317) (nat_lit 6312537687) (nat_lit 0) A10K2.t1903 from rfl, totK_node, tot1902, tot1903]
  decide +kernel

theorem arows1898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1898 = true := by
  rw [show A10K2.u1898 = KTree.node A10K2.t1904 (nat_lit 30001444) (nat_lit 14257594719) (nat_lit 0) A10K2.t1905 from rfl, allE_node, rows1904, irow1898, rows1905]
  all_goals rfl

theorem atot1898 : totK PA10K2 A10K2.u1898 = [0, 0, 561620743098, 2713243926523, 4189457697186, 1918235813410, 185085570599, 0, 0, 0] := by
  rw [show A10K2.u1898 = KTree.node A10K2.t1904 (nat_lit 30001444) (nat_lit 14257594719) (nat_lit 0) A10K2.t1905 from rfl, totK_node, tot1904, tot1905]
  decide +kernel

theorem arows1899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1899 = true := by
  rw [show A10K2.u1899 = KTree.node A10K2.t1906 (nat_lit 30010373) (nat_lit 1742778095) (nat_lit 0) A10K2.t1907 from rfl, allE_node, rows1906, irow1899, rows1907]
  all_goals rfl

theorem atot1899 : totK PA10K2 A10K2.u1899 = [0, 285766734819, 1577932179043, 3449624755261, 3372321377513, 1245467172325, 159793653657, 6121173289, 0, 0] := by
  rw [show A10K2.u1899 = KTree.node A10K2.t1906 (nat_lit 30010373) (nat_lit 1742778095) (nat_lit 0) A10K2.t1907 from rfl, totK_node, tot1906, tot1907]
  decide +kernel

theorem arows1901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1901 = true := by
  rw [show A10K2.u1901 = KTree.node A10K2.t1908 (nat_lit 30085218) (nat_lit 2751907505) (nat_lit 0) A10K2.t1909 from rfl, allE_node, rows1908, irow1901, rows1909]
  all_goals rfl

theorem atot1901 : totK PA10K2 A10K2.u1901 = [0, 543883175844, 2551518201067, 4145752272385, 2385236097967, 411620860343, 13349922262, 0, 0, 0] := by
  rw [show A10K2.u1901 = KTree.node A10K2.t1908 (nat_lit 30085218) (nat_lit 2751907505) (nat_lit 0) A10K2.t1909 from rfl, totK_node, tot1908, tot1909]
  decide +kernel

theorem arows1902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1902 = true := by
  rw [show A10K2.u1902 = KTree.node A10K2.t1910 (nat_lit 30092750) (nat_lit 14771366741) (nat_lit 0) A10K2.t1911 from rfl, allE_node, rows1910, irow1902, rows1911]
  all_goals rfl

theorem atot1902 : totK PA10K2 A10K2.u1902 = [0, 540850438005, 2658689796235, 4072347543803, 2217823406819, 427949727887, 25715051306, 0, 0, 0] := by
  rw [show A10K2.u1902 = KTree.node A10K2.t1910 (nat_lit 30092750) (nat_lit 14771366741) (nat_lit 0) A10K2.t1911 from rfl, totK_node, tot1910, tot1911]
  decide +kernel

theorem arows1905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1905 = true := by
  rw [show A10K2.u1905 = KTree.node A10K2.t1912 (nat_lit 30106182) (nat_lit 13415364663) (nat_lit 0) A10K2.t1913 from rfl, allE_node, rows1912, irow1905, rows1913]
  all_goals rfl

theorem atot1905 : totK PA10K2 A10K2.u1905 = [0, 866947050573, 3133735764756, 3885340417918, 1806190900295, 247322272269, 6032141194, 0, 0, 0] := by
  rw [show A10K2.u1905 = KTree.node A10K2.t1912 (nat_lit 30106182) (nat_lit 13415364663) (nat_lit 0) A10K2.t1913 from rfl, totK_node, tot1912, tot1913]
  decide +kernel

theorem arows1906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1906 = true := by
  rw [show A10K2.u1906 = KTree.node A10K2.t1914 (nat_lit 30110944) (nat_lit 2704343515) (nat_lit 0) A10K2.t1915 from rfl, allE_node, rows1914, irow1906, rows1915]
  all_goals rfl

theorem atot1906 : totK PA10K2 A10K2.u1906 = [0, 0, 1341495351692, 4172443014870, 3660791677298, 832247507186, 25672301411, 0, 0, 0] := by
  rw [show A10K2.u1906 = KTree.node A10K2.t1914 (nat_lit 30110944) (nat_lit 2704343515) (nat_lit 0) A10K2.t1915 from rfl, totK_node, tot1914, tot1915]
  decide +kernel

theorem arows1908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1908 = true := by
  rw [show A10K2.u1908 = KTree.node A10K2.t1916 (nat_lit 30117371) (nat_lit 6145254905) (nat_lit 0) A10K2.t1917 from rfl, allE_node, rows1916, irow1908, rows1917]
  all_goals rfl

theorem atot1908 : totK PA10K2 A10K2.u1908 = [0, 0, 591520450209, 2722211794186, 4187971220047, 2241815813664, 293634445725, 6904928264, 0, 0] := by
  rw [show A10K2.u1908 = KTree.node A10K2.t1916 (nat_lit 30117371) (nat_lit 6145254905) (nat_lit 0) A10K2.t1917 from rfl, totK_node, tot1916, tot1917]
  decide +kernel

theorem arows1909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1909 = true := by
  rw [show A10K2.u1909 = KTree.node A10K2.t1918 (nat_lit 30124716) (nat_lit 11963881257) (nat_lit 0) A10K2.t1919 from rfl, allE_node, rows1918, irow1909, rows1919]
  all_goals rfl

theorem atot1909 : totK PA10K2 A10K2.u1909 = [0, 0, 786877021441, 3258452353223, 4102493128724, 1625321726497, 147386244137, 0, 0, 0] := by
  rw [show A10K2.u1909 = KTree.node A10K2.t1918 (nat_lit 30124716) (nat_lit 11963881257) (nat_lit 0) A10K2.t1919 from rfl, totK_node, tot1918, tot1919]
  decide +kernel

theorem arows1916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1916 = true := by
  rw [show A10K2.u1916 = KTree.node A10K2.t1920 (nat_lit 30138822) (nat_lit 15671917983) (nat_lit 0) A10K2.t1921 from rfl, allE_node, rows1920, irow1916, rows1921]
  all_goals rfl

theorem atot1916 : totK PA10K2 A10K2.u1916 = [0, 0, 744098969203, 2942738583774, 3949638866231, 1999668540982, 280985905428, 7047025452, 0, 0] := by
  rw [show A10K2.u1916 = KTree.node A10K2.t1920 (nat_lit 30138822) (nat_lit 15671917983) (nat_lit 0) A10K2.t1921 from rfl, totK_node, tot1920, tot1921]
  decide +kernel

theorem arows1917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1917 = true := by
  rw [show A10K2.u1917 = KTree.node A10K2.t1922 (nat_lit 30143417) (nat_lit 6905817850) (nat_lit 0) A10K2.t1923 from rfl, allE_node, rows1922, irow1917, rows1923]
  all_goals rfl

theorem atot1917 : totK PA10K2 A10K2.u1917 = [0, 0, 122137344176, 1615450256587, 4192200561946, 3327328160871, 634676129872, 17977415720, 0, 0] := by
  rw [show A10K2.u1917 = KTree.node A10K2.t1922 (nat_lit 30143417) (nat_lit 6905817850) (nat_lit 0) A10K2.t1923 from rfl, totK_node, tot1922, tot1923]
  decide +kernel

theorem arows1919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1919 = true := by
  rw [show A10K2.u1919 = KTree.node A10K2.t1924 (nat_lit 30222598) (nat_lit 11933677) (nat_lit 0) A10K2.t1925 from rfl, allE_node, rows1924, irow1919, rows1925]
  all_goals rfl

theorem atot1919 : totK PA10K2 A10K2.u1919 = [0, 0, 846871377146, 3217747476447, 3742377779362, 1595302339699, 407765595963, 43132710386, 0, 0] := by
  rw [show A10K2.u1919 = KTree.node A10K2.t1924 (nat_lit 30222598) (nat_lit 11933677) (nat_lit 0) A10K2.t1925 from rfl, totK_node, tot1924, tot1925]
  decide +kernel

theorem arows1920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1920 = true := by
  rw [show A10K2.u1920 = KTree.node A10K2.t1926 (nat_lit 30227462) (nat_lit 14669878319) (nat_lit 0) A10K2.t1927 from rfl, allE_node, rows1926, irow1920, rows1927]
  all_goals rfl

theorem atot1920 : totK PA10K2 A10K2.u1920 = [0, 0, 403059149735, 2019835133410, 3796644868272, 2781877798244, 594924703973, 31768748853, 0, 0] := by
  rw [show A10K2.u1920 = KTree.node A10K2.t1926 (nat_lit 30227462) (nat_lit 14669878319) (nat_lit 0) A10K2.t1927 from rfl, totK_node, tot1926, tot1927]
  decide +kernel

theorem arows1923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1923 = true := by
  rw [show A10K2.u1923 = KTree.node A10K2.t1928 (nat_lit 30234984) (nat_lit 9455488170) (nat_lit 0) A10K2.t1929 from rfl, allE_node, rows1928, irow1923, rows1929]
  all_goals rfl

theorem atot1923 : totK PA10K2 A10K2.u1923 = [0, 0, 646085331568, 2936424988945, 4132635285612, 1832278101368, 224286094321, 6239673734, 0, 0] := by
  rw [show A10K2.u1923 = KTree.node A10K2.t1928 (nat_lit 30234984) (nat_lit 9455488170) (nat_lit 0) A10K2.t1929 from rfl, totK_node, tot1928, tot1929]
  decide +kernel

theorem arows1924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1924 = true := by
  rw [show A10K2.u1924 = KTree.node A10K2.t1930 (nat_lit 30241267) (nat_lit 7799539766) (nat_lit 0) A10K2.t1931 from rfl, allE_node, rows1930, irow1924, rows1931]
  all_goals rfl

theorem atot1924 : totK PA10K2 A10K2.u1924 = [0, 0, 313255680567, 2090787934875, 4371867112807, 2912730319029, 446081848562, 6962742351, 0, 0] := by
  rw [show A10K2.u1924 = KTree.node A10K2.t1930 (nat_lit 30241267) (nat_lit 7799539766) (nat_lit 0) A10K2.t1931 from rfl, totK_node, tot1930, tot1931]
  decide +kernel

theorem arows1926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1926 = true := by
  rw [show A10K2.u1926 = KTree.node A10K2.t1932 (nat_lit 30255290) (nat_lit 14957480092) (nat_lit 0) A10K2.t1933 from rfl, allE_node, rows1932, irow1926, rows1933]
  all_goals rfl

theorem atot1926 : totK PA10K2 A10K2.u1926 = [0, 0, 0, 835228415024, 3364960552755, 4044013961306, 1400220054267, 105369073954, 0, 0] := by
  rw [show A10K2.u1926 = KTree.node A10K2.t1932 (nat_lit 30255290) (nat_lit 14957480092) (nat_lit 0) A10K2.t1933 from rfl, totK_node, tot1932, tot1933]
  decide +kernel

theorem arows1927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1927 = true := by
  rw [show A10K2.u1927 = KTree.node A10K2.t1934 (nat_lit 30262458) (nat_lit 14985198586) (nat_lit 0) A10K2.t1935 from rfl, allE_node, rows1934, irow1927, rows1935]
  all_goals rfl

theorem atot1927 : totK PA10K2 A10K2.u1927 = [0, 0, 0, 859297058299, 3089770816981, 3742275745999, 1714305767685, 261924018861, 8047840951, 0] := by
  rw [show A10K2.u1927 = KTree.node A10K2.t1934 (nat_lit 30262458) (nat_lit 14985198586) (nat_lit 0) A10K2.t1935 from rfl, totK_node, tot1934, tot1935]
  decide +kernel

theorem arows1931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1931 = true := by
  rw [show A10K2.u1931 = KTree.node A10K2.t1936 (nat_lit 30273470) (nat_lit 16396326754) (nat_lit 0) A10K2.t1937 from rfl, allE_node, rows1936, irow1931, rows1937]
  all_goals rfl

theorem atot1931 : totK PA10K2 A10K2.u1931 = [0, 0, 592533682082, 2465761817079, 3766336481896, 2601360506400, 690633962584, 44834977902, 0, 0] := by
  rw [show A10K2.u1931 = KTree.node A10K2.t1936 (nat_lit 30273470) (nat_lit 16396326754) (nat_lit 0) A10K2.t1937 from rfl, totK_node, tot1936, tot1937]
  decide +kernel

theorem arows1932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1932 = true := by
  rw [show A10K2.u1932 = KTree.node A10K2.t1938 (nat_lit 30350783) (nat_lit 14297797703) (nat_lit 0) A10K2.t1939 from rfl, allE_node, rows1938, irow1932, rows1939]
  all_goals rfl

theorem atot1932 : totK PA10K2 A10K2.u1932 = [0, 0, 516596241516, 2589112129566, 4222141674492, 2288515083110, 334026183275, 7007974415, 0, 0] := by
  rw [show A10K2.u1932 = KTree.node A10K2.t1938 (nat_lit 30350783) (nat_lit 14297797703) (nat_lit 0) A10K2.t1939 from rfl, totK_node, tot1938, tot1939]
  decide +kernel

theorem arows1934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1934 = true := by
  rw [show A10K2.u1934 = KTree.node A10K2.t1940 (nat_lit 30357148) (nat_lit 11134976119) (nat_lit 0) A10K2.t1941 from rfl, allE_node, rows1940, irow1934, rows1941]
  all_goals rfl

theorem atot1934 : totK PA10K2 A10K2.u1934 = [0, 0, 409037795253, 2185431315376, 4067419196540, 2788441281314, 485970969529, 13572172291, 0, 0] := by
  rw [show A10K2.u1934 = KTree.node A10K2.t1940 (nat_lit 30357148) (nat_lit 11134976119) (nat_lit 0) A10K2.t1941 from rfl, totK_node, tot1940, tot1941]
  decide +kernel

theorem arows1935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1935 = true := by
  rw [show A10K2.u1935 = KTree.node A10K2.t1942 (nat_lit 30370912) (nat_lit 12560228337) (nat_lit 0) A10K2.t1943 from rfl, allE_node, rows1942, irow1935, rows1943]
  all_goals rfl

theorem atot1935 : totK PA10K2 A10K2.u1935 = [0, 0, 727352339921, 3102013600415, 4161623270530, 1820715775377, 218854988373, 6281495166, 0, 0] := by
  rw [show A10K2.u1935 = KTree.node A10K2.t1942 (nat_lit 30370912) (nat_lit 12560228337) (nat_lit 0) A10K2.t1943 from rfl, totK_node, tot1942, tot1943]
  decide +kernel

theorem arows1938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1938 = true := by
  rw [show A10K2.u1938 = KTree.node A10K2.t1944 (nat_lit 30375473) (nat_lit 9249675876) (nat_lit 0) A10K2.t1945 from rfl, allE_node, rows1944, irow1938, rows1945]
  all_goals rfl

theorem atot1938 : totK PA10K2 A10K2.u1938 = [0, 415295505255, 1323007942973, 1876167508767, 2746558889863, 2726134865949, 818782482741, 56100664475, 0, 0] := by
  rw [show A10K2.u1938 = KTree.node A10K2.t1944 (nat_lit 30375473) (nat_lit 9249675876) (nat_lit 0) A10K2.t1945 from rfl, totK_node, tot1944, tot1945]
  decide +kernel

theorem arows1939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1939 = true := by
  rw [show A10K2.u1939 = KTree.node A10K2.t1946 (nat_lit 30937097) (nat_lit 9807832142) (nat_lit 0) A10K2.t1947 from rfl, allE_node, rows1946, irow1939, rows1947]
  all_goals rfl

theorem atot1939 : totK PA10K2 A10K2.u1939 = [0, 404480103954, 2192625134329, 3886956021539, 2543649170721, 513145475211, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u1939 = KTree.node A10K2.t1946 (nat_lit 30937097) (nat_lit 9807832142) (nat_lit 0) A10K2.t1947 from rfl, totK_node, tot1946, tot1947]
  decide +kernel

theorem arows1941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1941 = true := by
  rw [show A10K2.u1941 = KTree.node A10K2.t1948 (nat_lit 30951528) (nat_lit 12030484897) (nat_lit 0) A10K2.t1949 from rfl, allE_node, rows1948, irow1941, rows1949]
  all_goals rfl

theorem atot1941 : totK PA10K2 A10K2.u1941 = [0, 591181298461, 2670192039199, 4072080074543, 2069133949568, 307828218018, 11814975521, 0, 0, 0] := by
  rw [show A10K2.u1941 = KTree.node A10K2.t1948 (nat_lit 30951528) (nat_lit 12030484897) (nat_lit 0) A10K2.t1949 from rfl, totK_node, tot1948, tot1949]
  decide +kernel

theorem arows1942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1942 = true := by
  rw [show A10K2.u1942 = KTree.node A10K2.t1950 (nat_lit 30960699) (nat_lit 6090575109) (nat_lit 0) A10K2.t1951 from rfl, allE_node, rows1950, irow1942, rows1951]
  all_goals rfl

theorem atot1942 : totK PA10K2 A10K2.u1942 = [0, 716351531586, 3167349823998, 4260048350524, 1797610182392, 172521313174, 0, 0, 0, 0] := by
  rw [show A10K2.u1942 = KTree.node A10K2.t1950 (nat_lit 30960699) (nat_lit 6090575109) (nat_lit 0) A10K2.t1951 from rfl, totK_node, tot1950, tot1951]
  decide +kernel

theorem arows1947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1947 = true := by
  rw [show A10K2.u1947 = KTree.node A10K2.t1952 (nat_lit 30965326) (nat_lit 10774798059) (nat_lit 0) A10K2.t1953 from rfl, allE_node, rows1952, irow1947, rows1953]
  all_goals rfl

theorem atot1947 : totK PA10K2 A10K2.u1947 = [0, 0, 950766091242, 3591338973460, 4100045133342, 1293103263997, 88646843074, 0, 0, 0] := by
  rw [show A10K2.u1947 = KTree.node A10K2.t1952 (nat_lit 30965326) (nat_lit 10774798059) (nat_lit 0) A10K2.t1953 from rfl, totK_node, tot1952, tot1953]
  decide +kernel

theorem arows1948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1948 = true := by
  rw [show A10K2.u1948 = KTree.node A10K2.t1954 (nat_lit 30969962) (nat_lit 4071537193) (nat_lit 0) A10K2.t1955 from rfl, allE_node, rows1954, irow1948, rows1955]
  all_goals rfl

theorem atot1948 : totK PA10K2 A10K2.u1948 = [0, 0, 395161385929, 2201905034377, 3860998266159, 2423658707439, 525581918128, 30650496230, 0, 0] := by
  rw [show A10K2.u1948 = KTree.node A10K2.t1954 (nat_lit 30969962) (nat_lit 4071537193) (nat_lit 0) A10K2.t1955 from rfl, totK_node, tot1954, tot1955]
  decide +kernel

theorem arows1950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1950 = true := by
  rw [show A10K2.u1950 = KTree.node A10K2.t1956 (nat_lit 30984752) (nat_lit 13990106741) (nat_lit 0) A10K2.t1957 from rfl, allE_node, rows1956, irow1950, rows1957]
  all_goals rfl

theorem atot1950 : totK PA10K2 A10K2.u1950 = [0, 0, 767385258479, 3246255786150, 4074297478145, 1459613897751, 114247235250, 0, 0, 0] := by
  rw [show A10K2.u1950 = KTree.node A10K2.t1956 (nat_lit 30984752) (nat_lit 13990106741) (nat_lit 0) A10K2.t1957 from rfl, totK_node, tot1956, tot1957]
  decide +kernel

theorem arows1951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1951 = true := by
  rw [show A10K2.u1951 = KTree.node A10K2.t1958 (nat_lit 30993991) (nat_lit 11179514773) (nat_lit 0) A10K2.t1959 from rfl, allE_node, rows1958, irow1951, rows1959]
  all_goals rfl

theorem atot1951 : totK PA10K2 A10K2.u1951 = [0, 409801074616, 1905017990562, 3508089035915, 3129447737312, 1001781334960, 77617841135, 0, 0, 0] := by
  rw [show A10K2.u1951 = KTree.node A10K2.t1958 (nat_lit 30993991) (nat_lit 11179514773) (nat_lit 0) A10K2.t1959 from rfl, totK_node, tot1958, tot1959]
  decide +kernel

theorem arows1954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1954 = true := by
  rw [show A10K2.u1954 = KTree.node A10K2.t1960 (nat_lit 31012108) (nat_lit 7088077074) (nat_lit 0) A10K2.t1961 from rfl, allE_node, rows1960, irow1954, rows1961]
  all_goals rfl

theorem atot1954 : totK PA10K2 A10K2.u1954 = [0, 371335780827, 2174987255886, 4062793165857, 2728447810313, 568573577237, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1954 = KTree.node A10K2.t1960 (nat_lit 31012108) (nat_lit 7088077074) (nat_lit 0) A10K2.t1961 from rfl, totK_node, tot1960, tot1961]
  decide +kernel

theorem arows1955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1955 = true := by
  rw [show A10K2.u1955 = KTree.node A10K2.t1962 (nat_lit 31023141) (nat_lit 4691665701) (nat_lit 0) A10K2.t1963 from rfl, allE_node, rows1962, irow1955, rows1963]
  all_goals rfl

theorem atot1955 : totK PA10K2 A10K2.u1955 = [0, 824318682979, 3270705031309, 4127216768915, 1615946842237, 141883877761, 0, 0, 0, 0] := by
  rw [show A10K2.u1955 = KTree.node A10K2.t1962 (nat_lit 31023141) (nat_lit 4691665701) (nat_lit 0) A10K2.t1963 from rfl, totK_node, tot1962, tot1963]
  decide +kernel

theorem arows1957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1957 = true := by
  rw [show A10K2.u1957 = KTree.node A10K2.t1964 (nat_lit 31028096) (nat_lit 15145072596) (nat_lit 0) A10K2.t1965 from rfl, allE_node, rows1964, irow1957, rows1965]
  all_goals rfl

theorem atot1957 : totK PA10K2 A10K2.u1957 = [0, 270838076424, 1937454363375, 4217520523798, 3213356770155, 617068531857, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u1957 = KTree.node A10K2.t1964 (nat_lit 31028096) (nat_lit 15145072596) (nat_lit 0) A10K2.t1965 from rfl, totK_node, tot1964, tot1965]
  decide +kernel

theorem arows1958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1958 = true := by
  rw [show A10K2.u1958 = KTree.node A10K2.t1966 (nat_lit 31041760) (nat_lit 3993647107) (nat_lit 0) A10K2.t1967 from rfl, allE_node, rows1966, irow1958, rows1967]
  all_goals rfl

theorem atot1958 : totK PA10K2 A10K2.u1958 = [0, 0, 780048416979, 3201264127786, 4101668189974, 1613252791153, 137510119329, 0, 0, 0] := by
  rw [show A10K2.u1958 = KTree.node A10K2.t1966 (nat_lit 31041760) (nat_lit 3993647107) (nat_lit 0) A10K2.t1967 from rfl, totK_node, tot1966, tot1967]
  decide +kernel

theorem arows1962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1962 = true := by
  rw [show A10K2.u1962 = KTree.node A10K2.t1968 (nat_lit 31047155) (nat_lit 8800572675) (nat_lit 0) A10K2.t1969 from rfl, allE_node, rows1968, irow1962, rows1969]
  all_goals rfl

theorem atot1962 : totK PA10K2 A10K2.u1962 = [0, 0, 454334724907, 2276650654582, 3988128670416, 2545412770961, 448027995768, 13576218110, 0, 0] := by
  rw [show A10K2.u1962 = KTree.node A10K2.t1968 (nat_lit 31047155) (nat_lit 8800572675) (nat_lit 0) A10K2.t1969 from rfl, totK_node, tot1968, tot1969]
  decide +kernel

theorem arows1963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1963 = true := by
  rw [show A10K2.u1963 = KTree.node A10K2.t1970 (nat_lit 31059155) (nat_lit 10663384502) (nat_lit 0) A10K2.t1971 from rfl, allE_node, rows1970, irow1963, rows1971]
  all_goals rfl

theorem atot1963 : totK PA10K2 A10K2.u1963 = [0, 296996980728, 1581218027184, 3463575324899, 3460215194686, 1138530016877, 76172042037, 0, 0, 0] := by
  rw [show A10K2.u1963 = KTree.node A10K2.t1970 (nat_lit 31059155) (nat_lit 10663384502) (nat_lit 0) A10K2.t1971 from rfl, totK_node, tot1970, tot1971]
  decide +kernel

theorem arows1965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1965 = true := by
  rw [show A10K2.u1965 = KTree.node A10K2.t1972 (nat_lit 31133591) (nat_lit 14525556150) (nat_lit 0) A10K2.t1973 from rfl, allE_node, rows1972, irow1965, rows1973]
  all_goals rfl

theorem atot1965 : totK PA10K2 A10K2.u1965 = [0, 469130319405, 2336114988983, 3922250375859, 2462715045863, 488509018561, 25140510525, 0, 0, 0] := by
  rw [show A10K2.u1965 = KTree.node A10K2.t1972 (nat_lit 31133591) (nat_lit 14525556150) (nat_lit 0) A10K2.t1973 from rfl, totK_node, tot1972, tot1973]
  decide +kernel

theorem arows1966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1966 = true := by
  rw [show A10K2.u1966 = KTree.node A10K2.t1974 (nat_lit 31140026) (nat_lit 14957480092) (nat_lit 0) A10K2.t1975 from rfl, allE_node, rows1974, irow1966, rows1975]
  all_goals rfl

theorem atot1966 : totK PA10K2 A10K2.u1966 = [0, 729415278239, 3133741090886, 4135341583933, 1719669534703, 158392291440, 0, 0, 0, 0] := by
  rw [show A10K2.u1966 = KTree.node A10K2.t1974 (nat_lit 31140026) (nat_lit 14957480092) (nat_lit 0) A10K2.t1975 from rfl, totK_node, tot1974, tot1975]
  decide +kernel

theorem arows1969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1969 = true := by
  rw [show A10K2.u1969 = KTree.node A10K2.t1976 (nat_lit 31145436) (nat_lit 4552419755) (nat_lit 0) A10K2.t1977 from rfl, allE_node, rows1976, irow1969, rows1977]
  all_goals rfl

theorem atot1969 : totK PA10K2 A10K2.u1969 = [0, 561086773668, 2463326970473, 3827510210538, 2367291622764, 475379840956, 18682938825, 0, 0, 0] := by
  rw [show A10K2.u1969 = KTree.node A10K2.t1976 (nat_lit 31145436) (nat_lit 4552419755) (nat_lit 0) A10K2.t1977 from rfl, totK_node, tot1976, tot1977]
  decide +kernel

theorem arows1970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1970 = true := by
  rw [show A10K2.u1970 = KTree.node A10K2.t1978 (nat_lit 31158387) (nat_lit 5359809791) (nat_lit 0) A10K2.t1979 from rfl, allE_node, rows1978, irow1970, rows1979]
  all_goals rfl

theorem atot1970 : totK PA10K2 A10K2.u1970 = [0, 332208314330, 2053300822549, 4132915623890, 2915048950992, 542002746541, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u1970 = KTree.node A10K2.t1978 (nat_lit 31158387) (nat_lit 5359809791) (nat_lit 0) A10K2.t1979 from rfl, totK_node, tot1978, tot1979]
  decide +kernel

theorem arows1972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1972 = true := by
  rw [show A10K2.u1972 = KTree.node A10K2.t1980 (nat_lit 31162928) (nat_lit 15077602919) (nat_lit 0) A10K2.t1981 from rfl, allE_node, rows1980, irow1972, rows1981]
  all_goals rfl

theorem atot1972 : totK PA10K2 A10K2.u1972 = [0, 0, 991729964312, 3657890077242, 3969961438419, 1210311712113, 81257643656, 0, 0, 0] := by
  rw [show A10K2.u1972 = KTree.node A10K2.t1980 (nat_lit 31162928) (nat_lit 15077602919) (nat_lit 0) A10K2.t1981 from rfl, totK_node, tot1980, tot1981]
  decide +kernel

theorem arows1973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1973 = true := by
  rw [show A10K2.u1973 = KTree.node A10K2.t1982 (nat_lit 31169651) (nat_lit 5656967505) (nat_lit 0) A10K2.t1983 from rfl, allE_node, rows1982, irow1973, rows1983]
  all_goals rfl

theorem atot1973 : totK PA10K2 A10K2.u1973 = [0, 0, 420068636232, 2322784186950, 4119569956786, 2387103669186, 347476446757, 6904928264, 0, 0] := by
  rw [show A10K2.u1973 = KTree.node A10K2.t1982 (nat_lit 31169651) (nat_lit 5656967505) (nat_lit 0) A10K2.t1983 from rfl, totK_node, tot1982, tot1983]
  decide +kernel

theorem arows1979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1979 = true := by
  rw [show A10K2.u1979 = KTree.node A10K2.t1984 (nat_lit 31176114) (nat_lit 14849761924) (nat_lit 0) A10K2.t1985 from rfl, allE_node, rows1984, irow1979, rows1985]
  all_goals rfl

theorem atot1979 : totK PA10K2 A10K2.u1979 = [0, 0, 589318300413, 2666182880668, 4092013087986, 2250185252582, 309897509188, 7047025452, 0, 0] := by
  rw [show A10K2.u1979 = KTree.node A10K2.t1984 (nat_lit 31176114) (nat_lit 14849761924) (nat_lit 0) A10K2.t1985 from rfl, totK_node, tot1984, tot1985]
  decide +kernel

theorem arows1980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1980 = true := by
  rw [show A10K2.u1980 = KTree.node A10K2.t1986 (nat_lit 31190229) (nat_lit 4933041150) (nat_lit 0) A10K2.t1987 from rfl, allE_node, rows1986, irow1980, rows1987]
  all_goals rfl

theorem atot1980 : totK PA10K2 A10K2.u1980 = [0, 0, 611024340025, 2815823661808, 4173092903761, 2041161613328, 241247949953, 6066958478, 0, 0] := by
  rw [show A10K2.u1980 = KTree.node A10K2.t1986 (nat_lit 31190229) (nat_lit 4933041150) (nat_lit 0) A10K2.t1987 from rfl, totK_node, tot1986, tot1987]
  decide +kernel

theorem arows1982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1982 = true := by
  rw [show A10K2.u1982 = KTree.node A10K2.t1988 (nat_lit 31194788) (nat_lit 5146135775) (nat_lit 0) A10K2.t1989 from rfl, allE_node, rows1988, irow1982, rows1989]
  all_goals rfl

theorem atot1982 : totK PA10K2 A10K2.u1982 = [0, 0, 474803355335, 2086947124989, 3633311724527, 2773027155403, 777222328458, 55043167628, 0, 0] := by
  rw [show A10K2.u1982 = KTree.node A10K2.t1988 (nat_lit 31194788) (nat_lit 5146135775) (nat_lit 0) A10K2.t1989 from rfl, totK_node, tot1988, tot1989]
  decide +kernel

theorem arows1983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1983 = true := by
  rw [show A10K2.u1983 = KTree.node A10K2.t1990 (nat_lit 31199336) (nat_lit 12163877487) (nat_lit 0) A10K2.t1991 from rfl, allE_node, rows1990, irow1983, rows1991]
  all_goals rfl

theorem atot1983 : totK PA10K2 A10K2.u1983 = [0, 0, 344472880302, 2127557539165, 3941139173163, 2578581715865, 550903098702, 30780440178, 0, 0] := by
  rw [show A10K2.u1983 = KTree.node A10K2.t1990 (nat_lit 31199336) (nat_lit 12163877487) (nat_lit 0) A10K2.t1991 from rfl, totK_node, tot1990, tot1991]
  decide +kernel

theorem arows1986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1986 = true := by
  rw [show A10K2.u1986 = KTree.node A10K2.t1992 (nat_lit 31213921) (nat_lit 8951841821) (nat_lit 0) A10K2.t1993 from rfl, allE_node, rows1992, irow1986, rows1993]
  all_goals rfl

theorem atot1986 : totK PA10K2 A10K2.u1986 = [0, 0, 769704103279, 3157496713470, 4065709191331, 1605674197408, 141290311716, 0, 0, 0] := by
  rw [show A10K2.u1986 = KTree.node A10K2.t1992 (nat_lit 31213921) (nat_lit 8951841821) (nat_lit 0) A10K2.t1993 from rfl, totK_node, tot1992, tot1993]
  decide +kernel

theorem arows1987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1987 = true := by
  rw [show A10K2.u1987 = KTree.node A10K2.t1994 (nat_lit 31223259) (nat_lit 6673012401) (nat_lit 0) A10K2.t1995 from rfl, allE_node, rows1994, irow1987, rows1995]
  all_goals rfl

theorem atot1987 : totK PA10K2 A10K2.u1987 = [0, 0, 536325474129, 2656403978284, 4271939412246, 2318644447455, 344830681703, 6853348008, 0, 0] := by
  rw [show A10K2.u1987 = KTree.node A10K2.t1994 (nat_lit 31223259) (nat_lit 6673012401) (nat_lit 0) A10K2.t1995 from rfl, totK_node, tot1994, tot1995]
  decide +kernel

theorem arows1989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1989 = true := by
  rw [show A10K2.u1989 = KTree.node A10K2.t1996 (nat_lit 31227918) (nat_lit 14244308590) (nat_lit 0) A10K2.t1997 from rfl, allE_node, rows1996, irow1989, rows1997]
  all_goals rfl

theorem atot1989 : totK PA10K2 A10K2.u1989 = [0, 0, 0, 954520515298, 3619277850895, 3999879005576, 1185568409420, 81073325079, 0, 0] := by
  rw [show A10K2.u1989 = KTree.node A10K2.t1996 (nat_lit 31227918) (nat_lit 14244308590) (nat_lit 0) A10K2.t1997 from rfl, totK_node, tot1996, tot1997]
  decide +kernel

theorem arows1990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1990 = true := by
  rw [show A10K2.u1990 = KTree.node A10K2.t1998 (nat_lit 31232562) (nat_lit 5777373935) (nat_lit 0) A10K2.t1999 from rfl, allE_node, rows1998, irow1990, rows1999]
  all_goals rfl

theorem atot1990 : totK PA10K2 A10K2.u1990 = [0, 0, 0, 574295481900, 2697023610971, 4079756848113, 2095369057042, 302728369852, 7007974415, 0] := by
  rw [show A10K2.u1990 = KTree.node A10K2.t1998 (nat_lit 31232562) (nat_lit 5777373935) (nat_lit 0) A10K2.t1999 from rfl, totK_node, tot1998, tot1999]
  decide +kernel

theorem arows1994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1994 = true := by
  rw [show A10K2.u1994 = KTree.node A10K2.t2000 (nat_lit 31253292) (nat_lit 10528469465) (nat_lit 0) A10K2.t2001 from rfl, allE_node, rows2000, irow1994, rows2001]
  all_goals rfl

theorem atot1994 : totK PA10K2 A10K2.u1994 = [0, 0, 0, 1024271473374, 3829550347986, 4011984960265, 1049835782207, 42646640660, 0, 0] := by
  rw [show A10K2.u1994 = KTree.node A10K2.t2000 (nat_lit 31253292) (nat_lit 10528469465) (nat_lit 0) A10K2.t2001 from rfl, totK_node, tot2000, tot2001]
  decide +kernel

theorem arows1995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1995 = true := by
  rw [show A10K2.u1995 = KTree.node A10K2.t2002 (nat_lit 31271587) (nat_lit 10480732544) (nat_lit 0) A10K2.t2003 from rfl, allE_node, rows2002, irow1995, rows2003]
  all_goals rfl

theorem atot1995 : totK PA10K2 A10K2.u1995 = [0, 0, 780638625629, 3166494299641, 3929188731769, 1648924083598, 336384484006, 37674914273, 0, 0] := by
  rw [show A10K2.u1995 = KTree.node A10K2.t2002 (nat_lit 31271587) (nat_lit 10480732544) (nat_lit 0) A10K2.t2003 from rfl, totK_node, tot2002, tot2003]
  decide +kernel

theorem arows1997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1997 = true := by
  rw [show A10K2.u1997 = KTree.node A10K2.t2004 (nat_lit 31278294) (nat_lit 14055641635) (nat_lit 0) A10K2.t2005 from rfl, allE_node, rows2004, irow1997, rows2005]
  all_goals rfl

theorem atot1997 : totK PA10K2 A10K2.u1997 = [0, 0, 484404536456, 2384027510437, 4026399392196, 2612958046168, 464010653884, 13576218110, 0, 0] := by
  rw [show A10K2.u1997 = KTree.node A10K2.t2004 (nat_lit 31278294) (nat_lit 14055641635) (nat_lit 0) A10K2.t2005 from rfl, totK_node, tot2004, tot2005]
  decide +kernel

theorem arows1998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1998 = true := by
  rw [show A10K2.u1998 = KTree.node A10K2.t2006 (nat_lit 31288773) (nat_lit 2662788558) (nat_lit 0) A10K2.t2007 from rfl, allE_node, rows2006, irow1998, rows2007]
  all_goals rfl

theorem atot1998 : totK PA10K2 A10K2.u1998 = [0, 0, 609252834019, 2791421208986, 4201511114551, 2202287092618, 296381871032, 6279851884, 0, 0] := by
  rw [show A10K2.u1998 = KTree.node A10K2.t2006 (nat_lit 31288773) (nat_lit 2662788558) (nat_lit 0) A10K2.t2007 from rfl, totK_node, tot2006, tot2007]
  decide +kernel

theorem arows2001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2001 = true := by
  rw [show A10K2.u2001 = KTree.node A10K2.t2008 (nat_lit 31302805) (nat_lit 6681160818) (nat_lit 0) A10K2.t2009 from rfl, allE_node, rows2008, irow2001, rows2009]
  all_goals rfl

theorem atot2001 : totK PA10K2 A10K2.u2001 = [0, 0, 0, 1066388543416, 3810762155008, 3987180135126, 1144514946489, 69689103260, 0, 0] := by
  rw [show A10K2.u2001 = KTree.node A10K2.t2008 (nat_lit 31302805) (nat_lit 6681160818) (nat_lit 0) A10K2.t2009 from rfl, totK_node, tot2008, tot2009]
  decide +kernel

theorem arows2002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2002 = true := by
  rw [show A10K2.u2002 = KTree.node A10K2.t2010 (nat_lit 31307932) (nat_lit 11679886158) (nat_lit 0) A10K2.t2011 from rfl, allE_node, rows2010, irow2002, rows2011]
  all_goals rfl

theorem atot2002 : totK PA10K2 A10K2.u2002 = [0, 0, 0, 599325350123, 2815044801020, 4291771161174, 2029717737205, 254101849660, 7151180950, 0] := by
  rw [show A10K2.u2002 = KTree.node A10K2.t2010 (nat_lit 31307932) (nat_lit 11679886158) (nat_lit 0) A10K2.t2011 from rfl, totK_node, tot2010, tot2011]
  decide +kernel

theorem arows2004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2004 = true := by
  rw [show A10K2.u2004 = KTree.node A10K2.t2012 (nat_lit 31321670) (nat_lit 15069347848) (nat_lit 0) A10K2.t2013 from rfl, allE_node, rows2012, irow2004, rows2013]
  all_goals rfl

theorem atot2004 : totK PA10K2 A10K2.u2004 = [0, 0, 409909650706, 1963266634743, 3587361966539, 2954738377236, 907736375622, 62632138461, 0, 0] := by
  rw [show A10K2.u2004 = KTree.node A10K2.t2012 (nat_lit 31321670) (nat_lit 15069347848) (nat_lit 0) A10K2.t2013 from rfl, totK_node, tot2012, tot2013]
  decide +kernel

theorem arows2005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2005 = true := by
  rw [show A10K2.u2005 = KTree.node A10K2.t2014 (nat_lit 31396165) (nat_lit 6222635340) (nat_lit 0) A10K2.t2015 from rfl, allE_node, rows2014, irow2005, rows2015]
  all_goals rfl

theorem atot2005 : totK PA10K2 A10K2.u2005 = [0, 0, 372635303599, 2219143476819, 4147998927504, 2667775597041, 459664671698, 11991740650, 0, 0] := by
  rw [show A10K2.u2005 = KTree.node A10K2.t2014 (nat_lit 31396165) (nat_lit 6222635340) (nat_lit 0) A10K2.t2015 from rfl, totK_node, tot2014, tot2015]
  decide +kernel

theorem arows2010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2010 = true := by
  rw [show A10K2.u2010 = KTree.node A10K2.t2016 (nat_lit 31403236) (nat_lit 9847279019) (nat_lit 0) A10K2.t2017 from rfl, allE_node, rows2016, irow2010, rows2017]
  all_goals rfl

theorem atot2010 : totK PA10K2 A10K2.u2010 = [0, 0, 700926227992, 2953606169545, 3871417044850, 1857526904413, 296897746939, 12219140272, 0, 0] := by
  rw [show A10K2.u2010 = KTree.node A10K2.t2016 (nat_lit 31403236) (nat_lit 9847279019) (nat_lit 0) A10K2.t2017 from rfl, totK_node, tot2016, tot2017]
  decide +kernel

theorem arows2011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2011 = true := by
  rw [show A10K2.u2011 = KTree.node A10K2.t2018 (nat_lit 31416900) (nat_lit 10436837726) (nat_lit 0) A10K2.t2019 from rfl, allE_node, rows2018, irow2011, rows2019]
  all_goals rfl

theorem atot2011 : totK PA10K2 A10K2.u2011 = [0, 0, 845272548503, 3156479243886, 3959847188037, 1792809588591, 170037518940, 0, 0, 0] := by
  rw [show A10K2.u2011 = KTree.node A10K2.t2018 (nat_lit 31416900) (nat_lit 10436837726) (nat_lit 0) A10K2.t2019 from rfl, totK_node, tot2018, tot2019]
  decide +kernel

theorem arows2013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2013 = true := by
  rw [show A10K2.u2013 = KTree.node A10K2.t2020 (nat_lit 31421605) (nat_lit 5559613874) (nat_lit 0) A10K2.t2021 from rfl, allE_node, rows2020, irow2013, rows2021]
  all_goals rfl

theorem atot2013 : totK PA10K2 A10K2.u2013 = [0, 0, 46039240014, 1440060396478, 4219456764875, 3602025399604, 725027903991, 19546091569, 0, 0] := by
  rw [show A10K2.u2013 = KTree.node A10K2.t2020 (nat_lit 31421605) (nat_lit 5559613874) (nat_lit 0) A10K2.t2021 from rfl, totK_node, tot2020, tot2021]
  decide +kernel

theorem arows2014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2014 = true := by
  rw [show A10K2.u2014 = KTree.node A10K2.t2022 (nat_lit 31427372) (nat_lit 11862806193) (nat_lit 0) A10K2.t2023 from rfl, allE_node, rows2022, irow2014, rows2023]
  all_goals rfl

theorem atot2014 : totK PA10K2 A10K2.u2014 = [0, 0, 0, 762198234076, 3121428229619, 4116034428277, 1698324012158, 149895851979, 0, 0] := by
  rw [show A10K2.u2014 = KTree.node A10K2.t2022 (nat_lit 31427372) (nat_lit 11862806193) (nat_lit 0) A10K2.t2023 from rfl, totK_node, tot2022, tot2023]
  decide +kernel

theorem arows2017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2017 = true := by
  rw [show A10K2.u2017 = KTree.node A10K2.t2024 (nat_lit 31434416) (nat_lit 9594373260) (nat_lit 0) A10K2.t2025 from rfl, allE_node, rows2024, irow2017, rows2025]
  all_goals rfl

theorem atot2017 : totK PA10K2 A10K2.u2017 = [0, 0, 0, 725721388566, 3076654130301, 4068021457787, 1716789998400, 203028699907, 6318667960, 0] := by
  rw [show A10K2.u2017 = KTree.node A10K2.t2024 (nat_lit 31434416) (nat_lit 9594373260) (nat_lit 0) A10K2.t2025 from rfl, totK_node, tot2024, tot2025]
  decide +kernel

theorem arows2018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2018 = true := by
  rw [show A10K2.u2018 = KTree.node A10K2.t2026 (nat_lit 31449138) (nat_lit 10491640441) (nat_lit 0) A10K2.t2027 from rfl, allE_node, rows2026, irow2018, rows2027]
  all_goals rfl

theorem atot2018 : totK PA10K2 A10K2.u2018 = [0, 0, 0, 555507056115, 2698321040015, 4062499220233, 2134014096073, 286492903526, 6439430839, 0] := by
  rw [show A10K2.u2018 = KTree.node A10K2.t2026 (nat_lit 31449138) (nat_lit 10491640441) (nat_lit 0) A10K2.t2027 from rfl, totK_node, tot2026, tot2027]
  decide +kernel

theorem arows2020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2020 = true := by
  rw [show A10K2.u2020 = KTree.node A10K2.t2028 (nat_lit 31453644) (nat_lit 5508607251) (nat_lit 0) A10K2.t2029 from rfl, allE_node, rows2028, irow2020, rows2029]
  all_goals rfl

theorem atot2020 : totK PA10K2 A10K2.u2020 = [0, 0, 0, 328627686157, 2120139578545, 4152166945457, 2746439928251, 459971349271, 12132367858, 0] := by
  rw [show A10K2.u2020 = KTree.node A10K2.t2028 (nat_lit 31453644) (nat_lit 5508607251) (nat_lit 0) A10K2.t2029 from rfl, totK_node, tot2028, tot2029]
  decide +kernel

theorem arows2021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2021 = true := by
  rw [show A10K2.u2021 = KTree.node A10K2.t2030 (nat_lit 38348680) (nat_lit 8653665151) (nat_lit 0) A10K2.t2031 from rfl, allE_node, rows2030, irow2021, rows2031]
  all_goals rfl

theorem atot2021 : totK PA10K2 A10K2.u2021 = [876250713213, 3080719290227, 3045804694393, 788833028163, 37497888367, 447704699636, 1025234692155, 501217979401, 48886019071, 0] := by
  rw [show A10K2.u2021 = KTree.node A10K2.t2030 (nat_lit 38348680) (nat_lit 8653665151) (nat_lit 0) A10K2.t2031 from rfl, totK_node, tot2030, tot2031]
  decide +kernel

theorem arows2025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2025 = true := by
  rw [show A10K2.u2025 = KTree.node A10K2.t2032 (nat_lit 38353152) (nat_lit 9882099843) (nat_lit 0) A10K2.t2033 from rfl, allE_node, rows2032, irow2025, rows2033]
  all_goals rfl

theorem atot2025 : totK PA10K2 A10K2.u2025 = [175253966261, 1536055015494, 3958426344983, 3171900775687, 657072223155, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2025 = KTree.node A10K2.t2032 (nat_lit 38353152) (nat_lit 9882099843) (nat_lit 0) A10K2.t2033 from rfl, totK_node, tot2032, tot2033]
  decide +kernel

theorem arows2026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2026 = true := by
  rw [show A10K2.u2026 = KTree.node A10K2.t2034 (nat_lit 38357666) (nat_lit 13905161396) (nat_lit 0) A10K2.t2035 from rfl, allE_node, rows2034, irow2026, rows2035]
  all_goals rfl

theorem atot2026 : totK PA10K2 A10K2.u2026 = [533655686777, 2803024014134, 4148231162965, 1779016559829, 152417435608, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2026 = KTree.node A10K2.t2034 (nat_lit 38357666) (nat_lit 13905161396) (nat_lit 0) A10K2.t2035 from rfl, totK_node, tot2034, tot2035]
  decide +kernel

theorem arows2028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2028 = true := by
  rw [show A10K2.u2028 = KTree.node A10K2.t2036 (nat_lit 38365024) (nat_lit 7325391894) (nat_lit 0) A10K2.t2037 from rfl, allE_node, rows2036, irow2028, rows2037]
  all_goals rfl

theorem atot2028 : totK PA10K2 A10K2.u2028 = [785223503628, 3065051215461, 3998884027519, 1935659635268, 299607952134, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2028 = KTree.node A10K2.t2036 (nat_lit 38365024) (nat_lit 7325391894) (nat_lit 0) A10K2.t2037 from rfl, totK_node, tot2036, tot2037]
  decide +kernel

theorem arows2029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2029 = true := by
  rw [show A10K2.u2029 = KTree.node A10K2.t2038 (nat_lit 38370865) (nat_lit 8809347695) (nat_lit 0) A10K2.t2039 from rfl, allE_node, rows2038, irow2029, rows2039]
  all_goals rfl

theorem atot2029 : totK PA10K2 A10K2.u2029 = [0, 982714712232, 3644079631323, 3944969351958, 1247191873561, 87913305165, 0, 0, 0, 0] := by
  rw [show A10K2.u2029 = KTree.node A10K2.t2038 (nat_lit 38370865) (nat_lit 8809347695) (nat_lit 0) A10K2.t2039 from rfl, totK_node, tot2038, tot2039]
  decide +kernel

theorem arows2032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2032 = true := by
  rw [show A10K2.u2032 = KTree.node A10K2.t2040 (nat_lit 38383558) (nat_lit 15139994962) (nat_lit 0) A10K2.t2041 from rfl, allE_node, rows2040, irow2032, rows2041]
  all_goals rfl

theorem atot2032 : totK PA10K2 A10K2.u2032 = [0, 499887713090, 2454398486209, 4005258275704, 2210676192185, 416284441717, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u2032 = KTree.node A10K2.t2040 (nat_lit 38383558) (nat_lit 15139994962) (nat_lit 0) A10K2.t2041 from rfl, totK_node, tot2040, tot2041]
  decide +kernel

theorem arows2033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2033 = true := by
  rw [show A10K2.u2033 = KTree.node A10K2.t2042 (nat_lit 38389176) (nat_lit 9714651210) (nat_lit 0) A10K2.t2043 from rfl, allE_node, rows2042, irow2033, rows2043]
  all_goals rfl

theorem atot2033 : totK PA10K2 A10K2.u2033 = [0, 722374899439, 3057998452168, 3791581450281, 1582953670898, 205297305071, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u2033 = KTree.node A10K2.t2042 (nat_lit 38389176) (nat_lit 9714651210) (nat_lit 0) A10K2.t2043 from rfl, totK_node, tot2042, tot2043]
  decide +kernel

theorem arows2035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2035 = true := by
  rw [show A10K2.u2035 = KTree.node A10K2.t2044 (nat_lit 38396339) (nat_lit 8194008132) (nat_lit 0) A10K2.t2045 from rfl, allE_node, rows2044, irow2035, rows2045]
  all_goals rfl

theorem atot2035 : totK PA10K2 A10K2.u2035 = [0, 663374983978, 2788359673580, 4024460198390, 1912451099668, 239038658697, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2035 = KTree.node A10K2.t2044 (nat_lit 38396339) (nat_lit 8194008132) (nat_lit 0) A10K2.t2045 from rfl, totK_node, tot2044, tot2045]
  decide +kernel

theorem arows2036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2036 = true := by
  rw [show A10K2.u2036 = KTree.node A10K2.t2046 (nat_lit 38406309) (nat_lit 7321820484) (nat_lit 0) A10K2.t2047 from rfl, allE_node, rows2046, irow2036, rows2047]
  all_goals rfl

theorem atot2036 : totK PA10K2 A10K2.u2036 = [424355675811, 2072769148557, 3424741320685, 2470379218129, 832415690963, 75682887341, 0, 0, 0, 0] := by
  rw [show A10K2.u2036 = KTree.node A10K2.t2046 (nat_lit 38406309) (nat_lit 7321820484) (nat_lit 0) A10K2.t2047 from rfl, totK_node, tot2046, tot2047]
  decide +kernel

theorem arows2047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2047 = true := by
  rw [show A10K2.u2047 = KTree.node A10K2.t2048 (nat_lit 38414526) (nat_lit 13001525521) (nat_lit 0) A10K2.t2049 from rfl, allE_node, rows2048, irow2047, rows2049]
  all_goals rfl

theorem atot2047 : totK PA10K2 A10K2.u2047 = [803828201493, 3107580690597, 3900684105112, 1762132544398, 231429081983, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u2047 = KTree.node A10K2.t2048 (nat_lit 38414526) (nat_lit 13001525521) (nat_lit 0) A10K2.t2049 from rfl, totK_node, tot2048, tot2049]
  decide +kernel

theorem arows2048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2048 = true := by
  rw [show A10K2.u2048 = KTree.node A10K2.t2050 (nat_lit 38419621) (nat_lit 6412468723) (nat_lit 0) A10K2.t2051 from rfl, allE_node, rows2050, irow2048, rows2051]
  all_goals rfl

theorem atot2048 : totK PA10K2 A10K2.u2048 = [476246592928, 2119385657843, 3615116608313, 2639067367350, 588319400774, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2048 = KTree.node A10K2.t2050 (nat_lit 38419621) (nat_lit 6412468723) (nat_lit 0) A10K2.t2051 from rfl, totK_node, tot2050, tot2051]
  decide +kernel

theorem arows2050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2050 = true := by
  rw [show A10K2.u2050 = KTree.node A10K2.t2052 (nat_lit 38424896) (nat_lit 14662692861) (nat_lit 0) A10K2.t2053 from rfl, allE_node, rows2052, irow2050, rows2053]
  all_goals rfl

theorem atot2050 : totK PA10K2 A10K2.u2050 = [298263154340, 2164110921947, 4172611215727, 2308941719616, 322523913193, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2050 = KTree.node A10K2.t2052 (nat_lit 38424896) (nat_lit 14662692861) (nat_lit 0) A10K2.t2053 from rfl, totK_node, tot2052, tot2053]
  decide +kernel

theorem arows2051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2051 = true := by
  rw [show A10K2.u2051 = KTree.node A10K2.t2054 (nat_lit 38446376) (nat_lit 9663837485) (nat_lit 0) A10K2.t2055 from rfl, allE_node, rows2054, irow2051, rows2055]
  all_goals rfl

theorem atot2051 : totK PA10K2 A10K2.u2051 = [0, 1000121128547, 3578074008612, 3722762593891, 1043904503980, 64458820912, 0, 0, 0, 0] := by
  rw [show A10K2.u2051 = KTree.node A10K2.t2054 (nat_lit 38446376) (nat_lit 9663837485) (nat_lit 0) A10K2.t2055 from rfl, totK_node, tot2054, tot2055]
  decide +kernel

theorem arows2054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2054 = true := by
  rw [show A10K2.u2054 = KTree.node A10K2.t2056 (nat_lit 38454555) (nat_lit 10025055015) (nat_lit 0) A10K2.t2057 from rfl, allE_node, rows2056, irow2054, rows2057]
  all_goals rfl

theorem atot2054 : totK PA10K2 A10K2.u2054 = [0, 921233463613, 3540775717970, 3829851560066, 1040343571740, 63496944544, 0, 0, 0, 0] := by
  rw [show A10K2.u2054 = KTree.node A10K2.t2056 (nat_lit 38454555) (nat_lit 10025055015) (nat_lit 0) A10K2.t2057 from rfl, totK_node, tot2056, tot2057]
  decide +kernel

theorem arows2055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2055 = true := by
  rw [show A10K2.u2055 = KTree.node A10K2.t2058 (nat_lit 38460266) (nat_lit 8930862375) (nat_lit 0) A10K2.t2059 from rfl, allE_node, rows2058, irow2055, rows2059]
  all_goals rfl

theorem atot2055 : totK PA10K2 A10K2.u2055 = [476537513919, 1782589394850, 2744541086347, 2852614835321, 1504534913450, 259417048368, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2055 = KTree.node A10K2.t2058 (nat_lit 38460266) (nat_lit 8930862375) (nat_lit 0) A10K2.t2059 from rfl, totK_node, tot2058, tot2059]
  decide +kernel

theorem arows2057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2057 = true := by
  rw [show A10K2.u2057 = KTree.node A10K2.t2060 (nat_lit 38479517) (nat_lit 6032514964) (nat_lit 0) A10K2.t2061 from rfl, allE_node, rows2060, irow2057, rows2061]
  all_goals rfl

theorem atot2057 : totK PA10K2 A10K2.u2057 = [817218475588, 3179330400021, 4011698777855, 1779655845692, 258247959780, 14423867395, 0, 0, 0, 0] := by
  rw [show A10K2.u2057 = KTree.node A10K2.t2060 (nat_lit 38479517) (nat_lit 6032514964) (nat_lit 0) A10K2.t2061 from rfl, totK_node, tot2060, tot2061]
  decide +kernel

theorem arows2058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2058 = true := by
  rw [show A10K2.u2058 = KTree.node A10K2.t2062 (nat_lit 38484200) (nat_lit 6144531408) (nat_lit 0) A10K2.t2063 from rfl, allE_node, rows2062, irow2058, rows2063]
  all_goals rfl

theorem atot2058 : totK PA10K2 A10K2.u2058 = [223542980710, 1796073361622, 4085047101446, 3070814871938, 633395184838, 31747192500, 0, 0, 0, 0] := by
  rw [show A10K2.u2058 = KTree.node A10K2.t2062 (nat_lit 38484200) (nat_lit 6144531408) (nat_lit 0) A10K2.t2063 from rfl, totK_node, tot2062, tot2063]
  decide +kernel

theorem arows2062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2062 = true := by
  rw [show A10K2.u2062 = KTree.node A10K2.t2064 (nat_lit 38497796) (nat_lit 6809414763) (nat_lit 0) A10K2.t2065 from rfl, allE_node, rows2064, irow2062, rows2065]
  all_goals rfl

theorem atot2062 : totK PA10K2 A10K2.u2062 = [613328696870, 2818738080237, 4153673586634, 2100991138203, 297294343891, 6853348008, 0, 0, 0, 0] := by
  rw [show A10K2.u2062 = KTree.node A10K2.t2064 (nat_lit 38497796) (nat_lit 6809414763) (nat_lit 0) A10K2.t2065 from rfl, totK_node, tot2064, tot2065]
  decide +kernel

theorem arows2063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2063 = true := by
  rw [show A10K2.u2063 = KTree.node A10K2.t2066 (nat_lit 38502412) (nat_lit 9135145093) (nat_lit 0) A10K2.t2067 from rfl, allE_node, rows2066, irow2063, rows2067]
  all_goals rfl

theorem atot2063 : totK PA10K2 A10K2.u2063 = [0, 842490507131, 3467524787672, 4228547762687, 1503953553075, 121120850252, 0, 0, 0, 0] := by
  rw [show A10K2.u2063 = KTree.node A10K2.t2066 (nat_lit 38502412) (nat_lit 9135145093) (nat_lit 0) A10K2.t2067 from rfl, totK_node, tot2066, tot2067]
  decide +kernel

theorem arows2065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2065 = true := by
  rw [show A10K2.u2065 = KTree.node A10K2.t2068 (nat_lit 38512304) (nat_lit 9594373260) (nat_lit 0) A10K2.t2069 from rfl, allE_node, rows2068, irow2065, rows2069]
  all_goals rfl

theorem atot2065 : totK PA10K2 A10K2.u2065 = [0, 817074536471, 3160105158019, 3989775149486, 1766366678868, 254546565892, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u2065 = KTree.node A10K2.t2068 (nat_lit 38512304) (nat_lit 9594373260) (nat_lit 0) A10K2.t2069 from rfl, totK_node, tot2068, tot2069]
  decide +kernel

theorem arows2066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2066 = true := by
  rw [show A10K2.u2066 = KTree.node A10K2.t2070 (nat_lit 38517809) (nat_lit 8575554911) (nat_lit 0) A10K2.t2071 from rfl, allE_node, rows2070, irow2066, rows2071]
  all_goals rfl

theorem atot2066 : totK PA10K2 A10K2.u2066 = [0, 512905690969, 2503779550487, 4119411034387, 2402515350708, 343972081642, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u2066 = KTree.node A10K2.t2070 (nat_lit 38517809) (nat_lit 8575554911) (nat_lit 0) A10K2.t2071 from rfl, totK_node, tot2070, tot2071]
  decide +kernel

theorem arows2069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2069 = true := by
  rw [show A10K2.u2069 = KTree.node A10K2.t2072 (nat_lit 38531056) (nat_lit 13422220158) (nat_lit 0) A10K2.t2073 from rfl, allE_node, rows2072, irow2069, rows2073]
  all_goals rfl

theorem atot2069 : totK PA10K2 A10K2.u2069 = [0, 323255249417, 2189521856132, 4241613495312, 2666696541405, 451417863891, 12224107035, 0, 0, 0] := by
  rw [show A10K2.u2069 = KTree.node A10K2.t2072 (nat_lit 38531056) (nat_lit 13422220158) (nat_lit 0) A10K2.t2073 from rfl, totK_node, tot2072, tot2073]
  decide +kernel

theorem arows2070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2070 = true := by
  rw [show A10K2.u2070 = KTree.node A10K2.t2074 (nat_lit 38610583) (nat_lit 13383187762) (nat_lit 0) A10K2.t2075 from rfl, allE_node, rows2074, irow2070, rows2075]
  all_goals rfl

theorem atot2070 : totK PA10K2 A10K2.u2070 = [0, 829038191732, 2903227155840, 3483971074910, 1920692125247, 553926716059, 48886019071, 0, 0, 0] := by
  rw [show A10K2.u2070 = KTree.node A10K2.t2074 (nat_lit 38610583) (nat_lit 13383187762) (nat_lit 0) A10K2.t2075 from rfl, totK_node, tot2074, tot2075]
  decide +kernel

theorem arows2072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2072 = true := by
  rw [show A10K2.u2072 = KTree.node A10K2.t2076 (nat_lit 38614935) (nat_lit 13738972102) (nat_lit 0) A10K2.t2077 from rfl, allE_node, rows2076, irow2072, rows2077]
  all_goals rfl

theorem atot2072 : totK PA10K2 A10K2.u2072 = [0, 191671050156, 1733620219472, 4027776277568, 3052292817026, 620688589921, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2072 = KTree.node A10K2.t2076 (nat_lit 38614935) (nat_lit 13738972102) (nat_lit 0) A10K2.t2077 from rfl, totK_node, tot2076, tot2077]
  decide +kernel

theorem arows2073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2073 = true := by
  rw [show A10K2.u2073 = KTree.node A10K2.t2078 (nat_lit 38619415) (nat_lit 8055579516) (nat_lit 0) A10K2.t2079 from rfl, allE_node, rows2078, irow2073, rows2079]
  all_goals rfl

theorem atot2073 : totK PA10K2 A10K2.u2073 = [0, 575382584799, 2896456429602, 4168429948066, 1609954568362, 109831023369, 0, 0, 0, 0] := by
  rw [show A10K2.u2073 = KTree.node A10K2.t2078 (nat_lit 38619415) (nat_lit 8055579516) (nat_lit 0) A10K2.t2079 from rfl, totK_node, tot2078, tot2079]
  decide +kernel

theorem arows2078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2078 = true := by
  rw [show A10K2.u2078 = KTree.node A10K2.t2080 (nat_lit 38626993) (nat_lit 5116158706) (nat_lit 0) A10K2.t2081 from rfl, allE_node, rows2080, irow2078, rows2081]
  all_goals rfl

theorem atot2078 : totK PA10K2 A10K2.u2078 = [0, 784301050123, 3092783097309, 4019321582332, 1802083624195, 230834178417, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u2078 = KTree.node A10K2.t2080 (nat_lit 38626993) (nat_lit 5116158706) (nat_lit 0) A10K2.t2081 from rfl, totK_node, tot2080, tot2081]
  decide +kernel

theorem arows2079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2079 = true := by
  rw [show A10K2.u2079 = KTree.node A10K2.t2082 (nat_lit 38632903) (nat_lit 14488173040) (nat_lit 0) A10K2.t2083 from rfl, allE_node, rows2082, irow2079, rows2083]
  all_goals rfl

theorem atot2079 : totK PA10K2 A10K2.u2079 = [0, 0, 967808445883, 3732240963854, 4041557874782, 1143952255883, 67541609336, 0, 0, 0] := by
  rw [show A10K2.u2079 = KTree.node A10K2.t2082 (nat_lit 38632903) (nat_lit 14488173040) (nat_lit 0) A10K2.t2083 from rfl, totK_node, tot2082, tot2083]
  decide +kernel

theorem arows2081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2081 = true := by
  rw [show A10K2.u2081 = KTree.node A10K2.t2084 (nat_lit 38645695) (nat_lit 14089511519) (nat_lit 0) A10K2.t2085 from rfl, allE_node, rows2084, irow2081, rows2085]
  all_goals rfl

theorem atot2081 : totK PA10K2 A10K2.u2081 = [0, 0, 546278226073, 2521604565692, 3827082318819, 2105668735332, 418917722352, 25565504801, 0, 0] := by
  rw [show A10K2.u2081 = KTree.node A10K2.t2084 (nat_lit 38645695) (nat_lit 14089511519) (nat_lit 0) A10K2.t2085 from rfl, totK_node, tot2084, tot2085]
  decide +kernel

theorem arows2082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2082 = true := by
  rw [show A10K2.u2082 = KTree.node A10K2.t2086 (nat_lit 38651376) (nat_lit 6860957455) (nat_lit 0) A10K2.t2087 from rfl, allE_node, rows2086, irow2082, rows2087]
  all_goals rfl

theorem atot2082 : totK PA10K2 A10K2.u2082 = [0, 0, 715817143954, 3058098187673, 3788694945627, 1450525004599, 186290793500, 5453062850, 0, 0] := by
  rw [show A10K2.u2082 = KTree.node A10K2.t2086 (nat_lit 38651376) (nat_lit 6860957455) (nat_lit 0) A10K2.t2087 from rfl, totK_node, tot2086, tot2087]
  decide +kernel

theorem arows2085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2085 = true := by
  rw [show A10K2.u2085 = KTree.node A10K2.t2088 (nat_lit 38659254) (nat_lit 16118998823) (nat_lit 0) A10K2.t2089 from rfl, allE_node, rows2088, irow2085, rows2089]
  all_goals rfl

theorem atot2085 : totK PA10K2 A10K2.u2085 = [0, 0, 780524279054, 3037062272970, 3921744332979, 1725140777848, 214920901947, 5685526223, 0, 0] := by
  rw [show A10K2.u2085 = KTree.node A10K2.t2088 (nat_lit 38659254) (nat_lit 16118998823) (nat_lit 0) A10K2.t2089 from rfl, totK_node, tot2088, tot2089]
  decide +kernel

theorem arows2086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2086 = true := by
  rw [show A10K2.u2086 = KTree.node A10K2.t2090 (nat_lit 38670340) (nat_lit 12127902057) (nat_lit 0) A10K2.t2091 from rfl, allE_node, rows2090, irow2086, rows2091]
  all_goals rfl

theorem atot2086 : totK PA10K2 A10K2.u2086 = [0, 733773351599, 2779005003471, 3519603363509, 1814417992545, 386204378150, 29875833331, 0, 0, 0] := by
  rw [show A10K2.u2086 = KTree.node A10K2.t2090 (nat_lit 38670340) (nat_lit 12127902057) (nat_lit 0) A10K2.t2091 from rfl, totK_node, tot2090, tot2091]
  decide +kernel

theorem arows2088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2088 = true := by
  rw [show A10K2.u2088 = KTree.node A10K2.t2092 (nat_lit 38677960) (nat_lit 5877248018) (nat_lit 0) A10K2.t2093 from rfl, allE_node, rows2092, irow2088, rows2093]
  all_goals rfl

theorem atot2088 : totK PA10K2 A10K2.u2088 = [0, 494410525705, 2559762870485, 4083145900076, 2213380484654, 417368768387, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u2088 = KTree.node A10K2.t2092 (nat_lit 38677960) (nat_lit 5877248018) (nat_lit 0) A10K2.t2093 from rfl, totK_node, tot2092, tot2093]
  decide +kernel

theorem arows2089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2089 = true := by
  rw [show A10K2.u2089 = KTree.node A10K2.t2094 (nat_lit 38683399) (nat_lit 6174495171) (nat_lit 0) A10K2.t2095 from rfl, allE_node, rows2094, irow2089, rows2095]
  all_goals rfl

theorem atot2089 : totK PA10K2 A10K2.u2089 = [0, 774509747268, 2842883533655, 3600107133393, 1891293129643, 271754004698, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u2089 = KTree.node A10K2.t2094 (nat_lit 38683399) (nat_lit 6174495171) (nat_lit 0) A10K2.t2095 from rfl, totK_node, tot2094, tot2095]
  decide +kernel

theorem arows2093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2093 = true := by
  rw [show A10K2.u2093 = KTree.node A10K2.t2096 (nat_lit 38689000) (nat_lit 7217163367) (nat_lit 0) A10K2.t2097 from rfl, allE_node, rows2096, irow2093, rows2097]
  all_goals rfl

theorem atot2093 : totK PA10K2 A10K2.u2093 = [0, 0, 1513154103581, 4234400708427, 2859161165056, 469320717649, 11740475125, 0, 0, 0] := by
  rw [show A10K2.u2093 = KTree.node A10K2.t2096 (nat_lit 38689000) (nat_lit 7217163367) (nat_lit 0) A10K2.t2097 from rfl, totK_node, tot2096, tot2097]
  decide +kernel

theorem arows2094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2094 = true := by
  rw [show A10K2.u2094 = KTree.node A10K2.t2098 (nat_lit 38709510) (nat_lit 3188216863) (nat_lit 0) A10K2.t2099 from rfl, allE_node, rows2098, irow2094, rows2099]
  all_goals rfl

theorem atot2094 : totK PA10K2 A10K2.u2094 = [0, 0, 995486728553, 3716369525503, 3834069960314, 916942567667, 45352262510, 0, 0, 0] := by
  rw [show A10K2.u2094 = KTree.node A10K2.t2098 (nat_lit 38709510) (nat_lit 3188216863) (nat_lit 0) A10K2.t2099 from rfl, totK_node, tot2098, tot2099]
  decide +kernel

theorem arows2096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2096 = true := by
  rw [show A10K2.u2096 = KTree.node A10K2.t2100 (nat_lit 38717795) (nat_lit 9260894841) (nat_lit 0) A10K2.t2101 from rfl, allE_node, rows2100, irow2096, rows2101]
  all_goals rfl

theorem atot2096 : totK PA10K2 A10K2.u2096 = [0, 0, 574550352975, 2951922492350, 4164334887531, 1398716652581, 100662997981, 0, 0, 0] := by
  rw [show A10K2.u2096 = KTree.node A10K2.t2100 (nat_lit 38717795) (nat_lit 9260894841) (nat_lit 0) A10K2.t2101 from rfl, totK_node, tot2100, tot2101]
  decide +kernel

theorem arows2097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2097 = true := by
  rw [show A10K2.u2097 = KTree.node A10K2.t2102 (nat_lit 38735478) (nat_lit 16090012373) (nat_lit 0) A10K2.t2103 from rfl, allE_node, rows2102, irow2097, rows2103]
  all_goals rfl

theorem atot2097 : totK PA10K2 A10K2.u2097 = [0, 603357570004, 2540942148037, 3660666052008, 2225681325520, 828118811729, 151947803034, 6239673734, 0, 0] := by
  rw [show A10K2.u2097 = KTree.node A10K2.t2102 (nat_lit 38735478) (nat_lit 16090012373) (nat_lit 0) A10K2.t2103 from rfl, totK_node, tot2102, tot2103]
  decide +kernel

theorem arows2100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2100 = true := by
  rw [show A10K2.u2100 = KTree.node A10K2.t2104 (nat_lit 38743225) (nat_lit 5721428334) (nat_lit 0) A10K2.t2105 from rfl, allE_node, rows2104, irow2100, rows2105]
  all_goals rfl

theorem atot2100 : totK PA10K2 A10K2.u2100 = [0, 687295360416, 2976146033385, 4052768954787, 1893864318991, 306511869228, 20328650499, 0, 0, 0] := by
  rw [show A10K2.u2100 = KTree.node A10K2.t2104 (nat_lit 38743225) (nat_lit 5721428334) (nat_lit 0) A10K2.t2105 from rfl, totK_node, tot2104, tot2105]
  decide +kernel

theorem arows2101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2101 = true := by
  rw [show A10K2.u2101 = KTree.node A10K2.t2106 (nat_lit 38756763) (nat_lit 8811260245) (nat_lit 0) A10K2.t2107 from rfl, allE_node, rows2106, irow2101, rows2107]
  all_goals rfl

theorem atot2101 : totK PA10K2 A10K2.u2101 = [0, 670212589725, 2746689587579, 3870278828675, 2154709422552, 373416046804, 10956717587, 0, 0, 0] := by
  rw [show A10K2.u2101 = KTree.node A10K2.t2106 (nat_lit 38756763) (nat_lit 8811260245) (nat_lit 0) A10K2.t2107 from rfl, totK_node, tot2106, tot2107]
  decide +kernel

theorem arows2103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2103 = true := by
  rw [show A10K2.u2103 = KTree.node A10K2.t2108 (nat_lit 38761621) (nat_lit 5999753819) (nat_lit 0) A10K2.t2109 from rfl, allE_node, rows2108, irow2103, rows2109]
  all_goals rfl

theorem atot2103 : totK PA10K2 A10K2.u2103 = [0, 165736271258, 1663452970556, 4144461842029, 3325307415692, 678204946961, 19094568524, 0, 0, 0] := by
  rw [show A10K2.u2103 = KTree.node A10K2.t2108 (nat_lit 38761621) (nat_lit 5999753819) (nat_lit 0) A10K2.t2109 from rfl, totK_node, tot2108, tot2109]
  decide +kernel

theorem arows2104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2104 = true := by
  rw [show A10K2.u2104 = KTree.node A10K2.t2110 (nat_lit 38799624) (nat_lit 13716224831) (nat_lit 0) A10K2.t2111 from rfl, allE_node, rows2110, irow2104, rows2111]
  all_goals rfl

theorem atot2104 : totK PA10K2 A10K2.u2104 = [560981842138, 2432438447327, 3410791211182, 1988927165786, 868587145924, 362475617594, 43287591117, 0, 0, 0] := by
  rw [show A10K2.u2104 = KTree.node A10K2.t2110 (nat_lit 38799624) (nat_lit 13716224831) (nat_lit 0) A10K2.t2111 from rfl, totK_node, tot2110, tot2111]
  decide +kernel

theorem arows2110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2110 = true := by
  rw [show A10K2.u2110 = KTree.node A10K2.t2112 (nat_lit 38814956) (nat_lit 11787121870) (nat_lit 0) A10K2.t2113 from rfl, allE_node, rows2112, irow2110, rows2113]
  all_goals rfl

theorem atot2110 : totK PA10K2 A10K2.u2110 = [738817371650, 2949479863883, 3791368047678, 1721976493213, 220470125417, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u2110 = KTree.node A10K2.t2112 (nat_lit 38814956) (nat_lit 11787121870) (nat_lit 0) A10K2.t2113 from rfl, totK_node, tot2112, tot2113]
  decide +kernel

theorem arows2111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2111 = true := by
  rw [show A10K2.u2111 = KTree.node A10K2.t2114 (nat_lit 38830156) (nat_lit 10804632683) (nat_lit 0) A10K2.t2115 from rfl, allE_node, rows2114, irow2111, rows2115]
  all_goals rfl

theorem atot2111 : totK PA10K2 A10K2.u2111 = [0, 1189398127796, 3971719463609, 3488378809151, 774811800914, 37576894105, 0, 0, 0, 0] := by
  rw [show A10K2.u2111 = KTree.node A10K2.t2114 (nat_lit 38830156) (nat_lit 10804632683) (nat_lit 0) A10K2.t2115 from rfl, totK_node, tot2114, tot2115]
  decide +kernel

theorem arows2113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2113 = true := by
  rw [show A10K2.u2113 = KTree.node A10K2.t2116 (nat_lit 38837015) (nat_lit 680262868) (nat_lit 0) A10K2.t2117 from rfl, allE_node, rows2116, irow2113, rows2117]
  all_goals rfl

theorem atot2113 : totK PA10K2 A10K2.u2113 = [0, 522579977342, 2244344853847, 3675494593106, 2329891630842, 520125404644, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u2113 = KTree.node A10K2.t2116 (nat_lit 38837015) (nat_lit 680262868) (nat_lit 0) A10K2.t2117 from rfl, totK_node, tot2116, tot2117]
  decide +kernel

theorem arows2114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2114 = true := by
  rw [show A10K2.u2114 = KTree.node A10K2.t2118 (nat_lit 38852663) (nat_lit 4012119998) (nat_lit 0) A10K2.t2119 from rfl, allE_node, rows2118, irow2114, rows2119]
  all_goals rfl

theorem atot2114 : totK PA10K2 A10K2.u2114 = [316846731414, 1273228238483, 2691168587274, 3324364186480, 1551079002651, 199083392831, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u2114 = KTree.node A10K2.t2118 (nat_lit 38852663) (nat_lit 4012119998) (nat_lit 0) A10K2.t2119 from rfl, totK_node, tot2118, tot2119]
  decide +kernel

theorem arows2117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2117 = true := by
  rw [show A10K2.u2117 = KTree.node A10K2.t2120 (nat_lit 38874834) (nat_lit 15347524877) (nat_lit 0) A10K2.t2121 from rfl, allE_node, rows2120, irow2117, rows2121]
  all_goals rfl

theorem atot2117 : totK PA10K2 A10K2.u2117 = [527310909255, 2540368131233, 3949668820015, 2252991182138, 431676513418, 25734533292, 0, 0, 0, 0] := by
  rw [show A10K2.u2117 = KTree.node A10K2.t2120 (nat_lit 38874834) (nat_lit 15347524877) (nat_lit 0) A10K2.t2121 from rfl, totK_node, tot2120, tot2121]
  decide +kernel

theorem arows2118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2118 = true := by
  rw [show A10K2.u2118 = KTree.node A10K2.t2122 (nat_lit 38880404) (nat_lit 12505876131) (nat_lit 0) A10K2.t2123 from rfl, allE_node, rows2122, irow2118, rows2123]
  all_goals rfl

theorem atot2118 : totK PA10K2 A10K2.u2118 = [760368498474, 2924864130750, 3716189047257, 1828713548912, 259210729695, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u2118 = KTree.node A10K2.t2122 (nat_lit 38880404) (nat_lit 12505876131) (nat_lit 0) A10K2.t2123 from rfl, totK_node, tot2122, tot2123]
  decide +kernel

theorem arows2120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2120 = true := by
  rw [show A10K2.u2120 = KTree.node A10K2.t2124 (nat_lit 38885894) (nat_lit 7177912599) (nat_lit 0) A10K2.t2125 from rfl, allE_node, rows2124, irow2120, rows2125]
  all_goals rfl

theorem atot2120 : totK PA10K2 A10K2.u2120 = [507908548294, 2531627063775, 4140755389186, 2169634414594, 301874974759, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2120 = KTree.node A10K2.t2124 (nat_lit 38885894) (nat_lit 7177912599) (nat_lit 0) A10K2.t2125 from rfl, totK_node, tot2124, tot2125]
  decide +kernel

theorem arows2121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2121 = true := by
  rw [show A10K2.u2121 = KTree.node A10K2.t2126 (nat_lit 38894654) (nat_lit 16101479194) (nat_lit 0) A10K2.t2127 from rfl, allE_node, rows2126, irow2121, rows2127]
  all_goals rfl

theorem atot2121 : totK PA10K2 A10K2.u2121 = [84375141745, 1458892288122, 4127104664530, 3521506391409, 881078465243, 55240978033, 0, 0, 0, 0] := by
  rw [show A10K2.u2121 = KTree.node A10K2.t2126 (nat_lit 38894654) (nat_lit 16101479194) (nat_lit 0) A10K2.t2127 from rfl, totK_node, tot2126, tot2127]
  decide +kernel

theorem arows2125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2125 = true := by
  rw [show A10K2.u2125 = KTree.node A10K2.t2128 (nat_lit 38907383) (nat_lit 14964648615) (nat_lit 0) A10K2.t2129 from rfl, allE_node, rows2128, irow2125, rows2129]
  all_goals rfl

theorem atot2125 : totK PA10K2 A10K2.u2125 = [0, 525699093747, 2549071073317, 3944978221353, 2130943573381, 409339687510, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u2125 = KTree.node A10K2.t2128 (nat_lit 38907383) (nat_lit 14964648615) (nat_lit 0) A10K2.t2129 from rfl, totK_node, tot2128, tot2129]
  decide +kernel

theorem arows2126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2126 = true := by
  rw [show A10K2.u2126 = KTree.node A10K2.t2130 (nat_lit 38912877) (nat_lit 5414526590) (nat_lit 0) A10K2.t2131 from rfl, allE_node, rows2130, irow2126, rows2131]
  all_goals rfl

theorem atot2126 : totK PA10K2 A10K2.u2126 = [0, 760220352298, 2974910850559, 3788479273699, 1717044902071, 226966334845, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u2126 = KTree.node A10K2.t2130 (nat_lit 38912877) (nat_lit 5414526590) (nat_lit 0) A10K2.t2131 from rfl, totK_node, tot2130, tot2131]
  decide +kernel

theorem arows2128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2128 = true := by
  rw [show A10K2.u2128 = KTree.node A10K2.t2132 (nat_lit 38918691) (nat_lit 7735507675) (nat_lit 0) A10K2.t2133 from rfl, allE_node, rows2132, irow2128, rows2133]
  all_goals rfl

theorem atot2128 : totK PA10K2 A10K2.u2128 = [0, 544386966071, 2590622987586, 4111128025390, 2019142284497, 245216352043, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2128 = KTree.node A10K2.t2132 (nat_lit 38918691) (nat_lit 7735507675) (nat_lit 0) A10K2.t2133 from rfl, totK_node, tot2132, tot2133]
  decide +kernel

theorem arows2129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2129 = true := by
  rw [show A10K2.u2129 = KTree.node A10K2.t2134 (nat_lit 38930508) (nat_lit 10942262896) (nat_lit 0) A10K2.t2135 from rfl, allE_node, rows2134, irow2129, rows2135]
  all_goals rfl

theorem atot2129 : totK PA10K2 A10K2.u2129 = [582799510374, 2394834724106, 3471949891219, 2267217624869, 739823049007, 69709111130, 0, 0, 0, 0] := by
  rw [show A10K2.u2129 = KTree.node A10K2.t2134 (nat_lit 38930508) (nat_lit 10942262896) (nat_lit 0) A10K2.t2135 from rfl, totK_node, tot2134, tot2135]
  decide +kernel

theorem arows2132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2132 = true := by
  rw [show A10K2.u2132 = KTree.node A10K2.t2136 (nat_lit 38938098) (nat_lit 14298392437) (nat_lit 0) A10K2.t2137 from rfl, allE_node, rows2136, irow2132, rows2137]
  all_goals rfl

theorem atot2132 : totK PA10K2 A10K2.u2132 = [769220453689, 2909492414460, 3687436038595, 1850856242705, 317271190992, 10760911071, 0, 0, 0, 0] := by
  rw [show A10K2.u2132 = KTree.node A10K2.t2136 (nat_lit 38938098) (nat_lit 14298392437) (nat_lit 0) A10K2.t2137 from rfl, totK_node, tot2136, tot2137]
  decide +kernel

theorem arows2133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2133 = true := by
  rw [show A10K2.u2133 = KTree.node A10K2.t2138 (nat_lit 38942940) (nat_lit 11238371875) (nat_lit 0) A10K2.t2139 from rfl, allE_node, rows2138, irow2133, rows2139]
  all_goals rfl

theorem atot2133 : totK PA10K2 A10K2.u2133 = [238785603865, 1769747236793, 3874968663070, 2958400086419, 635748773415, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2133 = KTree.node A10K2.t2138 (nat_lit 38942940) (nat_lit 11238371875) (nat_lit 0) A10K2.t2139 from rfl, totK_node, tot2138, tot2139]
  decide +kernel

theorem arows2135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2135 = true := by
  rw [show A10K2.u2135 = KTree.node A10K2.t2140 (nat_lit 38947158) (nat_lit 8907601558) (nat_lit 0) A10K2.t2141 from rfl, allE_node, rows2140, irow2135, rows2141]
  all_goals rfl

theorem atot2135 : totK PA10K2 A10K2.u2135 = [583317622402, 2920958629165, 4178541591575, 1647495388651, 125584219509, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2135 = KTree.node A10K2.t2140 (nat_lit 38947158) (nat_lit 8907601558) (nat_lit 0) A10K2.t2141 from rfl, totK_node, tot2140, tot2141]
  decide +kernel

theorem arows2136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2136 = true := by
  rw [show A10K2.u2136 = KTree.node A10K2.t2142 (nat_lit 38963297) (nat_lit 9952831216) (nat_lit 0) A10K2.t2143 from rfl, allE_node, rows2142, irow2136, rows2143]
  all_goals rfl

theorem atot2136 : totK PA10K2 A10K2.u2136 = [0, 1000990479823, 3719516818274, 3699401701950, 931439028205, 45137667897, 0, 0, 0, 0] := by
  rw [show A10K2.u2136 = KTree.node A10K2.t2142 (nat_lit 38963297) (nat_lit 9952831216) (nat_lit 0) A10K2.t2143 from rfl, totK_node, tot2142, tot2143]
  decide +kernel

theorem arows2141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2141 = true := by
  rw [show A10K2.u2141 = KTree.node A10K2.t2144 (nat_lit 38973118) (nat_lit 15093659588) (nat_lit 0) A10K2.t2145 from rfl, allE_node, rows2144, irow2141, rows2145]
  all_goals rfl

theorem atot2141 : totK PA10K2 A10K2.u2141 = [0, 979941970775, 3579556248420, 3788960430154, 1043301240761, 64078106957, 0, 0, 0, 0] := by
  rw [show A10K2.u2141 = KTree.node A10K2.t2144 (nat_lit 38973118) (nat_lit 15093659588) (nat_lit 0) A10K2.t2145 from rfl, totK_node, tot2144, tot2145]
  decide +kernel

theorem arows2142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2142 = true := by
  rw [show A10K2.u2142 = KTree.node A10K2.t2146 (nat_lit 38982028) (nat_lit 8648287244) (nat_lit 0) A10K2.t2147 from rfl, allE_node, rows2146, irow2142, rows2147]
  all_goals rfl

theorem atot2142 : totK PA10K2 A10K2.u2142 = [0, 517628883618, 2515484011803, 3987859406811, 1946177180973, 291306829918, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2142 = KTree.node A10K2.t2146 (nat_lit 38982028) (nat_lit 8648287244) (nat_lit 0) A10K2.t2147 from rfl, totK_node, tot2146, tot2147]
  decide +kernel

theorem arows2144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2144 = true := by
  rw [show A10K2.u2144 = KTree.node A10K2.t2148 (nat_lit 39063622) (nat_lit 14595535263) (nat_lit 0) A10K2.t2149 from rfl, allE_node, rows2148, irow2144, rows2149]
  all_goals rfl

theorem atot2144 : totK PA10K2 A10K2.u2144 = [0, 364870581428, 2145195776257, 3905901709864, 2503453447915, 526782755111, 30818366867, 0, 0, 0] := by
  rw [show A10K2.u2144 = KTree.node A10K2.t2148 (nat_lit 39063622) (nat_lit 14595535263) (nat_lit 0) A10K2.t2149 from rfl, totK_node, tot2148, tot2149]
  decide +kernel

theorem arows2145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2145 = true := by
  rw [show A10K2.u2145 = KTree.node A10K2.t2150 (nat_lit 39077945) (nat_lit 7037043558) (nat_lit 0) A10K2.t2151 from rfl, allE_node, rows2150, irow2145, rows2151]
  all_goals rfl

theorem atot2145 : totK PA10K2 A10K2.u2145 = [0, 721155701649, 3139640285873, 3986090143422, 1476620174890, 117993539710, 0, 0, 0, 0] := by
  rw [show A10K2.u2145 = KTree.node A10K2.t2150 (nat_lit 39077945) (nat_lit 7037043558) (nat_lit 0) A10K2.t2151 from rfl, totK_node, tot2150, tot2151]
  decide +kernel

theorem arows2148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2148 = true := by
  rw [show A10K2.u2148 = KTree.node A10K2.t2152 (nat_lit 39134963) (nat_lit 8447119407) (nat_lit 0) A10K2.t2153 from rfl, allE_node, rows2152, irow2148, rows2153]
  all_goals rfl

theorem atot2148 : totK PA10K2 A10K2.u2148 = [0, 844157640669, 3121053960162, 3755907601797, 1610291102947, 240870855005, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2148 = KTree.node A10K2.t2152 (nat_lit 39134963) (nat_lit 8447119407) (nat_lit 0) A10K2.t2153 from rfl, totK_node, tot2152, tot2153]
  decide +kernel

theorem arows2149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2149 = true := by
  rw [show A10K2.u2149 = KTree.node A10K2.t2154 (nat_lit 39139538) (nat_lit 15339778260) (nat_lit 0) A10K2.t2155 from rfl, allE_node, rows2154, irow2149, rows2155]
  all_goals rfl

theorem atot2149 : totK PA10K2 A10K2.u2149 = [0, 176986670399, 1679771005456, 3960189579170, 3034664008353, 611401934233, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u2149 = KTree.node A10K2.t2154 (nat_lit 39139538) (nat_lit 15339778260) (nat_lit 0) A10K2.t2155 from rfl, totK_node, tot2154, tot2155]
  decide +kernel

theorem arows2151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2151 = true := by
  rw [show A10K2.u2151 = KTree.node A10K2.t2156 (nat_lit 39143948) (nat_lit 11719777864) (nat_lit 0) A10K2.t2157 from rfl, allE_node, rows2156, irow2151, rows2157]
  all_goals rfl

theorem atot2151 : totK PA10K2 A10K2.u2151 = [0, 583381828075, 2895369274780, 4202092248223, 1698604651018, 138271686854, 0, 0, 0, 0] := by
  rw [show A10K2.u2151 = KTree.node A10K2.t2156 (nat_lit 39143948) (nat_lit 11719777864) (nat_lit 0) A10K2.t2157 from rfl, totK_node, tot2156, tot2157]
  decide +kernel

theorem arows2152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2152 = true := by
  rw [show A10K2.u2152 = KTree.node A10K2.t2158 (nat_lit 39152858) (nat_lit 13957107525) (nat_lit 0) A10K2.t2159 from rfl, allE_node, rows2158, irow2152, rows2159]
  all_goals rfl

theorem atot2152 : totK PA10K2 A10K2.u2152 = [0, 592283690039, 2475940176774, 3948267037969, 2504524067506, 441674959049, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u2152 = KTree.node A10K2.t2158 (nat_lit 39152858) (nat_lit 13957107525) (nat_lit 0) A10K2.t2159 from rfl, totK_node, tot2158, tot2159]
  decide +kernel

theorem arows2156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2156 = true := by
  rw [show A10K2.u2156 = KTree.node A10K2.t2160 (nat_lit 39192787) (nat_lit 10561428562) (nat_lit 0) A10K2.t2161 from rfl, allE_node, rows2160, irow2156, rows2161]
  all_goals rfl

theorem atot2156 : totK PA10K2 A10K2.u2156 = [0, 582189416179, 2638719845580, 3822585037788, 1995046807073, 370081755667, 19313972475, 0, 0, 0] := by
  rw [show A10K2.u2156 = KTree.node A10K2.t2160 (nat_lit 39192787) (nat_lit 10561428562) (nat_lit 0) A10K2.t2161 from rfl, totK_node, tot2160, tot2161]
  decide +kernel

theorem arows2157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2157 = true := by
  rw [show A10K2.u2157 = KTree.node A10K2.t2162 (nat_lit 39200447) (nat_lit 11208942370) (nat_lit 0) A10K2.t2163 from rfl, allE_node, rows2162, irow2157, rows2163]
  all_goals rfl

theorem atot2157 : totK PA10K2 A10K2.u2157 = [0, 768831851770, 3063889396971, 3860198294810, 1664360115915, 210390463828, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u2157 = KTree.node A10K2.t2162 (nat_lit 39200447) (nat_lit 11208942370) (nat_lit 0) A10K2.t2163 from rfl, totK_node, tot2162, tot2163]
  decide +kernel

theorem arows2159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2159 = true := by
  rw [show A10K2.u2159 = KTree.node A10K2.t2164 (nat_lit 39205229) (nat_lit 6389384265) (nat_lit 0) A10K2.t2165 from rfl, allE_node, rows2164, irow2159, rows2165]
  all_goals rfl

theorem atot2159 : totK PA10K2 A10K2.u2159 = [0, 346241136035, 1858055989240, 3846926266520, 2698719828018, 513559548322, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u2159 = KTree.node A10K2.t2164 (nat_lit 39205229) (nat_lit 6389384265) (nat_lit 0) A10K2.t2165 from rfl, totK_node, tot2164, tot2165]
  decide +kernel

theorem arows2160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2160 = true := by
  rw [show A10K2.u2160 = KTree.node A10K2.t2166 (nat_lit 39209746) (nat_lit 14238572755) (nat_lit 0) A10K2.t2167 from rfl, allE_node, rows2166, irow2160, rows2167]
  all_goals rfl

theorem atot2160 : totK PA10K2 A10K2.u2160 = [0, 474251286325, 2772776993507, 4255962733543, 1705612627319, 138456623420, 0, 0, 0, 0] := by
  rw [show A10K2.u2160 = KTree.node A10K2.t2166 (nat_lit 39209746) (nat_lit 14238572755) (nat_lit 0) A10K2.t2167 from rfl, totK_node, tot2166, tot2167]
  decide +kernel

theorem arows2163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2163 = true := by
  rw [show A10K2.u2163 = KTree.node A10K2.t2168 (nat_lit 39225636) (nat_lit 14146055856) (nat_lit 0) A10K2.t2169 from rfl, allE_node, rows2168, irow2163, rows2169]
  all_goals rfl

theorem atot2163 : totK PA10K2 A10K2.u2163 = [0, 0, 944240495777, 3547553427900, 3701369087970, 984780761692, 62884008615, 0, 0, 0] := by
  rw [show A10K2.u2163 = KTree.node A10K2.t2168 (nat_lit 39225636) (nat_lit 14146055856) (nat_lit 0) A10K2.t2169 from rfl, totK_node, tot2168, tot2169]
  decide +kernel

theorem arows2164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2164 = true := by
  rw [show A10K2.u2164 = KTree.node A10K2.t2170 (nat_lit 39240249) (nat_lit 5916184694) (nat_lit 0) A10K2.t2171 from rfl, allE_node, rows2170, irow2164, rows2171]
  all_goals rfl

theorem atot2164 : totK PA10K2 A10K2.u2164 = [0, 0, 1177859234617, 3755976576086, 3384234360000, 826339076684, 56464005069, 0, 0, 0] := by
  rw [show A10K2.u2164 = KTree.node A10K2.t2170 (nat_lit 39240249) (nat_lit 5916184694) (nat_lit 0) A10K2.t2171 from rfl, totK_node, tot2170, tot2171]
  decide +kernel

theorem arows2166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2166 = true := by
  rw [show A10K2.u2166 = KTree.node A10K2.t2172 (nat_lit 39246066) (nat_lit 11842504003) (nat_lit 0) A10K2.t2173 from rfl, allE_node, rows2172, irow2166, rows2173]
  all_goals rfl

theorem atot2166 : totK PA10K2 A10K2.u2166 = [404349054931, 1306467708132, 1294435233361, 1609989964147, 2870806123631, 1611320955236, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u2166 = KTree.node A10K2.t2172 (nat_lit 39246066) (nat_lit 11842504003) (nat_lit 0) A10K2.t2173 from rfl, totK_node, tot2172, tot2173]
  decide +kernel

theorem arows2167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2167 = true := by
  rw [show A10K2.u2167 = KTree.node A10K2.t2174 (nat_lit 39326465) (nat_lit 10313294501) (nat_lit 0) A10K2.t2175 from rfl, allE_node, rows2174, irow2167, rows2175]
  all_goals rfl

theorem atot2167 : totK PA10K2 A10K2.u2167 = [549414831884, 2546406299573, 4114972592242, 2402833646166, 452812665683, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u2167 = KTree.node A10K2.t2174 (nat_lit 39326465) (nat_lit 10313294501) (nat_lit 0) A10K2.t2175 from rfl, totK_node, tot2174, tot2175]
  decide +kernel

theorem arows2174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2174 = true := by
  rw [show A10K2.u2174 = KTree.node A10K2.t2176 (nat_lit 39350227) (nat_lit 9043472346) (nat_lit 0) A10K2.t2177 from rfl, allE_node, rows2176, irow2174, rows2177]
  all_goals rfl

theorem atot2174 : totK PA10K2 A10K2.u2174 = [432469934381, 2412159770771, 4218895975983, 2732117925414, 535409155302, 13814455608, 0, 0, 0, 0] := by
  rw [show A10K2.u2174 = KTree.node A10K2.t2176 (nat_lit 39350227) (nat_lit 9043472346) (nat_lit 0) A10K2.t2177 from rfl, totK_node, tot2176, tot2177]
  decide +kernel

theorem arows2175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2175 = true := by
  rw [show A10K2.u2175 = KTree.node A10K2.t2178 (nat_lit 39354944) (nat_lit 15088835041) (nat_lit 0) A10K2.t2179 from rfl, allE_node, rows2178, irow2175, rows2179]
  all_goals rfl

theorem atot2175 : totK PA10K2 A10K2.u2175 = [0, 806844841637, 3345545518569, 4219851174075, 1566486413132, 129821519417, 0, 0, 0, 0] := by
  rw [show A10K2.u2175 = KTree.node A10K2.t2178 (nat_lit 39354944) (nat_lit 15088835041) (nat_lit 0) A10K2.t2179 from rfl, totK_node, tot2178, tot2179]
  decide +kernel

theorem arows2177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2177 = true := by
  rw [show A10K2.u2177 = KTree.node A10K2.t2180 (nat_lit 39379560) (nat_lit 11944968539) (nat_lit 0) A10K2.t2181 from rfl, allE_node, rows2180, irow2177, rows2181]
  all_goals rfl

theorem atot2177 : totK PA10K2 A10K2.u2177 = [0, 793904700356, 3153756503009, 3967371280393, 1806831748859, 358391606717, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u2177 = KTree.node A10K2.t2180 (nat_lit 39379560) (nat_lit 11944968539) (nat_lit 0) A10K2.t2181 from rfl, totK_node, tot2180, tot2181]
  decide +kernel

theorem arows2178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2178 = true := by
  rw [show A10K2.u2178 = KTree.node A10K2.t2182 (nat_lit 39397640) (nat_lit 7553604572) (nat_lit 0) A10K2.t2183 from rfl, allE_node, rows2182, irow2178, rows2183]
  all_goals rfl

theorem atot2178 : totK PA10K2 A10K2.u2178 = [846901670217, 3224721057321, 3755624459074, 1621609551908, 424362894394, 43766171556, 0, 0, 0, 0] := by
  rw [show A10K2.u2178 = KTree.node A10K2.t2182 (nat_lit 39397640) (nat_lit 7553604572) (nat_lit 0) A10K2.t2183 from rfl, totK_node, tot2182, tot2183]
  decide +kernel

theorem arows2181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2181 = true := by
  rw [show A10K2.u2181 = KTree.node A10K2.t2184 (nat_lit 39402349) (nat_lit 6034215561) (nat_lit 0) A10K2.t2185 from rfl, allE_node, rows2184, irow2181, rows2185]
  all_goals rfl

theorem atot2181 : totK PA10K2 A10K2.u2181 = [364599868439, 1948622720189, 3832566041116, 2864483982875, 610253011352, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2181 = KTree.node A10K2.t2184 (nat_lit 39402349) (nat_lit 6034215561) (nat_lit 0) A10K2.t2185 from rfl, totK_node, tot2184, tot2185]
  decide +kernel

theorem arows2182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2182 = true := by
  rw [show A10K2.u2182 = KTree.node A10K2.t2186 (nat_lit 39409965) (nat_lit 6651382109) (nat_lit 0) A10K2.t2187 from rfl, allE_node, rows2186, irow2182, rows2187]
  all_goals rfl

theorem atot2182 : totK PA10K2 A10K2.u2182 = [687877822425, 2966246185876, 3989003224520, 1802471791635, 257906956198, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2182 = KTree.node A10K2.t2186 (nat_lit 39409965) (nat_lit 6651382109) (nat_lit 0) A10K2.t2187 from rfl, totK_node, tot2186, tot2187]
  decide +kernel

theorem arows2184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2184 = true := by
  rw [show A10K2.u2184 = KTree.node A10K2.t2188 (nat_lit 39415927) (nat_lit 14469999615) (nat_lit 0) A10K2.t2189 from rfl, allE_node, rows2188, irow2184, rows2189]
  all_goals rfl

theorem atot2184 : totK PA10K2 A10K2.u2184 = [319364795913, 2079891140304, 4255215720535, 2954520639874, 541948307067, 13814447077, 0, 0, 0, 0] := by
  rw [show A10K2.u2184 = KTree.node A10K2.t2188 (nat_lit 39415927) (nat_lit 14469999615) (nat_lit 0) A10K2.t2189 from rfl, totK_node, tot2188, tot2189]
  decide +kernel

theorem arows2185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2185 = true := by
  rw [show A10K2.u2185 = KTree.node A10K2.t2190 (nat_lit 39429917) (nat_lit 6295643072) (nat_lit 0) A10K2.t2191 from rfl, allE_node, rows2190, irow2185, rows2191]
  all_goals rfl

theorem atot2185 : totK PA10K2 A10K2.u2185 = [0, 966295491792, 3621983268610, 3987720138063, 1209318674643, 81687574006, 0, 0, 0, 0] := by
  rw [show A10K2.u2185 = KTree.node A10K2.t2190 (nat_lit 39429917) (nat_lit 6295643072) (nat_lit 0) A10K2.t2191 from rfl, totK_node, tot2190, tot2191]
  decide +kernel

theorem arows2189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2189 = true := by
  rw [show A10K2.u2189 = KTree.node A10K2.t2192 (nat_lit 39434515) (nat_lit 10619119242) (nat_lit 0) A10K2.t2193 from rfl, allE_node, rows2192, irow2189, rows2193]
  all_goals rfl

theorem atot2189 : totK PA10K2 A10K2.u2189 = [0, 292336804476, 1899472829643, 3902565123452, 2825474306348, 592087440964, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u2189 = KTree.node A10K2.t2192 (nat_lit 39434515) (nat_lit 10619119242) (nat_lit 0) A10K2.t2193 from rfl, totK_node, tot2192, tot2193]
  decide +kernel

theorem arows2190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2190 = true := by
  rw [show A10K2.u2190 = KTree.node A10K2.t2194 (nat_lit 39442497) (nat_lit 8038769539) (nat_lit 0) A10K2.t2195 from rfl, allE_node, rows2194, irow2190, rows2195]
  all_goals rfl

theorem atot2190 : totK PA10K2 A10K2.u2190 = [0, 646390431836, 2847616308353, 4004761851916, 1818298891262, 220675299389, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2190 = KTree.node A10K2.t2194 (nat_lit 39442497) (nat_lit 8038769539) (nat_lit 0) A10K2.t2195 from rfl, totK_node, tot2194, tot2195]
  decide +kernel

theorem arows2192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2192 = true := by
  rw [show A10K2.u2192 = KTree.node A10K2.t2196 (nat_lit 39448475) (nat_lit 8501118200) (nat_lit 0) A10K2.t2197 from rfl, allE_node, rows2196, irow2192, rows2197]
  all_goals rfl

theorem atot2192 : totK PA10K2 A10K2.u2192 = [625736493037, 2353863278576, 3409166928689, 2707292806012, 931331990545, 76344806208, 0, 0, 0, 0] := by
  rw [show A10K2.u2192 = KTree.node A10K2.t2196 (nat_lit 39448475) (nat_lit 8501118200) (nat_lit 0) A10K2.t2197 from rfl, totK_node, tot2196, tot2197]
  decide +kernel

theorem arows2193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2193 = true := by
  rw [show A10K2.u2193 = KTree.node A10K2.t2198 (nat_lit 39525390) (nat_lit 14594430816) (nat_lit 0) A10K2.t2199 from rfl, allE_node, rows2198, irow2193, rows2199]
  all_goals rfl

theorem atot2193 : totK PA10K2 A10K2.u2193 = [404541561496, 2329601066213, 4207163785213, 2549457935449, 427278642784, 19474173409, 0, 0, 0, 0] := by
  rw [show A10K2.u2193 = KTree.node A10K2.t2198 (nat_lit 39525390) (nat_lit 14594430816) (nat_lit 0) A10K2.t2199 from rfl, totK_node, tot2198, tot2199]
  decide +kernel

theorem arows2196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2196 = true := by
  rw [show A10K2.u2196 = KTree.node A10K2.t2200 (nat_lit 39531738) (nat_lit 14159968836) (nat_lit 0) A10K2.t2201 from rfl, allE_node, rows2200, irow2196, rows2201]
  all_goals rfl

theorem atot2196 : totK PA10K2 A10K2.u2196 = [380633387599, 2225207921740, 4081077495161, 2652052963657, 546137462049, 31677228370, 0, 0, 0, 0] := by
  rw [show A10K2.u2196 = KTree.node A10K2.t2200 (nat_lit 39531738) (nat_lit 14159968836) (nat_lit 0) A10K2.t2201 from rfl, totK_node, tot2200, tot2201]
  decide +kernel

theorem arows2197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2197 = true := by
  rw [show A10K2.u2197 = KTree.node A10K2.t2202 (nat_lit 39544284) (nat_lit 4891738487) (nat_lit 0) A10K2.t2203 from rfl, allE_node, rows2202, irow2197, rows2203]
  all_goals rfl

theorem atot2197 : totK PA10K2 A10K2.u2197 = [873803232168, 3346324208060, 3995304936104, 1580264502516, 151336385663, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2197 = KTree.node A10K2.t2202 (nat_lit 39544284) (nat_lit 4891738487) (nat_lit 0) A10K2.t2203 from rfl, totK_node, tot2202, tot2203]
  decide +kernel

theorem arows2199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2199 = true := by
  rw [show A10K2.u2199 = KTree.node A10K2.t2204 (nat_lit 39548856) (nat_lit 12261905858) (nat_lit 0) A10K2.t2205 from rfl, allE_node, rows2204, irow2199, rows2205]
  all_goals rfl

theorem atot2199 : totK PA10K2 A10K2.u2199 = [0, 1107913417288, 3878169969139, 3847699027355, 1053711415811, 62996513375, 0, 0, 0, 0] := by
  rw [show A10K2.u2199 = KTree.node A10K2.t2204 (nat_lit 39548856) (nat_lit 12261905858) (nat_lit 0) A10K2.t2205 from rfl, totK_node, tot2204, tot2205]
  decide +kernel

theorem arows2200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2200 = true := by
  rw [show A10K2.u2200 = KTree.node A10K2.t2206 (nat_lit 39555080) (nat_lit 14576044548) (nat_lit 0) A10K2.t2207 from rfl, allE_node, rows2206, irow2200, rows2207]
  all_goals rfl

theorem atot2200 : totK PA10K2 A10K2.u2200 = [0, 536794590775, 2601118401531, 4207343095808, 2261618588954, 330936947375, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u2200 = KTree.node A10K2.t2206 (nat_lit 39555080) (nat_lit 14576044548) (nat_lit 0) A10K2.t2207 from rfl, totK_node, tot2206, tot2207]
  decide +kernel

theorem arows2205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2205 = true := by
  rw [show A10K2.u2205 = KTree.node A10K2.t2208 (nat_lit 39562636) (nat_lit 4334225104) (nat_lit 0) A10K2.t2209 from rfl, allE_node, rows2208, irow2205, rows2209]
  all_goals rfl

theorem atot2205 : totK PA10K2 A10K2.u2205 = [0, 605220318077, 2832484232266, 4072452147848, 2093289081211, 303125003105, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u2205 = KTree.node A10K2.t2208 (nat_lit 39562636) (nat_lit 4334225104) (nat_lit 0) A10K2.t2209 from rfl, totK_node, tot2208, tot2209]
  decide +kernel

theorem arows2206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2206 = true := by
  rw [show A10K2.u2206 = KTree.node A10K2.t2210 (nat_lit 39576732) (nat_lit 10615905542) (nat_lit 0) A10K2.t2211 from rfl, allE_node, rows2210, irow2206, rows2211]
  all_goals rfl

theorem atot2206 : totK PA10K2 A10K2.u2206 = [0, 872513974627, 3414861138684, 4075519608893, 1421785106719, 92961844951, 0, 0, 0, 0] := by
  rw [show A10K2.u2206 = KTree.node A10K2.t2210 (nat_lit 39576732) (nat_lit 10615905542) (nat_lit 0) A10K2.t2211 from rfl, totK_node, tot2210, tot2211]
  decide +kernel

theorem arows2208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2208 = true := by
  rw [show A10K2.u2208 = KTree.node A10K2.t2212 (nat_lit 39581143) (nat_lit 14300367555) (nat_lit 0) A10K2.t2213 from rfl, allE_node, rows2212, irow2208, rows2213]
  all_goals rfl

theorem atot2208 : totK PA10K2 A10K2.u2208 = [0, 114701829058, 1318897216474, 3783160125465, 3616410594563, 962575181491, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u2208 = KTree.node A10K2.t2212 (nat_lit 39581143) (nat_lit 14300367555) (nat_lit 0) A10K2.t2213 from rfl, totK_node, tot2212, tot2213]
  decide +kernel

theorem arows2209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2209 = true := by
  rw [show A10K2.u2209 = KTree.node A10K2.t2214 (nat_lit 39587575) (nat_lit 14419359076) (nat_lit 0) A10K2.t2215 from rfl, allE_node, rows2214, irow2209, rows2215]
  all_goals rfl

theorem atot2209 : totK PA10K2 A10K2.u2209 = [0, 476899383554, 2528094570180, 4205071530112, 2387384974644, 430853710907, 25333254304, 0, 0, 0] := by
  rw [show A10K2.u2209 = KTree.node A10K2.t2214 (nat_lit 39587575) (nat_lit 14419359076) (nat_lit 0) A10K2.t2215 from rfl, totK_node, tot2214, tot2215]
  decide +kernel

theorem arows2212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2212 = true := by
  rw [show A10K2.u2212 = KTree.node A10K2.t2216 (nat_lit 39611455) (nat_lit 14216893575) (nat_lit 0) A10K2.t2217 from rfl, allE_node, rows2216, irow2212, rows2217]
  all_goals rfl

theorem atot2212 : totK PA10K2 A10K2.u2212 = [0, 792629982373, 3173079224329, 4117740076166, 1839772820782, 263367286085, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u2212 = KTree.node A10K2.t2216 (nat_lit 39611455) (nat_lit 14216893575) (nat_lit 0) A10K2.t2217 from rfl, totK_node, tot2216, tot2217]
  decide +kernel

theorem arows2213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2213 = true := by
  rw [show A10K2.u2213 = KTree.node A10K2.t2218 (nat_lit 39616211) (nat_lit 9193976927) (nat_lit 0) A10K2.t2219 from rfl, allE_node, rows2218, irow2213, rows2219]
  all_goals rfl

theorem atot2213 : totK PA10K2 A10K2.u2213 = [0, 0, 1125123166457, 3801385122920, 3982195249521, 1181432011946, 81073325079, 0, 0, 0] := by
  rw [show A10K2.u2213 = KTree.node A10K2.t2218 (nat_lit 39616211) (nat_lit 9193976927) (nat_lit 0) A10K2.t2219 from rfl, totK_node, tot2218, tot2219]
  decide +kernel

theorem arows2215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2215 = true := by
  rw [show A10K2.u2215 = KTree.node A10K2.t2220 (nat_lit 39623865) (nat_lit 5758404913) (nat_lit 0) A10K2.t2221 from rfl, allE_node, rows2220, irow2215, rows2221]
  all_goals rfl

theorem atot2215 : totK PA10K2 A10K2.u2215 = [0, 0, 474865294577, 2772012987051, 4374516093338, 2120613654823, 299148954290, 7007974415, 0, 0] := by
  rw [show A10K2.u2215 = KTree.node A10K2.t2220 (nat_lit 39623865) (nat_lit 5758404913) (nat_lit 0) A10K2.t2221 from rfl, totK_node, tot2220, tot2221]
  decide +kernel

theorem arows2216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2216 = true := by
  rw [show A10K2.u2216 = KTree.node A10K2.t2222 (nat_lit 39658953) (nat_lit 4670254655) (nat_lit 0) A10K2.t2223 from rfl, allE_node, rows2222, irow2216, rows2223]
  all_goals rfl

theorem atot2216 : totK PA10K2 A10K2.u2216 = [0, 762731751758, 2869127197625, 3548385538908, 2009442541933, 606594523237, 50425690648, 0, 0, 0] := by
  rw [show A10K2.u2216 = KTree.node A10K2.t2222 (nat_lit 39658953) (nat_lit 4670254655) (nat_lit 0) A10K2.t2223 from rfl, totK_node, tot2222, tot2223]
  decide +kernel

theorem arows2220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2220 = true := by
  rw [show A10K2.u2220 = KTree.node A10K2.t2224 (nat_lit 39663494) (nat_lit 14458004004) (nat_lit 0) A10K2.t2225 from rfl, allE_node, rows2224, irow2220, rows2225]
  all_goals rfl

theorem atot2220 : totK PA10K2 A10K2.u2220 = [0, 280118805119, 1817381551302, 4009987501210, 3030782257534, 624427633828, 31306924438, 0, 0, 0] := by
  rw [show A10K2.u2220 = KTree.node A10K2.t2224 (nat_lit 39663494) (nat_lit 14458004004) (nat_lit 0) A10K2.t2225 from rfl, totK_node, tot2224, tot2225]
  decide +kernel

theorem arows2221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2221 = true := by
  rw [show A10K2.u2221 = KTree.node A10K2.t2226 (nat_lit 39670994) (nat_lit 15570890012) (nat_lit 0) A10K2.t2227 from rfl, allE_node, rows2226, irow2221, rows2227]
  all_goals rfl

theorem atot2221 : totK PA10K2 A10K2.u2221 = [0, 545808196439, 2781530229295, 4101360110630, 1892894618379, 234828554145, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u2221 = KTree.node A10K2.t2226 (nat_lit 39670994) (nat_lit 15570890012) (nat_lit 0) A10K2.t2227 from rfl, totK_node, tot2226, tot2227]
  decide +kernel

theorem arows2223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2223 = true := by
  rw [show A10K2.u2223 = KTree.node A10K2.t2228 (nat_lit 39677385) (nat_lit 6646807650) (nat_lit 0) A10K2.t2229 from rfl, allE_node, rows2228, irow2223, rows2229]
  all_goals rfl

theorem atot2223 : totK PA10K2 A10K2.u2223 = [0, 614826028692, 2823119324603, 4194714707176, 2155534670706, 302191831702, 6279851884, 0, 0, 0] := by
  rw [show A10K2.u2223 = KTree.node A10K2.t2228 (nat_lit 39677385) (nat_lit 6646807650) (nat_lit 0) A10K2.t2229 from rfl, totK_node, tot2228, tot2229]
  decide +kernel

theorem arows2224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2224 = true := by
  rw [show A10K2.u2224 = KTree.node A10K2.t2230 (nat_lit 39691427) (nat_lit 10628298838) (nat_lit 0) A10K2.t2231 from rfl, allE_node, rows2230, irow2224, rows2231]
  all_goals rfl

theorem atot2224 : totK PA10K2 A10K2.u2224 = [0, 0, 909613169185, 3598698244504, 4047378625907, 1222702617322, 82140578509, 0, 0, 0] := by
  rw [show A10K2.u2224 = KTree.node A10K2.t2230 (nat_lit 39691427) (nat_lit 10628298838) (nat_lit 0) A10K2.t2231 from rfl, totK_node, tot2230, tot2231]
  decide +kernel

theorem arows2227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2227 = true := by
  rw [show A10K2.u2227 = KTree.node A10K2.t2232 (nat_lit 39696027) (nat_lit 10042796836) (nat_lit 0) A10K2.t2233 from rfl, allE_node, rows2232, irow2227, rows2233]
  all_goals rfl

theorem atot2227 : totK PA10K2 A10K2.u2227 = [0, 0, 586534461202, 2686081448834, 4096413675201, 2154905305040, 309613191663, 7151180950, 0, 0] := by
  rw [show A10K2.u2227 = KTree.node A10K2.t2232 (nat_lit 39696027) (nat_lit 10042796836) (nat_lit 0) A10K2.t2233 from rfl, totK_node, tot2232, tot2233]
  decide +kernel

theorem arows2228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2228 = true := by
  rw [show A10K2.u2228 = KTree.node A10K2.t2234 (nat_lit 39707891) (nat_lit 10206975903) (nat_lit 0) A10K2.t2235 from rfl, allE_node, rows2234, irow2228, rows2235]
  all_goals rfl

theorem atot2228 : totK PA10K2 A10K2.u2228 = [0, 0, 1075267776003, 3808434007898, 3922992205661, 1020033335031, 37514573965, 0, 0, 0] := by
  rw [show A10K2.u2228 = KTree.node A10K2.t2234 (nat_lit 39707891) (nat_lit 10206975903) (nat_lit 0) A10K2.t2235 from rfl, totK_node, tot2234, tot2235]
  decide +kernel

theorem arows2230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2230 = true := by
  rw [show A10K2.u2230 = KTree.node A10K2.t2236 (nat_lit 39783838) (nat_lit 15580346291) (nat_lit 0) A10K2.t2237 from rfl, allE_node, rows2236, irow2230, rows2237]
  all_goals rfl

theorem atot2230 : totK PA10K2 A10K2.u2230 = [0, 625235104292, 2623128214974, 3834665849307, 2266940458765, 584018774724, 49666398741, 0, 0, 0] := by
  rw [show A10K2.u2230 = KTree.node A10K2.t2236 (nat_lit 39783838) (nat_lit 15580346291) (nat_lit 0) A10K2.t2237 from rfl, totK_node, tot2236, tot2237]
  decide +kernel

theorem arows2231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2231 = true := by
  rw [show A10K2.u2231 = KTree.node A10K2.t2238 (nat_lit 39790760) (nat_lit 3753114544) (nat_lit 0) A10K2.t2239 from rfl, allE_node, rows2238, irow2231, rows2239]
  all_goals rfl

theorem atot2231 : totK PA10K2 A10K2.u2231 = [0, 785174949095, 3297610695965, 4186982251595, 1637646992310, 143494244506, 0, 0, 0, 0] := by
  rw [show A10K2.u2231 = KTree.node A10K2.t2238 (nat_lit 39790760) (nat_lit 3753114544) (nat_lit 0) A10K2.t2239 from rfl, totK_node, tot2238, tot2239]
  decide +kernel

theorem arows2237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2237 = true := by
  rw [show A10K2.u2237 = KTree.node A10K2.t2240 (nat_lit 39796101) (nat_lit 1661866852) (nat_lit 0) A10K2.t2241 from rfl, allE_node, rows2240, irow2237, rows2241]
  all_goals rfl

theorem atot2237 : totK PA10K2 A10K2.u2237 = [0, 542445699397, 2421298140071, 3877456783290, 2500091946319, 441851261106, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u2237 = KTree.node A10K2.t2240 (nat_lit 39796101) (nat_lit 1661866852) (nat_lit 0) A10K2.t2241 from rfl, totK_node, tot2240, tot2241]
  decide +kernel

theorem arows2238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2238 = true := by
  rw [show A10K2.u2238 = KTree.node A10K2.t2242 (nat_lit 39809081) (nat_lit 7321262860) (nat_lit 0) A10K2.t2243 from rfl, allE_node, rows2242, irow2238, rows2243]
  all_goals rfl

theorem atot2238 : totK PA10K2 A10K2.u2238 = [0, 330364443976, 2094819526953, 4140198451159, 2832556599825, 505141478039, 13653259670, 0, 0, 0] := by
  rw [show A10K2.u2238 = KTree.node A10K2.t2242 (nat_lit 39809081) (nat_lit 7321262860) (nat_lit 0) A10K2.t2243 from rfl, totK_node, tot2242, tot2243]
  decide +kernel

theorem arows2240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2240 = true := by
  rw [show A10K2.u2240 = KTree.node A10K2.t2244 (nat_lit 39813697) (nat_lit 10286496343) (nat_lit 0) A10K2.t2245 from rfl, allE_node, rows2244, irow2240, rows2245]
  all_goals rfl

theorem atot2240 : totK PA10K2 A10K2.u2240 = [0, 0, 849447016535, 3451458424095, 4136572806004, 1466353626224, 111598289101, 0, 0, 0] := by
  rw [show A10K2.u2240 = KTree.node A10K2.t2244 (nat_lit 39813697) (nat_lit 10286496343) (nat_lit 0) A10K2.t2245 from rfl, totK_node, tot2244, tot2245]
  decide +kernel

theorem arows2241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2241 = true := by
  rw [show A10K2.u2241 = KTree.node A10K2.t2246 (nat_lit 39822746) (nat_lit 15023698103) (nat_lit 0) A10K2.t2247 from rfl, allE_node, rows2246, irow2241, rows2247]
  all_goals rfl

theorem atot2241 : totK PA10K2 A10K2.u2241 = [0, 0, 782236711393, 3059705094969, 3982133140377, 1853207728610, 234450951515, 6318667960, 0, 0] := by
  rw [show A10K2.u2241 = KTree.node A10K2.t2246 (nat_lit 39822746) (nat_lit 15023698103) (nat_lit 0) A10K2.t2247 from rfl, totK_node, tot2246, tot2247]
  decide +kernel

theorem arows2244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2244 = true := by
  rw [show A10K2.u2244 = KTree.node A10K2.t2248 (nat_lit 39828670) (nat_lit 15947229873) (nat_lit 0) A10K2.t2249 from rfl, allE_node, rows2248, irow2244, rows2249]
  all_goals rfl

theorem atot2244 : totK PA10K2 A10K2.u2244 = [0, 0, 539714045080, 2655927328104, 4105904260797, 2191046646211, 288098009724, 6439430839, 0, 0] := by
  rw [show A10K2.u2244 = KTree.node A10K2.t2248 (nat_lit 39828670) (nat_lit 15947229873) (nat_lit 0) A10K2.t2249 from rfl, totK_node, tot2248, tot2249]
  decide +kernel

theorem arows2245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2245 = true := by
  rw [show A10K2.u2245 = KTree.node A10K2.t2250 (nat_lit 39841825) (nat_lit 9831294521) (nat_lit 0) A10K2.t2251 from rfl, allE_node, rows2250, irow2245, rows2251]
  all_goals rfl

theorem atot2245 : totK PA10K2 A10K2.u2245 = [0, 0, 328041330167, 2131785464352, 4157663104392, 2655467845176, 450339952097, 12132367858, 0, 0] := by
  rw [show A10K2.u2245 = KTree.node A10K2.t2250 (nat_lit 39841825) (nat_lit 9831294521) (nat_lit 0) A10K2.t2251 from rfl, totK_node, tot2250, tot2251]
  decide +kernel

theorem arows2247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2247 = true := by
  rw [show A10K2.u2247 = KTree.node A10K2.t2252 (nat_lit 40445594) (nat_lit 15159780562) (nat_lit 0) A10K2.t2253 from rfl, allE_node, rows2252, irow2247, rows2253]
  all_goals rfl

theorem atot2247 : totK PA10K2 A10K2.u2247 = [0, 814623246770, 2672771201506, 2725433691747, 1613172720314, 1353133134582, 522012413546, 48886019071, 0, 0] := by
  rw [show A10K2.u2247 = KTree.node A10K2.t2252 (nat_lit 40445594) (nat_lit 15159780562) (nat_lit 0) A10K2.t2253 from rfl, totK_node, tot2252, tot2253]
  decide +kernel

theorem arows2248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2248 = true := by
  rw [show A10K2.u2248 = KTree.node A10K2.t2254 (nat_lit 40449940) (nat_lit 8921435088) (nat_lit 0) A10K2.t2255 from rfl, allE_node, rows2254, irow2248, rows2255]
  all_goals rfl

theorem atot2248 : totK PA10K2 A10K2.u2248 = [0, 190751720933, 1738503917184, 4009782210205, 3091243327552, 632831462324, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2248 = KTree.node A10K2.t2254 (nat_lit 40449940) (nat_lit 8921435088) (nat_lit 0) A10K2.t2255 from rfl, totK_node, tot2254, tot2255]
  decide +kernel

theorem arows2252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2252 = true := by
  rw [show A10K2.u2252 = KTree.node A10K2.t2256 (nat_lit 40454387) (nat_lit 9941396732) (nat_lit 0) A10K2.t2257 from rfl, allE_node, rows2256, irow2252, rows2257]
  all_goals rfl

theorem atot2252 : totK PA10K2 A10K2.u2252 = [0, 574197927629, 2895971295889, 4156664409176, 1608608826794, 109005264282, 0, 0, 0, 0] := by
  rw [show A10K2.u2252 = KTree.node A10K2.t2256 (nat_lit 40454387) (nat_lit 9941396732) (nat_lit 0) A10K2.t2257 from rfl, totK_node, tot2256, tot2257]
  decide +kernel

theorem arows2253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2253 = true := by
  rw [show A10K2.u2253 = KTree.node A10K2.t2258 (nat_lit 40461822) (nat_lit 15856477616) (nat_lit 0) A10K2.t2259 from rfl, allE_node, rows2258, irow2253, rows2259]
  all_goals rfl

theorem atot2253 : totK PA10K2 A10K2.u2253 = [0, 785223503628, 3065751549327, 3988540825747, 1827782211423, 246468645545, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2253 = KTree.node A10K2.t2258 (nat_lit 40461822) (nat_lit 15856477616) (nat_lit 0) A10K2.t2259 from rfl, totK_node, tot2258, tot2259]
  decide +kernel

theorem arows2255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2255 = true := by
  rw [show A10K2.u2255 = KTree.node A10K2.t2260 (nat_lit 40467698) (nat_lit 14816415194) (nat_lit 0) A10K2.t2261 from rfl, allE_node, rows2260, irow2255, rows2261]
  all_goals rfl

theorem atot2255 : totK PA10K2 A10K2.u2255 = [0, 0, 1036581180935, 3778337937130, 3983906372578, 1151952151051, 68129554170, 0, 0, 0] := by
  rw [show A10K2.u2255 = KTree.node A10K2.t2260 (nat_lit 40467698) (nat_lit 14816415194) (nat_lit 0) A10K2.t2261 from rfl, totK_node, tot2260, tot2261]
  decide +kernel

theorem arows2256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2256 = true := by
  rw [show A10K2.u2256 = KTree.node A10K2.t2262 (nat_lit 40480405) (nat_lit 5714453568) (nat_lit 0) A10K2.t2263 from rfl, allE_node, rows2262, irow2256, rows2263]
  all_goals rfl

theorem atot2256 : totK PA10K2 A10K2.u2256 = [0, 0, 551586428444, 2587983149565, 3953278098240, 2061651635391, 404267976865, 25565504801, 0, 0] := by
  rw [show A10K2.u2256 = KTree.node A10K2.t2262 (nat_lit 40480405) (nat_lit 5714453568) (nat_lit 0) A10K2.t2263 from rfl, totK_node, tot2262, tot2263]
  decide +kernel

theorem arows2259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2259 = true := by
  rw [show A10K2.u2259 = KTree.node A10K2.t2264 (nat_lit 40486117) (nat_lit 7023573905) (nat_lit 0) A10K2.t2265 from rfl, allE_node, rows2264, irow2259, rows2265]
  all_goals rfl

theorem atot2259 : totK PA10K2 A10K2.u2259 = [0, 0, 719606256589, 2999001711850, 3793395582664, 1597467463868, 211470570378, 5517381808, 0, 0] := by
  rw [show A10K2.u2259 = KTree.node A10K2.t2264 (nat_lit 40486117) (nat_lit 7023573905) (nat_lit 0) A10K2.t2265 from rfl, totK_node, tot2264, tot2265]
  decide +kernel

theorem arows2260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2260 = true := by
  rw [show A10K2.u2260 = KTree.node A10K2.t2266 (nat_lit 40491821) (nat_lit 6599882917) (nat_lit 0) A10K2.t2267 from rfl, allE_node, rows2266, irow2260, rows2267]
  all_goals rfl

theorem atot2260 : totK PA10K2 A10K2.u2260 = [0, 0, 556560574152, 2604484694582, 4102268384933, 1985071373178, 245194492484, 6121173289, 0, 0] := by
  rw [show A10K2.u2260 = KTree.node A10K2.t2266 (nat_lit 40491821) (nat_lit 6599882917) (nat_lit 0) A10K2.t2267 from rfl, totK_node, tot2266, tot2267]
  decide +kernel

theorem arows2262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2262 = true := by
  rw [show A10K2.u2262 = KTree.node A10K2.t2268 (nat_lit 40503341) (nat_lit 6533873830) (nat_lit 0) A10K2.t2269 from rfl, allE_node, rows2268, irow2262, rows2269]
  all_goals rfl

theorem atot2262 : totK PA10K2 A10K2.u2262 = [0, 424355675811, 2178943553689, 3700252832130, 2386325311255, 635759605372, 41778035756, 0, 0, 0] := by
  rw [show A10K2.u2262 = KTree.node A10K2.t2268 (nat_lit 40503341) (nat_lit 6533873830) (nat_lit 0) A10K2.t2269 from rfl, totK_node, tot2268, tot2269]
  decide +kernel

theorem arows2263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2263 = true := by
  rw [show A10K2.u2263 = KTree.node A10K2.t2270 (nat_lit 40511773) (nat_lit 6421608984) (nat_lit 0) A10K2.t2271 from rfl, allE_node, rows2270, irow2263, rows2271]
  all_goals rfl

theorem atot2263 : totK PA10K2 A10K2.u2263 = [0, 802908748769, 3206509025735, 3993610038387, 1633760717243, 202239840726, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u2263 = KTree.node A10K2.t2270 (nat_lit 40511773) (nat_lit 6421608984) (nat_lit 0) A10K2.t2271 from rfl, totK_node, tot2270, tot2271]
  decide +kernel

theorem arows2268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2268 = true := by
  rw [show A10K2.u2268 = KTree.node A10K2.t2272 (nat_lit 40517010) (nat_lit 15259374986) (nat_lit 0) A10K2.t2273 from rfl, allE_node, rows2272, irow2268, rows2273]
  all_goals rfl

theorem atot2268 : totK PA10K2 A10K2.u2268 = [0, 476245452792, 2094837535491, 3564970018587, 2653416556888, 600402468778, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2268 = KTree.node A10K2.t2272 (nat_lit 40517010) (nat_lit 15259374986) (nat_lit 0) A10K2.t2273 from rfl, totK_node, tot2272, tot2273]
  decide +kernel

theorem arows2269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2269 = true := by
  rw [show A10K2.u2269 = KTree.node A10K2.t2274 (nat_lit 40522924) (nat_lit 12833588919) (nat_lit 0) A10K2.t2275 from rfl, allE_node, rows2274, irow2269, rows2275]
  all_goals rfl

theorem atot2269 : totK PA10K2 A10K2.u2269 = [0, 297365837895, 2183818497192, 4181431620767, 2267996030059, 301645130653, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2269 = KTree.node A10K2.t2274 (nat_lit 40522924) (nat_lit 12833588919) (nat_lit 0) A10K2.t2275 from rfl, totK_node, tot2274, tot2275]
  decide +kernel

theorem arows2271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2271 = true := by
  rw [show A10K2.u2271 = KTree.node A10K2.t2276 (nat_lit 40543893) (nat_lit 6401147214) (nat_lit 0) A10K2.t2277 from rfl, allE_node, rows2276, irow2271, rows2277]
  all_goals rfl

theorem atot2271 : totK PA10K2 A10K2.u2271 = [0, 0, 1056061345938, 3749465878801, 3749844980709, 919574633510, 44211540368, 0, 0, 0] := by
  rw [show A10K2.u2271 = KTree.node A10K2.t2276 (nat_lit 40543893) (nat_lit 6401147214) (nat_lit 0) A10K2.t2277 from rfl, totK_node, tot2276, tot2277]
  decide +kernel

theorem arows2272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2272 = true := by
  rw [show A10K2.u2272 = KTree.node A10K2.t2278 (nat_lit 40552158) (nat_lit 6136279765) (nat_lit 0) A10K2.t2279 from rfl, allE_node, rows2278, irow2272, rows2279]
  all_goals rfl

theorem atot2272 : totK PA10K2 A10K2.u2272 = [0, 0, 769879323326, 3323095373150, 3974523369671, 1109233905137, 55994605943, 0, 0, 0] := by
  rw [show A10K2.u2272 = KTree.node A10K2.t2278 (nat_lit 40552158) (nat_lit 6136279765) (nat_lit 0) A10K2.t2279 from rfl, totK_node, tot2278, tot2279]
  decide +kernel

theorem arows2275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2275 = true := by
  rw [show A10K2.u2275 = KTree.node A10K2.t2280 (nat_lit 40567364) (nat_lit 9052899424) (nat_lit 0) A10K2.t2281 from rfl, allE_node, rows2280, irow2275, rows2281]
  all_goals rfl

theorem atot2275 : totK PA10K2 A10K2.u2275 = [0, 476537513919, 1944603884521, 3072326065522, 2802284041842, 1290616965156, 203667120553, 6354482628, 0, 0] := by
  rw [show A10K2.u2275 = KTree.node A10K2.t2280 (nat_lit 40567364) (nat_lit 9052899424) (nat_lit 0) A10K2.t2281 from rfl, totK_node, tot2280, tot2281]
  decide +kernel

theorem arows2276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2276 = true := by
  rw [show A10K2.u2276 = KTree.node A10K2.t2282 (nat_lit 40577175) (nat_lit 12087012632) (nat_lit 0) A10K2.t2283 from rfl, allE_node, rows2282, irow2276, rows2283]
  all_goals rfl

theorem atot2276 : totK PA10K2 A10K2.u2276 = [0, 816281940242, 3281633898180, 4141184804590, 1650127971202, 138501351771, 0, 0, 0, 0] := by
  rw [show A10K2.u2276 = KTree.node A10K2.t2282 (nat_lit 40577175) (nat_lit 12087012632) (nat_lit 0) A10K2.t2283 from rfl, totK_node, tot2282, tot2283]
  decide +kernel

theorem arows2278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2278 = true := by
  rw [show A10K2.u2278 = KTree.node A10K2.t2284 (nat_lit 40581994) (nat_lit 8965704443) (nat_lit 0) A10K2.t2285 from rfl, allE_node, rows2284, irow2278, rows2285]
  all_goals rfl

theorem atot2278 : totK PA10K2 A10K2.u2278 = [0, 452737599564, 2167397113951, 3853964809053, 2736342148615, 601543323645, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u2278 = KTree.node A10K2.t2284 (nat_lit 40581994) (nat_lit 8965704443) (nat_lit 0) A10K2.t2285 from rfl, totK_node, tot2284, tot2285]
  decide +kernel

theorem arows2279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2279 = true := by
  rw [show A10K2.u2279 = KTree.node A10K2.t2286 (nat_lit 40595390) (nat_lit 16396326754) (nat_lit 0) A10K2.t2287 from rfl, allE_node, rows2286, irow2279, rows2287]
  all_goals rfl

theorem atot2279 : totK PA10K2 A10K2.u2279 = [0, 384134078016, 2231373908781, 4167880256133, 2725631498843, 488463792685, 13549732798, 0, 0, 0] := by
  rw [show A10K2.u2279 = KTree.node A10K2.t2286 (nat_lit 40595390) (nat_lit 16396326754) (nat_lit 0) A10K2.t2287 from rfl, totK_node, tot2286, tot2287]
  decide +kernel

theorem arows2283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2283 = true := by
  rw [show A10K2.u2283 = KTree.node A10K2.t2288 (nat_lit 40600455) (nat_lit 14307607608) (nat_lit 0) A10K2.t2289 from rfl, allE_node, rows2288, irow2283, rows2289]
  all_goals rfl

theorem atot2283 : totK PA10K2 A10K2.u2283 = [0, 0, 798026428868, 3300843489235, 4239099564842, 1672417174682, 126804539090, 0, 0, 0] := by
  rw [show A10K2.u2283 = KTree.node A10K2.t2288 (nat_lit 40600455) (nat_lit 14307607608) (nat_lit 0) A10K2.t2289 from rfl, totK_node, tot2288, tot2289]
  decide +kernel

theorem arows2284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2284 = true := by
  rw [show A10K2.u2284 = KTree.node A10K2.t2290 (nat_lit 40610465) (nat_lit 4488428601) (nat_lit 0) A10K2.t2291 from rfl, allE_node, rows2290, irow2284, rows2291]
  all_goals rfl

theorem atot2284 : totK PA10K2 A10K2.u2284 = [0, 0, 816138001125, 3287582860998, 4079707475873, 1584316038768, 133014095321, 0, 0, 0] := by
  rw [show A10K2.u2284 = KTree.node A10K2.t2290 (nat_lit 40610465) (nat_lit 4488428601) (nat_lit 0) A10K2.t2291 from rfl, totK_node, tot2290, tot2291]
  decide +kernel

theorem arows2286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2286 = true := by
  rw [show A10K2.u2286 = KTree.node A10K2.t2292 (nat_lit 40624563) (nat_lit 8236344417) (nat_lit 0) A10K2.t2293 from rfl, allE_node, rows2292, irow2286, rows2293]
  all_goals rfl

theorem atot2286 : totK PA10K2 A10K2.u2286 = [0, 0, 714023596210, 2939298258981, 3975428820224, 1975847564539, 272948568143, 7047025452, 0, 0] := by
  rw [show A10K2.u2286 = KTree.node A10K2.t2292 (nat_lit 40624563) (nat_lit 8236344417) (nat_lit 0) A10K2.t2293 from rfl, totK_node, tot2292, tot2293]
  decide +kernel

theorem arows2287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2287 = true := by
  rw [show A10K2.u2287 = KTree.node A10K2.t2294 (nat_lit 40629527) (nat_lit 10410100123) (nat_lit 0) A10K2.t2295 from rfl, allE_node, rows2294, irow2287, rows2295]
  all_goals rfl

theorem atot2287 : totK PA10K2 A10K2.u2287 = [0, 0, 122137344176, 1552812553750, 4104690667426, 3367410080501, 732357640152, 17649229841, 0, 0] := by
  rw [show A10K2.u2287 = KTree.node A10K2.t2294 (nat_lit 40629527) (nat_lit 10410100123) (nat_lit 0) A10K2.t2295 from rfl, totK_node, tot2294, tot2295]
  decide +kernel

theorem arows2290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2290 = true := by
  rw [show A10K2.u2290 = KTree.node A10K2.t2296 (nat_lit 40708754) (nat_lit 15529038244) (nat_lit 0) A10K2.t2297 from rfl, allE_node, rows2296, irow2290, rows2297]
  all_goals rfl

theorem atot2290 : totK PA10K2 A10K2.u2290 = [0, 0, 868128639955, 3376306585841, 3983909875813, 1357417895152, 157674597719, 23481065185, 0, 0] := by
  rw [show A10K2.u2290 = KTree.node A10K2.t2296 (nat_lit 40708754) (nat_lit 15529038244) (nat_lit 0) A10K2.t2297 from rfl, totK_node, tot2296, tot2297]
  decide +kernel

theorem arows2291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2291 = true := by
  rw [show A10K2.u2291 = KTree.node A10K2.t2298 (nat_lit 40713395) (nat_lit 10179862693) (nat_lit 0) A10K2.t2299 from rfl, allE_node, rows2298, irow2291, rows2299]
  all_goals rfl

theorem atot2291 : totK PA10K2 A10K2.u2291 = [0, 0, 439866010505, 2170971596992, 3658342996263, 2577549037262, 580497295312, 31768748853, 0, 0] := by
  rw [show A10K2.u2291 = KTree.node A10K2.t2298 (nat_lit 40713395) (nat_lit 10179862693) (nat_lit 0) A10K2.t2299 from rfl, totK_node, tot2298, tot2299]
  decide +kernel

theorem arows2293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2293 = true := by
  rw [show A10K2.u2293 = KTree.node A10K2.t2300 (nat_lit 40719680) (nat_lit 9511563628) (nat_lit 0) A10K2.t2301 from rfl, allE_node, rows2300, irow2293, rows2301]
  all_goals rfl

theorem atot2293 : totK PA10K2 A10K2.u2293 = [0, 0, 565512600153, 2615621669305, 3992860664453, 1868016602755, 226584541499, 6239673734, 0, 0] := by
  rw [show A10K2.u2293 = KTree.node A10K2.t2300 (nat_lit 40719680) (nat_lit 9511563628) (nat_lit 0) A10K2.t2301 from rfl, totK_node, tot2300, tot2301]
  decide +kernel

theorem arows2294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2294 = true := by
  rw [show A10K2.u2294 = KTree.node A10K2.t2302 (nat_lit 40726245) (nat_lit 4954389940) (nat_lit 0) A10K2.t2303 from rfl, allE_node, rows2302, irow2294, rows2303]
  all_goals rfl

theorem atot2294 : totK PA10K2 A10K2.u2294 = [0, 0, 490690450838, 2596470685899, 4260246151507, 2334519703864, 336617369081, 6962742351, 0, 0] := by
  rw [show A10K2.u2294 = KTree.node A10K2.t2302 (nat_lit 40726245) (nat_lit 4954389940) (nat_lit 0) A10K2.t2303 from rfl, totK_node, tot2302, tot2303]
  decide +kernel

theorem arows2302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2302 = true := by
  rw [show A10K2.u2302 = KTree.node A10K2.t2304 (nat_lit 40740764) (nat_lit 8864228820) (nat_lit 0) A10K2.t2305 from rfl, allE_node, rows2304, irow2302, rows2305]
  all_goals rfl

theorem atot2302 : totK PA10K2 A10K2.u2302 = [0, 0, 0, 973649677310, 3661896037890, 3864728748054, 1083519258415, 68021021530, 0, 0] := by
  rw [show A10K2.u2302 = KTree.node A10K2.t2304 (nat_lit 40740764) (nat_lit 8864228820) (nat_lit 0) A10K2.t2305 from rfl, totK_node, tot2304, tot2305]
  decide +kernel

theorem arows2303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2303 = true := by
  rw [show A10K2.u2303 = KTree.node A10K2.t2306 (nat_lit 40745516) (nat_lit 10679622573) (nat_lit 0) A10K2.t2307 from rfl, allE_node, rows2306, irow2303, rows2307]
  all_goals rfl

theorem atot2303 : totK PA10K2 A10K2.u2303 = [0, 0, 0, 435231104081, 2120402390481, 3613732807012, 2466799264805, 551680168681, 31018567651, 0] := by
  rw [show A10K2.u2303 = KTree.node A10K2.t2306 (nat_lit 40745516) (nat_lit 10679622573) (nat_lit 0) A10K2.t2307 from rfl, totK_node, tot2306, tot2307]
  decide +kernel

theorem arows2305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2305 = true := by
  rw [show A10K2.u2305 = KTree.node A10K2.t2308 (nat_lit 40752288) (nat_lit 7055947845) (nat_lit 0) A10K2.t2309 from rfl, allE_node, rows2308, irow2305, rows2309]
  all_goals rfl

theorem atot2305 : totK PA10K2 A10K2.u2305 = [0, 0, 0, 563422510714, 2614256194027, 3924966330328, 1794143333311, 223954464666, 5685526223, 0] := by
  rw [show A10K2.u2305 = KTree.node A10K2.t2308 (nat_lit 40752288) (nat_lit 7055947845) (nat_lit 0) A10K2.t2309 from rfl, totK_node, tot2308, tot2309]
  decide +kernel

theorem arows2306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2306 = true := by
  rw [show A10K2.u2306 = KTree.node A10K2.t2310 (nat_lit 40759260) (nat_lit 2474013647) (nat_lit 0) A10K2.t2311 from rfl, allE_node, rows2310, irow2306, rows2311]
  all_goals rfl

theorem atot2306 : totK PA10K2 A10K2.u2306 = [0, 0, 424355675811, 2179475523176, 3755155853182, 2530998399174, 597167500296, 44919408541, 0, 0] := by
  rw [show A10K2.u2306 = KTree.node A10K2.t2310 (nat_lit 40759260) (nat_lit 2474013647) (nat_lit 0) A10K2.t2311 from rfl, totK_node, tot2310, tot2311]
  decide +kernel

theorem arows2309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2309 = true := by
  rw [show A10K2.u2309 = KTree.node A10K2.t2312 (nat_lit 40773398) (nat_lit 11247655626) (nat_lit 0) A10K2.t2313 from rfl, allE_node, rows2312, irow2309, rows2313]
  all_goals rfl

theorem atot2309 : totK PA10K2 A10K2.u2309 = [0, 0, 797557580337, 3092617795042, 3881072720621, 1586457611318, 160213669694, 5460492893, 0, 0] := by
  rw [show A10K2.u2309 = KTree.node A10K2.t2312 (nat_lit 40773398) (nat_lit 11247655626) (nat_lit 0) A10K2.t2313 from rfl, totK_node, tot2312, tot2313]
  decide +kernel

theorem arows2310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2310 = true := by
  rw [show A10K2.u2310 = KTree.node A10K2.t2314 (nat_lit 40778093) (nat_lit 6389384265) (nat_lit 0) A10K2.t2315 from rfl, allE_node, rows2314, irow2310, rows2315]
  all_goals rfl

theorem atot2310 : totK PA10K2 A10K2.u2310 = [0, 0, 305580541691, 1814682972588, 3811194395080, 2790178050174, 598427529620, 31768748853, 0, 0] := by
  rw [show A10K2.u2310 = KTree.node A10K2.t2314 (nat_lit 40778093) (nat_lit 6389384265) (nat_lit 0) A10K2.t2315 from rfl, totK_node, tot2314, tot2315]
  decide +kernel

theorem arows2312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2312 = true := by
  rw [show A10K2.u2312 = KTree.node A10K2.t2316 (nat_lit 40782675) (nat_lit 8881354790) (nat_lit 0) A10K2.t2317 from rfl, allE_node, rows2316, irow2312, rows2317]
  all_goals rfl

theorem atot2312 : totK PA10K2 A10K2.u2312 = [0, 0, 467092711113, 2603223967315, 4196382004603, 1876727853848, 149334533767, 0, 0, 0] := by
  rw [show A10K2.u2312 = KTree.node A10K2.t2316 (nat_lit 40782675) (nat_lit 8881354790) (nat_lit 0) A10K2.t2317 from rfl, totK_node, tot2316, tot2317]
  decide +kernel

theorem arows2313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2313 = true := by
  rw [show A10K2.u2313 = KTree.node A10K2.t2318 (nat_lit 40805719) (nat_lit 6118585603) (nat_lit 0) A10K2.t2319 from rfl, allE_node, rows2318, irow2313, rows2319]
  all_goals rfl

theorem atot2313 : totK PA10K2 A10K2.u2313 = [0, 0, 0, 1107780468459, 3750918566633, 3541294073577, 826765217835, 44833411993, 0, 0] := by
  rw [show A10K2.u2313 = KTree.node A10K2.t2318 (nat_lit 40805719) (nat_lit 6118585603) (nat_lit 0) A10K2.t2319 from rfl, totK_node, tot2318, tot2319]
  decide +kernel

theorem arows2317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2317 = true := by
  rw [show A10K2.u2317 = KTree.node A10K2.t2320 (nat_lit 40814237) (nat_lit 6085757737) (nat_lit 0) A10K2.t2321 from rfl, allE_node, rows2320, irow2317, rows2321]
  all_goals rfl

theorem atot2317 : totK PA10K2 A10K2.u2317 = [0, 0, 0, 873983014053, 3566542934784, 3862478172727, 960829403048, 50442382728, 0, 0] := by
  rw [show A10K2.u2317 = KTree.node A10K2.t2320 (nat_lit 40814237) (nat_lit 6085757737) (nat_lit 0) A10K2.t2321 from rfl, totK_node, tot2320, tot2321]
  decide +kernel

theorem arows2318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2318 = true := by
  rw [show A10K2.u2318 = KTree.node A10K2.t2322 (nat_lit 40832097) (nat_lit 5977710490) (nat_lit 0) A10K2.t2323 from rfl, allE_node, rows2322, irow2318, rows2323]
  all_goals rfl

theorem atot2318 : totK PA10K2 A10K2.u2318 = [0, 0, 786796184452, 2509811439584, 2813722043472, 2273142924646, 1104754676177, 181660199303, 5982052406, 0] := by
  rw [show A10K2.u2318 = KTree.node A10K2.t2322 (nat_lit 40832097) (nat_lit 5977710490) (nat_lit 0) A10K2.t2323 from rfl, totK_node, tot2322, tot2323]
  decide +kernel

theorem arows2320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2320 = true := by
  rw [show A10K2.u2320 = KTree.node A10K2.t2324 (nat_lit 40840883) (nat_lit 10143942411) (nat_lit 0) A10K2.t2325 from rfl, allE_node, rows2324, irow2320, rows2325]
  all_goals rfl

theorem atot2320 : totK PA10K2 A10K2.u2320 = [0, 0, 500856004971, 2531128311401, 4093050943087, 2244190760311, 414547065353, 25660650750, 0, 0] := by
  rw [show A10K2.u2320 = KTree.node A10K2.t2324 (nat_lit 40840883) (nat_lit 10143942411) (nat_lit 0) A10K2.t2325 from rfl, totK_node, tot2324, tot2325]
  decide +kernel

theorem arows2321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2321 = true := by
  rw [show A10K2.u2321 = KTree.node A10K2.t2326 (nat_lit 40854994) (nat_lit 15365736412) (nat_lit 0) A10K2.t2327 from rfl, allE_node, rows2326, irow2321, rows2327]
  all_goals rfl

theorem atot2321 : totK PA10K2 A10K2.u2321 = [0, 0, 833984530526, 3340198909022, 4153934555425, 1583601796045, 120497479135, 0, 0, 0] := by
  rw [show A10K2.u2321 = KTree.node A10K2.t2326 (nat_lit 40854994) (nat_lit 15365736412) (nat_lit 0) A10K2.t2327 from rfl, totK_node, tot2326, tot2327]
  decide +kernel

theorem arows2324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2324 = true := by
  rw [show A10K2.u2324 = KTree.node A10K2.t2328 (nat_lit 40861142) (nat_lit 15883464952) (nat_lit 0) A10K2.t2329 from rfl, allE_node, rows2328, irow2324, rows2329]
  all_goals rfl

theorem atot2324 : totK PA10K2 A10K2.u2324 = [0, 396587084194, 1314051885422, 2136192148829, 3001506383381, 2473748564419, 673747922148, 41590655314, 0, 0] := by
  rw [show A10K2.u2324 = KTree.node A10K2.t2328 (nat_lit 40861142) (nat_lit 15883464952) (nat_lit 0) A10K2.t2329 from rfl, totK_node, tot2328, tot2329]
  decide +kernel

theorem arows2325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2325 = true := by
  rw [show A10K2.u2325 = KTree.node A10K2.t2330 (nat_lit 40900614) (nat_lit 13058441128) (nat_lit 0) A10K2.t2331 from rfl, allE_node, rows2330, irow2325, rows2331]
  all_goals rfl

theorem atot2325 : totK PA10K2 A10K2.u2325 = [0, 421813282240, 2145200985869, 3772212315712, 2462757162485, 528314460027, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2325 = KTree.node A10K2.t2330 (nat_lit 40900614) (nat_lit 13058441128) (nat_lit 0) A10K2.t2331 from rfl, totK_node, tot2330, tot2331]
  decide +kernel

theorem arows2327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2327 = true := by
  rw [show A10K2.u2327 = KTree.node A10K2.t2332 (nat_lit 40914958) (nat_lit 13310075908) (nat_lit 0) A10K2.t2333 from rfl, allE_node, rows2332, irow2327, rows2333]
  all_goals rfl

theorem atot2327 : totK PA10K2 A10K2.u2327 = [0, 481398847354, 2528565920130, 4080104792886, 2104609255521, 263521385742, 0, 0, 0, 0] := by
  rw [show A10K2.u2327 = KTree.node A10K2.t2332 (nat_lit 40914958) (nat_lit 13310075908) (nat_lit 0) A10K2.t2333 from rfl, totK_node, tot2332, tot2333]
  decide +kernel

theorem arows2328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2328 = true := by
  rw [show A10K2.u2328 = KTree.node A10K2.t2334 (nat_lit 40930055) (nat_lit 7503015427) (nat_lit 0) A10K2.t2335 from rfl, allE_node, rows2334, irow2328, rows2335]
  all_goals rfl

theorem atot2328 : totK PA10K2 A10K2.u2328 = [0, 0, 1043950784366, 3672455570024, 3704690807575, 988698719906, 68756073609, 0, 0, 0] := by
  rw [show A10K2.u2328 = KTree.node A10K2.t2334 (nat_lit 40930055) (nat_lit 7503015427) (nat_lit 0) A10K2.t2335 from rfl, totK_node, tot2334, tot2335]
  decide +kernel

theorem arows2333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2333 = true := by
  rw [show A10K2.u2333 = KTree.node A10K2.t2336 (nat_lit 40949824) (nat_lit 14686140639) (nat_lit 0) A10K2.t2337 from rfl, allE_node, rows2336, irow2333, rows2337]
  all_goals rfl

theorem atot2333 : totK PA10K2 A10K2.u2333 = [0, 316846731414, 1309621504287, 2786258037212, 3297427392923, 1452216900959, 191878137383, 5546304973, 0, 0] := by
  rw [show A10K2.u2333 = KTree.node A10K2.t2336 (nat_lit 40949824) (nat_lit 14686140639) (nat_lit 0) A10K2.t2337 from rfl, totK_node, tot2336, tot2337]
  decide +kernel

theorem arows2334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2334 = true := by
  rw [show A10K2.u2334 = KTree.node A10K2.t2338 (nat_lit 40971995) (nat_lit 6873333145) (nat_lit 0) A10K2.t2339 from rfl, allE_node, rows2338, irow2334, rows2339]
  all_goals rfl

theorem atot2334 : totK PA10K2 A10K2.u2334 = [0, 527310909255, 2568249447948, 3944745403112, 2223847113284, 429546316397, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u2334 = KTree.node A10K2.t2338 (nat_lit 40971995) (nat_lit 6873333145) (nat_lit 0) A10K2.t2339 from rfl, totK_node, tot2338, tot2339]
  decide +kernel

theorem arows2336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2336 = true := by
  rw [show A10K2.u2336 = KTree.node A10K2.t2340 (nat_lit 40977565) (nat_lit 6181965923) (nat_lit 0) A10K2.t2341 from rfl, allE_node, rows2340, irow2336, rows2341]
  all_goals rfl

theorem atot2336 : totK PA10K2 A10K2.u2336 = [0, 760368498474, 2923062772246, 3728587120611, 1815165431835, 256607918213, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u2336 = KTree.node A10K2.t2340 (nat_lit 40977565) (nat_lit 6181965923) (nat_lit 0) A10K2.t2341 from rfl, totK_node, tot2340, tot2341]
  decide +kernel

theorem arows2337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2337 = true := by
  rw [show A10K2.u2337 = KTree.node A10K2.t2342 (nat_lit 40983072) (nat_lit 13135284805) (nat_lit 0) A10K2.t2343 from rfl, allE_node, rows2342, irow2337, rows2343]
  all_goals rfl

theorem atot2337 : totK PA10K2 A10K2.u2337 = [0, 546739207337, 2548272825751, 4088298373562, 2161582924844, 301443920409, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2337 = KTree.node A10K2.t2342 (nat_lit 40983072) (nat_lit 13135284805) (nat_lit 0) A10K2.t2343 from rfl, totK_node, tot2342, tot2343]
  decide +kernel

theorem arows2340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2340 = true := by
  rw [show A10K2.u2340 = KTree.node A10K2.t2344 (nat_lit 40991859) (nat_lit 6088182525) (nat_lit 0) A10K2.t2345 from rfl, allE_node, rows2344, irow2340, rows2345]
  all_goals rfl

theorem atot2340 : totK PA10K2 A10K2.u2340 = [0, 45544482702, 1414428716986, 4116863299416, 3542510252232, 903218956849, 56781017478, 0, 0, 0] := by
  rw [show A10K2.u2340 = KTree.node A10K2.t2344 (nat_lit 40991859) (nat_lit 6088182525) (nat_lit 0) A10K2.t2345 from rfl, totK_node, tot2344, tot2345]
  decide +kernel

theorem arows2341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2341 = true := by
  rw [show A10K2.u2341 = KTree.node A10K2.t2346 (nat_lit 41004606) (nat_lit 15680755588) (nat_lit 0) A10K2.t2347 from rfl, allE_node, rows2346, irow2341, rows2347]
  all_goals rfl

theorem atot2341 : totK PA10K2 A10K2.u2341 = [0, 0, 525699093747, 2588977702370, 3978466136173, 2066543389965, 399033399313, 25565504801, 0, 0] := by
  rw [show A10K2.u2341 = KTree.node A10K2.t2346 (nat_lit 41004606) (nat_lit 15680755588) (nat_lit 0) A10K2.t2347 from rfl, totK_node, tot2346, tot2347]
  decide +kernel

theorem arows2343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2343 = true := by
  rw [show A10K2.u2343 = KTree.node A10K2.t2348 (nat_lit 41010358) (nat_lit 14372356488) (nat_lit 0) A10K2.t2349 from rfl, allE_node, rows2348, irow2343, rows2349]
  all_goals rfl

theorem atot2343 : totK PA10K2 A10K2.u2343 = [0, 0, 760220352298, 3038452791953, 3787246543697, 1622444835081, 211130646547, 5517381808, 0, 0] := by
  rw [show A10K2.u2343 = KTree.node A10K2.t2348 (nat_lit 41010358) (nat_lit 14372356488) (nat_lit 0) A10K2.t2349 from rfl, totK_node, tot2348, tot2349]
  decide +kernel

theorem arows2344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2344 = true := by
  rw [show A10K2.u2344 = KTree.node A10K2.t2350 (nat_lit 41015980) (nat_lit 12620475288) (nat_lit 0) A10K2.t2351 from rfl, allE_node, rows2350, irow2344, rows2351]
  all_goals rfl

theorem atot2344 : totK PA10K2 A10K2.u2344 = [0, 0, 589931448773, 2662269644773, 4063490475245, 1973252533054, 245216352043, 6121173289, 0, 0] := by
  rw [show A10K2.u2344 = KTree.node A10K2.t2350 (nat_lit 41015980) (nat_lit 12620475288) (nat_lit 0) A10K2.t2351 from rfl, totK_node, tot2350, tot2351]
  decide +kernel

theorem arows2348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2348 = true := by
  rw [show A10K2.u2348 = KTree.node A10K2.t2352 (nat_lit 41027752) (nat_lit 8983246001) (nat_lit 0) A10K2.t2353 from rfl, allE_node, rows2352, irow2348, rows2353]
  all_goals rfl

theorem atot2348 : totK PA10K2 A10K2.u2348 = [0, 582799510374, 2349290241404, 3378398228256, 2331242013360, 730724827741, 55409504833, 0, 0, 0] := by
  rw [show A10K2.u2348 = KTree.node A10K2.t2352 (nat_lit 41027752) (nat_lit 8983246001) (nat_lit 0) A10K2.t2353 from rfl, totK_node, tot2352, tot2353]
  decide +kernel

theorem arows2349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2349 = true := by
  rw [show A10K2.u2349 = KTree.node A10K2.t2354 (nat_lit 41035447) (nat_lit 13339020630) (nat_lit 0) A10K2.t2355 from rfl, allE_node, rows2354, irow2349, rows2355]
  all_goals rfl

theorem atot2349 : totK PA10K2 A10K2.u2349 = [0, 769220453689, 3034397956936, 3859237211425, 1684066856542, 248769709551, 10760911071, 0, 0, 0] := by
  rw [show A10K2.u2349 = KTree.node A10K2.t2354 (nat_lit 41035447) (nat_lit 13339020630) (nat_lit 0) A10K2.t2355 from rfl, totK_node, tot2354, tot2355]
  decide +kernel

theorem arows2351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2351 = true := by
  rw [show A10K2.u2351 = KTree.node A10K2.t2356 (nat_lit 41040156) (nat_lit 12193009390) (nat_lit 0) A10K2.t2357 from rfl, allE_node, rows2356, irow2351, rows2357]
  all_goals rfl

theorem atot2351 : totK PA10K2 A10K2.u2351 = [0, 238785603865, 1709533037384, 3856785898974, 2978862855991, 628753727655, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2351 = KTree.node A10K2.t2356 (nat_lit 41040156) (nat_lit 12193009390) (nat_lit 0) A10K2.t2357 from rfl, totK_node, tot2356, tot2357]
  decide +kernel

theorem arows2352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2352 = true := by
  rw [show A10K2.u2352 = KTree.node A10K2.t2358 (nat_lit 41044535) (nat_lit 5997226036) (nat_lit 0) A10K2.t2359 from rfl, allE_node, rows2358, irow2352, rows2359]
  all_goals rfl

theorem atot2352 : totK PA10K2 A10K2.u2352 = [0, 583317622402, 2892915991251, 4119979931862, 1686811112658, 145433579552, 0, 0, 0, 0] := by
  rw [show A10K2.u2352 = KTree.node A10K2.t2358 (nat_lit 41044535) (nat_lit 5997226036) (nat_lit 0) A10K2.t2359 from rfl, totK_node, tot2358, tot2359]
  decide +kernel

theorem arows2355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2355 = true := by
  rw [show A10K2.u2355 = KTree.node A10K2.t2360 (nat_lit 41060566) (nat_lit 8546283487) (nat_lit 0) A10K2.t2361 from rfl, allE_node, rows2360, irow2355, rows2361]
  all_goals rfl

theorem atot2355 : totK PA10K2 A10K2.u2355 = [0, 0, 956053949346, 3674716852666, 3742551439984, 959887589246, 58502284136, 0, 0, 0] := by
  rw [show A10K2.u2355 = KTree.node A10K2.t2360 (nat_lit 41060566) (nat_lit 8546283487) (nat_lit 0) A10K2.t2361 from rfl, totK_node, tot2360, tot2361]
  decide +kernel

theorem arows2356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2356 = true := by
  rw [show A10K2.u2356 = KTree.node A10K2.t2362 (nat_lit 41074701) (nat_lit 5771049398) (nat_lit 0) A10K2.t2363 from rfl, allE_node, rows2362, irow2356, rows2363]
  all_goals rfl

theorem atot2356 : totK PA10K2 A10K2.u2356 = [0, 0, 978718430357, 3577650766209, 3774047079074, 1023672173606, 63118289004, 0, 0, 0] := by
  rw [show A10K2.u2356 = KTree.node A10K2.t2362 (nat_lit 41074701) (nat_lit 5771049398) (nat_lit 0) A10K2.t2363 from rfl, totK_node, tot2362, tot2363]
  decide +kernel

theorem arows2358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2358 = true := by
  rw [show A10K2.u2358 = KTree.node A10K2.t2364 (nat_lit 41080040) (nat_lit 4774902657) (nat_lit 0) A10K2.t2365 from rfl, allE_node, rows2364, irow2358, rows2365]
  all_goals rfl

theorem atot2358 : totK PA10K2 A10K2.u2358 = [0, 0, 598472900375, 2716213496413, 3904730605118, 1810137743315, 271677105452, 6354482628, 0, 0] := by
  rw [show A10K2.u2358 = KTree.node A10K2.t2364 (nat_lit 41080040) (nat_lit 4774902657) (nat_lit 0) A10K2.t2365 from rfl, totK_node, tot2364, tot2365]
  decide +kernel

theorem arows2359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2359 = true := by
  rw [show A10K2.u2359 = KTree.node A10K2.t2366 (nat_lit 41161058) (nat_lit 8955295194) (nat_lit 0) A10K2.t2367 from rfl, allE_node, rows2366, irow2359, rows2367]
  all_goals rfl

theorem atot2359 : totK PA10K2 A10K2.u2359 = [0, 0, 509481651681, 2630966077824, 4069255488985, 1874673595976, 238729750056, 5447185874, 0, 0] := by
  rw [show A10K2.u2359 = KTree.node A10K2.t2366 (nat_lit 41161058) (nat_lit 8955295194) (nat_lit 0) A10K2.t2367 from rfl, totK_node, tot2366, tot2367]
  decide +kernel

theorem arows2365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2365 = true := by
  rw [show A10K2.u2365 = KTree.node A10K2.t2368 (nat_lit 41175840) (nat_lit 12655210993) (nat_lit 0) A10K2.t2369 from rfl, allE_node, rows2368, irow2365, rows2369]
  all_goals rfl

theorem atot2365 : totK PA10K2 A10K2.u2365 = [0, 0, 495048406196, 2595974656197, 4235479407780, 1841985927110, 146270772628, 0, 0, 0] := by
  rw [show A10K2.u2365 = KTree.node A10K2.t2368 (nat_lit 41175840) (nat_lit 12655210993) (nat_lit 0) A10K2.t2369 from rfl, totK_node, tot2368, tot2369]
  decide +kernel

theorem arows2366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2366 = true := by
  rw [show A10K2.u2366 = KTree.node A10K2.t2370 (nat_lit 41232746) (nat_lit 9865715108) (nat_lit 0) A10K2.t2371 from rfl, allE_node, rows2370, irow2366, rows2371]
  all_goals rfl

theorem atot2366 : totK PA10K2 A10K2.u2366 = [0, 0, 844157640669, 3298572465765, 3931153481937, 1442455154363, 168264726921, 6354482628, 0, 0] := by
  rw [show A10K2.u2366 = KTree.node A10K2.t2370 (nat_lit 41232746) (nat_lit 9865715108) (nat_lit 0) A10K2.t2371 from rfl, totK_node, tot2370, tot2371]
  decide +kernel

theorem arows2368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2368 = true := by
  rw [show A10K2.u2368 = KTree.node A10K2.t2372 (nat_lit 41237719) (nat_lit 12656074390) (nat_lit 0) A10K2.t2373 from rfl, allE_node, rows2372, irow2368, rows2373]
  all_goals rfl

theorem atot2368 : totK PA10K2 A10K2.u2368 = [0, 0, 466842231207, 2152836834731, 3656005444313, 2549293240341, 561159119234, 31452573850, 0, 0] := by
  rw [show A10K2.u2368 = KTree.node A10K2.t2372 (nat_lit 41237719) (nat_lit 12656074390) (nat_lit 0) A10K2.t2373 from rfl, totK_node, tot2372, tot2373]
  decide +kernel

theorem arows2369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2369 = true := by
  rw [show A10K2.u2369 = KTree.node A10K2.t2374 (nat_lit 41243884) (nat_lit 11606420549) (nat_lit 0) A10K2.t2375 from rfl, allE_node, rows2374, irow2369, rows2375]
  all_goals rfl

theorem atot2369 : totK PA10K2 A10K2.u2369 = [0, 0, 592338980951, 2646720801451, 3978738649912, 1948575921936, 241147085312, 6354482628, 0, 0] := by
  rw [show A10K2.u2369 = KTree.node A10K2.t2374 (nat_lit 41243884) (nat_lit 11606420549) (nat_lit 0) A10K2.t2375 from rfl, totK_node, tot2374, tot2375]
  decide +kernel

theorem arows2372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2372 = true := by
  rw [show A10K2.u2372 = KTree.node A10K2.t2376 (nat_lit 41252017) (nat_lit 4131011510) (nat_lit 0) A10K2.t2377 from rfl, allE_node, rows2376, irow2372, rows2377]
  all_goals rfl

theorem atot2372 : totK PA10K2 A10K2.u2372 = [0, 0, 532989512826, 2737224501897, 4259814188861, 2178106911867, 306940003127, 6962742351, 0, 0] := by
  rw [show A10K2.u2372 = KTree.node A10K2.t2376 (nat_lit 41252017) (nat_lit 4131011510) (nat_lit 0) A10K2.t2377 from rfl, totK_node, tot2376, tot2377]
  decide +kernel

theorem arows2373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2373 = true := by
  rw [show A10K2.u2373 = KTree.node A10K2.t2378 (nat_lit 41291882) (nat_lit 4267099027) (nat_lit 0) A10K2.t2379 from rfl, allE_node, rows2378, irow2373, rows2379]
  all_goals rfl

theorem atot2373 : totK PA10K2 A10K2.u2373 = [0, 0, 642116440155, 2756145415776, 3921641608299, 1736139209115, 211921579284, 5460492893, 0, 0] := by
  rw [show A10K2.u2373 = KTree.node A10K2.t2378 (nat_lit 41291882) (nat_lit 4267099027) (nat_lit 0) A10K2.t2379 from rfl, totK_node, tot2378, tot2379]
  decide +kernel

theorem arows2375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2375 = true := by
  rw [show A10K2.u2375 = KTree.node A10K2.t2380 (nat_lit 41299377) (nat_lit 5789452796) (nat_lit 0) A10K2.t2381 from rfl, allE_node, rows2380, irow2375, rows2381]
  all_goals rfl

theorem atot2375 : totK PA10K2 A10K2.u2375 = [0, 0, 469386291323, 2552835584222, 4118603728548, 2081306438919, 350584490309, 24969229125, 0, 0] := by
  rw [show A10K2.u2375 = KTree.node A10K2.t2380 (nat_lit 41299377) (nat_lit 5789452796) (nat_lit 0) A10K2.t2381 from rfl, totK_node, tot2380, tot2381]
  decide +kernel

theorem arows2376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2376 = true := by
  rw [show A10K2.u2376 = KTree.node A10K2.t2382 (nat_lit 41304917) (nat_lit 6365417349) (nat_lit 0) A10K2.t2383 from rfl, allE_node, rows2382, irow2376, rows2383]
  all_goals rfl

theorem atot2376 : totK PA10K2 A10K2.u2376 = [0, 0, 820492422360, 3020869113244, 3610828018387, 1598666062910, 221911475030, 6034215561, 0, 0] := by
  rw [show A10K2.u2376 = KTree.node A10K2.t2382 (nat_lit 41304917) (nat_lit 6365417349) (nat_lit 0) A10K2.t2383 from rfl, totK_node, tot2382, tot2383]
  decide +kernel

theorem arows2380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2380 = true := by
  rw [show A10K2.u2380 = KTree.node A10K2.t2384 (nat_lit 41310455) (nat_lit 4741712768) (nat_lit 0) A10K2.t2385 from rfl, allE_node, rows2384, irow2380, rows2385]
  all_goals rfl

theorem atot2380 : totK PA10K2 A10K2.u2380 = [0, 0, 0, 1515586057008, 4316689553309, 2819164610458, 455367706873, 11740475125, 0, 0] := by
  rw [show A10K2.u2380 = KTree.node A10K2.t2384 (nat_lit 41310455) (nat_lit 4741712768) (nat_lit 0) A10K2.t2385 from rfl, totK_node, tot2384, tot2385]
  decide +kernel

theorem arows2381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2381 = true := by
  rw [show A10K2.u2381 = KTree.node A10K2.t2386 (nat_lit 41330785) (nat_lit 9490660250) (nat_lit 0) A10K2.t2387 from rfl, allE_node, rows2386, irow2381, rows2387]
  all_goals rfl

theorem atot2381 : totK PA10K2 A10K2.u2381 = [0, 0, 0, 1102075327196, 3930387908516, 3474681448779, 714812406696, 38045387652, 0, 0] := by
  rw [show A10K2.u2381 = KTree.node A10K2.t2386 (nat_lit 41330785) (nat_lit 9490660250) (nat_lit 0) A10K2.t2387 from rfl, totK_node, tot2386, tot2387]
  decide +kernel

theorem arows2383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2383 = true := by
  rw [show A10K2.u2383 = KTree.node A10K2.t2388 (nat_lit 41339396) (nat_lit 12683970786) (nat_lit 0) A10K2.t2389 from rfl, allE_node, rows2388, irow2383, rows2389]
  all_goals rfl

theorem atot2383 : totK PA10K2 A10K2.u2383 = [0, 0, 0, 570365406722, 2921808948384, 4057356042647, 1383143240441, 100804477560, 0, 0] := by
  rw [show A10K2.u2383 = KTree.node A10K2.t2388 (nat_lit 41339396) (nat_lit 12683970786) (nat_lit 0) A10K2.t2389 from rfl, totK_node, tot2388, tot2389]
  decide +kernel

theorem arows2384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2384 = true := by
  rw [show A10K2.u2384 = KTree.node A10K2.t2390 (nat_lit 41422208) (nat_lit 15104162539) (nat_lit 0) A10K2.t2391 from rfl, allE_node, rows2390, irow2384, rows2391]
  all_goals rfl

theorem atot2384 : totK PA10K2 A10K2.u2384 = [0, 591294713498, 2465630538831, 3511525759154, 1913191234370, 682860914371, 541489482115, 151598891327, 6354482628, 0] := by
  rw [show A10K2.u2384 = KTree.node A10K2.t2390 (nat_lit 41422208) (nat_lit 15104162539) (nat_lit 0) A10K2.t2391 from rfl, totK_node, tot2390, tot2391]
  decide +kernel

theorem arows2387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2387 = true := by
  rw [show A10K2.u2387 = KTree.node A10K2.t2392 (nat_lit 41444786) (nat_lit 14678519464) (nat_lit 0) A10K2.t2393 from rfl, allE_node, rows2392, irow2387, rows2393]
  all_goals rfl

theorem atot2387 : totK PA10K2 A10K2.u2387 = [0, 794133235012, 3325744520023, 4269639770271, 1703162618224, 160120073630, 0, 0, 0, 0] := by
  rw [show A10K2.u2387 = KTree.node A10K2.t2392 (nat_lit 41444786) (nat_lit 14678519464) (nat_lit 0) A10K2.t2393 from rfl, totK_node, tot2392, tot2393]
  decide +kernel

theorem arows2388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2388 = true := by
  rw [show A10K2.u2388 = KTree.node A10K2.t2394 (nat_lit 41450718) (nat_lit 11410772216) (nat_lit 0) A10K2.t2395 from rfl, allE_node, rows2394, irow2388, rows2395]
  all_goals rfl

theorem atot2388 : totK PA10K2 A10K2.u2388 = [0, 0, 979696397645, 3717697828280, 4127759170107, 1234536323103, 82984143167, 0, 0, 0] := by
  rw [show A10K2.u2388 = KTree.node A10K2.t2394 (nat_lit 41450718) (nat_lit 11410772216) (nat_lit 0) A10K2.t2395 from rfl, totK_node, tot2394, tot2395]
  decide +kernel

theorem arows2390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2390 = true := by
  rw [show A10K2.u2390 = KTree.node A10K2.t2396 (nat_lit 41456140) (nat_lit 10989989318) (nat_lit 0) A10K2.t2397 from rfl, allE_node, rows2396, irow2390, rows2397]
  all_goals rfl

theorem atot2390 : totK PA10K2 A10K2.u2390 = [0, 0, 655658349622, 2887721060328, 4120943171888, 2049201882781, 298068997950, 7237400819, 0, 0] := by
  rw [show A10K2.u2390 = KTree.node A10K2.t2396 (nat_lit 41456140) (nat_lit 10989989318) (nat_lit 0) A10K2.t2397 from rfl, totK_node, tot2396, tot2397]
  decide +kernel

theorem arows2391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2391 = true := by
  rw [show A10K2.u2391 = KTree.node A10K2.t2398 (nat_lit 41480179) (nat_lit 8194827383) (nat_lit 0) A10K2.t2399 from rfl, allE_node, rows2398, irow2391, rows2399]
  all_goals rfl

theorem atot2391 : totK PA10K2 A10K2.u2391 = [0, 548589231577, 2325082926948, 3581618242396, 2672223703002, 795202163173, 57551169768, 0, 0, 0] := by
  rw [show A10K2.u2391 = KTree.node A10K2.t2398 (nat_lit 41480179) (nat_lit 8194827383) (nat_lit 0) A10K2.t2399 from rfl, totK_node, tot2398, tot2399]
  decide +kernel

end QECKChecks.A10K2
