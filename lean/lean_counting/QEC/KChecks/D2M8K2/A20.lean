import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A19

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows15228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15228 = true := by
  rw [show D2M8K2.u15228 = KTree.node D2M8K2.u15226 (nat_lit 33102806) (nat_lit 1951938130) (nat_lit 0) D2M8K2.u15227 from rfl, allE_node, arows15226, irow15228, arows15227]
  all_goals rfl

theorem atot15228 : totK PD2M8K2 D2M8K2.u15228 = [0, 0, 414966268661, 1518118808225, 1417043086129, 215892743932, 5352208004, 0] := by
  rw [show D2M8K2.u15228 = KTree.node D2M8K2.u15226 (nat_lit 33102806) (nat_lit 1951938130) (nat_lit 0) D2M8K2.u15227 from rfl, totK_node, atot15226, atot15227]
  decide +kernel

theorem arows15231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15231 = true := by
  rw [show D2M8K2.u15231 = KTree.node D2M8K2.u15229 (nat_lit 33106373) (nat_lit 2292441303) (nat_lit 0) D2M8K2.u15230 from rfl, allE_node, arows15229, irow15231, arows15230]
  all_goals rfl

theorem atot15231 : totK PD2M8K2 D2M8K2.u15231 = [0, 0, 415180659811, 1522746595665, 1419765110120, 217303973999, 5408826336, 0] := by
  rw [show D2M8K2.u15231 = KTree.node D2M8K2.u15229 (nat_lit 33106373) (nat_lit 2292441303) (nat_lit 0) D2M8K2.u15230 from rfl, totK_node, atot15229, atot15230]
  decide +kernel

theorem arows15235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15235 = true := by
  rw [show D2M8K2.u15235 = KTree.node D2M8K2.u15233 (nat_lit 33109697) (nat_lit 2219482276) (nat_lit 0) D2M8K2.u15234 from rfl, allE_node, arows15233, irow15235, arows15234]
  all_goals rfl

theorem atot15235 : totK PD2M8K2 D2M8K2.u15235 = [0, 0, 483867376649, 1637278906403, 1303031045418, 130015453657, 1096505104, 0] := by
  rw [show D2M8K2.u15235 = KTree.node D2M8K2.u15233 (nat_lit 33109697) (nat_lit 2219482276) (nat_lit 0) D2M8K2.u15234 from rfl, totK_node, atot15233, atot15234]
  decide +kernel

theorem arows15238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15238 = true := by
  rw [show D2M8K2.u15238 = KTree.node D2M8K2.u15236 (nat_lit 33113712) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u15237 from rfl, allE_node, arows15236, irow15238, arows15237]
  all_goals rfl

theorem atot15238 : totK PD2M8K2 D2M8K2.u15238 = [0, 0, 332761069974, 1318483924871, 1504010897620, 387743308952, 21771963874, 0] := by
  rw [show D2M8K2.u15238 = KTree.node D2M8K2.u15236 (nat_lit 33113712) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u15237 from rfl, totK_node, atot15236, atot15237]
  decide +kernel

theorem arows15243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15243 = true := by
  rw [show D2M8K2.u15243 = KTree.node D2M8K2.u15241 (nat_lit 33116982) (nat_lit 3673672734) (nat_lit 0) D2M8K2.u15242 from rfl, allE_node, arows15241, irow15243, arows15242]
  all_goals rfl

theorem atot15243 : totK PD2M8K2 D2M8K2.u15243 = [0, 0, 0, 500958668356, 1701070247669, 1137971607771, 130987888018, 1369150432] := by
  rw [show D2M8K2.u15243 = KTree.node D2M8K2.u15241 (nat_lit 33116982) (nat_lit 3673672734) (nat_lit 0) D2M8K2.u15242 from rfl, totK_node, atot15241, atot15242]
  decide +kernel

theorem arows15246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15246 = true := by
  rw [show D2M8K2.u15246 = KTree.node D2M8K2.u15244 (nat_lit 33126121) (nat_lit 1263548408) (nat_lit 0) D2M8K2.u15245 from rfl, allE_node, arows15244, irow15246, arows15245]
  all_goals rfl

theorem atot15246 : totK PD2M8K2 D2M8K2.u15246 = [0, 0, 0, 852565328217, 1964556642602, 656206750182, 30696493668, 0] := by
  rw [show D2M8K2.u15246 = KTree.node D2M8K2.u15244 (nat_lit 33126121) (nat_lit 1263548408) (nat_lit 0) D2M8K2.u15245 from rfl, totK_node, atot15244, atot15245]
  decide +kernel

theorem arows15250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15250 = true := by
  rw [show D2M8K2.u15250 = KTree.node D2M8K2.u15248 (nat_lit 33133292) (nat_lit 2165469665) (nat_lit 0) D2M8K2.u15249 from rfl, allE_node, arows15248, irow15250, arows15249]
  all_goals rfl

theorem atot15250 : totK PD2M8K2 D2M8K2.u15250 = [0, 0, 179595312347, 1043986199565, 1741758332687, 558261064874, 25834701992, 0] := by
  rw [show D2M8K2.u15250 = KTree.node D2M8K2.u15248 (nat_lit 33133292) (nat_lit 2165469665) (nat_lit 0) D2M8K2.u15249 from rfl, totK_node, atot15248, atot15249]
  decide +kernel

theorem arows15253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15253 = true := by
  rw [show D2M8K2.u15253 = KTree.node D2M8K2.u15251 (nat_lit 33179576) (nat_lit 3682918158) (nat_lit 0) D2M8K2.u15252 from rfl, allE_node, arows15251, irow15253, arows15252]
  all_goals rfl

theorem atot15253 : totK PD2M8K2 D2M8K2.u15253 = [0, 0, 416276928871, 1567507515002, 1411992874905, 186392722184, 1369150432, 0] := by
  rw [show D2M8K2.u15253 = KTree.node D2M8K2.u15251 (nat_lit 33179576) (nat_lit 3682918158) (nat_lit 0) D2M8K2.u15252 from rfl, totK_node, atot15251, atot15252]
  decide +kernel

theorem arows15259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15259 = true := by
  rw [show D2M8K2.u15259 = KTree.node D2M8K2.u15257 (nat_lit 33184580) (nat_lit 3320357973) (nat_lit 0) D2M8K2.u15258 from rfl, allE_node, arows15257, irow15259, arows15258]
  all_goals rfl

theorem atot15259 : totK PD2M8K2 D2M8K2.u15259 = [0, 0, 570814407717, 1716099932146, 1217135652494, 155185604497, 1527735764, 0] := by
  rw [show D2M8K2.u15259 = KTree.node D2M8K2.u15257 (nat_lit 33184580) (nat_lit 3320357973) (nat_lit 0) D2M8K2.u15258 from rfl, totK_node, atot15257, atot15258]
  decide +kernel

theorem arows15262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15262 = true := by
  rw [show D2M8K2.u15262 = KTree.node D2M8K2.u15260 (nat_lit 33191482) (nat_lit 3590263183) (nat_lit 0) D2M8K2.u15261 from rfl, allE_node, arows15260, irow15262, arows15261]
  all_goals rfl

theorem atot15262 : totK PD2M8K2 D2M8K2.u15262 = [0, 0, 397852796650, 1526357081973, 1433295076817, 233306988321, 5398830306, 0] := by
  rw [show D2M8K2.u15262 = KTree.node D2M8K2.u15260 (nat_lit 33191482) (nat_lit 3590263183) (nat_lit 0) D2M8K2.u15261 from rfl, totK_node, atot15260, atot15261]
  decide +kernel

theorem arows15266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15266 = true := by
  rw [show D2M8K2.u15266 = KTree.node D2M8K2.u15264 (nat_lit 33195377) (nat_lit 1734587283) (nat_lit 0) D2M8K2.u15265 from rfl, allE_node, arows15264, irow15266, arows15265]
  all_goals rfl

theorem atot15266 : totK PD2M8K2 D2M8K2.u15266 = [0, 0, 415975907804, 1550542699598, 1447508851608, 198736782707, 2328903425, 0] := by
  rw [show D2M8K2.u15266 = KTree.node D2M8K2.u15264 (nat_lit 33195377) (nat_lit 1734587283) (nat_lit 0) D2M8K2.u15265 from rfl, totK_node, atot15264, atot15265]
  decide +kernel

theorem arows15269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15269 = true := by
  rw [show D2M8K2.u15269 = KTree.node D2M8K2.u15267 (nat_lit 33219810) (nat_lit 1542599085) (nat_lit 0) D2M8K2.u15268 from rfl, allE_node, arows15267, irow15269, arows15268]
  all_goals rfl

theorem atot15269 : totK PD2M8K2 D2M8K2.u15269 = [0, 0, 418147218595, 1451473722829, 1367449698734, 312746557497, 13821054428, 0] := by
  rw [show D2M8K2.u15269 = KTree.node D2M8K2.u15267 (nat_lit 33219810) (nat_lit 1542599085) (nat_lit 0) D2M8K2.u15268 from rfl, totK_node, atot15267, atot15268]
  decide +kernel

theorem arows15274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15274 = true := by
  rw [show D2M8K2.u15274 = KTree.node D2M8K2.u15272 (nat_lit 33223663) (nat_lit 2344612426) (nat_lit 0) D2M8K2.u15273 from rfl, allE_node, arows15272, irow15274, arows15273]
  all_goals rfl

theorem atot15274 : totK PD2M8K2 D2M8K2.u15274 = [0, 0, 381862838626, 1558561299260, 1528191445064, 212181747671, 1535615586, 0] := by
  rw [show D2M8K2.u15274 = KTree.node D2M8K2.u15272 (nat_lit 33223663) (nat_lit 2344612426) (nat_lit 0) D2M8K2.u15273 from rfl, totK_node, atot15272, atot15273]
  decide +kernel

theorem arows15277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15277 = true := by
  rw [show D2M8K2.u15277 = KTree.node D2M8K2.u15275 (nat_lit 33231005) (nat_lit 2060685546) (nat_lit 0) D2M8K2.u15276 from rfl, allE_node, arows15275, irow15277, arows15276]
  all_goals rfl

theorem atot15277 : totK PD2M8K2 D2M8K2.u15277 = [0, 0, 420162371525, 1536952428016, 1421255006522, 247535026802, 5436324950, 0] := by
  rw [show D2M8K2.u15277 = KTree.node D2M8K2.u15275 (nat_lit 33231005) (nat_lit 2060685546) (nat_lit 0) D2M8K2.u15276 from rfl, totK_node, atot15275, atot15276]
  decide +kernel

theorem arows15281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15281 = true := by
  rw [show D2M8K2.u15281 = KTree.node D2M8K2.u15279 (nat_lit 33234635) (nat_lit 2735669354) (nat_lit 0) D2M8K2.u15280 from rfl, allE_node, arows15279, irow15281, arows15280]
  all_goals rfl

theorem atot15281 : totK PD2M8K2 D2M8K2.u15281 = [0, 0, 511253821508, 1686979219457, 1269683970449, 121920073589, 1096505104, 0] := by
  rw [show D2M8K2.u15281 = KTree.node D2M8K2.u15279 (nat_lit 33234635) (nat_lit 2735669354) (nat_lit 0) D2M8K2.u15280 from rfl, totK_node, atot15279, atot15280]
  decide +kernel

theorem arows15284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15284 = true := by
  rw [show D2M8K2.u15284 = KTree.node D2M8K2.u15282 (nat_lit 33238433) (nat_lit 1706869009) (nat_lit 0) D2M8K2.u15283 from rfl, allE_node, arows15282, irow15284, arows15283]
  all_goals rfl

theorem atot15284 : totK PD2M8K2 D2M8K2.u15284 = [0, 0, 425086696153, 1455358473265, 1407877799207, 319238449348, 13714665880, 0] := by
  rw [show D2M8K2.u15284 = KTree.node D2M8K2.u15282 (nat_lit 33238433) (nat_lit 1706869009) (nat_lit 0) D2M8K2.u15283 from rfl, totK_node, atot15282, atot15283]
  decide +kernel

theorem arows15291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15291 = true := by
  rw [show D2M8K2.u15291 = KTree.node D2M8K2.u15289 (nat_lit 33262854) (nat_lit 2804775578) (nat_lit 0) D2M8K2.u15290 from rfl, allE_node, arows15289, irow15291, arows15290]
  all_goals rfl

theorem atot15291 : totK PD2M8K2 D2M8K2.u15291 = [0, 0, 477390986520, 1619286790756, 1343902710118, 143507879532, 1369150432, 0] := by
  rw [show D2M8K2.u15291 = KTree.node D2M8K2.u15289 (nat_lit 33262854) (nat_lit 2804775578) (nat_lit 0) D2M8K2.u15290 from rfl, totK_node, atot15289, atot15290]
  decide +kernel

theorem arows15294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15294 = true := by
  rw [show D2M8K2.u15294 = KTree.node D2M8K2.u15292 (nat_lit 33270363) (nat_lit 3744811825) (nat_lit 0) D2M8K2.u15293 from rfl, allE_node, arows15292, irow15294, arows15293]
  all_goals rfl

theorem atot15294 : totK PD2M8K2 D2M8K2.u15294 = [0, 0, 495883097628, 1660189082868, 1293618906653, 137542460028, 1164319620, 0] := by
  rw [show D2M8K2.u15294 = KTree.node D2M8K2.u15292 (nat_lit 33270363) (nat_lit 3744811825) (nat_lit 0) D2M8K2.u15293 from rfl, totK_node, atot15292, atot15293]
  decide +kernel

theorem arows15298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15298 = true := by
  rw [show D2M8K2.u15298 = KTree.node D2M8K2.u15296 (nat_lit 33274454) (nat_lit 3132936133) (nat_lit 0) D2M8K2.u15297 from rfl, allE_node, arows15296, irow15298, arows15297]
  all_goals rfl

theorem atot15298 : totK PD2M8K2 D2M8K2.u15298 = [0, 0, 491027067740, 1651561200601, 1307147887906, 138607701839, 1198073392, 0] := by
  rw [show D2M8K2.u15298 = KTree.node D2M8K2.u15296 (nat_lit 33274454) (nat_lit 3132936133) (nat_lit 0) D2M8K2.u15297 from rfl, totK_node, atot15296, atot15297]
  decide +kernel

theorem arows15301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15301 = true := by
  rw [show D2M8K2.u15301 = KTree.node D2M8K2.u15299 (nat_lit 33302619) (nat_lit 3445022857) (nat_lit 0) D2M8K2.u15300 from rfl, allE_node, arows15299, irow15301, arows15300]
  all_goals rfl

theorem atot15301 : totK PD2M8K2 D2M8K2.u15301 = [0, 0, 420136633399, 1630380739339, 1378400228036, 147331919548, 1096505104, 0] := by
  rw [show D2M8K2.u15301 = KTree.node D2M8K2.u15299 (nat_lit 33302619) (nat_lit 3445022857) (nat_lit 0) D2M8K2.u15300 from rfl, totK_node, atot15299, atot15300]
  decide +kernel

theorem arows15306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15306 = true := by
  rw [show D2M8K2.u15306 = KTree.node D2M8K2.u15304 (nat_lit 33306202) (nat_lit 3732917961) (nat_lit 0) D2M8K2.u15305 from rfl, allE_node, arows15304, irow15306, arows15305]
  all_goals rfl

theorem atot15306 : totK PD2M8K2 D2M8K2.u15306 = [0, 0, 347812456902, 1493058027773, 1589242079429, 253218359012, 2771166413, 0] := by
  rw [show D2M8K2.u15306 = KTree.node D2M8K2.u15304 (nat_lit 33306202) (nat_lit 3732917961) (nat_lit 0) D2M8K2.u15305 from rfl, totK_node, atot15304, atot15305]
  decide +kernel

theorem arows15309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15309 = true := by
  rw [show D2M8K2.u15309 = KTree.node D2M8K2.u15307 (nat_lit 33309760) (nat_lit 3289551508) (nat_lit 0) D2M8K2.u15308 from rfl, allE_node, arows15307, irow15309, arows15308]
  all_goals rfl

theorem atot15309 : totK PD2M8K2 D2M8K2.u15309 = [0, 0, 412109869931, 1413969860942, 1426685629061, 344831029089, 13312069015, 0] := by
  rw [show D2M8K2.u15309 = KTree.node D2M8K2.u15307 (nat_lit 33309760) (nat_lit 3289551508) (nat_lit 0) D2M8K2.u15308 from rfl, totK_node, atot15307, atot15308]
  decide +kernel

theorem arows15313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15313 = true := by
  rw [show D2M8K2.u15313 = KTree.node D2M8K2.u15311 (nat_lit 33313635) (nat_lit 2851363495) (nat_lit 0) D2M8K2.u15312 from rfl, allE_node, arows15311, irow15313, arows15312]
  all_goals rfl

theorem atot15313 : totK PD2M8K2 D2M8K2.u15313 = [0, 0, 412353775687, 1526260325282, 1447406483953, 235106216386, 5193381917, 0] := by
  rw [show D2M8K2.u15313 = KTree.node D2M8K2.u15311 (nat_lit 33313635) (nat_lit 2851363495) (nat_lit 0) D2M8K2.u15312 from rfl, totK_node, atot15311, atot15312]
  decide +kernel

theorem arows15316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15316 = true := by
  rw [show D2M8K2.u15316 = KTree.node D2M8K2.u15314 (nat_lit 33320330) (nat_lit 4193211049) (nat_lit 0) D2M8K2.u15315 from rfl, allE_node, arows15314, irow15316, arows15315]
  all_goals rfl

theorem atot15316 : totK PD2M8K2 D2M8K2.u15316 = [0, 0, 441963102691, 1536929014051, 1410641893421, 258363225246, 4882834716, 0] := by
  rw [show D2M8K2.u15316 = KTree.node D2M8K2.u15314 (nat_lit 33320330) (nat_lit 4193211049) (nat_lit 0) D2M8K2.u15315 from rfl, totK_node, atot15314, atot15315]
  decide +kernel

theorem arows15322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15322 = true := by
  rw [show D2M8K2.u15322 = KTree.node D2M8K2.u15320 (nat_lit 33389382) (nat_lit 3872665113) (nat_lit 0) D2M8K2.u15321 from rfl, allE_node, arows15320, irow15322, arows15321]
  all_goals rfl

theorem atot15322 : totK PD2M8K2 D2M8K2.u15322 = [0, 449442817316, 1307803878311, 1081666246852, 593080573971, 221435012113, 17014456371, 0] := by
  rw [show D2M8K2.u15322 = KTree.node D2M8K2.u15320 (nat_lit 33389382) (nat_lit 3872665113) (nat_lit 0) D2M8K2.u15321 from rfl, totK_node, atot15320, atot15321]
  decide +kernel

theorem arows15325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15325 = true := by
  rw [show D2M8K2.u15325 = KTree.node D2M8K2.u15323 (nat_lit 33392188) (nat_lit 3937950544) (nat_lit 0) D2M8K2.u15324 from rfl, allE_node, arows15323, irow15325, arows15324]
  all_goals rfl

theorem atot15325 : totK PD2M8K2 D2M8K2.u15325 = [0, 420106413946, 1376770702482, 1389113489923, 427680618349, 16208961603, 0, 0] := by
  rw [show D2M8K2.u15325 = KTree.node D2M8K2.u15323 (nat_lit 33392188) (nat_lit 3937950544) (nat_lit 0) D2M8K2.u15324 from rfl, totK_node, atot15323, atot15324]
  decide +kernel

theorem arows15329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15329 = true := by
  rw [show D2M8K2.u15329 = KTree.node D2M8K2.u15327 (nat_lit 33395481) (nat_lit 1496120418) (nat_lit 0) D2M8K2.u15328 from rfl, allE_node, arows15327, irow15329, arows15328]
  all_goals rfl

theorem atot15329 : totK PD2M8K2 D2M8K2.u15329 = [0, 420335746920, 1456241746718, 1400447922476, 315103370040, 11619426831, 0, 0] := by
  rw [show D2M8K2.u15329 = KTree.node D2M8K2.u15327 (nat_lit 33395481) (nat_lit 1496120418) (nat_lit 0) D2M8K2.u15328 from rfl, totK_node, atot15327, atot15328]
  decide +kernel

theorem arows15332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15332 = true := by
  rw [show D2M8K2.u15332 = KTree.node D2M8K2.u15330 (nat_lit 33398867) (nat_lit 2166840958) (nat_lit 0) D2M8K2.u15331 from rfl, allE_node, arows15330, irow15332, arows15331]
  all_goals rfl

theorem atot15332 : totK PD2M8K2 D2M8K2.u15332 = [0, 401950222738, 1421886310351, 1423550980035, 336457659845, 11778552896, 0, 0] := by
  rw [show D2M8K2.u15332 = KTree.node D2M8K2.u15330 (nat_lit 33398867) (nat_lit 2166840958) (nat_lit 0) D2M8K2.u15331 from rfl, totK_node, atot15330, atot15331]
  decide +kernel

theorem arows15337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15337 = true := by
  rw [show D2M8K2.u15337 = KTree.node D2M8K2.u15335 (nat_lit 33402573) (nat_lit 1449435006) (nat_lit 0) D2M8K2.u15336 from rfl, allE_node, arows15335, irow15337, arows15336]
  all_goals rfl

theorem atot15337 : totK PD2M8K2 D2M8K2.u15337 = [0, 425933657684, 1571835803392, 1424115409753, 226996471899, 2585032425, 0, 0] := by
  rw [show D2M8K2.u15337 = KTree.node D2M8K2.u15335 (nat_lit 33402573) (nat_lit 1449435006) (nat_lit 0) D2M8K2.u15336 from rfl, totK_node, atot15335, atot15336]
  decide +kernel

theorem arows15340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15340 = true := by
  rw [show D2M8K2.u15340 = KTree.node D2M8K2.u15338 (nat_lit 33405688) (nat_lit 3332910879) (nat_lit 0) D2M8K2.u15339 from rfl, allE_node, arows15338, irow15340, arows15339]
  all_goals rfl

theorem atot15340 : totK PD2M8K2 D2M8K2.u15340 = [0, 0, 777419715181, 1898288840451, 893756632471, 59431258179, 0, 0] := by
  rw [show D2M8K2.u15340 = KTree.node D2M8K2.u15338 (nat_lit 33405688) (nat_lit 3332910879) (nat_lit 0) D2M8K2.u15339 from rfl, totK_node, atot15338, atot15339]
  decide +kernel

theorem arows15344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15344 = true := by
  rw [show D2M8K2.u15344 = KTree.node D2M8K2.u15342 (nat_lit 33412067) (nat_lit 2323206573) (nat_lit 0) D2M8K2.u15343 from rfl, allE_node, arows15342, irow15344, arows15343]
  all_goals rfl

theorem atot15344 : totK PD2M8K2 D2M8K2.u15344 = [0, 0, 322585227726, 1215911769288, 1492995531311, 563957048925, 36921873854, 0] := by
  rw [show D2M8K2.u15344 = KTree.node D2M8K2.u15342 (nat_lit 33412067) (nat_lit 2323206573) (nat_lit 0) D2M8K2.u15343 from rfl, totK_node, atot15342, atot15343]
  decide +kernel

theorem arows15347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15347 = true := by
  rw [show D2M8K2.u15347 = KTree.node D2M8K2.u15345 (nat_lit 33415159) (nat_lit 855286398) (nat_lit 0) D2M8K2.u15346 from rfl, allE_node, arows15345, irow15347, arows15346]
  all_goals rfl

theorem atot15347 : totK PD2M8K2 D2M8K2.u15347 = [0, 0, 418346517339, 1525969753943, 1403957401355, 242873427770, 5159868635, 0] := by
  rw [show D2M8K2.u15347 = KTree.node D2M8K2.u15345 (nat_lit 33415159) (nat_lit 855286398) (nat_lit 0) D2M8K2.u15346 from rfl, totK_node, atot15345, atot15346]
  decide +kernel

theorem arows15358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15358 = true := by
  rw [show D2M8K2.u15358 = KTree.node D2M8K2.u15356 (nat_lit 33418984) (nat_lit 3411623718) (nat_lit 0) D2M8K2.u15357 from rfl, allE_node, arows15356, irow15358, arows15357]
  all_goals rfl

theorem atot15358 : totK PD2M8K2 D2M8K2.u15358 = [0, 0, 447922926863, 1536729365909, 1349940247896, 242433587342, 5218872685, 0] := by
  rw [show D2M8K2.u15358 = KTree.node D2M8K2.u15356 (nat_lit 33418984) (nat_lit 3411623718) (nat_lit 0) D2M8K2.u15357 from rfl, totK_node, atot15356, atot15357]
  decide +kernel

theorem arows15361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15361 = true := by
  rw [show D2M8K2.u15361 = KTree.node D2M8K2.u15359 (nat_lit 33422575) (nat_lit 1735057362) (nat_lit 0) D2M8K2.u15360 from rfl, allE_node, arows15359, irow15361, arows15360]
  all_goals rfl

theorem atot15361 : totK PD2M8K2 D2M8K2.u15361 = [0, 0, 471246010530, 1634276556693, 1352912668382, 169438295087, 1415142070, 0] := by
  rw [show D2M8K2.u15361 = KTree.node D2M8K2.u15359 (nat_lit 33422575) (nat_lit 1735057362) (nat_lit 0) D2M8K2.u15360 from rfl, totK_node, atot15359, atot15360]
  decide +kernel

theorem arows15365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15365 = true := by
  rw [show D2M8K2.u15365 = KTree.node D2M8K2.u15363 (nat_lit 33426314) (nat_lit 4134472591) (nat_lit 0) D2M8K2.u15364 from rfl, allE_node, arows15363, irow15365, arows15364]
  all_goals rfl

theorem atot15365 : totK PD2M8K2 D2M8K2.u15365 = [0, 325398345861, 920506206517, 1061300117815, 994986778103, 285723302859, 9302370699, 0] := by
  rw [show D2M8K2.u15365 = KTree.node D2M8K2.u15363 (nat_lit 33426314) (nat_lit 4134472591) (nat_lit 0) D2M8K2.u15364 from rfl, totK_node, atot15363, atot15364]
  decide +kernel

theorem arows15368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15368 = true := by
  rw [show D2M8K2.u15368 = KTree.node D2M8K2.u15366 (nat_lit 33430666) (nat_lit 3924853953) (nat_lit 0) D2M8K2.u15367 from rfl, allE_node, arows15366, irow15368, arows15367]
  all_goals rfl

theorem atot15368 : totK PD2M8K2 D2M8K2.u15368 = [0, 428948337720, 1496982186302, 1399208277430, 307702610866, 18552171439, 0, 0] := by
  rw [show D2M8K2.u15368 = KTree.node D2M8K2.u15366 (nat_lit 33430666) (nat_lit 3924853953) (nat_lit 0) D2M8K2.u15367 from rfl, totK_node, atot15366, atot15367]
  decide +kernel

theorem arows15373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15373 = true := by
  rw [show D2M8K2.u15373 = KTree.node D2M8K2.u15371 (nat_lit 33433466) (nat_lit 3327984632) (nat_lit 0) D2M8K2.u15372 from rfl, allE_node, arows15371, irow15373, arows15372]
  all_goals rfl

theorem atot15373 : totK PD2M8K2 D2M8K2.u15373 = [0, 438381136503, 1379675489808, 1346982409601, 444028874831, 20414095810, 0, 0] := by
  rw [show D2M8K2.u15373 = KTree.node D2M8K2.u15371 (nat_lit 33433466) (nat_lit 3327984632) (nat_lit 0) D2M8K2.u15372 from rfl, totK_node, atot15371, atot15372]
  decide +kernel

theorem arows15376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15376 = true := by
  rw [show D2M8K2.u15376 = KTree.node D2M8K2.u15374 (nat_lit 33436606) (nat_lit 3828572643) (nat_lit 0) D2M8K2.u15375 from rfl, allE_node, arows15374, irow15376, arows15375]
  all_goals rfl

theorem atot15376 : totK PD2M8K2 D2M8K2.u15376 = [0, 382184329876, 1411964962615, 1467159247809, 337587386197, 13049727234, 0, 0] := by
  rw [show D2M8K2.u15376 = KTree.node D2M8K2.u15374 (nat_lit 33436606) (nat_lit 3828572643) (nat_lit 0) D2M8K2.u15375 from rfl, totK_node, atot15374, atot15375]
  decide +kernel

theorem arows15380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15380 = true := by
  rw [show D2M8K2.u15380 = KTree.node D2M8K2.u15378 (nat_lit 33444065) (nat_lit 2202242593) (nat_lit 0) D2M8K2.u15379 from rfl, allE_node, arows15378, irow15380, arows15379]
  all_goals rfl

theorem atot15380 : totK PD2M8K2 D2M8K2.u15380 = [0, 418584527484, 1591933597985, 1424684591588, 210569726663, 3884009855, 0, 0] := by
  rw [show D2M8K2.u15380 = KTree.node D2M8K2.u15378 (nat_lit 33444065) (nat_lit 2202242593) (nat_lit 0) D2M8K2.u15379 from rfl, totK_node, atot15378, atot15379]
  decide +kernel

theorem arows15383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15383 = true := by
  rw [show D2M8K2.u15383 = KTree.node D2M8K2.u15381 (nat_lit 33447270) (nat_lit 2670290799) (nat_lit 0) D2M8K2.u15382 from rfl, allE_node, arows15381, irow15383, arows15382]
  all_goals rfl

theorem atot15383 : totK PD2M8K2 D2M8K2.u15383 = [0, 0, 677318167881, 1798366651394, 968800813983, 97955607515, 1206465782, 0] := by
  rw [show D2M8K2.u15383 = KTree.node D2M8K2.u15381 (nat_lit 33447270) (nat_lit 2670290799) (nat_lit 0) D2M8K2.u15382 from rfl, totK_node, atot15381, atot15382]
  decide +kernel

theorem arows15389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15389 = true := by
  rw [show D2M8K2.u15389 = KTree.node D2M8K2.u15387 (nat_lit 33451737) (nat_lit 1862188859) (nat_lit 0) D2M8K2.u15388 from rfl, allE_node, arows15387, irow15389, arows15388]
  all_goals rfl

theorem atot15389 : totK PD2M8K2 D2M8K2.u15389 = [0, 0, 635331766411, 1788069020444, 1116917426066, 99416346364, 0, 0] := by
  rw [show D2M8K2.u15389 = KTree.node D2M8K2.u15387 (nat_lit 33451737) (nat_lit 1862188859) (nat_lit 0) D2M8K2.u15388 from rfl, totK_node, atot15387, atot15388]
  decide +kernel

theorem arows15392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15392 = true := by
  rw [show D2M8K2.u15392 = KTree.node D2M8K2.u15390 (nat_lit 33456391) (nat_lit 1402878040) (nat_lit 0) D2M8K2.u15391 from rfl, allE_node, arows15390, irow15392, arows15391]
  all_goals rfl

theorem atot15392 : totK PD2M8K2 D2M8K2.u15392 = [0, 0, 415792357929, 1483350872756, 1353726705562, 284961562072, 9467545976, 0] := by
  rw [show D2M8K2.u15392 = KTree.node D2M8K2.u15390 (nat_lit 33456391) (nat_lit 1402878040) (nat_lit 0) D2M8K2.u15391 from rfl, totK_node, atot15390, atot15391]
  decide +kernel

theorem arows15396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15396 = true := by
  rw [show D2M8K2.u15396 = KTree.node D2M8K2.u15394 (nat_lit 33463921) (nat_lit 1442371810) (nat_lit 0) D2M8K2.u15395 from rfl, allE_node, arows15394, irow15396, arows15395]
  all_goals rfl

theorem atot15396 : totK PD2M8K2 D2M8K2.u15396 = [0, 0, 520361646590, 1715596374620, 1216911231346, 131641220243, 1330264907, 0] := by
  rw [show D2M8K2.u15396 = KTree.node D2M8K2.u15394 (nat_lit 33463921) (nat_lit 1442371810) (nat_lit 0) D2M8K2.u15395 from rfl, totK_node, atot15394, atot15395]
  decide +kernel

theorem arows15399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15399 = true := by
  rw [show D2M8K2.u15399 = KTree.node D2M8K2.u15397 (nat_lit 33469404) (nat_lit 3123615032) (nat_lit 0) D2M8K2.u15398 from rfl, allE_node, arows15397, irow15399, arows15398]
  all_goals rfl

theorem atot15399 : totK PD2M8K2 D2M8K2.u15399 = [0, 419114938304, 1472335138122, 1396260470667, 332755511794, 17666192220, 0, 0] := by
  rw [show D2M8K2.u15399 = KTree.node D2M8K2.u15397 (nat_lit 33469404) (nat_lit 3123615032) (nat_lit 0) D2M8K2.u15398 from rfl, totK_node, atot15397, atot15398]
  decide +kernel

theorem arows15404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15404 = true := by
  rw [show D2M8K2.u15404 = KTree.node D2M8K2.u15402 (nat_lit 33473441) (nat_lit 2091409177) (nat_lit 0) D2M8K2.u15403 from rfl, allE_node, arows15402, irow15404, arows15403]
  all_goals rfl

theorem atot15404 : totK PD2M8K2 D2M8K2.u15404 = [0, 335420412233, 1301777439954, 1470496358366, 495267654851, 30795354140, 0, 0] := by
  rw [show D2M8K2.u15404 = KTree.node D2M8K2.u15402 (nat_lit 33473441) (nat_lit 2091409177) (nat_lit 0) D2M8K2.u15403 from rfl, totK_node, atot15402, atot15403]
  decide +kernel

theorem arows15407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15407 = true := by
  rw [show D2M8K2.u15407 = KTree.node D2M8K2.u15405 (nat_lit 33479599) (nat_lit 2068016384) (nat_lit 0) D2M8K2.u15406 from rfl, allE_node, arows15405, irow15407, arows15406]
  all_goals rfl

theorem atot15407 : totK PD2M8K2 D2M8K2.u15407 = [0, 438575211120, 1451793888049, 1363055059703, 352800500757, 16468471291, 0, 0] := by
  rw [show D2M8K2.u15407 = KTree.node D2M8K2.u15405 (nat_lit 33479599) (nat_lit 2068016384) (nat_lit 0) D2M8K2.u15406 from rfl, totK_node, atot15405, atot15406]
  decide +kernel

theorem arows15411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15411 = true := by
  rw [show D2M8K2.u15411 = KTree.node D2M8K2.u15409 (nat_lit 33482768) (nat_lit 3691383965) (nat_lit 0) D2M8K2.u15410 from rfl, allE_node, arows15409, irow15411, arows15410]
  all_goals rfl

theorem atot15411 : totK PD2M8K2 D2M8K2.u15411 = [0, 406527518314, 1490453839930, 1439312706054, 275932175941, 7465959684, 0, 0] := by
  rw [show D2M8K2.u15411 = KTree.node D2M8K2.u15409 (nat_lit 33482768) (nat_lit 3691383965) (nat_lit 0) D2M8K2.u15410 from rfl, totK_node, atot15409, atot15410]
  decide +kernel

theorem arows15414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15414 = true := by
  rw [show D2M8K2.u15414 = KTree.node D2M8K2.u15412 (nat_lit 33486761) (nat_lit 1613839664) (nat_lit 0) D2M8K2.u15413 from rfl, allE_node, arows15412, irow15414, arows15413]
  all_goals rfl

theorem atot15414 : totK PD2M8K2 D2M8K2.u15414 = [0, 394405686972, 1462070917013, 1450377364977, 329917332693, 8684770685, 0, 0] := by
  rw [show D2M8K2.u15414 = KTree.node D2M8K2.u15412 (nat_lit 33486761) (nat_lit 1613839664) (nat_lit 0) D2M8K2.u15413 from rfl, totK_node, atot15412, atot15413]
  decide +kernel

theorem arows15421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15421 = true := by
  rw [show D2M8K2.u15421 = KTree.node D2M8K2.u15419 (nat_lit 33490366) (nat_lit 3738227693) (nat_lit 0) D2M8K2.u15420 from rfl, allE_node, arows15419, irow15421, arows15420]
  all_goals rfl

theorem atot15421 : totK PD2M8K2 D2M8K2.u15421 = [0, 0, 490286406710, 1658439511854, 1269631972590, 153341961658, 1239866073, 0] := by
  rw [show D2M8K2.u15421 = KTree.node D2M8K2.u15419 (nat_lit 33490366) (nat_lit 3738227693) (nat_lit 0) D2M8K2.u15420 from rfl, totK_node, atot15419, atot15420]
  decide +kernel

theorem arows15424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15424 = true := by
  rw [show D2M8K2.u15424 = KTree.node D2M8K2.u15422 (nat_lit 33499382) (nat_lit 3999417673) (nat_lit 0) D2M8K2.u15423 from rfl, allE_node, arows15422, irow15424, arows15423]
  all_goals rfl

theorem atot15424 : totK PD2M8K2 D2M8K2.u15424 = [0, 0, 698865798155, 1848326515190, 1002872555488, 73273936268, 0, 0] := by
  rw [show D2M8K2.u15424 = KTree.node D2M8K2.u15422 (nat_lit 33499382) (nat_lit 3999417673) (nat_lit 0) D2M8K2.u15423 from rfl, totK_node, atot15422, atot15423]
  decide +kernel

theorem arows15428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15428 = true := by
  rw [show D2M8K2.u15428 = KTree.node D2M8K2.u15426 (nat_lit 33502804) (nat_lit 3927732617) (nat_lit 0) D2M8K2.u15427 from rfl, allE_node, arows15426, irow15428, arows15427]
  all_goals rfl

theorem atot15428 : totK PD2M8K2 D2M8K2.u15428 = [0, 0, 381429296974, 1479377389252, 1409905608316, 288008500562, 9527367360, 0] := by
  rw [show D2M8K2.u15428 = KTree.node D2M8K2.u15426 (nat_lit 33502804) (nat_lit 3927732617) (nat_lit 0) D2M8K2.u15427 from rfl, totK_node, atot15426, atot15427]
  decide +kernel

theorem arows15431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15431 = true := by
  rw [show D2M8K2.u15431 = KTree.node D2M8K2.u15429 (nat_lit 33506662) (nat_lit 2471593177) (nat_lit 0) D2M8K2.u15430 from rfl, allE_node, arows15429, irow15431, arows15430]
  all_goals rfl

theorem atot15431 : totK PD2M8K2 D2M8K2.u15431 = [0, 180280610855, 808950791921, 1515214943678, 997203836473, 124856981909, 1376099875, 0] := by
  rw [show D2M8K2.u15431 = KTree.node D2M8K2.u15429 (nat_lit 33506662) (nat_lit 2471593177) (nat_lit 0) D2M8K2.u15430 from rfl, totK_node, atot15429, atot15430]
  decide +kernel

theorem arows15436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15436 = true := by
  rw [show D2M8K2.u15436 = KTree.node D2M8K2.u15434 (nat_lit 33515093) (nat_lit 2145833384) (nat_lit 0) D2M8K2.u15435 from rfl, allE_node, arows15434, irow15436, arows15435]
  all_goals rfl

theorem atot15436 : totK PD2M8K2 D2M8K2.u15436 = [0, 301990691332, 1211645611407, 1498640041356, 579651760061, 37601708222, 0, 0] := by
  rw [show D2M8K2.u15436 = KTree.node D2M8K2.u15434 (nat_lit 33515093) (nat_lit 2145833384) (nat_lit 0) D2M8K2.u15435 from rfl, totK_node, atot15434, atot15435]
  decide +kernel

theorem arows15439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15439 = true := by
  rw [show D2M8K2.u15439 = KTree.node D2M8K2.u15437 (nat_lit 33517930) (nat_lit 3961319894) (nat_lit 0) D2M8K2.u15438 from rfl, allE_node, arows15437, irow15439, arows15438]
  all_goals rfl

theorem atot15439 : totK PD2M8K2 D2M8K2.u15439 = [0, 416191135741, 1512302441392, 1383405009175, 282631746410, 11885407614, 0, 0] := by
  rw [show D2M8K2.u15439 = KTree.node D2M8K2.u15437 (nat_lit 33517930) (nat_lit 3961319894) (nat_lit 0) D2M8K2.u15438 from rfl, totK_node, atot15437, atot15438]
  decide +kernel

theorem arows15443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15443 = true := by
  rw [show D2M8K2.u15443 = KTree.node D2M8K2.u15441 (nat_lit 33521556) (nat_lit 3260124361) (nat_lit 0) D2M8K2.u15442 from rfl, allE_node, arows15441, irow15443, arows15442]
  all_goals rfl

theorem atot15443 : totK PD2M8K2 D2M8K2.u15443 = [0, 444070162080, 1508296247829, 1366114516696, 290758178786, 12052611869, 0, 0] := by
  rw [show D2M8K2.u15443 = KTree.node D2M8K2.u15441 (nat_lit 33521556) (nat_lit 3260124361) (nat_lit 0) D2M8K2.u15442 from rfl, totK_node, atot15441, atot15442]
  decide +kernel

theorem arows15446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15446 = true := by
  rw [show D2M8K2.u15446 = KTree.node D2M8K2.u15444 (nat_lit 33525012) (nat_lit 3208754756) (nat_lit 0) D2M8K2.u15445 from rfl, allE_node, arows15444, irow15446, arows15445]
  all_goals rfl

theorem atot15446 : totK PD2M8K2 D2M8K2.u15446 = [0, 315751930257, 1415036807950, 1524693998764, 381994979140, 25815485168, 0, 0] := by
  rw [show D2M8K2.u15446 = KTree.node D2M8K2.u15444 (nat_lit 33525012) (nat_lit 3208754756) (nat_lit 0) D2M8K2.u15445 from rfl, totK_node, atot15444, atot15445]
  decide +kernel

theorem arows15452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15452 = true := by
  rw [show D2M8K2.u15452 = KTree.node D2M8K2.u15450 (nat_lit 33537340) (nat_lit 3937950544) (nat_lit 0) D2M8K2.u15451 from rfl, allE_node, arows15450, irow15452, arows15451]
  all_goals rfl

theorem atot15452 : totK PD2M8K2 D2M8K2.u15452 = [0, 0, 752440165737, 1910166578965, 890401206993, 50436658191, 0, 0] := by
  rw [show D2M8K2.u15452 = KTree.node D2M8K2.u15450 (nat_lit 33537340) (nat_lit 3937950544) (nat_lit 0) D2M8K2.u15451 from rfl, totK_node, atot15450, atot15451]
  decide +kernel

theorem arows15455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15455 = true := by
  rw [show D2M8K2.u15455 = KTree.node D2M8K2.u15453 (nat_lit 33543948) (nat_lit 3603536935) (nat_lit 0) D2M8K2.u15454 from rfl, allE_node, arows15453, irow15455, arows15454]
  all_goals rfl

theorem atot15455 : totK PD2M8K2 D2M8K2.u15455 = [0, 0, 736108402700, 1872906569856, 927687314197, 59829185461, 0, 0] := by
  rw [show D2M8K2.u15455 = KTree.node D2M8K2.u15453 (nat_lit 33543948) (nat_lit 3603536935) (nat_lit 0) D2M8K2.u15454 from rfl, totK_node, atot15453, atot15454]
  decide +kernel

theorem arows15459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15459 = true := by
  rw [show D2M8K2.u15459 = KTree.node D2M8K2.u15457 (nat_lit 33551075) (nat_lit 2357175640) (nat_lit 0) D2M8K2.u15458 from rfl, allE_node, arows15457, irow15459, arows15458]
  all_goals rfl

theorem atot15459 : totK PD2M8K2 D2M8K2.u15459 = [0, 342835346343, 1018369199565, 1253354832904, 835710223030, 131273824455, 1493059870, 0] := by
  rw [show D2M8K2.u15459 = KTree.node D2M8K2.u15457 (nat_lit 33551075) (nat_lit 2357175640) (nat_lit 0) D2M8K2.u15458 from rfl, totK_node, atot15457, atot15458]
  decide +kernel

theorem arows15462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15462 = true := by
  rw [show D2M8K2.u15462 = KTree.node D2M8K2.u15460 (nat_lit 33555330) (nat_lit 3291094432) (nat_lit 0) D2M8K2.u15461 from rfl, allE_node, arows15460, irow15462, arows15461]
  all_goals rfl

theorem atot15462 : totK PD2M8K2 D2M8K2.u15462 = [0, 430864336105, 1508364989791, 1394768573532, 326468641540, 24250117784, 0, 0] := by
  rw [show D2M8K2.u15462 = KTree.node D2M8K2.u15460 (nat_lit 33555330) (nat_lit 3291094432) (nat_lit 0) D2M8K2.u15461 from rfl, totK_node, atot15460, atot15461]
  decide +kernel

theorem arows15467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15467 = true := by
  rw [show D2M8K2.u15467 = KTree.node D2M8K2.u15465 (nat_lit 33558170) (nat_lit 4118934592) (nat_lit 0) D2M8K2.u15466 from rfl, allE_node, arows15465, irow15467, arows15466]
  all_goals rfl

theorem atot15467 : totK PD2M8K2 D2M8K2.u15467 = [0, 414868691538, 1391458957579, 1395019228358, 408678090075, 14503648626, 0, 0] := by
  rw [show D2M8K2.u15467 = KTree.node D2M8K2.u15465 (nat_lit 33558170) (nat_lit 4118934592) (nat_lit 0) D2M8K2.u15466 from rfl, totK_node, atot15465, atot15466]
  decide +kernel

theorem arows15470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15470 = true := by
  rw [show D2M8K2.u15470 = KTree.node D2M8K2.u15468 (nat_lit 33561602) (nat_lit 4073968270) (nat_lit 0) D2M8K2.u15469 from rfl, allE_node, arows15468, irow15470, arows15469]
  all_goals rfl

theorem atot15470 : totK PD2M8K2 D2M8K2.u15470 = [0, 415117285625, 1478341936506, 1427126705626, 300618193628, 10463569636, 0, 0] := by
  rw [show D2M8K2.u15470 = KTree.node D2M8K2.u15468 (nat_lit 33561602) (nat_lit 4073968270) (nat_lit 0) D2M8K2.u15469 from rfl, totK_node, atot15468, atot15469]
  decide +kernel

theorem arows15474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15474 = true := by
  rw [show D2M8K2.u15474 = KTree.node D2M8K2.u15472 (nat_lit 33568472) (nat_lit 3423312568) (nat_lit 0) D2M8K2.u15473 from rfl, allE_node, arows15472, irow15474, arows15473]
  all_goals rfl

theorem atot15474 : totK PD2M8K2 D2M8K2.u15474 = [0, 443433827047, 1490950426723, 1383219229510, 319814055664, 11782027357, 0, 0] := by
  rw [show D2M8K2.u15474 = KTree.node D2M8K2.u15472 (nat_lit 33568472) (nat_lit 3423312568) (nat_lit 0) D2M8K2.u15473 from rfl, totK_node, atot15472, atot15473]
  decide +kernel

theorem arows15477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15477 = true := by
  rw [show D2M8K2.u15477 = KTree.node D2M8K2.u15475 (nat_lit 33571534) (nat_lit 3560417634) (nat_lit 0) D2M8K2.u15476 from rfl, allE_node, arows15475, irow15477, arows15476]
  all_goals rfl

theorem atot15477 : totK PD2M8K2 D2M8K2.u15477 = [0, 0, 763538977394, 1910115976811, 869969084887, 49094443204, 0, 0] := by
  rw [show D2M8K2.u15477 = KTree.node D2M8K2.u15475 (nat_lit 33571534) (nat_lit 3560417634) (nat_lit 0) D2M8K2.u15476 from rfl, totK_node, atot15475, atot15476]
  decide +kernel

theorem arows15485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15485 = true := by
  rw [show D2M8K2.u15485 = KTree.node D2M8K2.u15483 (nat_lit 33575860) (nat_lit 3792735541) (nat_lit 0) D2M8K2.u15484 from rfl, allE_node, arows15483, irow15485, arows15484]
  all_goals rfl

theorem atot15485 : totK PD2M8K2 D2M8K2.u15485 = [0, 0, 573211262210, 1685735914712, 1232847943461, 149665191467, 1310285577, 0] := by
  rw [show D2M8K2.u15485 = KTree.node D2M8K2.u15483 (nat_lit 33575860) (nat_lit 3792735541) (nat_lit 0) D2M8K2.u15484 from rfl, totK_node, atot15483, atot15484]
  decide +kernel

theorem arows15488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15488 = true := by
  rw [show D2M8K2.u15488 = KTree.node D2M8K2.u15486 (nat_lit 33580420) (nat_lit 3911606865) (nat_lit 0) D2M8K2.u15487 from rfl, allE_node, arows15486, irow15488, arows15487]
  all_goals rfl

theorem atot15488 : totK PD2M8K2 D2M8K2.u15488 = [0, 0, 432289520903, 1564837695590, 1362516094143, 221553558762, 4879840392, 0] := by
  rw [show D2M8K2.u15488 = KTree.node D2M8K2.u15486 (nat_lit 33580420) (nat_lit 3911606865) (nat_lit 0) D2M8K2.u15487 from rfl, totK_node, atot15486, atot15487]
  decide +kernel

theorem arows15492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15492 = true := by
  rw [show D2M8K2.u15492 = KTree.node D2M8K2.u15490 (nat_lit 33584098) (nat_lit 4128327083) (nat_lit 0) D2M8K2.u15491 from rfl, allE_node, arows15490, irow15492, arows15491]
  all_goals rfl

theorem atot15492 : totK PD2M8K2 D2M8K2.u15492 = [0, 0, 475235778734, 1578662089325, 1322498566997, 214598432905, 4931404646, 0] := by
  rw [show D2M8K2.u15492 = KTree.node D2M8K2.u15490 (nat_lit 33584098) (nat_lit 4128327083) (nat_lit 0) D2M8K2.u15491 from rfl, totK_node, atot15490, atot15491]
  decide +kernel

theorem arows15495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15495 = true := by
  rw [show D2M8K2.u15495 = KTree.node D2M8K2.u15493 (nat_lit 33591181) (nat_lit 1319347485) (nat_lit 0) D2M8K2.u15494 from rfl, allE_node, arows15493, irow15495, arows15494]
  all_goals rfl

theorem atot15495 : totK PD2M8K2 D2M8K2.u15495 = [0, 161564142879, 542345614271, 1139229781283, 1310536903577, 394602841290, 21751168066, 0] := by
  rw [show D2M8K2.u15495 = KTree.node D2M8K2.u15493 (nat_lit 33591181) (nat_lit 1319347485) (nat_lit 0) D2M8K2.u15494 from rfl, totK_node, atot15493, atot15494]
  decide +kernel

theorem arows15500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15500 = true := by
  rw [show D2M8K2.u15500 = KTree.node D2M8K2.u15498 (nat_lit 33843029) (nat_lit 2138367068) (nat_lit 0) D2M8K2.u15499 from rfl, allE_node, arows15498, irow15500, arows15499]
  all_goals rfl

theorem atot15500 : totK PD2M8K2 D2M8K2.u15500 = [0, 431825658977, 1591186582209, 1381859539770, 190723956201, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15500 = KTree.node D2M8K2.u15498 (nat_lit 33843029) (nat_lit 2138367068) (nat_lit 0) D2M8K2.u15499 from rfl, totK_node, atot15498, atot15499]
  decide +kernel

theorem arows15503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15503 = true := by
  rw [show D2M8K2.u15503 = KTree.node D2M8K2.u15501 (nat_lit 33850129) (nat_lit 1249648390) (nat_lit 0) D2M8K2.u15502 from rfl, allE_node, arows15501, irow15503, arows15502]
  all_goals rfl

theorem atot15503 : totK PD2M8K2 D2M8K2.u15503 = [0, 421883839686, 1437457792140, 1377538210067, 321765469104, 13049727234, 0, 0] := by
  rw [show D2M8K2.u15503 = KTree.node D2M8K2.u15501 (nat_lit 33850129) (nat_lit 1249648390) (nat_lit 0) D2M8K2.u15502 from rfl, totK_node, atot15501, atot15502]
  decide +kernel

theorem arows15507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15507 = true := by
  rw [show D2M8K2.u15507 = KTree.node D2M8K2.u15505 (nat_lit 33854457) (nat_lit 1840860304) (nat_lit 0) D2M8K2.u15506 from rfl, allE_node, arows15505, irow15507, arows15506]
  all_goals rfl

theorem atot15507 : totK PD2M8K2 D2M8K2.u15507 = [0, 456597242844, 1560746301482, 1323426385973, 235639473953, 5455647540, 0, 0] := by
  rw [show D2M8K2.u15507 = KTree.node D2M8K2.u15505 (nat_lit 33854457) (nat_lit 1840860304) (nat_lit 0) D2M8K2.u15506 from rfl, totK_node, atot15505, atot15506]
  decide +kernel

theorem arows15510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15510 = true := by
  rw [show D2M8K2.u15510 = KTree.node D2M8K2.u15508 (nat_lit 33858489) (nat_lit 1707026518) (nat_lit 0) D2M8K2.u15509 from rfl, allE_node, arows15508, irow15510, arows15509]
  all_goals rfl

theorem atot15510 : totK PD2M8K2 D2M8K2.u15510 = [0, 500893754207, 1573714326186, 1301698471291, 217108905343, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15510 = KTree.node D2M8K2.u15508 (nat_lit 33858489) (nat_lit 1707026518) (nat_lit 0) D2M8K2.u15509 from rfl, totK_node, atot15508, atot15509]
  decide +kernel

theorem arows15516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15516 = true := by
  rw [show D2M8K2.u15516 = KTree.node D2M8K2.u15514 (nat_lit 33861727) (nat_lit 2303470709) (nat_lit 0) D2M8K2.u15515 from rfl, allE_node, arows15514, irow15516, arows15515]
  all_goals rfl

theorem atot15516 : totK PD2M8K2 D2M8K2.u15516 = [0, 0, 844959592473, 1913197245453, 740488744060, 36953044490, 0, 0] := by
  rw [show D2M8K2.u15516 = KTree.node D2M8K2.u15514 (nat_lit 33861727) (nat_lit 2303470709) (nat_lit 0) D2M8K2.u15515 from rfl, totK_node, atot15514, atot15515]
  decide +kernel

theorem arows15519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15519 = true := by
  rw [show D2M8K2.u15519 = KTree.node D2M8K2.u15517 (nat_lit 33868806) (nat_lit 3520803613) (nat_lit 0) D2M8K2.u15518 from rfl, allE_node, arows15517, irow15519, arows15518]
  all_goals rfl

theorem atot15519 : totK PD2M8K2 D2M8K2.u15519 = [0, 0, 501928260823, 1649157379950, 1201008223731, 152903190386, 1369150432, 0] := by
  rw [show D2M8K2.u15519 = KTree.node D2M8K2.u15517 (nat_lit 33868806) (nat_lit 3520803613) (nat_lit 0) D2M8K2.u15518 from rfl, totK_node, atot15517, atot15518]
  decide +kernel

theorem arows15523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15523 = true := by
  rw [show D2M8K2.u15523 = KTree.node D2M8K2.u15521 (nat_lit 33875734) (nat_lit 3390669793) (nat_lit 0) D2M8K2.u15522 from rfl, allE_node, arows15521, irow15523, arows15522]
  all_goals rfl

theorem atot15523 : totK PD2M8K2 D2M8K2.u15523 = [0, 0, 735368292000, 1917067905314, 855989289090, 40543724770, 0, 0] := by
  rw [show D2M8K2.u15523 = KTree.node D2M8K2.u15521 (nat_lit 33875734) (nat_lit 3390669793) (nat_lit 0) D2M8K2.u15522 from rfl, totK_node, atot15521, atot15522]
  decide +kernel

theorem arows15526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15526 = true := by
  rw [show D2M8K2.u15526 = KTree.node D2M8K2.u15524 (nat_lit 33880782) (nat_lit 3639982437) (nat_lit 0) D2M8K2.u15525 from rfl, allE_node, arows15524, irow15526, arows15525]
  all_goals rfl

theorem atot15526 : totK PD2M8K2 D2M8K2.u15526 = [0, 353535550406, 1232621633111, 1475736656363, 560630636734, 29716642559, 0, 0] := by
  rw [show D2M8K2.u15526 = KTree.node D2M8K2.u15524 (nat_lit 33880782) (nat_lit 3639982437) (nat_lit 0) D2M8K2.u15525 from rfl, totK_node, atot15524, atot15525]
  decide +kernel

theorem arows15531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15531 = true := by
  rw [show D2M8K2.u15531 = KTree.node D2M8K2.u15529 (nat_lit 33888902) (nat_lit 3089259579) (nat_lit 0) D2M8K2.u15530 from rfl, allE_node, arows15529, irow15531, arows15530]
  all_goals rfl

theorem atot15531 : totK PD2M8K2 D2M8K2.u15531 = [0, 286200058165, 1195322010632, 1544918780430, 593696524548, 37609398105, 0, 0] := by
  rw [show D2M8K2.u15531 = KTree.node D2M8K2.u15529 (nat_lit 33888902) (nat_lit 3089259579) (nat_lit 0) D2M8K2.u15530 from rfl, totK_node, atot15529, atot15530]
  decide +kernel

theorem arows15534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15534 = true := by
  rw [show D2M8K2.u15534 = KTree.node D2M8K2.u15532 (nat_lit 33891845) (nat_lit 2347077519) (nat_lit 0) D2M8K2.u15533 from rfl, allE_node, arows15532, irow15534, arows15533]
  all_goals rfl

theorem atot15534 : totK PD2M8K2 D2M8K2.u15534 = [0, 405670814317, 1434421226667, 1434467851491, 331413491595, 13036865798, 0, 0] := by
  rw [show D2M8K2.u15534 = KTree.node D2M8K2.u15532 (nat_lit 33891845) (nat_lit 2347077519) (nat_lit 0) D2M8K2.u15533 from rfl, totK_node, atot15532, atot15533]
  decide +kernel

theorem arows15538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15538 = true := by
  rw [show D2M8K2.u15538 = KTree.node D2M8K2.u15536 (nat_lit 33896069) (nat_lit 1545828077) (nat_lit 0) D2M8K2.u15537 from rfl, allE_node, arows15536, irow15538, arows15537]
  all_goals rfl

theorem atot15538 : totK PD2M8K2 D2M8K2.u15538 = [0, 451303240103, 1558637649807, 1386818536701, 271224266047, 8388394511, 0, 0] := by
  rw [show D2M8K2.u15538 = KTree.node D2M8K2.u15536 (nat_lit 33896069) (nat_lit 1545828077) (nat_lit 0) D2M8K2.u15537 from rfl, totK_node, atot15536, atot15537]
  decide +kernel

theorem arows15541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15541 = true := by
  rw [show D2M8K2.u15541 = KTree.node D2M8K2.u15539 (nat_lit 33900048) (nat_lit 3716413433) (nat_lit 0) D2M8K2.u15540 from rfl, allE_node, arows15539, irow15541, arows15540]
  all_goals rfl

theorem atot15541 : totK PD2M8K2 D2M8K2.u15541 = [0, 504384611049, 1647362614700, 1315030956245, 192025062783, 3880716147, 0, 0] := by
  rw [show D2M8K2.u15541 = KTree.node D2M8K2.u15539 (nat_lit 33900048) (nat_lit 3716413433) (nat_lit 0) D2M8K2.u15540 from rfl, totK_node, atot15539, atot15540]
  decide +kernel

theorem arows15548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15548 = true := by
  rw [show D2M8K2.u15548 = KTree.node D2M8K2.u15546 (nat_lit 33903277) (nat_lit 1002657652) (nat_lit 0) D2M8K2.u15547 from rfl, allE_node, arows15546, irow15548, arows15547]
  all_goals rfl

theorem atot15548 : totK PD2M8K2 D2M8K2.u15548 = [0, 0, 807036536072, 1908406296374, 863020438045, 56010293219, 0, 0] := by
  rw [show D2M8K2.u15548 = KTree.node D2M8K2.u15546 (nat_lit 33903277) (nat_lit 1002657652) (nat_lit 0) D2M8K2.u15547 from rfl, totK_node, atot15546, atot15547]
  decide +kernel

theorem arows15551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15551 = true := by
  rw [show D2M8K2.u15551 = KTree.node D2M8K2.u15549 (nat_lit 33909722) (nat_lit 4241602830) (nat_lit 0) D2M8K2.u15550 from rfl, allE_node, arows15549, irow15551, arows15550]
  all_goals rfl

theorem atot15551 : totK PD2M8K2 D2M8K2.u15551 = [0, 0, 341210262695, 1222404385525, 1491312667266, 536357077528, 33015336044, 0] := by
  rw [show D2M8K2.u15551 = KTree.node D2M8K2.u15549 (nat_lit 33909722) (nat_lit 4241602830) (nat_lit 0) D2M8K2.u15550 from rfl, totK_node, atot15549, atot15550]
  decide +kernel

theorem arows15555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15555 = true := by
  rw [show D2M8K2.u15555 = KTree.node D2M8K2.u15553 (nat_lit 33912779) (nat_lit 2318629368) (nat_lit 0) D2M8K2.u15554 from rfl, allE_node, arows15553, irow15555, arows15554]
  all_goals rfl

theorem atot15555 : totK PD2M8K2 D2M8K2.u15555 = [0, 0, 416817405783, 1537083956462, 1409370568831, 250498693874, 5159868635, 0] := by
  rw [show D2M8K2.u15555 = KTree.node D2M8K2.u15553 (nat_lit 33912779) (nat_lit 2318629368) (nat_lit 0) D2M8K2.u15554 from rfl, totK_node, atot15553, atot15554]
  decide +kernel

theorem arows15558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15558 = true := by
  rw [show D2M8K2.u15558 = KTree.node D2M8K2.u15556 (nat_lit 33917520) (nat_lit 2662244622) (nat_lit 0) D2M8K2.u15557 from rfl, allE_node, arows15556, irow15558, arows15557]
  all_goals rfl

theorem atot15558 : totK PD2M8K2 D2M8K2.u15558 = [0, 0, 466588160177, 1651141109467, 1340817150364, 186814037661, 1557581783, 0] := by
  rw [show D2M8K2.u15558 = KTree.node D2M8K2.u15556 (nat_lit 33917520) (nat_lit 2662244622) (nat_lit 0) D2M8K2.u15557 from rfl, totK_node, atot15556, atot15557]
  decide +kernel

theorem arows15563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15563 = true := by
  rw [show D2M8K2.u15563 = KTree.node D2M8K2.u15561 (nat_lit 33921262) (nat_lit 3948075685) (nat_lit 0) D2M8K2.u15562 from rfl, allE_node, arows15561, irow15563, arows15562]
  all_goals rfl

theorem atot15563 : totK PD2M8K2 D2M8K2.u15563 = [0, 0, 418158479266, 1606705804727, 1444891208941, 193638238058, 1415142070, 0] := by
  rw [show D2M8K2.u15563 = KTree.node D2M8K2.u15561 (nat_lit 33921262) (nat_lit 3948075685) (nat_lit 0) D2M8K2.u15562 from rfl, totK_node, atot15561, atot15562]
  decide +kernel

theorem arows15566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15566 = true := by
  rw [show D2M8K2.u15566 = KTree.node D2M8K2.u15564 (nat_lit 33925033) (nat_lit 1508216469) (nat_lit 0) D2M8K2.u15565 from rfl, allE_node, arows15564, irow15566, arows15565]
  all_goals rfl

theorem atot15566 : totK PD2M8K2 D2M8K2.u15566 = [0, 413176513979, 1236606494665, 1049812122135, 616946177183, 218995557831, 9302370699, 0] := by
  rw [show D2M8K2.u15566 = KTree.node D2M8K2.u15564 (nat_lit 33925033) (nat_lit 1508216469) (nat_lit 0) D2M8K2.u15565 from rfl, totK_node, atot15564, atot15565]
  decide +kernel

theorem arows15570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15570 = true := by
  rw [show D2M8K2.u15570 = KTree.node D2M8K2.u15568 (nat_lit 33928638) (nat_lit 3982683020) (nat_lit 0) D2M8K2.u15569 from rfl, allE_node, arows15568, irow15570, arows15569]
  all_goals rfl

theorem atot15570 : totK PD2M8K2 D2M8K2.u15570 = [0, 423543875246, 1498039640732, 1395383004310, 312455970109, 21156758932, 0, 0] := by
  rw [show D2M8K2.u15570 = KTree.node D2M8K2.u15568 (nat_lit 33928638) (nat_lit 3982683020) (nat_lit 0) D2M8K2.u15569 from rfl, totK_node, atot15568, atot15569]
  decide +kernel

theorem arows15573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15573 = true := by
  rw [show D2M8K2.u15573 = KTree.node D2M8K2.u15571 (nat_lit 33931400) (nat_lit 3887263102) (nat_lit 0) D2M8K2.u15572 from rfl, allE_node, arows15571, irow15573, arows15572]
  all_goals rfl

theorem atot15573 : totK PD2M8K2 D2M8K2.u15573 = [0, 445880033282, 1448378631474, 1339730082072, 382166414745, 14829996138, 0, 0] := by
  rw [show D2M8K2.u15573 = KTree.node D2M8K2.u15571 (nat_lit 33931400) (nat_lit 3887263102) (nat_lit 0) D2M8K2.u15572 from rfl, totK_node, atot15571, atot15572]
  decide +kernel

theorem arows15579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15579 = true := by
  rw [show D2M8K2.u15579 = KTree.node D2M8K2.u15577 (nat_lit 33938086) (nat_lit 2780837586) (nat_lit 0) D2M8K2.u15578 from rfl, allE_node, arows15577, irow15579, arows15578]
  all_goals rfl

theorem atot15579 : totK PD2M8K2 D2M8K2.u15579 = [0, 399905632603, 1432022608121, 1413193719030, 325929929871, 13049727234, 0, 0] := by
  rw [show D2M8K2.u15579 = KTree.node D2M8K2.u15577 (nat_lit 33938086) (nat_lit 2780837586) (nat_lit 0) D2M8K2.u15578 from rfl, totK_node, atot15577, atot15578]
  decide +kernel

theorem arows15582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15582 = true := by
  rw [show D2M8K2.u15582 = KTree.node D2M8K2.u15580 (nat_lit 33941742) (nat_lit 3767908015) (nat_lit 0) D2M8K2.u15581 from rfl, allE_node, arows15580, irow15582, arows15581]
  all_goals rfl

theorem atot15582 : totK PD2M8K2 D2M8K2.u15582 = [0, 424338653836, 1522906858736, 1425016794974, 237187851997, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15582 = KTree.node D2M8K2.u15580 (nat_lit 33941742) (nat_lit 3767908015) (nat_lit 0) D2M8K2.u15581 from rfl, totK_node, atot15580, atot15581]
  decide +kernel

theorem arows15586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15586 = true := by
  rw [show D2M8K2.u15586 = KTree.node D2M8K2.u15584 (nat_lit 33944931) (nat_lit 2579914156) (nat_lit 0) D2M8K2.u15585 from rfl, allE_node, arows15584, irow15586, arows15585]
  all_goals rfl

theorem atot15586 : totK PD2M8K2 D2M8K2.u15586 = [0, 0, 756234438000, 1911360407347, 822887812827, 40732505624, 0, 0] := by
  rw [show D2M8K2.u15586 = KTree.node D2M8K2.u15584 (nat_lit 33944931) (nat_lit 2579914156) (nat_lit 0) D2M8K2.u15585 from rfl, totK_node, atot15584, atot15585]
  decide +kernel

theorem arows15589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15589 = true := by
  rw [show D2M8K2.u15589 = KTree.node D2M8K2.u15587 (nat_lit 33948917) (nat_lit 2401362874) (nat_lit 0) D2M8K2.u15588 from rfl, allE_node, arows15587, irow15589, arows15588]
  all_goals rfl

theorem atot15589 : totK PD2M8K2 D2M8K2.u15589 = [0, 0, 508195051022, 1652748355705, 1254234526622, 148792823152, 1206465782, 0] := by
  rw [show D2M8K2.u15589 = KTree.node D2M8K2.u15587 (nat_lit 33948917) (nat_lit 2401362874) (nat_lit 0) D2M8K2.u15588 from rfl, totK_node, atot15587, atot15588]
  decide +kernel

theorem arows15594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15594 = true := by
  rw [show D2M8K2.u15594 = KTree.node D2M8K2.u15592 (nat_lit 33953453) (nat_lit 2149376973) (nat_lit 0) D2M8K2.u15593 from rfl, allE_node, arows15592, irow15594, arows15593]
  all_goals rfl

theorem atot15594 : totK PD2M8K2 D2M8K2.u15594 = [0, 0, 407659621657, 1461732680823, 1362645157212, 307057040313, 13016197374, 0] := by
  rw [show D2M8K2.u15594 = KTree.node D2M8K2.u15592 (nat_lit 33953453) (nat_lit 2149376973) (nat_lit 0) D2M8K2.u15593 from rfl, totK_node, atot15592, atot15593]
  decide +kernel

theorem arows15597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15597 = true := by
  rw [show D2M8K2.u15597 = KTree.node D2M8K2.u15595 (nat_lit 33960384) (nat_lit 3756869540) (nat_lit 0) D2M8K2.u15596 from rfl, allE_node, arows15595, irow15597, arows15596]
  all_goals rfl

theorem atot15597 : totK PD2M8K2 D2M8K2.u15597 = [0, 0, 486629290481, 1601404606103, 1199739874076, 177039489383, 4574395652, 0] := by
  rw [show D2M8K2.u15597 = KTree.node D2M8K2.u15595 (nat_lit 33960384) (nat_lit 3756869540) (nat_lit 0) D2M8K2.u15596 from rfl, totK_node, atot15595, atot15596]
  decide +kernel

theorem arows15601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15601 = true := by
  rw [show D2M8K2.u15601 = KTree.node D2M8K2.u15599 (nat_lit 34007173) (nat_lit 1377495917) (nat_lit 0) D2M8K2.u15600 from rfl, allE_node, arows15599, irow15601, arows15600]
  all_goals rfl

theorem atot15601 : totK PD2M8K2 D2M8K2.u15601 = [0, 395356023686, 1322902077614, 1324333910172, 511933092043, 42903141254, 0, 0] := by
  rw [show D2M8K2.u15601 = KTree.node D2M8K2.u15599 (nat_lit 34007173) (nat_lit 1377495917) (nat_lit 0) D2M8K2.u15600 from rfl, totK_node, atot15599, atot15600]
  decide +kernel

theorem arows15604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15604 = true := by
  rw [show D2M8K2.u15604 = KTree.node D2M8K2.u15602 (nat_lit 34011177) (nat_lit 1896846186) (nat_lit 0) D2M8K2.u15603 from rfl, allE_node, arows15602, irow15604, arows15603]
  all_goals rfl

theorem atot15604 : totK PD2M8K2 D2M8K2.u15604 = [0, 407036568121, 1497171224655, 1445109752490, 285402368032, 11304534362, 0, 0] := by
  rw [show D2M8K2.u15604 = KTree.node D2M8K2.u15602 (nat_lit 34011177) (nat_lit 1896846186) (nat_lit 0) D2M8K2.u15603 from rfl, totK_node, atot15602, atot15603]
  decide +kernel

theorem arows15613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15613 = true := by
  rw [show D2M8K2.u15613 = KTree.node D2M8K2.u15611 (nat_lit 34014366) (nat_lit 3061641163) (nat_lit 0) D2M8K2.u15612 from rfl, allE_node, arows15611, irow15613, arows15612]
  all_goals rfl

theorem atot15613 : totK PD2M8K2 D2M8K2.u15613 = [0, 424820203696, 1483865470988, 1402173553085, 313734870320, 6547232298, 0, 0] := by
  rw [show D2M8K2.u15613 = KTree.node D2M8K2.u15611 (nat_lit 34014366) (nat_lit 3061641163) (nat_lit 0) D2M8K2.u15612 from rfl, totK_node, atot15611, atot15612]
  decide +kernel

theorem arows15616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15616 = true := by
  rw [show D2M8K2.u15616 = KTree.node D2M8K2.u15614 (nat_lit 34021202) (nat_lit 4112515687) (nat_lit 0) D2M8K2.u15615 from rfl, allE_node, arows15614, irow15616, arows15615]
  all_goals rfl

theorem atot15616 : totK PD2M8K2 D2M8K2.u15616 = [0, 424157580399, 1474750061571, 1388757225836, 299461409381, 11885407614, 0, 0] := by
  rw [show D2M8K2.u15616 = KTree.node D2M8K2.u15614 (nat_lit 34021202) (nat_lit 4112515687) (nat_lit 0) D2M8K2.u15615 from rfl, totK_node, atot15614, atot15615]
  decide +kernel

theorem arows15620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15620 = true := by
  rw [show D2M8K2.u15620 = KTree.node D2M8K2.u15618 (nat_lit 34028410) (nat_lit 3834079717) (nat_lit 0) D2M8K2.u15619 from rfl, allE_node, arows15618, irow15620, arows15619]
  all_goals rfl

theorem atot15620 : totK PD2M8K2 D2M8K2.u15620 = [0, 0, 757549604271, 1856556753641, 830810652185, 69343372553, 1138244013, 0] := by
  rw [show D2M8K2.u15620 = KTree.node D2M8K2.u15618 (nat_lit 34028410) (nat_lit 3834079717) (nat_lit 0) D2M8K2.u15619 from rfl, totK_node, atot15618, atot15619]
  decide +kernel

theorem arows15623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15623 = true := by
  rw [show D2M8K2.u15623 = KTree.node D2M8K2.u15621 (nat_lit 34032362) (nat_lit 3989013130) (nat_lit 0) D2M8K2.u15622 from rfl, allE_node, arows15621, irow15623, arows15622]
  all_goals rfl

theorem atot15623 : totK PD2M8K2 D2M8K2.u15623 = [0, 0, 655279199985, 1841268841456, 1042933897088, 76067389531, 0, 0] := by
  rw [show D2M8K2.u15623 = KTree.node D2M8K2.u15621 (nat_lit 34032362) (nat_lit 3989013130) (nat_lit 0) D2M8K2.u15622 from rfl, totK_node, atot15621, atot15622]
  decide +kernel

theorem arows15628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15628 = true := by
  rw [show D2M8K2.u15628 = KTree.node D2M8K2.u15626 (nat_lit 34042154) (nat_lit 4052162500) (nat_lit 0) D2M8K2.u15627 from rfl, allE_node, arows15626, irow15628, arows15627]
  all_goals rfl

theorem atot15628 : totK PD2M8K2 D2M8K2.u15628 = [0, 0, 592448857524, 1774869157665, 1058652954219, 101029531999, 1095107716, 0] := by
  rw [show D2M8K2.u15628 = KTree.node D2M8K2.u15626 (nat_lit 34042154) (nat_lit 4052162500) (nat_lit 0) D2M8K2.u15627 from rfl, totK_node, atot15626, atot15627]
  decide +kernel

theorem arows15631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15631 = true := by
  rw [show D2M8K2.u15631 = KTree.node D2M8K2.u15629 (nat_lit 34049531) (nat_lit 2365313361) (nat_lit 0) D2M8K2.u15630 from rfl, allE_node, arows15629, irow15631, arows15630]
  all_goals rfl

theorem atot15631 : totK PD2M8K2 D2M8K2.u15631 = [0, 408214539155, 1311208010047, 1231435641698, 505882878631, 94451906807, 3882006667, 0] := by
  rw [show D2M8K2.u15631 = KTree.node D2M8K2.u15629 (nat_lit 34049531) (nat_lit 2365313361) (nat_lit 0) D2M8K2.u15630 from rfl, totK_node, atot15629, atot15630]
  decide +kernel

theorem arows15635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15635 = true := by
  rw [show D2M8K2.u15635 = KTree.node D2M8K2.u15633 (nat_lit 34053178) (nat_lit 3211615224) (nat_lit 0) D2M8K2.u15634 from rfl, allE_node, arows15633, irow15635, arows15634]
  all_goals rfl

theorem atot15635 : totK PD2M8K2 D2M8K2.u15635 = [0, 419614553652, 1469591423699, 1392164431722, 362521368375, 25114608015, 0, 0] := by
  rw [show D2M8K2.u15635 = KTree.node D2M8K2.u15633 (nat_lit 34053178) (nat_lit 3211615224) (nat_lit 0) D2M8K2.u15634 from rfl, totK_node, atot15633, atot15634]
  decide +kernel

theorem arows15638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15638 = true := by
  rw [show D2M8K2.u15638 = KTree.node D2M8K2.u15636 (nat_lit 34056000) (nat_lit 3705351137) (nat_lit 0) D2M8K2.u15637 from rfl, allE_node, arows15636, irow15638, arows15637]
  all_goals rfl

theorem atot15638 : totK PD2M8K2 D2M8K2.u15638 = [0, 426292166354, 1407806002640, 1397559321923, 386682613224, 11999689481, 0, 0] := by
  rw [show D2M8K2.u15638 = KTree.node D2M8K2.u15636 (nat_lit 34056000) (nat_lit 3705351137) (nat_lit 0) D2M8K2.u15637 from rfl, totK_node, atot15636, atot15637]
  decide +kernel

theorem arows15644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15644 = true := by
  rw [show D2M8K2.u15644 = KTree.node D2M8K2.u15642 (nat_lit 34059392) (nat_lit 3495328222) (nat_lit 0) D2M8K2.u15643 from rfl, allE_node, arows15642, irow15644, arows15643]
  all_goals rfl

theorem atot15644 : totK PD2M8K2 D2M8K2.u15644 = [0, 345540029431, 1407871395505, 1528156824780, 348369300951, 13077537112, 0, 0] := by
  rw [show D2M8K2.u15644 = KTree.node D2M8K2.u15642 (nat_lit 34059392) (nat_lit 3495328222) (nat_lit 0) D2M8K2.u15643 from rfl, totK_node, atot15642, atot15643]
  decide +kernel

theorem arows15647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15647 = true := by
  rw [show D2M8K2.u15647 = KTree.node D2M8K2.u15645 (nat_lit 34066674) (nat_lit 3433520064) (nat_lit 0) D2M8K2.u15646 from rfl, allE_node, arows15645, irow15647, arows15646]
  all_goals rfl

theorem atot15647 : totK PD2M8K2 D2M8K2.u15647 = [0, 443022665011, 1489284446943, 1400751708384, 314423419936, 8996765196, 0, 0] := by
  rw [show D2M8K2.u15647 = KTree.node D2M8K2.u15645 (nat_lit 34066674) (nat_lit 3433520064) (nat_lit 0) D2M8K2.u15646 from rfl, totK_node, atot15645, atot15646]
  decide +kernel

theorem arows15651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15651 = true := by
  rw [show D2M8K2.u15651 = KTree.node D2M8K2.u15649 (nat_lit 34070132) (nat_lit 3036252308) (nat_lit 0) D2M8K2.u15650 from rfl, allE_node, arows15649, irow15651, arows15650]
  all_goals rfl

theorem atot15651 : totK PD2M8K2 D2M8K2.u15651 = [0, 0, 584038143653, 1731533382868, 1109257770911, 120140245299, 1310285577, 0] := by
  rw [show D2M8K2.u15651 = KTree.node D2M8K2.u15649 (nat_lit 34070132) (nat_lit 3036252308) (nat_lit 0) D2M8K2.u15650 from rfl, totK_node, atot15649, atot15650]
  decide +kernel

theorem arows15654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15654 = true := by
  rw [show D2M8K2.u15654 = KTree.node D2M8K2.u15652 (nat_lit 34073815) (nat_lit 2316112564) (nat_lit 0) D2M8K2.u15653 from rfl, allE_node, arows15652, irow15654, arows15653]
  all_goals rfl

theorem atot15654 : totK PD2M8K2 D2M8K2.u15654 = [0, 0, 639237700177, 1769970047317, 1140895575318, 101383388377, 0, 0] := by
  rw [show D2M8K2.u15654 = KTree.node D2M8K2.u15652 (nat_lit 34073815) (nat_lit 2316112564) (nat_lit 0) D2M8K2.u15653 from rfl, totK_node, atot15652, atot15653]
  decide +kernel

theorem arows15659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15659 = true := by
  rw [show D2M8K2.u15659 = KTree.node D2M8K2.u15657 (nat_lit 34078526) (nat_lit 3693085758) (nat_lit 0) D2M8K2.u15658 from rfl, allE_node, arows15657, irow15659, arows15658]
  all_goals rfl

theorem atot15659 : totK PD2M8K2 D2M8K2.u15659 = [0, 0, 454892652735, 1575141566910, 1327484937719, 212558894564, 4879840392, 0] := by
  rw [show D2M8K2.u15659 = KTree.node D2M8K2.u15657 (nat_lit 34078526) (nat_lit 3693085758) (nat_lit 0) D2M8K2.u15658 from rfl, totK_node, atot15657, atot15658]
  decide +kernel

theorem arows15662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15662 = true := by
  rw [show D2M8K2.u15662 = KTree.node D2M8K2.u15660 (nat_lit 34086584) (nat_lit 3216729781) (nat_lit 0) D2M8K2.u15661 from rfl, allE_node, arows15660, irow15662, arows15661]
  all_goals rfl

theorem atot15662 : totK PD2M8K2 D2M8K2.u15662 = [0, 0, 492605021187, 1600984508956, 1310844788957, 209922439439, 4931404646, 0] := by
  rw [show D2M8K2.u15662 = KTree.node D2M8K2.u15660 (nat_lit 34086584) (nat_lit 3216729781) (nat_lit 0) D2M8K2.u15661 from rfl, totK_node, atot15660, atot15661]
  decide +kernel

theorem arows15666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15666 = true := by
  rw [show D2M8K2.u15666 = KTree.node D2M8K2.u15664 (nat_lit 34089749) (nat_lit 2344747991) (nat_lit 0) D2M8K2.u15665 from rfl, allE_node, arows15664, irow15666, arows15665]
  all_goals rfl

theorem atot15666 : totK PD2M8K2 D2M8K2.u15666 = [0, 0, 360336569011, 1347446780537, 1410038709935, 397474858792, 21751168066, 0] := by
  rw [show D2M8K2.u15666 = KTree.node D2M8K2.u15664 (nat_lit 34089749) (nat_lit 2344747991) (nat_lit 0) D2M8K2.u15665 from rfl, totK_node, atot15664, atot15665]
  decide +kernel

theorem arows15669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15669 = true := by
  rw [show D2M8K2.u15669 = KTree.node D2M8K2.u15667 (nat_lit 34093190) (nat_lit 3211076501) (nat_lit 0) D2M8K2.u15668 from rfl, allE_node, arows15667, irow15669, arows15668]
  all_goals rfl

theorem atot15669 : totK PD2M8K2 D2M8K2.u15669 = [0, 0, 435490896519, 1608757459117, 1360788327237, 169037116951, 1369150432, 0] := by
  rw [show D2M8K2.u15669 = KTree.node D2M8K2.u15667 (nat_lit 34093190) (nat_lit 3211076501) (nat_lit 0) D2M8K2.u15668 from rfl, totK_node, atot15667, atot15668]
  decide +kernel

theorem arows15676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15676 = true := by
  rw [show D2M8K2.u15676 = KTree.node D2M8K2.u15674 (nat_lit 34100136) (nat_lit 3346331192) (nat_lit 0) D2M8K2.u15675 from rfl, allE_node, arows15674, irow15676, arows15675]
  all_goals rfl

theorem atot15676 : totK PD2M8K2 D2M8K2.u15676 = [0, 0, 411494211132, 1538842078467, 1403961788043, 231909888114, 5398830306, 0] := by
  rw [show D2M8K2.u15676 = KTree.node D2M8K2.u15674 (nat_lit 34100136) (nat_lit 3346331192) (nat_lit 0) D2M8K2.u15675 from rfl, totK_node, atot15674, atot15675]
  decide +kernel

theorem arows15679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15679 = true := by
  rw [show D2M8K2.u15679 = KTree.node D2M8K2.u15677 (nat_lit 34104631) (nat_lit 1521848789) (nat_lit 0) D2M8K2.u15678 from rfl, allE_node, arows15677, irow15679, arows15678]
  all_goals rfl

theorem atot15679 : totK PD2M8K2 D2M8K2.u15679 = [0, 0, 375622004332, 1522160751428, 1445358378923, 180691424220, 2294578496, 0] := by
  rw [show D2M8K2.u15679 = KTree.node D2M8K2.u15677 (nat_lit 34104631) (nat_lit 1521848789) (nat_lit 0) D2M8K2.u15678 from rfl, totK_node, atot15677, atot15678]
  decide +kernel

theorem arows15683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15683 = true := by
  rw [show D2M8K2.u15683 = KTree.node D2M8K2.u15681 (nat_lit 34108785) (nat_lit 1351616781) (nat_lit 0) D2M8K2.u15682 from rfl, allE_node, arows15681, irow15683, arows15682]
  all_goals rfl

theorem atot15683 : totK PD2M8K2 D2M8K2.u15683 = [0, 0, 415031635960, 1493726063183, 1432184647401, 275783661409, 6161573843, 0] := by
  rw [show D2M8K2.u15683 = KTree.node D2M8K2.u15681 (nat_lit 34108785) (nat_lit 1351616781) (nat_lit 0) D2M8K2.u15682 from rfl, totK_node, atot15681, atot15682]
  decide +kernel

theorem arows15686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15686 = true := by
  rw [show D2M8K2.u15686 = KTree.node D2M8K2.u15684 (nat_lit 34112243) (nat_lit 2897870831) (nat_lit 0) D2M8K2.u15685 from rfl, allE_node, arows15684, irow15686, arows15685]
  all_goals rfl

theorem atot15686 : totK PD2M8K2 D2M8K2.u15686 = [0, 0, 0, 547659141125, 1768594132721, 1040933189327, 99579577015, 1275377855] := by
  rw [show D2M8K2.u15686 = KTree.node D2M8K2.u15684 (nat_lit 34112243) (nat_lit 2897870831) (nat_lit 0) D2M8K2.u15685 from rfl, totK_node, atot15684, atot15685]
  decide +kernel

theorem arows15691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15691 = true := by
  rw [show D2M8K2.u15691 = KTree.node D2M8K2.u15689 (nat_lit 34121352) (nat_lit 3593511707) (nat_lit 0) D2M8K2.u15690 from rfl, allE_node, arows15689, irow15691, arows15690]
  all_goals rfl

theorem atot15691 : totK PD2M8K2 D2M8K2.u15691 = [0, 0, 0, 950051724080, 1958310521354, 587786372056, 19430278005, 0] := by
  rw [show D2M8K2.u15691 = KTree.node D2M8K2.u15689 (nat_lit 34121352) (nat_lit 3593511707) (nat_lit 0) D2M8K2.u15690 from rfl, totK_node, atot15689, atot15690]
  decide +kernel

theorem arows15694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15694 = true := by
  rw [show D2M8K2.u15694 = KTree.node D2M8K2.u15692 (nat_lit 34129648) (nat_lit 3381387423) (nat_lit 0) D2M8K2.u15693 from rfl, allE_node, arows15692, irow15694, arows15693]
  all_goals rfl

theorem atot15694 : totK PD2M8K2 D2M8K2.u15694 = [0, 0, 351244263953, 1343992538036, 1511717761494, 404976153598, 15213377707, 0] := by
  rw [show D2M8K2.u15694 = KTree.node D2M8K2.u15692 (nat_lit 34129648) (nat_lit 3381387423) (nat_lit 0) D2M8K2.u15693 from rfl, totK_node, atot15692, atot15693]
  decide +kernel

theorem arows15698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15698 = true := by
  rw [show D2M8K2.u15698 = KTree.node D2M8K2.u15696 (nat_lit 34138142) (nat_lit 3881137344) (nat_lit 0) D2M8K2.u15697 from rfl, allE_node, arows15696, irow15698, arows15697]
  all_goals rfl

theorem atot15698 : totK PD2M8K2 D2M8K2.u15698 = [0, 0, 424561853211, 1450748214254, 1394557469987, 387081910865, 16311238869, 0] := by
  rw [show D2M8K2.u15698 = KTree.node D2M8K2.u15696 (nat_lit 34138142) (nat_lit 3881137344) (nat_lit 0) D2M8K2.u15697 from rfl, totK_node, atot15696, atot15697]
  decide +kernel

theorem arows15701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15701 = true := by
  rw [show D2M8K2.u15701 = KTree.node D2M8K2.u15699 (nat_lit 34141630) (nat_lit 3839314143) (nat_lit 0) D2M8K2.u15700 from rfl, allE_node, arows15699, irow15701, arows15700]
  all_goals rfl

theorem atot15701 : totK PD2M8K2 D2M8K2.u15701 = [0, 0, 524707813345, 1639752727521, 1316967120097, 211917250896, 4231263225, 0] := by
  rw [show D2M8K2.u15701 = KTree.node D2M8K2.u15699 (nat_lit 34141630) (nat_lit 3839314143) (nat_lit 0) D2M8K2.u15700 from rfl, totK_node, atot15699, atot15700]
  decide +kernel

theorem arows15707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15707 = true := by
  rw [show D2M8K2.u15707 = KTree.node D2M8K2.u15705 (nat_lit 34149138) (nat_lit 3192067368) (nat_lit 0) D2M8K2.u15706 from rfl, allE_node, arows15705, irow15707, arows15706]
  all_goals rfl

theorem atot15707 : totK PD2M8K2 D2M8K2.u15707 = [0, 0, 693030976581, 1846905174174, 1054926926104, 97618938699, 0, 0] := by
  rw [show D2M8K2.u15707 = KTree.node D2M8K2.u15705 (nat_lit 34149138) (nat_lit 3192067368) (nat_lit 0) D2M8K2.u15706 from rfl, totK_node, atot15705, atot15706]
  decide +kernel

theorem arows15710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15710 = true := by
  rw [show D2M8K2.u15710 = KTree.node D2M8K2.u15708 (nat_lit 34173607) (nat_lit 2000578630) (nat_lit 0) D2M8K2.u15709 from rfl, allE_node, arows15708, irow15710, arows15709]
  all_goals rfl

theorem atot15710 : totK PD2M8K2 D2M8K2.u15710 = [0, 0, 410139960575, 1457162086066, 1358519937096, 313853125504, 13935871499, 0] := by
  rw [show D2M8K2.u15710 = KTree.node D2M8K2.u15708 (nat_lit 34173607) (nat_lit 2000578630) (nat_lit 0) D2M8K2.u15709 from rfl, totK_node, atot15708, atot15709]
  decide +kernel

theorem arows15714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15714 = true := by
  rw [show D2M8K2.u15714 = KTree.node D2M8K2.u15712 (nat_lit 34177227) (nat_lit 3467781381) (nat_lit 0) D2M8K2.u15713 from rfl, allE_node, arows15712, irow15714, arows15713]
  all_goals rfl

theorem atot15714 : totK PD2M8K2 D2M8K2.u15714 = [0, 0, 419771997431, 1538537065762, 1438326502015, 247946020653, 10165445843, 0] := by
  rw [show D2M8K2.u15714 = KTree.node D2M8K2.u15712 (nat_lit 34177227) (nat_lit 3467781381) (nat_lit 0) D2M8K2.u15713 from rfl, totK_node, atot15712, atot15713]
  decide +kernel

theorem arows15717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15717 = true := by
  rw [show D2M8K2.u15717 = KTree.node D2M8K2.u15715 (nat_lit 34180451) (nat_lit 2833255305) (nat_lit 0) D2M8K2.u15716 from rfl, allE_node, arows15715, irow15717, arows15716]
  all_goals rfl

theorem atot15717 : totK PD2M8K2 D2M8K2.u15717 = [0, 0, 444072127565, 1527351320554, 1372581224616, 290747598536, 6839707167, 0] := by
  rw [show D2M8K2.u15717 = KTree.node D2M8K2.u15715 (nat_lit 34180451) (nat_lit 2833255305) (nat_lit 0) D2M8K2.u15716 from rfl, totK_node, atot15715, atot15716]
  decide +kernel

theorem arows15722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15722 = true := by
  rw [show D2M8K2.u15722 = KTree.node D2M8K2.u15720 (nat_lit 34187237) (nat_lit 2371143950) (nat_lit 0) D2M8K2.u15721 from rfl, allE_node, arows15720, irow15722, arows15721]
  all_goals rfl

theorem atot15722 : totK PD2M8K2 D2M8K2.u15722 = [0, 0, 395099004894, 1427513430576, 1396844719893, 304065146387, 12948334120, 0] := by
  rw [show D2M8K2.u15722 = KTree.node D2M8K2.u15720 (nat_lit 34187237) (nat_lit 2371143950) (nat_lit 0) D2M8K2.u15721 from rfl, totK_node, atot15720, atot15721]
  decide +kernel

theorem arows15725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15725 = true := by
  rw [show D2M8K2.u15725 = KTree.node D2M8K2.u15723 (nat_lit 34190901) (nat_lit 1712920774) (nat_lit 0) D2M8K2.u15724 from rfl, allE_node, arows15723, irow15725, arows15724]
  all_goals rfl

theorem atot15725 : totK PD2M8K2 D2M8K2.u15725 = [0, 0, 421297857185, 1522270431485, 1398016204684, 239243549555, 5024003845, 0] := by
  rw [show D2M8K2.u15725 = KTree.node D2M8K2.u15723 (nat_lit 34190901) (nat_lit 1712920774) (nat_lit 0) D2M8K2.u15724 from rfl, totK_node, atot15723, atot15724]
  decide +kernel

theorem arows15729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15729 = true := by
  rw [show D2M8K2.u15729 = KTree.node D2M8K2.u15727 (nat_lit 34194625) (nat_lit 1482125611) (nat_lit 0) D2M8K2.u15728 from rfl, allE_node, arows15727, irow15729, arows15728]
  all_goals rfl

theorem atot15729 : totK PD2M8K2 D2M8K2.u15729 = [0, 0, 0, 596457210384, 1770265852186, 984281112907, 93653971027, 1206465782] := by
  rw [show D2M8K2.u15729 = KTree.node D2M8K2.u15727 (nat_lit 34194625) (nat_lit 1482125611) (nat_lit 0) D2M8K2.u15728 from rfl, totK_node, atot15727, atot15728]
  decide +kernel

theorem arows15732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15732 = true := by
  rw [show D2M8K2.u15732 = KTree.node D2M8K2.u15730 (nat_lit 34200592) (nat_lit 3398309562) (nat_lit 0) D2M8K2.u15731 from rfl, allE_node, arows15730, irow15732, arows15731]
  all_goals rfl

theorem atot15732 : totK PD2M8K2 D2M8K2.u15732 = [0, 0, 0, 828874759840, 1903595763531, 836134457790, 51723477313, 0] := by
  rw [show D2M8K2.u15732 = KTree.node D2M8K2.u15730 (nat_lit 34200592) (nat_lit 3398309562) (nat_lit 0) D2M8K2.u15731 from rfl, totK_node, atot15730, atot15731]
  decide +kernel

theorem arows15740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15740 = true := by
  rw [show D2M8K2.u15740 = KTree.node D2M8K2.u15738 (nat_lit 34207626) (nat_lit 2290178608) (nat_lit 0) D2M8K2.u15739 from rfl, allE_node, arows15738, irow15740, arows15739]
  all_goals rfl

theorem atot15740 : totK PD2M8K2 D2M8K2.u15740 = [0, 0, 0, 545496896409, 1606940347867, 1132470408679, 191073345471, 5395128787] := by
  rw [show D2M8K2.u15740 = KTree.node D2M8K2.u15738 (nat_lit 34207626) (nat_lit 2290178608) (nat_lit 0) D2M8K2.u15739 from rfl, totK_node, atot15738, atot15739]
  decide +kernel

theorem arows15743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15743 = true := by
  rw [show D2M8K2.u15743 = KTree.node D2M8K2.u15741 (nat_lit 34256504) (nat_lit 3741770008) (nat_lit 0) D2M8K2.u15742 from rfl, allE_node, arows15741, irow15743, arows15742]
  all_goals rfl

theorem atot15743 : totK PD2M8K2 D2M8K2.u15743 = [0, 0, 394123133746, 1399878743772, 1342562580837, 393430055865, 24762946045, 0] := by
  rw [show D2M8K2.u15743 = KTree.node D2M8K2.u15741 (nat_lit 34256504) (nat_lit 3741770008) (nat_lit 0) D2M8K2.u15742 from rfl, totK_node, atot15741, atot15742]
  decide +kernel

theorem arows15747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15747 = true := by
  rw [show D2M8K2.u15747 = KTree.node D2M8K2.u15745 (nat_lit 34260510) (nat_lit 3869046296) (nat_lit 0) D2M8K2.u15746 from rfl, allE_node, arows15745, irow15747, arows15746]
  all_goals rfl

theorem atot15747 : totK PD2M8K2 D2M8K2.u15747 = [0, 0, 677613928996, 1796468656633, 1098486477966, 84825776592, 0, 0] := by
  rw [show D2M8K2.u15747 = KTree.node D2M8K2.u15745 (nat_lit 34260510) (nat_lit 3869046296) (nat_lit 0) D2M8K2.u15746 from rfl, totK_node, atot15745, atot15746]
  decide +kernel

theorem arows15750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15750 = true := by
  rw [show D2M8K2.u15750 = KTree.node D2M8K2.u15748 (nat_lit 34265824) (nat_lit 2332861757) (nat_lit 0) D2M8K2.u15749 from rfl, allE_node, arows15748, irow15750, arows15749]
  all_goals rfl

theorem atot15750 : totK PD2M8K2 D2M8K2.u15750 = [0, 0, 477569700225, 1614885925686, 1279742333719, 186311741903, 4626333750, 0] := by
  rw [show D2M8K2.u15750 = KTree.node D2M8K2.u15748 (nat_lit 34265824) (nat_lit 2332861757) (nat_lit 0) D2M8K2.u15749 from rfl, totK_node, atot15748, atot15749]
  decide +kernel

theorem arows15755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15755 = true := by
  rw [show D2M8K2.u15755 = KTree.node D2M8K2.u15753 (nat_lit 34272818) (nat_lit 3800829681) (nat_lit 0) D2M8K2.u15754 from rfl, allE_node, arows15753, irow15755, arows15754]
  all_goals rfl

theorem atot15755 : totK PD2M8K2 D2M8K2.u15755 = [0, 0, 499003881069, 1628464157415, 1240500567661, 183886232194, 4980514959, 0] := by
  rw [show D2M8K2.u15755 = KTree.node D2M8K2.u15753 (nat_lit 34272818) (nat_lit 3800829681) (nat_lit 0) D2M8K2.u15754 from rfl, totK_node, atot15753, atot15754]
  decide +kernel

theorem arows15758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15758 = true := by
  rw [show D2M8K2.u15758 = KTree.node D2M8K2.u15756 (nat_lit 34301307) (nat_lit 3688517945) (nat_lit 0) D2M8K2.u15757 from rfl, allE_node, arows15756, irow15758, arows15757]
  all_goals rfl

theorem atot15758 : totK PD2M8K2 D2M8K2.u15758 = [0, 0, 416217893360, 1587217117120, 1461995981056, 194092897432, 1369150432, 0] := by
  rw [show D2M8K2.u15758 = KTree.node D2M8K2.u15756 (nat_lit 34301307) (nat_lit 3688517945) (nat_lit 0) D2M8K2.u15757 from rfl, totK_node, atot15756, atot15757]
  decide +kernel

theorem arows15762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15762 = true := by
  rw [show D2M8K2.u15762 = KTree.node D2M8K2.u15760 (nat_lit 34304585) (nat_lit 1806589123) (nat_lit 0) D2M8K2.u15761 from rfl, allE_node, arows15760, irow15762, arows15761]
  all_goals rfl

theorem atot15762 : totK PD2M8K2 D2M8K2.u15762 = [0, 0, 422276889940, 1464418803335, 1380379865015, 354711669033, 16311238869, 0] := by
  rw [show D2M8K2.u15762 = KTree.node D2M8K2.u15760 (nat_lit 34304585) (nat_lit 1806589123) (nat_lit 0) D2M8K2.u15761 from rfl, totK_node, atot15760, atot15761]
  decide +kernel

theorem arows15765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15765 = true := by
  rw [show D2M8K2.u15765 = KTree.node D2M8K2.u15763 (nat_lit 34308064) (nat_lit 3589298066) (nat_lit 0) D2M8K2.u15764 from rfl, allE_node, arows15763, irow15765, arows15764]
  all_goals rfl

theorem atot15765 : totK PD2M8K2 D2M8K2.u15765 = [0, 0, 343285879541, 1419884308090, 1544681932626, 316800177318, 9030142127, 0] := by
  rw [show D2M8K2.u15765 = KTree.node D2M8K2.u15763 (nat_lit 34308064) (nat_lit 3589298066) (nat_lit 0) D2M8K2.u15764 from rfl, totK_node, atot15763, atot15764]
  decide +kernel

theorem arows15771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15771 = true := by
  rw [show D2M8K2.u15771 = KTree.node D2M8K2.u15769 (nat_lit 34315375) (nat_lit 1611060035) (nat_lit 0) D2M8K2.u15770 from rfl, allE_node, arows15769, irow15771, arows15770]
  all_goals rfl

theorem atot15771 : totK PD2M8K2 D2M8K2.u15771 = [0, 0, 441741639255, 1541245606485, 1401814466490, 259614776784, 5299605691, 0] := by
  rw [show D2M8K2.u15771 = KTree.node D2M8K2.u15769 (nat_lit 34315375) (nat_lit 1611060035) (nat_lit 0) D2M8K2.u15770 from rfl, totK_node, atot15769, atot15770]
  decide +kernel

theorem arows15774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15774 = true := by
  rw [show D2M8K2.u15774 = KTree.node D2M8K2.u15772 (nat_lit 34339586) (nat_lit 3522771503) (nat_lit 0) D2M8K2.u15773 from rfl, allE_node, arows15772, irow15774, arows15773]
  all_goals rfl

theorem atot15774 : totK PD2M8K2 D2M8K2.u15774 = [0, 433286471789, 1193649943215, 959640400435, 671937826450, 286820177699, 20713713085, 0] := by
  rw [show D2M8K2.u15774 = KTree.node D2M8K2.u15772 (nat_lit 34339586) (nat_lit 3522771503) (nat_lit 0) D2M8K2.u15773 from rfl, totK_node, atot15772, atot15773]
  decide +kernel

theorem arows15778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15778 = true := by
  rw [show D2M8K2.u15778 = KTree.node D2M8K2.u15776 (nat_lit 34346937) (nat_lit 1862413635) (nat_lit 0) D2M8K2.u15777 from rfl, allE_node, arows15776, irow15778, arows15777]
  all_goals rfl

theorem atot15778 : totK PD2M8K2 D2M8K2.u15778 = [0, 325096442640, 1468424104026, 1533727244068, 264589862587, 5398830306, 0, 0] := by
  rw [show D2M8K2.u15778 = KTree.node D2M8K2.u15776 (nat_lit 34346937) (nat_lit 1862413635) (nat_lit 0) D2M8K2.u15777 from rfl, totK_node, atot15776, atot15777]
  decide +kernel

theorem arows15781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15781 = true := by
  rw [show D2M8K2.u15781 = KTree.node D2M8K2.u15779 (nat_lit 34350666) (nat_lit 3832192377) (nat_lit 0) D2M8K2.u15780 from rfl, allE_node, arows15779, irow15781, arows15780]
  all_goals rfl

theorem atot15781 : totK PD2M8K2 D2M8K2.u15781 = [0, 423460293700, 1443229340377, 1376394185521, 327812150115, 13250685261, 0, 0] := by
  rw [show D2M8K2.u15781 = KTree.node D2M8K2.u15779 (nat_lit 34350666) (nat_lit 3832192377) (nat_lit 0) D2M8K2.u15780 from rfl, totK_node, atot15779, atot15780]
  decide +kernel

theorem arows15786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15786 = true := by
  rw [show D2M8K2.u15786 = KTree.node D2M8K2.u15784 (nat_lit 34353850) (nat_lit 1941427838) (nat_lit 0) D2M8K2.u15785 from rfl, allE_node, arows15784, irow15786, arows15785]
  all_goals rfl

theorem atot15786 : totK PD2M8K2 D2M8K2.u15786 = [0, 447052610153, 1517001160640, 1363934050257, 235911950322, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15786 = KTree.node D2M8K2.u15784 (nat_lit 34353850) (nat_lit 1941427838) (nat_lit 0) D2M8K2.u15785 from rfl, totK_node, atot15784, atot15785]
  decide +kernel

theorem arows15789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15789 = true := by
  rw [show D2M8K2.u15789 = KTree.node D2M8K2.u15787 (nat_lit 34357752) (nat_lit 3415880598) (nat_lit 0) D2M8K2.u15788 from rfl, allE_node, arows15787, irow15789, arows15788]
  all_goals rfl

theorem atot15789 : totK PD2M8K2 D2M8K2.u15789 = [0, 347849501403, 1377115952472, 1502979184037, 377027932463, 9938656398, 0, 0] := by
  rw [show D2M8K2.u15789 = KTree.node D2M8K2.u15787 (nat_lit 34357752) (nat_lit 3415880598) (nat_lit 0) D2M8K2.u15788 from rfl, totK_node, atot15787, atot15788]
  decide +kernel

theorem arows15793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15793 = true := by
  rw [show D2M8K2.u15793 = KTree.node D2M8K2.u15791 (nat_lit 34361003) (nat_lit 2942248401) (nat_lit 0) D2M8K2.u15792 from rfl, allE_node, arows15791, irow15793, arows15792]
  all_goals rfl

theorem atot15793 : totK PD2M8K2 D2M8K2.u15793 = [0, 0, 483186049783, 1622964369193, 1211224222539, 162476546387, 1369150432, 0] := by
  rw [show D2M8K2.u15793 = KTree.node D2M8K2.u15791 (nat_lit 34361003) (nat_lit 2942248401) (nat_lit 0) D2M8K2.u15792 from rfl, totK_node, atot15791, atot15792]
  decide +kernel

theorem arows15796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15796 = true := by
  rw [show D2M8K2.u15796 = KTree.node D2M8K2.u15794 (nat_lit 34370238) (nat_lit 3946891661) (nat_lit 0) D2M8K2.u15795 from rfl, allE_node, arows15794, irow15796, arows15795]
  all_goals rfl

theorem atot15796 : totK PD2M8K2 D2M8K2.u15796 = [0, 0, 755152169715, 1908488229390, 859961373623, 42141323070, 0, 0] := by
  rw [show D2M8K2.u15796 = KTree.node D2M8K2.u15794 (nat_lit 34370238) (nat_lit 3946891661) (nat_lit 0) D2M8K2.u15795 from rfl, totK_node, atot15794, atot15795]
  decide +kernel

theorem arows15803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15803 = true := by
  rw [show D2M8K2.u15803 = KTree.node D2M8K2.u15801 (nat_lit 34376941) (nat_lit 1133093022) (nat_lit 0) D2M8K2.u15802 from rfl, allE_node, arows15801, irow15803, arows15802]
  all_goals rfl

theorem atot15803 : totK PD2M8K2 D2M8K2.u15803 = [0, 0, 729769713580, 1917547217067, 882381744166, 38945391355, 0, 0] := by
  rw [show D2M8K2.u15803 = KTree.node D2M8K2.u15801 (nat_lit 34376941) (nat_lit 1133093022) (nat_lit 0) D2M8K2.u15802 from rfl, totK_node, atot15801, atot15802]
  decide +kernel

theorem arows15806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15806 = true := by
  rw [show D2M8K2.u15806 = KTree.node D2M8K2.u15804 (nat_lit 34385156) (nat_lit 3609684929) (nat_lit 0) D2M8K2.u15805 from rfl, allE_node, arows15804, irow15806, arows15805]
  all_goals rfl

theorem atot15806 : totK PD2M8K2 D2M8K2.u15806 = [0, 442620365002, 1415748416967, 1335666578008, 438790198967, 36487900741, 0, 0] := by
  rw [show D2M8K2.u15806 = KTree.node D2M8K2.u15804 (nat_lit 34385156) (nat_lit 3609684929) (nat_lit 0) D2M8K2.u15805 from rfl, totK_node, atot15804, atot15805]
  decide +kernel

theorem arows15810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15810 = true := by
  rw [show D2M8K2.u15810 = KTree.node D2M8K2.u15808 (nat_lit 34388420) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u15809 from rfl, allE_node, arows15808, irow15810, arows15809]
  all_goals rfl

theorem atot15810 : totK PD2M8K2 D2M8K2.u15810 = [0, 331688504469, 1340561663172, 1559278214160, 436181932789, 16517381251, 0, 0] := by
  rw [show D2M8K2.u15810 = KTree.node D2M8K2.u15808 (nat_lit 34388420) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u15809 from rfl, totK_node, atot15808, atot15809]
  decide +kernel

theorem arows15813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15813 = true := by
  rw [show D2M8K2.u15813 = KTree.node D2M8K2.u15811 (nat_lit 34392140) (nat_lit 3143902764) (nat_lit 0) D2M8K2.u15812 from rfl, allE_node, arows15811, irow15813, arows15812]
  all_goals rfl

theorem atot15813 : totK PD2M8K2 D2M8K2.u15813 = [0, 425109459846, 1451060210728, 1384715567242, 327499931136, 13237669976, 0, 0] := by
  rw [show D2M8K2.u15813 = KTree.node D2M8K2.u15811 (nat_lit 34392140) (nat_lit 3143902764) (nat_lit 0) D2M8K2.u15812 from rfl, totK_node, atot15811, atot15812]
  decide +kernel

theorem arows15818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15818 = true := by
  rw [show D2M8K2.u15818 = KTree.node D2M8K2.u15816 (nat_lit 34395316) (nat_lit 3992702721) (nat_lit 0) D2M8K2.u15817 from rfl, allE_node, arows15816, irow15818, arows15817]
  all_goals rfl

theorem atot15818 : totK PD2M8K2 D2M8K2.u15818 = [0, 451107252812, 1602492377877, 1386937274518, 214225634394, 3880716147, 0, 0] := by
  rw [show D2M8K2.u15818 = KTree.node D2M8K2.u15816 (nat_lit 34395316) (nat_lit 3992702721) (nat_lit 0) D2M8K2.u15817 from rfl, totK_node, atot15816, atot15817]
  decide +kernel

theorem arows15821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15821 = true := by
  rw [show D2M8K2.u15821 = KTree.node D2M8K2.u15819 (nat_lit 34399295) (nat_lit 2760641158) (nat_lit 0) D2M8K2.u15820 from rfl, allE_node, arows15819, irow15821, arows15820]
  all_goals rfl

theorem atot15821 : totK PD2M8K2 D2M8K2.u15821 = [0, 350791537959, 1329861691784, 1506352446817, 436303556517, 17729668807, 0, 0] := by
  rw [show D2M8K2.u15821 = KTree.node D2M8K2.u15819 (nat_lit 34399295) (nat_lit 2760641158) (nat_lit 0) D2M8K2.u15820 from rfl, totK_node, atot15819, atot15820]
  decide +kernel

theorem arows15825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15825 = true := by
  rw [show D2M8K2.u15825 = KTree.node D2M8K2.u15823 (nat_lit 34405953) (nat_lit 1402756439) (nat_lit 0) D2M8K2.u15824 from rfl, allE_node, arows15823, irow15825, arows15824]
  all_goals rfl

theorem atot15825 : totK PD2M8K2 D2M8K2.u15825 = [0, 0, 441536895049, 1448221161486, 1356937588302, 389076103431, 25214516004, 0] := by
  rw [show D2M8K2.u15825 = KTree.node D2M8K2.u15823 (nat_lit 34405953) (nat_lit 1402756439) (nat_lit 0) D2M8K2.u15824 from rfl, totK_node, atot15823, atot15824]
  decide +kernel

theorem arows15828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15828 = true := by
  rw [show D2M8K2.u15828 = KTree.node D2M8K2.u15826 (nat_lit 34409306) (nat_lit 3885127174) (nat_lit 0) D2M8K2.u15827 from rfl, allE_node, arows15826, irow15828, arows15827]
  all_goals rfl

theorem atot15828 : totK PD2M8K2 D2M8K2.u15828 = [0, 0, 400836574095, 1468437837481, 1452920671573, 321628834634, 9425257959, 0] := by
  rw [show D2M8K2.u15828 = KTree.node D2M8K2.u15826 (nat_lit 34409306) (nat_lit 3885127174) (nat_lit 0) D2M8K2.u15827 from rfl, totK_node, atot15826, atot15827]
  decide +kernel

theorem arows15834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15834 = true := by
  rw [show D2M8K2.u15834 = KTree.node D2M8K2.u15832 (nat_lit 34413120) (nat_lit 3735470318) (nat_lit 0) D2M8K2.u15833 from rfl, allE_node, arows15832, irow15834, arows15833]
  all_goals rfl

theorem atot15834 : totK PD2M8K2 D2M8K2.u15834 = [0, 0, 463175915061, 1538036302842, 1347825016440, 248809612945, 5218872685, 0] := by
  rw [show D2M8K2.u15834 = KTree.node D2M8K2.u15832 (nat_lit 34413120) (nat_lit 3735470318) (nat_lit 0) D2M8K2.u15833 from rfl, totK_node, atot15832, atot15833]
  decide +kernel

theorem arows15837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15837 = true := by
  rw [show D2M8K2.u15837 = KTree.node D2M8K2.u15835 (nat_lit 34416972) (nat_lit 2618681704) (nat_lit 0) D2M8K2.u15836 from rfl, allE_node, arows15835, irow15837, arows15836]
  all_goals rfl

theorem atot15837 : totK PD2M8K2 D2M8K2.u15837 = [0, 0, 506751342733, 1650265738960, 1331528563815, 174466072967, 1415142070, 0] := by
  rw [show D2M8K2.u15837 = KTree.node D2M8K2.u15835 (nat_lit 34416972) (nat_lit 2618681704) (nat_lit 0) D2M8K2.u15836 from rfl, totK_node, atot15835, atot15836]
  decide +kernel

theorem arows15841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15841 = true := by
  rw [show D2M8K2.u15841 = KTree.node D2M8K2.u15839 (nat_lit 34420878) (nat_lit 3115461861) (nat_lit 0) D2M8K2.u15840 from rfl, allE_node, arows15839, irow15841, arows15840]
  all_goals rfl

theorem atot15841 : totK PD2M8K2 D2M8K2.u15841 = [0, 243831636970, 707569317893, 1160360611572, 1171491229256, 293543030478, 9302370699, 0] := by
  rw [show D2M8K2.u15841 = KTree.node D2M8K2.u15839 (nat_lit 34420878) (nat_lit 3115461861) (nat_lit 0) D2M8K2.u15840 from rfl, totK_node, atot15839, atot15840]
  decide +kernel

theorem arows15844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15844 = true := by
  rw [show D2M8K2.u15844 = KTree.node D2M8K2.u15842 (nat_lit 34465928) (nat_lit 3861468663) (nat_lit 0) D2M8K2.u15843 from rfl, allE_node, arows15842, irow15844, arows15843]
  all_goals rfl

theorem atot15844 : totK PD2M8K2 D2M8K2.u15844 = [0, 420471202410, 1574430020967, 1420678480480, 196253216367, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15844 = KTree.node D2M8K2.u15842 (nat_lit 34465928) (nat_lit 3861468663) (nat_lit 0) D2M8K2.u15843 from rfl, totK_node, atot15842, atot15843]
  decide +kernel

theorem arows15849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15849 = true := by
  rw [show D2M8K2.u15849 = KTree.node D2M8K2.u15847 (nat_lit 34469326) (nat_lit 3917406774) (nat_lit 0) D2M8K2.u15848 from rfl, allE_node, arows15847, irow15849, arows15848]
  all_goals rfl

theorem atot15849 : totK PD2M8K2 D2M8K2.u15849 = [0, 349171680814, 1249005155413, 1428979688773, 561622854947, 35992185241, 0, 0] := by
  rw [show D2M8K2.u15849 = KTree.node D2M8K2.u15847 (nat_lit 34469326) (nat_lit 3917406774) (nat_lit 0) D2M8K2.u15848 from rfl, totK_node, atot15847, atot15848]
  decide +kernel

theorem arows15852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15852 = true := by
  rw [show D2M8K2.u15852 = KTree.node D2M8K2.u15850 (nat_lit 34475488) (nat_lit 1824638906) (nat_lit 0) D2M8K2.u15851 from rfl, allE_node, arows15850, irow15852, arows15851]
  all_goals rfl

theorem atot15852 : totK PD2M8K2 D2M8K2.u15852 = [0, 352395409821, 1397239139732, 1495755628272, 353405981230, 13250685261, 0, 0] := by
  rw [show D2M8K2.u15852 = KTree.node D2M8K2.u15850 (nat_lit 34475488) (nat_lit 1824638906) (nat_lit 0) D2M8K2.u15851 from rfl, totK_node, atot15850, atot15851]
  decide +kernel

theorem arows15856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15856 = true := by
  rw [show D2M8K2.u15856 = KTree.node D2M8K2.u15854 (nat_lit 34478888) (nat_lit 3871746995) (nat_lit 0) D2M8K2.u15855 from rfl, allE_node, arows15854, irow15856, arows15855]
  all_goals rfl

theorem atot15856 : totK PD2M8K2 D2M8K2.u15856 = [0, 474593861401, 1551220608032, 1333283035815, 220989300234, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15856 = KTree.node D2M8K2.u15854 (nat_lit 34478888) (nat_lit 3871746995) (nat_lit 0) D2M8K2.u15855 from rfl, totK_node, atot15854, atot15855]
  decide +kernel

theorem arows15859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15859 = true := by
  rw [show D2M8K2.u15859 = KTree.node D2M8K2.u15857 (nat_lit 34482404) (nat_lit 2139908631) (nat_lit 0) D2M8K2.u15858 from rfl, allE_node, arows15857, irow15859, arows15858]
  all_goals rfl

theorem atot15859 : totK PD2M8K2 D2M8K2.u15859 = [0, 262677949119, 1274664206516, 1603278705972, 457295086777, 22013628430, 0, 0] := by
  rw [show D2M8K2.u15859 = KTree.node D2M8K2.u15857 (nat_lit 34482404) (nat_lit 2139908631) (nat_lit 0) D2M8K2.u15858 from rfl, totK_node, atot15857, atot15858]
  decide +kernel

theorem arows15869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15869 = true := by
  rw [show D2M8K2.u15869 = KTree.node D2M8K2.u15867 (nat_lit 34485747) (nat_lit 1055151510) (nat_lit 0) D2M8K2.u15868 from rfl, allE_node, arows15867, irow15869, arows15868]
  all_goals rfl

theorem atot15869 : totK PD2M8K2 D2M8K2.u15869 = [0, 0, 482039762552, 1642080578945, 1255934451460, 145013368316, 1239866073, 0] := by
  rw [show D2M8K2.u15869 = KTree.node D2M8K2.u15867 (nat_lit 34485747) (nat_lit 1055151510) (nat_lit 0) D2M8K2.u15868 from rfl, totK_node, atot15867, atot15868]
  decide +kernel

theorem arows15872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15872 = true := by
  rw [show D2M8K2.u15872 = KTree.node D2M8K2.u15870 (nat_lit 34494602) (nat_lit 3302444197) (nat_lit 0) D2M8K2.u15871 from rfl, allE_node, arows15870, irow15872, arows15871]
  all_goals rfl

theorem atot15872 : totK PD2M8K2 D2M8K2.u15872 = [0, 0, 705053015296, 1878773217947, 982349023433, 63974389740, 0, 0] := by
  rw [show D2M8K2.u15872 = KTree.node D2M8K2.u15870 (nat_lit 34494602) (nat_lit 3302444197) (nat_lit 0) D2M8K2.u15871 from rfl, totK_node, atot15870, atot15871]
  decide +kernel

theorem arows15876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15876 = true := by
  rw [show D2M8K2.u15876 = KTree.node D2M8K2.u15874 (nat_lit 34497892) (nat_lit 3619914485) (nat_lit 0) D2M8K2.u15875 from rfl, allE_node, arows15874, irow15876, arows15875]
  all_goals rfl

theorem atot15876 : totK PD2M8K2 D2M8K2.u15876 = [0, 0, 397972036307, 1457341578561, 1341713143876, 306012512020, 13105450397, 0] := by
  rw [show D2M8K2.u15876 = KTree.node D2M8K2.u15874 (nat_lit 34497892) (nat_lit 3619914485) (nat_lit 0) D2M8K2.u15875 from rfl, totK_node, atot15874, atot15875]
  decide +kernel

theorem arows15879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15879 = true := by
  rw [show D2M8K2.u15879 = KTree.node D2M8K2.u15877 (nat_lit 34501629) (nat_lit 1436298848) (nat_lit 0) D2M8K2.u15878 from rfl, allE_node, arows15877, irow15879, arows15878]
  all_goals rfl

theorem atot15879 : totK PD2M8K2 D2M8K2.u15879 = [0, 89266124844, 546934526573, 1464178294519, 1238551849604, 196705456950, 4720618446, 0] := by
  rw [show D2M8K2.u15879 = KTree.node D2M8K2.u15877 (nat_lit 34501629) (nat_lit 1436298848) (nat_lit 0) D2M8K2.u15878 from rfl, totK_node, atot15877, atot15878]
  decide +kernel

theorem arows15884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15884 = true := by
  rw [show D2M8K2.u15884 = KTree.node D2M8K2.u15882 (nat_lit 34506496) (nat_lit 3551995409) (nat_lit 0) D2M8K2.u15883 from rfl, allE_node, arows15882, irow15884, arows15883]
  all_goals rfl

theorem atot15884 : totK PD2M8K2 D2M8K2.u15884 = [0, 468206115189, 1607535887132, 1339293309910, 174896013859, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15884 = KTree.node D2M8K2.u15882 (nat_lit 34506496) (nat_lit 3551995409) (nat_lit 0) D2M8K2.u15883 from rfl, totK_node, atot15882, atot15883]
  decide +kernel

theorem arows15887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15887 = true := by
  rw [show D2M8K2.u15887 = KTree.node D2M8K2.u15885 (nat_lit 34510444) (nat_lit 3177994736) (nat_lit 514) D2M8K2.u15886 from rfl, allE_node, arows15885, irow15887, arows15886]
  all_goals rfl

theorem atot15887 : totK PD2M8K2 D2M8K2.u15887 = [0, 409114234512, 1448217528751, 1404570199592, 378347298505, 15407717105, 0, 0] := by
  rw [show D2M8K2.u15887 = KTree.node D2M8K2.u15885 (nat_lit 34510444) (nat_lit 3177994736) (nat_lit 514) D2M8K2.u15886 from rfl, totK_node, atot15885, atot15886]
  decide +kernel

theorem arows15891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15891 = true := by
  rw [show D2M8K2.u15891 = KTree.node D2M8K2.u15889 (nat_lit 34517001) (nat_lit 1241184453) (nat_lit 0) D2M8K2.u15890 from rfl, allE_node, arows15889, irow15891, arows15890]
  all_goals rfl

theorem atot15891 : totK PD2M8K2 D2M8K2.u15891 = [0, 360755751474, 1414325085948, 1464122522709, 341343446458, 13250685261, 0, 0] := by
  rw [show D2M8K2.u15891 = KTree.node D2M8K2.u15889 (nat_lit 34517001) (nat_lit 1241184453) (nat_lit 0) D2M8K2.u15890 from rfl, totK_node, atot15889, atot15890]
  decide +kernel

theorem arows15894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15894 = true := by
  rw [show D2M8K2.u15894 = KTree.node D2M8K2.u15892 (nat_lit 34520346) (nat_lit 3621399480) (nat_lit 0) D2M8K2.u15893 from rfl, allE_node, arows15892, irow15894, arows15893]
  all_goals rfl

theorem atot15894 : totK PD2M8K2 D2M8K2.u15894 = [0, 320437801854, 1389174466226, 1562233784058, 329792636685, 6350335412, 0, 0] := by
  rw [show D2M8K2.u15894 = KTree.node D2M8K2.u15892 (nat_lit 34520346) (nat_lit 3621399480) (nat_lit 0) D2M8K2.u15893 from rfl, totK_node, atot15892, atot15893]
  decide +kernel

theorem arows15900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15900 = true := by
  rw [show D2M8K2.u15900 = KTree.node D2M8K2.u15898 (nat_lit 34527812) (nat_lit 3278264574) (nat_lit 0) D2M8K2.u15899 from rfl, allE_node, arows15898, irow15900, arows15899]
  all_goals rfl

theorem atot15900 : totK PD2M8K2 D2M8K2.u15900 = [0, 0, 518813602769, 1708663106077, 1180929156110, 119095276625, 1138244013, 0] := by
  rw [show D2M8K2.u15900 = KTree.node D2M8K2.u15898 (nat_lit 34527812) (nat_lit 3278264574) (nat_lit 0) D2M8K2.u15899 from rfl, totK_node, atot15898, atot15899]
  decide +kernel

theorem arows15903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15903 = true := by
  rw [show D2M8K2.u15903 = KTree.node D2M8K2.u15901 (nat_lit 34536773) (nat_lit 1951902496) (nat_lit 0) D2M8K2.u15902 from rfl, allE_node, arows15901, irow15903, arows15902]
  all_goals rfl

theorem atot15903 : totK PD2M8K2 D2M8K2.u15903 = [0, 0, 750984247216, 1908161746236, 888391553982, 49287460177, 0, 0] := by
  rw [show D2M8K2.u15903 = KTree.node D2M8K2.u15901 (nat_lit 34536773) (nat_lit 1951902496) (nat_lit 0) D2M8K2.u15902 from rfl, totK_node, atot15901, atot15902]
  decide +kernel

theorem arows15907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15907 = true := by
  rw [show D2M8K2.u15907 = KTree.node D2M8K2.u15905 (nat_lit 34541406) (nat_lit 3512695474) (nat_lit 0) D2M8K2.u15906 from rfl, allE_node, arows15905, irow15907, arows15906]
  all_goals rfl

theorem atot15907 : totK PD2M8K2 D2M8K2.u15907 = [0, 250622349935, 795923881164, 1283713641243, 1018389840008, 175696762697, 4977114383, 0] := by
  rw [show D2M8K2.u15907 = KTree.node D2M8K2.u15905 (nat_lit 34541406) (nat_lit 3512695474) (nat_lit 0) D2M8K2.u15906 from rfl, totK_node, atot15905, atot15906]
  decide +kernel

theorem arows15910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15910 = true := by
  rw [show D2M8K2.u15910 = KTree.node D2M8K2.u15908 (nat_lit 34548891) (nat_lit 3339836139) (nat_lit 0) D2M8K2.u15909 from rfl, allE_node, arows15908, irow15910, arows15909]
  all_goals rfl

theorem atot15910 : totK PD2M8K2 D2M8K2.u15910 = [0, 419425061436, 1579635081383, 1419552707989, 198884180264, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15910 = KTree.node D2M8K2.u15908 (nat_lit 34548891) (nat_lit 3339836139) (nat_lit 0) D2M8K2.u15909 from rfl, totK_node, atot15908, atot15909]
  decide +kernel

theorem arows15915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15915 = true := by
  rw [show D2M8K2.u15915 = KTree.node D2M8K2.u15913 (nat_lit 34552324) (nat_lit 2363536875) (nat_lit 0) D2M8K2.u15914 from rfl, allE_node, arows15913, irow15915, arows15914]
  all_goals rfl

theorem atot15915 : totK PD2M8K2 D2M8K2.u15915 = [0, 317240270130, 1243925843094, 1490436434292, 571125188181, 35989886328, 0, 0] := by
  rw [show D2M8K2.u15915 = KTree.node D2M8K2.u15913 (nat_lit 34552324) (nat_lit 2363536875) (nat_lit 0) D2M8K2.u15914 from rfl, totK_node, atot15913, atot15914]
  decide +kernel

theorem arows15918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15918 = true := by
  rw [show D2M8K2.u15918 = KTree.node D2M8K2.u15916 (nat_lit 34555570) (nat_lit 3683486168) (nat_lit 0) D2M8K2.u15917 from rfl, allE_node, arows15916, irow15918, arows15917]
  all_goals rfl

theorem atot15918 : totK PD2M8K2 D2M8K2.u15918 = [0, 490294916201, 1547487259858, 1352835955196, 261389839008, 7820929001, 0, 0] := by
  rw [show D2M8K2.u15918 = KTree.node D2M8K2.u15916 (nat_lit 34555570) (nat_lit 3683486168) (nat_lit 0) D2M8K2.u15917 from rfl, totK_node, atot15916, atot15917]
  decide +kernel

theorem arows15922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15922 = true := by
  rw [show D2M8K2.u15922 = KTree.node D2M8K2.u15920 (nat_lit 34559452) (nat_lit 3093478044) (nat_lit 0) D2M8K2.u15921 from rfl, allE_node, arows15920, irow15922, arows15921]
  all_goals rfl

theorem atot15922 : totK PD2M8K2 D2M8K2.u15922 = [0, 375014462591, 1430948652453, 1458960990547, 343082614446, 13243784863, 0, 0] := by
  rw [show D2M8K2.u15922 = KTree.node D2M8K2.u15920 (nat_lit 34559452) (nat_lit 3093478044) (nat_lit 0) D2M8K2.u15921 from rfl, totK_node, atot15920, atot15921]
  decide +kernel

theorem arows15925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15925 = true := by
  rw [show D2M8K2.u15925 = KTree.node D2M8K2.u15923 (nat_lit 34565911) (nat_lit 1105440913) (nat_lit 0) D2M8K2.u15924 from rfl, allE_node, arows15923, irow15925, arows15924]
  all_goals rfl

theorem atot15925 : totK PD2M8K2 D2M8K2.u15925 = [0, 182433760473, 1084192119126, 1717400566524, 595798567003, 27384849158, 0, 0] := by
  rw [show D2M8K2.u15925 = KTree.node D2M8K2.u15923 (nat_lit 34565911) (nat_lit 1105440913) (nat_lit 0) D2M8K2.u15924 from rfl, totK_node, atot15923, atot15924]
  decide +kernel

theorem arows15932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15932 = true := by
  rw [show D2M8K2.u15932 = KTree.node D2M8K2.u15930 (nat_lit 34569517) (nat_lit 1362935374) (nat_lit 0) D2M8K2.u15931 from rfl, allE_node, arows15930, irow15932, arows15931]
  all_goals rfl

theorem atot15932 : totK PD2M8K2 D2M8K2.u15932 = [0, 0, 499570462802, 1624637312817, 1306446109255, 155202712465, 1310285577, 0] := by
  rw [show D2M8K2.u15932 = KTree.node D2M8K2.u15930 (nat_lit 34569517) (nat_lit 1362935374) (nat_lit 0) D2M8K2.u15931 from rfl, totK_node, atot15930, atot15931]
  decide +kernel

theorem arows15935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15935 = true := by
  rw [show D2M8K2.u15935 = KTree.node D2M8K2.u15933 (nat_lit 34574442) (nat_lit 3063351482) (nat_lit 0) D2M8K2.u15934 from rfl, allE_node, arows15933, irow15935, arows15934]
  all_goals rfl

theorem atot15935 : totK PD2M8K2 D2M8K2.u15935 = [0, 0, 501885980326, 1619193382139, 1292738086984, 198873626240, 4879840392, 0] := by
  rw [show D2M8K2.u15935 = KTree.node D2M8K2.u15933 (nat_lit 34574442) (nat_lit 3063351482) (nat_lit 0) D2M8K2.u15934 from rfl, totK_node, atot15933, atot15934]
  decide +kernel

theorem arows15939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15939 = true := by
  rw [show D2M8K2.u15939 = KTree.node D2M8K2.u15937 (nat_lit 34578692) (nat_lit 3375452311) (nat_lit 0) D2M8K2.u15938 from rfl, allE_node, arows15937, irow15939, arows15938]
  all_goals rfl

theorem atot15939 : totK PD2M8K2 D2M8K2.u15939 = [0, 0, 428226590381, 1546984577087, 1370800525379, 229899189010, 4931404646, 0] := by
  rw [show D2M8K2.u15939 = KTree.node D2M8K2.u15937 (nat_lit 34578692) (nat_lit 3375452311) (nat_lit 0) D2M8K2.u15938 from rfl, totK_node, atot15937, atot15938]
  decide +kernel

theorem arows15942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15942 = true := by
  rw [show D2M8K2.u15942 = KTree.node D2M8K2.u15940 (nat_lit 34585679) (nat_lit 2161348375) (nat_lit 0) D2M8K2.u15941 from rfl, allE_node, arows15940, irow15942, arows15941]
  all_goals rfl

theorem atot15942 : totK PD2M8K2 D2M8K2.u15942 = [0, 0, 433938177331, 1495097444022, 1364935700444, 286217816660, 8424427256, 0] := by
  rw [show D2M8K2.u15942 = KTree.node D2M8K2.u15940 (nat_lit 34585679) (nat_lit 2161348375) (nat_lit 0) D2M8K2.u15941 from rfl, totK_node, atot15940, atot15941]
  decide +kernel

theorem arows15947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15947 = true := by
  rw [show D2M8K2.u15947 = KTree.node D2M8K2.u15945 (nat_lit 34588870) (nat_lit 2719067660) (nat_lit 0) D2M8K2.u15946 from rfl, allE_node, arows15945, irow15947, arows15946]
  all_goals rfl

theorem atot15947 : totK PD2M8K2 D2M8K2.u15947 = [0, 0, 431998163385, 1506614411219, 1334803138856, 270791577268, 14695891242, 0] := by
  rw [show D2M8K2.u15947 = KTree.node D2M8K2.u15945 (nat_lit 34588870) (nat_lit 2719067660) (nat_lit 0) D2M8K2.u15946 from rfl, totK_node, atot15945, atot15946]
  decide +kernel

theorem arows15950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15950 = true := by
  rw [show D2M8K2.u15950 = KTree.node D2M8K2.u15948 (nat_lit 34596340) (nat_lit 4003057398) (nat_lit 0) D2M8K2.u15949 from rfl, allE_node, arows15948, irow15950, arows15949]
  all_goals rfl

theorem atot15950 : totK PD2M8K2 D2M8K2.u15950 = [0, 0, 518609512973, 1673515500266, 1266609299055, 135815181104, 1164319620, 0] := by
  rw [show D2M8K2.u15950 = KTree.node D2M8K2.u15948 (nat_lit 34596340) (nat_lit 4003057398) (nat_lit 0) D2M8K2.u15949 from rfl, totK_node, atot15948, atot15949]
  decide +kernel

theorem arows15954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15954 = true := by
  rw [show D2M8K2.u15954 = KTree.node D2M8K2.u15952 (nat_lit 34600621) (nat_lit 1326937735) (nat_lit 0) D2M8K2.u15953 from rfl, allE_node, arows15952, irow15954, arows15953]
  all_goals rfl

theorem atot15954 : totK PD2M8K2 D2M8K2.u15954 = [0, 0, 461853153277, 1546959374653, 1331349254974, 233929156027, 5455647540, 0] := by
  rw [show D2M8K2.u15954 = KTree.node D2M8K2.u15952 (nat_lit 34600621) (nat_lit 1326937735) (nat_lit 0) D2M8K2.u15953 from rfl, totK_node, atot15952, atot15953]
  decide +kernel

theorem arows15957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15957 = true := by
  rw [show D2M8K2.u15957 = KTree.node D2M8K2.u15955 (nat_lit 34604453) (nat_lit 2316525931) (nat_lit 0) D2M8K2.u15956 from rfl, allE_node, arows15955, irow15957, arows15956]
  all_goals rfl

theorem atot15957 : totK PD2M8K2 D2M8K2.u15957 = [0, 0, 534811437377, 1691630509429, 1233771653268, 120283184998, 1096505104, 0] := by
  rw [show D2M8K2.u15957 = KTree.node D2M8K2.u15955 (nat_lit 34604453) (nat_lit 2316525931) (nat_lit 0) D2M8K2.u15956 from rfl, totK_node, atot15955, atot15956]
  decide +kernel

theorem arows15963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15963 = true := by
  rw [show D2M8K2.u15963 = KTree.node D2M8K2.u15961 (nat_lit 34608296) (nat_lit 1530286350) (nat_lit 0) D2M8K2.u15962 from rfl, allE_node, arows15961, irow15963, arows15962]
  all_goals rfl

theorem atot15963 : totK PD2M8K2 D2M8K2.u15963 = [0, 0, 19692840307, 945859302329, 1935948105827, 605991518063, 21566532531, 0] := by
  rw [show D2M8K2.u15963 = KTree.node D2M8K2.u15961 (nat_lit 34608296) (nat_lit 1530286350) (nat_lit 0) D2M8K2.u15962 from rfl, totK_node, atot15961, atot15962]
  decide +kernel

theorem arows15966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15966 = true := by
  rw [show D2M8K2.u15966 = KTree.node D2M8K2.u15964 (nat_lit 34615912) (nat_lit 3901240501) (nat_lit 0) D2M8K2.u15965 from rfl, allE_node, arows15964, irow15966, arows15965]
  all_goals rfl

theorem atot15966 : totK PD2M8K2 D2M8K2.u15966 = [0, 0, 0, 588480419066, 1790150808720, 1013796129552, 95499263297, 1310517177] := by
  rw [show D2M8K2.u15966 = KTree.node D2M8K2.u15964 (nat_lit 34615912) (nat_lit 3901240501) (nat_lit 0) D2M8K2.u15965 from rfl, totK_node, atot15964, atot15965]
  decide +kernel

theorem arows15970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15970 = true := by
  rw [show D2M8K2.u15970 = KTree.node D2M8K2.u15968 (nat_lit 34623347) (nat_lit 2315155848) (nat_lit 0) D2M8K2.u15969 from rfl, allE_node, arows15968, irow15970, arows15969]
  all_goals rfl

theorem atot15970 : totK PD2M8K2 D2M8K2.u15970 = [0, 0, 0, 945142164538, 1957394491555, 603107445866, 18746186300, 0] := by
  rw [show D2M8K2.u15970 = KTree.node D2M8K2.u15968 (nat_lit 34623347) (nat_lit 2315155848) (nat_lit 0) D2M8K2.u15969 from rfl, totK_node, atot15968, atot15969]
  decide +kernel

theorem arows15973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15973 = true := by
  rw [show D2M8K2.u15973 = KTree.node D2M8K2.u15971 (nat_lit 34633880) (nat_lit 3613870797) (nat_lit 0) D2M8K2.u15972 from rfl, allE_node, arows15971, irow15973, arows15972]
  all_goals rfl

theorem atot15973 : totK PD2M8K2 D2M8K2.u15973 = [0, 0, 439879725741, 1479014943577, 1369634858790, 386561295418, 20918021424, 0] := by
  rw [show D2M8K2.u15973 = KTree.node D2M8K2.u15971 (nat_lit 34633880) (nat_lit 3613870797) (nat_lit 0) D2M8K2.u15972 from rfl, totK_node, atot15971, atot15972]
  decide +kernel

theorem arows15978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15978 = true := by
  rw [show D2M8K2.u15978 = KTree.node D2M8K2.u15976 (nat_lit 34637698) (nat_lit 3967171411) (nat_lit 0) D2M8K2.u15977 from rfl, allE_node, arows15976, irow15978, arows15977]
  all_goals rfl

theorem atot15978 : totK PD2M8K2 D2M8K2.u15978 = [0, 0, 700808866955, 1765024185807, 1062627875627, 166786878807, 4239164426, 0] := by
  rw [show D2M8K2.u15978 = KTree.node D2M8K2.u15976 (nat_lit 34637698) (nat_lit 3967171411) (nat_lit 0) D2M8K2.u15977 from rfl, totK_node, atot15976, atot15977]
  decide +kernel

theorem arows15981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15981 = true := by
  rw [show D2M8K2.u15981 = KTree.node D2M8K2.u15979 (nat_lit 34643273) (nat_lit 1801706132) (nat_lit 0) D2M8K2.u15980 from rfl, allE_node, arows15979, irow15981, arows15980]
  all_goals rfl

theorem atot15981 : totK PD2M8K2 D2M8K2.u15981 = [0, 0, 532180463340, 1626776614238, 1289678571608, 215486792143, 4254338973, 0] := by
  rw [show D2M8K2.u15981 = KTree.node D2M8K2.u15979 (nat_lit 34643273) (nat_lit 1801706132) (nat_lit 0) D2M8K2.u15980 from rfl, totK_node, atot15979, atot15980]
  decide +kernel

theorem arows15985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15985 = true := by
  rw [show D2M8K2.u15985 = KTree.node D2M8K2.u15983 (nat_lit 34648211) (nat_lit 2792904163) (nat_lit 0) D2M8K2.u15984 from rfl, allE_node, arows15983, irow15985, arows15984]
  all_goals rfl

theorem atot15985 : totK PD2M8K2 D2M8K2.u15985 = [0, 0, 431262796055, 1532708259179, 1391859551099, 295252624675, 12632203081, 0] := by
  rw [show D2M8K2.u15985 = KTree.node D2M8K2.u15983 (nat_lit 34648211) (nat_lit 2792904163) (nat_lit 0) D2M8K2.u15984 from rfl, totK_node, atot15983, atot15984]
  decide +kernel

theorem arows15988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15988 = true := by
  rw [show D2M8K2.u15988 = KTree.node D2M8K2.u15986 (nat_lit 34713949) (nat_lit 1369150432) (nat_lit 0) D2M8K2.u15987 from rfl, allE_node, arows15986, irow15988, arows15987]
  all_goals rfl

theorem atot15988 : totK PD2M8K2 D2M8K2.u15988 = [0, 0, 491333866748, 1613264125610, 1312255427574, 164812838318, 1369150432, 0] := by
  rw [show D2M8K2.u15988 = KTree.node D2M8K2.u15986 (nat_lit 34713949) (nat_lit 1369150432) (nat_lit 0) D2M8K2.u15987 from rfl, totK_node, atot15986, atot15987]
  decide +kernel

theorem arows15996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15996 = true := by
  rw [show D2M8K2.u15996 = KTree.node D2M8K2.u15994 (nat_lit 34718141) (nat_lit 1783937229) (nat_lit 0) D2M8K2.u15995 from rfl, allE_node, arows15994, irow15996, arows15995]
  all_goals rfl

theorem atot15996 : totK PD2M8K2 D2M8K2.u15996 = [0, 0, 401273863176, 1478905794547, 1405986377979, 356604749950, 16293883145, 0] := by
  rw [show D2M8K2.u15996 = KTree.node D2M8K2.u15994 (nat_lit 34718141) (nat_lit 1783937229) (nat_lit 0) D2M8K2.u15995 from rfl, totK_node, atot15994, atot15995]
  decide +kernel

theorem arows15999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15999 = true := by
  rw [show D2M8K2.u15999 = KTree.node D2M8K2.u15997 (nat_lit 34724523) (nat_lit 3703598000) (nat_lit 0) D2M8K2.u15998 from rfl, allE_node, arows15997, irow15999, arows15998]
  all_goals rfl

theorem atot15999 : totK PD2M8K2 D2M8K2.u15999 = [0, 0, 427635945914, 1444734318743, 1383405977624, 329134325196, 13250685261, 0] := by
  rw [show D2M8K2.u15999 = KTree.node D2M8K2.u15997 (nat_lit 34724523) (nat_lit 3703598000) (nat_lit 0) D2M8K2.u15998 from rfl, totK_node, atot15997, atot15998]
  decide +kernel

theorem arows16003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16003 = true := by
  rw [show D2M8K2.u16003 = KTree.node D2M8K2.u16001 (nat_lit 34728208) (nat_lit 2475382443) (nat_lit 0) D2M8K2.u16002 from rfl, allE_node, arows16001, irow16003, arows16002]
  all_goals rfl

theorem atot16003 : totK PD2M8K2 D2M8K2.u16003 = [0, 0, 471647187930, 1563915885092, 1313834900175, 208761132743, 4980514959, 0] := by
  rw [show D2M8K2.u16003 = KTree.node D2M8K2.u16001 (nat_lit 34728208) (nat_lit 2475382443) (nat_lit 0) D2M8K2.u16002 from rfl, totK_node, atot16001, atot16002]
  decide +kernel

theorem arows16006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16006 = true := by
  rw [show D2M8K2.u16006 = KTree.node D2M8K2.u16004 (nat_lit 34731779) (nat_lit 2964435455) (nat_lit 0) D2M8K2.u16005 from rfl, allE_node, arows16004, irow16006, arows16005]
  all_goals rfl

theorem atot16006 : totK PD2M8K2 D2M8K2.u16006 = [0, 0, 182137505762, 1133529096977, 1712937486918, 497198896140, 19617843124, 0] := by
  rw [show D2M8K2.u16006 = KTree.node D2M8K2.u16004 (nat_lit 34731779) (nat_lit 2964435455) (nat_lit 0) D2M8K2.u16005 from rfl, totK_node, atot16004, atot16005]
  decide +kernel

theorem arows16011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16011 = true := by
  rw [show D2M8K2.u16011 = KTree.node D2M8K2.u16009 (nat_lit 34735688) (nat_lit 3697004479) (nat_lit 0) D2M8K2.u16010 from rfl, allE_node, arows16009, irow16011, arows16010]
  all_goals rfl

theorem atot16011 : totK PD2M8K2 D2M8K2.u16011 = [0, 0, 0, 621063701002, 1761821173077, 1050242980161, 101520798793, 1217496766] := by
  rw [show D2M8K2.u16011 = KTree.node D2M8K2.u16009 (nat_lit 34735688) (nat_lit 3697004479) (nat_lit 0) D2M8K2.u16010 from rfl, totK_node, atot16009, atot16010]
  decide +kernel

theorem arows16014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16014 = true := by
  rw [show D2M8K2.u16014 = KTree.node D2M8K2.u16012 (nat_lit 34744647) (nat_lit 3607090878) (nat_lit 0) D2M8K2.u16013 from rfl, allE_node, arows16012, irow16014, arows16013]
  all_goals rfl

theorem atot16014 : totK PD2M8K2 D2M8K2.u16014 = [0, 0, 0, 477705817183, 1596138819908, 1258522577973, 208915821433, 5425831197] := by
  rw [show D2M8K2.u16014 = KTree.node D2M8K2.u16012 (nat_lit 34744647) (nat_lit 3607090878) (nat_lit 0) D2M8K2.u16013 from rfl, totK_node, atot16012, atot16013]
  decide +kernel

theorem arows16018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16018 = true := by
  rw [show D2M8K2.u16018 = KTree.node D2M8K2.u16016 (nat_lit 34750421) (nat_lit 1556223037) (nat_lit 0) D2M8K2.u16017 from rfl, allE_node, arows16016, irow16018, arows16017]
  all_goals rfl

theorem atot16018 : totK PD2M8K2 D2M8K2.u16018 = [0, 0, 99421869408, 990074444200, 1773680386078, 648973904454, 35054905332, 0] := by
  rw [show D2M8K2.u16018 = KTree.node D2M8K2.u16016 (nat_lit 34750421) (nat_lit 1556223037) (nat_lit 0) D2M8K2.u16017 from rfl, totK_node, atot16016, atot16017]
  decide +kernel

theorem arows16021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16021 = true := by
  rw [show D2M8K2.u16021 = KTree.node D2M8K2.u16019 (nat_lit 34755845) (nat_lit 2342956359) (nat_lit 0) D2M8K2.u16020 from rfl, allE_node, arows16019, irow16021, arows16020]
  all_goals rfl

theorem atot16021 : totK PD2M8K2 D2M8K2.u16021 = [0, 0, 546625103161, 1708397467505, 1205793252555, 122985712892, 1310517177, 0] := by
  rw [show D2M8K2.u16021 = KTree.node D2M8K2.u16019 (nat_lit 34755845) (nat_lit 2342956359) (nat_lit 0) D2M8K2.u16020 from rfl, totK_node, atot16019, atot16020]
  decide +kernel

theorem arows16027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16027 = true := by
  rw [show D2M8K2.u16027 = KTree.node D2M8K2.u16025 (nat_lit 34765036) (nat_lit 2413727503) (nat_lit 0) D2M8K2.u16026 from rfl, allE_node, arows16025, irow16027, arows16026]
  all_goals rfl

theorem atot16027 : totK PD2M8K2 D2M8K2.u16027 = [0, 0, 809601596306, 1921589802444, 863216509856, 48703863742, 0, 0] := by
  rw [show D2M8K2.u16027 = KTree.node D2M8K2.u16025 (nat_lit 34765036) (nat_lit 2413727503) (nat_lit 0) D2M8K2.u16026 from rfl, totK_node, atot16025, atot16026]
  decide +kernel

theorem arows16030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16030 = true := by
  rw [show D2M8K2.u16030 = KTree.node D2M8K2.u16028 (nat_lit 34769985) (nat_lit 1825578435) (nat_lit 0) D2M8K2.u16029 from rfl, allE_node, arows16028, irow16030, arows16029]
  all_goals rfl

theorem atot16030 : totK PD2M8K2 D2M8K2.u16030 = [0, 0, 452391359153, 1602666938170, 1299523532458, 195417371589, 4980514959, 0] := by
  rw [show D2M8K2.u16030 = KTree.node D2M8K2.u16028 (nat_lit 34769985) (nat_lit 1825578435) (nat_lit 0) D2M8K2.u16029 from rfl, totK_node, atot16028, atot16029]
  decide +kernel

theorem arows16034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16034 = true := by
  rw [show D2M8K2.u16034 = KTree.node D2M8K2.u16032 (nat_lit 34798224) (nat_lit 3538277001) (nat_lit 0) D2M8K2.u16033 from rfl, allE_node, arows16032, irow16034, arows16033]
  all_goals rfl

theorem atot16034 : totK PD2M8K2 D2M8K2.u16034 = [0, 0, 512808298635, 1642480758634, 1314716489578, 165323426533, 1369150432, 0] := by
  rw [show D2M8K2.u16034 = KTree.node D2M8K2.u16032 (nat_lit 34798224) (nat_lit 3538277001) (nat_lit 0) D2M8K2.u16033 from rfl, totK_node, atot16032, atot16033]
  decide +kernel

theorem arows16037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16037 = true := by
  rw [show D2M8K2.u16037 = KTree.node D2M8K2.u16035 (nat_lit 34801849) (nat_lit 1233424256) (nat_lit 0) D2M8K2.u16036 from rfl, allE_node, arows16035, irow16037, arows16036]
  all_goals rfl

theorem atot16037 : totK PD2M8K2 D2M8K2.u16037 = [0, 0, 381071417480, 1470886005166, 1447202183302, 369680656743, 16293883145, 0] := by
  rw [show D2M8K2.u16037 = KTree.node D2M8K2.u16035 (nat_lit 34801849) (nat_lit 1233424256) (nat_lit 0) D2M8K2.u16036 from rfl, totK_node, atot16035, atot16036]
  decide +kernel

theorem arows16042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16042 = true := by
  rw [show D2M8K2.u16042 = KTree.node D2M8K2.u16040 (nat_lit 34805842) (nat_lit 3970467854) (nat_lit 0) D2M8K2.u16041 from rfl, allE_node, arows16040, irow16042, arows16041]
  all_goals rfl

theorem atot16042 : totK PD2M8K2 D2M8K2.u16042 = [0, 0, 422688696237, 1485600977753, 1411499701593, 264816291277, 6370881270, 0] := by
  rw [show D2M8K2.u16042 = KTree.node D2M8K2.u16040 (nat_lit 34805842) (nat_lit 3970467854) (nat_lit 0) D2M8K2.u16041 from rfl, totK_node, atot16040, atot16041]
  decide +kernel

theorem arows16045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16045 = true := by
  rw [show D2M8K2.u16045 = KTree.node D2M8K2.u16043 (nat_lit 34812674) (nat_lit 4084330547) (nat_lit 0) D2M8K2.u16044 from rfl, allE_node, arows16043, irow16045, arows16044]
  all_goals rfl

theorem atot16045 : totK PD2M8K2 D2M8K2.u16045 = [0, 0, 441885296877, 1529650109726, 1393284664267, 266675359874, 7698146732, 0] := by
  rw [show D2M8K2.u16045 = KTree.node D2M8K2.u16043 (nat_lit 34812674) (nat_lit 4084330547) (nat_lit 0) D2M8K2.u16044 from rfl, totK_node, atot16043, atot16044]
  decide +kernel

theorem arows16049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16049 = true := by
  rw [show D2M8K2.u16049 = KTree.node D2M8K2.u16047 (nat_lit 35334201) (nat_lit 1822536073) (nat_lit 0) D2M8K2.u16048 from rfl, allE_node, arows16047, irow16049, arows16048]
  all_goals rfl

theorem atot16049 : totK PD2M8K2 D2M8K2.u16049 = [0, 423734741471, 992452930421, 804637085300, 947428153316, 387366760675, 21982715828, 0] := by
  rw [show D2M8K2.u16049 = KTree.node D2M8K2.u16047 (nat_lit 35334201) (nat_lit 1822536073) (nat_lit 0) D2M8K2.u16048 from rfl, totK_node, atot16047, atot16048]
  decide +kernel

theorem arows16052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16052 = true := by
  rw [show D2M8K2.u16052 = KTree.node D2M8K2.u16050 (nat_lit 35341194) (nat_lit 3488772352) (nat_lit 0) D2M8K2.u16051 from rfl, allE_node, arows16050, irow16052, arows16051]
  all_goals rfl

theorem atot16052 : totK PD2M8K2 D2M8K2.u16052 = [0, 423361586569, 1591813761537, 1407297963051, 192492260361, 1369150432, 0, 0] := by
  rw [show D2M8K2.u16052 = KTree.node D2M8K2.u16050 (nat_lit 35341194) (nat_lit 3488772352) (nat_lit 0) D2M8K2.u16051 from rfl, totK_node, atot16050, atot16051]
  decide +kernel

theorem arows16059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16059 = true := by
  rw [show D2M8K2.u16059 = KTree.node D2M8K2.u16057 (nat_lit 35344636) (nat_lit 3534814932) (nat_lit 0) D2M8K2.u16058 from rfl, allE_node, arows16057, irow16059, arows16058]
  all_goals rfl

theorem atot16059 : totK PD2M8K2 D2M8K2.u16059 = [0, 411611454674, 1446238187055, 1413688503504, 304350438569, 8815471973, 0, 0] := by
  rw [show D2M8K2.u16059 = KTree.node D2M8K2.u16057 (nat_lit 35344636) (nat_lit 3534814932) (nat_lit 0) D2M8K2.u16058 from rfl, totK_node, atot16057, atot16058]
  decide +kernel

theorem arows16062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16062 = true := by
  rw [show D2M8K2.u16062 = KTree.node D2M8K2.u16060 (nat_lit 35348065) (nat_lit 1509172513) (nat_lit 0) D2M8K2.u16061 from rfl, allE_node, arows16060, irow16062, arows16061]
  all_goals rfl

theorem atot16062 : totK PD2M8K2 D2M8K2.u16062 = [0, 320634672064, 1362119717832, 1503654903397, 351544974233, 10013174153, 0, 0] := by
  rw [show D2M8K2.u16062 = KTree.node D2M8K2.u16060 (nat_lit 35348065) (nat_lit 1509172513) (nat_lit 0) D2M8K2.u16061 from rfl, totK_node, atot16060, atot16061]
  decide +kernel

theorem arows16066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16066 = true := by
  rw [show D2M8K2.u16066 = KTree.node D2M8K2.u16064 (nat_lit 35352296) (nat_lit 3273815301) (nat_lit 0) D2M8K2.u16065 from rfl, allE_node, arows16064, irow16066, arows16065]
  all_goals rfl

theorem atot16066 : totK PD2M8K2 D2M8K2.u16066 = [0, 428339404384, 1542963628859, 1415795841245, 237307745356, 2304167554, 0, 0] := by
  rw [show D2M8K2.u16066 = KTree.node D2M8K2.u16064 (nat_lit 35352296) (nat_lit 3273815301) (nat_lit 0) D2M8K2.u16065 from rfl, totK_node, atot16064, atot16065]
  decide +kernel

theorem arows16069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16069 = true := by
  rw [show D2M8K2.u16069 = KTree.node D2M8K2.u16067 (nat_lit 35355731) (nat_lit 2905711124) (nat_lit 0) D2M8K2.u16068 from rfl, allE_node, arows16067, irow16069, arows16068]
  all_goals rfl

theorem atot16069 : totK PD2M8K2 D2M8K2.u16069 = [0, 0, 612815078170, 1744831908176, 1031689509328, 124944282617, 1369150432, 0] := by
  rw [show D2M8K2.u16069 = KTree.node D2M8K2.u16067 (nat_lit 35355731) (nat_lit 2905711124) (nat_lit 0) D2M8K2.u16068 from rfl, totK_node, atot16067, atot16068]
  decide +kernel

theorem arows16074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16074 = true := by
  rw [show D2M8K2.u16074 = KTree.node D2M8K2.u16072 (nat_lit 35362609) (nat_lit 1402517022) (nat_lit 0) D2M8K2.u16073 from rfl, allE_node, arows16072, irow16074, arows16073]
  all_goals rfl

theorem atot16074 : totK PD2M8K2 D2M8K2.u16074 = [0, 0, 647156153415, 1831544877281, 1018116818517, 64576123940, 0, 0] := by
  rw [show D2M8K2.u16074 = KTree.node D2M8K2.u16072 (nat_lit 35362609) (nat_lit 1402517022) (nat_lit 0) D2M8K2.u16073 from rfl, totK_node, atot16072, atot16073]
  decide +kernel

theorem arows16077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16077 = true := by
  rw [show D2M8K2.u16077 = KTree.node D2M8K2.u16075 (nat_lit 35369546) (nat_lit 3142170643) (nat_lit 0) D2M8K2.u16076 from rfl, allE_node, arows16075, irow16077, arows16076]
  all_goals rfl

theorem atot16077 : totK PD2M8K2 D2M8K2.u16077 = [0, 0, 738941846964, 1909322124152, 858364769474, 36885279528, 0, 0] := by
  rw [show D2M8K2.u16077 = KTree.node D2M8K2.u16075 (nat_lit 35369546) (nat_lit 3142170643) (nat_lit 0) D2M8K2.u16076 from rfl, totK_node, atot16075, atot16076]
  decide +kernel

theorem arows16081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16081 = true := by
  rw [show D2M8K2.u16081 = KTree.node D2M8K2.u16079 (nat_lit 35379821) (nat_lit 2069618004) (nat_lit 0) D2M8K2.u16080 from rfl, allE_node, arows16079, irow16081, arows16080]
  all_goals rfl

theorem atot16081 : totK PD2M8K2 D2M8K2.u16081 = [0, 444330752118, 1415190773316, 1351017890308, 434497192858, 33374361218, 0, 0] := by
  rw [show D2M8K2.u16081 = KTree.node D2M8K2.u16079 (nat_lit 35379821) (nat_lit 2069618004) (nat_lit 0) D2M8K2.u16080 from rfl, totK_node, atot16079, atot16080]
  decide +kernel

theorem arows16084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16084 = true := by
  rw [show D2M8K2.u16084 = KTree.node D2M8K2.u16082 (nat_lit 35382576) (nat_lit 3596949163) (nat_lit 0) D2M8K2.u16083 from rfl, allE_node, arows16082, irow16084, arows16083]
  all_goals rfl

theorem atot16084 : totK PD2M8K2 D2M8K2.u16084 = [0, 414666365944, 1315989085588, 1383516299485, 500588318076, 24472827335, 0, 0] := by
  rw [show D2M8K2.u16084 = KTree.node D2M8K2.u16082 (nat_lit 35382576) (nat_lit 3596949163) (nat_lit 0) D2M8K2.u16083 from rfl, totK_node, atot16082, atot16083]
  decide +kernel

theorem arows16090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16090 = true := by
  rw [show D2M8K2.u16090 = KTree.node D2M8K2.u16088 (nat_lit 35385839) (nat_lit 2777452777) (nat_lit 0) D2M8K2.u16089 from rfl, allE_node, arows16088, irow16090, arows16089]
  all_goals rfl

theorem atot16090 : totK PD2M8K2 D2M8K2.u16090 = [0, 395540202782, 1448382436360, 1442788500617, 322947790775, 11623571359, 0, 0] := by
  rw [show D2M8K2.u16090 = KTree.node D2M8K2.u16088 (nat_lit 35385839) (nat_lit 2777452777) (nat_lit 0) D2M8K2.u16089 from rfl, totK_node, atot16088, atot16089]
  decide +kernel

theorem arows16093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16093 = true := by
  rw [show D2M8K2.u16093 = KTree.node D2M8K2.u16091 (nat_lit 35389243) (nat_lit 2231011960) (nat_lit 0) D2M8K2.u16092 from rfl, allE_node, arows16091, irow16093, arows16092]
  all_goals rfl

theorem atot16093 : totK PD2M8K2 D2M8K2.u16093 = [0, 346925655167, 1420051714749, 1514596162953, 350170708722, 11777714805, 0, 0] := by
  rw [show D2M8K2.u16093 = KTree.node D2M8K2.u16091 (nat_lit 35389243) (nat_lit 2231011960) (nat_lit 0) D2M8K2.u16092 from rfl, totK_node, atot16091, atot16092]
  decide +kernel

theorem arows16097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16097 = true := by
  rw [show D2M8K2.u16097 = KTree.node D2M8K2.u16095 (nat_lit 35393518) (nat_lit 3948075685) (nat_lit 0) D2M8K2.u16096 from rfl, allE_node, arows16095, irow16097, arows16096]
  all_goals rfl

theorem atot16097 : totK PD2M8K2 D2M8K2.u16097 = [0, 429727646880, 1554983002558, 1445835950323, 243754285816, 2760920482, 0, 0] := by
  rw [show D2M8K2.u16097 = KTree.node D2M8K2.u16095 (nat_lit 35393518) (nat_lit 3948075685) (nat_lit 0) D2M8K2.u16096 from rfl, totK_node, atot16095, atot16096]
  decide +kernel

theorem arows16100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16100 = true := by
  rw [show D2M8K2.u16100 = KTree.node D2M8K2.u16098 (nat_lit 35400382) (nat_lit 3897375164) (nat_lit 0) D2M8K2.u16099 from rfl, allE_node, arows16098, irow16100, arows16099]
  all_goals rfl

theorem atot16100 : totK PD2M8K2 D2M8K2.u16100 = [0, 0, 708934714264, 1850676278227, 1002754407368, 81492833556, 0, 0] := by
  rw [show D2M8K2.u16100 = KTree.node D2M8K2.u16098 (nat_lit 35400382) (nat_lit 3897375164) (nat_lit 0) D2M8K2.u16099 from rfl, totK_node, atot16098, atot16099]
  decide +kernel

theorem arows16105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16105 = true := by
  rw [show D2M8K2.u16105 = KTree.node D2M8K2.u16103 (nat_lit 35403149) (nat_lit 2046037017) (nat_lit 0) D2M8K2.u16104 from rfl, allE_node, arows16103, irow16105, arows16104]
  all_goals rfl

theorem atot16105 : totK PD2M8K2 D2M8K2.u16105 = [0, 0, 342160275933, 1241986586641, 1456174223995, 520775524717, 30892441579, 0] := by
  rw [show D2M8K2.u16105 = KTree.node D2M8K2.u16103 (nat_lit 35403149) (nat_lit 2046037017) (nat_lit 0) D2M8K2.u16104 from rfl, totK_node, atot16103, atot16104]
  decide +kernel

theorem arows16108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16108 = true := by
  rw [show D2M8K2.u16108 = KTree.node D2M8K2.u16106 (nat_lit 35406742) (nat_lit 3421996718) (nat_lit 0) D2M8K2.u16107 from rfl, allE_node, arows16106, irow16108, arows16107]
  all_goals rfl

theorem atot16108 : totK PD2M8K2 D2M8K2.u16108 = [0, 0, 485278506110, 1584042587539, 1345542872277, 213760087135, 2665309491, 0] := by
  rw [show D2M8K2.u16108 = KTree.node D2M8K2.u16106 (nat_lit 35406742) (nat_lit 3421996718) (nat_lit 0) D2M8K2.u16107 from rfl, totK_node, atot16106, atot16107]
  decide +kernel

theorem arows16112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16112 = true := by
  rw [show D2M8K2.u16112 = KTree.node D2M8K2.u16110 (nat_lit 35410636) (nat_lit 3836522516) (nat_lit 0) D2M8K2.u16111 from rfl, allE_node, arows16110, irow16112, arows16111]
  all_goals rfl

theorem atot16112 : totK PD2M8K2 D2M8K2.u16112 = [0, 0, 326332545645, 1495250323686, 1556867625080, 259086671096, 2681443193, 0] := by
  rw [show D2M8K2.u16112 = KTree.node D2M8K2.u16110 (nat_lit 35410636) (nat_lit 3836522516) (nat_lit 0) D2M8K2.u16111 from rfl, totK_node, atot16110, atot16111]
  decide +kernel

theorem arows16115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16115 = true := by
  rw [show D2M8K2.u16115 = KTree.node D2M8K2.u16113 (nat_lit 35414589) (nat_lit 1494789685) (nat_lit 0) D2M8K2.u16114 from rfl, allE_node, arows16113, irow16115, arows16114]
  all_goals rfl

theorem atot16115 : totK PD2M8K2 D2M8K2.u16115 = [0, 0, 427907794299, 1587765184357, 1418557527315, 205569325067, 1238673482, 0] := by
  rw [show D2M8K2.u16115 = KTree.node D2M8K2.u16113 (nat_lit 35414589) (nat_lit 1494789685) (nat_lit 0) D2M8K2.u16114 from rfl, totK_node, atot16113, atot16114]
  decide +kernel

theorem arows16124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16124 = true := by
  rw [show D2M8K2.u16124 = KTree.node D2M8K2.u16122 (nat_lit 35418304) (nat_lit 3722224459) (nat_lit 0) D2M8K2.u16123 from rfl, allE_node, arows16122, irow16124, arows16123]
  all_goals rfl

theorem atot16124 : totK PD2M8K2 D2M8K2.u16124 = [0, 407181422912, 1386757394993, 1212778804922, 405607048520, 134395867309, 8063697217, 0] := by
  rw [show D2M8K2.u16124 = KTree.node D2M8K2.u16122 (nat_lit 35418304) (nat_lit 3722224459) (nat_lit 0) D2M8K2.u16123 from rfl, totK_node, atot16122, atot16123]
  decide +kernel

theorem arows16127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16127 = true := by
  rw [show D2M8K2.u16127 = KTree.node D2M8K2.u16125 (nat_lit 35421948) (nat_lit 2120589423) (nat_lit 0) D2M8K2.u16126 from rfl, allE_node, arows16125, irow16127, arows16126]
  all_goals rfl

theorem atot16127 : totK PD2M8K2 D2M8K2.u16127 = [0, 418604162135, 1412373341668, 1383736948464, 429269776772, 27744257752, 0, 0] := by
  rw [show D2M8K2.u16127 = KTree.node D2M8K2.u16125 (nat_lit 35421948) (nat_lit 2120589423) (nat_lit 0) D2M8K2.u16126 from rfl, totK_node, atot16125, atot16126]
  decide +kernel

theorem arows16131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16131 = true := by
  rw [show D2M8K2.u16131 = KTree.node D2M8K2.u16129 (nat_lit 35424701) (nat_lit 2326292714) (nat_lit 0) D2M8K2.u16130 from rfl, allE_node, arows16129, irow16131, arows16130]
  all_goals rfl

theorem atot16131 : totK PD2M8K2 D2M8K2.u16131 = [0, 439844950168, 1473049547169, 1387784380770, 326933960038, 9374251252, 0, 0] := by
  rw [show D2M8K2.u16131 = KTree.node D2M8K2.u16129 (nat_lit 35424701) (nat_lit 2326292714) (nat_lit 0) D2M8K2.u16130 from rfl, totK_node, atot16129, atot16130]
  decide +kernel

theorem arows16134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16134 = true := by
  rw [show D2M8K2.u16134 = KTree.node D2M8K2.u16132 (nat_lit 35431495) (nat_lit 1898701291) (nat_lit 0) D2M8K2.u16133 from rfl, allE_node, arows16132, irow16134, arows16133]
  all_goals rfl

theorem atot16134 : totK PD2M8K2 D2M8K2.u16134 = [0, 342434448945, 1398514667530, 1510162580981, 328666793588, 12981912718, 0, 0] := by
  rw [show D2M8K2.u16134 = KTree.node D2M8K2.u16132 (nat_lit 35431495) (nat_lit 1898701291) (nat_lit 0) D2M8K2.u16133 from rfl, totK_node, atot16132, atot16133]
  decide +kernel

theorem arows16139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16139 = true := by
  rw [show D2M8K2.u16139 = KTree.node D2M8K2.u16137 (nat_lit 35435893) (nat_lit 1225325920) (nat_lit 0) D2M8K2.u16138 from rfl, allE_node, arows16137, irow16139, arows16138]
  all_goals rfl

theorem atot16139 : totK PD2M8K2 D2M8K2.u16139 = [0, 406574288871, 1458583677701, 1423734183535, 329822891045, 8708200738, 0, 0] := by
  rw [show D2M8K2.u16139 = KTree.node D2M8K2.u16137 (nat_lit 35435893) (nat_lit 1225325920) (nat_lit 0) D2M8K2.u16138 from rfl, totK_node, atot16137, atot16138]
  decide +kernel

theorem arows16142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16142 = true := by
  rw [show D2M8K2.u16142 = KTree.node D2M8K2.u16140 (nat_lit 35439198) (nat_lit 3733983378) (nat_lit 0) D2M8K2.u16141 from rfl, allE_node, arows16140, irow16142, arows16141]
  all_goals rfl

theorem atot16142 : totK PD2M8K2 D2M8K2.u16142 = [0, 0, 517738947991, 1696720323144, 1175894626456, 119061346046, 1206465782, 0] := by
  rw [show D2M8K2.u16142 = KTree.node D2M8K2.u16140 (nat_lit 35439198) (nat_lit 3733983378) (nat_lit 0) D2M8K2.u16141 from rfl, totK_node, atot16140, atot16141]
  decide +kernel

theorem arows16146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16146 = true := by
  rw [show D2M8K2.u16146 = KTree.node D2M8K2.u16144 (nat_lit 35442947) (nat_lit 2870585650) (nat_lit 0) D2M8K2.u16145 from rfl, allE_node, arows16144, irow16146, arows16145]
  all_goals rfl

theorem atot16146 : totK PD2M8K2 D2M8K2.u16146 = [0, 0, 710771201168, 1866069141064, 985359762044, 72677044528, 0, 0] := by
  rw [show D2M8K2.u16146 = KTree.node D2M8K2.u16144 (nat_lit 35442947) (nat_lit 2870585650) (nat_lit 0) D2M8K2.u16145 from rfl, totK_node, atot16144, atot16145]
  decide +kernel

theorem arows16149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16149 = true := by
  rw [show D2M8K2.u16149 = KTree.node D2M8K2.u16147 (nat_lit 35447924) (nat_lit 2305210978) (nat_lit 0) D2M8K2.u16148 from rfl, allE_node, arows16147, irow16149, arows16148]
  all_goals rfl

theorem atot16149 : totK PD2M8K2 D2M8K2.u16149 = [0, 0, 394043115790, 1486285108888, 1372096103561, 272113843451, 8802081085, 0] := by
  rw [show D2M8K2.u16149 = KTree.node D2M8K2.u16147 (nat_lit 35447924) (nat_lit 2305210978) (nat_lit 0) D2M8K2.u16148 from rfl, totK_node, atot16147, atot16148]
  decide +kernel

theorem arows16155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16155 = true := by
  rw [show D2M8K2.u16155 = KTree.node D2M8K2.u16153 (nat_lit 35455737) (nat_lit 1779637458) (nat_lit 0) D2M8K2.u16154 from rfl, allE_node, arows16153, irow16155, arows16154]
  all_goals rfl

theorem atot16155 : totK PD2M8K2 D2M8K2.u16155 = [0, 156589052074, 792729480962, 1510957920795, 1004218586144, 107168984963, 1021600638, 0] := by
  rw [show D2M8K2.u16155 = KTree.node D2M8K2.u16153 (nat_lit 35455737) (nat_lit 1779637458) (nat_lit 0) D2M8K2.u16154 from rfl, totK_node, atot16153, atot16154]
  decide +kernel

theorem arows16158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16158 = true := by
  rw [show D2M8K2.u16158 = KTree.node D2M8K2.u16156 (nat_lit 35460921) (nat_lit 1726096149) (nat_lit 0) D2M8K2.u16157 from rfl, allE_node, arows16156, irow16158, arows16157]
  all_goals rfl

theorem atot16158 : totK PD2M8K2 D2M8K2.u16158 = [0, 480127109971, 1587309825665, 1362682422425, 189786493970, 1369150432, 0, 0] := by
  rw [show D2M8K2.u16158 = KTree.node D2M8K2.u16156 (nat_lit 35460921) (nat_lit 1726096149) (nat_lit 0) D2M8K2.u16157 from rfl, totK_node, atot16156, atot16157]
  decide +kernel

theorem arows16162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16162 = true := by
  rw [show D2M8K2.u16162 = KTree.node D2M8K2.u16160 (nat_lit 35464490) (nat_lit 4198031037) (nat_lit 0) D2M8K2.u16161 from rfl, allE_node, arows16160, irow16162, arows16161]
  all_goals rfl

theorem atot16162 : totK PD2M8K2 D2M8K2.u16162 = [0, 309657456744, 1240099507265, 1482690511722, 566890295121, 35992459077, 0, 0] := by
  rw [show D2M8K2.u16162 = KTree.node D2M8K2.u16160 (nat_lit 35464490) (nat_lit 4198031037) (nat_lit 0) D2M8K2.u16161 from rfl, totK_node, atot16160, atot16161]
  decide +kernel

theorem arows16165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16165 = true := by
  rw [show D2M8K2.u16165 = KTree.node D2M8K2.u16163 (nat_lit 35470731) (nat_lit 2974064662) (nat_lit 0) D2M8K2.u16164 from rfl, allE_node, arows16163, irow16165, arows16164]
  all_goals rfl

theorem atot16165 : totK PD2M8K2 D2M8K2.u16165 = [0, 399095265404, 1412234282410, 1446363113879, 347844887119, 13250685261, 0, 0] := by
  rw [show D2M8K2.u16165 = KTree.node D2M8K2.u16163 (nat_lit 35470731) (nat_lit 2974064662) (nat_lit 0) D2M8K2.u16164 from rfl, totK_node, atot16163, atot16164]
  decide +kernel

theorem arows16170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16170 = true := by
  rw [show D2M8K2.u16170 = KTree.node D2M8K2.u16168 (nat_lit 35474451) (nat_lit 3683534290) (nat_lit 0) D2M8K2.u16169 from rfl, allE_node, arows16168, irow16170, arows16169]
  all_goals rfl

theorem atot16170 : totK PD2M8K2 D2M8K2.u16170 = [0, 491020305335, 1657123718001, 1318293569854, 165754792812, 1096505104, 0, 0] := by
  rw [show D2M8K2.u16170 = KTree.node D2M8K2.u16168 (nat_lit 35474451) (nat_lit 3683534290) (nat_lit 0) D2M8K2.u16169 from rfl, totK_node, atot16168, atot16169]
  decide +kernel

theorem arows16173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16173 = true := by
  rw [show D2M8K2.u16173 = KTree.node D2M8K2.u16171 (nat_lit 35478304) (nat_lit 2921734316) (nat_lit 0) D2M8K2.u16172 from rfl, allE_node, arows16171, irow16173, arows16172]
  all_goals rfl

theorem atot16173 : totK PD2M8K2 D2M8K2.u16173 = [0, 182261201038, 1110304071949, 1712824702398, 569929530840, 24561152333, 0, 0] := by
  rw [show D2M8K2.u16173 = KTree.node D2M8K2.u16171 (nat_lit 35478304) (nat_lit 2921734316) (nat_lit 0) D2M8K2.u16172 from rfl, totK_node, atot16171, atot16172]
  decide +kernel

theorem arows16177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16177 = true := by
  rw [show D2M8K2.u16177 = KTree.node D2M8K2.u16175 (nat_lit 35481992) (nat_lit 3861468663) (nat_lit 0) D2M8K2.u16176 from rfl, allE_node, arows16175, irow16177, arows16176]
  all_goals rfl

theorem atot16177 : totK PD2M8K2 D2M8K2.u16177 = [0, 0, 485868818635, 1658709595691, 1290847838268, 138853250526, 1239866073, 0] := by
  rw [show D2M8K2.u16177 = KTree.node D2M8K2.u16175 (nat_lit 35481992) (nat_lit 3861468663) (nat_lit 0) D2M8K2.u16176 from rfl, totK_node, atot16175, atot16176]
  decide +kernel

theorem arows16180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16180 = true := by
  rw [show D2M8K2.u16180 = KTree.node D2M8K2.u16178 (nat_lit 35490642) (nat_lit 3480840810) (nat_lit 0) D2M8K2.u16179 from rfl, allE_node, arows16178, irow16180, arows16179]
  all_goals rfl

theorem atot16180 : totK PD2M8K2 D2M8K2.u16180 = [0, 0, 575767331717, 1724083663755, 1162649639180, 136408000547, 1171084559, 0] := by
  rw [show D2M8K2.u16180 = KTree.node D2M8K2.u16178 (nat_lit 35490642) (nat_lit 3480840810) (nat_lit 0) D2M8K2.u16179 from rfl, totK_node, atot16178, atot16179]
  decide +kernel

theorem arows16187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16187 = true := by
  rw [show D2M8K2.u16187 = KTree.node D2M8K2.u16185 (nat_lit 35494070) (nat_lit 3946446048) (nat_lit 0) D2M8K2.u16186 from rfl, allE_node, arows16185, irow16187, arows16186]
  all_goals rfl

theorem atot16187 : totK PD2M8K2 D2M8K2.u16187 = [0, 0, 407686379121, 1492068221047, 1362288264885, 250428099282, 8735979960, 0] := by
  rw [show D2M8K2.u16187 = KTree.node D2M8K2.u16185 (nat_lit 35494070) (nat_lit 3946446048) (nat_lit 0) D2M8K2.u16186 from rfl, totK_node, atot16185, atot16186]
  decide +kernel

theorem arows16190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16190 = true := by
  rw [show D2M8K2.u16190 = KTree.node D2M8K2.u16188 (nat_lit 35498283) (nat_lit 3491308454) (nat_lit 0) D2M8K2.u16189 from rfl, allE_node, arows16188, irow16190, arows16189]
  all_goals rfl

theorem atot16190 : totK PD2M8K2 D2M8K2.u16190 = [0, 393878508058, 1268073709786, 1343969420932, 564146666877, 44849745537, 0, 0] := by
  rw [show D2M8K2.u16190 = KTree.node D2M8K2.u16188 (nat_lit 35498283) (nat_lit 3491308454) (nat_lit 0) D2M8K2.u16189 from rfl, totK_node, atot16188, atot16189]
  decide +kernel

theorem arows16194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16194 = true := by
  rw [show D2M8K2.u16194 = KTree.node D2M8K2.u16192 (nat_lit 35545379) (nat_lit 2962688467) (nat_lit 0) D2M8K2.u16193 from rfl, allE_node, arows16192, irow16194, arows16193]
  all_goals rfl

theorem atot16194 : totK PD2M8K2 D2M8K2.u16194 = [0, 446590550280, 1616109806995, 1402476385492, 191868887774, 1369150432, 0, 0] := by
  rw [show D2M8K2.u16194 = KTree.node D2M8K2.u16192 (nat_lit 35545379) (nat_lit 2962688467) (nat_lit 0) D2M8K2.u16193 from rfl, totK_node, atot16192, atot16193]
  decide +kernel

theorem arows16197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16197 = true := by
  rw [show D2M8K2.u16197 = KTree.node D2M8K2.u16195 (nat_lit 35548158) (nat_lit 3879454023) (nat_lit 0) D2M8K2.u16196 from rfl, allE_node, arows16195, irow16197, arows16196]
  all_goals rfl

theorem atot16197 : totK PD2M8K2 D2M8K2.u16197 = [0, 299429600405, 1193561247753, 1519415259231, 587633299624, 35328214344, 0, 0] := by
  rw [show D2M8K2.u16197 = KTree.node D2M8K2.u16195 (nat_lit 35548158) (nat_lit 3879454023) (nat_lit 0) D2M8K2.u16196 from rfl, totK_node, atot16195, atot16196]
  decide +kernel

theorem arows16202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16202 = true := by
  rw [show D2M8K2.u16202 = KTree.node D2M8K2.u16200 (nat_lit 35551328) (nat_lit 3566918786) (nat_lit 0) D2M8K2.u16201 from rfl, allE_node, arows16200, irow16202, arows16201]
  all_goals rfl

theorem atot16202 : totK PD2M8K2 D2M8K2.u16202 = [0, 387736233321, 1439455669153, 1449163439451, 325505752212, 11203196507, 0, 0] := by
  rw [show D2M8K2.u16202 = KTree.node D2M8K2.u16200 (nat_lit 35551328) (nat_lit 3566918786) (nat_lit 0) D2M8K2.u16201 from rfl, totK_node, atot16200, atot16201]
  decide +kernel

theorem arows16205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16205 = true := by
  rw [show D2M8K2.u16205 = KTree.node D2M8K2.u16203 (nat_lit 35554708) (nat_lit 1739870893) (nat_lit 0) D2M8K2.u16204 from rfl, allE_node, arows16203, irow16205, arows16204]
  all_goals rfl

theorem atot16205 : totK PD2M8K2 D2M8K2.u16205 = [0, 422800425657, 1457188777211, 1415452369063, 327793099366, 11344622705, 0, 0] := by
  rw [show D2M8K2.u16205 = KTree.node D2M8K2.u16203 (nat_lit 35554708) (nat_lit 1739870893) (nat_lit 0) D2M8K2.u16204 from rfl, totK_node, atot16203, atot16204]
  decide +kernel

theorem arows16209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16209 = true := by
  rw [show D2M8K2.u16209 = KTree.node D2M8K2.u16207 (nat_lit 35561150) (nat_lit 3861145161) (nat_lit 0) D2M8K2.u16208 from rfl, allE_node, arows16207, irow16209, arows16208]
  all_goals rfl

theorem atot16209 : totK PD2M8K2 D2M8K2.u16209 = [0, 182497872290, 1145014959475, 1723251159282, 543904293900, 23418599596, 0, 0] := by
  rw [show D2M8K2.u16209 = KTree.node D2M8K2.u16207 (nat_lit 35561150) (nat_lit 3861145161) (nat_lit 0) D2M8K2.u16208 from rfl, totK_node, atot16207, atot16208]
  decide +kernel

theorem arows16212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16212 = true := by
  rw [show D2M8K2.u16212 = KTree.node D2M8K2.u16210 (nat_lit 35564588) (nat_lit 1818450765) (nat_lit 0) D2M8K2.u16211 from rfl, allE_node, arows16210, irow16212, arows16211]
  all_goals rfl

theorem atot16212 : totK PD2M8K2 D2M8K2.u16212 = [0, 0, 452338334350, 1602317638752, 1353821861979, 159156041085, 1310285577, 0] := by
  rw [show D2M8K2.u16212 = KTree.node D2M8K2.u16210 (nat_lit 35564588) (nat_lit 1818450765) (nat_lit 0) D2M8K2.u16211 from rfl, totK_node, atot16210, atot16211]
  decide +kernel

theorem arows16218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16218 = true := by
  rw [show D2M8K2.u16218 = KTree.node D2M8K2.u16216 (nat_lit 35569636) (nat_lit 4020326175) (nat_lit 0) D2M8K2.u16217 from rfl, allE_node, arows16216, irow16218, arows16217]
  all_goals rfl

theorem atot16218 : totK PD2M8K2 D2M8K2.u16218 = [0, 0, 632324198695, 1754564207065, 1105263629393, 116653995108, 1075657031, 0] := by
  rw [show D2M8K2.u16218 = KTree.node D2M8K2.u16216 (nat_lit 35569636) (nat_lit 4020326175) (nat_lit 0) D2M8K2.u16217 from rfl, totK_node, atot16216, atot16217]
  decide +kernel

theorem arows16221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16221 = true := by
  rw [show D2M8K2.u16221 = KTree.node D2M8K2.u16219 (nat_lit 35573476) (nat_lit 2602726617) (nat_lit 0) D2M8K2.u16220 from rfl, allE_node, arows16219, irow16221, arows16220]
  all_goals rfl

theorem atot16221 : totK PD2M8K2 D2M8K2.u16221 = [0, 0, 420214939264, 1562502211715, 1369709944681, 216928160333, 4911340522, 0] := by
  rw [show D2M8K2.u16221 = KTree.node D2M8K2.u16219 (nat_lit 35573476) (nat_lit 2602726617) (nat_lit 0) D2M8K2.u16220 from rfl, totK_node, atot16219, atot16220]
  decide +kernel

theorem arows16225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16225 = true := by
  rw [show D2M8K2.u16225 = KTree.node D2M8K2.u16223 (nat_lit 35580217) (nat_lit 1490317522) (nat_lit 0) D2M8K2.u16224 from rfl, allE_node, arows16223, irow16225, arows16224]
  all_goals rfl

theorem atot16225 : totK PD2M8K2 D2M8K2.u16225 = [0, 0, 446060975287, 1566263690937, 1359051185437, 233885358492, 5066386085, 0] := by
  rw [show D2M8K2.u16225 = KTree.node D2M8K2.u16223 (nat_lit 35580217) (nat_lit 1490317522) (nat_lit 0) D2M8K2.u16224 from rfl, totK_node, atot16223, atot16224]
  decide +kernel

theorem arows16228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16228 = true := by
  rw [show D2M8K2.u16228 = KTree.node D2M8K2.u16226 (nat_lit 35583682) (nat_lit 4107158209) (nat_lit 0) D2M8K2.u16227 from rfl, allE_node, arows16226, irow16228, arows16227]
  all_goals rfl

theorem atot16228 : totK PD2M8K2 D2M8K2.u16228 = [0, 0, 435713681569, 1431134585862, 1298739838963, 361111124738, 21878179898, 0] := by
  rw [show D2M8K2.u16228 = KTree.node D2M8K2.u16226 (nat_lit 35583682) (nat_lit 4107158209) (nat_lit 0) D2M8K2.u16227 from rfl, totK_node, atot16226, atot16227]
  decide +kernel

theorem arows16233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16233 = true := by
  rw [show D2M8K2.u16233 = KTree.node D2M8K2.u16231 (nat_lit 35590492) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u16232 from rfl, allE_node, arows16231, irow16233, arows16232]
  all_goals rfl

theorem atot16233 : totK PD2M8K2 D2M8K2.u16233 = [0, 0, 410776601515, 1559236648308, 1447992261276, 189607666626, 1164319620, 0] := by
  rw [show D2M8K2.u16233 = KTree.node D2M8K2.u16231 (nat_lit 35590492) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u16232 from rfl, totK_node, atot16231, atot16232]
  decide +kernel

theorem arows16236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16236 = true := by
  rw [show D2M8K2.u16236 = KTree.node D2M8K2.u16234 (nat_lit 35594357) (nat_lit 1151923654) (nat_lit 0) D2M8K2.u16235 from rfl, allE_node, arows16234, irow16236, arows16235]
  all_goals rfl

theorem atot16236 : totK PD2M8K2 D2M8K2.u16236 = [0, 0, 411005903297, 1510207547377, 1418096643039, 244674133258, 5206561650, 0] := by
  rw [show D2M8K2.u16236 = KTree.node D2M8K2.u16234 (nat_lit 35594357) (nat_lit 1151923654) (nat_lit 0) D2M8K2.u16235 from rfl, totK_node, atot16234, atot16235]
  decide +kernel

theorem arows16240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16240 = true := by
  rw [show D2M8K2.u16240 = KTree.node D2M8K2.u16238 (nat_lit 35598002) (nat_lit 2792771641) (nat_lit 2048) D2M8K2.u16239 from rfl, allE_node, arows16238, irow16240, arows16239]
  all_goals rfl

theorem atot16240 : totK PD2M8K2 D2M8K2.u16240 = [0, 0, 480444177866, 1600593323636, 1276962778696, 171963995680, 5127371492, 0] := by
  rw [show D2M8K2.u16240 = KTree.node D2M8K2.u16238 (nat_lit 35598002) (nat_lit 2792771641) (nat_lit 2048) D2M8K2.u16239 from rfl, totK_node, atot16238, atot16239]
  decide +kernel

theorem arows16243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16243 = true := by
  rw [show D2M8K2.u16243 = KTree.node D2M8K2.u16241 (nat_lit 35602134) (nat_lit 3596172723) (nat_lit 0) D2M8K2.u16242 from rfl, allE_node, arows16241, irow16243, arows16242]
  all_goals rfl

theorem atot16243 : totK PD2M8K2 D2M8K2.u16243 = [0, 0, 266716252076, 1264603272181, 1578060270732, 444545380952, 21916389073, 0] := by
  rw [show D2M8K2.u16243 = KTree.node D2M8K2.u16241 (nat_lit 35602134) (nat_lit 3596172723) (nat_lit 0) D2M8K2.u16242 from rfl, totK_node, atot16241, atot16242]
  decide +kernel

theorem arows16251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16251 = true := by
  rw [show D2M8K2.u16251 = KTree.node D2M8K2.u16249 (nat_lit 35605382) (nat_lit 1701701339) (nat_lit 0) D2M8K2.u16250 from rfl, allE_node, arows16249, irow16251, arows16250]
  all_goals rfl

theorem atot16251 : totK PD2M8K2 D2M8K2.u16251 = [0, 0, 0, 509075729703, 1708449617379, 1119651022955, 124913735939, 1369150432] := by
  rw [show D2M8K2.u16251 = KTree.node D2M8K2.u16249 (nat_lit 35605382) (nat_lit 1701701339) (nat_lit 0) D2M8K2.u16250 from rfl, totK_node, atot16249, atot16250]
  decide +kernel

theorem arows16254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16254 = true := by
  rw [show D2M8K2.u16254 = KTree.node D2M8K2.u16252 (nat_lit 35614447) (nat_lit 2430501014) (nat_lit 0) D2M8K2.u16253 from rfl, allE_node, arows16252, irow16254, arows16253]
  all_goals rfl

theorem atot16254 : totK PD2M8K2 D2M8K2.u16254 = [0, 0, 0, 754455868987, 1950112372275, 770794548363, 33313588554, 0] := by
  rw [show D2M8K2.u16254 = KTree.node D2M8K2.u16252 (nat_lit 35614447) (nat_lit 2430501014) (nat_lit 0) D2M8K2.u16253 from rfl, totK_node, atot16252, atot16253]
  decide +kernel

theorem arows16258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16258 = true := by
  rw [show D2M8K2.u16258 = KTree.node D2M8K2.u16256 (nat_lit 35621621) (nat_lit 2401304114) (nat_lit 0) D2M8K2.u16257 from rfl, allE_node, arows16256, irow16258, arows16257]
  all_goals rfl

theorem atot16258 : totK PD2M8K2 D2M8K2.u16258 = [0, 0, 134721454216, 959617941687, 1772655653745, 665192666058, 31893025369, 0] := by
  rw [show D2M8K2.u16258 = KTree.node D2M8K2.u16256 (nat_lit 35621621) (nat_lit 2401304114) (nat_lit 0) D2M8K2.u16257 from rfl, totK_node, atot16256, atot16257]
  decide +kernel

theorem arows16261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16261 = true := by
  rw [show D2M8K2.u16261 = KTree.node D2M8K2.u16259 (nat_lit 35630043) (nat_lit 3702834849) (nat_lit 0) D2M8K2.u16260 from rfl, allE_node, arows16259, irow16261, arows16260]
  all_goals rfl

theorem atot16261 : totK PD2M8K2 D2M8K2.u16261 = [0, 0, 372297179740, 1362279827861, 1439079408530, 453700204252, 25516869169, 0] := by
  rw [show D2M8K2.u16261 = KTree.node D2M8K2.u16259 (nat_lit 35630043) (nat_lit 3702834849) (nat_lit 0) D2M8K2.u16260 from rfl, totK_node, atot16259, atot16260]
  decide +kernel

theorem arows16266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16266 = true := by
  rw [show D2M8K2.u16266 = KTree.node D2M8K2.u16264 (nat_lit 35633066) (nat_lit 4051131158) (nat_lit 0) D2M8K2.u16265 from rfl, allE_node, arows16264, irow16266, arows16265]
  all_goals rfl

theorem atot16266 : totK PD2M8K2 D2M8K2.u16266 = [0, 0, 504080510190, 1664100357831, 1291697367703, 193645319233, 4166040359, 0] := by
  rw [show D2M8K2.u16266 = KTree.node D2M8K2.u16264 (nat_lit 35633066) (nat_lit 4051131158) (nat_lit 0) D2M8K2.u16265 from rfl, totK_node, atot16264, atot16265]
  decide +kernel

theorem arows16269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16269 = true := by
  rw [show D2M8K2.u16269 = KTree.node D2M8K2.u16267 (nat_lit 35636925) (nat_lit 1163278076) (nat_lit 512) D2M8K2.u16268 from rfl, allE_node, arows16267, irow16269, arows16268]
  all_goals rfl

theorem atot16269 : totK PD2M8K2 D2M8K2.u16269 = [0, 0, 449253550648, 1627129303593, 1380455400918, 222588064047, 4189012250, 0] := by
  rw [show D2M8K2.u16269 = KTree.node D2M8K2.u16267 (nat_lit 35636925) (nat_lit 1163278076) (nat_lit 512) D2M8K2.u16268 from rfl, totK_node, atot16267, atot16268]
  decide +kernel

theorem arows16273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16273 = true := by
  rw [show D2M8K2.u16273 = KTree.node D2M8K2.u16271 (nat_lit 35642620) (nat_lit 3284418889) (nat_lit 0) D2M8K2.u16272 from rfl, allE_node, arows16271, irow16273, arows16272]
  all_goals rfl

theorem atot16273 : totK PD2M8K2 D2M8K2.u16273 = [0, 0, 562836258841, 1693546769274, 1230874517661, 181805573084, 3654551267, 0] := by
  rw [show D2M8K2.u16273 = KTree.node D2M8K2.u16271 (nat_lit 35642620) (nat_lit 3284418889) (nat_lit 0) D2M8K2.u16272 from rfl, totK_node, atot16271, atot16272]
  decide +kernel

theorem arows16276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16276 = true := by
  rw [show D2M8K2.u16276 = KTree.node D2M8K2.u16274 (nat_lit 35667000) (nat_lit 3428286285) (nat_lit 0) D2M8K2.u16275 from rfl, allE_node, arows16274, irow16276, arows16275]
  all_goals rfl

theorem atot16276 : totK PD2M8K2 D2M8K2.u16276 = [0, 0, 406510199064, 1445541610512, 1369479898029, 323220548988, 18396418596, 0] := by
  rw [show D2M8K2.u16276 = KTree.node D2M8K2.u16274 (nat_lit 35667000) (nat_lit 3428286285) (nat_lit 0) D2M8K2.u16275 from rfl, totK_node, atot16274, atot16275]
  decide +kernel

theorem arows16282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16282 = true := by
  rw [show D2M8K2.u16282 = KTree.node D2M8K2.u16280 (nat_lit 35670723) (nat_lit 2567899289) (nat_lit 0) D2M8K2.u16281 from rfl, allE_node, arows16280, irow16282, arows16281]
  all_goals rfl

theorem atot16282 : totK PD2M8K2 D2M8K2.u16282 = [0, 0, 417412625262, 1542548278042, 1424208434346, 297582126702, 12064694307, 0] := by
  rw [show D2M8K2.u16282 = KTree.node D2M8K2.u16280 (nat_lit 35670723) (nat_lit 2567899289) (nat_lit 0) D2M8K2.u16281 from rfl, totK_node, atot16280, atot16281]
  decide +kernel

theorem arows16285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16285 = true := by
  rw [show D2M8K2.u16285 = KTree.node D2M8K2.u16283 (nat_lit 35674094) (nat_lit 3826854700) (nat_lit 0) D2M8K2.u16284 from rfl, allE_node, arows16283, irow16285, arows16284]
  all_goals rfl

theorem atot16285 : totK PD2M8K2 D2M8K2.u16285 = [0, 0, 439041384501, 1473889931524, 1381156934758, 317632553914, 12081162873, 0] := by
  rw [show D2M8K2.u16285 = KTree.node D2M8K2.u16283 (nat_lit 35674094) (nat_lit 3826854700) (nat_lit 0) D2M8K2.u16284 from rfl, totK_node, atot16283, atot16284]
  decide +kernel

theorem arows16289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16289 = true := by
  rw [show D2M8K2.u16289 = KTree.node D2M8K2.u16287 (nat_lit 35680997) (nat_lit 2326679395) (nat_lit 0) D2M8K2.u16288 from rfl, allE_node, arows16287, irow16289, arows16288]
  all_goals rfl

theorem atot16289 : totK PD2M8K2 D2M8K2.u16289 = [0, 0, 495231337090, 1618128240003, 1299609496135, 174733609563, 2043780168, 0] := by
  rw [show D2M8K2.u16289 = KTree.node D2M8K2.u16287 (nat_lit 35680997) (nat_lit 2326679395) (nat_lit 0) D2M8K2.u16288 from rfl, totK_node, atot16287, atot16288]
  decide +kernel

theorem arows16292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16292 = true := by
  rw [show D2M8K2.u16292 = KTree.node D2M8K2.u16290 (nat_lit 35685314) (nat_lit 4058584325) (nat_lit 0) D2M8K2.u16291 from rfl, allE_node, arows16290, irow16292, arows16291]
  all_goals rfl

theorem atot16292 : totK PD2M8K2 D2M8K2.u16292 = [0, 0, 254251863405, 1199332835115, 1606067765416, 503599771650, 23346432518, 0] := by
  rw [show D2M8K2.u16292 = KTree.node D2M8K2.u16290 (nat_lit 35685314) (nat_lit 4058584325) (nat_lit 0) D2M8K2.u16291 from rfl, totK_node, atot16290, atot16291]
  decide +kernel

theorem arows16297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16297 = true := by
  rw [show D2M8K2.u16297 = KTree.node D2M8K2.u16295 (nat_lit 35688993) (nat_lit 1239476046) (nat_lit 512) D2M8K2.u16296 from rfl, allE_node, arows16295, irow16297, arows16296]
  all_goals rfl

theorem atot16297 : totK PD2M8K2 D2M8K2.u16297 = [0, 0, 0, 635753377722, 1748408306675, 1021196136518, 97709707473, 1166720416] := by
  rw [show D2M8K2.u16297 = KTree.node D2M8K2.u16295 (nat_lit 35688993) (nat_lit 1239476046) (nat_lit 512) D2M8K2.u16296 from rfl, totK_node, atot16295, atot16296]
  decide +kernel

theorem arows16300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16300 = true := by
  rw [show D2M8K2.u16300 = KTree.node D2M8K2.u16298 (nat_lit 35694836) (nat_lit 3605660575) (nat_lit 0) D2M8K2.u16299 from rfl, allE_node, arows16298, irow16300, arows16299]
  all_goals rfl

theorem atot16300 : totK PD2M8K2 D2M8K2.u16300 = [0, 0, 0, 481753268369, 1630918260928, 1183711168023, 181337709715, 5134755853] := by
  rw [show D2M8K2.u16300 = KTree.node D2M8K2.u16298 (nat_lit 35694836) (nat_lit 3605660575) (nat_lit 0) D2M8K2.u16299 from rfl, totK_node, atot16298, atot16299]
  decide +kernel

theorem arows16304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16304 = true := by
  rw [show D2M8K2.u16304 = KTree.node D2M8K2.u16302 (nat_lit 35704438) (nat_lit 3507175020) (nat_lit 0) D2M8K2.u16303 from rfl, allE_node, arows16302, irow16304, arows16303]
  all_goals rfl

theorem atot16304 : totK PD2M8K2 D2M8K2.u16304 = [0, 0, 118459880326, 997861953889, 1729725567194, 667720761964, 41685490832, 0] := by
  rw [show D2M8K2.u16304 = KTree.node D2M8K2.u16302 (nat_lit 35704438) (nat_lit 3507175020) (nat_lit 0) D2M8K2.u16303 from rfl, totK_node, atot16302, atot16303]
  decide +kernel

theorem arows16307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16307 = true := by
  rw [show D2M8K2.u16307 = KTree.node D2M8K2.u16305 (nat_lit 35709323) (nat_lit 2091858212) (nat_lit 0) D2M8K2.u16306 from rfl, allE_node, arows16305, irow16307, arows16306]
  all_goals rfl

theorem atot16307 : totK PD2M8K2 D2M8K2.u16307 = [0, 0, 480994361231, 1626585896243, 1332652141321, 166936613678, 1369150432, 0] := by
  rw [show D2M8K2.u16307 = KTree.node D2M8K2.u16305 (nat_lit 35709323) (nat_lit 2091858212) (nat_lit 0) D2M8K2.u16306 from rfl, totK_node, atot16305, atot16306]
  decide +kernel

theorem arows16314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16314 = true := by
  rw [show D2M8K2.u16314 = KTree.node D2M8K2.u16312 (nat_lit 35713486) (nat_lit 3917406774) (nat_lit 0) D2M8K2.u16313 from rfl, allE_node, arows16312, irow16314, arows16313]
  all_goals rfl

theorem atot16314 : totK PD2M8K2 D2M8K2.u16314 = [0, 0, 428960022016, 1490470518701, 1384447761979, 358055906860, 16293883145, 0] := by
  rw [show D2M8K2.u16314 = KTree.node D2M8K2.u16312 (nat_lit 35713486) (nat_lit 3917406774) (nat_lit 0) D2M8K2.u16313 from rfl, totK_node, atot16312, atot16313]
  decide +kernel

theorem arows16317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16317 = true := by
  rw [show D2M8K2.u16317 = KTree.node D2M8K2.u16315 (nat_lit 35719906) (nat_lit 4137557961) (nat_lit 0) D2M8K2.u16316 from rfl, allE_node, arows16315, irow16317, arows16316]
  all_goals rfl

theorem atot16317 : totK PD2M8K2 D2M8K2.u16317 = [0, 0, 394375818074, 1472678291116, 1426803285108, 300922187146, 8899456870, 0] := by
  rw [show D2M8K2.u16317 = KTree.node D2M8K2.u16315 (nat_lit 35719906) (nat_lit 4137557961) (nat_lit 0) D2M8K2.u16316 from rfl, totK_node, atot16315, atot16316]
  decide +kernel

theorem arows16321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16321 = true := by
  rw [show D2M8K2.u16321 = KTree.node D2M8K2.u16319 (nat_lit 35724865) (nat_lit 1489806105) (nat_lit 0) D2M8K2.u16320 from rfl, allE_node, arows16319, irow16321, arows16320]
  all_goals rfl

theorem atot16321 : totK PD2M8K2 D2M8K2.u16321 = [0, 0, 586757166690, 1732501097328, 1182767928011, 120353376023, 1096505104, 0] := by
  rw [show D2M8K2.u16321 = KTree.node D2M8K2.u16319 (nat_lit 35724865) (nat_lit 1489806105) (nat_lit 0) D2M8K2.u16320 from rfl, totK_node, atot16319, atot16320]
  decide +kernel

theorem arows16324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16324 = true := by
  rw [show D2M8K2.u16324 = KTree.node D2M8K2.u16322 (nat_lit 35728058) (nat_lit 3688858876) (nat_lit 0) D2M8K2.u16323 from rfl, allE_node, arows16322, irow16324, arows16323]
  all_goals rfl

theorem atot16324 : totK PD2M8K2 D2M8K2.u16324 = [0, 0, 0, 839839845930, 1940479701694, 702331330479, 30942051890, 0] := by
  rw [show D2M8K2.u16324 = KTree.node D2M8K2.u16322 (nat_lit 35728058) (nat_lit 3688858876) (nat_lit 0) D2M8K2.u16323 from rfl, totK_node, atot16322, atot16323]
  decide +kernel

theorem arows16329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16329 = true := by
  rw [show D2M8K2.u16329 = KTree.node D2M8K2.u16327 (nat_lit 35732454) (nat_lit 3868185851) (nat_lit 0) D2M8K2.u16328 from rfl, allE_node, arows16327, irow16329, arows16328]
  all_goals rfl

theorem atot16329 : totK PD2M8K2 D2M8K2.u16329 = [0, 0, 0, 611419757921, 1735196537662, 1098788272379, 109711929986, 1200365979] := by
  rw [show D2M8K2.u16329 = KTree.node D2M8K2.u16327 (nat_lit 35732454) (nat_lit 3868185851) (nat_lit 0) D2M8K2.u16328 from rfl, totK_node, atot16327, atot16328]
  decide +kernel

theorem arows16332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16332 = true := by
  rw [show D2M8K2.u16332 = KTree.node D2M8K2.u16330 (nat_lit 35741163) (nat_lit 3527755669) (nat_lit 0) D2M8K2.u16331 from rfl, allE_node, arows16330, irow16332, arows16331]
  all_goals rfl

theorem atot16332 : totK PD2M8K2 D2M8K2.u16332 = [0, 0, 0, 617928089551, 1608900725797, 1064220555133, 174413134395, 5163565574] := by
  rw [show D2M8K2.u16332 = KTree.node D2M8K2.u16330 (nat_lit 35741163) (nat_lit 3527755669) (nat_lit 0) D2M8K2.u16331 from rfl, totK_node, atot16330, atot16331]
  decide +kernel

theorem arows16336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16336 = true := by
  rw [show D2M8K2.u16336 = KTree.node D2M8K2.u16334 (nat_lit 35790348) (nat_lit 3608248717) (nat_lit 0) D2M8K2.u16335 from rfl, allE_node, arows16334, irow16336, arows16335]
  all_goals rfl

theorem atot16336 : totK PD2M8K2 D2M8K2.u16336 = [0, 0, 416852308827, 1323685370852, 1308124088134, 499620342113, 33968447482, 0] := by
  rw [show D2M8K2.u16336 = KTree.node D2M8K2.u16334 (nat_lit 35790348) (nat_lit 3608248717) (nat_lit 0) D2M8K2.u16335 from rfl, totK_node, atot16334, atot16335]
  decide +kernel

theorem arows16339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16339 = true := by
  rw [show D2M8K2.u16339 = KTree.node D2M8K2.u16337 (nat_lit 35794286) (nat_lit 3868467641) (nat_lit 0) D2M8K2.u16338 from rfl, allE_node, arows16337, irow16339, arows16338]
  all_goals rfl

theorem atot16339 : totK PD2M8K2 D2M8K2.u16339 = [0, 0, 426204706533, 1583105555046, 1444272243080, 195765157892, 1369150432, 0] := by
  rw [show D2M8K2.u16339 = KTree.node D2M8K2.u16337 (nat_lit 35794286) (nat_lit 3868467641) (nat_lit 0) D2M8K2.u16338 from rfl, totK_node, atot16337, atot16338]
  decide +kernel

theorem arows16345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16345 = true := by
  rw [show D2M8K2.u16345 = KTree.node D2M8K2.u16343 (nat_lit 35797261) (nat_lit 1391311165) (nat_lit 0) D2M8K2.u16344 from rfl, allE_node, arows16343, irow16345, arows16344]
  all_goals rfl

theorem atot16345 : totK PD2M8K2 D2M8K2.u16345 = [0, 0, 412609397409, 1358278273089, 1385537410617, 443226757791, 25217618697, 0] := by
  rw [show D2M8K2.u16345 = KTree.node D2M8K2.u16343 (nat_lit 35797261) (nat_lit 1391311165) (nat_lit 0) D2M8K2.u16344 from rfl, totK_node, atot16343, atot16344]
  decide +kernel

theorem arows16348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16348 = true := by
  rw [show D2M8K2.u16348 = KTree.node D2M8K2.u16346 (nat_lit 35800552) (nat_lit 3762376533) (nat_lit 0) D2M8K2.u16347 from rfl, allE_node, arows16346, irow16348, arows16347]
  all_goals rfl

theorem atot16348 : totK PD2M8K2 D2M8K2.u16348 = [0, 0, 402108213753, 1459014924715, 1418994669531, 288894518971, 8557595888, 0] := by
  rw [show D2M8K2.u16348 = KTree.node D2M8K2.u16346 (nat_lit 35800552) (nat_lit 3762376533) (nat_lit 0) D2M8K2.u16347 from rfl, totK_node, atot16346, atot16347]
  decide +kernel

theorem arows16352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16352 = true := by
  rw [show D2M8K2.u16352 = KTree.node D2M8K2.u16350 (nat_lit 35803955) (nat_lit 2899928239) (nat_lit 0) D2M8K2.u16351 from rfl, allE_node, arows16350, irow16352, arows16351]
  all_goals rfl

theorem atot16352 : totK PD2M8K2 D2M8K2.u16352 = [0, 0, 377265502146, 1451122740752, 1462327486975, 304468316977, 8656689423, 0] := by
  rw [show D2M8K2.u16352 = KTree.node D2M8K2.u16350 (nat_lit 35803955) (nat_lit 2899928239) (nat_lit 0) D2M8K2.u16351 from rfl, totK_node, atot16350, atot16351]
  decide +kernel

theorem arows16355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16355 = true := by
  rw [show D2M8K2.u16355 = KTree.node D2M8K2.u16353 (nat_lit 35810364) (nat_lit 2920646351) (nat_lit 0) D2M8K2.u16354 from rfl, allE_node, arows16353, irow16355, arows16354]
  all_goals rfl

theorem atot16355 : totK PD2M8K2 D2M8K2.u16355 = [0, 0, 93924006320, 955528684700, 1815634278116, 669977913389, 31289960066, 0] := by
  rw [show D2M8K2.u16355 = KTree.node D2M8K2.u16353 (nat_lit 35810364) (nat_lit 2920646351) (nat_lit 0) D2M8K2.u16354 from rfl, totK_node, atot16353, atot16354]
  decide +kernel

theorem arows16360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16360 = true := by
  rw [show D2M8K2.u16360 = KTree.node D2M8K2.u16358 (nat_lit 35814256) (nat_lit 3178629014) (nat_lit 0) D2M8K2.u16359 from rfl, allE_node, arows16358, irow16360, arows16359]
  all_goals rfl

theorem atot16360 : totK PD2M8K2 D2M8K2.u16360 = [0, 0, 0, 561782584693, 1663915149131, 1178943072259, 138947354655, 1288491354] := by
  rw [show D2M8K2.u16360 = KTree.node D2M8K2.u16358 (nat_lit 35814256) (nat_lit 3178629014) (nat_lit 0) D2M8K2.u16359 from rfl, totK_node, atot16358, atot16359]
  decide +kernel

theorem arows16363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16363 = true := by
  rw [show D2M8K2.u16363 = KTree.node D2M8K2.u16361 (nat_lit 35819444) (nat_lit 2348810439) (nat_lit 0) D2M8K2.u16362 from rfl, allE_node, arows16361, irow16363, arows16362]
  all_goals rfl

theorem atot16363 : totK PD2M8K2 D2M8K2.u16363 = [0, 0, 0, 458835270525, 1581265486570, 1252441377497, 194625654857, 4787054165] := by
  rw [show D2M8K2.u16363 = KTree.node D2M8K2.u16361 (nat_lit 35819444) (nat_lit 2348810439) (nat_lit 0) D2M8K2.u16362 from rfl, totK_node, atot16361, atot16362]
  decide +kernel

theorem arows16367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16367 = true := by
  rw [show D2M8K2.u16367 = KTree.node D2M8K2.u16365 (nat_lit 35823098) (nat_lit 3979444259) (nat_lit 0) D2M8K2.u16366 from rfl, allE_node, arows16365, irow16367, arows16366]
  all_goals rfl

theorem atot16367 : totK PD2M8K2 D2M8K2.u16367 = [0, 0, 0, 485831775126, 1603788277722, 1207416500525, 190336756897, 4838243418] := by
  rw [show D2M8K2.u16367 = KTree.node D2M8K2.u16365 (nat_lit 35823098) (nat_lit 3979444259) (nat_lit 0) D2M8K2.u16366 from rfl, totK_node, atot16365, atot16366]
  decide +kernel

theorem arows16370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16370 = true := by
  rw [show D2M8K2.u16370 = KTree.node D2M8K2.u16368 (nat_lit 35830128) (nat_lit 3589097136) (nat_lit 0) D2M8K2.u16369 from rfl, allE_node, arows16368, irow16370, arows16369]
  all_goals rfl

theorem atot16370 : totK PD2M8K2 D2M8K2.u16370 = [0, 0, 0, 336734528459, 1322235403090, 1456067580281, 408220067113, 21751168066] := by
  rw [show D2M8K2.u16370 = KTree.node D2M8K2.u16368 (nat_lit 35830128) (nat_lit 3589097136) (nat_lit 0) D2M8K2.u16369 from rfl, totK_node, atot16368, atot16369]
  decide +kernel

theorem arows6 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6 = true := by
  rw [show D2M8K2.u6 = KTree.node D2M8K2.u2 (nat_lit 7006) (nat_lit 3668920217) (nat_lit 0) D2M8K2.u5 from rfl, allE_node, arows2, irow6, arows5]
  all_goals rfl

theorem atot6 : totK PD2M8K2 D2M8K2.u6 = [871127801312, 3061643568000, 2779652379123, 510717105025, 14418877666, 0, 0, 0] := by
  rw [show D2M8K2.u6 = KTree.node D2M8K2.u2 (nat_lit 7006) (nat_lit 3668920217) (nat_lit 0) D2M8K2.u5 from rfl, totK_node, atot2, atot5]
  decide +kernel

theorem arows13 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13 = true := by
  rw [show D2M8K2.u13 = KTree.node D2M8K2.u9 (nat_lit 13587) (nat_lit 2786751732) (nat_lit 0) D2M8K2.u12 from rfl, allE_node, arows9, irow13, arows12]
  all_goals rfl

theorem atot13 : totK PD2M8K2 D2M8K2.u13 = [831675792627, 2969703086724, 2808148606969, 561442998410, 15416603213, 0, 0, 0] := by
  rw [show D2M8K2.u13 = KTree.node D2M8K2.u9 (nat_lit 13587) (nat_lit 2786751732) (nat_lit 0) D2M8K2.u12 from rfl, totK_node, atot9, atot12]
  decide +kernel

theorem arows21 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u21 = true := by
  rw [show D2M8K2.u21 = KTree.node D2M8K2.u17 (nat_lit 20481) (nat_lit 711063594) (nat_lit 0) D2M8K2.u20 from rfl, allE_node, arows17, irow21, arows20]
  all_goals rfl

theorem atot21 : totK PD2M8K2 D2M8K2.u21 = [422999544115, 1947332185515, 3049403951444, 1530662914312, 175537324112, 1369150432, 0, 0] := by
  rw [show D2M8K2.u21 = KTree.node D2M8K2.u17 (nat_lit 20481) (nat_lit 711063594) (nat_lit 0) D2M8K2.u20 from rfl, totK_node, atot17, atot20]
  decide +kernel

theorem arows28 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u28 = true := by
  rw [show D2M8K2.u28 = KTree.node D2M8K2.u24 (nat_lit 32349) (nat_lit 1569734978) (nat_lit 0) D2M8K2.u27 from rfl, allE_node, arows24, irow28, arows27]
  all_goals rfl

theorem atot28 : totK PD2M8K2 D2M8K2.u28 = [0, 1480156903848, 3775729754237, 1796114699391, 98896926484, 0, 0, 0] := by
  rw [show D2M8K2.u28 = KTree.node D2M8K2.u24 (nat_lit 32349) (nat_lit 1569734978) (nat_lit 0) D2M8K2.u27 from rfl, totK_node, atot24, atot27]
  decide +kernel

theorem arows37 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u37 = true := by
  rw [show D2M8K2.u37 = KTree.node D2M8K2.u33 (nat_lit 85256) (nat_lit 3575344930) (nat_lit 0) D2M8K2.u36 from rfl, allE_node, arows33, irow37, arows36]
  all_goals rfl

theorem atot37 : totK PD2M8K2 D2M8K2.u37 = [750106935813, 2778860461218, 2861652381511, 797835479598, 45199664339, 0, 0, 0] := by
  rw [show D2M8K2.u37 = KTree.node D2M8K2.u33 (nat_lit 85256) (nat_lit 3575344930) (nat_lit 0) D2M8K2.u36 from rfl, totK_node, atot33, atot36]
  decide +kernel

theorem arows44 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u44 = true := by
  rw [show D2M8K2.u44 = KTree.node D2M8K2.u40 (nat_lit 92316) (nat_lit 3087898953) (nat_lit 0) D2M8K2.u43 from rfl, allE_node, arows40, irow44, arows43]
  all_goals rfl

theorem atot44 : totK PD2M8K2 D2M8K2.u44 = [848718035950, 2921859621657, 2776008308382, 636748093294, 22346416134, 0, 0, 0] := by
  rw [show D2M8K2.u44 = KTree.node D2M8K2.u40 (nat_lit 92316) (nat_lit 3087898953) (nat_lit 0) D2M8K2.u43 from rfl, totK_node, atot40, atot43]
  decide +kernel

theorem arows52 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u52 = true := by
  rw [show D2M8K2.u52 = KTree.node D2M8K2.u48 (nat_lit 102676) (nat_lit 3691847987) (nat_lit 0) D2M8K2.u51 from rfl, allE_node, arows48, irow52, arows51]
  all_goals rfl

theorem atot52 : totK PD2M8K2 D2M8K2.u52 = [414661219762, 2070047278777, 3165536922480, 1365657664228, 123312128058, 1206465782, 0, 0] := by
  rw [show D2M8K2.u52 = KTree.node D2M8K2.u48 (nat_lit 102676) (nat_lit 3691847987) (nat_lit 0) D2M8K2.u51 from rfl, totK_node, atot48, atot51]
  decide +kernel

theorem arows59 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u59 = true := by
  rw [show D2M8K2.u59 = KTree.node D2M8K2.u55 (nat_lit 111812) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u58 from rfl, allE_node, arows55, irow59, arows58]
  all_goals rfl

theorem atot59 : totK PD2M8K2 D2M8K2.u59 = [0, 1030246020340, 3257343896670, 2440572479023, 391275222655, 13016197374, 0, 0] := by
  rw [show D2M8K2.u59 = KTree.node D2M8K2.u55 (nat_lit 111812) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u58 from rfl, totK_node, atot55, atot58]
  decide +kernel

theorem arows69 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u69 = true := by
  rw [show D2M8K2.u69 = KTree.node D2M8K2.u65 (nat_lit 122400) (nat_lit 3708958841) (nat_lit 0) D2M8K2.u68 from rfl, allE_node, arows65, irow69, arows68]
  all_goals rfl

theorem atot69 : totK PD2M8K2 D2M8K2.u69 = [422427504925, 1963735791858, 2957404199637, 1566952574963, 201470723463, 4574395652, 0, 0] := by
  rw [show D2M8K2.u69 = KTree.node D2M8K2.u65 (nat_lit 122400) (nat_lit 3708958841) (nat_lit 0) D2M8K2.u68 from rfl, totK_node, atot65, atot68]
  decide +kernel

theorem arows76 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u76 = true := by
  rw [show D2M8K2.u76 = KTree.node D2M8K2.u72 (nat_lit 134857) (nat_lit 1517277401) (nat_lit 0) D2M8K2.u75 from rfl, allE_node, arows72, irow76, arows75]
  all_goals rfl

theorem atot76 : totK PD2M8K2 D2M8K2.u76 = [767539080666, 2763623335952, 2873100696297, 807872060105, 43983153175, 0, 0, 0] := by
  rw [show D2M8K2.u76 = KTree.node D2M8K2.u72 (nat_lit 134857) (nat_lit 1517277401) (nat_lit 0) D2M8K2.u75 from rfl, totK_node, atot72, atot75]
  decide +kernel

theorem arows84 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u84 = true := by
  rw [show D2M8K2.u84 = KTree.node D2M8K2.u80 (nat_lit 141366) (nat_lit 3579298864) (nat_lit 0) D2M8K2.u83 from rfl, allE_node, arows80, irow84, arows83]
  all_goals rfl

theorem atot84 : totK PD2M8K2 D2M8K2.u84 = [824002103115, 2943554229291, 2829211292627, 590982021093, 13688528596, 0, 0, 0] := by
  rw [show D2M8K2.u84 = KTree.node D2M8K2.u80 (nat_lit 141366) (nat_lit 3579298864) (nat_lit 0) D2M8K2.u83 from rfl, totK_node, atot80, atot83]
  decide +kernel

theorem arows91 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u91 = true := by
  rw [show D2M8K2.u91 = KTree.node D2M8K2.u87 (nat_lit 148978) (nat_lit 3938046735) (nat_lit 0) D2M8K2.u90 from rfl, allE_node, arows87, irow91, arows90]
  all_goals rfl

theorem atot91 : totK PD2M8K2 D2M8K2.u91 = [0, 1222837667861, 3533025150782, 2203107039284, 211943725833, 1239866073, 0, 0] := by
  rw [show D2M8K2.u91 = KTree.node D2M8K2.u87 (nat_lit 148978) (nat_lit 3938046735) (nat_lit 0) D2M8K2.u90 from rfl, totK_node, atot87, atot90]
  decide +kernel

theorem arows100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u100 = true := by
  rw [show D2M8K2.u100 = KTree.node D2M8K2.u96 (nat_lit 160285) (nat_lit 1080269869) (nat_lit 0) D2M8K2.u99 from rfl, allE_node, arows96, irow100, arows99]
  all_goals rfl

theorem atot100 : totK PD2M8K2 D2M8K2.u100 = [22498951891, 848693382135, 2969590800509, 2691752956929, 513136757892, 17826068843, 0, 0] := by
  rw [show D2M8K2.u100 = KTree.node D2M8K2.u96 (nat_lit 160285) (nat_lit 1080269869) (nat_lit 0) D2M8K2.u99 from rfl, totK_node, atot96, atot99]
  decide +kernel

theorem arows107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u107 = true := by
  rw [show D2M8K2.u107 = KTree.node D2M8K2.u103 (nat_lit 169840) (nat_lit 3707287913) (nat_lit 0) D2M8K2.u106 from rfl, allE_node, arows103, irow107, arows106]
  all_goals rfl

theorem atot107 : totK PD2M8K2 D2M8K2.u107 = [889210267021, 2984360796682, 2684526629893, 624248704567, 27904876975, 0, 0, 0] := by
  rw [show D2M8K2.u107 = KTree.node D2M8K2.u103 (nat_lit 169840) (nat_lit 3707287913) (nat_lit 0) D2M8K2.u106 from rfl, totK_node, atot103, atot106]
  decide +kernel

theorem arows115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u115 = true := by
  rw [show D2M8K2.u115 = KTree.node D2M8K2.u111 (nat_lit 176676) (nat_lit 2125244572) (nat_lit 0) D2M8K2.u114 from rfl, allE_node, arows111, irow115, arows114]
  all_goals rfl

theorem atot115 : totK PD2M8K2 D2M8K2.u115 = [789233269930, 2843072833959, 2834979040192, 664735344038, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u115 = KTree.node D2M8K2.u111 (nat_lit 176676) (nat_lit 2125244572) (nat_lit 0) D2M8K2.u114 from rfl, totK_node, atot111, atot114]
  decide +kernel

theorem arows122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u122 = true := by
  rw [show D2M8K2.u122 = KTree.node D2M8K2.u118 (nat_lit 187248) (nat_lit 3588550848) (nat_lit 0) D2M8K2.u121 from rfl, allE_node, arows118, irow122, arows121]
  all_goals rfl

theorem atot122 : totK PD2M8K2 D2M8K2.u122 = [303387510043, 1910403113932, 3276037480245, 1512287266461, 140908411657, 1138244013, 0, 0] := by
  rw [show D2M8K2.u122 = KTree.node D2M8K2.u118 (nat_lit 187248) (nat_lit 3588550848) (nat_lit 0) D2M8K2.u121 from rfl, totK_node, atot118, atot121]
  decide +kernel

theorem arows133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u133 = true := by
  rw [show D2M8K2.u133 = KTree.node D2M8K2.u129 (nat_lit 197973) (nat_lit 1734347021) (nat_lit 0) D2M8K2.u132 from rfl, allE_node, arows129, irow133, arows132]
  all_goals rfl

theorem atot133 : totK PD2M8K2 D2M8K2.u133 = [0, 1355633554908, 3642935361926, 1956691341462, 166308278061, 1095107716, 0, 0] := by
  rw [show D2M8K2.u133 = KTree.node D2M8K2.u129 (nat_lit 197973) (nat_lit 1734347021) (nat_lit 0) D2M8K2.u132 from rfl, totK_node, atot129, atot132]
  decide +kernel

theorem arows140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u140 = true := by
  rw [show D2M8K2.u140 = KTree.node D2M8K2.u136 (nat_lit 209786) (nat_lit 3770641079) (nat_lit 0) D2M8K2.u139 from rfl, allE_node, arows136, irow140, arows139]
  all_goals rfl

theorem atot140 : totK PD2M8K2 D2M8K2.u140 = [752182103749, 2587467344835, 2677935575911, 1040897876919, 152222063894, 3882006667, 0, 0] := by
  rw [show D2M8K2.u140 = KTree.node D2M8K2.u136 (nat_lit 209786) (nat_lit 3770641079) (nat_lit 0) D2M8K2.u139 from rfl, totK_node, atot136, atot139]
  decide +kernel

theorem arows148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u148 = true := by
  rw [show D2M8K2.u148 = KTree.node D2M8K2.u144 (nat_lit 217184) (nat_lit 3696601444) (nat_lit 0) D2M8K2.u147 from rfl, allE_node, arows144, irow148, arows147]
  all_goals rfl

theorem atot148 : totK PD2M8K2 D2M8K2.u148 = [825402083562, 2872159616930, 2792679623535, 688296071014, 29513444391, 0, 0, 0] := by
  rw [show D2M8K2.u148 = KTree.node D2M8K2.u144 (nat_lit 217184) (nat_lit 3696601444) (nat_lit 0) D2M8K2.u147 from rfl, totK_node, atot144, atot147]
  decide +kernel

theorem arows155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u155 = true := by
  rw [show D2M8K2.u155 = KTree.node D2M8K2.u151 (nat_lit 227065) (nat_lit 1473350719) (nat_lit 0) D2M8K2.u154 from rfl, allE_node, arows151, irow155, arows154]
  all_goals rfl

theorem atot155 : totK PD2M8K2 D2M8K2.u155 = [441685160947, 2148667707299, 3171198517590, 1323946562271, 115657119620, 1310285577, 0, 0] := by
  rw [show D2M8K2.u155 = KTree.node D2M8K2.u151 (nat_lit 227065) (nat_lit 1473350719) (nat_lit 0) D2M8K2.u154 from rfl, totK_node, atot151, atot154]
  decide +kernel

theorem arows164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u164 = true := by
  rw [show D2M8K2.u164 = KTree.node D2M8K2.u160 (nat_lit 235778) (nat_lit 4047483344) (nat_lit 0) D2M8K2.u163 from rfl, allE_node, arows160, irow164, arows163]
  all_goals rfl

theorem atot164 : totK PD2M8K2 D2M8K2.u164 = [0, 1025102031765, 3265245089490, 2554290762965, 331419748696, 4879840392, 0, 0] := by
  rw [show D2M8K2.u164 = KTree.node D2M8K2.u160 (nat_lit 235778) (nat_lit 4047483344) (nat_lit 0) D2M8K2.u163 from rfl, totK_node, atot160, atot163]
  decide +kernel

theorem arows171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u171 = true := by
  rw [show D2M8K2.u171 = KTree.node D2M8K2.u167 (nat_lit 246413) (nat_lit 1444569612) (nat_lit 0) D2M8K2.u170 from rfl, allE_node, arows167, irow171, arows170]
  all_goals rfl

theorem atot171 : totK PD2M8K2 D2M8K2.u171 = [0, 832254516356, 2939903718438, 2736057616045, 611602332868, 26682572712, 0, 0] := by
  rw [show D2M8K2.u171 = KTree.node D2M8K2.u167 (nat_lit 246413) (nat_lit 1444569612) (nat_lit 0) D2M8K2.u170 from rfl, totK_node, atot167, atot170]
  decide +kernel

theorem arows179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u179 = true := by
  rw [show D2M8K2.u179 = KTree.node D2M8K2.u175 (nat_lit 256936) (nat_lit 3782286622) (nat_lit 0) D2M8K2.u178 from rfl, allE_node, arows175, irow179, arows178]
  all_goals rfl

theorem atot179 : totK PD2M8K2 D2M8K2.u179 = [0, 839768372045, 3045712814299, 2800506435270, 479985423885, 14260808441, 0, 0] := by
  rw [show D2M8K2.u179 = KTree.node D2M8K2.u175 (nat_lit 256936) (nat_lit 3782286622) (nat_lit 0) D2M8K2.u178 from rfl, totK_node, atot175, atot178]
  decide +kernel

theorem arows186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u186 = true := by
  rw [show D2M8K2.u186 = KTree.node D2M8K2.u182 (nat_lit 263473) (nat_lit 1403630470) (nat_lit 0) D2M8K2.u185 from rfl, allE_node, arows182, irow186, arows185]
  all_goals rfl

theorem atot186 : totK PD2M8K2 D2M8K2.u186 = [0, 858699699788, 2974193463635, 2750682730815, 509381928394, 18026911340, 0, 0] := by
  rw [show D2M8K2.u186 = KTree.node D2M8K2.u182 (nat_lit 263473) (nat_lit 1403630470) (nat_lit 0) D2M8K2.u185 from rfl, totK_node, atot182, atot185]
  decide +kernel

theorem arows196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u196 = true := by
  rw [show D2M8K2.u196 = KTree.node D2M8K2.u192 (nat_lit 270517) (nat_lit 1259977240) (nat_lit 0) D2M8K2.u195 from rfl, allE_node, arows192, irow196, arows195]
  all_goals rfl

theorem atot196 : totK PD2M8K2 D2M8K2.u196 = [0, 144051062126, 1578042437800, 3387841435221, 1725372189356, 195964469298, 1369150432, 0] := by
  rw [show D2M8K2.u196 = KTree.node D2M8K2.u192 (nat_lit 270517) (nat_lit 1259977240) (nat_lit 0) D2M8K2.u195 from rfl, totK_node, atot192, atot195]
  decide +kernel

theorem arows203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u203 = true := by
  rw [show D2M8K2.u203 = KTree.node D2M8K2.u199 (nat_lit 284352) (nat_lit 3512258599) (nat_lit 0) D2M8K2.u202 from rfl, allE_node, arows199, irow203, arows202]
  all_goals rfl

theorem atot203 : totK PD2M8K2 D2M8K2.u203 = [0, 249819336703, 1924816937061, 3489912812534, 1316064222264, 78930523588, 0, 0] := by
  rw [show D2M8K2.u203 = KTree.node D2M8K2.u199 (nat_lit 284352) (nat_lit 3512258599) (nat_lit 0) D2M8K2.u202 from rfl, totK_node, atot199, atot202]
  decide +kernel

theorem arows211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u211 = true := by
  rw [show D2M8K2.u211 = KTree.node D2M8K2.u207 (nat_lit 336719) (nat_lit 2159978722) (nat_lit 0) D2M8K2.u210 from rfl, allE_node, arows207, irow211, arows210]
  all_goals rfl

theorem atot211 : totK PD2M8K2 D2M8K2.u211 = [0, 936154233919, 3157061141725, 2697237479418, 436993268538, 6653499497, 0, 0] := by
  rw [show D2M8K2.u211 = KTree.node D2M8K2.u207 (nat_lit 336719) (nat_lit 2159978722) (nat_lit 0) D2M8K2.u210 from rfl, totK_node, atot207, atot210]
  decide +kernel

theorem arows218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u218 = true := by
  rw [show D2M8K2.u218 = KTree.node D2M8K2.u214 (nat_lit 346855) (nat_lit 2359060360) (nat_lit 0) D2M8K2.u217 from rfl, allE_node, arows214, irow218, arows217]
  all_goals rfl

theorem atot218 : totK PD2M8K2 D2M8K2.u218 = [0, 821762796072, 2953683534327, 2827995475725, 549935585354, 17966996581, 0, 0] := by
  rw [show D2M8K2.u218 = KTree.node D2M8K2.u214 (nat_lit 346855) (nat_lit 2359060360) (nat_lit 0) D2M8K2.u217 from rfl, totK_node, atot214, atot217]
  decide +kernel

theorem arows227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u227 = true := by
  rw [show D2M8K2.u227 = KTree.node D2M8K2.u223 (nat_lit 374860) (nat_lit 2830267036) (nat_lit 0) D2M8K2.u226 from rfl, allE_node, arows223, irow227, arows226]
  all_goals rfl

theorem atot227 : totK PD2M8K2 D2M8K2.u227 = [0, 747371853637, 2917371554996, 2949421634665, 577416500144, 15053452749, 0, 0] := by
  rw [show D2M8K2.u227 = KTree.node D2M8K2.u223 (nat_lit 374860) (nat_lit 2830267036) (nat_lit 0) D2M8K2.u226 from rfl, totK_node, atot223, atot226]
  decide +kernel

theorem arows234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u234 = true := by
  rw [show D2M8K2.u234 = KTree.node D2M8K2.u230 (nat_lit 386286) (nat_lit 4086215485) (nat_lit 0) D2M8K2.u233 from rfl, allE_node, arows230, irow234, arows233]
  all_goals rfl

theorem atot234 : totK PD2M8K2 D2M8K2.u234 = [0, 847117539815, 2941530591397, 2776392155634, 595649789416, 19615988614, 0, 0] := by
  rw [show D2M8K2.u234 = KTree.node D2M8K2.u230 (nat_lit 386286) (nat_lit 4086215485) (nat_lit 0) D2M8K2.u233 from rfl, totK_node, atot230, atot233]
  decide +kernel

theorem arows242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u242 = true := by
  rw [show D2M8K2.u242 = KTree.node D2M8K2.u238 (nat_lit 392952) (nat_lit 3481732596) (nat_lit 0) D2M8K2.u241 from rfl, allE_node, arows238, irow242, arows241]
  all_goals rfl

theorem atot242 : totK PD2M8K2 D2M8K2.u242 = [0, 833686676701, 2948615015406, 2791702324887, 579967535161, 18904996023, 0, 0] := by
  rw [show D2M8K2.u242 = KTree.node D2M8K2.u238 (nat_lit 392952) (nat_lit 3481732596) (nat_lit 0) D2M8K2.u241 from rfl, totK_node, atot238, atot241]
  decide +kernel

theorem arows249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u249 = true := by
  rw [show D2M8K2.u249 = KTree.node D2M8K2.u245 (nat_lit 421824) (nat_lit 3593909260) (nat_lit 0) D2M8K2.u248 from rfl, allE_node, arows245, irow249, arows248]
  all_goals rfl

theorem atot249 : totK PD2M8K2 D2M8K2.u249 = [0, 820100775366, 2980071274084, 2846146335463, 518096286009, 14393010609, 0, 0] := by
  rw [show D2M8K2.u249 = KTree.node D2M8K2.u245 (nat_lit 421824) (nat_lit 3593909260) (nat_lit 0) D2M8K2.u248 from rfl, totK_node, atot245, atot248]
  decide +kernel

theorem arows261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u261 = true := by
  rw [show D2M8K2.u261 = KTree.node D2M8K2.u257 (nat_lit 428671) (nat_lit 2265454588) (nat_lit 0) D2M8K2.u260 from rfl, allE_node, arows257, irow261, arows260]
  all_goals rfl

theorem atot261 : totK PD2M8K2 D2M8K2.u261 = [0, 841527444555, 2974158334587, 2805587242760, 548125357456, 18164832359, 0, 0] := by
  rw [show D2M8K2.u261 = KTree.node D2M8K2.u257 (nat_lit 428671) (nat_lit 2265454588) (nat_lit 0) D2M8K2.u260 from rfl, totK_node, atot257, atot260]
  decide +kernel

theorem arows268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u268 = true := by
  rw [show D2M8K2.u268 = KTree.node D2M8K2.u264 (nat_lit 460250) (nat_lit 4242461733) (nat_lit 0) D2M8K2.u267 from rfl, allE_node, arows264, irow268, arows267]
  all_goals rfl

theorem atot268 : totK PD2M8K2 D2M8K2.u268 = [0, 893386830355, 3058582037523, 2750456759497, 516548506338, 10944778055, 0, 0] := by
  rw [show D2M8K2.u268 = KTree.node D2M8K2.u264 (nat_lit 460250) (nat_lit 4242461733) (nat_lit 0) D2M8K2.u267 from rfl, totK_node, atot264, atot267]
  decide +kernel

theorem arows276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u276 = true := by
  rw [show D2M8K2.u276 = KTree.node D2M8K2.u272 (nat_lit 467579) (nat_lit 2364312512) (nat_lit 0) D2M8K2.u275 from rfl, allE_node, arows272, irow276, arows275]
  all_goals rfl

theorem atot276 : totK PD2M8K2 D2M8K2.u276 = [0, 855726997933, 3053171081454, 2810934031555, 505533327852, 10331839290, 0, 0] := by
  rw [show D2M8K2.u276 = KTree.node D2M8K2.u272 (nat_lit 467579) (nat_lit 2364312512) (nat_lit 0) D2M8K2.u275 from rfl, totK_node, atot272, atot275]
  decide +kernel

theorem arows283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u283 = true := by
  rw [show D2M8K2.u283 = KTree.node D2M8K2.u279 (nat_lit 996108) (nat_lit 3039064465) (nat_lit 0) D2M8K2.u282 from rfl, allE_node, arows279, irow283, arows282]
  all_goals rfl

theorem atot283 : totK PD2M8K2 D2M8K2.u283 = [637203700550, 2196031592682, 2468188223059, 1504766744390, 411002843790, 21897291087, 0, 0] := by
  rw [show D2M8K2.u283 = KTree.node D2M8K2.u279 (nat_lit 996108) (nat_lit 3039064465) (nat_lit 0) D2M8K2.u282 from rfl, totK_node, atot279, atot282]
  decide +kernel

theorem arows292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u292 = true := by
  rw [show D2M8K2.u292 = KTree.node D2M8K2.u288 (nat_lit 1006797) (nat_lit 1471437730) (nat_lit 0) D2M8K2.u291 from rfl, allE_node, arows288, irow292, arows291]
  all_goals rfl

theorem atot292 : totK PD2M8K2 D2M8K2.u292 = [827305840257, 2898120002343, 2769062842038, 644274720062, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u292 = KTree.node D2M8K2.u288 (nat_lit 1006797) (nat_lit 1471437730) (nat_lit 0) D2M8K2.u291 from rfl, totK_node, atot288, atot291]
  decide +kernel

theorem arows299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u299 = true := by
  rw [show D2M8K2.u299 = KTree.node D2M8K2.u295 (nat_lit 1013605) (nat_lit 1350073034) (nat_lit 0) D2M8K2.u298 from rfl, allE_node, arows295, irow299, arows298]
  all_goals rfl

theorem atot299 : totK PD2M8K2 D2M8K2.u299 = [557232741001, 2542682988513, 3150308471992, 882575140255, 36640207665, 0, 0, 0] := by
  rw [show D2M8K2.u299 = KTree.node D2M8K2.u295 (nat_lit 1013605) (nat_lit 1350073034) (nat_lit 0) D2M8K2.u298 from rfl, totK_node, atot295, atot298]
  decide +kernel

theorem arows307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u307 = true := by
  rw [show D2M8K2.u307 = KTree.node D2M8K2.u303 (nat_lit 1024184) (nat_lit 3813067118) (nat_lit 0) D2M8K2.u306 from rfl, allE_node, arows303, irow307, arows306]
  all_goals rfl

theorem atot307 : totK PD2M8K2 D2M8K2.u307 = [0, 1209576602353, 3534008068553, 2126358166940, 215015415622, 1369150432, 0, 0] := by
  rw [show D2M8K2.u307 = KTree.node D2M8K2.u303 (nat_lit 1024184) (nat_lit 3813067118) (nat_lit 0) D2M8K2.u306 from rfl, totK_node, atot303, atot306]
  decide +kernel

theorem arows314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u314 = true := by
  rw [show D2M8K2.u314 = KTree.node D2M8K2.u310 (nat_lit 1041034) (nat_lit 3924853953) (nat_lit 0) D2M8K2.u313 from rfl, allE_node, arows310, irow314, arows313]
  all_goals rfl

theorem atot314 : totK PD2M8K2 D2M8K2.u314 = [501585544218, 2185949307716, 3160498602755, 1331659966544, 79729434633, 0, 0, 0] := by
  rw [show D2M8K2.u314 = KTree.node D2M8K2.u310 (nat_lit 1041034) (nat_lit 3924853953) (nat_lit 0) D2M8K2.u313 from rfl, totK_node, atot310, atot313]
  decide +kernel

theorem arows324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u324 = true := by
  rw [show D2M8K2.u324 = KTree.node D2M8K2.u320 (nat_lit 1050631) (nat_lit 2232029273) (nat_lit 0) D2M8K2.u323 from rfl, allE_node, arows320, irow324, arows323]
  all_goals rfl

theorem atot324 : totK PD2M8K2 D2M8K2.u324 = [823090133791, 2968449590451, 2830562419272, 580527278043, 18013738644, 0, 0, 0] := by
  rw [show D2M8K2.u324 = KTree.node D2M8K2.u320 (nat_lit 1050631) (nat_lit 2232029273) (nat_lit 0) D2M8K2.u323 from rfl, totK_node, atot320, atot323]
  decide +kernel

theorem arows331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u331 = true := by
  rw [show D2M8K2.u331 = KTree.node D2M8K2.u327 (nat_lit 1061318) (nat_lit 4185429624) (nat_lit 0) D2M8K2.u330 from rfl, allE_node, arows327, irow331, arows330]
  all_goals rfl

theorem atot331 : totK PD2M8K2 D2M8K2.u331 = [337878552242, 1747707659301, 2919249992610, 1802393129918, 433903155276, 29044448997, 0, 0] := by
  rw [show D2M8K2.u331 = KTree.node D2M8K2.u327 (nat_lit 1061318) (nat_lit 4185429624) (nat_lit 0) D2M8K2.u330 from rfl, totK_node, atot327, atot330]
  decide +kernel

theorem arows339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u339 = true := by
  rw [show D2M8K2.u339 = KTree.node D2M8K2.u335 (nat_lit 1067366) (nat_lit 4109748624) (nat_lit 0) D2M8K2.u338 from rfl, allE_node, arows335, irow339, arows338]
  all_goals rfl

theorem atot339 : totK PD2M8K2 D2M8K2.u339 = [0, 823617471401, 2996141624949, 2825264903108, 533180753581, 13037293492, 0, 0] := by
  rw [show D2M8K2.u339 = KTree.node D2M8K2.u335 (nat_lit 1067366) (nat_lit 4109748624) (nat_lit 0) D2M8K2.u338 from rfl, totK_node, atot335, atot338]
  decide +kernel

theorem arows346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u346 = true := by
  rw [show D2M8K2.u346 = KTree.node D2M8K2.u342 (nat_lit 1078218) (nat_lit 3255516858) (nat_lit 0) D2M8K2.u345 from rfl, allE_node, arows342, irow346, arows345]
  all_goals rfl

theorem atot346 : totK PD2M8K2 D2M8K2.u346 = [493992587577, 2000124678080, 2712827466972, 1619929650095, 372679081473, 10717512769, 0, 0] := by
  rw [show D2M8K2.u346 = KTree.node D2M8K2.u342 (nat_lit 1078218) (nat_lit 3255516858) (nat_lit 0) D2M8K2.u345 from rfl, totK_node, atot342, atot345]
  decide +kernel

theorem arows355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u355 = true := by
  rw [show D2M8K2.u355 = KTree.node D2M8K2.u351 (nat_lit 1084981) (nat_lit 944153317) (nat_lit 0) D2M8K2.u354 from rfl, allE_node, arows351, irow355, arows354]
  all_goals rfl

theorem atot355 : totK PD2M8K2 D2M8K2.u355 = [776140459051, 2780235947465, 2835886686521, 816093101567, 44060904243, 0, 0, 0] := by
  rw [show D2M8K2.u355 = KTree.node D2M8K2.u351 (nat_lit 1084981) (nat_lit 944153317) (nat_lit 0) D2M8K2.u354 from rfl, totK_node, atot351, atot354]
  decide +kernel

theorem arows362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u362 = true := by
  rw [show D2M8K2.u362 = KTree.node D2M8K2.u358 (nat_lit 1094788) (nat_lit 2908664129) (nat_lit 0) D2M8K2.u361 from rfl, allE_node, arows358, irow362, arows361]
  all_goals rfl

theorem atot362 : totK PD2M8K2 D2M8K2.u362 = [836963459370, 2947457055696, 2811256742328, 567083383295, 13410525106, 0, 0, 0] := by
  rw [show D2M8K2.u362 = KTree.node D2M8K2.u358 (nat_lit 1094788) (nat_lit 2908664129) (nat_lit 0) D2M8K2.u361 from rfl, totK_node, atot358, atot361]
  decide +kernel

theorem arows370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u370 = true := by
  rw [show D2M8K2.u370 = KTree.node D2M8K2.u366 (nat_lit 1101920) (nat_lit 3784708862) (nat_lit 0) D2M8K2.u369 from rfl, allE_node, arows366, irow370, arows369]
  all_goals rfl

theorem atot370 : totK PD2M8K2 D2M8K2.u370 = [0, 1247154619416, 3542056786915, 2146363766419, 202401791850, 1206465782, 0, 0] := by
  rw [show D2M8K2.u370 = KTree.node D2M8K2.u366 (nat_lit 1101920) (nat_lit 3784708862) (nat_lit 0) D2M8K2.u369 from rfl, totK_node, atot366, atot369]
  decide +kernel

theorem arows377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u377 = true := by
  rw [show D2M8K2.u377 = KTree.node D2M8K2.u373 (nat_lit 1113540) (nat_lit 3001905520) (nat_lit 0) D2M8K2.u376 from rfl, allE_node, arows373, irow377, arows376]
  all_goals rfl

theorem atot377 : totK PD2M8K2 D2M8K2.u377 = [0, 865471875073, 3041862422250, 2612166172715, 488613080092, 17590593026, 0, 0] := by
  rw [show D2M8K2.u377 = KTree.node D2M8K2.u373 (nat_lit 1113540) (nat_lit 3001905520) (nat_lit 0) D2M8K2.u376 from rfl, totK_node, atot373, atot376]
  decide +kernel

theorem arows388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u388 = true := by
  rw [show D2M8K2.u388 = KTree.node D2M8K2.u384 (nat_lit 1163929) (nat_lit 1486102151) (nat_lit 0) D2M8K2.u387 from rfl, allE_node, arows384, irow388, arows387]
  all_goals rfl

theorem atot388 : totK PD2M8K2 D2M8K2.u388 = [795790547778, 2824881491990, 2785022655981, 760155799919, 44096311817, 0, 0, 0] := by
  rw [show D2M8K2.u388 = KTree.node D2M8K2.u384 (nat_lit 1163929) (nat_lit 1486102151) (nat_lit 0) D2M8K2.u387 from rfl, totK_node, atot384, atot387]
  decide +kernel

theorem arows395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u395 = true := by
  rw [show D2M8K2.u395 = KTree.node D2M8K2.u391 (nat_lit 1170500) (nat_lit 3341709948) (nat_lit 0) D2M8K2.u394 from rfl, allE_node, arows391, irow395, arows394]
  all_goals rfl

theorem atot395 : totK PD2M8K2 D2M8K2.u395 = [750091096706, 2764154536369, 2868078558054, 761128061289, 33712187542, 0, 0, 0] := by
  rw [show D2M8K2.u395 = KTree.node D2M8K2.u391 (nat_lit 1170500) (nat_lit 3341709948) (nat_lit 0) D2M8K2.u394 from rfl, totK_node, atot391, atot394]
  decide +kernel

theorem arows403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u403 = true := by
  rw [show D2M8K2.u403 = KTree.node D2M8K2.u399 (nat_lit 1177977) (nat_lit 1864447005) (nat_lit 0) D2M8K2.u402 from rfl, allE_node, arows399, irow403, arows402]
  all_goals rfl

theorem atot403 : totK PD2M8K2 D2M8K2.u403 = [435809923056, 2079487789210, 3125275288355, 1355687497932, 119670315092, 1138244013, 0, 0] := by
  rw [show D2M8K2.u403 = KTree.node D2M8K2.u399 (nat_lit 1177977) (nat_lit 1864447005) (nat_lit 0) D2M8K2.u402 from rfl, totK_node, atot399, atot402]
  decide +kernel

theorem arows410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u410 = true := by
  rw [show D2M8K2.u410 = KTree.node D2M8K2.u406 (nat_lit 1190470) (nat_lit 2517805820) (nat_lit 0) D2M8K2.u409 from rfl, allE_node, arows406, irow410, arows409]
  all_goals rfl

theorem atot410 : totK PD2M8K2 D2M8K2.u410 = [0, 1467308757168, 3721207466744, 1861976200941, 128142199393, 0, 0, 0] := by
  rw [show D2M8K2.u410 = KTree.node D2M8K2.u406 (nat_lit 1190470) (nat_lit 2517805820) (nat_lit 0) D2M8K2.u409 from rfl, totK_node, atot406, atot409]
  decide +kernel

theorem arows419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u419 = true := by
  rw [show D2M8K2.u419 = KTree.node D2M8K2.u415 (nat_lit 1204393) (nat_lit 1453006153) (nat_lit 0) D2M8K2.u418 from rfl, allE_node, arows415, irow419, arows418]
  all_goals rfl

theorem atot419 : totK PD2M8K2 D2M8K2.u419 = [799181244681, 2555938291761, 2516702526112, 1108155660309, 204027783084, 4977114383, 0, 0] := by
  rw [show D2M8K2.u419 = KTree.node D2M8K2.u415 (nat_lit 1204393) (nat_lit 1453006153) (nat_lit 0) D2M8K2.u418 from rfl, totK_node, atot415, atot418]
  decide +kernel

theorem arows426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u426 = true := by
  rw [show D2M8K2.u426 = KTree.node D2M8K2.u422 (nat_lit 1211242) (nat_lit 3989793527) (nat_lit 0) D2M8K2.u425 from rfl, allE_node, arows422, irow426, arows425]
  all_goals rfl

theorem atot426 : totK PD2M8K2 D2M8K2.u426 = [753814390661, 2733875894999, 2870029281006, 837030477098, 38875779224, 0, 0, 0] := by
  rw [show D2M8K2.u426 = KTree.node D2M8K2.u422 (nat_lit 1211242) (nat_lit 3989793527) (nat_lit 0) D2M8K2.u425 from rfl, totK_node, atot422, atot425]
  decide +kernel

theorem arows434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u434 = true := by
  rw [show D2M8K2.u434 = KTree.node D2M8K2.u430 (nat_lit 1221966) (nat_lit 3726701012) (nat_lit 0) D2M8K2.u433 from rfl, allE_node, arows430, irow434, arows433]
  all_goals rfl

theorem atot434 : totK PD2M8K2 D2M8K2.u434 = [440265286504, 2222306591746, 3287406316298, 1198717266271, 59824478667, 0, 0, 0] := by
  rw [show D2M8K2.u434 = KTree.node D2M8K2.u430 (nat_lit 1221966) (nat_lit 3726701012) (nat_lit 0) D2M8K2.u433 from rfl, totK_node, atot430, atot433]
  decide +kernel

theorem arows441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u441 = true := by
  rw [show D2M8K2.u441 = KTree.node D2M8K2.u437 (nat_lit 1230717) (nat_lit 819840534) (nat_lit 0) D2M8K2.u440 from rfl, allE_node, arows437, irow441, arows440]
  all_goals rfl

theorem atot441 : totK PD2M8K2 D2M8K2.u441 = [0, 961704904177, 3188389353591, 2643165364046, 378409110121, 6190125969, 0, 0] := by
  rw [show D2M8K2.u441 = KTree.node D2M8K2.u437 (nat_lit 1230717) (nat_lit 819840534) (nat_lit 0) D2M8K2.u440 from rfl, totK_node, atot437, atot440]
  decide +kernel

theorem arows451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u451 = true := by
  rw [show D2M8K2.u451 = KTree.node D2M8K2.u447 (nat_lit 1241676) (nat_lit 2822161470) (nat_lit 0) D2M8K2.u450 from rfl, allE_node, arows447, irow451, arows450]
  all_goals rfl

theorem atot451 : totK PD2M8K2 D2M8K2.u451 = [0, 878180850432, 2932206517924, 2716505461000, 618425580474, 26682572712, 0, 0] := by
  rw [show D2M8K2.u451 = KTree.node D2M8K2.u447 (nat_lit 1241676) (nat_lit 2822161470) (nat_lit 0) D2M8K2.u450 from rfl, totK_node, atot447, atot450]
  decide +kernel

theorem arows458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u458 = true := by
  rw [show D2M8K2.u458 = KTree.node D2M8K2.u454 (nat_lit 1251915) (nat_lit 3403449122) (nat_lit 0) D2M8K2.u457 from rfl, allE_node, arows454, irow458, arows457]
  all_goals rfl

theorem atot458 : totK PD2M8K2 D2M8K2.u458 = [0, 855058150767, 3061890278763, 2758579808290, 495564364165, 14418877666, 0, 0] := by
  rw [show D2M8K2.u458 = KTree.node D2M8K2.u454 (nat_lit 1251915) (nat_lit 3403449122) (nat_lit 0) D2M8K2.u457 from rfl, totK_node, atot454, atot457]
  decide +kernel

theorem arows466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u466 = true := by
  rw [show D2M8K2.u466 = KTree.node D2M8K2.u462 (nat_lit 1259385) (nat_lit 1903903263) (nat_lit 0) D2M8K2.u465 from rfl, allE_node, arows462, irow466, arows465]
  all_goals rfl

theorem atot466 : totK PD2M8K2 D2M8K2.u466 = [0, 906932737198, 3172614146835, 2701888807287, 382215090664, 6115342739, 0, 0] := by
  rw [show D2M8K2.u466 = KTree.node D2M8K2.u462 (nat_lit 1259385) (nat_lit 1903903263) (nat_lit 0) D2M8K2.u465 from rfl, totK_node, atot462, atot465]
  decide +kernel

theorem arows473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u473 = true := by
  rw [show D2M8K2.u473 = KTree.node D2M8K2.u469 (nat_lit 1266686) (nat_lit 2059420879) (nat_lit 0) D2M8K2.u472 from rfl, allE_node, arows469, irow473, arows472]
  all_goals rfl

theorem atot473 : totK PD2M8K2 D2M8K2.u473 = [0, 0, 1345523742042, 3657167648796, 1841680569333, 157620708406, 1275377855, 0] := by
  rw [show D2M8K2.u473 = KTree.node D2M8K2.u469 (nat_lit 1266686) (nat_lit 2059420879) (nat_lit 0) D2M8K2.u472 from rfl, totK_node, atot469, atot472]
  decide +kernel

theorem arows482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u482 = true := by
  rw [show D2M8K2.u482 = KTree.node D2M8K2.u478 (nat_lit 1283067) (nat_lit 3088296497) (nat_lit 0) D2M8K2.u481 from rfl, allE_node, arows478, irow482, arows481]
  all_goals rfl

theorem atot482 : totK PD2M8K2 D2M8K2.u482 = [0, 430077321765, 2305667194839, 3319873322245, 1080692543721, 54329421547, 0, 0] := by
  rw [show D2M8K2.u482 = KTree.node D2M8K2.u478 (nat_lit 1283067) (nat_lit 3088296497) (nat_lit 0) D2M8K2.u481 from rfl, totK_node, atot478, atot481]
  decide +kernel

theorem arows489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u489 = true := by
  rw [show D2M8K2.u489 = KTree.node D2M8K2.u485 (nat_lit 1294598) (nat_lit 4178041573) (nat_lit 0) D2M8K2.u488 from rfl, allE_node, arows485, irow489, arows488]
  all_goals rfl

theorem atot489 : totK PD2M8K2 D2M8K2.u489 = [0, 824398054263, 2899465908601, 2780749970320, 680864288198, 25111220349, 0, 0] := by
  rw [show D2M8K2.u489 = KTree.node D2M8K2.u485 (nat_lit 1294598) (nat_lit 4178041573) (nat_lit 0) D2M8K2.u488 from rfl, totK_node, atot485, atot488]
  decide +kernel

theorem arows497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u497 = true := by
  rw [show D2M8K2.u497 = KTree.node D2M8K2.u493 (nat_lit 1305263) (nat_lit 2130997309) (nat_lit 0) D2M8K2.u496 from rfl, allE_node, arows493, irow497, arows496]
  all_goals rfl

theorem atot497 : totK PD2M8K2 D2M8K2.u497 = [0, 821621908998, 2911525835554, 2799539175304, 641417992464, 23006347722, 0, 0] := by
  rw [show D2M8K2.u497 = KTree.node D2M8K2.u493 (nat_lit 1305263) (nat_lit 2130997309) (nat_lit 0) D2M8K2.u496 from rfl, totK_node, atot493, atot496]
  decide +kernel

theorem arows504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u504 = true := by
  rw [show D2M8K2.u504 = KTree.node D2M8K2.u500 (nat_lit 1333060) (nat_lit 4038862822) (nat_lit 0) D2M8K2.u503 from rfl, allE_node, arows500, irow504, arows503]
  all_goals rfl

theorem atot504 : totK PD2M8K2 D2M8K2.u504 = [0, 851305115891, 2946845331733, 2785407122542, 631247162800, 25253243897, 0, 0] := by
  rw [show D2M8K2.u504 = KTree.node D2M8K2.u500 (nat_lit 1333060) (nat_lit 4038862822) (nat_lit 0) D2M8K2.u503 from rfl, totK_node, atot500, atot503]
  decide +kernel

theorem arows517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u517 = true := by
  rw [show D2M8K2.u517 = KTree.node D2M8K2.u513 (nat_lit 1342789) (nat_lit 1247173908) (nat_lit 0) D2M8K2.u516 from rfl, allE_node, arows513, irow517, arows516]
  all_goals rfl

theorem atot517 : totK PD2M8K2 D2M8K2.u517 = [0, 834584878615, 2982602911992, 2794523453541, 537201163221, 17972337965, 0, 0] := by
  rw [show D2M8K2.u517 = KTree.node D2M8K2.u513 (nat_lit 1342789) (nat_lit 1247173908) (nat_lit 0) D2M8K2.u516 from rfl, totK_node, atot513, atot516]
  decide +kernel

theorem arows524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u524 = true := by
  rw [show D2M8K2.u524 = KTree.node D2M8K2.u520 (nat_lit 1349730) (nat_lit 1554881596) (nat_lit 0) D2M8K2.u523 from rfl, allE_node, arows520, irow524, arows523]
  all_goals rfl

theorem atot524 : totK PD2M8K2 D2M8K2.u524 = [0, 0, 1344200942903, 3606391053617, 1919661326052, 177581301533, 1206465782, 0] := by
  rw [show D2M8K2.u524 = KTree.node D2M8K2.u520 (nat_lit 1349730) (nat_lit 1554881596) (nat_lit 0) D2M8K2.u523 from rfl, totK_node, atot520, atot523]
  decide +kernel

theorem arows532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u532 = true := by
  rw [show D2M8K2.u532 = KTree.node D2M8K2.u528 (nat_lit 1362192) (nat_lit 2598234342) (nat_lit 0) D2M8K2.u531 from rfl, allE_node, arows528, irow532, arows531]
  all_goals rfl

theorem atot532 : totK PD2M8K2 D2M8K2.u532 = [0, 0, 904748522059, 3065210906268, 2471319868150, 476676464247, 17590593026, 0] := by
  rw [show D2M8K2.u532 = KTree.node D2M8K2.u528 (nat_lit 1362192) (nat_lit 2598234342) (nat_lit 0) D2M8K2.u531 from rfl, totK_node, atot528, atot531]
  decide +kernel

theorem arows539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u539 = true := by
  rw [show D2M8K2.u539 = KTree.node D2M8K2.u535 (nat_lit 1412933) (nat_lit 2289525901) (nat_lit 0) D2M8K2.u538 from rfl, allE_node, arows535, irow539, arows538]
  all_goals rfl

theorem atot539 : totK PD2M8K2 D2M8K2.u539 = [0, 794123137510, 2908517743435, 2800021740274, 665934137283, 28294748274, 0, 0] := by
  rw [show D2M8K2.u539 = KTree.node D2M8K2.u535 (nat_lit 1412933) (nat_lit 2289525901) (nat_lit 0) D2M8K2.u538 from rfl, totK_node, atot535, atot538]
  decide +kernel

theorem arows548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u548 = true := by
  rw [show D2M8K2.u548 = KTree.node D2M8K2.u544 (nat_lit 1419897) (nat_lit 1862413635) (nat_lit 0) D2M8K2.u547 from rfl, allE_node, arows544, irow548, arows547]
  all_goals rfl

theorem atot548 : totK PD2M8K2 D2M8K2.u548 = [0, 837854052912, 2921504365555, 2785213072188, 592638645749, 19145436479, 0, 0] := by
  rw [show D2M8K2.u548 = KTree.node D2M8K2.u544 (nat_lit 1419897) (nat_lit 1862413635) (nat_lit 0) D2M8K2.u547 from rfl, totK_node, atot544, atot547]
  decide +kernel

theorem arows555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u555 = true := by
  rw [show D2M8K2.u555 = KTree.node D2M8K2.u551 (nat_lit 1431049) (nat_lit 1508690721) (nat_lit 0) D2M8K2.u554 from rfl, allE_node, arows551, irow555, arows554]
  all_goals rfl

theorem atot555 : totK PD2M8K2 D2M8K2.u555 = [0, 345466061500, 1994316281863, 3268237376184, 1350229526672, 104215170320, 1103454931, 0] := by
  rw [show D2M8K2.u555 = KTree.node D2M8K2.u551 (nat_lit 1431049) (nat_lit 1508690721) (nat_lit 0) D2M8K2.u554 from rfl, totK_node, atot551, atot554]
  decide +kernel

theorem arows563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u563 = true := by
  rw [show D2M8K2.u563 = KTree.node D2M8K2.u559 (nat_lit 1442529) (nat_lit 1843401288) (nat_lit 0) D2M8K2.u562 from rfl, allE_node, arows559, irow563, arows562]
  all_goals rfl

theorem atot563 : totK PD2M8K2 D2M8K2.u563 = [0, 78129874012, 1390736930801, 3444488245199, 1860306093562, 207283965160, 4779662215, 0] := by
  rw [show D2M8K2.u563 = KTree.node D2M8K2.u559 (nat_lit 1442529) (nat_lit 1843401288) (nat_lit 0) D2M8K2.u562 from rfl, totK_node, atot559, atot562]
  decide +kernel

theorem arows570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u570 = true := by
  rw [show D2M8K2.u570 = KTree.node D2M8K2.u566 (nat_lit 1455586) (nat_lit 3994981239) (nat_lit 0) D2M8K2.u569 from rfl, allE_node, arows566, irow570, arows569]
  all_goals rfl

theorem atot570 : totK PD2M8K2 D2M8K2.u570 = [0, 800335206434, 2885062303335, 2806002095776, 705940424735, 34131549329, 0, 0] := by
  rw [show D2M8K2.u570 = KTree.node D2M8K2.u566 (nat_lit 1455586) (nat_lit 3994981239) (nat_lit 0) D2M8K2.u569 from rfl, totK_node, atot566, atot569]
  decide +kernel

theorem arows580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u580 = true := by
  rw [show D2M8K2.u580 = KTree.node D2M8K2.u576 (nat_lit 1462110) (nat_lit 3987774429) (nat_lit 0) D2M8K2.u579 from rfl, allE_node, arows576, irow580, arows579]
  all_goals rfl

theorem atot580 : totK PD2M8K2 D2M8K2.u580 = [0, 910865802997, 3054226733034, 2740757788483, 526242110122, 14812611811, 0, 0] := by
  rw [show D2M8K2.u580 = KTree.node D2M8K2.u576 (nat_lit 1462110) (nat_lit 3987774429) (nat_lit 0) D2M8K2.u579 from rfl, totK_node, atot576, atot579]
  decide +kernel

theorem arows587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u587 = true := by
  rw [show D2M8K2.u587 = KTree.node D2M8K2.u583 (nat_lit 1493682) (nat_lit 2667374021) (nat_lit 0) D2M8K2.u586 from rfl, allE_node, arows583, irow587, arows586]
  all_goals rfl

theorem atot587 : totK PD2M8K2 D2M8K2.u587 = [613088067924, 2154138538605, 2472432903091, 1543853503951, 426905975533, 21982452388, 0, 0] := by
  rw [show D2M8K2.u587 = KTree.node D2M8K2.u583 (nat_lit 1493682) (nat_lit 2667374021) (nat_lit 0) D2M8K2.u586 from rfl, totK_node, atot583, atot586]
  decide +kernel

theorem arows595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u595 = true := by
  rw [show D2M8K2.u595 = KTree.node D2M8K2.u591 (nat_lit 1504521) (nat_lit 1850731021) (nat_lit 0) D2M8K2.u594 from rfl, allE_node, arows591, irow595, arows594]
  all_goals rfl

theorem atot595 : totK PD2M8K2 D2M8K2.u595 = [824126208430, 2874146933289, 2784907614109, 655408229568, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u595 = KTree.node D2M8K2.u591 (nat_lit 1504521) (nat_lit 1850731021) (nat_lit 0) D2M8K2.u594 from rfl, totK_node, atot591, atot594]
  decide +kernel

theorem arows602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u602 = true := by
  rw [show D2M8K2.u602 = KTree.node D2M8K2.u598 (nat_lit 1511168) (nat_lit 2899012122) (nat_lit 0) D2M8K2.u601 from rfl, allE_node, arows598, irow602, arows601]
  all_goals rfl

theorem atot602 : totK PD2M8K2 D2M8K2.u602 = [592516514321, 2573613596286, 3098017588841, 867715900813, 36640207665, 0, 0, 0] := by
  rw [show D2M8K2.u602 = KTree.node D2M8K2.u598 (nat_lit 1511168) (nat_lit 2899012122) (nat_lit 0) D2M8K2.u601 from rfl, totK_node, atot598, atot601]
  decide +kernel

theorem arows611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u611 = true := by
  rw [show D2M8K2.u611 = KTree.node D2M8K2.u607 (nat_lit 1521993) (nat_lit 1828798327) (nat_lit 0) D2M8K2.u610 from rfl, allE_node, arows607, irow611, arows610]
  all_goals rfl

theorem atot611 : totK PD2M8K2 D2M8K2.u611 = [0, 1222208887534, 3547672114835, 2112006165744, 212612227272, 1369150432, 0, 0] := by
  rw [show D2M8K2.u611 = KTree.node D2M8K2.u607 (nat_lit 1521993) (nat_lit 1828798327) (nat_lit 0) D2M8K2.u610 from rfl, totK_node, atot607, atot610]
  decide +kernel

theorem arows618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u618 = true := by
  rw [show D2M8K2.u618 = KTree.node D2M8K2.u614 (nat_lit 1538617) (nat_lit 1147450146) (nat_lit 0) D2M8K2.u617 from rfl, allE_node, arows614, irow618, arows617]
  all_goals rfl

theorem atot618 : totK PD2M8K2 D2M8K2.u618 = [434179821839, 2128483335953, 3242209965735, 1369163792244, 82181888105, 0, 0, 0] := by
  rw [show D2M8K2.u618 = KTree.node D2M8K2.u614 (nat_lit 1538617) (nat_lit 1147450146) (nat_lit 0) D2M8K2.u617 from rfl, totK_node, atot614, atot617]
  decide +kernel

theorem arows626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u626 = true := by
  rw [show D2M8K2.u626 = KTree.node D2M8K2.u622 (nat_lit 1548038) (nat_lit 4112680829) (nat_lit 0) D2M8K2.u625 from rfl, allE_node, arows622, irow626, arows625]
  all_goals rfl

theorem atot626 : totK PD2M8K2 D2M8K2.u626 = [846548629682, 2966449957227, 2806756043675, 589379492076, 18214542822, 0, 0, 0] := by
  rw [show D2M8K2.u626 = KTree.node D2M8K2.u622 (nat_lit 1548038) (nat_lit 4112680829) (nat_lit 0) D2M8K2.u625 from rfl, totK_node, atot622, atot625]
  decide +kernel

theorem arows633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u633 = true := by
  rw [show D2M8K2.u633 = KTree.node D2M8K2.u629 (nat_lit 1555090) (nat_lit 4014846645) (nat_lit 0) D2M8K2.u632 from rfl, allE_node, arows629, irow633, arows632]
  all_goals rfl

theorem atot633 : totK PD2M8K2 D2M8K2.u633 = [382152125481, 1848788177324, 2888472417818, 1706800250821, 413387983413, 29044448997, 0, 0] := by
  rw [show D2M8K2.u633 = KTree.node D2M8K2.u629 (nat_lit 1555090) (nat_lit 4014846645) (nat_lit 0) D2M8K2.u632 from rfl, totK_node, atot629, atot632]
  decide +kernel

theorem arows644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u644 = true := by
  rw [show D2M8K2.u644 = KTree.node D2M8K2.u640 (nat_lit 1568385) (nat_lit 1758926435) (nat_lit 0) D2M8K2.u643 from rfl, allE_node, arows640, irow644, arows643]
  all_goals rfl

theorem atot644 : totK PD2M8K2 D2M8K2.u644 = [0, 823851705333, 3012832083317, 2809812410281, 536706743952, 13096297542, 0, 0] := by
  rw [show D2M8K2.u644 = KTree.node D2M8K2.u640 (nat_lit 1568385) (nat_lit 1758926435) (nat_lit 0) D2M8K2.u643 from rfl, totK_node, atot640, atot643]
  decide +kernel

theorem arows651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u651 = true := by
  rw [show D2M8K2.u651 = KTree.node D2M8K2.u647 (nat_lit 1575771) (nat_lit 3640750391) (nat_lit 0) D2M8K2.u650 from rfl, allE_node, arows647, irow651, arows650]
  all_goals rfl

theorem atot651 : totK PD2M8K2 D2M8K2.u651 = [437729727136, 1901158078464, 2750182647810, 1722132361347, 390071600409, 10717512769, 0, 0] := by
  rw [show D2M8K2.u651 = KTree.node D2M8K2.u647 (nat_lit 1575771) (nat_lit 3640750391) (nat_lit 0) D2M8K2.u650 from rfl, totK_node, atot647, atot650]
  decide +kernel

theorem arows659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u659 = true := by
  rw [show D2M8K2.u659 = KTree.node D2M8K2.u655 (nat_lit 1624033) (nat_lit 1495297859) (nat_lit 0) D2M8K2.u658 from rfl, allE_node, arows655, irow659, arows658]
  all_goals rfl

theorem atot659 : totK PD2M8K2 D2M8K2.u659 = [832677861078, 2841210703712, 2769493830658, 779666054984, 40244046672, 0, 0, 0] := by
  rw [show D2M8K2.u659 = KTree.node D2M8K2.u655 (nat_lit 1624033) (nat_lit 1495297859) (nat_lit 0) D2M8K2.u658 from rfl, totK_node, atot655, atot658]
  decide +kernel

theorem arows666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u666 = true := by
  rw [show D2M8K2.u666 = KTree.node D2M8K2.u662 (nat_lit 1633829) (nat_lit 1934481791) (nat_lit 0) D2M8K2.u665 from rfl, allE_node, arows662, irow666, arows665]
  all_goals rfl

theorem atot666 : totK PD2M8K2 D2M8K2.u666 = [837108855589, 2969921095397, 2803945983830, 550797747102, 13731065314, 0, 0, 0] := by
  rw [show D2M8K2.u666 = KTree.node D2M8K2.u662 (nat_lit 1633829) (nat_lit 1934481791) (nat_lit 0) D2M8K2.u665 from rfl, totK_node, atot662, atot665]
  decide +kernel

theorem arows675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u675 = true := by
  rw [show D2M8K2.u675 = KTree.node D2M8K2.u671 (nat_lit 1640811) (nat_lit 3409650406) (nat_lit 0) D2M8K2.u674 from rfl, allE_node, arows671, irow675, arows674]
  all_goals rfl

theorem atot675 : totK PD2M8K2 D2M8K2.u675 = [0, 1233289157463, 3519324797916, 2190169749819, 209717606504, 1239866073, 0, 0] := by
  rw [show D2M8K2.u675 = KTree.node D2M8K2.u671 (nat_lit 1640811) (nat_lit 3409650406) (nat_lit 0) D2M8K2.u674 from rfl, totK_node, atot671, atot674]
  decide +kernel

theorem arows682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u682 = true := by
  rw [show D2M8K2.u682 = KTree.node D2M8K2.u678 (nat_lit 1652514) (nat_lit 3302475107) (nat_lit 0) D2M8K2.u681 from rfl, allE_node, arows678, irow682, arows681]
  all_goals rfl

theorem atot682 : totK PD2M8K2 D2M8K2.u682 = [0, 864406112439, 3027870904838, 2641438726048, 501039344500, 17826068843, 0, 0] := by
  rw [show D2M8K2.u682 = KTree.node D2M8K2.u678 (nat_lit 1652514) (nat_lit 3302475107) (nat_lit 0) D2M8K2.u681 from rfl, totK_node, atot678, atot681]
  decide +kernel

theorem arows690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u690 = true := by
  rw [show D2M8K2.u690 = KTree.node D2M8K2.u686 (nat_lit 1661253) (nat_lit 1490410262) (nat_lit 0) D2M8K2.u689 from rfl, allE_node, arows686, irow690, arows689]
  all_goals rfl

theorem atot690 : totK PD2M8K2 D2M8K2.u690 = [795894362607, 2810707345219, 2758283145587, 798155582564, 52577323950, 0, 0, 0] := by
  rw [show D2M8K2.u690 = KTree.node D2M8K2.u686 (nat_lit 1661253) (nat_lit 1490410262) (nat_lit 0) D2M8K2.u689 from rfl, totK_node, atot686, atot689]
  decide +kernel

theorem arows697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u697 = true := by
  rw [show D2M8K2.u697 = KTree.node D2M8K2.u693 (nat_lit 1668672) (nat_lit 3677347549) (nat_lit 0) D2M8K2.u696 from rfl, allE_node, arows693, irow697, arows696]
  all_goals rfl

theorem atot697 : totK PD2M8K2 D2M8K2.u697 = [750161295513, 2714287646810, 2869467359021, 803568115517, 33697933978, 0, 0, 0] := by
  rw [show D2M8K2.u697 = KTree.node D2M8K2.u693 (nat_lit 1668672) (nat_lit 3677347549) (nat_lit 0) D2M8K2.u696 from rfl, totK_node, atot693, atot696]
  decide +kernel

theorem arows707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u707 = true := by
  rw [show D2M8K2.u707 = KTree.node D2M8K2.u703 (nat_lit 1675325) (nat_lit 1698005714) (nat_lit 0) D2M8K2.u706 from rfl, allE_node, arows703, irow707, arows706]
  all_goals rfl

theorem atot707 : totK PD2M8K2 D2M8K2.u707 = [435828682369, 2093507924841, 3121264703415, 1341382047567, 119670315092, 1138244013, 0, 0] := by
  rw [show D2M8K2.u707 = KTree.node D2M8K2.u703 (nat_lit 1675325) (nat_lit 1698005714) (nat_lit 0) D2M8K2.u706 from rfl, totK_node, atot703, atot706]
  decide +kernel

theorem arows714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u714 = true := by
  rw [show D2M8K2.u714 = KTree.node D2M8K2.u710 (nat_lit 1690042) (nat_lit 2652070606) (nat_lit 0) D2M8K2.u713 from rfl, allE_node, arows710, irow714, arows713]
  all_goals rfl

theorem atot714 : totK PD2M8K2 D2M8K2.u714 = [0, 1473614258211, 3743084205642, 1850854060596, 121992819000, 0, 0, 0] := by
  rw [show D2M8K2.u714 = KTree.node D2M8K2.u710 (nat_lit 1690042) (nat_lit 2652070606) (nat_lit 0) D2M8K2.u713 from rfl, totK_node, atot710, atot713]
  decide +kernel

theorem arows722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u722 = true := by
  rw [show D2M8K2.u722 = KTree.node D2M8K2.u718 (nat_lit 1701850) (nat_lit 3992918297) (nat_lit 0) D2M8K2.u721 from rfl, allE_node, arows718, irow722, arows721]
  all_goals rfl

theorem atot722 : totK PD2M8K2 D2M8K2.u722 = [799295251953, 2562644069838, 2515318253859, 1107740307391, 197603858656, 4977114383, 0, 0] := by
  rw [show D2M8K2.u722 = KTree.node D2M8K2.u718 (nat_lit 1701850) (nat_lit 3992918297) (nat_lit 0) D2M8K2.u721 from rfl, totK_node, atot718, atot721]
  decide +kernel

theorem arows729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u729 = true := by
  rw [show D2M8K2.u729 = KTree.node D2M8K2.u725 (nat_lit 1709044) (nat_lit 4003057398) (nat_lit 0) D2M8K2.u728 from rfl, allE_node, arows725, irow729, arows728]
  all_goals rfl

theorem atot729 : totK PD2M8K2 D2M8K2.u729 = [753889690797, 2718346889391, 2876154710649, 855995253645, 47074980593, 0, 0, 0] := by
  rw [show D2M8K2.u729 = KTree.node D2M8K2.u725 (nat_lit 1709044) (nat_lit 4003057398) (nat_lit 0) D2M8K2.u728 from rfl, totK_node, atot725, atot728]
  decide +kernel

theorem arows738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u738 = true := by
  rw [show D2M8K2.u738 = KTree.node D2M8K2.u734 (nat_lit 1719420) (nat_lit 3222443541) (nat_lit 0) D2M8K2.u737 from rfl, allE_node, arows734, irow738, arows737]
  all_goals rfl

theorem atot738 : totK PD2M8K2 D2M8K2.u738 = [440289439084, 2314049119795, 3322048605085, 1081127343059, 44528817767, 0, 0, 0] := by
  rw [show D2M8K2.u738 = KTree.node D2M8K2.u734 (nat_lit 1719420) (nat_lit 3222443541) (nat_lit 0) D2M8K2.u737 from rfl, totK_node, atot734, atot737]
  decide +kernel

theorem arows745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u745 = true := by
  rw [show D2M8K2.u745 = KTree.node D2M8K2.u741 (nat_lit 1728145) (nat_lit 1557112149) (nat_lit 0) D2M8K2.u744 from rfl, allE_node, arows741, irow745, arows744]
  all_goals rfl

theorem atot745 : totK PD2M8K2 D2M8K2.u745 = [0, 955570014920, 3164979976781, 2699376950758, 392090015992, 6190125969, 0, 0] := by
  rw [show D2M8K2.u745 = KTree.node D2M8K2.u741 (nat_lit 1728145) (nat_lit 1557112149) (nat_lit 0) D2M8K2.u744 from rfl, totK_node, atot741, atot744]
  decide +kernel

theorem arows753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u753 = true := by
  rw [show D2M8K2.u753 = KTree.node D2M8K2.u749 (nat_lit 1739145) (nat_lit 1567786621) (nat_lit 0) D2M8K2.u752 from rfl, allE_node, arows749, irow753, arows752]
  all_goals rfl

theorem atot753 : totK PD2M8K2 D2M8K2.u753 = [0, 792827605490, 2931533158508, 2756283505457, 616205507256, 26682572712, 0, 0] := by
  rw [show D2M8K2.u753 = KTree.node D2M8K2.u749 (nat_lit 1739145) (nat_lit 1567786621) (nat_lit 0) D2M8K2.u752 from rfl, totK_node, atot749, atot752]
  decide +kernel

theorem arows760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u760 = true := by
  rw [show D2M8K2.u760 = KTree.node D2M8K2.u756 (nat_lit 1749949) (nat_lit 1213604548) (nat_lit 0) D2M8K2.u759 from rfl, allE_node, arows756, irow760, arows759]
  all_goals rfl

theorem atot760 : totK PD2M8K2 D2M8K2.u760 = [0, 1016003089377, 3296030497909, 2570275199294, 327238648471, 2533470052, 0, 0] := by
  rw [show D2M8K2.u760 = KTree.node D2M8K2.u756 (nat_lit 1749949) (nat_lit 1213604548) (nat_lit 0) D2M8K2.u759 from rfl, totK_node, atot756, atot759]
  decide +kernel

theorem arows772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u772 = true := by
  rw [show D2M8K2.u772 = KTree.node D2M8K2.u768 (nat_lit 1756847) (nat_lit 1111331225) (nat_lit 0) D2M8K2.u771 from rfl, allE_node, arows768, irow772, arows771]
  all_goals rfl

theorem atot772 : totK PD2M8K2 D2M8K2.u772 = [0, 831932393438, 2965079044057, 2778825481463, 550659468134, 18107683323, 0, 0] := by
  rw [show D2M8K2.u772 = KTree.node D2M8K2.u768 (nat_lit 1756847) (nat_lit 1111331225) (nat_lit 0) D2M8K2.u771 from rfl, totK_node, atot768, atot771]
  decide +kernel

theorem arows779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u779 = true := by
  rw [show D2M8K2.u779 = KTree.node D2M8K2.u775 (nat_lit 1764091) (nat_lit 2207755931) (nat_lit 0) D2M8K2.u778 from rfl, allE_node, arows775, irow779, arows778]
  all_goals rfl

theorem atot779 : totK PD2M8K2 D2M8K2.u779 = [0, 0, 1448046904860, 3688651834862, 1731299518579, 142216245722, 1310517177, 0] := by
  rw [show D2M8K2.u779 = KTree.node D2M8K2.u775 (nat_lit 1764091) (nat_lit 2207755931) (nat_lit 0) D2M8K2.u778 from rfl, totK_node, atot775, atot778]
  decide +kernel

theorem arows787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u787 = true := by
  rw [show D2M8K2.u787 = KTree.node D2M8K2.u783 (nat_lit 1780214) (nat_lit 3955190428) (nat_lit 0) D2M8K2.u786 from rfl, allE_node, arows783, irow787, arows786]
  all_goals rfl

theorem atot787 : totK PD2M8K2 D2M8K2.u787 = [0, 430243710856, 2246873783232, 3306883747614, 1135549104634, 56537577069, 0, 0] := by
  rw [show D2M8K2.u787 = KTree.node D2M8K2.u783 (nat_lit 1780214) (nat_lit 3955190428) (nat_lit 0) D2M8K2.u786 from rfl, totK_node, atot783, atot786]
  decide +kernel

theorem arows794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u794 = true := by
  rw [show D2M8K2.u794 = KTree.node D2M8K2.u790 (nat_lit 1795176) (nat_lit 3446532554) (nat_lit 0) D2M8K2.u793 from rfl, allE_node, arows790, irow794, arows793]
  all_goals rfl

theorem atot794 : totK PD2M8K2 D2M8K2.u794 = [0, 770227379103, 2681605195957, 2833295771272, 878600726106, 43665812515, 0, 0] := by
  rw [show D2M8K2.u794 = KTree.node D2M8K2.u790 (nat_lit 1795176) (nat_lit 3446532554) (nat_lit 0) D2M8K2.u793 from rfl, totK_node, atot790, atot793]
  decide +kernel

theorem arows803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u803 = true := by
  rw [show D2M8K2.u803 = KTree.node D2M8K2.u799 (nat_lit 1802284) (nat_lit 3829442997) (nat_lit 0) D2M8K2.u802 from rfl, allE_node, arows799, irow803, arows802]
  all_goals rfl

theorem atot803 : totK PD2M8K2 D2M8K2.u803 = [0, 876722909606, 3005714948907, 2704347432728, 596068990346, 21707210787, 0, 0] := by
  rw [show D2M8K2.u803 = KTree.node D2M8K2.u799 (nat_lit 1802284) (nat_lit 3829442997) (nat_lit 0) D2M8K2.u802 from rfl, totK_node, atot799, atot802]
  decide +kernel

theorem arows810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u810 = true := by
  rw [show D2M8K2.u810 = KTree.node D2M8K2.u806 (nat_lit 1871768) (nat_lit 3670241035) (nat_lit 0) D2M8K2.u809 from rfl, allE_node, arows806, irow810, arows809]
  all_goals rfl

theorem atot810 : totK PD2M8K2 D2M8K2.u810 = [0, 762597720769, 2834676284545, 2868650265706, 714460205581, 31520323406, 0, 0] := by
  rw [show D2M8K2.u810 = KTree.node D2M8K2.u806 (nat_lit 1871768) (nat_lit 3670241035) (nat_lit 0) D2M8K2.u809 from rfl, totK_node, atot806, atot809]
  decide +kernel

theorem arows818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u818 = true := by
  rw [show D2M8K2.u818 = KTree.node D2M8K2.u814 (nat_lit 1881048) (nat_lit 3420842040) (nat_lit 0) D2M8K2.u817 from rfl, allE_node, arows814, irow818, arows817]
  all_goals rfl

theorem atot818 : totK PD2M8K2 D2M8K2.u818 = [0, 831067673161, 2941072621712, 2802492461847, 569014880184, 18231200220, 0, 0] := by
  rw [show D2M8K2.u818 = KTree.node D2M8K2.u814 (nat_lit 1881048) (nat_lit 3420842040) (nat_lit 0) D2M8K2.u817 from rfl, totK_node, atot814, atot817]
  decide +kernel

theorem arows825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u825 = true := by
  rw [show D2M8K2.u825 = KTree.node D2M8K2.u821 (nat_lit 1888168) (nat_lit 2434895734) (nat_lit 0) D2M8K2.u824 from rfl, allE_node, arows821, irow825, arows824]
  all_goals rfl

theorem atot825 : totK PD2M8K2 D2M8K2.u825 = [0, 92620862180, 1520344266447, 3505175148367, 1771827363567, 160308132829, 1217496766, 0] := by
  rw [show D2M8K2.u825 = KTree.node D2M8K2.u821 (nat_lit 1888168) (nat_lit 2434895734) (nat_lit 0) D2M8K2.u824 from rfl, totK_node, atot821, atot824]
  decide +kernel

theorem arows835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u835 = true := by
  rw [show D2M8K2.u835 = KTree.node D2M8K2.u831 (nat_lit 1900440) (nat_lit 3247267020) (nat_lit 0) D2M8K2.u834 from rfl, allE_node, arows831, irow835, arows834]
  all_goals rfl

theorem atot835 : totK PD2M8K2 D2M8K2.u835 = [0, 0, 868281597874, 3037613788302, 2555525331600, 492286738012, 17736366219, 0] := by
  rw [show D2M8K2.u835 = KTree.node D2M8K2.u831 (nat_lit 1900440) (nat_lit 3247267020) (nat_lit 0) D2M8K2.u834 from rfl, totK_node, atot831, atot834]
  decide +kernel

theorem arows842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u842 = true := by
  rw [show D2M8K2.u842 = KTree.node D2M8K2.u838 (nat_lit 1909277) (nat_lit 1838256299) (nat_lit 0) D2M8K2.u841 from rfl, allE_node, arows838, irow842, arows841]
  all_goals rfl

theorem atot842 : totK PD2M8K2 D2M8K2.u842 = [0, 795078674787, 2903036861692, 2821277500137, 650802281216, 27764663151, 0, 0] := by
  rw [show D2M8K2.u842 = KTree.node D2M8K2.u838 (nat_lit 1909277) (nat_lit 1838256299) (nat_lit 0) D2M8K2.u841 from rfl, totK_node, atot838, atot841]
  decide +kernel

theorem arows850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u850 = true := by
  rw [show D2M8K2.u850 = KTree.node D2M8K2.u846 (nat_lit 1916985) (nat_lit 1836439462) (nat_lit 0) D2M8K2.u849 from rfl, allE_node, arows846, irow850, arows849]
  all_goals rfl

theorem atot850 : totK PD2M8K2 D2M8K2.u850 = [0, 748706122977, 2801318299909, 2898524441763, 705710893437, 25368011527, 0, 0] := by
  rw [show D2M8K2.u850 = KTree.node D2M8K2.u846 (nat_lit 1916985) (nat_lit 1836439462) (nat_lit 0) D2M8K2.u849 from rfl, totK_node, atot846, atot849]
  decide +kernel

theorem arows857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u857 = true := by
  rw [show D2M8K2.u857 = KTree.node D2M8K2.u853 (nat_lit 1923948) (nat_lit 3098270986) (nat_lit 0) D2M8K2.u856 from rfl, allE_node, arows853, irow857, arows856]
  all_goals rfl

theorem atot857 : totK PD2M8K2 D2M8K2.u857 = [0, 435344516724, 2103582644255, 3131410975252, 1264661808414, 99813323252, 1138244013, 0] := by
  rw [show D2M8K2.u857 = KTree.node D2M8K2.u853 (nat_lit 1923948) (nat_lit 3098270986) (nat_lit 0) D2M8K2.u856 from rfl, totK_node, atot853, atot856]
  decide +kernel

theorem arows866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u866 = true := by
  rw [show D2M8K2.u866 = KTree.node D2M8K2.u862 (nat_lit 1939293) (nat_lit 1306876004) (nat_lit 0) D2M8K2.u865 from rfl, allE_node, arows862, irow866, arows865]
  all_goals rfl

theorem atot866 : totK PD2M8K2 D2M8K2.u866 = [0, 0, 1551552905201, 3789939024721, 1645967304035, 88943026891, 0, 0] := by
  rw [show D2M8K2.u866 = KTree.node D2M8K2.u862 (nat_lit 1939293) (nat_lit 1306876004) (nat_lit 0) D2M8K2.u865 from rfl, totK_node, atot862, atot865]
  decide +kernel

theorem arows873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u873 = true := by
  rw [show D2M8K2.u873 = KTree.node D2M8K2.u869 (nat_lit 1951538) (nat_lit 3610500938) (nat_lit 0) D2M8K2.u872 from rfl, allE_node, arows869, irow873, arows872]
  all_goals rfl

theorem atot873 : totK PD2M8K2 D2M8K2.u873 = [0, 798340129520, 2629296271881, 2545827845762, 1005637939725, 166432174223, 4914284239, 0] := by
  rw [show D2M8K2.u873 = KTree.node D2M8K2.u869 (nat_lit 1951538) (nat_lit 3610500938) (nat_lit 0) D2M8K2.u872 from rfl, totK_node, atot869, atot872]
  decide +kernel

theorem arows881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u881 = true := by
  rw [show D2M8K2.u881 = KTree.node D2M8K2.u877 (nat_lit 1958665) (nat_lit 1333963812) (nat_lit 0) D2M8K2.u880 from rfl, allE_node, arows877, irow881, arows880]
  all_goals rfl

theorem atot881 : totK PD2M8K2 D2M8K2.u881 = [0, 752115776599, 2770846194052, 2911130107405, 750940867205, 26912484102, 0, 0] := by
  rw [show D2M8K2.u881 = KTree.node D2M8K2.u877 (nat_lit 1958665) (nat_lit 1333963812) (nat_lit 0) D2M8K2.u880 from rfl, totK_node, atot877, atot880]
  decide +kernel

theorem arows888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u888 = true := by
  rw [show D2M8K2.u888 = KTree.node D2M8K2.u884 (nat_lit 1968980) (nat_lit 1493787405) (nat_lit 0) D2M8K2.u887 from rfl, allE_node, arows884, irow888, arows887]
  all_goals rfl

theorem atot888 : totK PD2M8K2 D2M8K2.u888 = [437191058986, 1708931420098, 2528821646918, 1974927685005, 535296426746, 25501097534, 0, 0] := by
  rw [show D2M8K2.u888 = KTree.node D2M8K2.u884 (nat_lit 1968980) (nat_lit 1493787405) (nat_lit 0) D2M8K2.u887 from rfl, totK_node, atot884, atot887]
  decide +kernel

theorem arows899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u899 = true := by
  rw [show D2M8K2.u899 = KTree.node D2M8K2.u895 (nat_lit 1999999) (nat_lit 1422092992) (nat_lit 0) D2M8K2.u898 from rfl, allE_node, arows895, irow899, arows898]
  all_goals rfl

theorem atot899 : totK PD2M8K2 D2M8K2.u899 = [823661137413, 2994869311863, 2829547955816, 531601206531, 14247800626, 0, 0, 0] := by
  rw [show D2M8K2.u899 = KTree.node D2M8K2.u895 (nat_lit 1999999) (nat_lit 1422092992) (nat_lit 0) D2M8K2.u898 from rfl, totK_node, atot895, atot898]
  decide +kernel

theorem arows906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u906 = true := by
  rw [show D2M8K2.u906 = KTree.node D2M8K2.u902 (nat_lit 2006797) (nat_lit 1274366497) (nat_lit 0) D2M8K2.u905 from rfl, allE_node, arows902, irow906, arows905]
  all_goals rfl

theorem atot906 : totK PD2M8K2 D2M8K2.u906 = [766944076493, 2830014898573, 2881974767926, 676446428313, 23066226746, 0, 0, 0] := by
  rw [show D2M8K2.u906 = KTree.node D2M8K2.u902 (nat_lit 2006797) (nat_lit 1274366497) (nat_lit 0) D2M8K2.u905 from rfl, totK_node, atot902, atot905]
  decide +kernel

theorem arows914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u914 = true := by
  rw [show D2M8K2.u914 = KTree.node D2M8K2.u910 (nat_lit 2014333) (nat_lit 1201939146) (nat_lit 0) D2M8K2.u913 from rfl, allE_node, arows910, irow914, arows913]
  all_goals rfl

theorem atot914 : totK PD2M8K2 D2M8K2.u914 = [0, 1215088995579, 3520352497955, 2127542468814, 221066197655, 1369150432, 0, 0] := by
  rw [show D2M8K2.u914 = KTree.node D2M8K2.u910 (nat_lit 2014333) (nat_lit 1201939146) (nat_lit 0) D2M8K2.u913 from rfl, totK_node, atot910, atot913]
  decide +kernel

theorem arows921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u921 = true := by
  rw [show D2M8K2.u921 = KTree.node D2M8K2.u917 (nat_lit 2029578) (nat_lit 3876098903) (nat_lit 0) D2M8K2.u920 from rfl, allE_node, arows917, irow921, arows920]
  all_goals rfl

theorem atot921 : totK PD2M8K2 D2M8K2.u921 = [430146303138, 2147299193324, 3252548975037, 1327282333451, 80234139465, 0, 0, 0] := by
  rw [show D2M8K2.u921 = KTree.node D2M8K2.u917 (nat_lit 2029578) (nat_lit 3876098903) (nat_lit 0) D2M8K2.u920 from rfl, totK_node, atot917, atot920]
  decide +kernel

theorem arows930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u930 = true := by
  rw [show D2M8K2.u930 = KTree.node D2M8K2.u926 (nat_lit 2040882) (nat_lit 2442420305) (nat_lit 0) D2M8K2.u929 from rfl, allE_node, arows926, irow930, arows929]
  all_goals rfl

theorem atot930 : totK PD2M8K2 D2M8K2.u930 = [805061060087, 2802381878467, 2822135805934, 762705659703, 29245827401, 0, 0, 0] := by
  rw [show D2M8K2.u930 = KTree.node D2M8K2.u926 (nat_lit 2040882) (nat_lit 2442420305) (nat_lit 0) D2M8K2.u929 from rfl, totK_node, atot926, atot929]
  decide +kernel

theorem arows937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u937 = true := by
  rw [show D2M8K2.u937 = KTree.node D2M8K2.u933 (nat_lit 2047733) (nat_lit 2361090294) (nat_lit 0) D2M8K2.u936 from rfl, allE_node, arows933, irow937, arows936]
  all_goals rfl

theorem atot937 : totK PD2M8K2 D2M8K2.u937 = [423909952681, 2279630684414, 3289306421112, 1187380696927, 77210658068, 0, 0, 0] := by
  rw [show D2M8K2.u937 = KTree.node D2M8K2.u933 (nat_lit 2047733) (nat_lit 2361090294) (nat_lit 0) D2M8K2.u936 from rfl, totK_node, atot933, atot936]
  decide +kernel

theorem arows945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u945 = true := by
  rw [show D2M8K2.u945 = KTree.node D2M8K2.u941 (nat_lit 2061169) (nat_lit 1360866032) (nat_lit 0) D2M8K2.u944 from rfl, allE_node, arows941, irow945, arows944]
  all_goals rfl

theorem atot945 : totK PD2M8K2 D2M8K2.u945 = [0, 803196875681, 2753576490156, 2795111862075, 794831164003, 42081742489, 0, 0] := by
  rw [show D2M8K2.u945 = KTree.node D2M8K2.u941 (nat_lit 2061169) (nat_lit 1360866032) (nat_lit 0) D2M8K2.u944 from rfl, totK_node, atot941, atot944]
  decide +kernel

theorem arows952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u952 = true := by
  rw [show D2M8K2.u952 = KTree.node D2M8K2.u948 (nat_lit 2068081) (nat_lit 1405493141) (nat_lit 0) D2M8K2.u951 from rfl, allE_node, arows948, irow952, arows951]
  all_goals rfl

theorem atot952 : totK PD2M8K2 D2M8K2.u952 = [409976030251, 1555332450476, 2632077930698, 2177844181922, 392761120339, 6634014755, 0, 0] := by
  rw [show D2M8K2.u952 = KTree.node D2M8K2.u948 (nat_lit 2068081) (nat_lit 1405493141) (nat_lit 0) D2M8K2.u951 from rfl, totK_node, atot948, atot951]
  decide +kernel

theorem arows962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u962 = true := by
  rw [show D2M8K2.u962 = KTree.node D2M8K2.u958 (nat_lit 2079422) (nat_lit 3915131715) (nat_lit 0) D2M8K2.u961 from rfl, allE_node, arows958, irow962, arows961]
  all_goals rfl

theorem atot962 : totK PD2M8K2 D2M8K2.u962 = [824191994526, 2879551385100, 2786478399701, 726943328816, 37640035450, 0, 0, 0] := by
  rw [show D2M8K2.u962 = KTree.node D2M8K2.u958 (nat_lit 2079422) (nat_lit 3915131715) (nat_lit 0) D2M8K2.u961 from rfl, totK_node, atot958, atot961]
  decide +kernel

theorem arows969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u969 = true := by
  rw [show D2M8K2.u969 = KTree.node D2M8K2.u965 (nat_lit 2088825) (nat_lit 1903903263) (nat_lit 0) D2M8K2.u968 from rfl, allE_node, arows965, irow969, arows968]
  all_goals rfl

theorem atot969 : totK PD2M8K2 D2M8K2.u969 = [751044334138, 2832461961559, 2947227909352, 652200326067, 19298981496, 0, 0, 0] := by
  rw [show D2M8K2.u969 = KTree.node D2M8K2.u965 (nat_lit 2088825) (nat_lit 1903903263) (nat_lit 0) D2M8K2.u968 from rfl, totK_node, atot965, atot968]
  decide +kernel

theorem arows977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u977 = true := by
  rw [show D2M8K2.u977 = KTree.node D2M8K2.u973 (nat_lit 2097032) (nat_lit 3816815635) (nat_lit 0) D2M8K2.u976 from rfl, allE_node, arows973, irow977, arows976]
  all_goals rfl

theorem atot977 : totK PD2M8K2 D2M8K2.u977 = [0, 1255637915411, 3540769233869, 2132734227890, 205616706909, 1206465782, 0, 0] := by
  rw [show D2M8K2.u977 = KTree.node D2M8K2.u973 (nat_lit 2097032) (nat_lit 3816815635) (nat_lit 0) D2M8K2.u976 from rfl, totK_node, atot973, atot976]
  decide +kernel

theorem arows984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u984 = true := by
  rw [show D2M8K2.u984 = KTree.node D2M8K2.u980 (nat_lit 2108881) (nat_lit 1513665335) (nat_lit 0) D2M8K2.u983 from rfl, allE_node, arows980, irow984, arows983]
  all_goals rfl

theorem atot984 : totK PD2M8K2 D2M8K2.u984 = [0, 883235748338, 3057834565789, 2592469591852, 487411610793, 17590593026, 0, 0] := by
  rw [show D2M8K2.u984 = KTree.node D2M8K2.u980 (nat_lit 2108881) (nat_lit 1513665335) (nat_lit 0) D2M8K2.u983 from rfl, totK_node, atot980, atot983]
  decide +kernel

theorem arows993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u993 = true := by
  rw [show D2M8K2.u993 = KTree.node D2M8K2.u989 (nat_lit 2118847) (nat_lit 2341283416) (nat_lit 0) D2M8K2.u992 from rfl, allE_node, arows989, irow993, arows992]
  all_goals rfl

theorem atot993 : totK PD2M8K2 D2M8K2.u993 = [796528290587, 2824673859128, 2788079901923, 772536943433, 45627444008, 0, 0, 0] := by
  rw [show D2M8K2.u993 = KTree.node D2M8K2.u989 (nat_lit 2118847) (nat_lit 2341283416) (nat_lit 0) D2M8K2.u992 from rfl, totK_node, atot989, atot992]
  decide +kernel

theorem arows1000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1000 = true := by
  rw [show D2M8K2.u1000 = KTree.node D2M8K2.u996 (nat_lit 2128372) (nat_lit 3081297887) (nat_lit 0) D2M8K2.u999 from rfl, allE_node, arows996, irow1000, arows999]
  all_goals rfl

theorem atot1000 : totK PD2M8K2 D2M8K2.u1000 = [859929940157, 2982849289355, 2770007347187, 580175496561, 19898593461, 0, 0, 0] := by
  rw [show D2M8K2.u1000 = KTree.node D2M8K2.u996 (nat_lit 2128372) (nat_lit 3081297887) (nat_lit 0) D2M8K2.u999 from rfl, totK_node, atot996, atot999]
  decide +kernel

theorem arows1008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1008 = true := by
  rw [show D2M8K2.u1008 = KTree.node D2M8K2.u1004 (nat_lit 2135864) (nat_lit 3588980262) (nat_lit 0) D2M8K2.u1007 from rfl, allE_node, arows1004, irow1008, arows1007]
  all_goals rfl

theorem atot1008 : totK PD2M8K2 D2M8K2.u1008 = [329265630786, 1796437204690, 3162413468990, 1704446992852, 167383514319, 1239866073, 0, 0] := by
  rw [show D2M8K2.u1008 = KTree.node D2M8K2.u1004 (nat_lit 2135864) (nat_lit 3588980262) (nat_lit 0) D2M8K2.u1007 from rfl, totK_node, atot1004, atot1007]
  decide +kernel

theorem arows1015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1015 = true := by
  rw [show D2M8K2.u1015 = KTree.node D2M8K2.u1011 (nat_lit 2147916) (nat_lit 3547315960) (nat_lit 0) D2M8K2.u1014 from rfl, allE_node, arows1011, irow1015, arows1014]
  all_goals rfl

theorem atot1015 : totK PD2M8K2 D2M8K2.u1015 = [0, 1130829829444, 3340866461728, 2293082140622, 367120686646, 13105450397, 0, 0] := by
  rw [show D2M8K2.u1015 = KTree.node D2M8K2.u1011 (nat_lit 2147916) (nat_lit 3547315960) (nat_lit 0) D2M8K2.u1014 from rfl, totK_node, atot1011, atot1014]
  decide +kernel

theorem arows1029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1029 = true := by
  rw [show D2M8K2.u1029 = KTree.node D2M8K2.u1025 (nat_lit 2157236) (nat_lit 3651056711) (nat_lit 0) D2M8K2.u1028 from rfl, allE_node, arows1025, irow1029, arows1028]
  all_goals rfl

theorem atot1029 : totK PD2M8K2 D2M8K2.u1029 = [595054678973, 2227650996508, 2741244784576, 1384903780958, 201602150328, 4720618446, 0, 0] := by
  rw [show D2M8K2.u1029 = KTree.node D2M8K2.u1025 (nat_lit 2157236) (nat_lit 3651056711) (nat_lit 0) D2M8K2.u1028 from rfl, totK_node, atot1025, atot1028]
  decide +kernel

theorem arows1036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1036 = true := by
  rw [show D2M8K2.u1036 = KTree.node D2M8K2.u1032 (nat_lit 2163775) (nat_lit 2166790736) (nat_lit 0) D2M8K2.u1035 from rfl, allE_node, arows1032, irow1036, arows1035]
  all_goals rfl

theorem atot1036 : totK PD2M8K2 D2M8K2.u1036 = [729899589616, 2652395998757, 2849729428700, 868465142281, 46100071433, 0, 0, 0] := by
  rw [show D2M8K2.u1036 = KTree.node D2M8K2.u1032 (nat_lit 2163775) (nat_lit 2166790736) (nat_lit 0) D2M8K2.u1035 from rfl, totK_node, atot1032, atot1035]
  decide +kernel

theorem arows1044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1044 = true := by
  rw [show D2M8K2.u1044 = KTree.node D2M8K2.u1040 (nat_lit 2170459) (nat_lit 2238214606) (nat_lit 0) D2M8K2.u1043 from rfl, allE_node, arows1040, irow1044, arows1043]
  all_goals rfl

theorem atot1044 : totK PD2M8K2 D2M8K2.u1044 = [777451607106, 2946088276240, 2894082049481, 594355289843, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u1044 = KTree.node D2M8K2.u1040 (nat_lit 2170459) (nat_lit 2238214606) (nat_lit 0) D2M8K2.u1043 from rfl, totK_node, atot1040, atot1043]
  decide +kernel

theorem arows1051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1051 = true := by
  rw [show D2M8K2.u1051 = KTree.node D2M8K2.u1047 (nat_lit 2181363) (nat_lit 3681445855) (nat_lit 0) D2M8K2.u1050 from rfl, allE_node, arows1047, irow1051, arows1050]
  all_goals rfl

theorem atot1051 : totK PD2M8K2 D2M8K2.u1051 = [0, 1266707607593, 3576539604085, 2063285901147, 180046281401, 1138244013, 0, 0] := by
  rw [show D2M8K2.u1051 = KTree.node D2M8K2.u1047 (nat_lit 2181363) (nat_lit 3681445855) (nat_lit 0) D2M8K2.u1050 from rfl, totK_node, atot1047, atot1050]
  decide +kernel

theorem arows1060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1060 = true := by
  rw [show D2M8K2.u1060 = KTree.node D2M8K2.u1056 (nat_lit 2192266) (nat_lit 2708699124) (nat_lit 0) D2M8K2.u1059 from rfl, allE_node, arows1056, irow1060, arows1059]
  all_goals rfl

theorem atot1060 : totK PD2M8K2 D2M8K2.u1060 = [0, 1182576494506, 3468722606004, 2206797486833, 274452416541, 4977114383, 0, 0] := by
  rw [show D2M8K2.u1060 = KTree.node D2M8K2.u1056 (nat_lit 2192266) (nat_lit 2708699124) (nat_lit 0) D2M8K2.u1059 from rfl, totK_node, atot1056, atot1059]
  decide +kernel

theorem arows1067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1067 = true := by
  rw [show D2M8K2.u1067 = KTree.node D2M8K2.u1063 (nat_lit 2248048) (nat_lit 3512545649) (nat_lit 0) D2M8K2.u1066 from rfl, allE_node, arows1063, irow1067, arows1066]
  all_goals rfl

theorem atot1067 : totK PD2M8K2 D2M8K2.u1067 = [0, 862272162826, 3066862209049, 2747095295124, 472407930124, 14352600228, 0, 0] := by
  rw [show D2M8K2.u1067 = KTree.node D2M8K2.u1063 (nat_lit 2248048) (nat_lit 3512545649) (nat_lit 0) D2M8K2.u1066 from rfl, totK_node, atot1063, atot1066]
  decide +kernel

theorem arows1075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1075 = true := by
  rw [show D2M8K2.u1075 = KTree.node D2M8K2.u1071 (nat_lit 2254616) (nat_lit 3651215652) (nat_lit 0) D2M8K2.u1074 from rfl, allE_node, arows1071, irow1075, arows1074]
  all_goals rfl

theorem atot1075 : totK PD2M8K2 D2M8K2.u1075 = [0, 763385201231, 2883937693541, 2886873368927, 592000755206, 19433571662, 0, 0] := by
  rw [show D2M8K2.u1075 = KTree.node D2M8K2.u1071 (nat_lit 2254616) (nat_lit 3651215652) (nat_lit 0) D2M8K2.u1074 from rfl, totK_node, atot1071, atot1074]
  decide +kernel

theorem arows1082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1082 = true := by
  rw [show D2M8K2.u1082 = KTree.node D2M8K2.u1078 (nat_lit 2263204) (nat_lit 3745827875) (nat_lit 0) D2M8K2.u1081 from rfl, allE_node, arows1078, irow1082, arows1081]
  all_goals rfl

theorem atot1082 : totK PD2M8K2 D2M8K2.u1082 = [0, 0, 1560206953457, 3705938317443, 1617898913718, 136692916180, 1209030869, 0] := by
  rw [show D2M8K2.u1082 = KTree.node D2M8K2.u1078 (nat_lit 2263204) (nat_lit 3745827875) (nat_lit 0) D2M8K2.u1081 from rfl, totK_node, atot1078, atot1081]
  decide +kernel

theorem arows1092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1092 = true := by
  rw [show D2M8K2.u1092 = KTree.node D2M8K2.u1088 (nat_lit 2285162) (nat_lit 4204973949) (nat_lit 0) D2M8K2.u1091 from rfl, allE_node, arows1088, irow1092, arows1091]
  all_goals rfl

theorem atot1092 : totK PD2M8K2 D2M8K2.u1092 = [0, 482415798439, 2287729173523, 3217975613795, 1152204216932, 62187767220, 0, 0] := by
  rw [show D2M8K2.u1092 = KTree.node D2M8K2.u1088 (nat_lit 2285162) (nat_lit 4204973949) (nat_lit 0) D2M8K2.u1091 from rfl, totK_node, atot1088, atot1091]
  decide +kernel

theorem arows1099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1099 = true := by
  rw [show D2M8K2.u1099 = KTree.node D2M8K2.u1095 (nat_lit 2291593) (nat_lit 1457085983) (nat_lit 0) D2M8K2.u1098 from rfl, allE_node, arows1095, irow1099, arows1098]
  all_goals rfl

theorem atot1099 : totK PD2M8K2 D2M8K2.u1099 = [0, 858765941289, 3015399328349, 2743931826146, 569407712759, 23913298926, 0, 0] := by
  rw [show D2M8K2.u1099 = KTree.node D2M8K2.u1095 (nat_lit 2291593) (nat_lit 1457085983) (nat_lit 0) D2M8K2.u1098 from rfl, totK_node, atot1095, atot1098]
  decide +kernel

theorem arows1107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1107 = true := by
  rw [show D2M8K2.u1107 = KTree.node D2M8K2.u1103 (nat_lit 2323140) (nat_lit 3249755499) (nat_lit 0) D2M8K2.u1106 from rfl, allE_node, arows1103, irow1107, arows1106]
  all_goals rfl

theorem atot1107 : totK PD2M8K2 D2M8K2.u1107 = [0, 921525634984, 3198812978839, 2713255950273, 384917797615, 5190883085, 0, 0] := by
  rw [show D2M8K2.u1107 = KTree.node D2M8K2.u1103 (nat_lit 2323140) (nat_lit 3249755499) (nat_lit 0) D2M8K2.u1106 from rfl, totK_node, atot1103, atot1106]
  decide +kernel

theorem arows1114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1114 = true := by
  rw [show D2M8K2.u1114 = KTree.node D2M8K2.u1110 (nat_lit 2330029) (nat_lit 1117684301) (nat_lit 0) D2M8K2.u1113 from rfl, allE_node, arows1110, irow1114, arows1113]
  all_goals rfl

theorem atot1114 : totK PD2M8K2 D2M8K2.u1114 = [0, 794339991852, 2856124475350, 2840989505294, 704640689646, 28063716506, 0, 0] := by
  rw [show D2M8K2.u1114 = KTree.node D2M8K2.u1110 (nat_lit 2330029) (nat_lit 1117684301) (nat_lit 0) D2M8K2.u1113 from rfl, totK_node, atot1110, atot1113]
  decide +kernel

theorem arows1123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1123 = true := by
  rw [show D2M8K2.u1123 = KTree.node D2M8K2.u1119 (nat_lit 2340348) (nat_lit 3211026252) (nat_lit 0) D2M8K2.u1122 from rfl, allE_node, arows1119, irow1123, arows1122]
  all_goals rfl

theorem atot1123 : totK PD2M8K2 D2M8K2.u1123 = [0, 937983256565, 3105114931691, 2661221597424, 469212529695, 9861410126, 0, 0] := by
  rw [show D2M8K2.u1123 = KTree.node D2M8K2.u1119 (nat_lit 2340348) (nat_lit 3211026252) (nat_lit 0) D2M8K2.u1122 from rfl, totK_node, atot1119, atot1122]
  decide +kernel

theorem arows1130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1130 = true := by
  rw [show D2M8K2.u1130 = KTree.node D2M8K2.u1126 (nat_lit 2369428) (nat_lit 3994463264) (nat_lit 0) D2M8K2.u1129 from rfl, allE_node, arows1126, irow1130, arows1129]
  all_goals rfl

theorem atot1130 : totK PD2M8K2 D2M8K2.u1130 = [0, 873473036088, 3043466133489, 2778801248683, 556329867143, 16376849850, 0, 0] := by
  rw [show D2M8K2.u1130 = KTree.node D2M8K2.u1126 (nat_lit 2369428) (nat_lit 3994463264) (nat_lit 0) D2M8K2.u1129 from rfl, totK_node, atot1126, atot1129]
  decide +kernel

theorem arows1138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1138 = true := by
  rw [show D2M8K2.u1138 = KTree.node D2M8K2.u1134 (nat_lit 2378958) (nat_lit 4003271712) (nat_lit 0) D2M8K2.u1137 from rfl, allE_node, arows1134, irow1138, arows1137]
  all_goals rfl

theorem atot1138 : totK PD2M8K2 D2M8K2.u1138 = [0, 749002052952, 2866873693266, 2929940766480, 613011924134, 19361296925, 0, 0] := by
  rw [show D2M8K2.u1138 = KTree.node D2M8K2.u1134 (nat_lit 2378958) (nat_lit 4003271712) (nat_lit 0) D2M8K2.u1137 from rfl, totK_node, atot1134, atot1137]
  decide +kernel

theorem arows1145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1145 = true := by
  rw [show D2M8K2.u1145 = KTree.node D2M8K2.u1141 (nat_lit 2407976) (nat_lit 3576313689) (nat_lit 0) D2M8K2.u1144 from rfl, allE_node, arows1141, irow1145, arows1144]
  all_goals rfl

theorem atot1145 : totK PD2M8K2 D2M8K2.u1145 = [0, 818726509270, 2945118295660, 2779273940057, 579200513782, 23368668605, 0, 0] := by
  rw [show D2M8K2.u1145 = KTree.node D2M8K2.u1141 (nat_lit 2407976) (nat_lit 3576313689) (nat_lit 0) D2M8K2.u1144 from rfl, totK_node, atot1141, atot1144]
  decide +kernel

theorem arows1156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1156 = true := by
  rw [show D2M8K2.u1156 = KTree.node D2M8K2.u1152 (nat_lit 2414610) (nat_lit 2165679669) (nat_lit 0) D2M8K2.u1155 from rfl, allE_node, arows1152, irow1156, arows1155]
  all_goals rfl

theorem atot1156 : totK PD2M8K2 D2M8K2.u1156 = [0, 831695990590, 2886528316578, 2780071253240, 603874283807, 19465557061, 0, 0] := by
  rw [show D2M8K2.u1156 = KTree.node D2M8K2.u1152 (nat_lit 2414610) (nat_lit 2165679669) (nat_lit 0) D2M8K2.u1155 from rfl, totK_node, atot1152, atot1155]
  decide +kernel

theorem arows1163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1163 = true := by
  rw [show D2M8K2.u1163 = KTree.node D2M8K2.u1159 (nat_lit 2421202) (nat_lit 2405963571) (nat_lit 0) D2M8K2.u1162 from rfl, allE_node, arows1159, irow1163, arows1162]
  all_goals rfl

theorem atot1163 : totK PD2M8K2 D2M8K2.u1163 = [0, 443323040853, 2237690172706, 3184064069841, 1120359262711, 102137147671, 1138244013, 0] := by
  rw [show D2M8K2.u1163 = KTree.node D2M8K2.u1159 (nat_lit 2421202) (nat_lit 2405963571) (nat_lit 0) D2M8K2.u1162 from rfl, totK_node, atot1159, atot1162]
  decide +kernel

theorem arows1171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1171 = true := by
  rw [show D2M8K2.u1171 = KTree.node D2M8K2.u1167 (nat_lit 2434186) (nat_lit 2613719366) (nat_lit 0) D2M8K2.u1170 from rfl, allE_node, arows1167, irow1171, arows1170]
  all_goals rfl

theorem atot1171 : totK PD2M8K2 D2M8K2.u1171 = [0, 0, 1481137210286, 3749468848200, 1737545761713, 116107079278, 0, 0] := by
  rw [show D2M8K2.u1171 = KTree.node D2M8K2.u1167 (nat_lit 2434186) (nat_lit 2613719366) (nat_lit 0) D2M8K2.u1170 from rfl, totK_node, atot1167, atot1170]
  decide +kernel

theorem arows1178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1178 = true := by
  rw [show D2M8K2.u1178 = KTree.node D2M8K2.u1174 (nat_lit 2489451) (nat_lit 3237741135) (nat_lit 0) D2M8K2.u1177 from rfl, allE_node, arows1174, irow1178, arows1177]
  all_goals rfl

theorem atot1178 : totK PD2M8K2 D2M8K2.u1178 = [751404570366, 2275484782191, 1834063324984, 1112869285117, 978798324946, 206276769067, 4977114383, 0] := by
  rw [show D2M8K2.u1178 = KTree.node D2M8K2.u1174 (nat_lit 2489451) (nat_lit 3237741135) (nat_lit 0) D2M8K2.u1177 from rfl, totK_node, atot1174, atot1177]
  decide +kernel

theorem arows1187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1187 = true := by
  rw [show D2M8K2.u1187 = KTree.node D2M8K2.u1183 (nat_lit 2499897) (nat_lit 1812157702) (nat_lit 0) D2M8K2.u1186 from rfl, allE_node, arows1183, irow1187, arows1186]
  all_goals rfl

theorem atot1187 : totK PD2M8K2 D2M8K2.u1187 = [768692977472, 2849634612897, 2839582156437, 671020584374, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u1187 = KTree.node D2M8K2.u1183 (nat_lit 2499897) (nat_lit 1812157702) (nat_lit 0) D2M8K2.u1186 from rfl, totK_node, atot1183, atot1186]
  decide +kernel

theorem arows1194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1194 = true := by
  rw [show D2M8K2.u1194 = KTree.node D2M8K2.u1190 (nat_lit 2507217) (nat_lit 753930372) (nat_lit 0) D2M8K2.u1193 from rfl, allE_node, arows1190, irow1194, arows1193]
  all_goals rfl

theorem atot1194 : totK PD2M8K2 D2M8K2.u1194 = [503957506805, 2424612647709, 3206181730558, 987939466952, 46113392009, 0, 0, 0] := by
  rw [show D2M8K2.u1194 = KTree.node D2M8K2.u1190 (nat_lit 2507217) (nat_lit 753930372) (nat_lit 0) D2M8K2.u1193 from rfl, totK_node, atot1190, atot1193]
  decide +kernel

theorem arows1202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1202 = true := by
  rw [show D2M8K2.u1202 = KTree.node D2M8K2.u1198 (nat_lit 2517547) (nat_lit 1547152706) (nat_lit 0) D2M8K2.u1201 from rfl, allE_node, arows1198, irow1202, arows1201]
  all_goals rfl

theorem atot1202 : totK PD2M8K2 D2M8K2.u1202 = [0, 1233269138971, 3530891174140, 2122408179205, 216755687950, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1202 = KTree.node D2M8K2.u1198 (nat_lit 2517547) (nat_lit 1547152706) (nat_lit 0) D2M8K2.u1201 from rfl, totK_node, atot1198, atot1201]
  decide +kernel

theorem arows1209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1209 = true := by
  rw [show D2M8K2.u1209 = KTree.node D2M8K2.u1205 (nat_lit 2534350) (nat_lit 3023972472) (nat_lit 0) D2M8K2.u1208 from rfl, allE_node, arows1205, irow1209, arows1208]
  all_goals rfl

theorem atot1209 : totK PD2M8K2 D2M8K2.u1209 = [587208211945, 2333060039261, 3058175319595, 1237084444470, 71238665010, 0, 0, 0] := by
  rw [show D2M8K2.u1209 = KTree.node D2M8K2.u1205 (nat_lit 2534350) (nat_lit 3023972472) (nat_lit 0) D2M8K2.u1208 from rfl, totK_node, atot1205, atot1208]
  decide +kernel

theorem arows1219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1219 = true := by
  rw [show D2M8K2.u1219 = KTree.node D2M8K2.u1215 (nat_lit 2540666) (nat_lit 4109651873) (nat_lit 0) D2M8K2.u1218 from rfl, allE_node, arows1215, irow1219, arows1218]
  all_goals rfl

theorem atot1219 : totK PD2M8K2 D2M8K2.u1219 = [813114664991, 2890056251643, 2852082695928, 664056294821, 26209976466, 0, 0, 0] := by
  rw [show D2M8K2.u1219 = KTree.node D2M8K2.u1215 (nat_lit 2540666) (nat_lit 4109651873) (nat_lit 0) D2M8K2.u1218 from rfl, totK_node, atot1215, atot1218]
  decide +kernel

theorem arows1226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1226 = true := by
  rw [show D2M8K2.u1226 = KTree.node D2M8K2.u1222 (nat_lit 2554443) (nat_lit 3776241721) (nat_lit 0) D2M8K2.u1225 from rfl, allE_node, arows1222, irow1226, arows1225]
  all_goals rfl

theorem atot1226 : totK PD2M8K2 D2M8K2.u1226 = [266108403091, 1591370017853, 2920583694387, 1937199271879, 491892862446, 30397782892, 0, 0] := by
  rw [show D2M8K2.u1226 = KTree.node D2M8K2.u1222 (nat_lit 2554443) (nat_lit 3776241721) (nat_lit 0) D2M8K2.u1225 from rfl, totK_node, atot1222, atot1225]
  decide +kernel

theorem arows1234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1234 = true := by
  rw [show D2M8K2.u1234 = KTree.node D2M8K2.u1230 (nat_lit 2560664) (nat_lit 2899641604) (nat_lit 0) D2M8K2.u1233 from rfl, allE_node, arows1230, irow1234, arows1233]
  all_goals rfl

theorem atot1234 : totK PD2M8K2 D2M8K2.u1234 = [0, 857493462651, 2971570818550, 2769860113632, 588980857331, 16902832282, 0, 0] := by
  rw [show D2M8K2.u1234 = KTree.node D2M8K2.u1230 (nat_lit 2560664) (nat_lit 2899641604) (nat_lit 0) D2M8K2.u1233 from rfl, totK_node, atot1230, atot1233]
  decide +kernel

theorem arows1241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1241 = true := by
  rw [show D2M8K2.u1241 = KTree.node D2M8K2.u1237 (nat_lit 2571286) (nat_lit 3547600099) (nat_lit 0) D2M8K2.u1240 from rfl, allE_node, arows1237, irow1241, arows1240]
  all_goals rfl

theorem atot1241 : totK PD2M8K2 D2M8K2.u1241 = [501701010607, 2010630875109, 2761762054419, 1613695072354, 322772511367, 9302370699, 0, 0] := by
  rw [show D2M8K2.u1241 = KTree.node D2M8K2.u1237 (nat_lit 2571286) (nat_lit 3547600099) (nat_lit 0) D2M8K2.u1240 from rfl, totK_node, atot1237, atot1240]
  decide +kernel

theorem arows1250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1250 = true := by
  rw [show D2M8K2.u1250 = KTree.node D2M8K2.u1246 (nat_lit 2578236) (nat_lit 3251093975) (nat_lit 0) D2M8K2.u1249 from rfl, allE_node, arows1246, irow1250, arows1249]
  all_goals rfl

theorem atot1250 : totK PD2M8K2 D2M8K2.u1250 = [734983927897, 2700560459699, 2874772012317, 866711984609, 49328154309, 0, 0, 0] := by
  rw [show D2M8K2.u1250 = KTree.node D2M8K2.u1246 (nat_lit 2578236) (nat_lit 3251093975) (nat_lit 0) D2M8K2.u1249 from rfl, totK_node, atot1246, atot1249]
  decide +kernel

theorem arows1257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1257 = true := by
  rw [show D2M8K2.u1257 = KTree.node D2M8K2.u1253 (nat_lit 2589003) (nat_lit 3773292463) (nat_lit 0) D2M8K2.u1256 from rfl, allE_node, arows1253, irow1257, arows1256]
  all_goals rfl

theorem atot1257 : totK PD2M8K2 D2M8K2.u1257 = [752708862040, 2821485757738, 2909707620301, 706410935903, 27023453779, 0, 0, 0] := by
  rw [show D2M8K2.u1257 = KTree.node D2M8K2.u1253 (nat_lit 2589003) (nat_lit 3773292463) (nat_lit 0) D2M8K2.u1256 from rfl, totK_node, atot1253, atot1256]
  decide +kernel

theorem arows1265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1265 = true := by
  rw [show D2M8K2.u1265 = KTree.node D2M8K2.u1261 (nat_lit 2596175) (nat_lit 2750918044) (nat_lit 0) D2M8K2.u1264 from rfl, allE_node, arows1261, irow1265, arows1264]
  all_goals rfl

theorem atot1265 : totK PD2M8K2 D2M8K2.u1265 = [0, 1143885115243, 3487664050450, 2281123556257, 232967423063, 2369401571, 0, 0] := by
  rw [show D2M8K2.u1265 = KTree.node D2M8K2.u1261 (nat_lit 2596175) (nat_lit 2750918044) (nat_lit 0) D2M8K2.u1264 from rfl, totK_node, atot1261, atot1264]
  decide +kernel

theorem arows1272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1272 = true := by
  rw [show D2M8K2.u1272 = KTree.node D2M8K2.u1268 (nat_lit 2608231) (nat_lit 1843056442) (nat_lit 0) D2M8K2.u1271 from rfl, allE_node, arows1268, irow1272, arows1271]
  all_goals rfl

theorem atot1272 : totK PD2M8K2 D2M8K2.u1272 = [245750340552, 1305659457583, 2784897401036, 2289388988520, 452489899973, 16427657237, 0, 0] := by
  rw [show D2M8K2.u1272 = KTree.node D2M8K2.u1268 (nat_lit 2608231) (nat_lit 1843056442) (nat_lit 0) D2M8K2.u1271 from rfl, totK_node, atot1268, atot1271]
  decide +kernel

theorem arows1284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1284 = true := by
  rw [show D2M8K2.u1284 = KTree.node D2M8K2.u1280 (nat_lit 2617441) (nat_lit 1328253638) (nat_lit 0) D2M8K2.u1283 from rfl, allE_node, arows1280, irow1284, arows1283]
  all_goals rfl

theorem atot1284 : totK PD2M8K2 D2M8K2.u1284 = [800947606245, 2833190226599, 2843442199545, 748651970518, 37678169206, 0, 0, 0] := by
  rw [show D2M8K2.u1284 = KTree.node D2M8K2.u1280 (nat_lit 2617441) (nat_lit 1328253638) (nat_lit 0) D2M8K2.u1283 from rfl, totK_node, atot1280, atot1283]
  decide +kernel

theorem arows1291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1291 = true := by
  rw [show D2M8K2.u1291 = KTree.node D2M8K2.u1287 (nat_lit 2627440) (nat_lit 2460379158) (nat_lit 0) D2M8K2.u1290 from rfl, allE_node, arows1287, irow1291, arows1290]
  all_goals rfl

theorem atot1291 : totK PD2M8K2 D2M8K2.u1291 = [850290126210, 2997612648725, 2773569613513, 577899810205, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u1291 = KTree.node D2M8K2.u1287 (nat_lit 2627440) (nat_lit 2460379158) (nat_lit 0) D2M8K2.u1290 from rfl, totK_node, atot1287, atot1290]
  decide +kernel

theorem arows1299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1299 = true := by
  rw [show D2M8K2.u1299 = KTree.node D2M8K2.u1295 (nat_lit 2634668) (nat_lit 3682898901) (nat_lit 0) D2M8K2.u1298 from rfl, allE_node, arows1295, irow1299, arows1298]
  all_goals rfl

theorem atot1299 : totK PD2M8K2 D2M8K2.u1299 = [92934196222, 1465706668614, 3471631348630, 1949714754655, 181246911281, 1239866073, 0, 0] := by
  rw [show D2M8K2.u1299 = KTree.node D2M8K2.u1295 (nat_lit 2634668) (nat_lit 3682898901) (nat_lit 0) D2M8K2.u1298 from rfl, totK_node, atot1295, atot1298]
  decide +kernel

theorem arows1306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1306 = true := by
  rw [show D2M8K2.u1306 = KTree.node D2M8K2.u1302 (nat_lit 2646803) (nat_lit 2179530731) (nat_lit 0) D2M8K2.u1305 from rfl, allE_node, arows1302, irow1306, arows1305]
  all_goals rfl

theorem atot1306 : totK PD2M8K2 D2M8K2.u1306 = [0, 880619484442, 3047215157451, 2647833728428, 502963502777, 17826068843, 0, 0] := by
  rw [show D2M8K2.u1306 = KTree.node D2M8K2.u1302 (nat_lit 2646803) (nat_lit 2179530731) (nat_lit 0) D2M8K2.u1305 from rfl, totK_node, atot1302, atot1305]
  decide +kernel

theorem arows1315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1315 = true := by
  rw [show D2M8K2.u1315 = KTree.node D2M8K2.u1311 (nat_lit 2697315) (nat_lit 3317563269) (nat_lit 0) D2M8K2.u1314 from rfl, allE_node, arows1311, irow1315, arows1314]
  all_goals rfl

theorem atot1315 : totK PD2M8K2 D2M8K2.u1315 = [826019128133, 2893234870836, 2751557764754, 740851710640, 46700155415, 0, 0, 0] := by
  rw [show D2M8K2.u1315 = KTree.node D2M8K2.u1311 (nat_lit 2697315) (nat_lit 3317563269) (nat_lit 0) D2M8K2.u1314 from rfl, totK_node, atot1311, atot1314]
  decide +kernel

theorem arows1322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1322 = true := by
  rw [show D2M8K2.u1322 = KTree.node D2M8K2.u1318 (nat_lit 2704063) (nat_lit 2076581861) (nat_lit 0) D2M8K2.u1321 from rfl, allE_node, arows1318, irow1322, arows1321]
  all_goals rfl

theorem atot1322 : totK PD2M8K2 D2M8K2.u1322 = [748737118828, 2671520022096, 2839882896062, 863941315761, 48840500007, 0, 0, 0] := by
  rw [show D2M8K2.u1322 = KTree.node D2M8K2.u1318 (nat_lit 2704063) (nat_lit 2076581861) (nat_lit 0) D2M8K2.u1321 from rfl, totK_node, atot1318, atot1321]
  decide +kernel

theorem arows1330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1330 = true := by
  rw [show D2M8K2.u1330 = KTree.node D2M8K2.u1326 (nat_lit 2713917) (nat_lit 1491364713) (nat_lit 0) D2M8K2.u1329 from rfl, allE_node, arows1326, irow1330, arows1329]
  all_goals rfl

theorem atot1330 : totK PD2M8K2 D2M8K2.u1330 = [537563995491, 2493724079459, 3211663529300, 959108168330, 40601202707, 0, 0, 0] := by
  rw [show D2M8K2.u1330 = KTree.node D2M8K2.u1326 (nat_lit 2713917) (nat_lit 1491364713) (nat_lit 0) D2M8K2.u1329 from rfl, totK_node, atot1326, atot1329]
  decide +kernel

theorem arows1337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1337 = true := by
  rw [show D2M8K2.u1337 = KTree.node D2M8K2.u1333 (nat_lit 2720977) (nat_lit 1090736072) (nat_lit 0) D2M8K2.u1336 from rfl, allE_node, arows1333, irow1337, arows1336]
  all_goals rfl

theorem atot1337 : totK PD2M8K2 D2M8K2.u1337 = [0, 1015903834602, 3308201691735, 2536813998395, 296015480286, 2385942608, 0, 0] := by
  rw [show D2M8K2.u1337 = KTree.node D2M8K2.u1333 (nat_lit 2720977) (nat_lit 1090736072) (nat_lit 0) D2M8K2.u1336 from rfl, totK_node, atot1333, atot1336]
  decide +kernel

theorem arows1347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1347 = true := by
  rw [show D2M8K2.u1347 = KTree.node D2M8K2.u1343 (nat_lit 2729616) (nat_lit 2903882826) (nat_lit 0) D2M8K2.u1346 from rfl, allE_node, arows1343, irow1347, arows1346]
  all_goals rfl

theorem atot1347 : totK PD2M8K2 D2M8K2.u1347 = [0, 862923901879, 3031394992847, 2721950845001, 511669483836, 13547403126, 0, 0] := by
  rw [show D2M8K2.u1347 = KTree.node D2M8K2.u1343 (nat_lit 2729616) (nat_lit 2903882826) (nat_lit 0) D2M8K2.u1346 from rfl, totK_node, atot1343, atot1346]
  decide +kernel

theorem arows1354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1354 = true := by
  rw [show D2M8K2.u1354 = KTree.node D2M8K2.u1350 (nat_lit 2739593) (nat_lit 1615235865) (nat_lit 0) D2M8K2.u1353 from rfl, allE_node, arows1350, irow1354, arows1353]
  all_goals rfl

theorem atot1354 : totK PD2M8K2 D2M8K2.u1354 = [0, 850205376020, 3019469688797, 2755557062179, 543391491684, 19472822999, 0, 0] := by
  rw [show D2M8K2.u1354 = KTree.node D2M8K2.u1350 (nat_lit 2739593) (nat_lit 1615235865) (nat_lit 0) D2M8K2.u1353 from rfl, totK_node, atot1350, atot1353]
  decide +kernel

theorem arows1362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1362 = true := by
  rw [show D2M8K2.u1362 = KTree.node D2M8K2.u1358 (nat_lit 2750360) (nat_lit 3699121871) (nat_lit 0) D2M8K2.u1361 from rfl, allE_node, arows1358, irow1362, arows1361]
  all_goals rfl

theorem atot1362 : totK PD2M8K2 D2M8K2.u1362 = [0, 863050453709, 3080476188275, 2746440629107, 466094326008, 9221790261, 0, 0] := by
  rw [show D2M8K2.u1362 = KTree.node D2M8K2.u1358 (nat_lit 2750360) (nat_lit 3699121871) (nat_lit 0) D2M8K2.u1361 from rfl, totK_node, atot1358, atot1361]
  decide +kernel

theorem arows1369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1369 = true := by
  rw [show D2M8K2.u1369 = KTree.node D2M8K2.u1365 (nat_lit 2757937) (nat_lit 1519155515) (nat_lit 0) D2M8K2.u1368 from rfl, allE_node, arows1365, irow1369, arows1368]
  all_goals rfl

theorem atot1369 : totK PD2M8K2 D2M8K2.u1369 = [0, 314298660944, 1788780705088, 3217015160251, 1584046799479, 149433790519, 1369150432, 0] := by
  rw [show D2M8K2.u1369 = KTree.node D2M8K2.u1365 (nat_lit 2757937) (nat_lit 1519155515) (nat_lit 0) D2M8K2.u1368 from rfl, totK_node, atot1365, atot1368]
  decide +kernel

theorem arows1378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1378 = true := by
  rw [show D2M8K2.u1378 = KTree.node D2M8K2.u1374 (nat_lit 2771795) (nat_lit 2324269531) (nat_lit 0) D2M8K2.u1377 from rfl, allE_node, arows1374, irow1378, arows1377]
  all_goals rfl

theorem atot1378 : totK PD2M8K2 D2M8K2.u1378 = [0, 53299326172, 1575210841734, 3815634757852, 1583058354656, 66285826615, 0, 0] := by
  rw [show D2M8K2.u1378 = KTree.node D2M8K2.u1374 (nat_lit 2771795) (nat_lit 2324269531) (nat_lit 0) D2M8K2.u1377 from rfl, totK_node, atot1374, atot1377]
  decide +kernel

theorem arows1385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1385 = true := by
  rw [show D2M8K2.u1385 = KTree.node D2M8K2.u1381 (nat_lit 2785153) (nat_lit 847829285) (nat_lit 0) D2M8K2.u1384 from rfl, allE_node, arows1381, irow1385, arows1384]
  all_goals rfl

theorem atot1385 : totK PD2M8K2 D2M8K2.u1385 = [0, 776771083370, 2776843649208, 2820381789068, 837279823034, 45378430039, 0, 0] := by
  rw [show D2M8K2.u1385 = KTree.node D2M8K2.u1381 (nat_lit 2785153) (nat_lit 847829285) (nat_lit 0) D2M8K2.u1384 from rfl, totK_node, atot1381, atot1384]
  decide +kernel

theorem arows1393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1393 = true := by
  rw [show D2M8K2.u1393 = KTree.node D2M8K2.u1389 (nat_lit 2791958) (nat_lit 3815407660) (nat_lit 0) D2M8K2.u1392 from rfl, allE_node, arows1389, irow1393, arows1392]
  all_goals rfl

theorem atot1393 : totK PD2M8K2 D2M8K2.u1393 = [0, 831640738716, 2922767819813, 2837651895878, 624984871264, 15272280086, 0, 0] := by
  rw [show D2M8K2.u1393 = KTree.node D2M8K2.u1389 (nat_lit 2791958) (nat_lit 3815407660) (nat_lit 0) D2M8K2.u1392 from rfl, totK_node, atot1389, atot1392]
  decide +kernel

theorem arows1400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1400 = true := by
  rw [show D2M8K2.u1400 = KTree.node D2M8K2.u1396 (nat_lit 2822813) (nat_lit 1631549608) (nat_lit 0) D2M8K2.u1399 from rfl, allE_node, arows1396, irow1400, arows1399]
  all_goals rfl

theorem atot1400 : totK PD2M8K2 D2M8K2.u1400 = [0, 797995087299, 2843063492611, 2777457242083, 741613109326, 43087738991, 0, 0] := by
  rw [show D2M8K2.u1400 = KTree.node D2M8K2.u1396 (nat_lit 2822813) (nat_lit 1631549608) (nat_lit 0) D2M8K2.u1399 from rfl, totK_node, atot1396, atot1399]
  decide +kernel

theorem arows1411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1411 = true := by
  rw [show D2M8K2.u1411 = KTree.node D2M8K2.u1407 (nat_lit 2829344) (nat_lit 3716735052) (nat_lit 0) D2M8K2.u1410 from rfl, allE_node, arows1407, irow1411, arows1410]
  all_goals rfl

theorem atot1411 : totK PD2M8K2 D2M8K2.u1411 = [0, 763390395092, 2855394042687, 2883843376776, 657632679459, 22186165160, 0, 0] := by
  rw [show D2M8K2.u1411 = KTree.node D2M8K2.u1407 (nat_lit 2829344) (nat_lit 3716735052) (nat_lit 0) D2M8K2.u1410 from rfl, totK_node, atot1407, atot1410]
  decide +kernel

theorem arows1418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1418 = true := by
  rw [show D2M8K2.u1418 = KTree.node D2M8K2.u1414 (nat_lit 2840193) (nat_lit 1054556325) (nat_lit 0) D2M8K2.u1417 from rfl, allE_node, arows1414, irow1418, arows1417]
  all_goals rfl

theorem atot1418 : totK PD2M8K2 D2M8K2.u1418 = [0, 425796529102, 1962458714782, 3114500282062, 1456924843913, 115346592053, 1166720416, 0] := by
  rw [show D2M8K2.u1418 = KTree.node D2M8K2.u1414 (nat_lit 2840193) (nat_lit 1054556325) (nat_lit 0) D2M8K2.u1417 from rfl, totK_node, atot1414, atot1417]
  decide +kernel

theorem arows1426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1426 = true := by
  rw [show D2M8K2.u1426 = KTree.node D2M8K2.u1422 (nat_lit 2849522) (nat_lit 3091360922) (nat_lit 0) D2M8K2.u1425 from rfl, allE_node, arows1422, irow1426, arows1425]
  all_goals rfl

theorem atot1426 : totK PD2M8K2 D2M8K2.u1426 = [0, 0, 1337148675150, 3525529486026, 1984964867123, 237206124537, 5134755853, 0] := by
  rw [show D2M8K2.u1426 = KTree.node D2M8K2.u1422 (nat_lit 2849522) (nat_lit 3091360922) (nat_lit 0) D2M8K2.u1425 from rfl, totK_node, atot1422, atot1425]
  decide +kernel

theorem arows1433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1433 = true := by
  rw [show D2M8K2.u1433 = KTree.node D2M8K2.u1429 (nat_lit 2863998) (nat_lit 2852640996) (nat_lit 0) D2M8K2.u1432 from rfl, allE_node, arows1429, irow1433, arows1432]
  all_goals rfl

theorem atot1433 : totK PD2M8K2 D2M8K2.u1433 = [0, 798159910373, 2841966353277, 2778412180233, 762307881255, 45018141573, 0, 0] := by
  rw [show D2M8K2.u1433 = KTree.node D2M8K2.u1429 (nat_lit 2863998) (nat_lit 2852640996) (nat_lit 0) D2M8K2.u1432 from rfl, totK_node, atot1429, atot1432]
  decide +kernel

theorem arows1442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1442 = true := by
  rw [show D2M8K2.u1442 = KTree.node D2M8K2.u1438 (nat_lit 2874011) (nat_lit 2652746937) (nat_lit 0) D2M8K2.u1441 from rfl, allE_node, arows1438, irow1442, arows1441]
  all_goals rfl

theorem atot1442 : totK PD2M8K2 D2M8K2.u1442 = [0, 763714014634, 2807930455008, 2879010508547, 719346898493, 26362348786, 0, 0] := by
  rw [show D2M8K2.u1442 = KTree.node D2M8K2.u1438 (nat_lit 2874011) (nat_lit 2652746937) (nat_lit 0) D2M8K2.u1441 from rfl, totK_node, atot1438, atot1441]
  decide +kernel

theorem arows1449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1449 = true := by
  rw [show D2M8K2.u1449 = KTree.node D2M8K2.u1445 (nat_lit 2881514) (nat_lit 4049560188) (nat_lit 0) D2M8K2.u1448 from rfl, allE_node, arows1445, irow1449, arows1448]
  all_goals rfl

theorem atot1449 : totK PD2M8K2 D2M8K2.u1449 = [0, 425844345751, 1996007143841, 3124472114777, 1411205767655, 110395617750, 1200365979, 0] := by
  rw [show D2M8K2.u1449 = KTree.node D2M8K2.u1445 (nat_lit 2881514) (nat_lit 4049560188) (nat_lit 0) D2M8K2.u1448 from rfl, totK_node, atot1445, atot1448]
  decide +kernel

theorem arows1457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1457 = true := by
  rw [show D2M8K2.u1457 = KTree.node D2M8K2.u1453 (nat_lit 2894263) (nat_lit 1876230518) (nat_lit 0) D2M8K2.u1456 from rfl, allE_node, arows1453, irow1457, arows1456]
  all_goals rfl

theorem atot1457 : totK PD2M8K2 D2M8K2.u1457 = [0, 0, 1343253120289, 3510026296997, 2015345484208, 243640500600, 5163565574, 0] := by
  rw [show D2M8K2.u1457 = KTree.node D2M8K2.u1453 (nat_lit 2894263) (nat_lit 1876230518) (nat_lit 0) D2M8K2.u1456 from rfl, totK_node, atot1453, atot1456]
  decide +kernel

theorem arows1464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1464 = true := by
  rw [show D2M8K2.u1464 = KTree.node D2M8K2.u1460 (nat_lit 2946834) (nat_lit 2606008473) (nat_lit 0) D2M8K2.u1463 from rfl, allE_node, arows1460, irow1464, arows1463]
  all_goals rfl

theorem atot1464 : totK PD2M8K2 D2M8K2.u1464 = [0, 825501190029, 2897098046770, 2742012153370, 711935150767, 43976828047, 0, 0] := by
  rw [show D2M8K2.u1464 = KTree.node D2M8K2.u1460 (nat_lit 2946834) (nat_lit 2606008473) (nat_lit 0) D2M8K2.u1463 from rfl, totK_node, atot1460, atot1463]
  decide +kernel

theorem arows1474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1474 = true := by
  rw [show D2M8K2.u1474 = KTree.node D2M8K2.u1470 (nat_lit 2953285) (nat_lit 1335752211) (nat_lit 0) D2M8K2.u1473 from rfl, allE_node, arows1470, irow1474, arows1473]
  all_goals rfl

theorem atot1474 : totK PD2M8K2 D2M8K2.u1474 = [0, 837485631266, 2855889644313, 2763402436214, 681638218671, 20240857102, 0, 0] := by
  rw [show D2M8K2.u1474 = KTree.node D2M8K2.u1470 (nat_lit 2953285) (nat_lit 1335752211) (nat_lit 0) D2M8K2.u1473 from rfl, totK_node, atot1470, atot1473]
  decide +kernel

theorem arows1481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1481 = true := by
  rw [show D2M8K2.u1481 = KTree.node D2M8K2.u1477 (nat_lit 2963455) (nat_lit 2408648108) (nat_lit 0) D2M8K2.u1480 from rfl, allE_node, arows1477, irow1481, arows1480]
  all_goals rfl

theorem atot1481 : totK PD2M8K2 D2M8K2.u1481 = [0, 447429866516, 2313326235491, 3309478914617, 1030335723586, 41026424422, 0, 0] := by
  rw [show D2M8K2.u1481 = KTree.node D2M8K2.u1477 (nat_lit 2963455) (nat_lit 2408648108) (nat_lit 0) D2M8K2.u1480 from rfl, totK_node, atot1477, atot1480]
  decide +kernel

theorem arows1489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1489 = true := by
  rw [show D2M8K2.u1489 = KTree.node D2M8K2.u1485 (nat_lit 2972268) (nat_lit 3101801540) (nat_lit 0) D2M8K2.u1488 from rfl, allE_node, arows1485, irow1489, arows1488]
  all_goals rfl

theorem atot1489 : totK PD2M8K2 D2M8K2.u1489 = [0, 0, 988810511617, 3241813920707, 2479094541477, 339335451067, 6075545519, 0] := by
  rw [show D2M8K2.u1489 = KTree.node D2M8K2.u1485 (nat_lit 2972268) (nat_lit 3101801540) (nat_lit 0) D2M8K2.u1488 from rfl, totK_node, atot1485, atot1488]
  decide +kernel

theorem arows1496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1496 = true := by
  rw [show D2M8K2.u1496 = KTree.node D2M8K2.u1492 (nat_lit 2983082) (nat_lit 4117642644) (nat_lit 0) D2M8K2.u1495 from rfl, allE_node, arows1492, irow1496, arows1495]
  all_goals rfl

theorem atot1496 : totK PD2M8K2 D2M8K2.u1496 = [0, 92342479873, 957738162469, 2798654246623, 2598317184362, 597213669937, 26589411484, 0] := by
  rw [show D2M8K2.u1496 = KTree.node D2M8K2.u1492 (nat_lit 2983082) (nat_lit 4117642644) (nat_lit 0) D2M8K2.u1495 from rfl, totK_node, atot1492, atot1495]
  decide +kernel

theorem arows1505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1505 = true := by
  rw [show D2M8K2.u1505 = KTree.node D2M8K2.u1501 (nat_lit 2993293) (nat_lit 1013751997) (nat_lit 0) D2M8K2.u1504 from rfl, allE_node, arows1501, irow1505, arows1504]
  all_goals rfl

theorem atot1505 : totK PD2M8K2 D2M8K2.u1505 = [0, 859497563085, 3062473279220, 2781651576217, 504307931686, 14418877666, 0, 0] := by
  rw [show D2M8K2.u1505 = KTree.node D2M8K2.u1501 (nat_lit 2993293) (nat_lit 1013751997) (nat_lit 0) D2M8K2.u1504 from rfl, totK_node, atot1501, atot1504]
  decide +kernel

theorem arows1512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1512 = true := by
  rw [show D2M8K2.u1512 = KTree.node D2M8K2.u1508 (nat_lit 2999957) (nat_lit 2182209232) (nat_lit 0) D2M8K2.u1511 from rfl, allE_node, arows1508, irow1512, arows1511]
  all_goals rfl

theorem atot1512 : totK PD2M8K2 D2M8K2.u1512 = [0, 835637841890, 2952453082328, 2787399688846, 566439378074, 18231200220, 0, 0] := by
  rw [show D2M8K2.u1512 = KTree.node D2M8K2.u1508 (nat_lit 2999957) (nat_lit 2182209232) (nat_lit 0) D2M8K2.u1511 from rfl, totK_node, atot1508, atot1511]
  decide +kernel

theorem arows1520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1520 = true := by
  rw [show D2M8K2.u1520 = KTree.node D2M8K2.u1516 (nat_lit 3006707) (nat_lit 2971816977) (nat_lit 0) D2M8K2.u1519 from rfl, allE_node, arows1516, irow1520, arows1519]
  all_goals rfl

theorem atot1520 : totK PD2M8K2 D2M8K2.u1520 = [0, 334814008584, 1810281521321, 3149339495251, 1626258888904, 186534312951, 1369150432, 0] := by
  rw [show D2M8K2.u1520 = KTree.node D2M8K2.u1516 (nat_lit 3006707) (nat_lit 2971816977) (nat_lit 0) D2M8K2.u1519 from rfl, totK_node, atot1516, atot1519]
  decide +kernel

theorem arows1527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1527 = true := by
  rw [show D2M8K2.u1527 = KTree.node D2M8K2.u1523 (nat_lit 3018608) (nat_lit 3040217018) (nat_lit 0) D2M8K2.u1526 from rfl, allE_node, arows1523, irow1527, arows1526]
  all_goals rfl

theorem atot1527 : totK PD2M8K2 D2M8K2.u1527 = [0, 0, 1483419087430, 3793652994465, 1730291080090, 88990196606, 0, 0] := by
  rw [show D2M8K2.u1527 = KTree.node D2M8K2.u1523 (nat_lit 3018608) (nat_lit 3040217018) (nat_lit 0) D2M8K2.u1526 from rfl, totK_node, atot1523, atot1526]
  decide +kernel

theorem arows1540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1540 = true := by
  rw [show D2M8K2.u1540 = KTree.node D2M8K2.u1536 (nat_lit 3071647) (nat_lit 2337873149) (nat_lit 0) D2M8K2.u1539 from rfl, allE_node, arows1536, irow1540, arows1539]
  all_goals rfl

theorem atot1540 : totK PD2M8K2 D2M8K2.u1540 = [0, 750106935813, 2783637921098, 2877529073162, 763207909502, 29385619827, 0, 0] := by
  rw [show D2M8K2.u1540 = KTree.node D2M8K2.u1536 (nat_lit 3071647) (nat_lit 2337873149) (nat_lit 0) D2M8K2.u1539 from rfl, totK_node, atot1536, atot1539]
  decide +kernel

theorem arows1547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1547 = true := by
  rw [show D2M8K2.u1547 = KTree.node D2M8K2.u1543 (nat_lit 3078962) (nat_lit 3629440685) (nat_lit 0) D2M8K2.u1546 from rfl, allE_node, arows1543, irow1547, arows1546]
  all_goals rfl

theorem atot1547 : totK PD2M8K2 D2M8K2.u1547 = [0, 848718035950, 3002589940566, 2782374652058, 537341239561, 17206798491, 0, 0] := by
  rw [show D2M8K2.u1547 = KTree.node D2M8K2.u1543 (nat_lit 3078962) (nat_lit 3629440685) (nat_lit 0) D2M8K2.u1546 from rfl, totK_node, atot1543, atot1546]
  decide +kernel

theorem arows1555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1555 = true := by
  rw [show D2M8K2.u1555 = KTree.node D2M8K2.u1551 (nat_lit 3089389) (nat_lit 1332509896) (nat_lit 0) D2M8K2.u1554 from rfl, allE_node, arows1551, irow1555, arows1554]
  all_goals rfl

theorem atot1555 : totK PD2M8K2 D2M8K2.u1555 = [0, 414661219762, 1895756305197, 3077843833361, 1564650288179, 142340955508, 1206465782, 0] := by
  rw [show D2M8K2.u1555 = KTree.node D2M8K2.u1551 (nat_lit 3089389) (nat_lit 1332509896) (nat_lit 0) D2M8K2.u1554 from rfl, totK_node, atot1551, atot1554]
  decide +kernel

theorem arows1562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1562 = true := by
  rw [show D2M8K2.u1562 = KTree.node D2M8K2.u1558 (nat_lit 3098234) (nat_lit 3611419029) (nat_lit 0) D2M8K2.u1561 from rfl, allE_node, arows1558, irow1562, arows1561]
  all_goals rfl

theorem atot1562 : totK PD2M8K2 D2M8K2.u1562 = [0, 0, 1171063814041, 3397928357688, 2171948451860, 316342022987, 13016197374, 0] := by
  rw [show D2M8K2.u1562 = KTree.node D2M8K2.u1558 (nat_lit 3098234) (nat_lit 3611419029) (nat_lit 0) D2M8K2.u1561 from rfl, totK_node, atot1558, atot1561]
  decide +kernel

theorem arows1571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1571 = true := by
  rw [show D2M8K2.u1571 = KTree.node D2M8K2.u1567 (nat_lit 3110623) (nat_lit 2387646393) (nat_lit 0) D2M8K2.u1570 from rfl, allE_node, arows1567, irow1571, arows1570]
  all_goals rfl

theorem atot1571 : totK PD2M8K2 D2M8K2.u1571 = [0, 584955793067, 2224867322118, 2832695023488, 1317188403053, 165484956321, 4574395652, 0] := by
  rw [show D2M8K2.u1571 = KTree.node D2M8K2.u1567 (nat_lit 3110623) (nat_lit 2387646393) (nat_lit 0) D2M8K2.u1570 from rfl, totK_node, atot1567, atot1570]
  decide +kernel

theorem arows1578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1578 = true := by
  rw [show D2M8K2.u1578 = KTree.node D2M8K2.u1574 (nat_lit 3121742) (nat_lit 3794609127) (nat_lit 0) D2M8K2.u1577 from rfl, allE_node, arows1574, irow1578, arows1577]
  all_goals rfl

theorem atot1578 : totK PD2M8K2 D2M8K2.u1578 = [0, 767833112348, 2808820078207, 2844044585311, 751750421708, 26970162597, 0, 0] := by
  rw [show D2M8K2.u1578 = KTree.node D2M8K2.u1574 (nat_lit 3121742) (nat_lit 3794609127) (nat_lit 0) D2M8K2.u1577 from rfl, totK_node, atot1574, atot1577]
  decide +kernel

theorem arows1586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1586 = true := by
  rw [show D2M8K2.u1586 = KTree.node D2M8K2.u1582 (nat_lit 3128302) (nat_lit 3948075685) (nat_lit 0) D2M8K2.u1585 from rfl, allE_node, arows1582, irow1586, arows1585]
  all_goals rfl

theorem atot1586 : totK PD2M8K2 D2M8K2.u1586 = [0, 661179783291, 2682370143822, 3027704307819, 762955066195, 28392472652, 0, 0] := by
  rw [show D2M8K2.u1586 = KTree.node D2M8K2.u1582 (nat_lit 3128302) (nat_lit 3948075685) (nat_lit 0) D2M8K2.u1585 from rfl, totK_node, atot1582, atot1585]
  decide +kernel

theorem arows1593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1593 = true := by
  rw [show D2M8K2.u1593 = KTree.node D2M8K2.u1589 (nat_lit 3135916) (nat_lit 2854381456) (nat_lit 0) D2M8K2.u1592 from rfl, allE_node, arows1589, irow1593, arows1592]
  all_goals rfl

theorem atot1593 : totK PD2M8K2 D2M8K2.u1593 = [0, 0, 1023518651871, 3321712674106, 2418373181567, 334534539045, 9422004229, 0] := by
  rw [show D2M8K2.u1593 = KTree.node D2M8K2.u1589 (nat_lit 3135916) (nat_lit 2854381456) (nat_lit 0) D2M8K2.u1592 from rfl, totK_node, atot1589, atot1592]
  decide +kernel

theorem arows1603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1603 = true := by
  rw [show D2M8K2.u1603 = KTree.node D2M8K2.u1599 (nat_lit 3147908) (nat_lit 3364523720) (nat_lit 0) D2M8K2.u1602 from rfl, allE_node, arows1599, irow1603, arows1602]
  all_goals rfl

theorem atot1603 : totK PD2M8K2 D2M8K2.u1603 = [0, 280420785384, 1516617885881, 2965901879853, 1967439395805, 283248444587, 8192806269, 0] := by
  rw [show D2M8K2.u1603 = KTree.node D2M8K2.u1599 (nat_lit 3147908) (nat_lit 3364523720) (nat_lit 0) D2M8K2.u1602 from rfl, totK_node, atot1599, atot1602]
  decide +kernel

theorem arows1610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1610 = true := by
  rw [show D2M8K2.u1610 = KTree.node D2M8K2.u1606 (nat_lit 3156734) (nat_lit 2979313159) (nat_lit 0) D2M8K2.u1609 from rfl, allE_node, arows1606, irow1610, arows1609]
  all_goals rfl

theorem atot1610 : totK PD2M8K2 D2M8K2.u1610 = [0, 875167192469, 3013327955127, 2714271094278, 561274494014, 12095290585, 0, 0] := by
  rw [show D2M8K2.u1610 = KTree.node D2M8K2.u1606 (nat_lit 3156734) (nat_lit 2979313159) (nat_lit 0) D2M8K2.u1609 from rfl, totK_node, atot1606, atot1609]
  decide +kernel

theorem arows1618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1618 = true := by
  rw [show D2M8K2.u1618 = KTree.node D2M8K2.u1614 (nat_lit 3163916) (nat_lit 1532382989) (nat_lit 0) D2M8K2.u1617 from rfl, allE_node, arows1614, irow1618, arows1617]
  all_goals rfl

theorem atot1618 : totK PD2M8K2 D2M8K2.u1618 = [0, 829663135107, 2840924096640, 2783300616436, 660949307138, 26300412495, 0, 0] := by
  rw [show D2M8K2.u1618 = KTree.node D2M8K2.u1614 (nat_lit 3163916) (nat_lit 1532382989) (nat_lit 0) D2M8K2.u1617 from rfl, totK_node, atot1614, atot1617]
  decide +kernel

theorem arows1625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1625 = true := by
  rw [show D2M8K2.u1625 = KTree.node D2M8K2.u1621 (nat_lit 3174204) (nat_lit 3223743056) (nat_lit 0) D2M8K2.u1624 from rfl, allE_node, arows1621, irow1625, arows1624]
  all_goals rfl

theorem atot1625 : totK PD2M8K2 D2M8K2.u1625 = [0, 19228354030, 1503418362041, 3672586108762, 1756659511791, 136267818134, 1138244013, 0] := by
  rw [show D2M8K2.u1625 = KTree.node D2M8K2.u1621 (nat_lit 3174204) (nat_lit 3223743056) (nat_lit 0) D2M8K2.u1624 from rfl, totK_node, atot1621, atot1624]
  decide +kernel

theorem arows1634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1634 = true := by
  rw [show D2M8K2.u1634 = KTree.node D2M8K2.u1630 (nat_lit 3186806) (nat_lit 3982414624) (nat_lit 0) D2M8K2.u1633 from rfl, allE_node, arows1630, irow1634, arows1633]
  all_goals rfl

theorem atot1634 : totK PD2M8K2 D2M8K2.u1634 = [0, 176791677709, 1425185593513, 3241776707107, 1968607922726, 234997498278, 4977114383, 0] := by
  rw [show D2M8K2.u1634 = KTree.node D2M8K2.u1630 (nat_lit 3186806) (nat_lit 3982414624) (nat_lit 0) D2M8K2.u1633 from rfl, totK_node, atot1630, atot1633]
  decide +kernel

theorem arows1641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1641 = true := by
  rw [show D2M8K2.u1641 = KTree.node D2M8K2.u1637 (nat_lit 3197746) (nat_lit 3942439521) (nat_lit 0) D2M8K2.u1640 from rfl, allE_node, arows1637, irow1641, arows1640]
  all_goals rfl

theorem atot1641 : totK PD2M8K2 D2M8K2.u1641 = [0, 838738262740, 2958304888496, 2797140955316, 623380776605, 18295066670, 0, 0] := by
  rw [show D2M8K2.u1641 = KTree.node D2M8K2.u1637 (nat_lit 3197746) (nat_lit 3942439521) (nat_lit 0) D2M8K2.u1640 from rfl, totK_node, atot1637, atot1640]
  decide +kernel

theorem arows1649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1649 = true := by
  rw [show D2M8K2.u1649 = KTree.node D2M8K2.u1645 (nat_lit 3204824) (nat_lit 3833243408) (nat_lit 0) D2M8K2.u1648 from rfl, allE_node, arows1645, irow1649, arows1648]
  all_goals rfl

theorem atot1649 : totK PD2M8K2 D2M8K2.u1649 = [0, 819312581973, 2879907671132, 2813802843961, 649742991781, 26287568203, 0, 0] := by
  rw [show D2M8K2.u1649 = KTree.node D2M8K2.u1645 (nat_lit 3204824) (nat_lit 3833243408) (nat_lit 0) D2M8K2.u1648 from rfl, totK_node, atot1645, atot1648]
  decide +kernel

theorem arows1656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1656 = true := by
  rw [show D2M8K2.u1656 = KTree.node D2M8K2.u1652 (nat_lit 3214807) (nat_lit 1202095766) (nat_lit 0) D2M8K2.u1655 from rfl, allE_node, arows1652, irow1656, arows1655]
  all_goals rfl

theorem atot1656 : totK PD2M8K2 D2M8K2.u1656 = [0, 181674658392, 1623425931110, 3361802610380, 1836119412563, 163981432772, 1310285577, 0] := by
  rw [show D2M8K2.u1656 = KTree.node D2M8K2.u1652 (nat_lit 3214807) (nat_lit 1202095766) (nat_lit 0) D2M8K2.u1655 from rfl, totK_node, atot1652, atot1655]
  decide +kernel

theorem arows1667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1667 = true := by
  rw [show D2M8K2.u1667 = KTree.node D2M8K2.u1663 (nat_lit 3223969) (nat_lit 1399473665) (nat_lit 0) D2M8K2.u1666 from rfl, allE_node, arows1663, irow1667, arows1666]
  all_goals rfl

theorem atot1667 : totK PD2M8K2 D2M8K2.u1667 = [0, 0, 929764328622, 3210492240104, 2529095913636, 383043641512, 9811245038, 0] := by
  rw [show D2M8K2.u1667 = KTree.node D2M8K2.u1663 (nat_lit 3223969) (nat_lit 1399473665) (nat_lit 0) D2M8K2.u1666 from rfl, totK_node, atot1663, atot1666]
  decide +kernel

theorem arows1674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1674 = true := by
  rw [show D2M8K2.u1674 = KTree.node D2M8K2.u1670 (nat_lit 3234612) (nat_lit 3066230812) (nat_lit 0) D2M8K2.u1673 from rfl, allE_node, arows1670, irow1674, arows1673]
  all_goals rfl

theorem atot1674 : totK PD2M8K2 D2M8K2.u1674 = [0, 0, 861709310540, 3025408827135, 2693987623838, 536607160106, 23120318498, 0] := by
  rw [show D2M8K2.u1674 = KTree.node D2M8K2.u1670 (nat_lit 3234612) (nat_lit 3066230812) (nat_lit 0) D2M8K2.u1673 from rfl, totK_node, atot1670, atot1673]
  decide +kernel

theorem arows1682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1682 = true := by
  rw [show D2M8K2.u1682 = KTree.node D2M8K2.u1678 (nat_lit 3244924) (nat_lit 3876337880) (nat_lit 0) D2M8K2.u1681 from rfl, allE_node, arows1678, irow1682, arows1681]
  all_goals rfl

theorem atot1682 : totK PD2M8K2 D2M8K2.u1682 = [0, 0, 828505782136, 2872926205411, 2700444686539, 576176658764, 25984037814, 0] := by
  rw [show D2M8K2.u1682 = KTree.node D2M8K2.u1678 (nat_lit 3244924) (nat_lit 3876337880) (nat_lit 0) D2M8K2.u1681 from rfl, totK_node, atot1678, atot1681]
  decide +kernel

theorem arows1689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1689 = true := by
  rw [show D2M8K2.u1689 = KTree.node D2M8K2.u1685 (nat_lit 3251766) (nat_lit 3579298864) (nat_lit 0) D2M8K2.u1688 from rfl, allE_node, arows1685, irow1689, arows1688]
  all_goals rfl

theorem atot1689 : totK PD2M8K2 D2M8K2.u1689 = [0, 0, 828529054030, 2945363376321, 2732734934099, 503383369776, 13566232556, 0] := by
  rw [show D2M8K2.u1689 = KTree.node D2M8K2.u1685 (nat_lit 3251766) (nat_lit 3579298864) (nat_lit 0) D2M8K2.u1688 from rfl, totK_node, atot1685, atot1688]
  decide +kernel

theorem arows1698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1698 = true := by
  rw [show D2M8K2.u1698 = KTree.node D2M8K2.u1694 (nat_lit 3258843) (nat_lit 2279065536) (nat_lit 0) D2M8K2.u1697 from rfl, allE_node, arows1694, irow1698, arows1697]
  all_goals rfl

theorem atot1698 : totK PD2M8K2 D2M8K2.u1698 = [0, 0, 0, 1271012274896, 3515050330843, 1962437347453, 217112106599, 1369150432] := by
  rw [show D2M8K2.u1698 = KTree.node D2M8K2.u1694 (nat_lit 3258843) (nat_lit 2279065536) (nat_lit 0) D2M8K2.u1697 from rfl, totK_node, atot1694, atot1697]
  decide +kernel

theorem arows1705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1705 = true := by
  rw [show D2M8K2.u1705 = KTree.node D2M8K2.u1701 (nat_lit 3274547) (nat_lit 2978412160) (nat_lit 0) D2M8K2.u1704 from rfl, allE_node, arows1701, irow1705, arows1704]
  all_goals rfl

theorem atot1705 : totK PD2M8K2 D2M8K2.u1705 = [0, 0, 491039836135, 2416873790284, 3161366278406, 933194131784, 50520335698, 0] := by
  rw [show D2M8K2.u1705 = KTree.node D2M8K2.u1701 (nat_lit 3274547) (nat_lit 2978412160) (nat_lit 0) D2M8K2.u1704 from rfl, totK_node, atot1701, atot1704]
  decide +kernel

theorem arows1713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1713 = true := by
  rw [show D2M8K2.u1713 = KTree.node D2M8K2.u1709 (nat_lit 3326472) (nat_lit 3571975699) (nat_lit 0) D2M8K2.u1712 from rfl, allE_node, arows1709, irow1713, arows1712]
  all_goals rfl

theorem atot1713 : totK PD2M8K2 D2M8K2.u1713 = [0, 0, 1097827542700, 3316023629661, 2370191568748, 344896707964, 13049727234, 0] := by
  rw [show D2M8K2.u1713 = KTree.node D2M8K2.u1709 (nat_lit 3326472) (nat_lit 3571975699) (nat_lit 0) D2M8K2.u1712 from rfl, totK_node, atot1709, atot1712]
  decide +kernel

theorem arows1720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1720 = true := by
  rw [show D2M8K2.u1720 = KTree.node D2M8K2.u1716 (nat_lit 3337115) (nat_lit 2858455683) (nat_lit 0) D2M8K2.u1719 from rfl, allE_node, arows1716, irow1720, arows1719]
  all_goals rfl

theorem atot1720 : totK PD2M8K2 D2M8K2.u1720 = [0, 0, 829857565615, 2959218069234, 2724950835986, 550473691416, 19970722096, 0] := by
  rw [show D2M8K2.u1720 = KTree.node D2M8K2.u1716 (nat_lit 3337115) (nat_lit 2858455683) (nat_lit 0) D2M8K2.u1719 from rfl, totK_node, atot1716, atot1719]
  decide +kernel

theorem arows1730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1730 = true := by
  rw [show D2M8K2.u1730 = KTree.node D2M8K2.u1726 (nat_lit 3370693) (nat_lit 1201647414) (nat_lit 0) D2M8K2.u1729 from rfl, allE_node, arows1726, irow1730, arows1729]
  all_goals rfl

theorem atot1730 : totK PD2M8K2 D2M8K2.u1730 = [0, 0, 992997214898, 3224473184770, 2555401784419, 386214438369, 13170675918, 0] := by
  rw [show D2M8K2.u1730 = KTree.node D2M8K2.u1726 (nat_lit 3370693) (nat_lit 1201647414) (nat_lit 0) D2M8K2.u1729 from rfl, totK_node, atot1726, atot1729]
  decide +kernel

theorem arows1737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1737 = true := by
  rw [show D2M8K2.u1737 = KTree.node D2M8K2.u1733 (nat_lit 3377533) (nat_lit 1183270411) (nat_lit 0) D2M8K2.u1736 from rfl, allE_node, arows1733, irow1737, arows1736]
  all_goals rfl

theorem atot1737 : totK PD2M8K2 D2M8K2.u1737 = [0, 0, 923460404049, 3081582240438, 2606877222236, 482162241745, 18632350695, 0] := by
  rw [show D2M8K2.u1737 = KTree.node D2M8K2.u1733 (nat_lit 3377533) (nat_lit 1183270411) (nat_lit 0) D2M8K2.u1736 from rfl, totK_node, atot1733, atot1736]
  decide +kernel

theorem arows1745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1745 = true := by
  rw [show D2M8K2.u1745 = KTree.node D2M8K2.u1741 (nat_lit 3407719) (nat_lit 2216150654) (nat_lit 0) D2M8K2.u1744 from rfl, allE_node, arows1741, irow1745, arows1744]
  all_goals rfl

theorem atot1745 : totK PD2M8K2 D2M8K2.u1745 = [0, 0, 902702270511, 3098007873904, 2609630386190, 440498674572, 14352600228, 0] := by
  rw [show D2M8K2.u1745 = KTree.node D2M8K2.u1741 (nat_lit 3407719) (nat_lit 2216150654) (nat_lit 0) D2M8K2.u1744 from rfl, totK_node, atot1741, atot1744]
  decide +kernel

theorem arows1752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1752 = true := by
  rw [show D2M8K2.u1752 = KTree.node D2M8K2.u1748 (nat_lit 3414849) (nat_lit 1834342295) (nat_lit 0) D2M8K2.u1751 from rfl, allE_node, arows1748, irow1752, arows1751]
  all_goals rfl

theorem atot1752 : totK PD2M8K2 D2M8K2.u1752 = [0, 0, 879421873641, 3072697627100, 2656612321729, 474347359898, 18164832359, 0] := by
  rw [show D2M8K2.u1752 = KTree.node D2M8K2.u1748 (nat_lit 3414849) (nat_lit 1834342295) (nat_lit 0) D2M8K2.u1751 from rfl, totK_node, atot1748, atot1751]
  decide +kernel

theorem arows1761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1761 = true := by
  rw [show D2M8K2.u1761 = KTree.node D2M8K2.u1757 (nat_lit 3446452) (nat_lit 3792735541) (nat_lit 0) D2M8K2.u1760 from rfl, allE_node, arows1757, irow1761, arows1760]
  all_goals rfl

theorem atot1761 : totK PD2M8K2 D2M8K2.u1761 = [0, 0, 1033918047875, 3331351638708, 2507976402178, 307772239116, 2499119547, 0] := by
  rw [show D2M8K2.u1761 = KTree.node D2M8K2.u1757 (nat_lit 3446452) (nat_lit 3792735541) (nat_lit 0) D2M8K2.u1760 from rfl, totK_node, atot1757, atot1760]
  decide +kernel

theorem arows1768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1768 = true := by
  rw [show D2M8K2.u1768 = KTree.node D2M8K2.u1764 (nat_lit 3455529) (nat_lit 1913455844) (nat_lit 0) D2M8K2.u1767 from rfl, allE_node, arows1764, irow1768, arows1767]
  all_goals rfl

theorem atot1768 : totK PD2M8K2 D2M8K2.u1768 = [0, 0, 850695339145, 3053097222712, 2770761570477, 492985139034, 14084704891, 0] := by
  rw [show D2M8K2.u1768 = KTree.node D2M8K2.u1764 (nat_lit 3455529) (nat_lit 1913455844) (nat_lit 0) D2M8K2.u1767 from rfl, totK_node, atot1764, atot1767]
  decide +kernel

theorem arows1776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1776 = true := by
  rw [show D2M8K2.u1776 = KTree.node D2M8K2.u1772 (nat_lit 3984043) (nat_lit 1599916584) (nat_lit 0) D2M8K2.u1775 from rfl, allE_node, arows1772, irow1776, arows1775]
  all_goals rfl

theorem atot1776 : totK PD2M8K2 D2M8K2.u1776 = [0, 862802396972, 2884262386695, 2524979321232, 729928367139, 194030715845, 17014456371, 0] := by
  rw [show D2M8K2.u1776 = KTree.node D2M8K2.u1772 (nat_lit 3984043) (nat_lit 1599916584) (nat_lit 0) D2M8K2.u1775 from rfl, totK_node, atot1772, atot1775]
  decide +kernel

theorem arows1783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1783 = true := by
  rw [show D2M8K2.u1783 = KTree.node D2M8K2.u1779 (nat_lit 3994920) (nat_lit 3497358080) (nat_lit 0) D2M8K2.u1782 from rfl, allE_node, arows1779, irow1783, arows1782]
  all_goals rfl

theorem atot1783 : totK PD2M8K2 D2M8K2.u1783 = [0, 774119938336, 2848892218670, 2834475204869, 622616216915, 21693214350, 0, 0] := by
  rw [show D2M8K2.u1783 = KTree.node D2M8K2.u1779 (nat_lit 3994920) (nat_lit 3497358080) (nat_lit 0) D2M8K2.u1782 from rfl, totK_node, atot1779, atot1782]
  decide +kernel

theorem arows1795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1795 = true := by
  rw [show D2M8K2.u1795 = KTree.node D2M8K2.u1791 (nat_lit 4001853) (nat_lit 870803636) (nat_lit 0) D2M8K2.u1794 from rfl, allE_node, arows1791, irow1795, arows1794]
  all_goals rfl

theorem atot1795 : totK PD2M8K2 D2M8K2.u1795 = [0, 392661349882, 1881066538185, 3058400802949, 1576815997613, 179580293232, 1369150432, 0] := by
  rw [show D2M8K2.u1795 = KTree.node D2M8K2.u1791 (nat_lit 4001853) (nat_lit 870803636) (nat_lit 0) D2M8K2.u1794 from rfl, totK_node, atot1791, atot1794]
  decide +kernel

theorem arows1802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1802 = true := by
  rw [show D2M8K2.u1802 = KTree.node D2M8K2.u1798 (nat_lit 4014029) (nat_lit 1347775788) (nat_lit 2) D2M8K2.u1801 from rfl, allE_node, arows1798, irow1802, arows1801]
  all_goals rfl

theorem atot1802 : totK PD2M8K2 D2M8K2.u1802 = [0, 0, 1496673798130, 3792084694308, 1731942080520, 93078018824, 0, 0] := by
  rw [show D2M8K2.u1802 = KTree.node D2M8K2.u1798 (nat_lit 4014029) (nat_lit 1347775788) (nat_lit 2) D2M8K2.u1801 from rfl, totK_node, atot1798, atot1801]
  decide +kernel

theorem arows1810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1810 = true := by
  rw [show D2M8K2.u1810 = KTree.node D2M8K2.u1806 (nat_lit 4028859) (nat_lit 3765549472) (nat_lit 0) D2M8K2.u1809 from rfl, allE_node, arows1806, irow1810, arows1809]
  all_goals rfl

theorem atot1810 : totK PD2M8K2 D2M8K2.u1810 = [0, 856431462024, 2790829243494, 2713435176696, 856784301830, 52241386291, 0, 0] := by
  rw [show D2M8K2.u1810 = KTree.node D2M8K2.u1806 (nat_lit 4028859) (nat_lit 3765549472) (nat_lit 0) D2M8K2.u1809 from rfl, totK_node, atot1806, atot1809]
  decide +kernel

theorem arows1817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1817 = true := by
  rw [show D2M8K2.u1817 = KTree.node D2M8K2.u1813 (nat_lit 4038578) (nat_lit 3083928954) (nat_lit 0) D2M8K2.u1816 from rfl, allE_node, arows1813, irow1817, arows1816]
  all_goals rfl

theorem atot1817 : totK PD2M8K2 D2M8K2.u1817 = [0, 806122768227, 2938660611504, 2860933007151, 602507480372, 18117759132, 0, 0] := by
  rw [show D2M8K2.u1817 = KTree.node D2M8K2.u1813 (nat_lit 4038578) (nat_lit 3083928954) (nat_lit 0) D2M8K2.u1816 from rfl, totK_node, atot1813, atot1816]
  decide +kernel

theorem arows1826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1826 = true := by
  rw [show D2M8K2.u1826 = KTree.node D2M8K2.u1822 (nat_lit 4050583) (nat_lit 1182760676) (nat_lit 0) D2M8K2.u1825 from rfl, allE_node, arows1822, irow1826, arows1825]
  all_goals rfl

theorem atot1826 : totK PD2M8K2 D2M8K2.u1826 = [0, 0, 1231612313730, 3468348260384, 2228203157321, 285243377549, 5159868635, 0] := by
  rw [show D2M8K2.u1826 = KTree.node D2M8K2.u1822 (nat_lit 4050583) (nat_lit 1182760676) (nat_lit 0) D2M8K2.u1825 from rfl, totK_node, atot1822, atot1825]
  decide +kernel

theorem arows1833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1833 = true := by
  rw [show D2M8K2.u1833 = KTree.node D2M8K2.u1829 (nat_lit 4061484) (nat_lit 2405787796) (nat_lit 0) D2M8K2.u1832 from rfl, allE_node, arows1829, irow1833, arows1832]
  all_goals rfl

theorem atot1833 : totK PD2M8K2 D2M8K2.u1833 = [0, 417704280416, 1906414952728, 3044283750988, 1671024270354, 169683666113, 1415142070, 0] := by
  rw [show D2M8K2.u1833 = KTree.node D2M8K2.u1829 (nat_lit 4061484) (nat_lit 2405787796) (nat_lit 0) D2M8K2.u1832 from rfl, totK_node, atot1829, atot1832]
  decide +kernel

theorem arows1841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1841 = true := by
  rw [show D2M8K2.u1841 = KTree.node D2M8K2.u1837 (nat_lit 4070161) (nat_lit 1367513914) (nat_lit 0) D2M8K2.u1840 from rfl, allE_node, arows1837, irow1841, arows1840]
  all_goals rfl

theorem atot1841 : totK PD2M8K2 D2M8K2.u1841 = [0, 852428766212, 2939171600958, 2749878119058, 681411217602, 31051982411, 0, 0] := by
  rw [show D2M8K2.u1841 = KTree.node D2M8K2.u1837 (nat_lit 4070161) (nat_lit 1367513914) (nat_lit 0) D2M8K2.u1840 from rfl, totK_node, atot1837, atot1840]
  decide +kernel

theorem arows1848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1848 = true := by
  rw [show D2M8K2.u1848 = KTree.node D2M8K2.u1844 (nat_lit 4079492) (nat_lit 3611642318) (nat_lit 0) D2M8K2.u1847 from rfl, allE_node, arows1844, irow1848, arows1847]
  all_goals rfl

theorem atot1848 : totK PD2M8K2 D2M8K2.u1848 = [0, 836963459370, 2945103391397, 2810158272473, 577052281758, 18030242193, 0, 0] := by
  rw [show D2M8K2.u1848 = KTree.node D2M8K2.u1844 (nat_lit 4079492) (nat_lit 3611642318) (nat_lit 0) D2M8K2.u1847 from rfl, totK_node, atot1844, atot1847]
  decide +kernel

theorem arows1858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1858 = true := by
  rw [show D2M8K2.u1858 = KTree.node D2M8K2.u1854 (nat_lit 4086592) (nat_lit 3007148146) (nat_lit 0) D2M8K2.u1857 from rfl, allE_node, arows1854, irow1858, arows1857]
  all_goals rfl

theorem atot1858 : totK PD2M8K2 D2M8K2.u1858 = [0, 0, 1303021762099, 3598809837544, 2012762060493, 174755356357, 1206465782, 0] := by
  rw [show D2M8K2.u1858 = KTree.node D2M8K2.u1854 (nat_lit 4086592) (nat_lit 3007148146) (nat_lit 0) D2M8K2.u1857 from rfl, totK_node, atot1854, atot1857]
  decide +kernel

theorem arows1865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1865 = true := by
  rw [show D2M8K2.u1865 = KTree.node D2M8K2.u1861 (nat_lit 4098901) (nat_lit 1260382205) (nat_lit 0) D2M8K2.u1864 from rfl, allE_node, arows1861, irow1865, arows1864]
  all_goals rfl

theorem atot1865 : totK PD2M8K2 D2M8K2.u1865 = [0, 0, 875462237196, 3068212872853, 2573915327273, 484096529696, 17590593026, 0] := by
  rw [show D2M8K2.u1865 = KTree.node D2M8K2.u1861 (nat_lit 4098901) (nat_lit 1260382205) (nat_lit 0) D2M8K2.u1864 from rfl, totK_node, atot1861, atot1864]
  decide +kernel

theorem arows1873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1873 = true := by
  rw [show D2M8K2.u1873 = KTree.node D2M8K2.u1869 (nat_lit 4148875) (nat_lit 1575873793) (nat_lit 0) D2M8K2.u1872 from rfl, allE_node, arows1869, irow1873, arows1872]
  all_goals rfl

theorem atot1873 : totK PD2M8K2 D2M8K2.u1873 = [0, 795790547778, 2842871815666, 2790734432300, 740939894232, 43734089426, 0, 0] := by
  rw [show D2M8K2.u1873 = KTree.node D2M8K2.u1869 (nat_lit 4148875) (nat_lit 1575873793) (nat_lit 0) D2M8K2.u1872 from rfl, totK_node, atot1869, atot1872]
  decide +kernel

theorem arows1880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1880 = true := by
  rw [show D2M8K2.u1880 = KTree.node D2M8K2.u1876 (nat_lit 4155746) (nat_lit 3946380703) (nat_lit 0) D2M8K2.u1879 from rfl, allE_node, arows1876, irow1880, arows1879]
  all_goals rfl

theorem atot1880 : totK PD2M8K2 D2M8K2.u1880 = [0, 750091096706, 2709821390217, 2822891249573, 840994004771, 37526114190, 0, 0] := by
  rw [show D2M8K2.u1880 = KTree.node D2M8K2.u1876 (nat_lit 4155746) (nat_lit 3946380703) (nat_lit 0) D2M8K2.u1879 from rfl, totK_node, atot1876, atot1879]
  decide +kernel

theorem arows1889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1889 = true := by
  rw [show D2M8K2.u1889 = KTree.node D2M8K2.u1885 (nat_lit 4163081) (nat_lit 1788976002) (nat_lit 0) D2M8K2.u1888 from rfl, allE_node, arows1885, irow1889, arows1888]
  all_goals rfl

theorem atot1889 : totK PD2M8K2 D2M8K2.u1889 = [0, 435809923056, 2191761970849, 3168174032603, 1201491019301, 102861581913, 1138244013, 0] := by
  rw [show D2M8K2.u1889 = KTree.node D2M8K2.u1885 (nat_lit 4163081) (nat_lit 1788976002) (nat_lit 0) D2M8K2.u1888 from rfl, totK_node, atot1885, atot1888]
  decide +kernel

theorem arows1896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1896 = true := by
  rw [show D2M8K2.u1896 = KTree.node D2M8K2.u1892 (nat_lit 4175689) (nat_lit 1382862812) (nat_lit 0) D2M8K2.u1895 from rfl, allE_node, arows1892, irow1896, arows1895]
  all_goals rfl

theorem atot1896 : totK PD2M8K2 D2M8K2.u1896 = [0, 0, 1401619989014, 3756070530502, 1876182416428, 110953376103, 0, 0] := by
  rw [show D2M8K2.u1896 = KTree.node D2M8K2.u1892 (nat_lit 4175689) (nat_lit 1382862812) (nat_lit 0) D2M8K2.u1895 from rfl, totK_node, atot1892, atot1895]
  decide +kernel

theorem arows1904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1904 = true := by
  rw [show D2M8K2.u1904 = KTree.node D2M8K2.u1900 (nat_lit 4189968) (nat_lit 3683708532) (nat_lit 0) D2M8K2.u1903 from rfl, allE_node, arows1900, irow1904, arows1903]
  all_goals rfl

theorem atot1904 : totK PD2M8K2 D2M8K2.u1904 = [0, 799181244681, 2512646941500, 2548434905089, 1110426274989, 184018382634, 4977114383, 0] := by
  rw [show D2M8K2.u1904 = KTree.node D2M8K2.u1900 (nat_lit 4189968) (nat_lit 3683708532) (nat_lit 0) D2M8K2.u1903 from rfl, totK_node, atot1900, atot1903]
  decide +kernel

theorem arows1911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1911 = true := by
  rw [show D2M8K2.u1911 = KTree.node D2M8K2.u1907 (nat_lit 4196801) (nat_lit 2221654230) (nat_lit 0) D2M8K2.u1910 from rfl, allE_node, arows1907, irow1911, arows1910]
  all_goals rfl

theorem atot1911 : totK PD2M8K2 D2M8K2.u1911 = [0, 727305901354, 2703623430913, 2890023772621, 865306973838, 46621909635, 0, 0] := by
  rw [show D2M8K2.u1911 = KTree.node D2M8K2.u1907 (nat_lit 4196801) (nat_lit 2221654230) (nat_lit 0) D2M8K2.u1910 from rfl, totK_node, atot1907, atot1910]
  decide +kernel

theorem arows1922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1922 = true := by
  rw [show D2M8K2.u1922 = KTree.node D2M8K2.u1918 (nat_lit 4207604) (nat_lit 1766839535) (nat_lit 0) D2M8K2.u1921 from rfl, allE_node, arows1918, irow1922, arows1921]
  all_goals rfl

theorem atot1922 : totK PD2M8K2 D2M8K2.u1922 = [0, 463775079688, 2392763137227, 3288806892510, 1013622912956, 37938753836, 0, 0] := by
  rw [show D2M8K2.u1922 = KTree.node D2M8K2.u1918 (nat_lit 4207604) (nat_lit 1766839535) (nat_lit 0) D2M8K2.u1921 from rfl, totK_node, atot1918, atot1921]
  decide +kernel

theorem arows1929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1929 = true := by
  rw [show D2M8K2.u1929 = KTree.node D2M8K2.u1925 (nat_lit 4216410) (nat_lit 3448000644) (nat_lit 0) D2M8K2.u1928 from rfl, allE_node, arows1925, irow1929, arows1928]
  all_goals rfl

theorem atot1929 : totK PD2M8K2 D2M8K2.u1929 = [0, 0, 939592505599, 3212042147292, 2634698313462, 363760047540, 6190125969, 0] := by
  rw [show D2M8K2.u1929 = KTree.node D2M8K2.u1925 (nat_lit 4216410) (nat_lit 3448000644) (nat_lit 0) D2M8K2.u1928 from rfl, totK_node, atot1925, atot1928]
  decide +kernel

theorem arows1937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1937 = true := by
  rw [show D2M8K2.u1937 = KTree.node D2M8K2.u1933 (nat_lit 4228517) (nat_lit 1707935408) (nat_lit 0) D2M8K2.u1936 from rfl, allE_node, arows1933, irow1937, arows1936]
  all_goals rfl

theorem atot1937 : totK PD2M8K2 D2M8K2.u1937 = [0, 437347071871, 1832555070241, 2813765024833, 1807474977919, 327248085543, 13786494048, 0] := by
  rw [show D2M8K2.u1937 = KTree.node D2M8K2.u1933 (nat_lit 4228517) (nat_lit 1707935408) (nat_lit 0) D2M8K2.u1936 from rfl, totK_node, atot1933, atot1936]
  decide +kernel

theorem arows1944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1944 = true := by
  rw [show D2M8K2.u1944 = KTree.node D2M8K2.u1940 (nat_lit 4488395) (nat_lit 2325263571) (nat_lit 0) D2M8K2.u1943 from rfl, allE_node, arows1940, irow1944, arows1943]
  all_goals rfl

theorem atot1944 : totK PD2M8K2 D2M8K2.u1944 = [0, 767718503476, 2926907193054, 2903261292294, 569193971813, 15616951058, 0, 0] := by
  rw [show D2M8K2.u1944 = KTree.node D2M8K2.u1940 (nat_lit 4488395) (nat_lit 2325263571) (nat_lit 0) D2M8K2.u1943 from rfl, totK_node, atot1940, atot1943]
  decide +kernel

theorem arows1953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1953 = true := by
  rw [show D2M8K2.u1953 = KTree.node D2M8K2.u1949 (nat_lit 4495200) (nat_lit 3465352723) (nat_lit 0) D2M8K2.u1952 from rfl, allE_node, arows1949, irow1953, arows1952]
  all_goals rfl

theorem atot1953 : totK PD2M8K2 D2M8K2.u1953 = [0, 824665215328, 2924806268358, 2791110150171, 592062806941, 18301866131, 0, 0] := by
  rw [show D2M8K2.u1953 = KTree.node D2M8K2.u1949 (nat_lit 4495200) (nat_lit 3465352723) (nat_lit 0) D2M8K2.u1952 from rfl, totK_node, atot1949, atot1952]
  decide +kernel

theorem arows1960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1960 = true := by
  rw [show D2M8K2.u1960 = KTree.node D2M8K2.u1956 (nat_lit 4502032) (nat_lit 3397928081) (nat_lit 0) D2M8K2.u1959 from rfl, allE_node, arows1956, irow1960, arows1959]
  all_goals rfl

theorem atot1960 : totK PD2M8K2 D2M8K2.u1960 = [0, 0, 1207061710661, 3536616364809, 2100663623785, 219259173190, 1369150432, 0] := by
  rw [show D2M8K2.u1960 = KTree.node D2M8K2.u1956 (nat_lit 4502032) (nat_lit 3397928081) (nat_lit 0) D2M8K2.u1959 from rfl, totK_node, atot1956, atot1959]
  decide +kernel

theorem arows1968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1968 = true := by
  rw [show D2M8K2.u1968 = KTree.node D2M8K2.u1964 (nat_lit 4517562) (nat_lit 3241835309) (nat_lit 0) D2M8K2.u1967 from rfl, allE_node, arows1964, irow1968, arows1967]
  all_goals rfl

theorem atot1968 : totK PD2M8K2 D2M8K2.u1968 = [0, 430444351521, 2159087417472, 3256653951493, 1277209331570, 65629331401, 0, 0] := by
  rw [show D2M8K2.u1968 = KTree.node D2M8K2.u1964 (nat_lit 4517562) (nat_lit 3241835309) (nat_lit 0) D2M8K2.u1967 from rfl, totK_node, atot1964, atot1967]
  decide +kernel

theorem arows1975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1975 = true := by
  rw [show D2M8K2.u1975 = KTree.node D2M8K2.u1971 (nat_lit 4532221) (nat_lit 1082474456) (nat_lit 0) D2M8K2.u1974 from rfl, allE_node, arows1971, irow1975, arows1974]
  all_goals rfl

theorem atot1975 : totK PD2M8K2 D2M8K2.u1975 = [0, 736092773329, 2651775330487, 2874927331466, 911426747625, 50847068081, 0, 0] := by
  rw [show D2M8K2.u1975 = KTree.node D2M8K2.u1971 (nat_lit 4532221) (nat_lit 1082474456) (nat_lit 0) D2M8K2.u1974 from rfl, totK_node, atot1971, atot1974]
  decide +kernel

theorem arows1985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1985 = true := by
  rw [show D2M8K2.u1985 = KTree.node D2M8K2.u1981 (nat_lit 4539240) (nat_lit 3446605925) (nat_lit 0) D2M8K2.u1984 from rfl, allE_node, arows1981, irow1985, arows1984]
  all_goals rfl

theorem atot1985 : totK PD2M8K2 D2M8K2.u1985 = [0, 496343452152, 2448705541594, 3220442155675, 1034405985781, 56266236126, 0, 0] := by
  rw [show D2M8K2.u1985 = KTree.node D2M8K2.u1981 (nat_lit 4539240) (nat_lit 3446605925) (nat_lit 0) D2M8K2.u1984 from rfl, totK_node, atot1981, atot1984]
  decide +kernel

theorem arows1992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1992 = true := by
  rw [show D2M8K2.u1992 = KTree.node D2M8K2.u1988 (nat_lit 4554504) (nat_lit 3218938003) (nat_lit 0) D2M8K2.u1991 from rfl, allE_node, arows1988, irow1992, arows1991]
  all_goals rfl

theorem atot1992 : totK PD2M8K2 D2M8K2.u1992 = [0, 0, 960589176043, 3273481003478, 2585219305772, 370154051771, 6634014755, 0] := by
  rw [show D2M8K2.u1992 = KTree.node D2M8K2.u1988 (nat_lit 4554504) (nat_lit 3218938003) (nat_lit 0) D2M8K2.u1991 from rfl, totK_node, atot1988, atot1991]
  decide +kernel

theorem arows2000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2000 = true := by
  rw [show D2M8K2.u2000 = KTree.node D2M8K2.u1996 (nat_lit 4604888) (nat_lit 1860349719) (nat_lit 0) D2M8K2.u1999 from rfl, allE_node, arows1996, irow2000, arows1999]
  all_goals rfl

theorem atot2000 : totK PD2M8K2 D2M8K2.u2000 = [0, 824373476909, 2844226526172, 2751030875443, 778709032829, 47356391481, 0, 0] := by
  rw [show D2M8K2.u2000 = KTree.node D2M8K2.u1996 (nat_lit 4604888) (nat_lit 1860349719) (nat_lit 0) D2M8K2.u1999 from rfl, totK_node, atot1996, atot1999]
  decide +kernel

theorem arows2007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2007 = true := by
  rw [show D2M8K2.u2007 = KTree.node D2M8K2.u2003 (nat_lit 4615008) (nat_lit 3540521261) (nat_lit 0) D2M8K2.u2006 from rfl, allE_node, arows2003, irow2007, arows2006]
  all_goals rfl

theorem atot2007 : totK PD2M8K2 D2M8K2.u2007 = [0, 681665369427, 2621767894490, 2959241876744, 906848088652, 44325679150, 0, 0] := by
  rw [show D2M8K2.u2007 = KTree.node D2M8K2.u2003 (nat_lit 4615008) (nat_lit 3540521261) (nat_lit 0) D2M8K2.u2006 from rfl, totK_node, atot2003, atot2006]
  decide +kernel

theorem arows2016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2016 = true := by
  rw [show D2M8K2.u2016 = KTree.node D2M8K2.u2012 (nat_lit 4621583) (nat_lit 2145845470) (nat_lit 0) D2M8K2.u2015 from rfl, allE_node, arows2012, irow2016, arows2015]
  all_goals rfl

theorem atot2016 : totK PD2M8K2 D2M8K2.u2016 = [0, 601477597467, 2616091713973, 3127797332358, 812186534068, 25065853757, 0, 0] := by
  rw [show D2M8K2.u2016 = KTree.node D2M8K2.u2012 (nat_lit 4621583) (nat_lit 2145845470) (nat_lit 0) D2M8K2.u2015 from rfl, totK_node, atot2012, atot2015]
  decide +kernel

theorem arows2023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2023 = true := by
  rw [show D2M8K2.u2023 = KTree.node D2M8K2.u2019 (nat_lit 4628880) (nat_lit 3412284455) (nat_lit 0) D2M8K2.u2022 from rfl, allE_node, arows2019, irow2023, arows2022]
  all_goals rfl

theorem atot2023 : totK PD2M8K2 D2M8K2.u2023 = [0, 0, 1019753300237, 3339228389973, 2496960167513, 296612230452, 2410950632, 0] := by
  rw [show D2M8K2.u2023 = KTree.node D2M8K2.u2019 (nat_lit 4628880) (nat_lit 3412284455) (nat_lit 0) D2M8K2.u2022 from rfl, totK_node, atot2019, atot2022]
  decide +kernel

theorem arows2031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2031 = true := by
  rw [show D2M8K2.u2031 = KTree.node D2M8K2.u2027 (nat_lit 4640623) (nat_lit 2447609201) (nat_lit 0) D2M8K2.u2030 from rfl, allE_node, arows2027, irow2031, arows2030]
  all_goals rfl

theorem atot2031 : totK PD2M8K2 D2M8K2.u2031 = [0, 237504842221, 1366791574159, 2897861877379, 2133448202204, 393020821200, 16654984284, 0] := by
  rw [show D2M8K2.u2031 = KTree.node D2M8K2.u2027 (nat_lit 4640623) (nat_lit 2447609201) (nat_lit 0) D2M8K2.u2030 from rfl, totK_node, atot2027, atot2030]
  decide +kernel

theorem arows2038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2038 = true := by
  rw [show D2M8K2.u2038 = KTree.node D2M8K2.u2034 (nat_lit 4649502) (nat_lit 3869046296) (nat_lit 0) D2M8K2.u2037 from rfl, allE_node, arows2034, irow2038, arows2037]
  all_goals rfl

theorem atot2038 : totK PD2M8K2 D2M8K2.u2038 = [0, 797023815597, 2865862016351, 2786407835075, 724012043827, 34828062381, 0, 0] := by
  rw [show D2M8K2.u2038 = KTree.node D2M8K2.u2034 (nat_lit 4649502) (nat_lit 3869046296) (nat_lit 0) D2M8K2.u2037 from rfl, totK_node, atot2034, atot2037]
  decide +kernel

theorem arows2053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2053 = true := by
  rw [show D2M8K2.u2053 = KTree.node D2M8K2.u2049 (nat_lit 4656677) (nat_lit 1856132906) (nat_lit 0) D2M8K2.u2052 from rfl, allE_node, arows2049, irow2053, arows2052]
  all_goals rfl

theorem atot2053 : totK PD2M8K2 D2M8K2.u2053 = [0, 854632865161, 2888999286540, 2732688409271, 641952193185, 26300412495, 0, 0] := by
  rw [show D2M8K2.u2053 = KTree.node D2M8K2.u2049 (nat_lit 4656677) (nat_lit 1856132906) (nat_lit 0) D2M8K2.u2052 from rfl, totK_node, atot2049, atot2052]
  decide +kernel

theorem arows2060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2060 = true := by
  rw [show D2M8K2.u2060 = KTree.node D2M8K2.u2056 (nat_lit 4666946) (nat_lit 3459911583) (nat_lit 0) D2M8K2.u2059 from rfl, allE_node, arows2056, irow2060, arows2059]
  all_goals rfl

theorem atot2060 : totK PD2M8K2 D2M8K2.u2060 = [0, 92722817510, 1610358798107, 3559171414786, 1710144870066, 141457483142, 1138244013, 0] := by
  rw [show D2M8K2.u2060 = KTree.node D2M8K2.u2056 (nat_lit 4666946) (nat_lit 3459911583) (nat_lit 0) D2M8K2.u2059 from rfl, totK_node, atot2056, atot2059]
  decide +kernel

theorem arows2068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2068 = true := by
  rw [show D2M8K2.u2068 = KTree.node D2M8K2.u2064 (nat_lit 4679621) (nat_lit 2318098327) (nat_lit 0) D2M8K2.u2067 from rfl, allE_node, arows2064, irow2068, arows2067]
  all_goals rfl

theorem atot2068 : totK PD2M8K2 D2M8K2.u2068 = [0, 107685783034, 1347918426861, 3352570857739, 2030740239301, 243184790044, 4977114383, 0] := by
  rw [show D2M8K2.u2068 = KTree.node D2M8K2.u2064 (nat_lit 4679621) (nat_lit 2318098327) (nat_lit 0) D2M8K2.u2067 from rfl, totK_node, atot2064, atot2067]
  decide +kernel

theorem arows2075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2075 = true := by
  rw [show D2M8K2.u2075 = KTree.node D2M8K2.u2071 (nat_lit 4690564) (nat_lit 4051056822) (nat_lit 0) D2M8K2.u2074 from rfl, allE_node, arows2071, irow2075, arows2074]
  all_goals rfl

theorem atot2075 : totK PD2M8K2 D2M8K2.u2075 = [0, 815119476034, 2860063387443, 2806866346126, 734343084300, 35024321715, 0, 0] := by
  rw [show D2M8K2.u2075 = KTree.node D2M8K2.u2071 (nat_lit 4690564) (nat_lit 4051056822) (nat_lit 0) D2M8K2.u2074 from rfl, totK_node, atot2071, atot2074]
  decide +kernel

theorem arows2084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2084 = true := by
  rw [show D2M8K2.u2084 = KTree.node D2M8K2.u2080 (nat_lit 4697824) (nat_lit 1239281945) (nat_lit 0) D2M8K2.u2083 from rfl, allE_node, arows2080, irow2084, arows2083]
  all_goals rfl

theorem atot2084 : totK PD2M8K2 D2M8K2.u2084 = [0, 888235362293, 2996088403267, 2761025603496, 587328522144, 18642615169, 0, 0] := by
  rw [show D2M8K2.u2084 = KTree.node D2M8K2.u2080 (nat_lit 4697824) (nat_lit 1239281945) (nat_lit 0) D2M8K2.u2083 from rfl, totK_node, atot2080, atot2083]
  decide +kernel

theorem arows2091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2091 = true := by
  rw [show D2M8K2.u2091 = KTree.node D2M8K2.u2087 (nat_lit 4707792) (nat_lit 3691793810) (nat_lit 0) D2M8K2.u2090 from rfl, allE_node, arows2087, irow2091, arows2090]
  all_goals rfl

theorem atot2091 : totK PD2M8K2 D2M8K2.u2091 = [0, 182433760473, 1634521277404, 3352931429065, 1830248025218, 172622105493, 1310285577, 0] := by
  rw [show D2M8K2.u2091 = KTree.node D2M8K2.u2087 (nat_lit 4707792) (nat_lit 3691793810) (nat_lit 0) D2M8K2.u2090 from rfl, totK_node, atot2087, atot2090]
  decide +kernel

theorem arows2099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2099 = true := by
  rw [show D2M8K2.u2099 = KTree.node D2M8K2.u2095 (nat_lit 4718475) (nat_lit 3719515635) (nat_lit 0) D2M8K2.u2098 from rfl, allE_node, arows2095, irow2099, arows2098]
  all_goals rfl

theorem atot2099 : totK PD2M8K2 D2M8K2.u2099 = [0, 0, 1187012127611, 3459873116804, 2279168535686, 267109226408, 4931404646, 0] := by
  rw [show D2M8K2.u2099 = KTree.node D2M8K2.u2095 (nat_lit 4718475) (nat_lit 3719515635) (nat_lit 0) D2M8K2.u2098 from rfl, totK_node, atot2095, atot2098]
  decide +kernel

theorem arows2106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2106 = true := by
  rw [show D2M8K2.u2106 = KTree.node D2M8K2.u2102 (nat_lit 4977750) (nat_lit 3839372377) (nat_lit 0) D2M8K2.u2105 from rfl, allE_node, arows2102, irow2106, arows2105]
  all_goals rfl

theorem atot2106 : totK PD2M8K2 D2M8K2.u2106 = [0, 736522448081, 2402801883294, 2494207930283, 1283228779995, 287630672111, 13852303904, 0] := by
  rw [show D2M8K2.u2106 = KTree.node D2M8K2.u2102 (nat_lit 4977750) (nat_lit 3839372377) (nat_lit 0) D2M8K2.u2105 from rfl, totK_node, atot2102, atot2105]
  decide +kernel

theorem arows2116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2116 = true := by
  rw [show D2M8K2.u2116 = KTree.node D2M8K2.u2112 (nat_lit 4988200) (nat_lit 2854230369) (nat_lit 0) D2M8K2.u2115 from rfl, allE_node, arows2112, irow2116, arows2115]
  all_goals rfl

theorem atot2116 : totK PD2M8K2 D2M8K2.u2116 = [0, 766351827921, 2823407430540, 2842414366796, 667433710125, 26300412495, 0, 0] := by
  rw [show D2M8K2.u2116 = KTree.node D2M8K2.u2112 (nat_lit 4988200) (nat_lit 2854230369) (nat_lit 0) D2M8K2.u2115 from rfl, totK_node, atot2112, atot2115]
  decide +kernel

theorem arows2123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2123 = true := by
  rw [show D2M8K2.u2123 = KTree.node D2M8K2.u2119 (nat_lit 4995398) (nat_lit 3524230129) (nat_lit 0) D2M8K2.u2122 from rfl, allE_node, arows2119, irow2123, arows2122]
  all_goals rfl

theorem atot2123 : totK PD2M8K2 D2M8K2.u2123 = [0, 521490138033, 2442999482148, 3161566013912, 955371424957, 46113392009, 0, 0] := by
  rw [show D2M8K2.u2123 = KTree.node D2M8K2.u2119 (nat_lit 4995398) (nat_lit 3524230129) (nat_lit 0) D2M8K2.u2122 from rfl, totK_node, atot2119, atot2122]
  decide +kernel

theorem arows2131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2131 = true := by
  rw [show D2M8K2.u2131 = KTree.node D2M8K2.u2127 (nat_lit 5005876) (nat_lit 3741836149) (nat_lit 0) D2M8K2.u2130 from rfl, allE_node, arows2127, irow2131, arows2130]
  all_goals rfl

theorem atot2131 : totK PD2M8K2 D2M8K2.u2131 = [0, 0, 1236338815856, 3534588080902, 2074818311989, 209688752064, 1369150432, 0] := by
  rw [show D2M8K2.u2131 = KTree.node D2M8K2.u2127 (nat_lit 5005876) (nat_lit 3741836149) (nat_lit 0) D2M8K2.u2130 from rfl, totK_node, atot2127, atot2130]
  decide +kernel

theorem arows2138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2138 = true := by
  rw [show D2M8K2.u2138 = KTree.node D2M8K2.u2134 (nat_lit 5022703) (nat_lit 2344612426) (nat_lit 0) D2M8K2.u2137 from rfl, allE_node, arows2134, irow2138, arows2137]
  all_goals rfl

theorem atot2138 : totK PD2M8K2 D2M8K2.u2138 = [0, 586310880811, 2335651363496, 3047114343129, 1197847124548, 72720769527, 0, 0] := by
  rw [show D2M8K2.u2138 = KTree.node D2M8K2.u2134 (nat_lit 5022703) (nat_lit 2344612426) (nat_lit 0) D2M8K2.u2137 from rfl, totK_node, atot2134, atot2137]
  decide +kernel

theorem arows2147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2147 = true := by
  rw [show D2M8K2.u2147 = KTree.node D2M8K2.u2143 (nat_lit 5029014) (nat_lit 3800201112) (nat_lit 0) D2M8K2.u2146 from rfl, allE_node, arows2143, irow2147, arows2146]
  all_goals rfl

theorem atot2147 : totK PD2M8K2 D2M8K2.u2147 = [0, 809437163613, 2873348831918, 2812793303602, 663693578579, 26274535774, 0, 0] := by
  rw [show D2M8K2.u2147 = KTree.node D2M8K2.u2143 (nat_lit 5029014) (nat_lit 3800201112) (nat_lit 0) D2M8K2.u2146 from rfl, totK_node, atot2143, atot2146]
  decide +kernel

theorem arows2154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2154 = true := by
  rw [show D2M8K2.u2154 = KTree.node D2M8K2.u2150 (nat_lit 5043056) (nat_lit 3670958530) (nat_lit 0) D2M8K2.u2153 from rfl, allE_node, arows2150, irow2154, arows2153]
  all_goals rfl

theorem atot2154 : totK PD2M8K2 D2M8K2.u2154 = [0, 263369271482, 2044584491435, 3498198560807, 1354100319630, 78837358356, 0, 0] := by
  rw [show D2M8K2.u2154 = KTree.node D2M8K2.u2150 (nat_lit 5043056) (nat_lit 3670958530) (nat_lit 0) D2M8K2.u2153 from rfl, totK_node, atot2150, atot2153]
  decide +kernel

theorem arows2162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2162 = true := by
  rw [show D2M8K2.u2162 = KTree.node D2M8K2.u2158 (nat_lit 5054024) (nat_lit 3786099746) (nat_lit 0) D2M8K2.u2161 from rfl, allE_node, arows2158, irow2162, arows2161]
  all_goals rfl

theorem atot2162 : totK PD2M8K2 D2M8K2.u2162 = [0, 409976030251, 1868885032513, 3001970032703, 1699938959423, 190236898263, 1415142070, 0] := by
  rw [show D2M8K2.u2162 = KTree.node D2M8K2.u2158 (nat_lit 5054024) (nat_lit 3786099746) (nat_lit 0) D2M8K2.u2161 from rfl, totK_node, atot2158, atot2161]
  decide +kernel

theorem arows2169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2169 = true := by
  rw [show D2M8K2.u2169 = KTree.node D2M8K2.u2165 (nat_lit 5065440) (nat_lit 3176882508) (nat_lit 0) D2M8K2.u2168 from rfl, allE_node, arows2165, irow2169, arows2168]
  all_goals rfl

theorem atot2169 : totK PD2M8K2 D2M8K2.u2169 = [0, 824191994526, 2881301456163, 2785000969865, 716868432488, 34857115928, 0, 0] := by
  rw [show D2M8K2.u2169 = KTree.node D2M8K2.u2165 (nat_lit 5065440) (nat_lit 3176882508) (nat_lit 0) D2M8K2.u2168 from rfl, totK_node, atot2165, atot2168]
  decide +kernel

theorem arows2180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2180 = true := by
  rw [show D2M8K2.u2180 = KTree.node D2M8K2.u2176 (nat_lit 5074820) (nat_lit 3611642318) (nat_lit 0) D2M8K2.u2179 from rfl, allE_node, arows2176, irow2180, arows2179]
  all_goals rfl

theorem atot2180 : totK PD2M8K2 D2M8K2.u2180 = [0, 751044334138, 2863514777213, 2920708525353, 639444625078, 19298981496, 0, 0] := by
  rw [show D2M8K2.u2180 = KTree.node D2M8K2.u2176 (nat_lit 5074820) (nat_lit 3611642318) (nat_lit 0) D2M8K2.u2179 from rfl, totK_node, atot2176, atot2179]
  decide +kernel

theorem arows2187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2187 = true := by
  rw [show D2M8K2.u2187 = KTree.node D2M8K2.u2183 (nat_lit 5083233) (nat_lit 1828819198) (nat_lit 0) D2M8K2.u2186 from rfl, allE_node, arows2183, irow2187, arows2186]
  all_goals rfl

theorem atot2187 : totK PD2M8K2 D2M8K2.u2187 = [0, 0, 1280515922462, 3599974829179, 2053700150037, 177728264894, 1206465782, 0] := by
  rw [show D2M8K2.u2187 = KTree.node D2M8K2.u2183 (nat_lit 5083233) (nat_lit 1828819198) (nat_lit 0) D2M8K2.u2186 from rfl, totK_node, atot2183, atot2186]
  decide +kernel

theorem arows2195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2195 = true := by
  rw [show D2M8K2.u2195 = KTree.node D2M8K2.u2191 (nat_lit 5095082) (nat_lit 4005159470) (nat_lit 0) D2M8K2.u2194 from rfl, allE_node, arows2191, irow2195, arows2194]
  all_goals rfl

theorem atot2195 : totK PD2M8K2 D2M8K2.u2195 = [0, 28547172183, 897034363927, 3072141848273, 2530443275766, 459053833387, 17590593026, 0] := by
  rw [show D2M8K2.u2195 = KTree.node D2M8K2.u2191 (nat_lit 5095082) (nat_lit 4005159470) (nat_lit 0) D2M8K2.u2194 from rfl, totK_node, atot2191, atot2194]
  decide +kernel

theorem arows2202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2202 = true := by
  rw [show D2M8K2.u2202 = KTree.node D2M8K2.u2198 (nat_lit 5105025) (nat_lit 1806052559) (nat_lit 0) D2M8K2.u2201 from rfl, allE_node, arows2198, irow2202, arows2201]
  all_goals rfl

theorem atot2202 : totK PD2M8K2 D2M8K2.u2202 = [0, 814852301459, 2851388847185, 2780242681213, 727153472637, 34826615594, 0, 0] := by
  rw [show D2M8K2.u2202 = KTree.node D2M8K2.u2198 (nat_lit 5105025) (nat_lit 1806052559) (nat_lit 0) D2M8K2.u2201 from rfl, totK_node, atot2198, atot2201]
  decide +kernel

theorem arows2211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2211 = true := by
  rw [show D2M8K2.u2211 = KTree.node D2M8K2.u2207 (nat_lit 5114634) (nat_lit 3843874073) (nat_lit 0) D2M8K2.u2210 from rfl, allE_node, arows2207, irow2211, arows2210]
  all_goals rfl

theorem atot2211 : totK PD2M8K2 D2M8K2.u2211 = [0, 809469776840, 2990037650300, 2836330699448, 553346480750, 15416603213, 0, 0] := by
  rw [show D2M8K2.u2211 = KTree.node D2M8K2.u2207 (nat_lit 5114634) (nat_lit 3843874073) (nat_lit 0) D2M8K2.u2210 from rfl, totK_node, atot2207, atot2210]
  decide +kernel

theorem arows2218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2218 = true := by
  rw [show D2M8K2.u2218 = KTree.node D2M8K2.u2214 (nat_lit 5122473) (nat_lit 1885029635) (nat_lit 0) D2M8K2.u2217 from rfl, allE_node, arows2214, irow2218, arows2217]
  all_goals rfl

theorem atot2218 : totK PD2M8K2 D2M8K2.u2218 = [0, 329265630786, 1813384538158, 3187048821983, 1662566869607, 151595263250, 1239866073, 0] := by
  rw [show D2M8K2.u2218 = KTree.node D2M8K2.u2214 (nat_lit 5122473) (nat_lit 1885029635) (nat_lit 0) D2M8K2.u2217 from rfl, totK_node, atot2214, atot2217]
  decide +kernel

theorem arows2226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2226 = true := by
  rw [show D2M8K2.u2226 = KTree.node D2M8K2.u2222 (nat_lit 5134826) (nat_lit 4048820919) (nat_lit 0) D2M8K2.u2225 from rfl, allE_node, arows2222, irow2226, arows2225]
  all_goals rfl

theorem atot2226 : totK PD2M8K2 D2M8K2.u2226 = [0, 0, 1007576386292, 3265883322581, 2394378538118, 389012977932, 14158861562, 0] := by
  rw [show D2M8K2.u2226 = KTree.node D2M8K2.u2222 (nat_lit 5134826) (nat_lit 4048820919) (nat_lit 0) D2M8K2.u2225 from rfl, totK_node, atot2222, atot2225]
  decide +kernel

theorem arows2233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2233 = true := by
  rw [show D2M8K2.u2233 = KTree.node D2M8K2.u2229 (nat_lit 5143733) (nat_lit 2373749623) (nat_lit 0) D2M8K2.u2232 from rfl, allE_node, arows2229, irow2233, arows2232]
  all_goals rfl

theorem atot2233 : totK PD2M8K2 D2M8K2.u2233 = [0, 769924568502, 2634055265990, 2702099554614, 960521935824, 115131276287, 3667207281, 0] := by
  rw [show D2M8K2.u2233 = KTree.node D2M8K2.u2229 (nat_lit 5143733) (nat_lit 2373749623) (nat_lit 0) D2M8K2.u2232 from rfl, totK_node, atot2229, atot2232]
  decide +kernel

theorem arows2243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2243 = true := by
  rw [show D2M8K2.u2243 = KTree.node D2M8K2.u2239 (nat_lit 5150195) (nat_lit 2663603526) (nat_lit 0) D2M8K2.u2242 from rfl, allE_node, arows2239, irow2243, arows2242]
  all_goals rfl

theorem atot2243 : totK PD2M8K2 D2M8K2.u2243 = [0, 715399962469, 2649901002907, 2867942111943, 873427802985, 43786957124, 0, 0] := by
  rw [show D2M8K2.u2243 = KTree.node D2M8K2.u2239 (nat_lit 5150195) (nat_lit 2663603526) (nat_lit 0) D2M8K2.u2242 from rfl, totK_node, atot2239, atot2242]
  decide +kernel

theorem arows2250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2250 = true := by
  rw [show D2M8K2.u2250 = KTree.node D2M8K2.u2246 (nat_lit 5156957) (nat_lit 2324370134) (nat_lit 0) D2M8K2.u2249 from rfl, allE_node, arows2246, irow2250, arows2249]
  all_goals rfl

theorem atot2250 : totK PD2M8K2 D2M8K2.u2250 = [0, 617081344724, 2695392172299, 3094108016164, 757298896441, 27971341204, 0, 0] := by
  rw [show D2M8K2.u2250 = KTree.node D2M8K2.u2246 (nat_lit 5156957) (nat_lit 2324370134) (nat_lit 0) D2M8K2.u2249 from rfl, totK_node, atot2246, atot2249]
  decide +kernel

theorem arows2258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2258 = true := by
  rw [show D2M8K2.u2258 = KTree.node D2M8K2.u2254 (nat_lit 5167915) (nat_lit 1805480763) (nat_lit 0) D2M8K2.u2257 from rfl, allE_node, arows2254, irow2258, arows2257]
  all_goals rfl

theorem atot2258 : totK PD2M8K2 D2M8K2.u2258 = [0, 0, 1282533839642, 3611035705036, 2014529080176, 172200763276, 1138244013, 0] := by
  rw [show D2M8K2.u2258 = KTree.node D2M8K2.u2254 (nat_lit 5167915) (nat_lit 1805480763) (nat_lit 0) D2M8K2.u2257 from rfl, totK_node, atot2254, atot2257]
  decide +kernel

theorem arows2265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2265 = true := by
  rw [show D2M8K2.u2265 = KTree.node D2M8K2.u2261 (nat_lit 5179168) (nat_lit 3523873900) (nat_lit 0) D2M8K2.u2264 from rfl, allE_node, arows2261, irow2265, arows2264]
  all_goals rfl

theorem atot2265 : totK PD2M8K2 D2M8K2.u2265 = [0, 437509666450, 1870550750794, 2897258443529, 1679884954879, 242369250239, 4977114383, 0] := by
  rw [show D2M8K2.u2265 = KTree.node D2M8K2.u2261 (nat_lit 5179168) (nat_lit 3523873900) (nat_lit 0) D2M8K2.u2264 from rfl, totK_node, atot2261, atot2264]
  decide +kernel

theorem arows2274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2274 = true := by
  rw [show D2M8K2.u2274 = KTree.node D2M8K2.u2270 (nat_lit 5483620) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u2273 from rfl, allE_node, arows2270, irow2274, arows2273]
  all_goals rfl

theorem atot2274 : totK PD2M8K2 D2M8K2.u2274 = [0, 825619672458, 2994646873374, 2818277983620, 527323797679, 14247800626, 0, 0] := by
  rw [show D2M8K2.u2274 = KTree.node D2M8K2.u2270 (nat_lit 5483620) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u2273 from rfl, totK_node, atot2270, atot2273]
  decide +kernel

theorem arows2281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2281 = true := by
  rw [show D2M8K2.u2281 = KTree.node D2M8K2.u2277 (nat_lit 5491102) (nat_lit 2521634846) (nat_lit 0) D2M8K2.u2280 from rfl, allE_node, arows2277, irow2281, arows2280]
  all_goals rfl

theorem atot2281 : totK PD2M8K2 D2M8K2.u2281 = [0, 768488766912, 2849121871284, 2859065445362, 652018908072, 22001122845, 0, 0] := by
  rw [show D2M8K2.u2281 = KTree.node D2M8K2.u2277 (nat_lit 5491102) (nat_lit 2521634846) (nat_lit 0) D2M8K2.u2280 from rfl, totK_node, atot2277, atot2280]
  decide +kernel

theorem arows2289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2289 = true := by
  rw [show D2M8K2.u2289 = KTree.node D2M8K2.u2285 (nat_lit 5497929) (nat_lit 1853830114) (nat_lit 0) D2M8K2.u2288 from rfl, allE_node, arows2285, irow2289, arows2288]
  all_goals rfl

theorem atot2289 : totK PD2M8K2 D2M8K2.u2289 = [0, 0, 1207337020889, 3539393278690, 2115689526562, 216903331411, 1369150432, 0] := by
  rw [show D2M8K2.u2289 = KTree.node D2M8K2.u2285 (nat_lit 5497929) (nat_lit 1853830114) (nat_lit 0) D2M8K2.u2288 from rfl, totK_node, atot2285, atot2288]
  decide +kernel

theorem arows2296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2296 = true := by
  rw [show D2M8K2.u2296 = KTree.node D2M8K2.u2292 (nat_lit 5513192) (nat_lit 3200377769) (nat_lit 0) D2M8K2.u2295 from rfl, allE_node, arows2292, irow2296, arows2295]
  all_goals rfl

theorem atot2296 : totK PD2M8K2 D2M8K2.u2296 = [0, 430753227105, 2134108383526, 3221737220788, 1335027061829, 85856065079, 0, 0] := by
  rw [show D2M8K2.u2296 = KTree.node D2M8K2.u2292 (nat_lit 5513192) (nat_lit 3200377769) (nat_lit 0) D2M8K2.u2295 from rfl, totK_node, atot2292, atot2295]
  decide +kernel

theorem arows2308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2308 = true := by
  rw [show D2M8K2.u2308 = KTree.node D2M8K2.u2304 (nat_lit 5524465) (nat_lit 1509828865) (nat_lit 0) D2M8K2.u2307 from rfl, allE_node, arows2304, irow2308, arows2307]
  all_goals rfl

theorem atot2308 : totK PD2M8K2 D2M8K2.u2308 = [0, 807331588409, 2824092950449, 2838554770471, 752003567812, 25688786674, 0, 0] := by
  rw [show D2M8K2.u2308 = KTree.node D2M8K2.u2304 (nat_lit 5524465) (nat_lit 1509828865) (nat_lit 0) D2M8K2.u2307 from rfl, totK_node, atot2304, atot2307]
  decide +kernel

theorem arows2315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2315 = true := by
  rw [show D2M8K2.u2315 = KTree.node D2M8K2.u2311 (nat_lit 5534790) (nat_lit 3736644362) (nat_lit 0) D2M8K2.u2314 from rfl, allE_node, arows2311, irow2315, arows2314]
  all_goals rfl

theorem atot2315 : totK PD2M8K2 D2M8K2.u2315 = [0, 428346464513, 2262048879784, 3303703375723, 1196587836595, 66195348617, 0, 0] := by
  rw [show D2M8K2.u2315 = KTree.node D2M8K2.u2311 (nat_lit 5534790) (nat_lit 3736644362) (nat_lit 0) D2M8K2.u2314 from rfl, totK_node, atot2311, atot2314]
  decide +kernel

theorem arows2323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2323 = true := by
  rw [show D2M8K2.u2323 = KTree.node D2M8K2.u2319 (nat_lit 5546996) (nat_lit 3476458756) (nat_lit 0) D2M8K2.u2322 from rfl, allE_node, arows2319, irow2323, arows2322]
  all_goals rfl

theorem atot2323 : totK PD2M8K2 D2M8K2.u2323 = [0, 0, 1022374255524, 3373922352948, 2541804597010, 333179850522, 3105414885, 0] := by
  rw [show D2M8K2.u2323 = KTree.node D2M8K2.u2319 (nat_lit 5546996) (nat_lit 3476458756) (nat_lit 0) D2M8K2.u2322 from rfl, totK_node, atot2319, atot2322]
  decide +kernel

theorem arows2330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2330 = true := by
  rw [show D2M8K2.u2330 = KTree.node D2M8K2.u2326 (nat_lit 5557975) (nat_lit 1210224406) (nat_lit 0) D2M8K2.u2329 from rfl, allE_node, arows2326, irow2330, arows2329]
  all_goals rfl

theorem atot2330 : totK PD2M8K2 D2M8K2.u2330 = [0, 609097071523, 2198286937240, 2667211681963, 1450354110770, 282270315340, 9302370699, 0] := by
  rw [show D2M8K2.u2330 = KTree.node D2M8K2.u2326 (nat_lit 5557975) (nat_lit 1210224406) (nat_lit 0) D2M8K2.u2329 from rfl, totK_node, atot2326, atot2329]
  decide +kernel

theorem arows2339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2339 = true := by
  rw [show D2M8K2.u2339 = KTree.node D2M8K2.u2335 (nat_lit 5564645) (nat_lit 2379592452) (nat_lit 0) D2M8K2.u2338 from rfl, allE_node, arows2335, irow2339, arows2338]
  all_goals rfl

theorem atot2339 : totK PD2M8K2 D2M8K2.u2339 = [0, 746960155275, 2704444438902, 2857830783928, 869751950934, 46630286444, 0, 0] := by
  rw [show D2M8K2.u2339 = KTree.node D2M8K2.u2335 (nat_lit 5564645) (nat_lit 2379592452) (nat_lit 0) D2M8K2.u2338 from rfl, totK_node, atot2335, atot2338]
  decide +kernel

theorem arows2346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2346 = true := by
  rw [show D2M8K2.u2346 = KTree.node D2M8K2.u2342 (nat_lit 5575400) (nat_lit 2515082918) (nat_lit 0) D2M8K2.u2345 from rfl, allE_node, arows2342, irow2346, arows2345]
  all_goals rfl

theorem atot2346 : totK PD2M8K2 D2M8K2.u2346 = [0, 633336573746, 2636798105095, 3032645611269, 844685975189, 36864446645, 0, 0] := by
  rw [show D2M8K2.u2346 = KTree.node D2M8K2.u2342 (nat_lit 5575400) (nat_lit 2515082918) (nat_lit 0) D2M8K2.u2345 from rfl, totK_node, atot2342, atot2345]
  decide +kernel

theorem arows2354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2354 = true := by
  rw [show D2M8K2.u2354 = KTree.node D2M8K2.u2350 (nat_lit 5582880) (nat_lit 3476176154) (nat_lit 0) D2M8K2.u2353 from rfl, allE_node, arows2350, irow2354, arows2353]
  all_goals rfl

theorem atot2354 : totK PD2M8K2 D2M8K2.u2354 = [0, 0, 1020020364459, 3319391945717, 2444106947734, 335668935110, 6601594569, 0] := by
  rw [show D2M8K2.u2354 = KTree.node D2M8K2.u2350 (nat_lit 5582880) (nat_lit 3476176154) (nat_lit 0) D2M8K2.u2353 from rfl, totK_node, atot2350, atot2353]
  decide +kernel

theorem arows2361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2361 = true := by
  rw [show D2M8K2.u2361 = KTree.node D2M8K2.u2357 (nat_lit 5596745) (nat_lit 1776661562) (nat_lit 0) D2M8K2.u2360 from rfl, allE_node, arows2357, irow2361, arows2360]
  all_goals rfl

theorem atot2361 : totK PD2M8K2 D2M8K2.u2361 = [0, 410566095411, 2178525956518, 3228475251238, 1281384396414, 80936270420, 0, 0] := by
  rw [show D2M8K2.u2361 = KTree.node D2M8K2.u2357 (nat_lit 5596745) (nat_lit 1776661562) (nat_lit 0) D2M8K2.u2360 from rfl, totK_node, atot2357, atot2360]
  decide +kernel

theorem arows2371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2371 = true := by
  rw [show D2M8K2.u2371 = KTree.node D2M8K2.u2367 (nat_lit 5605389) (nat_lit 1289908094) (nat_lit 0) D2M8K2.u2370 from rfl, allE_node, arows2367, irow2371, arows2370]
  all_goals rfl

theorem atot2371 : totK PD2M8K2 D2M8K2.u2371 = [0, 826468267608, 2802171792072, 2781430379295, 817812150978, 43324884072, 0, 0] := by
  rw [show D2M8K2.u2371 = KTree.node D2M8K2.u2367 (nat_lit 5605389) (nat_lit 1289908094) (nat_lit 0) D2M8K2.u2370 from rfl, totK_node, atot2367, atot2370]
  decide +kernel

theorem arows2378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2378 = true := by
  rw [show D2M8K2.u2378 = KTree.node D2M8K2.u2374 (nat_lit 5616154) (nat_lit 3849923367) (nat_lit 0) D2M8K2.u2377 from rfl, allE_node, arows2374, irow2378, arows2377]
  all_goals rfl

theorem atot2378 : totK PD2M8K2 D2M8K2.u2378 = [0, 752887906210, 2831379154794, 2919191908865, 675097835063, 18498394793, 0, 0] := by
  rw [show D2M8K2.u2378 = KTree.node D2M8K2.u2374 (nat_lit 5616154) (nat_lit 3849923367) (nat_lit 0) D2M8K2.u2377 from rfl, totK_node, atot2374, atot2377]
  decide +kernel

theorem arows2386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2386 = true := by
  rw [show D2M8K2.u2386 = KTree.node D2M8K2.u2382 (nat_lit 5623438) (nat_lit 3602972963) (nat_lit 0) D2M8K2.u2385 from rfl, allE_node, arows2382, irow2386, arows2385]
  all_goals rfl

theorem atot2386 : totK PD2M8K2 D2M8K2.u2386 = [0, 0, 1233698954724, 3547296883653, 2183393909317, 202901489884, 1239866073, 0] := by
  rw [show D2M8K2.u2386 = KTree.node D2M8K2.u2382 (nat_lit 5623438) (nat_lit 3602972963) (nat_lit 0) D2M8K2.u2385 from rfl, totK_node, atot2382, atot2385]
  decide +kernel

theorem arows2393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2393 = true := by
  rw [show D2M8K2.u2393 = KTree.node D2M8K2.u2389 (nat_lit 5637148) (nat_lit 3804538969) (nat_lit 0) D2M8K2.u2392 from rfl, allE_node, arows2389, irow2393, arows2392]
  all_goals rfl

theorem atot2393 : totK PD2M8K2 D2M8K2.u2393 = [0, 418266149227, 1829966224723, 2914251676438, 1771001830692, 245773758672, 5425831197, 0] := by
  rw [show D2M8K2.u2393 = KTree.node D2M8K2.u2389 (nat_lit 5637148) (nat_lit 3804538969) (nat_lit 0) D2M8K2.u2392 from rfl, totK_node, atot2389, atot2392]
  decide +kernel

theorem arows2402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2402 = true := by
  rw [show D2M8K2.u2402 = KTree.node D2M8K2.u2398 (nat_lit 5687309) (nat_lit 2175808801) (nat_lit 0) D2M8K2.u2401 from rfl, allE_node, arows2398, irow2402, arows2401]
  all_goals rfl

theorem atot2402 : totK PD2M8K2 D2M8K2.u2402 = [0, 826965600308, 2825365637439, 2796844108839, 742425828479, 32763522543, 0, 0] := by
  rw [show D2M8K2.u2402 = KTree.node D2M8K2.u2398 (nat_lit 5687309) (nat_lit 2175808801) (nat_lit 0) D2M8K2.u2401 from rfl, totK_node, atot2398, atot2401]
  decide +kernel

theorem arows2409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2409 = true := by
  rw [show D2M8K2.u2409 = KTree.node D2M8K2.u2405 (nat_lit 5693531) (nat_lit 2908496283) (nat_lit 0) D2M8K2.u2408 from rfl, allE_node, arows2405, irow2409, arows2408]
  all_goals rfl

theorem atot2409 : totK PD2M8K2 D2M8K2.u2409 = [0, 773164486597, 2881983098548, 2894127779971, 639089990042, 17725851219, 0, 0] := by
  rw [show D2M8K2.u2409 = KTree.node D2M8K2.u2405 (nat_lit 5693531) (nat_lit 2908496283) (nat_lit 0) D2M8K2.u2408 from rfl, totK_node, atot2405, atot2408]
  decide +kernel

theorem arows2417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2417 = true := by
  rw [show D2M8K2.u2417 = KTree.node D2M8K2.u2413 (nat_lit 5703482) (nat_lit 3803575149) (nat_lit 0) D2M8K2.u2416 from rfl, allE_node, arows2413, irow2417, arows2416]
  all_goals rfl

theorem atot2417 : totK PD2M8K2 D2M8K2.u2417 = [0, 93924006320, 1450368259857, 3455862903835, 1991277631488, 182462848177, 1310285577, 0] := by
  rw [show D2M8K2.u2417 = KTree.node D2M8K2.u2413 (nat_lit 5703482) (nat_lit 3803575149) (nat_lit 0) D2M8K2.u2416 from rfl, totK_node, atot2413, atot2416]
  decide +kernel

theorem arows2424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2424 = true := by
  rw [show D2M8K2.u2424 = KTree.node D2M8K2.u2420 (nat_lit 5712243) (nat_lit 3042329965) (nat_lit 0) D2M8K2.u2423 from rfl, allE_node, arows2420, irow2424, arows2423]
  all_goals rfl

theorem atot2424 : totK PD2M8K2 D2M8K2.u2424 = [0, 0, 924570559905, 3180751510380, 2593325595808, 396096441878, 9811245038, 0] := by
  rw [show D2M8K2.u2424 = KTree.node D2M8K2.u2420 (nat_lit 5712243) (nat_lit 3042329965) (nat_lit 0) D2M8K2.u2423 from rfl, totK_node, atot2420, atot2423]
  decide +kernel

theorem arows2435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2435 = true := by
  rw [show D2M8K2.u2435 = KTree.node D2M8K2.u2431 (nat_lit 5722536) (nat_lit 3269297465) (nat_lit 0) D2M8K2.u2434 from rfl, allE_node, arows2431, irow2435, arows2434]
  all_goals rfl

theorem atot2435 : totK PD2M8K2 D2M8K2.u2435 = [449934862716, 1338413995501, 1533240448846, 1887848807239, 1624015499952, 420987221683, 21751168066, 0] := by
  rw [show D2M8K2.u2435 = KTree.node D2M8K2.u2431 (nat_lit 5722536) (nat_lit 3269297465) (nat_lit 0) D2M8K2.u2434 from rfl, totK_node, atot2431, atot2434]
  decide +kernel

theorem arows2442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2442 = true := by
  rw [show D2M8K2.u2442 = KTree.node D2M8K2.u2438 (nat_lit 6519898) (nat_lit 3367647917) (nat_lit 0) D2M8K2.u2441 from rfl, allE_node, arows2438, irow2442, arows2441]
  all_goals rfl

theorem atot2442 : totK PD2M8K2 D2M8K2.u2442 = [845726118887, 2890250341352, 2796152010116, 707184595101, 26232910576, 0, 0, 0] := by
  rw [show D2M8K2.u2442 = KTree.node D2M8K2.u2438 (nat_lit 6519898) (nat_lit 3367647917) (nat_lit 0) D2M8K2.u2441 from rfl, totK_node, atot2438, atot2441]
  decide +kernel

theorem arows2450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2450 = true := by
  rw [show D2M8K2.u2450 = KTree.node D2M8K2.u2446 (nat_lit 6526324) (nat_lit 3742063079) (nat_lit 0) D2M8K2.u2449 from rfl, allE_node, arows2446, irow2450, arows2449]
  all_goals rfl

theorem atot2450 : totK PD2M8K2 D2M8K2.u2450 = [845744674632, 2984256707823, 2822731815064, 583389385892, 17930741822, 0, 0, 0] := by
  rw [show D2M8K2.u2450 = KTree.node D2M8K2.u2446 (nat_lit 6526324) (nat_lit 3742063079) (nat_lit 0) D2M8K2.u2449 from rfl, totK_node, atot2446, atot2449]
  decide +kernel

theorem arows2457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2457 = true := by
  rw [show D2M8K2.u2457 = KTree.node D2M8K2.u2453 (nat_lit 6536742) (nat_lit 3617435441) (nat_lit 0) D2M8K2.u2456 from rfl, allE_node, arows2453, irow2457, arows2456]
  all_goals rfl

theorem atot2457 : totK PD2M8K2 D2M8K2.u2457 = [0, 1109518369317, 3116203865069, 2385907500733, 623118301443, 36921873854, 0, 0] := by
  rw [show D2M8K2.u2457 = KTree.node D2M8K2.u2453 (nat_lit 6536742) (nat_lit 3617435441) (nat_lit 0) D2M8K2.u2456 from rfl, totK_node, atot2453, atot2456]
  decide +kernel

theorem arows2466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2466 = true := by
  rw [show D2M8K2.u2466 = KTree.node D2M8K2.u2462 (nat_lit 6543300) (nat_lit 3044919166) (nat_lit 0) D2M8K2.u2465 from rfl, allE_node, arows2462, irow2466, arows2465]
  all_goals rfl

theorem atot2466 : totK PD2M8K2 D2M8K2.u2466 = [0, 847294422883, 3054989132911, 2786026719566, 503087674497, 10378741320, 0, 0] := by
  rw [show D2M8K2.u2466 = KTree.node D2M8K2.u2462 (nat_lit 6543300) (nat_lit 3044919166) (nat_lit 0) D2M8K2.u2465 from rfl, totK_node, atot2462, atot2465]
  decide +kernel

theorem arows2473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2473 = true := by
  rw [show D2M8K2.u2473 = KTree.node D2M8K2.u2469 (nat_lit 6550150) (nat_lit 2491984574) (nat_lit 0) D2M8K2.u2472 from rfl, allE_node, arows2469, irow2473, arows2472]
  all_goals rfl

theorem atot2473 : totK PD2M8K2 D2M8K2.u2473 = [322854152712, 1353291635133, 2691306410924, 2379969503831, 470660186415, 10717512769, 0, 0] := by
  rw [show D2M8K2.u2473 = KTree.node D2M8K2.u2469 (nat_lit 6550150) (nat_lit 2491984574) (nat_lit 0) D2M8K2.u2472 from rfl, totK_node, atot2469, atot2472]
  decide +kernel

theorem arows2481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2481 = true := by
  rw [show D2M8K2.u2481 = KTree.node D2M8K2.u2477 (nat_lit 6558227) (nat_lit 2709383176) (nat_lit 0) D2M8K2.u2480 from rfl, allE_node, arows2477, irow2481, arows2480]
  all_goals rfl

theorem atot2481 : totK PD2M8K2 D2M8K2.u2481 = [818747978156, 2847231172682, 2821570050282, 771047698438, 38966267249, 0, 0, 0] := by
  rw [show D2M8K2.u2481 = KTree.node D2M8K2.u2477 (nat_lit 6558227) (nat_lit 2709383176) (nat_lit 0) D2M8K2.u2480 from rfl, totK_node, atot2477, atot2480]
  decide +kernel

theorem arows2488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2488 = true := by
  rw [show D2M8K2.u2488 = KTree.node D2M8K2.u2484 (nat_lit 6567483) (nat_lit 3405981614) (nat_lit 0) D2M8K2.u2487 from rfl, allE_node, arows2484, irow2488, arows2487]
  all_goals rfl

theorem atot2488 : totK PD2M8K2 D2M8K2.u2488 = [812521612402, 2948229863648, 2848976942281, 586626838342, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u2488 = KTree.node D2M8K2.u2484 (nat_lit 6567483) (nat_lit 3405981614) (nat_lit 0) D2M8K2.u2487 from rfl, totK_node, atot2484, atot2487]
  decide +kernel

end QECKChecks.D2M8K2
