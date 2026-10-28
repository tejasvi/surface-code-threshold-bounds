import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A1

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows2396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2396 = true := by
  rw [show D2M8K2.u2396 = KTree.node D2M8K2.t2400 (nat_lit 5684600) (nat_lit 3440986249) (nat_lit 0) D2M8K2.t2401 from rfl, allE_node, rows2400, irow2396, rows2401]
  all_goals rfl

theorem atot2396 : totK PD2M8K2 D2M8K2.u2396 = [0, 106371811407, 658830009854, 889083222803, 162393438858, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2396 = KTree.node D2M8K2.t2400 (nat_lit 5684600) (nat_lit 3440986249) (nat_lit 0) D2M8K2.t2401 from rfl, totK_node, tot2400, tot2401]
  decide +kernel

theorem arows2397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2397 = true := by
  rw [show D2M8K2.u2397 = KTree.node D2M8K2.t2402 (nat_lit 5686324) (nat_lit 3966332001) (nat_lit 0) D2M8K2.t2403 from rfl, allE_node, rows2402, irow2397, rows2403]
  all_goals rfl

theorem atot2397 : totK PD2M8K2 D2M8K2.u2397 = [0, 297138705766, 883118940338, 571991087242, 60728694797, 0, 0, 0] := by
  rw [show D2M8K2.u2397 = KTree.node D2M8K2.t2402 (nat_lit 5686324) (nat_lit 3966332001) (nat_lit 0) D2M8K2.t2403 from rfl, totK_node, tot2402, tot2403]
  decide +kernel

theorem arows2399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2399 = true := by
  rw [show D2M8K2.u2399 = KTree.node D2M8K2.t2404 (nat_lit 5687866) (nat_lit 3189150191) (nat_lit 0) D2M8K2.t2405 from rfl, allE_node, rows2404, irow2399, rows2405]
  all_goals rfl

theorem atot2399 : totK PD2M8K2 D2M8K2.u2399 = [0, 36946381487, 359988405879, 876273713950, 482313574964, 31394372111, 0, 0] := by
  rw [show D2M8K2.u2399 = KTree.node D2M8K2.t2404 (nat_lit 5687866) (nat_lit 3189150191) (nat_lit 0) D2M8K2.t2405 from rfl, totK_node, tot2404, tot2405]
  decide +kernel

theorem arows2400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2400 = true := by
  rw [show D2M8K2.u2400 = KTree.node D2M8K2.t2406 (nat_lit 5689202) (nat_lit 4082330911) (nat_lit 0) D2M8K2.t2407 from rfl, allE_node, rows2406, irow2400, rows2407]
  all_goals rfl

theorem atot2400 : totK PD2M8K2 D2M8K2.u2400 = [0, 382266239915, 919683385017, 459496084844, 34814311059, 0, 0, 0] := by
  rw [show D2M8K2.u2400 = KTree.node D2M8K2.t2406 (nat_lit 5689202) (nat_lit 4082330911) (nat_lit 0) D2M8K2.t2407 from rfl, totK_node, tot2406, tot2407]
  decide +kernel

theorem arows2403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2403 = true := by
  rw [show D2M8K2.u2403 = KTree.node D2M8K2.t2408 (nat_lit 5690911) (nat_lit 1608211527) (nat_lit 0) D2M8K2.t2409 from rfl, allE_node, rows2408, irow2403, rows2409]
  all_goals rfl

theorem atot2403 : totK PD2M8K2 D2M8K2.u2403 = [0, 0, 515611396671, 978140890544, 273507906019, 8812418916, 0, 0] := by
  rw [show D2M8K2.u2403 = KTree.node D2M8K2.t2408 (nat_lit 5690911) (nat_lit 1608211527) (nat_lit 0) D2M8K2.t2409 from rfl, totK_node, tot2408, tot2409]
  decide +kernel

theorem arows2404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2404 = true := by
  rw [show D2M8K2.u2404 = KTree.node D2M8K2.t2410 (nat_lit 5692897) (nat_lit 1556966388) (nat_lit 0) D2M8K2.t2411 from rfl, allE_node, rows2410, irow2404, rows2411]
  all_goals rfl

theorem atot2404 : totK PD2M8K2 D2M8K2.u2404 = [0, 381247769648, 908002219543, 470082205391, 40868753786, 0, 0, 0] := by
  rw [show D2M8K2.u2404 = KTree.node D2M8K2.t2410 (nat_lit 5692897) (nat_lit 1556966388) (nat_lit 0) D2M8K2.t2411 from rfl, totK_node, tot2410, tot2411]
  decide +kernel

theorem arows2406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2406 = true := by
  rw [show D2M8K2.u2406 = KTree.node D2M8K2.t2412 (nat_lit 5694169) (nat_lit 1225946548) (nat_lit 0) D2M8K2.t2413 from rfl, allE_node, rows2412, irow2406, rows2413]
  all_goals rfl

theorem atot2406 : totK PD2M8K2 D2M8K2.u2406 = [0, 38189920222, 530798783534, 922016540850, 275591156469, 8913432303, 0, 0] := by
  rw [show D2M8K2.u2406 = KTree.node D2M8K2.t2412 (nat_lit 5694169) (nat_lit 1225946548) (nat_lit 0) D2M8K2.t2413 from rfl, totK_node, tot2412, tot2413]
  decide +kernel

theorem arows2407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2407 = true := by
  rw [show D2M8K2.u2407 = KTree.node D2M8K2.t2414 (nat_lit 5699457) (nat_lit 1638099013) (nat_lit 0) D2M8K2.t2415 from rfl, allE_node, rows2414, irow2407, rows2415]
  all_goals rfl

theorem atot2407 : totK PD2M8K2 D2M8K2.u2407 = [0, 353726796727, 924662202517, 522481690329, 47764208776, 0, 0, 0] := by
  rw [show D2M8K2.u2407 = KTree.node D2M8K2.t2414 (nat_lit 5699457) (nat_lit 1638099013) (nat_lit 0) D2M8K2.t2415 from rfl, totK_node, tot2414, tot2415]
  decide +kernel

theorem arows2411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2411 = true := by
  rw [show D2M8K2.u2411 = KTree.node D2M8K2.t2416 (nat_lit 5700918) (nat_lit 3324434432) (nat_lit 0) D2M8K2.t2417 from rfl, allE_node, rows2416, irow2411, rows2417]
  all_goals rfl

theorem atot2411 : totK PD2M8K2 D2M8K2.u2411 = [0, 93924006320, 617029953018, 876498935106, 221690728466, 4967996017, 0, 0] := by
  rw [show D2M8K2.u2411 = KTree.node D2M8K2.t2416 (nat_lit 5700918) (nat_lit 3324434432) (nat_lit 0) D2M8K2.t2417 from rfl, totK_node, tot2416, tot2417]
  decide +kernel

theorem arows2412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2412 = true := by
  rw [show D2M8K2.u2412 = KTree.node D2M8K2.t2418 (nat_lit 5702536) (nat_lit 3742317382) (nat_lit 0) D2M8K2.t2419 from rfl, allE_node, rows2418, irow2412, rows2419]
  all_goals rfl

theorem atot2412 : totK PD2M8K2 D2M8K2.u2412 = [0, 0, 358374757270, 955894340160, 442526056619, 23601535580, 0, 0] := by
  rw [show D2M8K2.u2412 = KTree.node D2M8K2.t2418 (nat_lit 5702536) (nat_lit 3742317382) (nat_lit 0) D2M8K2.t2419 from rfl, totK_node, tot2418, tot2419]
  decide +kernel

theorem arows2414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2414 = true := by
  rw [show D2M8K2.u2414 = KTree.node D2M8K2.t2420 (nat_lit 5704146) (nat_lit 3304689577) (nat_lit 0) D2M8K2.t2421 from rfl, allE_node, rows2420, irow2414, rows2421]
  all_goals rfl

theorem atot2414 : totK PD2M8K2 D2M8K2.u2414 = [0, 0, 155013321811, 736228612532, 756159780330, 103891713505, 1310285577, 0] := by
  rw [show D2M8K2.u2414 = KTree.node D2M8K2.t2420 (nat_lit 5704146) (nat_lit 3304689577) (nat_lit 0) D2M8K2.t2421 from rfl, totK_node, tot2420, tot2421]
  decide +kernel

theorem arows2415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2415 = true := by
  rw [show D2M8K2.u2415 = KTree.node D2M8K2.t2422 (nat_lit 5706489) (nat_lit 1801959837) (nat_lit 0) D2M8K2.t2423 from rfl, allE_node, rows2422, irow2415, rows2423]
  all_goals rfl

theorem atot2415 : totK PD2M8K2 D2M8K2.u2415 = [0, 0, 315986505576, 879992072659, 570901066073, 50001603075, 0, 0] := by
  rw [show D2M8K2.u2415 = KTree.node D2M8K2.t2422 (nat_lit 5706489) (nat_lit 1801959837) (nat_lit 0) D2M8K2.t2423 from rfl, totK_node, tot2422, tot2423]
  decide +kernel

theorem arows2418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2418 = true := by
  rw [show D2M8K2.u2418 = KTree.node D2M8K2.t2424 (nat_lit 5709583) (nat_lit 1745151044) (nat_lit 0) D2M8K2.t2425 from rfl, allE_node, rows2424, irow2418, rows2425]
  all_goals rfl

theorem atot2418 : totK PD2M8K2 D2M8K2.u2418 = [0, 0, 352146920111, 922613078632, 498018941224, 35985034972, 0, 0] := by
  rw [show D2M8K2.u2418 = KTree.node D2M8K2.t2424 (nat_lit 5709583) (nat_lit 1745151044) (nat_lit 0) D2M8K2.t2425 from rfl, totK_node, tot2424, tot2425]
  decide +kernel

theorem arows2419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2419 = true := by
  rw [show D2M8K2.u2419 = KTree.node D2M8K2.t2426 (nat_lit 5711122) (nat_lit 3744721073) (nat_lit 0) D2M8K2.t2427 from rfl, allE_node, rows2426, irow2419, rows2427]
  all_goals rfl

theorem atot2419 : totK PD2M8K2 D2M8K2.u2419 = [0, 0, 155002192905, 699908893304, 736957880325, 149709117070, 4879840392, 0] := by
  rw [show D2M8K2.u2419 = KTree.node D2M8K2.t2426 (nat_lit 5711122) (nat_lit 3744721073) (nat_lit 0) D2M8K2.t2427 from rfl, totK_node, tot2426, tot2427]
  decide +kernel

theorem arows2421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2421 = true := by
  rw [show D2M8K2.u2421 = KTree.node D2M8K2.t2428 (nat_lit 5713189) (nat_lit 1152166278) (nat_lit 0) D2M8K2.t2429 from rfl, allE_node, rows2428, irow2421, rows2429]
  all_goals rfl

theorem atot2421 : totK PD2M8K2 D2M8K2.u2421 = [0, 0, 327917920925, 892327802807, 530812410123, 43712046418, 0, 0] := by
  rw [show D2M8K2.u2421 = KTree.node D2M8K2.t2428 (nat_lit 5713189) (nat_lit 1152166278) (nat_lit 0) D2M8K2.t2429 from rfl, totK_node, tot2428, tot2429]
  decide +kernel

theorem arows2422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2422 = true := by
  rw [show D2M8K2.u2422 = KTree.node D2M8K2.t2430 (nat_lit 5714761) (nat_lit 1421628888) (nat_lit 0) D2M8K2.t2431 from rfl, allE_node, rows2430, irow2422, rows2431]
  all_goals rfl

theorem atot2422 : totK PD2M8K2 D2M8K2.u2422 = [0, 0, 89503525964, 662620511303, 823059422256, 166690243418, 4931404646, 0] := by
  rw [show D2M8K2.u2422 = KTree.node D2M8K2.t2430 (nat_lit 5714761) (nat_lit 1421628888) (nat_lit 0) D2M8K2.t2431 from rfl, totK_node, tot2430, tot2431]
  decide +kernel

theorem arows2429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2429 = true := by
  rw [show D2M8K2.u2429 = KTree.node D2M8K2.t2432 (nat_lit 5720246) (nat_lit 3929524261) (nat_lit 0) D2M8K2.t2433 from rfl, allE_node, rows2432, irow2429, rows2433]
  all_goals rfl

theorem atot2429 : totK PD2M8K2 D2M8K2.u2429 = [0, 0, 365575979961, 926240994722, 493842178259, 38456806952, 0, 0] := by
  rw [show D2M8K2.u2429 = KTree.node D2M8K2.t2432 (nat_lit 5720246) (nat_lit 3929524261) (nat_lit 0) D2M8K2.t2433 from rfl, totK_node, tot2432, tot2433]
  decide +kernel

theorem arows2430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2430 = true := by
  rw [show D2M8K2.u2430 = KTree.node D2M8K2.t2434 (nat_lit 5721749) (nat_lit 2251220496) (nat_lit 0) D2M8K2.t2435 from rfl, allE_node, rows2434, irow2430, rows2435]
  all_goals rfl

theorem atot2430 : totK PD2M8K2 D2M8K2.u2430 = [0, 0, 75904225969, 576707918656, 858079323223, 242011618512, 8424427256, 0] := by
  rw [show D2M8K2.u2430 = KTree.node D2M8K2.t2434 (nat_lit 5721749) (nat_lit 2251220496) (nat_lit 0) D2M8K2.t2435 from rfl, totK_node, tot2434, tot2435]
  decide +kernel

theorem arows2432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2432 = true := by
  rw [show D2M8K2.u2432 = KTree.node D2M8K2.t2436 (nat_lit 6515085) (nat_lit 1156510760) (nat_lit 0) D2M8K2.t2437 from rfl, allE_node, rows2436, irow2432, rows2437]
  all_goals rfl

theorem atot2432 : totK PD2M8K2 D2M8K2.u2432 = [272191924054, 667197265148, 376616927714, 127659711385, 244563288210, 140518796219, 13326740810, 0] := by
  rw [show D2M8K2.u2432 = KTree.node D2M8K2.t2436 (nat_lit 6515085) (nat_lit 1156510760) (nat_lit 0) D2M8K2.t2437 from rfl, totK_node, tot2436, tot2437]
  decide +kernel

theorem arows2433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2433 = true := by
  rw [show D2M8K2.u2433 = KTree.node D2M8K2.t2438 (nat_lit 6516269) (nat_lit 2134979284) (nat_lit 0) D2M8K2.t2439 from rfl, allE_node, rows2438, irow2433, rows2439]
  all_goals rfl

theorem atot2433 : totK PD2M8K2 D2M8K2.u2433 = [177742938662, 667234220455, 711121066142, 257240182476, 24261412795, 0, 0, 0] := by
  rw [show D2M8K2.u2433 = KTree.node D2M8K2.t2438 (nat_lit 6516269) (nat_lit 2134979284) (nat_lit 0) D2M8K2.t2439 from rfl, totK_node, tot2438, tot2439]
  decide +kernel

theorem arows2436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2436 = true := by
  rw [show D2M8K2.u2436 = KTree.node D2M8K2.t2440 (nat_lit 6517757) (nat_lit 2244266708) (nat_lit 0) D2M8K2.t2441 from rfl, allE_node, rows2440, irow2436, rows2441]
  all_goals rfl

theorem atot2436 : totK PD2M8K2 D2M8K2.u2436 = [149668319793, 556198503029, 774972595592, 325154681344, 13347985310, 0, 0, 0] := by
  rw [show D2M8K2.u2436 = KTree.node D2M8K2.t2440 (nat_lit 6517757) (nat_lit 2244266708) (nat_lit 0) D2M8K2.t2441 from rfl, totK_node, tot2440, tot2441]
  decide +kernel

theorem arows2437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2437 = true := by
  rw [show D2M8K2.u2437 = KTree.node D2M8K2.t2442 (nat_lit 6519249) (nat_lit 1850098401) (nat_lit 0) D2M8K2.t2443 from rfl, allE_node, rows2442, irow2437, rows2443]
  all_goals rfl

theorem atot2437 : totK PD2M8K2 D2M8K2.u2437 = [273090347178, 858701447732, 615021251005, 66646959115, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2437 = KTree.node D2M8K2.t2442 (nat_lit 6519249) (nat_lit 1850098401) (nat_lit 0) D2M8K2.t2443 from rfl, totK_node, tot2442, tot2443]
  decide +kernel

theorem arows2439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2439 = true := by
  rw [show D2M8K2.u2439 = KTree.node D2M8K2.t2444 (nat_lit 6520956) (nat_lit 3089173506) (nat_lit 0) D2M8K2.t2445 from rfl, allE_node, rows2444, irow2439, rows2445]
  all_goals rfl

theorem atot2439 : totK PD2M8K2 D2M8K2.u2439 = [102247145681, 571260346624, 843409856221, 265191235997, 12884925266, 0, 0, 0] := by
  rw [show D2M8K2.u2439 = KTree.node D2M8K2.t2444 (nat_lit 6520956) (nat_lit 3089173506) (nat_lit 0) D2M8K2.t2445 from rfl, totK_node, tot2444, tot2445]
  decide +kernel

theorem arows2440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2440 = true := by
  rw [show D2M8K2.u2440 = KTree.node D2M8K2.t2446 (nat_lit 6522650) (nat_lit 4210252945) (nat_lit 0) D2M8K2.t2447 from rfl, allE_node, rows2446, irow2440, rows2447]
  all_goals rfl

theorem atot2440 : totK PD2M8K2 D2M8K2.u2440 = [320720306235, 898156837703, 559380659381, 50191718645, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2440 = KTree.node D2M8K2.t2446 (nat_lit 6522650) (nat_lit 4210252945) (nat_lit 0) D2M8K2.t2447 from rfl, totK_node, tot2446, tot2447]
  decide +kernel

theorem arows2444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2444 = true := by
  rw [show D2M8K2.u2444 = KTree.node D2M8K2.t2448 (nat_lit 6524334) (nat_lit 3915818741) (nat_lit 0) D2M8K2.t2449 from rfl, allE_node, rows2448, irow2444, rows2449]
  all_goals rfl

theorem atot2444 : totK PD2M8K2 D2M8K2.u2444 = [65979365819, 519829811057, 886513863490, 289627797286, 13063444908, 0, 0, 0] := by
  rw [show D2M8K2.u2444 = KTree.node D2M8K2.t2448 (nat_lit 6524334) (nat_lit 3915818741) (nat_lit 0) D2M8K2.t2449 from rfl, totK_node, tot2448, tot2449]
  decide +kernel

theorem arows2445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2445 = true := by
  rw [show D2M8K2.u2445 = KTree.node D2M8K2.t2450 (nat_lit 6525717) (nat_lit 1461964138) (nat_lit 0) D2M8K2.t2451 from rfl, allE_node, rows2450, irow2445, rows2451]
  all_goals rfl

theorem atot2445 : totK PD2M8K2 D2M8K2.u2445 = [354389509663, 931026090142, 502800618203, 40152827578, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2445 = KTree.node D2M8K2.t2450 (nat_lit 6525717) (nat_lit 1461964138) (nat_lit 0) D2M8K2.t2451 from rfl, totK_node, tot2450, tot2451]
  decide +kernel

theorem arows2447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2447 = true := by
  rw [show D2M8K2.u2447 = KTree.node D2M8K2.t2452 (nat_lit 6527594) (nat_lit 4051909980) (nat_lit 0) D2M8K2.t2453 from rfl, allE_node, rows2452, irow2447, rows2453]
  all_goals rfl

theorem atot2447 : totK PD2M8K2 D2M8K2.u2447 = [87572808389, 623522194104, 890045031951, 201534280933, 4867296914, 0, 0, 0] := by
  rw [show D2M8K2.u2447 = KTree.node D2M8K2.t2452 (nat_lit 6527594) (nat_lit 4051909980) (nat_lit 0) D2M8K2.t2453 from rfl, totK_node, tot2452, tot2453]
  decide +kernel

theorem arows2448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2448 = true := by
  rw [show D2M8K2.u2448 = KTree.node D2M8K2.t2454 (nat_lit 6529258) (nat_lit 3878709408) (nat_lit 0) D2M8K2.t2455 from rfl, allE_node, rows2454, irow2448, rows2455]
  all_goals rfl

theorem atot2448 : totK PD2M8K2 D2M8K2.u2448 = [337802990761, 902856494863, 541573663183, 52074480095, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2448 = KTree.node D2M8K2.t2454 (nat_lit 6529258) (nat_lit 3878709408) (nat_lit 0) D2M8K2.t2455 from rfl, totK_node, tot2454, tot2455]
  decide +kernel

theorem arows2451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2451 = true := by
  rw [show D2M8K2.u2451 = KTree.node D2M8K2.t2456 (nat_lit 6530929) (nat_lit 963378267) (nat_lit 0) D2M8K2.t2457 from rfl, allE_node, rows2456, irow2451, rows2457]
  all_goals rfl

theorem atot2451 : totK PD2M8K2 D2M8K2.u2451 = [0, 412653780364, 975286755801, 378106347924, 14728774134, 0, 0, 0] := by
  rw [show D2M8K2.u2451 = KTree.node D2M8K2.t2456 (nat_lit 6530929) (nat_lit 963378267) (nat_lit 0) D2M8K2.t2457 from rfl, totK_node, tot2456, tot2457]
  decide +kernel

theorem arows2452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2452 = true := by
  rw [show D2M8K2.u2452 = KTree.node D2M8K2.t2458 (nat_lit 6536119) (nat_lit 1408549791) (nat_lit 0) D2M8K2.t2459 from rfl, allE_node, rows2458, irow2452, rows2459]
  all_goals rfl

theorem atot2452 : totK PD2M8K2 D2M8K2.u2452 = [0, 365602724352, 923396074342, 515726707412, 43248091783, 0, 0, 0] := by
  rw [show D2M8K2.u2452 = KTree.node D2M8K2.t2458 (nat_lit 6536119) (nat_lit 1408549791) (nat_lit 0) D2M8K2.t2459 from rfl, totK_node, tot2458, tot2459]
  decide +kernel

theorem arows2454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2454 = true := by
  rw [show D2M8K2.u2454 = KTree.node D2M8K2.t2460 (nat_lit 6537578) (nat_lit 4109747187) (nat_lit 0) D2M8K2.t2461 from rfl, allE_node, rows2460, irow2454, rows2461]
  all_goals rfl

theorem atot2454 : totK PD2M8K2 D2M8K2.u2454 = [0, 79192507633, 522892693634, 832975906500, 356994628030, 29044448997, 0, 0] := by
  rw [show D2M8K2.u2454 = KTree.node D2M8K2.t2460 (nat_lit 6537578) (nat_lit 4109747187) (nat_lit 0) D2M8K2.t2461 from rfl, totK_node, tot2460, tot2461]
  decide +kernel

theorem arows2455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2455 = true := by
  rw [show D2M8K2.u2455 = KTree.node D2M8K2.t2462 (nat_lit 6538876) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t2463 from rfl, allE_node, rows2462, irow2455, rows2463]
  all_goals rfl

theorem atot2455 : totK PD2M8K2 D2M8K2.u2455 = [0, 248451921527, 694628341292, 657263001920, 206844391309, 7877424857, 0, 0] := by
  rw [show D2M8K2.u2455 = KTree.node D2M8K2.t2462 (nat_lit 6538876) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t2463 from rfl, totK_node, tot2462, tot2463]
  decide +kernel

theorem arows2460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2460 = true := by
  rw [show D2M8K2.u2460 = KTree.node D2M8K2.t2464 (nat_lit 6540365) (nat_lit 2188079480) (nat_lit 0) D2M8K2.t2465 from rfl, allE_node, rows2464, irow2460, rows2465]
  all_goals rfl

theorem atot2460 : totK PD2M8K2 D2M8K2.u2460 = [0, 172383748415, 771816242896, 736632318290, 115361417471, 2909416399, 0, 0] := by
  rw [show D2M8K2.u2460 = KTree.node D2M8K2.t2464 (nat_lit 6540365) (nat_lit 2188079480) (nat_lit 0) D2M8K2.t2465 from rfl, totK_node, tot2464, tot2465]
  decide +kernel

theorem arows2461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2461 = true := by
  rw [show D2M8K2.u2461 = KTree.node D2M8K2.t2466 (nat_lit 6542434) (nat_lit 3839615647) (nat_lit 0) D2M8K2.t2467 from rfl, allE_node, rows2466, irow2461, rows2467]
  all_goals rfl

theorem atot2461 : totK PD2M8K2 D2M8K2.u2461 = [0, 248604891787, 769155428889, 660250731905, 130132422000, 2250452236, 0, 0] := by
  rw [show D2M8K2.u2461 = KTree.node D2M8K2.t2466 (nat_lit 6542434) (nat_lit 3839615647) (nat_lit 0) D2M8K2.t2467 from rfl, totK_node, tot2466, tot2467]
  decide +kernel

theorem arows2463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2463 = true := by
  rw [show D2M8K2.u2463 = KTree.node D2M8K2.t2468 (nat_lit 6543884) (nat_lit 1517917089) (nat_lit 0) D2M8K2.t2469 from rfl, allE_node, rows2468, irow2463, rows2469]
  all_goals rfl

theorem atot2463 : totK PD2M8K2 D2M8K2.u2463 = [0, 172446104734, 735820798369, 728515779273, 145134075354, 4031931762, 0, 0] := by
  rw [show D2M8K2.u2463 = KTree.node D2M8K2.t2468 (nat_lit 6543884) (nat_lit 1517917089) (nat_lit 0) D2M8K2.t2469 from rfl, totK_node, tot2468, tot2469]
  decide +kernel

theorem arows2464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2464 = true := by
  rw [show D2M8K2.u2464 = KTree.node D2M8K2.t2470 (nat_lit 6545995) (nat_lit 1804167824) (nat_lit 0) D2M8K2.t2471 from rfl, allE_node, rows2470, irow2464, rows2471]
  all_goals rfl

theorem atot2464 : totK PD2M8K2 D2M8K2.u2464 = [0, 253859677947, 773994862064, 653989541779, 112459759672, 1186940923, 0, 0] := by
  rw [show D2M8K2.u2464 = KTree.node D2M8K2.t2470 (nat_lit 6545995) (nat_lit 1804167824) (nat_lit 0) D2M8K2.t2471 from rfl, totK_node, tot2470, tot2471]
  decide +kernel

theorem arows2467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2467 = true := by
  rw [show D2M8K2.u2467 = KTree.node D2M8K2.t2472 (nat_lit 6547452) (nat_lit 2881910717) (nat_lit 0) D2M8K2.t2473 from rfl, allE_node, rows2472, irow2467, rows2473]
  all_goals rfl

theorem atot2467 : totK PD2M8K2 D2M8K2.u2467 = [0, 162053763936, 801097661526, 769470875663, 81196877645, 0, 0, 0] := by
  rw [show D2M8K2.u2467 = KTree.node D2M8K2.t2472 (nat_lit 6547452) (nat_lit 2881910717) (nat_lit 0) D2M8K2.t2473 from rfl, totK_node, tot2472, tot2473]
  decide +kernel

theorem arows2468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2468 = true := by
  rw [show D2M8K2.u2468 = KTree.node D2M8K2.t2474 (nat_lit 6549598) (nat_lit 3768840658) (nat_lit 0) D2M8K2.t2475 from rfl, allE_node, rows2474, irow2468, rows2475]
  all_goals rfl

theorem atot2468 : totK PD2M8K2 D2M8K2.u2468 = [0, 330889665297, 836331732701, 553137339264, 98318270170, 1415142070, 0, 0] := by
  rw [show D2M8K2.u2468 = KTree.node D2M8K2.t2474 (nat_lit 6549598) (nat_lit 3768840658) (nat_lit 0) D2M8K2.t2475 from rfl, totK_node, tot2474, tot2475]
  decide +kernel

theorem arows2470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2470 = true := by
  rw [show D2M8K2.u2470 = KTree.node D2M8K2.t2476 (nat_lit 6551237) (nat_lit 1924164693) (nat_lit 0) D2M8K2.t2477 from rfl, allE_node, rows2476, irow2470, rows2477]
  all_goals rfl

theorem atot2470 : totK PD2M8K2 D2M8K2.u2470 = [0, 92515481918, 662589972136, 856947509490, 189337935383, 2484078857, 0, 0] := by
  rw [show D2M8K2.u2470 = KTree.node D2M8K2.t2476 (nat_lit 6551237) (nat_lit 1924164693) (nat_lit 0) D2M8K2.t2477 from rfl, totK_node, tot2476, tot2477]
  decide +kernel

theorem arows2471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2471 = true := by
  rw [show D2M8K2.u2471 = KTree.node D2M8K2.t2478 (nat_lit 6553285) (nat_lit 1354964743) (nat_lit 0) D2M8K2.t2479 from rfl, allE_node, rows2478, irow2471, rows2479]
  all_goals rfl

theorem atot2471 : totK PD2M8K2 D2M8K2.u2471 = [322854152712, 767832723982, 391287044561, 191850830407, 101807103217, 6818291842, 0, 0] := by
  rw [show D2M8K2.u2471 = KTree.node D2M8K2.t2478 (nat_lit 6553285) (nat_lit 1354964743) (nat_lit 0) D2M8K2.t2479 from rfl, totK_node, tot2478, tot2479]
  decide +kernel

theorem arows2475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2475 = true := by
  rw [show D2M8K2.u2475 = KTree.node D2M8K2.t2480 (nat_lit 6555564) (nat_lit 3189829869) (nat_lit 0) D2M8K2.t2481 from rfl, allE_node, rows2480, irow2475, rows2481]
  all_goals rfl

theorem atot2475 : totK PD2M8K2 D2M8K2.u2475 = [149847357467, 700848312630, 829631225759, 146828229210, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2475 = KTree.node D2M8K2.t2480 (nat_lit 6555564) (nat_lit 3189829869) (nat_lit 0) D2M8K2.t2481 from rfl, totK_node, tot2480, tot2481]
  decide +kernel

theorem arows2476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2476 = true := by
  rw [show D2M8K2.u2476 = KTree.node D2M8K2.t2482 (nat_lit 6557334) (nat_lit 2670305817) (nat_lit 0) D2M8K2.t2483 from rfl, allE_node, rows2482, irow2476, rows2483]
  all_goals rfl

theorem atot2476 : totK PD2M8K2 D2M8K2.u2476 = [277123839233, 876087713288, 603789473517, 70634999408, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2476 = KTree.node D2M8K2.t2482 (nat_lit 6557334) (nat_lit 2670305817) (nat_lit 0) D2M8K2.t2483 from rfl, totK_node, tot2482, tot2483]
  decide +kernel

theorem arows2478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2478 = true := by
  rw [show D2M8K2.u2478 = KTree.node D2M8K2.t2484 (nat_lit 6558858) (nat_lit 3700799567) (nat_lit 0) D2M8K2.t2485 from rfl, allE_node, rows2484, irow2478, rows2485]
  all_goals rfl

theorem atot2478 : totK PD2M8K2 D2M8K2.u2478 = [0, 336431980192, 922589359045, 511440034954, 34299829713, 0, 0, 0] := by
  rw [show D2M8K2.u2478 = KTree.node D2M8K2.t2484 (nat_lit 6558858) (nat_lit 3700799567) (nat_lit 0) D2M8K2.t2485 from rfl, totK_node, tot2484, tot2485]
  decide +kernel

theorem arows2479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2479 = true := by
  rw [show D2M8K2.u2479 = KTree.node D2M8K2.t2486 (nat_lit 6560080) (nat_lit 3430010216) (nat_lit 0) D2M8K2.t2487 from rfl, allE_node, rows2486, irow2479, rows2487]
  all_goals rfl

theorem atot2479 : totK PD2M8K2 D2M8K2.u2479 = [387736818080, 933863166572, 465559991961, 39435051690, 2174602308, 0, 0, 0] := by
  rw [show D2M8K2.u2479 = KTree.node D2M8K2.t2486 (nat_lit 6560080) (nat_lit 3430010216) (nat_lit 0) D2M8K2.t2487 from rfl, totK_node, tot2486, tot2487]
  decide +kernel

theorem arows2482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2482 = true := by
  rw [show D2M8K2.u2482 = KTree.node D2M8K2.t2488 (nat_lit 6561605) (nat_lit 2315076869) (nat_lit 0) D2M8K2.t2489 from rfl, allE_node, rows2488, irow2482, rows2489]
  all_goals rfl

theorem atot2482 : totK PD2M8K2 D2M8K2.u2482 = [52364295763, 537524991845, 917321563838, 270951939996, 10568566766, 0, 0, 0] := by
  rw [show D2M8K2.u2482 = KTree.node D2M8K2.t2488 (nat_lit 6561605) (nat_lit 2315076869) (nat_lit 0) D2M8K2.t2489 from rfl, totK_node, tot2488, tot2489]
  decide +kernel

theorem arows2483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2483 = true := by
  rw [show D2M8K2.u2483 = KTree.node D2M8K2.t2490 (nat_lit 6566873) (nat_lit 1699420788) (nat_lit 0) D2M8K2.t2491 from rfl, allE_node, rows2490, irow2483, rows2491]
  all_goals rfl

theorem atot2483 : totK PD2M8K2 D2M8K2.u2483 = [319757383633, 878791310729, 544896149469, 67043434450, 1503593968, 0, 0, 0] := by
  rw [show D2M8K2.u2483 = KTree.node D2M8K2.t2490 (nat_lit 6566873) (nat_lit 1699420788) (nat_lit 0) D2M8K2.t2491 from rfl, totK_node, tot2490, tot2491]
  decide +kernel

theorem arows2485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2485 = true := by
  rw [show D2M8K2.u2485 = KTree.node D2M8K2.t2492 (nat_lit 6568460) (nat_lit 3710297274) (nat_lit 0) D2M8K2.t2493 from rfl, allE_node, rows2492, irow2485, rows2493]
  all_goals rfl

theorem atot2485 : totK PD2M8K2 D2M8K2.u2485 = [90936333741, 665798848800, 865768747707, 161535797525, 2165917952, 0, 0, 0] := by
  rw [show D2M8K2.u2485 = KTree.node D2M8K2.t2492 (nat_lit 6568460) (nat_lit 3710297274) (nat_lit 0) D2M8K2.t2493 from rfl, totK_node, tot2492, tot2493]
  decide +kernel

theorem arows2486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2486 = true := by
  rw [show D2M8K2.u2486 = KTree.node D2M8K2.t2494 (nat_lit 6570392) (nat_lit 3754315224) (nat_lit 0) D2M8K2.t2495 from rfl, allE_node, rows2494, irow2486, rows2495]
  all_goals rfl

theorem atot2486 : totK PD2M8K2 D2M8K2.u2486 = [349463599265, 866114712274, 517584499653, 86139647345, 2814597007, 0, 0, 0] := by
  rw [show D2M8K2.u2486 = KTree.node D2M8K2.t2494 (nat_lit 6570392) (nat_lit 3754315224) (nat_lit 0) D2M8K2.t2495 from rfl, totK_node, tot2494, tot2495]
  decide +kernel

theorem arows2492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2492 = true := by
  rw [show D2M8K2.u2492 = KTree.node D2M8K2.t2496 (nat_lit 6571954) (nat_lit 3937058269) (nat_lit 0) D2M8K2.t2497 from rfl, allE_node, rows2496, irow2492, rows2497]
  all_goals rfl

theorem atot2492 : totK PD2M8K2 D2M8K2.u2492 = [63020407318, 544124577228, 895745758638, 274254064744, 8554971388, 0, 0, 0] := by
  rw [show D2M8K2.u2492 = KTree.node D2M8K2.t2496 (nat_lit 6571954) (nat_lit 3937058269) (nat_lit 0) D2M8K2.t2497 from rfl, totK_node, tot2496, tot2497]
  decide +kernel

theorem arows2493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2493 = true := by
  rw [show D2M8K2.u2493 = KTree.node D2M8K2.t2498 (nat_lit 6573986) (nat_lit 3592907231) (nat_lit 0) D2M8K2.t2499 from rfl, allE_node, rows2498, irow2493, rows2499]
  all_goals rfl

theorem atot2493 : totK PD2M8K2 D2M8K2.u2493 = [0, 391784279789, 931058975069, 420230751621, 26959837225, 0, 0, 0] := by
  rw [show D2M8K2.u2493 = KTree.node D2M8K2.t2498 (nat_lit 6573986) (nat_lit 3592907231) (nat_lit 0) D2M8K2.t2499 from rfl, totK_node, tot2498, tot2499]
  decide +kernel

theorem arows2495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2495 = true := by
  rw [show D2M8K2.u2495 = KTree.node D2M8K2.t2500 (nat_lit 6576276) (nat_lit 2388973661) (nat_lit 0) D2M8K2.t2501 from rfl, allE_node, rows2500, irow2495, rows2501]
  all_goals rfl

theorem atot2495 : totK PD2M8K2 D2M8K2.u2495 = [0, 149430685018, 727172052639, 786513838006, 120823380739, 1206465782, 0, 0] := by
  rw [show D2M8K2.u2495 = KTree.node D2M8K2.t2500 (nat_lit 6576276) (nat_lit 2388973661) (nat_lit 0) D2M8K2.t2501 from rfl, totK_node, tot2500, tot2501]
  decide +kernel

theorem arows2496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2496 = true := by
  rw [show D2M8K2.u2496 = KTree.node D2M8K2.t2502 (nat_lit 6578094) (nat_lit 3718727449) (nat_lit 0) D2M8K2.t2503 from rfl, allE_node, rows2502, irow2496, rows2503]
  all_goals rfl

theorem atot2496 : totK PD2M8K2 D2M8K2.u2496 = [0, 361631981179, 950380420561, 461496251122, 27012155532, 0, 0, 0] := by
  rw [show D2M8K2.u2496 = KTree.node D2M8K2.t2502 (nat_lit 6578094) (nat_lit 3718727449) (nat_lit 0) D2M8K2.t2503 from rfl, totK_node, tot2502, tot2503]
  decide +kernel

theorem arows2499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2499 = true := by
  rw [show D2M8K2.u2499 = KTree.node D2M8K2.t2504 (nat_lit 6581045) (nat_lit 2315019738) (nat_lit 0) D2M8K2.t2505 from rfl, allE_node, rows2504, irow2499, rows2505]
  all_goals rfl

theorem atot2499 : totK PD2M8K2 D2M8K2.u2499 = [0, 357429793849, 942864955706, 493380348633, 33573894329, 0, 0, 0] := by
  rw [show D2M8K2.u2499 = KTree.node D2M8K2.t2504 (nat_lit 6581045) (nat_lit 2315019738) (nat_lit 0) D2M8K2.t2505 from rfl, totK_node, tot2504, tot2505]
  decide +kernel

theorem arows2500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2500 = true := by
  rw [show D2M8K2.u2500 = KTree.node D2M8K2.t2506 (nat_lit 6582721) (nat_lit 1414861519) (nat_lit 0) D2M8K2.t2507 from rfl, allE_node, rows2506, irow2500, rows2507]
  all_goals rfl

theorem atot2500 : totK PD2M8K2 D2M8K2.u2500 = [0, 64702258243, 515155955978, 854068976732, 272542298720, 13016197374, 0, 0] := by
  rw [show D2M8K2.u2500 = KTree.node D2M8K2.t2506 (nat_lit 6582721) (nat_lit 1414861519) (nat_lit 0) D2M8K2.t2507 from rfl, totK_node, tot2506, tot2507]
  decide +kernel

theorem arows2502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2502 = true := by
  rw [show D2M8K2.u2502 = KTree.node D2M8K2.t2508 (nat_lit 6587876) (nat_lit 2827845027) (nat_lit 0) D2M8K2.t2509 from rfl, allE_node, rows2508, irow2502, rows2509]
  all_goals rfl

theorem atot2502 : totK PD2M8K2 D2M8K2.u2502 = [0, 344919293345, 951974966856, 476243742003, 25180848616, 0, 0, 0] := by
  rw [show D2M8K2.u2502 = KTree.node D2M8K2.t2508 (nat_lit 6587876) (nat_lit 2827845027) (nat_lit 0) D2M8K2.t2509 from rfl, totK_node, tot2508, tot2509]
  decide +kernel

theorem arows2503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2503 = true := by
  rw [show D2M8K2.u2503 = KTree.node D2M8K2.t2510 (nat_lit 6590022) (nat_lit 3232582550) (nat_lit 0) D2M8K2.t2511 from rfl, allE_node, rows2510, irow2503, rows2511]
  all_goals rfl

theorem atot2503 : totK PD2M8K2 D2M8K2.u2503 = [0, 131972496502, 671431790725, 752216837242, 150211372026, 4574395652, 0, 0] := by
  rw [show D2M8K2.u2503 = KTree.node D2M8K2.t2510 (nat_lit 6590022) (nat_lit 3232582550) (nat_lit 0) D2M8K2.t2511 from rfl, totK_node, tot2510, tot2511]
  decide +kernel

theorem arows2507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2507 = true := by
  rw [show D2M8K2.u2507 = KTree.node D2M8K2.t2512 (nat_lit 6591580) (nat_lit 3306705031) (nat_lit 0) D2M8K2.t2513 from rfl, allE_node, rows2512, irow2507, rows2513]
  all_goals rfl

theorem atot2507 : totK PD2M8K2 D2M8K2.u2507 = [71343817081, 412123495182, 825161280673, 475952273837, 42755241284, 0, 0, 0] := by
  rw [show D2M8K2.u2507 = KTree.node D2M8K2.t2512 (nat_lit 6591580) (nat_lit 3306705031) (nat_lit 0) D2M8K2.t2513 from rfl, totK_node, tot2512, tot2513]
  decide +kernel

theorem arows2508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2508 = true := by
  rw [show D2M8K2.u2508 = KTree.node D2M8K2.t2514 (nat_lit 6595454) (nat_lit 2936772904) (nat_lit 0) D2M8K2.t2515 from rfl, allE_node, rows2514, irow2508, rows2515]
  all_goals rfl

theorem atot2508 : totK PD2M8K2 D2M8K2.u2508 = [251661989258, 816633832399, 626572947924, 95829431435, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2508 = KTree.node D2M8K2.t2514 (nat_lit 6595454) (nat_lit 2936772904) (nat_lit 0) D2M8K2.t2515 from rfl, totK_node, tot2514, tot2515]
  decide +kernel

theorem arows2510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2510 = true := by
  rw [show D2M8K2.u2510 = KTree.node D2M8K2.t2516 (nat_lit 6598001) (nat_lit 1729675020) (nat_lit 0) D2M8K2.t2517 from rfl, allE_node, rows2516, irow2510, rows2517]
  all_goals rfl

theorem atot2510 : totK PD2M8K2 D2M8K2.u2510 = [256340840216, 840939887857, 674155708308, 76422406866, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2510 = KTree.node D2M8K2.t2516 (nat_lit 6598001) (nat_lit 1729675020) (nat_lit 0) D2M8K2.t2517 from rfl, totK_node, tot2516, tot2517]
  decide +kernel

theorem arows2511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2511 = true := by
  rw [show D2M8K2.u2511 = KTree.node D2M8K2.t2518 (nat_lit 6599222) (nat_lit 3184346391) (nat_lit 0) D2M8K2.t2519 from rfl, allE_node, rows2518, irow2511, rows2519]
  all_goals rfl

theorem atot2511 : totK PD2M8K2 D2M8K2.u2511 = [174706502236, 647390421460, 692337602511, 276427124014, 25364689049, 0, 0, 0] := by
  rw [show D2M8K2.u2511 = KTree.node D2M8K2.t2518 (nat_lit 6599222) (nat_lit 3184346391) (nat_lit 0) D2M8K2.t2519 from rfl, totK_node, tot2518, tot2519]
  decide +kernel

theorem arows2514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2514 = true := by
  rw [show D2M8K2.u2514 = KTree.node D2M8K2.t2520 (nat_lit 6600732) (nat_lit 2385813508) (nat_lit 0) D2M8K2.t2521 from rfl, allE_node, rows2520, irow2514, rows2521]
  all_goals rfl

theorem atot2514 : totK PD2M8K2 D2M8K2.u2514 = [171607033725, 579352957254, 754619562863, 298924436331, 12230400950, 0, 0, 0] := by
  rw [show D2M8K2.u2514 = KTree.node D2M8K2.t2520 (nat_lit 6600732) (nat_lit 2385813508) (nat_lit 0) D2M8K2.t2521 from rfl, totK_node, tot2520, tot2521]
  decide +kernel

theorem arows2515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2515 = true := by
  rw [show D2M8K2.u2515 = KTree.node D2M8K2.t2522 (nat_lit 6605659) (nat_lit 2240536079) (nat_lit 0) D2M8K2.t2523 from rfl, allE_node, rows2522, irow2515, rows2523]
  all_goals rfl

theorem atot2515 : totK PD2M8K2 D2M8K2.u2515 = [268668266706, 875661753863, 624765697185, 59077904116, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2515 = KTree.node D2M8K2.t2522 (nat_lit 6605659) (nat_lit 2240536079) (nat_lit 0) D2M8K2.t2523 from rfl, totK_node, tot2522, tot2523]
  decide +kernel

theorem arows2517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2517 = true := by
  rw [show D2M8K2.u2517 = KTree.node D2M8K2.t2524 (nat_lit 6607330) (nat_lit 3322387528) (nat_lit 0) D2M8K2.t2525 from rfl, allE_node, rows2524, irow2517, rows2525]
  all_goals rfl

theorem atot2517 : totK PD2M8K2 D2M8K2.u2517 = [75421594546, 529276540085, 867060994569, 290176307180, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u2517 = KTree.node D2M8K2.t2524 (nat_lit 6607330) (nat_lit 3322387528) (nat_lit 0) D2M8K2.t2525 from rfl, totK_node, tot2524, tot2525]
  decide +kernel

theorem arows2518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2518 = true := by
  rw [show D2M8K2.u2518 = KTree.node D2M8K2.t2526 (nat_lit 6608749) (nat_lit 1382286413) (nat_lit 0) D2M8K2.t2527 from rfl, allE_node, rows2526, irow2518, rows2527]
  all_goals rfl

theorem atot2518 : totK PD2M8K2 D2M8K2.u2518 = [335338511724, 906418236935, 529016320644, 44091950419, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2518 = KTree.node D2M8K2.t2526 (nat_lit 6608749) (nat_lit 1382286413) (nat_lit 0) D2M8K2.t2527 from rfl, totK_node, tot2526, tot2527]
  decide +kernel

theorem arows2523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2523 = true := by
  rw [show D2M8K2.u2523 = KTree.node D2M8K2.t2528 (nat_lit 6610594) (nat_lit 3963276497) (nat_lit 0) D2M8K2.t2529 from rfl, allE_node, rows2528, irow2523, rows2529]
  all_goals rfl

theorem atot2523 : totK PD2M8K2 D2M8K2.u2523 = [113895582449, 629722928752, 842106078414, 198944368999, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u2523 = KTree.node D2M8K2.t2528 (nat_lit 6610594) (nat_lit 3963276497) (nat_lit 0) D2M8K2.t2529 from rfl, totK_node, tot2528, tot2529]
  decide +kernel

theorem arows2524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2524 = true := by
  rw [show D2M8K2.u2524 = KTree.node D2M8K2.t2530 (nat_lit 6612302) (nat_lit 3711930240) (nat_lit 0) D2M8K2.t2531 from rfl, allE_node, rows2530, irow2524, rows2531]
  all_goals rfl

theorem atot2524 : totK PD2M8K2 D2M8K2.u2524 = [302487518919, 880469096332, 591784709971, 57482936654, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2524 = KTree.node D2M8K2.t2530 (nat_lit 6612302) (nat_lit 3711930240) (nat_lit 0) D2M8K2.t2531 from rfl, totK_node, tot2530, tot2531]
  decide +kernel

theorem arows2526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2526 = true := by
  rw [show D2M8K2.u2526 = KTree.node D2M8K2.t2532 (nat_lit 6614011) (nat_lit 2241272188) (nat_lit 0) D2M8K2.t2533 from rfl, allE_node, rows2532, irow2526, rows2533]
  all_goals rfl

theorem atot2526 : totK PD2M8K2 D2M8K2.u2526 = [0, 416259566853, 955016584150, 390629327692, 21877146694, 0, 0, 0] := by
  rw [show D2M8K2.u2526 = KTree.node D2M8K2.t2532 (nat_lit 6614011) (nat_lit 2241272188) (nat_lit 0) D2M8K2.t2533 from rfl, totK_node, tot2532, tot2533]
  decide +kernel

theorem arows2527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2527 = true := by
  rw [show D2M8K2.u2527 = KTree.node D2M8K2.t2534 (nat_lit 6616130) (nat_lit 2704454313) (nat_lit 0) D2M8K2.t2535 from rfl, allE_node, rows2534, irow2527, rows2535]
  all_goals rfl

theorem atot2527 : totK PD2M8K2 D2M8K2.u2527 = [0, 254552422700, 831002216896, 590341259936, 79120925514, 1239866073, 0, 0] := by
  rw [show D2M8K2.u2527 = KTree.node D2M8K2.t2534 (nat_lit 6616130) (nat_lit 2704454313) (nat_lit 0) D2M8K2.t2535 from rfl, totK_node, tot2534, tot2535]
  decide +kernel

theorem arows2530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2530 = true := by
  rw [show D2M8K2.u2530 = KTree.node D2M8K2.t2536 (nat_lit 6618732) (nat_lit 1119948283) (nat_lit 0) D2M8K2.t2537 from rfl, allE_node, rows2536, irow2530, rows2537]
  all_goals rfl

theorem atot2530 : totK PD2M8K2 D2M8K2.u2530 = [0, 255527943874, 853349328614, 654179455759, 66211063180, 0, 0, 0] := by
  rw [show D2M8K2.u2530 = KTree.node D2M8K2.t2536 (nat_lit 6618732) (nat_lit 1119948283) (nat_lit 0) D2M8K2.t2537 from rfl, totK_node, tot2536, tot2537]
  decide +kernel

theorem arows2531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2531 = true := by
  rw [show D2M8K2.u2531 = KTree.node D2M8K2.t2538 (nat_lit 6625153) (nat_lit 1573092198) (nat_lit 0) D2M8K2.t2539 from rfl, allE_node, rows2538, irow2531, rows2539]
  all_goals rfl

theorem atot2531 : totK PD2M8K2 D2M8K2.u2531 = [0, 366762596533, 926619265252, 481094188600, 36748652938, 0, 0, 0] := by
  rw [show D2M8K2.u2531 = KTree.node D2M8K2.t2538 (nat_lit 6625153) (nat_lit 1573092198) (nat_lit 0) D2M8K2.t2539 from rfl, totK_node, tot2538, tot2539]
  decide +kernel

theorem arows2533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2533 = true := by
  rw [show D2M8K2.u2533 = KTree.node D2M8K2.t2540 (nat_lit 6626636) (nat_lit 3094805894) (nat_lit 0) D2M8K2.t2541 from rfl, allE_node, rows2540, irow2533, rows2541]
  all_goals rfl

theorem atot2533 : totK PD2M8K2 D2M8K2.u2533 = [0, 246072902558, 807906383067, 634490213635, 95739837719, 1171084559, 0, 0] := by
  rw [show D2M8K2.u2533 = KTree.node D2M8K2.t2540 (nat_lit 6626636) (nat_lit 3094805894) (nat_lit 0) D2M8K2.t2541 from rfl, totK_node, tot2540, tot2541]
  decide +kernel

theorem arows2534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2534 = true := by
  rw [show D2M8K2.u2534 = KTree.node D2M8K2.t2542 (nat_lit 6628333) (nat_lit 1285768494) (nat_lit 0) D2M8K2.t2543 from rfl, allE_node, rows2542, irow2534, rows2543]
  all_goals rfl

theorem atot2534 : totK PD2M8K2 D2M8K2.u2534 = [0, 163281325637, 653885118234, 719235969284, 207481170427, 11934365838, 0, 0] := by
  rw [show D2M8K2.u2534 = KTree.node D2M8K2.t2542 (nat_lit 6628333) (nat_lit 1285768494) (nat_lit 0) D2M8K2.t2543 from rfl, totK_node, tot2542, tot2543]
  decide +kernel

theorem arows2538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2538 = true := by
  rw [show D2M8K2.u2538 = KTree.node D2M8K2.t2544 (nat_lit 6629793) (nat_lit 1858652781) (nat_lit 0) D2M8K2.t2545 from rfl, allE_node, rows2544, irow2538, rows2545]
  all_goals rfl

theorem atot2538 : totK PD2M8K2 D2M8K2.u2538 = [0, 246407789312, 830413351194, 614446036469, 74446528432, 1053411165, 0, 0] := by
  rw [show D2M8K2.u2538 = KTree.node D2M8K2.t2544 (nat_lit 6629793) (nat_lit 1858652781) (nat_lit 0) D2M8K2.t2545 from rfl, totK_node, tot2544, tot2545]
  decide +kernel

theorem arows2539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2539 = true := by
  rw [show D2M8K2.u2539 = KTree.node D2M8K2.t2546 (nat_lit 6632157) (nat_lit 1481264170) (nat_lit 0) D2M8K2.t2547 from rfl, allE_node, rows2546, irow2539, rows2547]
  all_goals rfl

theorem atot2539 : totK PD2M8K2 D2M8K2.u2539 = [0, 234306229341, 752394335002, 656377896652, 119106305887, 3667207281, 0, 0] := by
  rw [show D2M8K2.u2539 = KTree.node D2M8K2.t2546 (nat_lit 6632157) (nat_lit 1481264170) (nat_lit 0) D2M8K2.t2547 from rfl, totK_node, tot2546, tot2547]
  decide +kernel

theorem arows2541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2541 = true := by
  rw [show D2M8K2.u2541 = KTree.node D2M8K2.t2548 (nat_lit 6633682) (nat_lit 4072409954) (nat_lit 0) D2M8K2.t2549 from rfl, allE_node, rows2548, irow2541, rows2549]
  all_goals rfl

theorem atot2541 : totK PD2M8K2 D2M8K2.u2541 = [156139380478, 570163984345, 710059738616, 337352407376, 25749572841, 0, 0, 0] := by
  rw [show D2M8K2.u2541 = KTree.node D2M8K2.t2548 (nat_lit 6633682) (nat_lit 4072409954) (nat_lit 0) D2M8K2.t2549 from rfl, totK_node, tot2548, tot2549]
  decide +kernel

theorem arows2542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2542 = true := by
  rw [show D2M8K2.u2542 = KTree.node D2M8K2.t2550 (nat_lit 6637310) (nat_lit 2473640247) (nat_lit 0) D2M8K2.t2551 from rfl, allE_node, rows2550, irow2542, rows2551]
  all_goals rfl

theorem atot2542 : totK PD2M8K2 D2M8K2.u2542 = [163001771088, 746903999787, 754316958813, 119618607319, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2542 = KTree.node D2M8K2.t2550 (nat_lit 6637310) (nat_lit 2473640247) (nat_lit 0) D2M8K2.t2551 from rfl, totK_node, tot2550, tot2551]
  decide +kernel

theorem arows2545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2545 = true := by
  rw [show D2M8K2.u2545 = KTree.node D2M8K2.t2552 (nat_lit 6639801) (nat_lit 1871988145) (nat_lit 0) D2M8K2.t2553 from rfl, allE_node, rows2552, irow2545, rows2553]
  all_goals rfl

theorem atot2545 : totK PD2M8K2 D2M8K2.u2545 = [361272879641, 919860642560, 516683573121, 44609296748, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2545 = KTree.node D2M8K2.t2552 (nat_lit 6639801) (nat_lit 1871988145) (nat_lit 0) D2M8K2.t2553 from rfl, totK_node, tot2552, tot2553]
  decide +kernel

theorem arows2546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2546 = true := by
  rw [show D2M8K2.u2546 = KTree.node D2M8K2.t2554 (nat_lit 6641289) (nat_lit 1724246189) (nat_lit 0) D2M8K2.t2555 from rfl, allE_node, rows2554, irow2546, rows2555]
  all_goals rfl

theorem atot2546 : totK PD2M8K2 D2M8K2.u2546 = [65600037915, 488877534410, 847743212522, 385074670147, 29391110695, 0, 0, 0] := by
  rw [show D2M8K2.u2546 = KTree.node D2M8K2.t2554 (nat_lit 6641289) (nat_lit 1724246189) (nat_lit 0) D2M8K2.t2555 from rfl, totK_node, tot2554, tot2555]
  decide +kernel

theorem arows2548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2548 = true := by
  rw [show D2M8K2.u2548 = KTree.node D2M8K2.t2556 (nat_lit 6642577) (nat_lit 1561206651) (nat_lit 0) D2M8K2.t2557 from rfl, allE_node, rows2556, irow2548, rows2557]
  all_goals rfl

theorem atot2548 : totK PD2M8K2 D2M8K2.u2548 = [255891841462, 708125242269, 632275656923, 207920643087, 8210597527, 0, 0, 0] := by
  rw [show D2M8K2.u2548 = KTree.node D2M8K2.t2556 (nat_lit 6642577) (nat_lit 1561206651) (nat_lit 0) D2M8K2.t2557 from rfl, totK_node, tot2556, tot2557]
  decide +kernel

theorem arows2549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2549 = true := by
  rw [show D2M8K2.u2549 = KTree.node D2M8K2.t2558 (nat_lit 6644138) (nat_lit 3998795320) (nat_lit 0) D2M8K2.t2559 from rfl, allE_node, rows2558, irow2549, rows2559]
  all_goals rfl

theorem atot2549 : totK PD2M8K2 D2M8K2.u2549 = [156729864509, 727598392930, 769125482509, 133879740494, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u2549 = KTree.node D2M8K2.t2558 (nat_lit 6644138) (nat_lit 3998795320) (nat_lit 0) D2M8K2.t2559 from rfl, totK_node, tot2558, tot2559]
  decide +kernel

theorem arows2558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2558 = true := by
  rw [show D2M8K2.u2558 = KTree.node D2M8K2.t2560 (nat_lit 6645988) (nat_lit 3200513770) (nat_lit 0) D2M8K2.t2561 from rfl, allE_node, rows2560, irow2558, rows2561]
  all_goals rfl

theorem atot2558 : totK PD2M8K2 D2M8K2.u2558 = [238338324810, 693679726521, 651789093230, 200217484494, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u2558 = KTree.node D2M8K2.t2560 (nat_lit 6645988) (nat_lit 3200513770) (nat_lit 0) D2M8K2.t2561 from rfl, totK_node, tot2560, tot2561]
  decide +kernel

theorem arows2559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2559 = true := by
  rw [show D2M8K2.u2559 = KTree.node D2M8K2.t2562 (nat_lit 6647498) (nat_lit 4170681981) (nat_lit 0) D2M8K2.t2563 from rfl, allE_node, rows2562, irow2559, rows2563]
  all_goals rfl

theorem atot2559 : totK PD2M8K2 D2M8K2.u2559 = [174512448385, 756527184177, 733593618439, 126864009882, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u2559 = KTree.node D2M8K2.t2562 (nat_lit 6647498) (nat_lit 4170681981) (nat_lit 0) D2M8K2.t2563 from rfl, totK_node, tot2562, tot2563]
  decide +kernel

theorem arows2561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2561 = true := by
  rw [show D2M8K2.u2561 = KTree.node D2M8K2.t2564 (nat_lit 6649366) (nat_lit 2255222352) (nat_lit 0) D2M8K2.t2565 from rfl, allE_node, rows2564, irow2561, rows2565]
  all_goals rfl

theorem atot2561 : totK PD2M8K2 D2M8K2.u2561 = [206212718462, 655663764280, 702701055432, 219108804786, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u2561 = KTree.node D2M8K2.t2564 (nat_lit 6649366) (nat_lit 2255222352) (nat_lit 0) D2M8K2.t2565 from rfl, totK_node, tot2564, tot2565]
  decide +kernel

theorem arows2562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2562 = true := by
  rw [show D2M8K2.u2562 = KTree.node D2M8K2.t2566 (nat_lit 6650549) (nat_lit 2380192317) (nat_lit 0) D2M8K2.t2567 from rfl, allE_node, rows2566, irow2562, rows2567]
  all_goals rfl

theorem atot2562 : totK PD2M8K2 D2M8K2.u2562 = [231845271634, 801814738857, 666249355022, 99940928189, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u2562 = KTree.node D2M8K2.t2566 (nat_lit 6650549) (nat_lit 2380192317) (nat_lit 0) D2M8K2.t2567 from rfl, totK_node, tot2566, tot2567]
  decide +kernel

theorem arows2565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2565 = true := by
  rw [show D2M8K2.u2565 = KTree.node D2M8K2.t2568 (nat_lit 6656266) (nat_lit 3093336680) (nat_lit 0) D2M8K2.t2569 from rfl, allE_node, rows2568, irow2565, rows2569]
  all_goals rfl

theorem atot2565 : totK PD2M8K2 D2M8K2.u2565 = [0, 480301023434, 981548615445, 310201527246, 13624150839, 0, 0, 0] := by
  rw [show D2M8K2.u2565 = KTree.node D2M8K2.t2568 (nat_lit 6656266) (nat_lit 3093336680) (nat_lit 0) D2M8K2.t2569 from rfl, totK_node, tot2568, tot2569]
  decide +kernel

theorem arows2566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2566 = true := by
  rw [show D2M8K2.u2566 = KTree.node D2M8K2.t2570 (nat_lit 6658185) (nat_lit 1568025830) (nat_lit 0) D2M8K2.t2571 from rfl, allE_node, rows2570, irow2566, rows2571]
  all_goals rfl

theorem atot2566 : totK PD2M8K2 D2M8K2.u2566 = [0, 193977019007, 770466834553, 678430506835, 95945170186, 1138244013, 0, 0] := by
  rw [show D2M8K2.u2566 = KTree.node D2M8K2.t2570 (nat_lit 6658185) (nat_lit 1568025830) (nat_lit 0) D2M8K2.t2571 from rfl, totK_node, tot2570, tot2571]
  decide +kernel

theorem arows2568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2568 = true := by
  rw [show D2M8K2.u2568 = KTree.node D2M8K2.t2572 (nat_lit 6660708) (nat_lit 2314964743) (nat_lit 0) D2M8K2.t2573 from rfl, allE_node, rows2572, irow2568, rows2573]
  all_goals rfl

theorem atot2568 : totK PD2M8K2 D2M8K2.u2568 = [0, 336623321802, 936856893383, 511013487235, 40629964457, 0, 0, 0] := by
  rw [show D2M8K2.u2568 = KTree.node D2M8K2.t2572 (nat_lit 6660708) (nat_lit 2314964743) (nat_lit 0) D2M8K2.t2573 from rfl, totK_node, tot2572, tot2573]
  decide +kernel

theorem arows2569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2569 = true := by
  rw [show D2M8K2.u2569 = KTree.node D2M8K2.t2574 (nat_lit 6663755) (nat_lit 2660470038) (nat_lit 0) D2M8K2.t2575 from rfl, allE_node, rows2574, irow2569, rows2575]
  all_goals rfl

theorem atot2569 : totK PD2M8K2 D2M8K2.u2569 = [0, 374985609495, 927512196183, 462280683743, 29145660678, 0, 0, 0] := by
  rw [show D2M8K2.u2569 = KTree.node D2M8K2.t2574 (nat_lit 6663755) (nat_lit 2660470038) (nat_lit 0) D2M8K2.t2575 from rfl, totK_node, tot2574, tot2575]
  decide +kernel

theorem arows2573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2573 = true := by
  rw [show D2M8K2.u2573 = KTree.node D2M8K2.t2576 (nat_lit 6667090) (nat_lit 3903939869) (nat_lit 0) D2M8K2.t2577 from rfl, allE_node, rows2576, irow2573, rows2577]
  all_goals rfl

theorem atot2573 : totK PD2M8K2 D2M8K2.u2573 = [0, 380658281887, 952039173123, 447562641421, 24315071409, 0, 0, 0] := by
  rw [show D2M8K2.u2573 = KTree.node D2M8K2.t2576 (nat_lit 6667090) (nat_lit 3903939869) (nat_lit 0) D2M8K2.t2577 from rfl, totK_node, tot2576, tot2577]
  decide +kernel

theorem arows2574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2574 = true := by
  rw [show D2M8K2.u2574 = KTree.node D2M8K2.t2578 (nat_lit 6670416) (nat_lit 2629648992) (nat_lit 0) D2M8K2.t2579 from rfl, allE_node, rows2578, irow2574, rows2579]
  all_goals rfl

theorem atot2574 : totK PD2M8K2 D2M8K2.u2574 = [0, 353872636958, 932064918142, 473157007729, 30573306287, 0, 0, 0] := by
  rw [show D2M8K2.u2574 = KTree.node D2M8K2.t2578 (nat_lit 6670416) (nat_lit 2629648992) (nat_lit 0) D2M8K2.t2579 from rfl, totK_node, tot2578, tot2579]
  decide +kernel

theorem arows2576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2576 = true := by
  rw [show D2M8K2.u2576 = KTree.node D2M8K2.t2580 (nat_lit 6671882) (nat_lit 2456557910) (nat_lit 0) D2M8K2.t2581 from rfl, allE_node, rows2580, irow2576, rows2581]
  all_goals rfl

theorem atot2576 : totK PD2M8K2 D2M8K2.u2576 = [0, 151653129149, 759548612580, 731887161194, 109964006875, 1095107716, 0, 0] := by
  rw [show D2M8K2.u2576 = KTree.node D2M8K2.t2580 (nat_lit 6671882) (nat_lit 2456557910) (nat_lit 0) D2M8K2.t2581 from rfl, totK_node, tot2580, tot2581]
  decide +kernel

theorem arows2577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2577 = true := by
  rw [show D2M8K2.u2577 = KTree.node D2M8K2.t2582 (nat_lit 6677676) (nat_lit 2453254443) (nat_lit 0) D2M8K2.t2583 from rfl, allE_node, rows2582, irow2577, rows2583]
  all_goals rfl

theorem atot2577 : totK PD2M8K2 D2M8K2.u2577 = [324769904457, 735442472438, 401618721180, 234949933469, 89936393989, 3882006667, 0, 0] := by
  rw [show D2M8K2.u2577 = KTree.node D2M8K2.t2582 (nat_lit 6677676) (nat_lit 2453254443) (nat_lit 0) D2M8K2.t2583 from rfl, totK_node, tot2582, tot2583]
  decide +kernel

theorem arows2580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2580 = true := by
  rw [show D2M8K2.u2580 = KTree.node D2M8K2.t2584 (nat_lit 6679676) (nat_lit 3213582136) (nat_lit 0) D2M8K2.t2585 from rfl, allE_node, rows2584, irow2580, rows2585]
  all_goals rfl

theorem atot2580 : totK PD2M8K2 D2M8K2.u2580 = [126560246313, 688840494449, 861283266840, 151818316195, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2580 = KTree.node D2M8K2.t2584 (nat_lit 6679676) (nat_lit 3213582136) (nat_lit 0) D2M8K2.t2585 from rfl, totK_node, tot2584, tot2585]
  decide +kernel

theorem arows2581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2581 = true := by
  rw [show D2M8K2.u2581 = KTree.node D2M8K2.t2586 (nat_lit 6681664) (nat_lit 3720816941) (nat_lit 0) D2M8K2.t2587 from rfl, allE_node, rows2586, irow2581, rows2587]
  all_goals rfl

theorem atot2581 : totK PD2M8K2 D2M8K2.u2581 = [304794862632, 910732035050, 563444258333, 52630012104, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2581 = KTree.node D2M8K2.t2586 (nat_lit 6681664) (nat_lit 3720816941) (nat_lit 0) D2M8K2.t2587 from rfl, totK_node, tot2586, tot2587]
  decide +kernel

theorem arows2583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2583 = true := by
  rw [show D2M8K2.u2583 = KTree.node D2M8K2.t2588 (nat_lit 6683154) (nat_lit 3440439777) (nat_lit 0) D2M8K2.t2589 from rfl, allE_node, rows2588, irow2583, rows2589]
  all_goals rfl

theorem atot2583 : totK PD2M8K2 D2M8K2.u2583 = [0, 355530979405, 942416055977, 482722045065, 31970480552, 0, 0, 0] := by
  rw [show D2M8K2.u2583 = KTree.node D2M8K2.t2588 (nat_lit 6683154) (nat_lit 3440439777) (nat_lit 0) D2M8K2.t2589 from rfl, totK_node, tot2588, tot2589]
  decide +kernel

theorem arows2584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2584 = true := by
  rw [show D2M8K2.u2584 = KTree.node D2M8K2.t2590 (nat_lit 6684462) (nat_lit 3636075308) (nat_lit 0) D2M8K2.t2591 from rfl, allE_node, rows2590, irow2584, rows2591]
  all_goals rfl

theorem atot2584 : totK PD2M8K2 D2M8K2.u2584 = [360960179449, 878942801740, 476675770108, 84942482855, 5618966238, 0, 0, 0] := by
  rw [show D2M8K2.u2584 = KTree.node D2M8K2.t2590 (nat_lit 6684462) (nat_lit 3636075308) (nat_lit 0) D2M8K2.t2591 from rfl, totK_node, tot2590, tot2591]
  decide +kernel

theorem arows2589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2589 = true := by
  rw [show D2M8K2.u2589 = KTree.node D2M8K2.t2592 (nat_lit 6686040) (nat_lit 2767242554) (nat_lit 0) D2M8K2.t2593 from rfl, allE_node, rows2592, irow2589, rows2593]
  all_goals rfl

theorem atot2589 : totK PD2M8K2 D2M8K2.u2589 = [53275168027, 538665755971, 906463462967, 274184985125, 12904417376, 0, 0, 0] := by
  rw [show D2M8K2.u2589 = KTree.node D2M8K2.t2592 (nat_lit 6686040) (nat_lit 2767242554) (nat_lit 0) D2M8K2.t2593 from rfl, totK_node, tot2592, tot2593]
  decide +kernel

theorem arows2590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2590 = true := by
  rw [show D2M8K2.u2590 = KTree.node D2M8K2.t2594 (nat_lit 6687886) (nat_lit 3606856051) (nat_lit 0) D2M8K2.t2595 from rfl, allE_node, rows2594, irow2590, rows2595]
  all_goals rfl

theorem atot2590 : totK PD2M8K2 D2M8K2.u2590 = [338275512812, 893279106494, 534648923981, 52130250627, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2590 = KTree.node D2M8K2.t2594 (nat_lit 6687886) (nat_lit 3606856051) (nat_lit 0) D2M8K2.t2595 from rfl, totK_node, tot2594, tot2595]
  decide +kernel

theorem arows2592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2592 = true := by
  rw [show D2M8K2.u2592 = KTree.node D2M8K2.t2596 (nat_lit 6689459) (nat_lit 2815820065) (nat_lit 0) D2M8K2.t2597 from rfl, allE_node, rows2596, irow2592, rows2597]
  all_goals rfl

theorem atot2592 : totK PD2M8K2 D2M8K2.u2592 = [76209290054, 553302508409, 871172485331, 275632978464, 13084067079, 0, 0, 0] := by
  rw [show D2M8K2.u2592 = KTree.node D2M8K2.t2596 (nat_lit 6689459) (nat_lit 2815820065) (nat_lit 0) D2M8K2.t2597 from rfl, totK_node, tot2596, tot2597]
  decide +kernel

theorem arows2593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2593 = true := by
  rw [show D2M8K2.u2593 = KTree.node D2M8K2.t2598 (nat_lit 6694749) (nat_lit 1374905925) (nat_lit 0) D2M8K2.t2599 from rfl, allE_node, rows2598, irow2593, rows2599]
  all_goals rfl

theorem atot2593 : totK PD2M8K2 D2M8K2.u2593 = [348545708807, 902472335901, 535503154012, 57350692337, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2593 = KTree.node D2M8K2.t2598 (nat_lit 6694749) (nat_lit 1374905925) (nat_lit 0) D2M8K2.t2599 from rfl, totK_node, tot2598, tot2599]
  decide +kernel

theorem arows2596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2596 = true := by
  rw [show D2M8K2.u2596 = KTree.node D2M8K2.t2600 (nat_lit 6696192) (nat_lit 3523492961) (nat_lit 0) D2M8K2.t2601 from rfl, allE_node, rows2600, irow2596, rows2601]
  all_goals rfl

theorem atot2596 : totK PD2M8K2 D2M8K2.u2596 = [93768764846, 624469183777, 873010481207, 217926498923, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u2596 = KTree.node D2M8K2.t2600 (nat_lit 6696192) (nat_lit 3523492961) (nat_lit 0) D2M8K2.t2601 from rfl, totK_node, tot2600, tot2601]
  decide +kernel

theorem arows2597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2597 = true := by
  rw [show D2M8K2.u2597 = KTree.node D2M8K2.t2602 (nat_lit 6697858) (nat_lit 4124157814) (nat_lit 0) D2M8K2.t2603 from rfl, allE_node, rows2602, irow2597, rows2603]
  all_goals rfl

theorem atot2597 : totK PD2M8K2 D2M8K2.u2597 = [0, 360403831560, 939585565923, 449493667103, 26435335346, 0, 0, 0] := by
  rw [show D2M8K2.u2597 = KTree.node D2M8K2.t2602 (nat_lit 6697858) (nat_lit 4124157814) (nat_lit 0) D2M8K2.t2603 from rfl, totK_node, tot2602, tot2603]
  decide +kernel

theorem arows2599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2599 = true := by
  rw [show D2M8K2.u2599 = KTree.node D2M8K2.t2604 (nat_lit 6700073) (nat_lit 1288964498) (nat_lit 0) D2M8K2.t2605 from rfl, allE_node, rows2604, irow2599, rows2605]
  all_goals rfl

theorem atot2599 : totK PD2M8K2 D2M8K2.u2599 = [0, 181886391094, 745237605369, 765357496897, 117656550624, 1310285577, 0, 0] := by
  rw [show D2M8K2.u2599 = KTree.node D2M8K2.t2604 (nat_lit 6700073) (nat_lit 1288964498) (nat_lit 0) D2M8K2.t2605 from rfl, totK_node, tot2604, tot2605]
  decide +kernel

theorem arows2600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2600 = true := by
  rw [show D2M8K2.u2600 = KTree.node D2M8K2.t2606 (nat_lit 6702212) (nat_lit 2281262073) (nat_lit 0) D2M8K2.t2607 from rfl, allE_node, rows2606, irow2600, rows2607]
  all_goals rfl

theorem atot2600 : totK PD2M8K2 D2M8K2.u2600 = [0, 336245756359, 924204657215, 535021728409, 34573068636, 0, 0, 0] := by
  rw [show D2M8K2.u2600 = KTree.node D2M8K2.t2606 (nat_lit 6702212) (nat_lit 2281262073) (nat_lit 0) D2M8K2.t2607 from rfl, totK_node, tot2606, tot2607]
  decide +kernel

theorem arows2604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2604 = true := by
  rw [show D2M8K2.u2604 = KTree.node D2M8K2.t2608 (nat_lit 6705226) (nat_lit 3890515101) (nat_lit 0) D2M8K2.t2609 from rfl, allE_node, rows2608, irow2604, rows2609]
  all_goals rfl

theorem atot2604 : totK PD2M8K2 D2M8K2.u2604 = [0, 378397281088, 916712998082, 465592631724, 39796824652, 0, 0, 0] := by
  rw [show D2M8K2.u2604 = KTree.node D2M8K2.t2608 (nat_lit 6705226) (nat_lit 3890515101) (nat_lit 0) D2M8K2.t2609 from rfl, totK_node, tot2608, tot2609]
  decide +kernel

theorem arows2605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2605 = true := by
  rw [show D2M8K2.u2605 = KTree.node D2M8K2.t2610 (nat_lit 6706979) (nat_lit 2679186684) (nat_lit 0) D2M8K2.t2611 from rfl, allE_node, rows2610, irow2605, rows2611]
  all_goals rfl

theorem atot2605 : totK PD2M8K2 D2M8K2.u2605 = [0, 99673874037, 636032223649, 837793381115, 178499370623, 4879840392, 0, 0] := by
  rw [show D2M8K2.u2605 = KTree.node D2M8K2.t2610 (nat_lit 6706979) (nat_lit 2679186684) (nat_lit 0) D2M8K2.t2611 from rfl, totK_node, tot2610, tot2611]
  decide +kernel

theorem arows2607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2607 = true := by
  rw [show D2M8K2.u2607 = KTree.node D2M8K2.t2612 (nat_lit 6709097) (nat_lit 1394550905) (nat_lit 0) D2M8K2.t2613 from rfl, allE_node, rows2612, irow2607, rows2613]
  all_goals rfl

theorem atot2607 : totK PD2M8K2 D2M8K2.u2607 = [0, 347982319087, 930536792304, 503645217153, 36722714610, 0, 0, 0] := by
  rw [show D2M8K2.u2607 = KTree.node D2M8K2.t2612 (nat_lit 6709097) (nat_lit 1394550905) (nat_lit 0) D2M8K2.t2613 from rfl, totK_node, tot2612, tot2613]
  decide +kernel

theorem arows2608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2608 = true := by
  rw [show D2M8K2.u2608 = KTree.node D2M8K2.t2614 (nat_lit 6710852) (nat_lit 1848201973) (nat_lit 0) D2M8K2.t2615 from rfl, allE_node, rows2614, irow2608, rows2615]
  all_goals rfl

theorem atot2608 : totK PD2M8K2 D2M8K2.u2608 = [0, 102015507908, 651862218874, 815459627054, 177727491953, 4931404646, 0, 0] := by
  rw [show D2M8K2.u2608 = KTree.node D2M8K2.t2614 (nat_lit 6710852) (nat_lit 1848201973) (nat_lit 0) D2M8K2.t2615 from rfl, totK_node, tot2614, tot2615]
  decide +kernel

theorem arows2611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2611 = true := by
  rw [show D2M8K2.u2611 = KTree.node D2M8K2.t2616 (nat_lit 6715882) (nat_lit 3919400347) (nat_lit 0) D2M8K2.t2617 from rfl, allE_node, rows2616, irow2611, rows2617]
  all_goals rfl

theorem atot2611 : totK PD2M8K2 D2M8K2.u2611 = [0, 338756553918, 915329907852, 536275181871, 44939479557, 0, 0, 0] := by
  rw [show D2M8K2.u2611 = KTree.node D2M8K2.t2616 (nat_lit 6715882) (nat_lit 3919400347) (nat_lit 0) D2M8K2.t2617 from rfl, totK_node, tot2616, tot2617]
  decide +kernel

theorem arows2612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2612 = true := by
  rw [show D2M8K2.u2612 = KTree.node D2M8K2.t2618 (nat_lit 6717520) (nat_lit 3366352207) (nat_lit 0) D2M8K2.t2619 from rfl, allE_node, rows2618, irow2612, rows2619]
  all_goals rfl

theorem atot2612 : totK PD2M8K2 D2M8K2.u2612 = [0, 0, 417278989180, 945695799912, 357165439958, 15977695833, 0, 0] := by
  rw [show D2M8K2.u2612 = KTree.node D2M8K2.t2618 (nat_lit 6717520) (nat_lit 3366352207) (nat_lit 0) D2M8K2.t2619 from rfl, totK_node, tot2618, tot2619]
  decide +kernel

theorem arows2614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2614 = true := by
  rw [show D2M8K2.u2614 = KTree.node D2M8K2.t2620 (nat_lit 6764216) (nat_lit 3865940388) (nat_lit 0) D2M8K2.t2621 from rfl, allE_node, rows2620, irow2614, rows2621]
  all_goals rfl

theorem atot2614 : totK PD2M8K2 D2M8K2.u2614 = [0, 363236630449, 924009923828, 507297603502, 48687212756, 5773472233, 0, 0] := by
  rw [show D2M8K2.u2614 = KTree.node D2M8K2.t2620 (nat_lit 6764216) (nat_lit 3865940388) (nat_lit 0) D2M8K2.t2621 from rfl, totK_node, tot2620, tot2621]
  decide +kernel

theorem arows2615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2615 = true := by
  rw [show D2M8K2.u2615 = KTree.node D2M8K2.t2622 (nat_lit 6765664) (nat_lit 3131211972) (nat_lit 0) D2M8K2.t2623 from rfl, allE_node, rows2622, irow2615, rows2623]
  all_goals rfl

theorem atot2615 : totK PD2M8K2 D2M8K2.u2615 = [0, 86698232267, 510647119324, 829496166571, 373296645297, 29394892645, 0, 0] := by
  rw [show D2M8K2.u2615 = KTree.node D2M8K2.t2622 (nat_lit 6765664) (nat_lit 3131211972) (nat_lit 0) D2M8K2.t2623 from rfl, totK_node, tot2622, tot2623]
  decide +kernel

theorem arows2621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2621 = true := by
  rw [show D2M8K2.u2621 = KTree.node D2M8K2.t2624 (nat_lit 6766948) (nat_lit 3769647798) (nat_lit 0) D2M8K2.t2625 from rfl, allE_node, rows2624, irow2621, rows2625]
  all_goals rfl

theorem atot2621 : totK PD2M8K2 D2M8K2.u2621 = [0, 245379484481, 690492210336, 678552096693, 219328783182, 8214505460, 0, 0] := by
  rw [show D2M8K2.u2621 = KTree.node D2M8K2.t2624 (nat_lit 6766948) (nat_lit 3769647798) (nat_lit 0) D2M8K2.t2625 from rfl, totK_node, tot2624, tot2625]
  decide +kernel

theorem arows2622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2622 = true := by
  rw [show D2M8K2.u2622 = KTree.node D2M8K2.t2626 (nat_lit 6768438) (nat_lit 2895363039) (nat_lit 0) D2M8K2.t2627 from rfl, allE_node, rows2626, irow2622, rows2627]
  all_goals rfl

theorem atot2622 : totK PD2M8K2 D2M8K2.u2622 = [0, 177379182490, 780168987639, 734955055976, 106469256627, 0, 0, 0] := by
  rw [show D2M8K2.u2622 = KTree.node D2M8K2.t2626 (nat_lit 6768438) (nat_lit 2895363039) (nat_lit 0) D2M8K2.t2627 from rfl, totK_node, tot2626, tot2627]
  decide +kernel

theorem arows2624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2624 = true := by
  rw [show D2M8K2.u2624 = KTree.node D2M8K2.t2628 (nat_lit 6770310) (nat_lit 3819484394) (nat_lit 0) D2M8K2.t2629 from rfl, allE_node, rows2628, irow2624, rows2629]
  all_goals rfl

theorem atot2624 : totK PD2M8K2 D2M8K2.u2624 = [0, 212879150761, 662050603028, 709872993132, 208910897406, 8706415949, 0, 0] := by
  rw [show D2M8K2.u2624 = KTree.node D2M8K2.t2628 (nat_lit 6770310) (nat_lit 3819484394) (nat_lit 0) D2M8K2.t2629 from rfl, totK_node, tot2628, tot2629]
  decide +kernel

theorem arows2625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2625 = true := by
  rw [show D2M8K2.u2625 = KTree.node D2M8K2.t2630 (nat_lit 6771826) (nat_lit 4010860176) (nat_lit 0) D2M8K2.t2631 from rfl, allE_node, rows2630, irow2625, rows2631]
  all_goals rfl

theorem atot2625 : totK PD2M8K2 D2M8K2.u2625 = [0, 210088301155, 803360774681, 693546018714, 95048668155, 0, 0, 0] := by
  rw [show D2M8K2.u2625 = KTree.node D2M8K2.t2630 (nat_lit 6771826) (nat_lit 4010860176) (nat_lit 0) D2M8K2.t2631 from rfl, totK_node, tot2630, tot2631]
  decide +kernel

theorem arows2628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2628 = true := by
  rw [show D2M8K2.u2628 = KTree.node D2M8K2.t2632 (nat_lit 6773545) (nat_lit 1452665944) (nat_lit 0) D2M8K2.t2633 from rfl, allE_node, rows2632, irow2628, rows2633]
  all_goals rfl

theorem atot2628 : totK PD2M8K2 D2M8K2.u2628 = [0, 168997499532, 636896048112, 751822699637, 226640769051, 8824320960, 0, 0] := by
  rw [show D2M8K2.u2628 = KTree.node D2M8K2.t2632 (nat_lit 6773545) (nat_lit 1452665944) (nat_lit 0) D2M8K2.t2633 from rfl, totK_node, tot2632, tot2633]
  decide +kernel

theorem arows2629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2629 = true := by
  rw [show D2M8K2.u2629 = KTree.node D2M8K2.t2634 (nat_lit 6774941) (nat_lit 2292250904) (nat_lit 0) D2M8K2.t2635 from rfl, allE_node, rows2634, irow2629, rows2635]
  all_goals rfl

theorem atot2629 : totK PD2M8K2 D2M8K2.u2629 = [0, 248487329549, 829516279442, 635751375646, 84008567264, 0, 0, 0] := by
  rw [show D2M8K2.u2629 = KTree.node D2M8K2.t2634 (nat_lit 6774941) (nat_lit 2292250904) (nat_lit 0) D2M8K2.t2635 from rfl, totK_node, tot2634, tot2635]
  decide +kernel

theorem arows2631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2631 = true := by
  rw [show D2M8K2.u2631 = KTree.node D2M8K2.t2636 (nat_lit 6777238) (nat_lit 3553329980) (nat_lit 0) D2M8K2.t2637 from rfl, allE_node, rows2636, irow2631, rows2637]
  all_goals rfl

theorem atot2631 : totK PD2M8K2 D2M8K2.u2631 = [0, 212521809544, 748446504755, 724315372307, 144741629816, 2498823382, 0, 0] := by
  rw [show D2M8K2.u2631 = KTree.node D2M8K2.t2636 (nat_lit 6777238) (nat_lit 3553329980) (nat_lit 0) D2M8K2.t2637 from rfl, totK_node, tot2636, tot2637]
  decide +kernel

theorem arows2632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2632 = true := by
  rw [show D2M8K2.u2632 = KTree.node D2M8K2.t2638 (nat_lit 6778741) (nat_lit 1223971308) (nat_lit 0) D2M8K2.t2639 from rfl, allE_node, rows2638, irow2632, rows2639]
  all_goals rfl

theorem atot2632 : totK PD2M8K2 D2M8K2.u2632 = [0, 210202840850, 787834539677, 705324856174, 103159255632, 0, 0, 0] := by
  rw [show D2M8K2.u2632 = KTree.node D2M8K2.t2638 (nat_lit 6778741) (nat_lit 1223971308) (nat_lit 0) D2M8K2.t2639 from rfl, totK_node, tot2638, tot2639]
  decide +kernel

theorem arows2636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2636 = true := by
  rw [show D2M8K2.u2636 = KTree.node D2M8K2.t2640 (nat_lit 6780463) (nat_lit 2415566519) (nat_lit 0) D2M8K2.t2641 from rfl, allE_node, rows2640, irow2636, rows2641]
  all_goals rfl

theorem atot2636 : totK PD2M8K2 D2M8K2.u2636 = [0, 0, 357507326297, 923430972959, 481781392656, 37675614470, 0, 0] := by
  rw [show D2M8K2.u2636 = KTree.node D2M8K2.t2640 (nat_lit 6780463) (nat_lit 2415566519) (nat_lit 0) D2M8K2.t2641 from rfl, totK_node, tot2640, tot2641]
  decide +kernel

theorem arows2637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2637 = true := by
  rw [show D2M8K2.u2637 = KTree.node D2M8K2.t2642 (nat_lit 6785348) (nat_lit 3388110699) (nat_lit 0) D2M8K2.t2643 from rfl, allE_node, rows2642, irow2637, rows2643]
  all_goals rfl

theorem atot2637 : totK PD2M8K2 D2M8K2.u2637 = [0, 0, 315888484598, 913558981355, 548469857680, 45464875329, 0, 0] := by
  rw [show D2M8K2.u2637 = KTree.node D2M8K2.t2642 (nat_lit 6785348) (nat_lit 3388110699) (nat_lit 0) D2M8K2.t2643 from rfl, totK_node, tot2642, tot2643]
  decide +kernel

theorem arows2639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2639 = true := by
  rw [show D2M8K2.u2639 = KTree.node D2M8K2.t2644 (nat_lit 6786829) (nat_lit 710169599) (nat_lit 0) D2M8K2.t2645 from rfl, allE_node, rows2644, irow2639, rows2645]
  all_goals rfl

theorem atot2639 : totK PD2M8K2 D2M8K2.u2639 = [0, 0, 0, 368317008638, 947560170417, 440221186418, 30397782892, 0] := by
  rw [show D2M8K2.u2639 = KTree.node D2M8K2.t2644 (nat_lit 6786829) (nat_lit 710169599) (nat_lit 0) D2M8K2.t2645 from rfl, totK_node, tot2644, tot2645]
  decide +kernel

theorem arows2640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2640 = true := by
  rw [show D2M8K2.u2640 = KTree.node D2M8K2.t2646 (nat_lit 6788164) (nat_lit 3869846782) (nat_lit 0) D2M8K2.t2647 from rfl, allE_node, rows2646, irow2640, rows2647]
  all_goals rfl

theorem atot2640 : totK PD2M8K2 D2M8K2.u2640 = [0, 0, 354304806914, 854899609755, 470175386549, 99570888044, 6524090962, 0] := by
  rw [show D2M8K2.u2640 = KTree.node D2M8K2.t2646 (nat_lit 6788164) (nat_lit 3869846782) (nat_lit 0) D2M8K2.t2647 from rfl, totK_node, tot2646, tot2647]
  decide +kernel

theorem arows2643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2643 = true := by
  rw [show D2M8K2.u2643 = KTree.node D2M8K2.t2648 (nat_lit 6789956) (nat_lit 3341709948) (nat_lit 0) D2M8K2.t2649 from rfl, allE_node, rows2648, irow2643, rows2649]
  all_goals rfl

theorem atot2643 : totK PD2M8K2 D2M8K2.u2643 = [0, 0, 87313293544, 610150269224, 877012102440, 188143965628, 5067863418, 0] := by
  rw [show D2M8K2.u2643 = KTree.node D2M8K2.t2648 (nat_lit 6789956) (nat_lit 3341709948) (nat_lit 0) D2M8K2.t2649 from rfl, totK_node, tot2648, tot2649]
  decide +kernel

theorem arows2644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2644 = true := by
  rw [show D2M8K2.u2644 = KTree.node D2M8K2.t2650 (nat_lit 6792018) (nat_lit 3480840810) (nat_lit 0) D2M8K2.t2651 from rfl, allE_node, rows2650, irow2644, rows2651]
  all_goals rfl

theorem atot2644 : totK PD2M8K2 D2M8K2.u2644 = [0, 0, 385277600650, 947732920873, 444491479702, 31012102688, 0, 0] := by
  rw [show D2M8K2.u2644 = KTree.node D2M8K2.t2650 (nat_lit 6792018) (nat_lit 3480840810) (nat_lit 0) D2M8K2.t2651 from rfl, totK_node, tot2650, tot2651]
  decide +kernel

theorem arows2646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2646 = true := by
  rw [show D2M8K2.u2646 = KTree.node D2M8K2.t2652 (nat_lit 6793869) (nat_lit 1097472976) (nat_lit 0) D2M8K2.t2653 from rfl, allE_node, rows2652, irow2646, rows2653]
  all_goals rfl

theorem atot2646 : totK PD2M8K2 D2M8K2.u2646 = [0, 0, 64198478510, 607004752454, 864818246860, 195078615179, 5126512042, 0] := by
  rw [show D2M8K2.u2646 = KTree.node D2M8K2.t2652 (nat_lit 6793869) (nat_lit 1097472976) (nat_lit 0) D2M8K2.t2653 from rfl, totK_node, tot2652, tot2653]
  decide +kernel

theorem arows2647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2647 = true := by
  rw [show D2M8K2.u2647 = KTree.node D2M8K2.t2654 (nat_lit 6795317) (nat_lit 2305983902) (nat_lit 0) D2M8K2.t2655 from rfl, allE_node, rows2654, irow2647, rows2655]
  all_goals rfl

theorem atot2647 : totK PD2M8K2 D2M8K2.u2647 = [0, 0, 350651136667, 918125912327, 497276627428, 35927619316, 0, 0] := by
  rw [show D2M8K2.u2647 = KTree.node D2M8K2.t2654 (nat_lit 6795317) (nat_lit 2305983902) (nat_lit 0) D2M8K2.t2655 from rfl, totK_node, tot2654, tot2655]
  decide +kernel

theorem arows2652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2652 = true := by
  rw [show D2M8K2.u2652 = KTree.node D2M8K2.t2656 (nat_lit 6797406) (nat_lit 3841478617) (nat_lit 0) D2M8K2.t2657 from rfl, allE_node, rows2656, irow2652, rows2657]
  all_goals rfl

theorem atot2652 : totK PD2M8K2 D2M8K2.u2652 = [0, 0, 156583173236, 722391749722, 795447552468, 132975374956, 1392055030, 0] := by
  rw [show D2M8K2.u2652 = KTree.node D2M8K2.t2656 (nat_lit 6797406) (nat_lit 3841478617) (nat_lit 0) D2M8K2.t2657 from rfl, totK_node, tot2656, tot2657]
  decide +kernel

theorem arows2653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2653 = true := by
  rw [show D2M8K2.u2653 = KTree.node D2M8K2.t2658 (nat_lit 6798991) (nat_lit 2339908243) (nat_lit 0) D2M8K2.t2659 from rfl, allE_node, rows2658, irow2653, rows2659]
  all_goals rfl

theorem atot2653 : totK PD2M8K2 D2M8K2.u2653 = [0, 0, 262921938247, 871198554552, 613347277635, 52525522229, 0, 0] := by
  rw [show D2M8K2.u2653 = KTree.node D2M8K2.t2658 (nat_lit 6798991) (nat_lit 2339908243) (nat_lit 0) D2M8K2.t2659 from rfl, totK_node, tot2658, tot2659]
  decide +kernel

theorem arows2655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2655 = true := by
  rw [show D2M8K2.u2655 = KTree.node D2M8K2.t2660 (nat_lit 6801189) (nat_lit 605639684) (nat_lit 0) D2M8K2.t2661 from rfl, allE_node, rows2660, irow2655, rows2661]
  all_goals rfl

theorem atot2655 : totK PD2M8K2 D2M8K2.u2655 = [0, 159221153091, 335783779590, 367467491469, 647933892801, 231198753070, 9139067247, 0] := by
  rw [show D2M8K2.u2655 = KTree.node D2M8K2.t2660 (nat_lit 6801189) (nat_lit 605639684) (nat_lit 0) D2M8K2.t2661 from rfl, totK_node, tot2660, tot2661]
  decide +kernel

theorem arows2656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2656 = true := by
  rw [show D2M8K2.u2656 = KTree.node D2M8K2.t2662 (nat_lit 6803064) (nat_lit 2835662639) (nat_lit 0) D2M8K2.t2663 from rfl, allE_node, rows2662, irow2656, rows2663]
  all_goals rfl

theorem atot2656 : totK PD2M8K2 D2M8K2.u2656 = [0, 163632999621, 754244344658, 737526541022, 105331784006, 1275377855, 0, 0] := by
  rw [show D2M8K2.u2656 = KTree.node D2M8K2.t2662 (nat_lit 6803064) (nat_lit 2835662639) (nat_lit 0) D2M8K2.t2663 from rfl, totK_node, tot2662, tot2663]
  decide +kernel

theorem arows2659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2659 = true := by
  rw [show D2M8K2.u2659 = KTree.node D2M8K2.t2664 (nat_lit 6805579) (nat_lit 1385257488) (nat_lit 0) D2M8K2.t2665 from rfl, allE_node, rows2664, irow2659, rows2665]
  all_goals rfl

theorem atot2659 : totK PD2M8K2 D2M8K2.u2659 = [0, 342827442907, 898900605983, 543477106926, 55084290422, 0, 0, 0] := by
  rw [show D2M8K2.u2659 = KTree.node D2M8K2.t2664 (nat_lit 6805579) (nat_lit 1385257488) (nat_lit 0) D2M8K2.t2665 from rfl, totK_node, tot2664, tot2665]
  decide +kernel

theorem arows2660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2660 = true := by
  rw [show D2M8K2.u2660 = KTree.node D2M8K2.t2666 (nat_lit 6807099) (nat_lit 3681907593) (nat_lit 0) D2M8K2.t2667 from rfl, allE_node, rows2666, irow2660, rows2667]
  all_goals rfl

theorem atot2660 : totK PD2M8K2 D2M8K2.u2660 = [0, 88183717169, 511515403165, 820096579596, 367858499286, 29321085627, 0, 0] := by
  rw [show D2M8K2.u2660 = KTree.node D2M8K2.t2666 (nat_lit 6807099) (nat_lit 3681907593) (nat_lit 0) D2M8K2.t2667 from rfl, totK_node, tot2666, tot2667]
  decide +kernel

theorem arows2662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2662 = true := by
  rw [show D2M8K2.u2662 = KTree.node D2M8K2.t2668 (nat_lit 6808382) (nat_lit 3262056161) (nat_lit 0) D2M8K2.t2669 from rfl, allE_node, rows2668, irow2662, rows2669]
  all_goals rfl

theorem atot2662 : totK PD2M8K2 D2M8K2.u2662 = [0, 223803873244, 678850597630, 691266965050, 219007849878, 8166240555, 0, 0] := by
  rw [show D2M8K2.u2662 = KTree.node D2M8K2.t2668 (nat_lit 6808382) (nat_lit 3262056161) (nat_lit 0) D2M8K2.t2669 from rfl, totK_node, tot2668, tot2669]
  decide +kernel

theorem arows2663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2663 = true := by
  rw [show D2M8K2.u2663 = KTree.node D2M8K2.t2670 (nat_lit 6809834) (nat_lit 3867383029) (nat_lit 0) D2M8K2.t2671 from rfl, allE_node, rows2670, irow2663, rows2671]
  all_goals rfl

theorem atot2663 : totK PD2M8K2 D2M8K2.u2663 = [0, 216297240599, 789022441816, 683252710401, 110502312810, 1164319620, 0, 0] := by
  rw [show D2M8K2.u2663 = KTree.node D2M8K2.t2670 (nat_lit 6809834) (nat_lit 3867383029) (nat_lit 0) D2M8K2.t2671 from rfl, totK_node, tot2670, tot2671]
  decide +kernel

theorem arows2667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2667 = true := by
  rw [show D2M8K2.u2667 = KTree.node D2M8K2.t2672 (nat_lit 6811523) (nat_lit 2889759130) (nat_lit 0) D2M8K2.t2673 from rfl, allE_node, rows2672, irow2667, rows2673]
  all_goals rfl

theorem atot2667 : totK PD2M8K2 D2M8K2.u2667 = [0, 163678763449, 644637735815, 743124729205, 220740195812, 11885407614, 0, 0] := by
  rw [show D2M8K2.u2667 = KTree.node D2M8K2.t2672 (nat_lit 6811523) (nat_lit 2889759130) (nat_lit 0) D2M8K2.t2673 from rfl, totK_node, tot2672, tot2673]
  decide +kernel

theorem arows2668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2668 = true := by
  rw [show D2M8K2.u2668 = KTree.node D2M8K2.t2674 (nat_lit 6816390) (nat_lit 3416420969) (nat_lit 0) D2M8K2.t2675 from rfl, allE_node, rows2674, irow2668, rows2675]
  all_goals rfl

theorem atot2668 : totK PD2M8K2 D2M8K2.u2668 = [0, 247014953925, 794776166083, 640289498568, 97279183706, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2668 = KTree.node D2M8K2.t2674 (nat_lit 6816390) (nat_lit 3416420969) (nat_lit 0) D2M8K2.t2675 from rfl, totK_node, tot2674, tot2675]
  decide +kernel

theorem arows2670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2670 = true := by
  rw [show D2M8K2.u2670 = KTree.node D2M8K2.t2676 (nat_lit 6818364) (nat_lit 2935904622) (nat_lit 0) D2M8K2.t2677 from rfl, allE_node, rows2676, irow2670, rows2677]
  all_goals rfl

theorem atot2670 : totK PD2M8K2 D2M8K2.u2670 = [0, 183090000448, 720135180577, 753273076403, 150953341344, 3884009855, 0, 0] := by
  rw [show D2M8K2.u2670 = KTree.node D2M8K2.t2676 (nat_lit 6818364) (nat_lit 2935904622) (nat_lit 0) D2M8K2.t2677 from rfl, totK_node, tot2676, tot2677]
  decide +kernel

theorem arows2671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2671 = true := by
  rw [show D2M8K2.u2671 = KTree.node D2M8K2.t2678 (nat_lit 6820206) (nat_lit 3998267349) (nat_lit 0) D2M8K2.t2679 from rfl, allE_node, rows2678, irow2671, rows2679]
  all_goals rfl

theorem atot2671 : totK PD2M8K2 D2M8K2.u2671 = [0, 233209878786, 788416348358, 672937586949, 111203375143, 1232398321, 0, 0] := by
  rw [show D2M8K2.u2671 = KTree.node D2M8K2.t2678 (nat_lit 6820206) (nat_lit 3998267349) (nat_lit 0) D2M8K2.t2679 from rfl, totK_node, tot2678, tot2679]
  decide +kernel

theorem arows2674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2674 = true := by
  rw [show D2M8K2.u2674 = KTree.node D2M8K2.t2680 (nat_lit 6821938) (nat_lit 4023268641) (nat_lit 0) D2M8K2.t2681 from rfl, allE_node, rows2680, irow2674, rows2681]
  all_goals rfl

theorem atot2674 : totK PD2M8K2 D2M8K2.u2674 = [0, 0, 406108614943, 957039061298, 386947365366, 19090867562, 0, 0] := by
  rw [show D2M8K2.u2674 = KTree.node D2M8K2.t2680 (nat_lit 6821938) (nat_lit 4023268641) (nat_lit 0) D2M8K2.t2681 from rfl, totK_node, tot2680, tot2681]
  decide +kernel

theorem arows2675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2675 = true := by
  rw [show D2M8K2.u2675 = KTree.node D2M8K2.t2682 (nat_lit 6826012) (nat_lit 3875912919) (nat_lit 0) D2M8K2.t2683 from rfl, allE_node, rows2682, irow2675, rows2683]
  all_goals rfl

theorem atot2675 : totK PD2M8K2 D2M8K2.u2675 = [0, 0, 417281563143, 953672958391, 404535402406, 29570000507, 0, 0] := by
  rw [show D2M8K2.u2675 = KTree.node D2M8K2.t2682 (nat_lit 6826012) (nat_lit 3875912919) (nat_lit 0) D2M8K2.t2683 from rfl, totK_node, tot2682, tot2683]
  decide +kernel

theorem arows2677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2677 = true := by
  rw [show D2M8K2.u2677 = KTree.node D2M8K2.t2684 (nat_lit 6827249) (nat_lit 1531274883) (nat_lit 0) D2M8K2.t2685 from rfl, allE_node, rows2684, irow2677, rows2685]
  all_goals rfl

theorem atot2677 : totK PD2M8K2 D2M8K2.u2677 = [0, 0, 341861218813, 931193424016, 483213535979, 29207550335, 0, 0] := by
  rw [show D2M8K2.u2677 = KTree.node D2M8K2.t2684 (nat_lit 6827249) (nat_lit 1531274883) (nat_lit 0) D2M8K2.t2685 from rfl, totK_node, tot2684, tot2685]
  decide +kernel

theorem arows2678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2678 = true := by
  rw [show D2M8K2.u2678 = KTree.node D2M8K2.t2686 (nat_lit 6830497) (nat_lit 1553212496) (nat_lit 0) D2M8K2.t2687 from rfl, allE_node, rows2686, irow2678, rows2687]
  all_goals rfl

theorem atot2678 : totK PD2M8K2 D2M8K2.u2678 = [0, 0, 265618885128, 864478624682, 602678850158, 49566964819, 0, 0] := by
  rw [show D2M8K2.u2678 = KTree.node D2M8K2.t2686 (nat_lit 6830497) (nat_lit 1553212496) (nat_lit 0) D2M8K2.t2687 from rfl, totK_node, tot2686, tot2687]
  decide +kernel

theorem arows2685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2685 = true := by
  rw [show D2M8K2.u2685 = KTree.node D2M8K2.t2688 (nat_lit 6832349) (nat_lit 2218991997) (nat_lit 0) D2M8K2.t2689 from rfl, allE_node, rows2688, irow2685, rows2689]
  all_goals rfl

theorem atot2685 : totK PD2M8K2 D2M8K2.u2685 = [0, 0, 198096895259, 681750104860, 692745243153, 172542398167, 5320761635, 0] := by
  rw [show D2M8K2.u2685 = KTree.node D2M8K2.t2688 (nat_lit 6832349) (nat_lit 2218991997) (nat_lit 0) D2M8K2.t2689 from rfl, totK_node, tot2688, tot2689]
  decide +kernel

theorem arows2686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2686 = true := by
  rw [show D2M8K2.u2686 = KTree.node D2M8K2.t2690 (nat_lit 6837229) (nat_lit 1127593384) (nat_lit 0) D2M8K2.t2691 from rfl, allE_node, rows2690, irow2686, rows2691]
  all_goals rfl

theorem atot2686 : totK PD2M8K2 D2M8K2.u2686 = [0, 0, 210403521034, 882442838305, 623577555528, 48082877313, 0, 0] := by
  rw [show D2M8K2.u2686 = KTree.node D2M8K2.t2690 (nat_lit 6837229) (nat_lit 1127593384) (nat_lit 0) D2M8K2.t2691 from rfl, totK_node, tot2690, tot2691]
  decide +kernel

theorem arows2688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2688 = true := by
  rw [show D2M8K2.u2688 = KTree.node D2M8K2.t2692 (nat_lit 6839838) (nat_lit 3813476699) (nat_lit 0) D2M8K2.t2693 from rfl, allE_node, rows2692, irow2688, rows2693]
  all_goals rfl

theorem atot2688 : totK PD2M8K2 D2M8K2.u2688 = [0, 0, 321323263661, 814624423225, 557029714372, 82178687012, 1225787871, 0] := by
  rw [show D2M8K2.u2688 = KTree.node D2M8K2.t2692 (nat_lit 6839838) (nat_lit 3813476699) (nat_lit 0) D2M8K2.t2693 from rfl, totK_node, tot2692, tot2693]
  decide +kernel

theorem arows2689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2689 = true := by
  rw [show D2M8K2.u2689 = KTree.node D2M8K2.t2694 (nat_lit 6843752) (nat_lit 3595937398) (nat_lit 0) D2M8K2.t2695 from rfl, allE_node, rows2694, irow2689, rows2695]
  all_goals rfl

theorem atot2689 : totK PD2M8K2 D2M8K2.u2689 = [0, 271560262698, 751855346640, 556675854591, 191738217391, 13065910070, 0, 0] := by
  rw [show D2M8K2.u2689 = KTree.node D2M8K2.t2694 (nat_lit 6843752) (nat_lit 3595937398) (nat_lit 0) D2M8K2.t2695 from rfl, totK_node, tot2694, tot2695]
  decide +kernel

theorem arows2692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2692 = true := by
  rw [show D2M8K2.u2692 = KTree.node D2M8K2.t2696 (nat_lit 6845771) (nat_lit 1909739430) (nat_lit 0) D2M8K2.t2697 from rfl, allE_node, rows2696, irow2692, rows2697]
  all_goals rfl

theorem atot2692 : totK PD2M8K2 D2M8K2.u2692 = [0, 145020162831, 723507012239, 814863168590, 129626623582, 1310517177, 0, 0] := by
  rw [show D2M8K2.u2692 = KTree.node D2M8K2.t2696 (nat_lit 6845771) (nat_lit 1909739430) (nat_lit 0) D2M8K2.t2697 from rfl, totK_node, tot2696, tot2697]
  decide +kernel

theorem arows2693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2693 = true := by
  rw [show D2M8K2.u2693 = KTree.node D2M8K2.t2698 (nat_lit 6847531) (nat_lit 1805480763) (nat_lit 0) D2M8K2.t2699 from rfl, allE_node, rows2698, irow2693, rows2699]
  all_goals rfl

theorem atot2693 : totK PD2M8K2 D2M8K2.u2693 = [0, 337472723262, 906985799367, 526054206575, 51172944255, 0, 0, 0] := by
  rw [show D2M8K2.u2693 = KTree.node D2M8K2.t2698 (nat_lit 6847531) (nat_lit 1805480763) (nat_lit 0) D2M8K2.t2699 from rfl, totK_node, tot2698, tot2699]
  decide +kernel

theorem arows2695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2695 = true := by
  rw [show D2M8K2.u2695 = KTree.node D2M8K2.t2700 (nat_lit 6849027) (nat_lit 3655480701) (nat_lit 0) D2M8K2.t2701 from rfl, allE_node, rows2700, irow2695, rows2701]
  all_goals rfl

theorem atot2695 : totK PD2M8K2 D2M8K2.u2695 = [0, 0, 389176348250, 946748836525, 448416668795, 30729496402, 0, 0] := by
  rw [show D2M8K2.u2695 = KTree.node D2M8K2.t2700 (nat_lit 6849027) (nat_lit 3655480701) (nat_lit 0) D2M8K2.t2701 from rfl, totK_node, tot2700, tot2701]
  decide +kernel

theorem arows2696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2696 = true := by
  rw [show D2M8K2.u2696 = KTree.node D2M8K2.t2702 (nat_lit 6853754) (nat_lit 4109651873) (nat_lit 0) D2M8K2.t2703 from rfl, allE_node, rows2702, irow2696, rows2703]
  all_goals rfl

theorem atot2696 : totK PD2M8K2 D2M8K2.u2696 = [0, 351891582662, 849065873348, 496890776625, 117258490665, 6756203132, 0, 0] := by
  rw [show D2M8K2.u2696 = KTree.node D2M8K2.t2702 (nat_lit 6853754) (nat_lit 4109651873) (nat_lit 0) D2M8K2.t2703 from rfl, totK_node, tot2702, tot2703]
  decide +kernel

theorem arows2700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2700 = true := by
  rw [show D2M8K2.u2700 = KTree.node D2M8K2.t2704 (nat_lit 6855244) (nat_lit 2897167708) (nat_lit 0) D2M8K2.t2705 from rfl, allE_node, rows2704, irow2700, rows2705]
  all_goals rfl

theorem atot2700 : totK PD2M8K2 D2M8K2.u2700 = [0, 88383717769, 615914408787, 858792352546, 229058068881, 9649412842, 0, 0] := by
  rw [show D2M8K2.u2700 = KTree.node D2M8K2.t2704 (nat_lit 6855244) (nat_lit 2897167708) (nat_lit 0) D2M8K2.t2705 from rfl, totK_node, tot2704, tot2705]
  decide +kernel

theorem arows2701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2701 = true := by
  rw [show D2M8K2.u2701 = KTree.node D2M8K2.t2706 (nat_lit 6857060) (nat_lit 3324329341) (nat_lit 0) D2M8K2.t2707 from rfl, allE_node, rows2706, irow2701, rows2707]
  all_goals rfl

theorem atot2701 : totK PD2M8K2 D2M8K2.u2701 = [0, 300845862405, 783283010425, 580003887013, 118262291937, 3546687146, 0, 0] := by
  rw [show D2M8K2.u2701 = KTree.node D2M8K2.t2706 (nat_lit 6857060) (nat_lit 3324329341) (nat_lit 0) D2M8K2.t2707 from rfl, totK_node, tot2706, tot2707]
  decide +kernel

theorem arows2703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2703 = true := by
  rw [show D2M8K2.u2703 = KTree.node D2M8K2.t2708 (nat_lit 6858580) (nat_lit 2450513499) (nat_lit 0) D2M8K2.t2709 from rfl, allE_node, rows2708, irow2703, rows2709]
  all_goals rfl

theorem atot2703 : totK PD2M8K2 D2M8K2.u2703 = [0, 106005114803, 730276666986, 830585045727, 128358860583, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2703 = KTree.node D2M8K2.t2708 (nat_lit 6858580) (nat_lit 2450513499) (nat_lit 0) D2M8K2.t2709 from rfl, totK_node, tot2708, tot2709]
  decide +kernel

theorem arows2704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2704 = true := by
  rw [show D2M8K2.u2704 = KTree.node D2M8K2.t2710 (nat_lit 6860619) (nat_lit 3773292463) (nat_lit 0) D2M8K2.t2711 from rfl, allE_node, rows2710, irow2704, rows2711]
  all_goals rfl

theorem atot2704 : totK PD2M8K2 D2M8K2.u2704 = [0, 324049755146, 824166894049, 543991371297, 110615963715, 3884009855, 0, 0] := by
  rw [show D2M8K2.u2704 = KTree.node D2M8K2.t2710 (nat_lit 6860619) (nat_lit 3773292463) (nat_lit 0) D2M8K2.t2711 from rfl, totK_node, tot2710, tot2711]
  decide +kernel

theorem arows2707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2707 = true := by
  rw [show D2M8K2.u2707 = KTree.node D2M8K2.t2712 (nat_lit 6862135) (nat_lit 1289556515) (nat_lit 0) D2M8K2.t2713 from rfl, allE_node, rows2712, irow2707, rows2713]
  all_goals rfl

theorem atot2707 : totK PD2M8K2 D2M8K2.u2707 = [0, 92333346222, 604116796716, 868755990139, 224708133555, 3563464126, 0, 0] := by
  rw [show D2M8K2.u2707 = KTree.node D2M8K2.t2712 (nat_lit 6862135) (nat_lit 1289556515) (nat_lit 0) D2M8K2.t2713 from rfl, totK_node, tot2712, tot2713]
  decide +kernel

theorem arows2708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2708 = true := by
  rw [show D2M8K2.u2708 = KTree.node D2M8K2.t2714 (nat_lit 6864486) (nat_lit 3866735348) (nat_lit 0) D2M8K2.t2715 from rfl, allE_node, rows2714, irow2708, rows2715]
  all_goals rfl

theorem atot2708 : totK PD2M8K2 D2M8K2.u2708 = [0, 0, 449530916019, 958299350979, 344582344349, 16723542245, 0, 0] := by
  rw [show D2M8K2.u2708 = KTree.node D2M8K2.t2714 (nat_lit 6864486) (nat_lit 3866735348) (nat_lit 0) D2M8K2.t2715 from rfl, totK_node, tot2714, tot2715]
  decide +kernel

theorem arows2710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2710 = true := by
  rw [show D2M8K2.u2710 = KTree.node D2M8K2.t2716 (nat_lit 6868032) (nat_lit 3117747415) (nat_lit 0) D2M8K2.t2717 from rfl, allE_node, rows2716, irow2710, rows2717]
  all_goals rfl

theorem atot2710 : totK PD2M8K2 D2M8K2.u2710 = [0, 0, 389310866479, 931991911457, 467557492100, 35016748412, 0, 0] := by
  rw [show D2M8K2.u2710 = KTree.node D2M8K2.t2716 (nat_lit 6868032) (nat_lit 3117747415) (nat_lit 0) D2M8K2.t2717 from rfl, totK_node, tot2716, tot2717]
  decide +kernel

theorem arows2711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2711 = true := by
  rw [show D2M8K2.u2711 = KTree.node D2M8K2.t2718 (nat_lit 6874472) (nat_lit 3423378229) (nat_lit 0) D2M8K2.t2719 from rfl, allE_node, rows2718, irow2711, rows2719]
  all_goals rfl

theorem atot2711 : totK PD2M8K2 D2M8K2.u2711 = [0, 0, 347588479009, 900163715048, 505467683667, 39036443051, 0, 0] := by
  rw [show D2M8K2.u2711 = KTree.node D2M8K2.t2718 (nat_lit 6874472) (nat_lit 3423378229) (nat_lit 0) D2M8K2.t2719 from rfl, totK_node, tot2718, tot2719]
  decide +kernel

theorem arows2716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2716 = true := by
  rw [show D2M8K2.u2716 = KTree.node D2M8K2.t2720 (nat_lit 6876097) (nat_lit 1037310177) (nat_lit 0) D2M8K2.t2721 from rfl, allE_node, rows2720, irow2716, rows2721]
  all_goals rfl

theorem atot2716 : totK PD2M8K2 D2M8K2.u2716 = [0, 0, 86235217742, 639154157201, 828355815626, 186034485593, 5352782441, 0] := by
  rw [show D2M8K2.u2716 = KTree.node D2M8K2.t2720 (nat_lit 6876097) (nat_lit 1037310177) (nat_lit 0) D2M8K2.t2721 from rfl, totK_node, tot2720, tot2721]
  decide +kernel

theorem arows2717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2717 = true := by
  rw [show D2M8K2.u2717 = KTree.node D2M8K2.t2722 (nat_lit 6877971) (nat_lit 3686328055) (nat_lit 0) D2M8K2.t2723 from rfl, allE_node, rows2722, irow2717, rows2723]
  all_goals rfl

theorem atot2717 : totK PD2M8K2 D2M8K2.u2717 = [0, 0, 352811503173, 923428382349, 483272543058, 34896750196, 0, 0] := by
  rw [show D2M8K2.u2717 = KTree.node D2M8K2.t2722 (nat_lit 6877971) (nat_lit 3686328055) (nat_lit 0) D2M8K2.t2723 from rfl, totK_node, tot2722, tot2723]
  decide +kernel

theorem arows2719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2719 = true := by
  rw [show D2M8K2.u2719 = KTree.node D2M8K2.t2724 (nat_lit 6880075) (nat_lit 1748528036) (nat_lit 0) D2M8K2.t2725 from rfl, allE_node, rows2724, irow2719, rows2725]
  all_goals rfl

theorem atot2719 : totK PD2M8K2 D2M8K2.u2719 = [0, 0, 156444569742, 757474166034, 727912571185, 98596610633, 1271866555, 0] := by
  rw [show D2M8K2.u2719 = KTree.node D2M8K2.t2724 (nat_lit 6880075) (nat_lit 1748528036) (nat_lit 0) D2M8K2.t2725 from rfl, totK_node, tot2724, tot2725]
  decide +kernel

theorem arows2720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2720 = true := by
  rw [show D2M8K2.u2720 = KTree.node D2M8K2.t2726 (nat_lit 6881880) (nat_lit 3543820183) (nat_lit 0) D2M8K2.t2727 from rfl, allE_node, rows2726, irow2720, rows2727]
  all_goals rfl

theorem atot2720 : totK PD2M8K2 D2M8K2.u2720 = [0, 70882335681, 411108255038, 815512740662, 473622535254, 39330056903, 0, 0] := by
  rw [show D2M8K2.u2720 = KTree.node D2M8K2.t2726 (nat_lit 6881880) (nat_lit 3543820183) (nat_lit 0) D2M8K2.t2727 from rfl, totK_node, tot2726, tot2727]
  decide +kernel

theorem arows2723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2723 = true := by
  rw [show D2M8K2.u2723 = KTree.node D2M8K2.t2728 (nat_lit 6885456) (nat_lit 3388576300) (nat_lit 0) D2M8K2.t2729 from rfl, allE_node, rows2728, irow2723, rows2729]
  all_goals rfl

theorem atot2723 : totK PD2M8K2 D2M8K2.u2723 = [0, 250270423695, 829277685153, 593805152338, 78032269117, 1209030869, 0, 0] := by
  rw [show D2M8K2.u2723 = KTree.node D2M8K2.t2728 (nat_lit 6885456) (nat_lit 3388576300) (nat_lit 0) D2M8K2.t2729 from rfl, totK_node, tot2728, tot2729]
  decide +kernel

theorem arows2724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2724 = true := by
  rw [show D2M8K2.u2724 = KTree.node D2M8K2.t2730 (nat_lit 6888299) (nat_lit 2675646481) (nat_lit 0) D2M8K2.t2731 from rfl, allE_node, rows2730, irow2724, rows2731]
  all_goals rfl

theorem atot2724 : totK PD2M8K2 D2M8K2.u2724 = [0, 268187714162, 829753619742, 651834266199, 71678534372, 0, 0, 0] := by
  rw [show D2M8K2.u2724 = KTree.node D2M8K2.t2730 (nat_lit 6888299) (nat_lit 2675646481) (nat_lit 0) D2M8K2.t2731 from rfl, totK_node, tot2730, tot2731]
  decide +kernel

theorem arows2726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2726 = true := by
  rw [show D2M8K2.u2726 = KTree.node D2M8K2.t2732 (nat_lit 6889523) (nat_lit 2966653545) (nat_lit 0) D2M8K2.t2733 from rfl, allE_node, rows2732, irow2726, rows2733]
  all_goals rfl

theorem atot2726 : totK PD2M8K2 D2M8K2.u2726 = [0, 162551884278, 655571047038, 720148032309, 262027536003, 24257630845, 0, 0] := by
  rw [show D2M8K2.u2726 = KTree.node D2M8K2.t2732 (nat_lit 6889523) (nat_lit 2966653545) (nat_lit 0) D2M8K2.t2733 from rfl, totK_node, tot2732, tot2733]
  decide +kernel

theorem arows2727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2727 = true := by
  rw [show D2M8K2.u2727 = KTree.node D2M8K2.t2734 (nat_lit 6891023) (nat_lit 2155955534) (nat_lit 0) D2M8K2.t2735 from rfl, allE_node, rows2734, irow2727, rows2735]
  all_goals rfl

theorem atot2727 : totK PD2M8K2 D2M8K2.u2727 = [0, 160211361594, 561955759351, 740759575805, 312117019433, 13233657716, 0, 0] := by
  rw [show D2M8K2.u2727 = KTree.node D2M8K2.t2734 (nat_lit 6891023) (nat_lit 2155955534) (nat_lit 0) D2M8K2.t2735 from rfl, totK_node, tot2734, tot2735]
  decide +kernel

theorem arows2731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2731 = true := by
  rw [show D2M8K2.u2731 = KTree.node D2M8K2.t2736 (nat_lit 6892506) (nat_lit 3731163821) (nat_lit 0) D2M8K2.t2737 from rfl, allE_node, rows2736, irow2731, rows2737]
  all_goals rfl

theorem atot2731 : totK PD2M8K2 D2M8K2.u2731 = [0, 248348952843, 816300017235, 629214559280, 89833397920, 1164319620, 0, 0] := by
  rw [show D2M8K2.u2731 = KTree.node D2M8K2.t2736 (nat_lit 6892506) (nat_lit 3731163821) (nat_lit 0) D2M8K2.t2737 from rfl, totK_node, tot2736, tot2737]
  decide +kernel

theorem arows2732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2732 = true := by
  rw [show D2M8K2.u2732 = KTree.node D2M8K2.t2738 (nat_lit 6894237) (nat_lit 1527034918) (nat_lit 0) D2M8K2.t2739 from rfl, allE_node, rows2738, irow2732, rows2739]
  all_goals rfl

theorem atot2732 : totK PD2M8K2 D2M8K2.u2732 = [0, 128998824005, 603208287320, 794693658695, 239262467067, 11885407614, 0, 0] := by
  rw [show D2M8K2.u2732 = KTree.node D2M8K2.t2738 (nat_lit 6894237) (nat_lit 1527034918) (nat_lit 0) D2M8K2.t2739 from rfl, totK_node, tot2738, tot2739]
  decide +kernel

theorem arows2734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2734 = true := by
  rw [show D2M8K2.u2734 = KTree.node D2M8K2.t2740 (nat_lit 6895921) (nat_lit 1373115841) (nat_lit 0) D2M8K2.t2741 from rfl, allE_node, rows2740, irow2734, rows2741]
  all_goals rfl

theorem atot2734 : totK PD2M8K2 D2M8K2.u2734 = [0, 283851949190, 858329814506, 600759316008, 62090850616, 0, 0, 0] := by
  rw [show D2M8K2.u2734 = KTree.node D2M8K2.t2740 (nat_lit 6895921) (nat_lit 1373115841) (nat_lit 0) D2M8K2.t2741 from rfl, totK_node, tot2740, tot2741]
  decide +kernel

theorem arows2735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2735 = true := by
  rw [show D2M8K2.u2735 = KTree.node D2M8K2.t2742 (nat_lit 6897646) (nat_lit 3240504785) (nat_lit 0) D2M8K2.t2743 from rfl, allE_node, rows2742, irow2735, rows2743]
  all_goals rfl

theorem atot2735 : totK PD2M8K2 D2M8K2.u2735 = [0, 100625761363, 550804593227, 821207026914, 277059230094, 13250685261, 0, 0] := by
  rw [show D2M8K2.u2735 = KTree.node D2M8K2.t2742 (nat_lit 6897646) (nat_lit 3240504785) (nat_lit 0) D2M8K2.t2743 from rfl, totK_node, tot2742, tot2743]
  decide +kernel

theorem arows2738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2738 = true := by
  rw [show D2M8K2.u2738 = KTree.node D2M8K2.t2744 (nat_lit 6899046) (nat_lit 3848496419) (nat_lit 0) D2M8K2.t2745 from rfl, allE_node, rows2744, irow2738, rows2745]
  all_goals rfl

theorem atot2738 : totK PD2M8K2 D2M8K2.u2738 = [0, 337432228733, 918939376099, 529818878535, 44149204265, 0, 0, 0] := by
  rw [show D2M8K2.u2738 = KTree.node D2M8K2.t2744 (nat_lit 6899046) (nat_lit 3848496419) (nat_lit 0) D2M8K2.t2745 from rfl, totK_node, tot2744, tot2745]
  decide +kernel

theorem arows2739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2739 = true := by
  rw [show D2M8K2.u2739 = KTree.node D2M8K2.t2746 (nat_lit 6900854) (nat_lit 3852983560) (nat_lit 0) D2M8K2.t2747 from rfl, allE_node, rows2746, irow2739, rows2747]
  all_goals rfl

theorem atot2739 : totK PD2M8K2 D2M8K2.u2739 = [0, 0, 507662501104, 1006734005411, 264914094069, 6350335412, 0, 0] := by
  rw [show D2M8K2.u2739 = KTree.node D2M8K2.t2746 (nat_lit 6900854) (nat_lit 3852983560) (nat_lit 0) D2M8K2.t2747 from rfl, totK_node, tot2746, tot2747]
  decide +kernel

theorem arows2741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2741 = true := by
  rw [show D2M8K2.u2741 = KTree.node D2M8K2.t2748 (nat_lit 6906344) (nat_lit 3933518588) (nat_lit 0) D2M8K2.t2749 from rfl, allE_node, rows2748, irow2741, rows2749]
  all_goals rfl

theorem atot2741 : totK PD2M8K2 D2M8K2.u2741 = [0, 0, 402359904199, 953597532969, 395517389165, 25351430514, 0, 0] := by
  rw [show D2M8K2.u2741 = KTree.node D2M8K2.t2748 (nat_lit 6906344) (nat_lit 3933518588) (nat_lit 0) D2M8K2.t2749 from rfl, totK_node, tot2748, tot2749]
  decide +kernel

theorem arows2742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2742 = true := by
  rw [show D2M8K2.u2742 = KTree.node D2M8K2.t2750 (nat_lit 6909872) (nat_lit 3810331381) (nat_lit 0) D2M8K2.t2751 from rfl, allE_node, rows2750, irow2742, rows2751]
  all_goals rfl

theorem atot2742 : totK PD2M8K2 D2M8K2.u2742 = [0, 0, 344572793289, 946414212810, 454795737750, 23725585656, 0, 0] := by
  rw [show D2M8K2.u2742 = KTree.node D2M8K2.t2750 (nat_lit 6909872) (nat_lit 3810331381) (nat_lit 0) D2M8K2.t2751 from rfl, totK_node, tot2750, tot2751]
  decide +kernel

theorem arows2748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2748 = true := by
  rw [show D2M8K2.u2748 = KTree.node D2M8K2.t2752 (nat_lit 6913183) (nat_lit 2135783548) (nat_lit 0) D2M8K2.t2753 from rfl, allE_node, rows2752, irow2748, rows2753]
  all_goals rfl

theorem atot2748 : totK PD2M8K2 D2M8K2.u2748 = [0, 0, 392456011569, 946873423548, 430756243663, 23439331458, 0, 0] := by
  rw [show D2M8K2.u2748 = KTree.node D2M8K2.t2752 (nat_lit 6913183) (nat_lit 2135783548) (nat_lit 0) D2M8K2.t2753 from rfl, totK_node, tot2752, tot2753]
  decide +kernel

theorem arows2749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2749 = true := by
  rw [show D2M8K2.u2749 = KTree.node D2M8K2.t2754 (nat_lit 6916538) (nat_lit 4027313416) (nat_lit 0) D2M8K2.t2755 from rfl, allE_node, rows2754, irow2749, rows2755]
  all_goals rfl

theorem atot2749 : totK PD2M8K2 D2M8K2.u2749 = [0, 0, 360932449222, 948455815059, 469263445615, 24808259618, 0, 0] := by
  rw [show D2M8K2.u2749 = KTree.node D2M8K2.t2754 (nat_lit 6916538) (nat_lit 4027313416) (nat_lit 0) D2M8K2.t2755 from rfl, totK_node, tot2754, tot2755]
  decide +kernel

theorem arows2751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2751 = true := by
  rw [show D2M8K2.u2751 = KTree.node D2M8K2.t2756 (nat_lit 6919545) (nat_lit 1853179180) (nat_lit 0) D2M8K2.t2757 from rfl, allE_node, rows2756, irow2751, rows2757]
  all_goals rfl

theorem atot2751 : totK PD2M8K2 D2M8K2.u2751 = [0, 0, 375007143037, 925006828362, 449303127349, 32547243808, 0, 0] := by
  rw [show D2M8K2.u2751 = KTree.node D2M8K2.t2756 (nat_lit 6919545) (nat_lit 1853179180) (nat_lit 0) D2M8K2.t2757 from rfl, totK_node, tot2756, tot2757]
  decide +kernel

theorem arows2752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2752 = true := by
  rw [show D2M8K2.u2752 = KTree.node D2M8K2.t2758 (nat_lit 6921339) (nat_lit 2389537736) (nat_lit 0) D2M8K2.t2759 from rfl, allE_node, rows2758, irow2752, rows2759]
  all_goals rfl

theorem atot2752 : totK PD2M8K2 D2M8K2.u2752 = [0, 71794763572, 185415848150, 623051843264, 740290968905, 135846678413, 1429815836, 0] := by
  rw [show D2M8K2.u2752 = KTree.node D2M8K2.t2758 (nat_lit 6921339) (nat_lit 2389537736) (nat_lit 0) D2M8K2.t2759 from rfl, totK_node, tot2758, tot2759]
  decide +kernel

theorem arows2755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2755 = true := by
  rw [show D2M8K2.u2755 = KTree.node D2M8K2.t2760 (nat_lit 6927294) (nat_lit 3794723290) (nat_lit 0) D2M8K2.t2761 from rfl, allE_node, rows2760, irow2755, rows2761]
  all_goals rfl

theorem atot2755 : totK PD2M8K2 D2M8K2.u2755 = [0, 252975140885, 817491456967, 627582750746, 90249140537, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2755 = KTree.node D2M8K2.t2760 (nat_lit 6927294) (nat_lit 3794723290) (nat_lit 0) D2M8K2.t2761 from rfl, totK_node, tot2760, tot2761]
  decide +kernel

theorem arows2756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2756 = true := by
  rw [show D2M8K2.u2756 = KTree.node D2M8K2.t2762 (nat_lit 6929803) (nat_lit 1742990493) (nat_lit 0) D2M8K2.t2763 from rfl, allE_node, rows2762, irow2756, rows2763]
  all_goals rfl

theorem atot2756 : totK PD2M8K2 D2M8K2.u2756 = [0, 268379818248, 834336596927, 658196541096, 76416569487, 0, 0, 0] := by
  rw [show D2M8K2.u2756 = KTree.node D2M8K2.t2762 (nat_lit 6929803) (nat_lit 1742990493) (nat_lit 0) D2M8K2.t2763 from rfl, totK_node, tot2762, tot2763]
  decide +kernel

theorem arows2758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2758 = true := by
  rw [show D2M8K2.u2758 = KTree.node D2M8K2.t2764 (nat_lit 6931335) (nat_lit 3639394546) (nat_lit 0) D2M8K2.t2765 from rfl, allE_node, rows2764, irow2758, rows2765]
  all_goals rfl

theorem atot2758 : totK PD2M8K2 D2M8K2.u2758 = [0, 162975290697, 642442474694, 712609901289, 278212386070, 25316940874, 0, 0] := by
  rw [show D2M8K2.u2758 = KTree.node D2M8K2.t2764 (nat_lit 6931335) (nat_lit 3639394546) (nat_lit 0) D2M8K2.t2765 from rfl, totK_node, tot2764, tot2765]
  decide +kernel

theorem arows2759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2759 = true := by
  rw [show D2M8K2.u2759 = KTree.node D2M8K2.t2766 (nat_lit 6932532) (nat_lit 2973815768) (nat_lit 0) D2M8K2.t2767 from rfl, allE_node, rows2766, irow2759, rows2767]
  all_goals rfl

theorem atot2759 : totK PD2M8K2 D2M8K2.u2759 = [0, 165400824333, 595569215538, 747096991877, 291623818712, 12163764758, 0, 0] := by
  rw [show D2M8K2.u2759 = KTree.node D2M8K2.t2766 (nat_lit 6932532) (nat_lit 2973815768) (nat_lit 0) D2M8K2.t2767 from rfl, totK_node, tot2766, tot2767]
  decide +kernel

theorem arows2763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2763 = true := by
  rw [show D2M8K2.u2763 = KTree.node D2M8K2.t2768 (nat_lit 6934083) (nat_lit 2559169081) (nat_lit 0) D2M8K2.t2769 from rfl, allE_node, rows2768, irow2763, rows2769]
  all_goals rfl

theorem atot2763 : totK PD2M8K2 D2M8K2.u2763 = [0, 248834523143, 800693459600, 650187451949, 101082247773, 1129969115, 0, 0] := by
  rw [show D2M8K2.u2763 = KTree.node D2M8K2.t2768 (nat_lit 6934083) (nat_lit 2559169081) (nat_lit 0) D2M8K2.t2769 from rfl, totK_node, tot2768, tot2769]
  decide +kernel

theorem arows2764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2764 = true := by
  rw [show D2M8K2.u2764 = KTree.node D2M8K2.t2770 (nat_lit 6935819) (nat_lit 1513049680) (nat_lit 0) D2M8K2.t2771 from rfl, allE_node, rows2770, irow2764, rows2771]
  all_goals rfl

theorem atot2764 : totK PD2M8K2 D2M8K2.u2764 = [0, 165497800747, 656427883942, 758631472137, 207873887330, 7938575017, 0, 0] := by
  rw [show D2M8K2.u2764 = KTree.node D2M8K2.t2770 (nat_lit 6935819) (nat_lit 1513049680) (nat_lit 0) D2M8K2.t2771 from rfl, totK_node, tot2770, tot2771]
  decide +kernel

theorem arows2766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2766 = true := by
  rw [show D2M8K2.u2766 = KTree.node D2M8K2.t2772 (nat_lit 6937516) (nat_lit 3232530593) (nat_lit 0) D2M8K2.t2773 from rfl, allE_node, rows2772, irow2766, rows2773]
  all_goals rfl

theorem atot2766 : totK PD2M8K2 D2M8K2.u2766 = [0, 248987002119, 794224038212, 653748370792, 104747294954, 1162515529, 0, 0] := by
  rw [show D2M8K2.u2766 = KTree.node D2M8K2.t2772 (nat_lit 6937516) (nat_lit 3232530593) (nat_lit 0) D2M8K2.t2773 from rfl, totK_node, tot2772, tot2773]
  decide +kernel

theorem arows2767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2767 = true := by
  rw [show D2M8K2.u2767 = KTree.node D2M8K2.t2774 (nat_lit 6939244) (nat_lit 2609777809) (nat_lit 0) D2M8K2.t2775 from rfl, allE_node, rows2774, irow2767, rows2775]
  all_goals rfl

theorem atot2767 : totK PD2M8K2 D2M8K2.u2767 = [0, 153566919969, 653447513830, 772914215321, 219131181292, 8017271805, 0, 0] := by
  rw [show D2M8K2.u2767 = KTree.node D2M8K2.t2774 (nat_lit 6939244) (nat_lit 2609777809) (nat_lit 0) D2M8K2.t2775 from rfl, totK_node, tot2774, tot2775]
  decide +kernel

theorem arows2770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2770 = true := by
  rw [show D2M8K2.u2770 = KTree.node D2M8K2.t2776 (nat_lit 6944077) (nat_lit 1003616553) (nat_lit 0) D2M8K2.t2777 from rfl, allE_node, rows2776, irow2770, rows2777]
  all_goals rfl

theorem atot2770 : totK PD2M8K2 D2M8K2.u2770 = [0, 285717665046, 874790699329, 613611484746, 59404358909, 0, 0, 0] := by
  rw [show D2M8K2.u2770 = KTree.node D2M8K2.t2776 (nat_lit 6944077) (nat_lit 1003616553) (nat_lit 0) D2M8K2.t2777 from rfl, totK_node, tot2776, tot2777]
  decide +kernel

theorem arows2771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2771 = true := by
  rw [show D2M8K2.u2771 = KTree.node D2M8K2.t2778 (nat_lit 6945722) (nat_lit 4204749349) (nat_lit 0) D2M8K2.t2779 from rfl, allE_node, rows2778, irow2771, rows2779]
  all_goals rfl

theorem atot2771 : totK PD2M8K2 D2M8K2.u2771 = [0, 0, 407390286265, 954809097364, 394775298427, 21951339401, 0, 0] := by
  rw [show D2M8K2.u2771 = KTree.node D2M8K2.t2778 (nat_lit 6945722) (nat_lit 4204749349) (nat_lit 0) D2M8K2.t2779 from rfl, totK_node, tot2778, tot2779]
  decide +kernel

theorem arows2773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2773 = true := by
  rw [show D2M8K2.u2773 = KTree.node D2M8K2.t2780 (nat_lit 6948143) (nat_lit 2778802946) (nat_lit 0) D2M8K2.t2781 from rfl, allE_node, rows2780, irow2773, rows2781]
  all_goals rfl

theorem atot2773 : totK PD2M8K2 D2M8K2.u2773 = [0, 0, 463303047383, 944110076438, 384135102085, 27292364086, 0, 0] := by
  rw [show D2M8K2.u2773 = KTree.node D2M8K2.t2780 (nat_lit 6948143) (nat_lit 2778802946) (nat_lit 0) D2M8K2.t2781 from rfl, totK_node, tot2780, tot2781]
  decide +kernel

theorem arows2774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2774 = true := by
  rw [show D2M8K2.u2774 = KTree.node D2M8K2.t2782 (nat_lit 6951516) (nat_lit 2862799498) (nat_lit 0) D2M8K2.t2783 from rfl, allE_node, rows2782, irow2774, rows2783]
  all_goals rfl

theorem atot2774 : totK PD2M8K2 D2M8K2.u2774 = [0, 0, 409782916509, 958444637257, 427765440894, 18961538022, 0, 0] := by
  rw [show D2M8K2.u2774 = KTree.node D2M8K2.t2782 (nat_lit 6951516) (nat_lit 2862799498) (nat_lit 0) D2M8K2.t2783 from rfl, totK_node, tot2782, tot2783]
  decide +kernel

theorem arows2779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2779 = true := by
  rw [show D2M8K2.u2779 = KTree.node D2M8K2.t2784 (nat_lit 6954821) (nat_lit 2352245897) (nat_lit 0) D2M8K2.t2785 from rfl, allE_node, rows2784, irow2779, rows2785]
  all_goals rfl

theorem atot2779 : totK PD2M8K2 D2M8K2.u2779 = [0, 0, 244822200128, 853075832845, 640065530868, 55269890733, 0, 0] := by
  rw [show D2M8K2.u2779 = KTree.node D2M8K2.t2784 (nat_lit 6954821) (nat_lit 2352245897) (nat_lit 0) D2M8K2.t2785 from rfl, totK_node, tot2784, tot2785]
  decide +kernel

theorem arows2780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2780 = true := by
  rw [show D2M8K2.u2780 = KTree.node D2M8K2.t2786 (nat_lit 6957081) (nat_lit 1340214373) (nat_lit 0) D2M8K2.t2787 from rfl, allE_node, rows2786, irow2780, rows2787]
  all_goals rfl

theorem atot2780 : totK PD2M8K2 D2M8K2.u2780 = [0, 0, 253434975277, 768910377550, 653412519497, 102892340418, 1323630408, 0] := by
  rw [show D2M8K2.u2780 = KTree.node D2M8K2.t2786 (nat_lit 6957081) (nat_lit 1340214373) (nat_lit 0) D2M8K2.t2787 from rfl, totK_node, tot2786, tot2787]
  decide +kernel

theorem arows2782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2782 = true := by
  rw [show D2M8K2.u2782 = KTree.node D2M8K2.t2788 (nat_lit 6958666) (nat_lit 3851399924) (nat_lit 0) D2M8K2.t2789 from rfl, allE_node, rows2788, irow2782, rows2789]
  all_goals rfl

theorem atot2782 : totK PD2M8K2 D2M8K2.u2782 = [0, 0, 154822114785, 775123282907, 741647080045, 102809574154, 1332468113, 0] := by
  rw [show D2M8K2.u2782 = KTree.node D2M8K2.t2788 (nat_lit 6958666) (nat_lit 3851399924) (nat_lit 0) D2M8K2.t2789 from rfl, totK_node, tot2788, tot2789]
  decide +kernel

theorem arows2783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2783 = true := by
  rw [show D2M8K2.u2783 = KTree.node D2M8K2.t2790 (nat_lit 6964373) (nat_lit 2083958128) (nat_lit 0) D2M8K2.t2791 from rfl, allE_node, rows2790, irow2783, rows2791]
  all_goals rfl

theorem atot2783 : totK PD2M8K2 D2M8K2.u2783 = [0, 0, 339281473064, 888006427193, 523654119954, 43785499791, 0, 0] := by
  rw [show D2M8K2.u2783 = KTree.node D2M8K2.t2790 (nat_lit 6964373) (nat_lit 2083958128) (nat_lit 0) D2M8K2.t2791 from rfl, totK_node, tot2790, tot2791]
  decide +kernel

theorem arows2786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2786 = true := by
  rw [show D2M8K2.u2786 = KTree.node D2M8K2.t2792 (nat_lit 6965998) (nat_lit 4033889481) (nat_lit 0) D2M8K2.t2793 from rfl, allE_node, rows2792, irow2786, rows2793]
  all_goals rfl

theorem atot2786 : totK PD2M8K2 D2M8K2.u2786 = [0, 0, 93211394557, 652214433674, 862469862654, 167918058395, 2465685039, 0] := by
  rw [show D2M8K2.u2786 = KTree.node D2M8K2.t2792 (nat_lit 6965998) (nat_lit 4033889481) (nat_lit 0) D2M8K2.t2793 from rfl, totK_node, tot2792, tot2793]
  decide +kernel

theorem arows2787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2787 = true := by
  rw [show D2M8K2.u2787 = KTree.node D2M8K2.t2794 (nat_lit 6968009) (nat_lit 1633674070) (nat_lit 0) D2M8K2.t2795 from rfl, allE_node, rows2794, irow2787, rows2795]
  all_goals rfl

theorem atot2787 : totK PD2M8K2 D2M8K2.u2787 = [335404452611, 813700341897, 359538631078, 39156983180, 134712615267, 97752493894, 7068066807, 0] := by
  rw [show D2M8K2.u2787 = KTree.node D2M8K2.t2794 (nat_lit 6968009) (nat_lit 1633674070) (nat_lit 0) D2M8K2.t2795 from rfl, totK_node, tot2794, tot2795]
  decide +kernel

theorem arows2789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2789 = true := by
  rw [show D2M8K2.u2789 = KTree.node D2M8K2.t2796 (nat_lit 6969271) (nat_lit 2032444923) (nat_lit 0) D2M8K2.t2797 from rfl, allE_node, rows2796, irow2789, rows2797]
  all_goals rfl

theorem atot2789 : totK PD2M8K2 D2M8K2.u2789 = [86391183362, 677851043877, 885152902401, 149225324909, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2789 = KTree.node D2M8K2.t2796 (nat_lit 6969271) (nat_lit 2032444923) (nat_lit 0) D2M8K2.t2797 from rfl, totK_node, tot2796, tot2797]
  decide +kernel

theorem arows2790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2790 = true := by
  rw [show D2M8K2.u2790 = KTree.node D2M8K2.t2798 (nat_lit 6974824) (nat_lit 3901240501) (nat_lit 0) D2M8K2.t2799 from rfl, allE_node, rows2798, irow2790, rows2799]
  all_goals rfl

theorem atot2790 : totK PD2M8K2 D2M8K2.u2790 = [384291589612, 922442021236, 464484597349, 39861248480, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2790 = KTree.node D2M8K2.t2798 (nat_lit 6974824) (nat_lit 3901240501) (nat_lit 0) D2M8K2.t2799 from rfl, totK_node, tot2798, tot2799]
  decide +kernel

theorem arows2794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2794 = true := by
  rw [show D2M8K2.u2794 = KTree.node D2M8K2.t2800 (nat_lit 6976362) (nat_lit 3009790087) (nat_lit 0) D2M8K2.t2801 from rfl, allE_node, rows2800, irow2794, rows2801]
  all_goals rfl

theorem atot2794 : totK PD2M8K2 D2M8K2.u2794 = [40212644391, 520152206772, 919841385137, 280754519114, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u2794 = KTree.node D2M8K2.t2800 (nat_lit 6976362) (nat_lit 3009790087) (nat_lit 0) D2M8K2.t2801 from rfl, totK_node, tot2800, tot2801]
  decide +kernel

theorem arows2795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2795 = true := by
  rw [show D2M8K2.u2795 = KTree.node D2M8K2.t2802 (nat_lit 6981638) (nat_lit 3777044431) (nat_lit 0) D2M8K2.t2803 from rfl, allE_node, rows2802, irow2795, rows2803]
  all_goals rfl

theorem atot2795 : totK PD2M8K2 D2M8K2.u2795 = [333364614163, 874057755362, 530758771817, 58665640198, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2795 = KTree.node D2M8K2.t2802 (nat_lit 6981638) (nat_lit 3777044431) (nat_lit 0) D2M8K2.t2803 from rfl, totK_node, tot2802, tot2803]
  decide +kernel

theorem arows2797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2797 = true := by
  rw [show D2M8K2.u2797 = KTree.node D2M8K2.t2804 (nat_lit 6983241) (nat_lit 1905615121) (nat_lit 0) D2M8K2.t2805 from rfl, allE_node, rows2804, irow2797, rows2805]
  all_goals rfl

theorem atot2797 : totK PD2M8K2 D2M8K2.u2797 = [86770772907, 617164772801, 870683908252, 201593321043, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u2797 = KTree.node D2M8K2.t2804 (nat_lit 6983241) (nat_lit 1905615121) (nat_lit 0) D2M8K2.t2805 from rfl, totK_node, tot2804, tot2805]
  decide +kernel

theorem arows2798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2798 = true := by
  rw [show D2M8K2.u2798 = KTree.node D2M8K2.t2806 (nat_lit 6985256) (nat_lit 3717866187) (nat_lit 0) D2M8K2.t2807 from rfl, allE_node, rows2806, irow2798, rows2807]
  all_goals rfl

theorem atot2798 : totK PD2M8K2 D2M8K2.u2798 = [381114732072, 935507683263, 468441562863, 36154162773, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2798 = KTree.node D2M8K2.t2806 (nat_lit 6985256) (nat_lit 3717866187) (nat_lit 0) D2M8K2.t2807 from rfl, totK_node, tot2806, tot2807]
  decide +kernel

theorem arows2801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2801 = true := by
  rw [show D2M8K2.u2801 = KTree.node D2M8K2.t2808 (nat_lit 6986945) (nat_lit 2222962290) (nat_lit 0) D2M8K2.t2809 from rfl, allE_node, rows2808, irow2801, rows2809]
  all_goals rfl

theorem atot2801 : totK PD2M8K2 D2M8K2.u2801 = [0, 473603484842, 972143603892, 325949717414, 9938656398, 0, 0, 0] := by
  rw [show D2M8K2.u2801 = KTree.node D2M8K2.t2808 (nat_lit 6986945) (nat_lit 2222962290) (nat_lit 0) D2M8K2.t2809 from rfl, totK_node, tot2808, tot2809]
  decide +kernel

theorem arows2802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2802 = true := by
  rw [show D2M8K2.u2802 = KTree.node D2M8K2.t2810 (nat_lit 6988805) (nat_lit 2377184134) (nat_lit 0) D2M8K2.t2811 from rfl, allE_node, rows2810, irow2802, rows2811]
  all_goals rfl

theorem atot2802 : totK PD2M8K2 D2M8K2.u2802 = [0, 341747571033, 912949006900, 458377138509, 33927183972, 0, 0, 0] := by
  rw [show D2M8K2.u2802 = KTree.node D2M8K2.t2810 (nat_lit 6988805) (nat_lit 2377184134) (nat_lit 0) D2M8K2.t2811 from rfl, totK_node, tot2810, tot2811]
  decide +kernel

theorem arows2804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2804 = true := by
  rw [show D2M8K2.u2804 = KTree.node D2M8K2.t2812 (nat_lit 6990369) (nat_lit 1413744912) (nat_lit 0) D2M8K2.t2813 from rfl, allE_node, rows2812, irow2804, rows2813]
  all_goals rfl

theorem atot2804 : totK PD2M8K2 D2M8K2.u2804 = [0, 125691141794, 690316272534, 771464667534, 142668472581, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2804 = KTree.node D2M8K2.t2812 (nat_lit 6990369) (nat_lit 1413744912) (nat_lit 0) D2M8K2.t2813 from rfl, totK_node, tot2812, tot2813]
  decide +kernel

theorem arows2805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2805 = true := by
  rw [show D2M8K2.u2805 = KTree.node D2M8K2.t2814 (nat_lit 6995673) (nat_lit 1729926509) (nat_lit 0) D2M8K2.t2815 from rfl, allE_node, rows2814, irow2805, rows2815]
  all_goals rfl

theorem atot2805 : totK PD2M8K2 D2M8K2.u2805 = [0, 372723355818, 955804070509, 436369721811, 18915990292, 0, 0, 0] := by
  rw [show D2M8K2.u2805 = KTree.node D2M8K2.t2814 (nat_lit 6995673) (nat_lit 1729926509) (nat_lit 0) D2M8K2.t2815 from rfl, totK_node, tot2814, tot2815]
  decide +kernel

theorem arows2813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2813 = true := by
  rw [show D2M8K2.u2813 = KTree.node D2M8K2.t2816 (nat_lit 7002465) (nat_lit 1818646111) (nat_lit 0) D2M8K2.t2817 from rfl, allE_node, rows2816, irow2813, rows2817]
  all_goals rfl

theorem atot2813 : totK PD2M8K2 D2M8K2.u2813 = [0, 378065726634, 929032678973, 439734835750, 27233885447, 0, 0, 0] := by
  rw [show D2M8K2.u2813 = KTree.node D2M8K2.t2816 (nat_lit 7002465) (nat_lit 1818646111) (nat_lit 0) D2M8K2.t2817 from rfl, totK_node, tot2816, tot2817]
  decide +kernel

theorem arows2814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2814 = true := by
  rw [show D2M8K2.u2814 = KTree.node D2M8K2.t2818 (nat_lit 7005808) (nat_lit 3551160016) (nat_lit 0) D2M8K2.t2819 from rfl, allE_node, rows2818, irow2814, rows2819]
  all_goals rfl

theorem atot2814 : totK PD2M8K2 D2M8K2.u2814 = [0, 352223369202, 962514963208, 464730972623, 20144741380, 0, 0, 0] := by
  rw [show D2M8K2.u2814 = KTree.node D2M8K2.t2818 (nat_lit 7005808) (nat_lit 3551160016) (nat_lit 0) D2M8K2.t2819 from rfl, totK_node, tot2818, tot2819]
  decide +kernel

theorem arows2816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2816 = true := by
  rw [show D2M8K2.u2816 = KTree.node D2M8K2.t2820 (nat_lit 7012786) (nat_lit 4137157413) (nat_lit 0) D2M8K2.t2821 from rfl, allE_node, rows2820, irow2816, rows2821]
  all_goals rfl

theorem atot2816 : totK PD2M8K2 D2M8K2.u2816 = [281748690754, 766924198206, 607871835612, 175401424333, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u2816 = KTree.node D2M8K2.t2820 (nat_lit 7012786) (nat_lit 4137157413) (nat_lit 0) D2M8K2.t2821 from rfl, totK_node, tot2820, tot2821]
  decide +kernel

theorem arows2817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2817 = true := by
  rw [show D2M8K2.u2817 = KTree.node D2M8K2.t2822 (nat_lit 7014288) (nat_lit 2727639945) (nat_lit 0) D2M8K2.t2823 from rfl, allE_node, rows2822, irow2817, rows2823]
  all_goals rfl

theorem atot2817 : totK PD2M8K2 D2M8K2.u2817 = [163342843260, 647676005949, 720297394471, 280419884680, 25373788367, 0, 0, 0] := by
  rw [show D2M8K2.u2817 = KTree.node D2M8K2.t2822 (nat_lit 7014288) (nat_lit 2727639945) (nat_lit 0) D2M8K2.t2823 from rfl, totK_node, tot2822, tot2823]
  decide +kernel

theorem arows2820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2820 = true := by
  rw [show D2M8K2.u2820 = KTree.node D2M8K2.t2824 (nat_lit 7015471) (nat_lit 2409944126) (nat_lit 0) D2M8K2.t2825 from rfl, allE_node, rows2824, irow2820, rows2825]
  all_goals rfl

theorem atot2820 : totK PD2M8K2 D2M8K2.u2820 = [160996825849, 582481130881, 762511205494, 306690389566, 12235609738, 0, 0, 0] := by
  rw [show D2M8K2.u2820 = KTree.node D2M8K2.t2824 (nat_lit 7015471) (nat_lit 2409944126) (nat_lit 0) D2M8K2.t2825 from rfl, totK_node, tot2824, tot2825]
  decide +kernel

theorem arows2821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2821 = true := by
  rw [show D2M8K2.u2821 = KTree.node D2M8K2.t2826 (nat_lit 7016987) (nat_lit 1002275516) (nat_lit 0) D2M8K2.t2827 from rfl, allE_node, rows2826, irow2821, rows2827]
  all_goals rfl

theorem atot2821 : totK PD2M8K2 D2M8K2.u2821 = [265702090843, 817756853388, 625769467583, 88241165159, 1163840124, 0, 0, 0] := by
  rw [show D2M8K2.u2821 = KTree.node D2M8K2.t2826 (nat_lit 7016987) (nat_lit 1002275516) (nat_lit 0) D2M8K2.t2827 from rfl, totK_node, tot2826, tot2827]
  decide +kernel

theorem arows2823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2823 = true := by
  rw [show D2M8K2.u2823 = KTree.node D2M8K2.t2828 (nat_lit 7018662) (nat_lit 3517145103) (nat_lit 0) D2M8K2.t2829 from rfl, allE_node, rows2828, irow2823, rows2829]
  all_goals rfl

theorem atot2823 : totK PD2M8K2 D2M8K2.u2823 = [90448200850, 588512330715, 890083167507, 252420448497, 11873025674, 0, 0, 0] := by
  rw [show D2M8K2.u2823 = KTree.node D2M8K2.t2828 (nat_lit 7018662) (nat_lit 3517145103) (nat_lit 0) D2M8K2.t2829 from rfl, totK_node, tot2828, tot2829]
  decide +kernel

theorem arows2824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2824 = true := by
  rw [show D2M8K2.u2824 = KTree.node D2M8K2.t2830 (nat_lit 7020608) (nat_lit 3161918047) (nat_lit 0) D2M8K2.t2831 from rfl, allE_node, rows2830, irow2824, rows2831]
  all_goals rfl

theorem atot2824 : totK PD2M8K2 D2M8K2.u2824 = [256591304702, 838221575015, 653225571476, 91505514197, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2824 = KTree.node D2M8K2.t2830 (nat_lit 7020608) (nat_lit 3161918047) (nat_lit 0) D2M8K2.t2831 from rfl, totK_node, tot2830, tot2831]
  decide +kernel

theorem arows2828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2828 = true := by
  rw [show D2M8K2.u2828 = KTree.node D2M8K2.t2832 (nat_lit 7022683) (nat_lit 2225330266) (nat_lit 0) D2M8K2.t2833 from rfl, allE_node, rows2832, irow2828, rows2833]
  all_goals rfl

theorem atot2828 : totK PD2M8K2 D2M8K2.u2828 = [241536686875, 698675863494, 660520290572, 196040778927, 10770125763, 0, 0, 0] := by
  rw [show D2M8K2.u2828 = KTree.node D2M8K2.t2832 (nat_lit 7022683) (nat_lit 2225330266) (nat_lit 0) D2M8K2.t2833 from rfl, totK_node, tot2832, tot2833]
  decide +kernel

theorem arows2829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2829 = true := by
  rw [show D2M8K2.u2829 = KTree.node D2M8K2.t2834 (nat_lit 7023916) (nat_lit 3822165885) (nat_lit 0) D2M8K2.t2835 from rfl, allE_node, rows2834, irow2829, rows2835]
  all_goals rfl

theorem atot2829 : totK PD2M8K2 D2M8K2.u2829 = [170291197795, 763628815745, 744061935339, 113990527869, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u2829 = KTree.node D2M8K2.t2834 (nat_lit 7023916) (nat_lit 3822165885) (nat_lit 0) D2M8K2.t2835 from rfl, totK_node, tot2834, tot2835]
  decide +kernel

theorem arows2831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2831 = true := by
  rw [show D2M8K2.u2831 = KTree.node D2M8K2.t2836 (nat_lit 7026274) (nat_lit 3872519973) (nat_lit 0) D2M8K2.t2837 from rfl, allE_node, rows2836, irow2831, rows2837]
  all_goals rfl

theorem atot2831 : totK PD2M8K2 D2M8K2.u2831 = [244509280412, 773941590976, 669587596403, 135031892150, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u2831 = KTree.node D2M8K2.t2836 (nat_lit 7026274) (nat_lit 3872519973) (nat_lit 0) D2M8K2.t2837 from rfl, totK_node, tot2836, tot2837]
  decide +kernel

theorem arows2832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2832 = true := by
  rw [show D2M8K2.u2832 = KTree.node D2M8K2.t2838 (nat_lit 7027764) (nat_lit 3139428520) (nat_lit 0) D2M8K2.t2839 from rfl, allE_node, rows2838, irow2832, rows2839]
  all_goals rfl

theorem atot2832 : totK PD2M8K2 D2M8K2.u2832 = [172965736300, 711781929879, 764575070149, 161489295534, 2300468944, 0, 0, 0] := by
  rw [show D2M8K2.u2832 = KTree.node D2M8K2.t2838 (nat_lit 7027764) (nat_lit 3139428520) (nat_lit 0) D2M8K2.t2839 from rfl, totK_node, tot2838, tot2839]
  decide +kernel

theorem arows2835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2835 = true := by
  rw [show D2M8K2.u2835 = KTree.node D2M8K2.t2840 (nat_lit 7029491) (nat_lit 2971816977) (nat_lit 0) D2M8K2.t2841 from rfl, allE_node, rows2840, irow2835, rows2841]
  all_goals rfl

theorem atot2835 : totK PD2M8K2 D2M8K2.u2835 = [0, 354933884796, 919768586311, 505211132217, 46019849101, 0, 0, 0] := by
  rw [show D2M8K2.u2835 = KTree.node D2M8K2.t2840 (nat_lit 7029491) (nat_lit 2971816977) (nat_lit 0) D2M8K2.t2841 from rfl, totK_node, tot2840, tot2841]
  decide +kernel

theorem arows2836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2836 = true := by
  rw [show D2M8K2.u2836 = KTree.node D2M8K2.t2842 (nat_lit 7034412) (nat_lit 2679301618) (nat_lit 0) D2M8K2.t2843 from rfl, allE_node, rows2842, irow2836, rows2843]
  all_goals rfl

theorem atot2836 : totK PD2M8K2 D2M8K2.u2836 = [0, 261260800916, 787635514991, 604474339179, 163395006357, 17176948997, 0, 0] := by
  rw [show D2M8K2.u2836 = KTree.node D2M8K2.t2842 (nat_lit 7034412) (nat_lit 2679301618) (nat_lit 0) D2M8K2.t2843 from rfl, totK_node, tot2842, tot2843]
  decide +kernel

theorem arows2838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2838 = true := by
  rw [show D2M8K2.u2838 = KTree.node D2M8K2.t2844 (nat_lit 7035882) (nat_lit 3788746598) (nat_lit 0) D2M8K2.t2845 from rfl, allE_node, rows2844, irow2838, rows2845]
  all_goals rfl

theorem atot2838 : totK PD2M8K2 D2M8K2.u2838 = [0, 65887972987, 433265009514, 875398543038, 385984192980, 19744924857, 0, 0] := by
  rw [show D2M8K2.u2838 = KTree.node D2M8K2.t2844 (nat_lit 7035882) (nat_lit 3788746598) (nat_lit 0) D2M8K2.t2845 from rfl, totK_node, tot2844, tot2845]
  decide +kernel

theorem arows2839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2839 = true := by
  rw [show D2M8K2.u2839 = KTree.node D2M8K2.t2846 (nat_lit 7037140) (nat_lit 3772581810) (nat_lit 0) D2M8K2.t2847 from rfl, allE_node, rows2846, irow2839, rows2847]
  all_goals rfl

theorem atot2839 : totK PD2M8K2 D2M8K2.u2839 = [0, 355107266381, 937262809221, 491226819892, 36574369064, 0, 0, 0] := by
  rw [show D2M8K2.u2839 = KTree.node D2M8K2.t2846 (nat_lit 7037140) (nat_lit 3772581810) (nat_lit 0) D2M8K2.t2847 from rfl, totK_node, tot2846, tot2847]
  decide +kernel

theorem arows2844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2844 = true := by
  rw [show D2M8K2.u2844 = KTree.node D2M8K2.t2848 (nat_lit 7038960) (nat_lit 3074050851) (nat_lit 0) D2M8K2.t2849 from rfl, allE_node, rows2848, irow2844, rows2849]
  all_goals rfl

theorem atot2844 : totK PD2M8K2 D2M8K2.u2844 = [0, 90132371221, 617024095468, 887733712454, 208228006681, 5159868635, 0, 0] := by
  rw [show D2M8K2.u2844 = KTree.node D2M8K2.t2848 (nat_lit 7038960) (nat_lit 3074050851) (nat_lit 0) D2M8K2.t2849 from rfl, totK_node, tot2848, tot2849]
  decide +kernel

theorem arows2845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2845 = true := by
  rw [show D2M8K2.u2845 = KTree.node D2M8K2.t2850 (nat_lit 7041136) (nat_lit 3201253569) (nat_lit 0) D2M8K2.t2851 from rfl, allE_node, rows2850, irow2845, rows2851]
  all_goals rfl

theorem atot2845 : totK PD2M8K2 D2M8K2.u2845 = [0, 255811931221, 860107528543, 653709424591, 72159954556, 0, 0, 0] := by
  rw [show D2M8K2.u2845 = KTree.node D2M8K2.t2850 (nat_lit 7041136) (nat_lit 3201253569) (nat_lit 0) D2M8K2.t2851 from rfl, totK_node, tot2850, tot2851]
  decide +kernel

theorem arows2847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2847 = true := by
  rw [show D2M8K2.u2847 = KTree.node D2M8K2.t2852 (nat_lit 7043164) (nat_lit 3584837655) (nat_lit 0) D2M8K2.t2853 from rfl, allE_node, rows2852, irow2847, rows2853]
  all_goals rfl

theorem atot2847 : totK PD2M8K2 D2M8K2.u2847 = [0, 185018637098, 656896662420, 749728324709, 196747967579, 5218872685, 0, 0] := by
  rw [show D2M8K2.u2847 = KTree.node D2M8K2.t2852 (nat_lit 7043164) (nat_lit 3584837655) (nat_lit 0) D2M8K2.t2853 from rfl, totK_node, tot2852, tot2853]
  decide +kernel

theorem arows2848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2848 = true := by
  rw [show D2M8K2.u2848 = KTree.node D2M8K2.t2854 (nat_lit 7044540) (nat_lit 3001179853) (nat_lit 0) D2M8K2.t2855 from rfl, allE_node, rows2854, irow2848, rows2855]
  all_goals rfl

theorem atot2848 : totK PD2M8K2 D2M8K2.u2848 = [0, 225830928227, 845136827308, 669681992227, 63521037800, 0, 0, 0] := by
  rw [show D2M8K2.u2848 = KTree.node D2M8K2.t2854 (nat_lit 7044540) (nat_lit 3001179853) (nat_lit 0) D2M8K2.t2855 from rfl, totK_node, tot2854, tot2855]
  decide +kernel

theorem arows2851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2851 = true := by
  rw [show D2M8K2.u2851 = KTree.node D2M8K2.t2856 (nat_lit 7047001) (nat_lit 1247043770) (nat_lit 0) D2M8K2.t2857 from rfl, allE_node, rows2856, irow2851, rows2857]
  all_goals rfl

theorem atot2851 : totK PD2M8K2 D2M8K2.u2851 = [0, 243681518177, 776167073144, 681043262506, 122150238841, 1415142070, 0, 0] := by
  rw [show D2M8K2.u2851 = KTree.node D2M8K2.t2856 (nat_lit 7047001) (nat_lit 1247043770) (nat_lit 0) D2M8K2.t2857 from rfl, totK_node, tot2856, tot2857]
  decide +kernel

theorem arows2852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2852 = true := by
  rw [show D2M8K2.u2852 = KTree.node D2M8K2.t2858 (nat_lit 7048495) (nat_lit 2183669256) (nat_lit 0) D2M8K2.t2859 from rfl, allE_node, rows2858, irow2852, rows2859]
  all_goals rfl

theorem atot2852 : totK PD2M8K2 D2M8K2.u2852 = [0, 172704866115, 761192651916, 746705062530, 130739359600, 1238673482, 0, 0] := by
  rw [show D2M8K2.u2852 = KTree.node D2M8K2.t2858 (nat_lit 7048495) (nat_lit 2183669256) (nat_lit 0) D2M8K2.t2859 from rfl, totK_node, tot2858, tot2859]
  decide +kernel

theorem arows2854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2854 = true := by
  rw [show D2M8K2.u2854 = KTree.node D2M8K2.t2860 (nat_lit 7050383) (nat_lit 2775174655) (nat_lit 0) D2M8K2.t2861 from rfl, allE_node, rows2860, irow2854, rows2861]
  all_goals rfl

theorem atot2854 : totK PD2M8K2 D2M8K2.u2854 = [246152310855, 602172704403, 389074102185, 363028960207, 162127089738, 8063697217, 0, 0] := by
  rw [show D2M8K2.u2854 = KTree.node D2M8K2.t2860 (nat_lit 7050383) (nat_lit 2775174655) (nat_lit 0) D2M8K2.t2861 from rfl, totK_node, tot2860, tot2861]
  decide +kernel

theorem arows2855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2855 = true := by
  rw [show D2M8K2.u2855 = KTree.node D2M8K2.t2862 (nat_lit 7052027) (nat_lit 2840222239) (nat_lit 0) D2M8K2.t2863 from rfl, allE_node, rows2862, irow2855, rows2863]
  all_goals rfl

theorem atot2855 : totK PD2M8K2 D2M8K2.u2855 = [151318649428, 713722817538, 767159223680, 130185036989, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2855 = KTree.node D2M8K2.t2862 (nat_lit 7052027) (nat_lit 2840222239) (nat_lit 0) D2M8K2.t2863 from rfl, totK_node, tot2862, tot2863]
  decide +kernel

theorem arows2859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2859 = true := by
  rw [show D2M8K2.u2859 = KTree.node D2M8K2.t2864 (nat_lit 7054340) (nat_lit 3359499841) (nat_lit 0) D2M8K2.t2865 from rfl, allE_node, rows2864, irow2859, rows2865]
  all_goals rfl

theorem atot2859 : totK PD2M8K2 D2M8K2.u2859 = [338972799009, 889281343922, 565295666224, 57731794172, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2859 = KTree.node D2M8K2.t2864 (nat_lit 7054340) (nat_lit 3359499841) (nat_lit 0) D2M8K2.t2865 from rfl, totK_node, tot2864, tot2865]
  decide +kernel

theorem arows2860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2860 = true := by
  rw [show D2M8K2.u2860 = KTree.node D2M8K2.t2866 (nat_lit 7055896) (nat_lit 3650184628) (nat_lit 0) D2M8K2.t2867 from rfl, allE_node, rows2866, irow2860, rows2867]
  all_goals rfl

theorem atot2860 : totK PD2M8K2 D2M8K2.u2860 = [87940474155, 550614025861, 818360997342, 341528610351, 28209739022, 0, 0, 0] := by
  rw [show D2M8K2.u2860 = KTree.node D2M8K2.t2866 (nat_lit 7055896) (nat_lit 3650184628) (nat_lit 0) D2M8K2.t2867 from rfl, totK_node, tot2866, tot2867]
  decide +kernel

theorem arows2862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2862 = true := by
  rw [show D2M8K2.u2862 = KTree.node D2M8K2.t2868 (nat_lit 7057161) (nat_lit 1826613998) (nat_lit 0) D2M8K2.t2869 from rfl, allE_node, rows2868, irow2862, rows2869]
  all_goals rfl

theorem atot2862 : totK PD2M8K2 D2M8K2.u2862 = [193674686868, 651603795225, 711844930595, 248604679573, 9331067253, 0, 0, 0] := by
  rw [show D2M8K2.u2862 = KTree.node D2M8K2.t2868 (nat_lit 7057161) (nat_lit 1826613998) (nat_lit 0) D2M8K2.t2869 from rfl, totK_node, tot2868, tot2869]
  decide +kernel

theorem arows2863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2863 = true := by
  rw [show D2M8K2.u2863 = KTree.node D2M8K2.t2870 (nat_lit 7058633) (nat_lit 1788386491) (nat_lit 0) D2M8K2.t2871 from rfl, allE_node, rows2870, irow2863, rows2871]
  all_goals rfl

theorem atot2863 : totK PD2M8K2 D2M8K2.u2863 = [247993473436, 807977590505, 657452681002, 103769372462, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u2863 = KTree.node D2M8K2.t2870 (nat_lit 7058633) (nat_lit 1788386491) (nat_lit 0) D2M8K2.t2871 from rfl, totK_node, tot2870, tot2871]
  decide +kernel

theorem arows2866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2866 = true := by
  rw [show D2M8K2.u2866 = KTree.node D2M8K2.t2872 (nat_lit 7060285) (nat_lit 977566500) (nat_lit 0) D2M8K2.t2873 from rfl, allE_node, rows2872, irow2866, rows2873]
  all_goals rfl

theorem atot2866 : totK PD2M8K2 D2M8K2.u2866 = [170158465841, 646839302119, 744603626029, 216436279313, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u2866 = KTree.node D2M8K2.t2872 (nat_lit 7060285) (nat_lit 977566500) (nat_lit 0) D2M8K2.t2873 from rfl, totK_node, tot2872, tot2873]
  decide +kernel

theorem arows2867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2867 = true := by
  rw [show D2M8K2.u2867 = KTree.node D2M8K2.t2874 (nat_lit 7065094) (nat_lit 1506896729) (nat_lit 0) D2M8K2.t2875 from rfl, allE_node, rows2874, irow2867, rows2875]
  all_goals rfl

theorem atot2867 : totK PD2M8K2 D2M8K2.u2867 = [245886261403, 787113487744, 636870532642, 97879964934, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u2867 = KTree.node D2M8K2.t2874 (nat_lit 7065094) (nat_lit 1506896729) (nat_lit 0) D2M8K2.t2875 from rfl, totK_node, tot2874, tot2875]
  decide +kernel

theorem arows2869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2869 = true := by
  rw [show D2M8K2.u2869 = KTree.node D2M8K2.t2876 (nat_lit 7067058) (nat_lit 3391941727) (nat_lit 0) D2M8K2.t2877 from rfl, allE_node, rows2876, irow2869, rows2877]
  all_goals rfl

theorem atot2869 : totK PD2M8K2 D2M8K2.u2869 = [171716076782, 721090164623, 758878780405, 157726308506, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u2869 = KTree.node D2M8K2.t2876 (nat_lit 7067058) (nat_lit 3391941727) (nat_lit 0) D2M8K2.t2877 from rfl, totK_node, tot2876, tot2877]
  decide +kernel

theorem arows2870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2870 = true := by
  rw [show D2M8K2.u2870 = KTree.node D2M8K2.t2878 (nat_lit 7068651) (nat_lit 3459815109) (nat_lit 0) D2M8K2.t2879 from rfl, allE_node, rows2878, irow2870, rows2879]
  all_goals rfl

theorem atot2870 : totK PD2M8K2 D2M8K2.u2870 = [249088850674, 789049485512, 652341660505, 105076034029, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u2870 = KTree.node D2M8K2.t2878 (nat_lit 7068651) (nat_lit 3459815109) (nat_lit 0) D2M8K2.t2879 from rfl, totK_node, tot2878, tot2879]
  decide +kernel

theorem arows2876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2876 = true := by
  rw [show D2M8K2.u2876 = KTree.node D2M8K2.t2880 (nat_lit 7070334) (nat_lit 3961937056) (nat_lit 0) D2M8K2.t2881 from rfl, allE_node, rows2880, irow2876, rows2881]
  all_goals rfl

theorem atot2876 : totK PD2M8K2 D2M8K2.u2876 = [0, 404903670856, 954521018602, 394924694132, 21987376568, 0, 0, 0] := by
  rw [show D2M8K2.u2876 = KTree.node D2M8K2.t2880 (nat_lit 7070334) (nat_lit 3961937056) (nat_lit 0) D2M8K2.t2881 from rfl, totK_node, tot2880, tot2881]
  decide +kernel

theorem arows2877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2877 = true := by
  rw [show D2M8K2.u2877 = KTree.node D2M8K2.t2882 (nat_lit 7072222) (nat_lit 1357979415) (nat_lit 0) D2M8K2.t2883 from rfl, allE_node, rows2882, irow2877, rows2883]
  all_goals rfl

theorem atot2877 : totK PD2M8K2 D2M8K2.u2877 = [0, 306338471931, 882121516809, 510200227465, 38811442079, 0, 0, 0] := by
  rw [show D2M8K2.u2877 = KTree.node D2M8K2.t2882 (nat_lit 7072222) (nat_lit 1357979415) (nat_lit 0) D2M8K2.t2883 from rfl, totK_node, tot2882, tot2883]
  decide +kernel

theorem arows2879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2879 = true := by
  rw [show D2M8K2.u2879 = KTree.node D2M8K2.t2884 (nat_lit 7074749) (nat_lit 2289909956) (nat_lit 0) D2M8K2.t2885 from rfl, allE_node, rows2884, irow2879, rows2885]
  all_goals rfl

theorem atot2879 : totK PD2M8K2 D2M8K2.u2879 = [0, 182442894580, 755076974093, 736008029529, 109197602803, 1206465782, 0, 0] := by
  rw [show D2M8K2.u2879 = KTree.node D2M8K2.t2884 (nat_lit 7074749) (nat_lit 2289909956) (nat_lit 0) D2M8K2.t2885 from rfl, totK_node, tot2884, tot2885]
  decide +kernel

theorem arows2880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2880 = true := by
  rw [show D2M8K2.u2880 = KTree.node D2M8K2.t2886 (nat_lit 7075951) (nat_lit 2174296166) (nat_lit 0) D2M8K2.t2887 from rfl, allE_node, rows2886, irow2880, rows2887]
  all_goals rfl

theorem atot2880 : totK PD2M8K2 D2M8K2.u2880 = [0, 413711728032, 966685563292, 413570547847, 19726876000, 0, 0, 0] := by
  rw [show D2M8K2.u2880 = KTree.node D2M8K2.t2886 (nat_lit 7075951) (nat_lit 2174296166) (nat_lit 0) D2M8K2.t2887 from rfl, totK_node, tot2886, tot2887]
  decide +kernel

theorem arows2883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2883 = true := by
  rw [show D2M8K2.u2883 = KTree.node D2M8K2.t2888 (nat_lit 7079140) (nat_lit 3825369563) (nat_lit 0) D2M8K2.t2889 from rfl, allE_node, rows2888, irow2883, rows2889]
  all_goals rfl

theorem atot2883 : totK PD2M8K2 D2M8K2.u2883 = [0, 272817837979, 876929103370, 598938198470, 57271880338, 0, 0, 0] := by
  rw [show D2M8K2.u2883 = KTree.node D2M8K2.t2888 (nat_lit 7079140) (nat_lit 3825369563) (nat_lit 0) D2M8K2.t2889 from rfl, totK_node, tot2888, tot2889]
  decide +kernel

theorem arows2884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2884 = true := by
  rw [show D2M8K2.u2884 = KTree.node D2M8K2.t2890 (nat_lit 7080832) (nat_lit 3736311988) (nat_lit 0) D2M8K2.t2891 from rfl, allE_node, rows2890, irow2884, rows2891]
  all_goals rfl

theorem atot2884 : totK PD2M8K2 D2M8K2.u2884 = [0, 101139757463, 573737793272, 791671289520, 248949941469, 13016197374, 0, 0] := by
  rw [show D2M8K2.u2884 = KTree.node D2M8K2.t2890 (nat_lit 7080832) (nat_lit 3736311988) (nat_lit 0) D2M8K2.t2891 from rfl, totK_node, tot2890, tot2891]
  decide +kernel

theorem arows2886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2886 = true := by
  rw [show D2M8K2.u2886 = KTree.node D2M8K2.t2892 (nat_lit 7085699) (nat_lit 2104998489) (nat_lit 0) D2M8K2.t2893 from rfl, allE_node, rows2892, irow2886, rows2893]
  all_goals rfl

theorem atot2886 : totK PD2M8K2 D2M8K2.u2886 = [0, 312611815235, 903039886506, 521145868702, 36872924868, 0, 0, 0] := by
  rw [show D2M8K2.u2886 = KTree.node D2M8K2.t2892 (nat_lit 7085699) (nat_lit 2104998489) (nat_lit 0) D2M8K2.t2893 from rfl, totK_node, tot2892, tot2893]
  decide +kernel

theorem arows2887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2887 = true := by
  rw [show D2M8K2.u2887 = KTree.node D2M8K2.t2894 (nat_lit 7087781) (nat_lit 2316525931) (nat_lit 0) D2M8K2.t2895 from rfl, allE_node, rows2894, irow2887, rows2895]
  all_goals rfl

theorem atot2887 : totK PD2M8K2 D2M8K2.u2887 = [0, 170979490969, 697332678927, 707514775887, 148675384066, 4574395652, 0, 0] := by
  rw [show D2M8K2.u2887 = KTree.node D2M8K2.t2894 (nat_lit 7087781) (nat_lit 2316525931) (nat_lit 0) D2M8K2.t2895 from rfl, totK_node, tot2894, tot2895]
  decide +kernel

theorem arows2891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2891 = true := by
  rw [show D2M8K2.u2891 = KTree.node D2M8K2.t2896 (nat_lit 7089390) (nat_lit 3765666450) (nat_lit 0) D2M8K2.t2897 from rfl, allE_node, rows2896, irow2891, rows2897]
  all_goals rfl

theorem atot2891 : totK PD2M8K2 D2M8K2.u2891 = [94892842607, 470623677172, 772211758311, 426647978652, 32976194192, 0, 0, 0] := by
  rw [show D2M8K2.u2891 = KTree.node D2M8K2.t2896 (nat_lit 7089390) (nat_lit 3765666450) (nat_lit 0) D2M8K2.t2897 from rfl, totK_node, tot2896, tot2897]
  decide +kernel

theorem arows2892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2892 = true := by
  rw [show D2M8K2.u2892 = KTree.node D2M8K2.t2898 (nat_lit 7134406) (nat_lit 2926326476) (nat_lit 0) D2M8K2.t2899 from rfl, allE_node, rows2898, irow2892, rows2899]
  all_goals rfl

theorem atot2892 : totK PD2M8K2 D2M8K2.u2892 = [282094188133, 820301619604, 575706755708, 88268025795, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2892 = KTree.node D2M8K2.t2898 (nat_lit 7134406) (nat_lit 2926326476) (nat_lit 0) D2M8K2.t2899 from rfl, totK_node, tot2898, tot2899]
  decide +kernel

theorem arows2894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2894 = true := by
  rw [show D2M8K2.u2894 = KTree.node D2M8K2.t2900 (nat_lit 7136978) (nat_lit 4138950161) (nat_lit 0) D2M8K2.t2901 from rfl, allE_node, rows2900, irow2894, rows2901]
  all_goals rfl

theorem atot2894 : totK PD2M8K2 D2M8K2.u2894 = [190466112048, 759527066317, 766942672249, 102641483953, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2894 = KTree.node D2M8K2.t2900 (nat_lit 7136978) (nat_lit 4138950161) (nat_lit 0) D2M8K2.t2901 from rfl, totK_node, tot2900, tot2901]
  decide +kernel

theorem arows2895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2895 = true := by
  rw [show D2M8K2.u2895 = KTree.node D2M8K2.t2902 (nat_lit 7138158) (nat_lit 3949119379) (nat_lit 0) D2M8K2.t2903 from rfl, allE_node, rows2902, irow2895, rows2903]
  all_goals rfl

theorem atot2895 : totK PD2M8K2 D2M8K2.u2895 = [229166277415, 749965455694, 639149651940, 203360789561, 21385708972, 0, 0, 0] := by
  rw [show D2M8K2.u2895 = KTree.node D2M8K2.t2902 (nat_lit 7138158) (nat_lit 3949119379) (nat_lit 0) D2M8K2.t2903 from rfl, totK_node, tot2902, tot2903]
  decide +kernel

theorem arows2898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2898 = true := by
  rw [show D2M8K2.u2898 = KTree.node D2M8K2.t2904 (nat_lit 7139670) (nat_lit 3186747281) (nat_lit 0) D2M8K2.t2905 from rfl, allE_node, rows2904, irow2898, rows2905]
  all_goals rfl

theorem atot2898 : totK PD2M8K2 D2M8K2.u2898 = [90975914836, 486227024442, 827758210859, 371290211535, 16182558003, 0, 0, 0] := by
  rw [show D2M8K2.u2898 = KTree.node D2M8K2.t2904 (nat_lit 7139670) (nat_lit 3186747281) (nat_lit 0) D2M8K2.t2905 from rfl, totK_node, tot2904, tot2905]
  decide +kernel

theorem arows2899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2899 = true := by
  rw [show D2M8K2.u2899 = KTree.node D2M8K2.t2906 (nat_lit 7140937) (nat_lit 1415546622) (nat_lit 0) D2M8K2.t2907 from rfl, allE_node, rows2906, irow2899, rows2907]
  all_goals rfl

theorem atot2899 : totK PD2M8K2 D2M8K2.u2899 = [328937252478, 904656028123, 545534877441, 47591763853, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2899 = KTree.node D2M8K2.t2906 (nat_lit 7140937) (nat_lit 1415546622) (nat_lit 0) D2M8K2.t2907 from rfl, totK_node, tot2906, tot2907]
  decide +kernel

theorem arows2901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2901 = true := by
  rw [show D2M8K2.u2901 = KTree.node D2M8K2.t2908 (nat_lit 7142643) (nat_lit 2316232055) (nat_lit 0) D2M8K2.t2909 from rfl, allE_node, rows2908, irow2901, rows2909]
  all_goals rfl

theorem atot2901 : totK PD2M8K2 D2M8K2.u2901 = [66418003249, 508775759690, 888995111951, 286566673022, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u2901 = KTree.node D2M8K2.t2908 (nat_lit 7142643) (nat_lit 2316232055) (nat_lit 0) D2M8K2.t2909 from rfl, totK_node, tot2908, tot2909]
  decide +kernel

theorem arows2902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2902 = true := by
  rw [show D2M8K2.u2902 = KTree.node D2M8K2.t2910 (nat_lit 7144657) (nat_lit 1405126266) (nat_lit 0) D2M8K2.t2911 from rfl, allE_node, rows2910, irow2902, rows2911]
  all_goals rfl

theorem atot2902 : totK PD2M8K2 D2M8K2.u2902 = [260798530835, 826119040413, 630021200843, 99990245137, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u2902 = KTree.node D2M8K2.t2910 (nat_lit 7144657) (nat_lit 1405126266) (nat_lit 0) D2M8K2.t2911 from rfl, totK_node, tot2910, tot2911]
  decide +kernel

theorem arows2907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2907 = true := by
  rw [show D2M8K2.u2907 = KTree.node D2M8K2.t2912 (nat_lit 7146676) (nat_lit 3206152832) (nat_lit 0) D2M8K2.t2913 from rfl, allE_node, rows2912, irow2907, rows2913]
  all_goals rfl

theorem atot2907 : totK PD2M8K2 D2M8K2.u2907 = [172390672205, 648213936284, 739066461985, 219153077302, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u2907 = KTree.node D2M8K2.t2912 (nat_lit 7146676) (nat_lit 3206152832) (nat_lit 0) D2M8K2.t2913 from rfl, totK_node, tot2912, tot2913]
  decide +kernel

theorem arows2908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2908 = true := by
  rw [show D2M8K2.u2908 = KTree.node D2M8K2.t2914 (nat_lit 7148178) (nat_lit 3357216697) (nat_lit 0) D2M8K2.t2915 from rfl, allE_node, rows2914, irow2908, rows2915]
  all_goals rfl

theorem atot2908 : totK PD2M8K2 D2M8K2.u2908 = [263330283239, 808523629955, 620564312375, 97752691186, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u2908 = KTree.node D2M8K2.t2914 (nat_lit 7148178) (nat_lit 3357216697) (nat_lit 0) D2M8K2.t2915 from rfl, totK_node, tot2914, tot2915]
  decide +kernel

theorem arows2910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2910 = true := by
  rw [show D2M8K2.u2910 = KTree.node D2M8K2.t2916 (nat_lit 7150111) (nat_lit 2228025001) (nat_lit 0) D2M8K2.t2917 from rfl, allE_node, rows2916, irow2910, rows2917]
  all_goals rfl

theorem atot2910 : totK PD2M8K2 D2M8K2.u2910 = [0, 468939809563, 978214419793, 319140683228, 13624150839, 0, 0, 0] := by
  rw [show D2M8K2.u2910 = KTree.node D2M8K2.t2916 (nat_lit 7150111) (nat_lit 2228025001) (nat_lit 0) D2M8K2.t2917 from rfl, totK_node, tot2916, tot2917]
  decide +kernel

theorem arows2911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2911 = true := by
  rw [show D2M8K2.u2911 = KTree.node D2M8K2.t2918 (nat_lit 7155511) (nat_lit 1604884070) (nat_lit 0) D2M8K2.t2919 from rfl, allE_node, rows2918, irow2911, rows2919]
  all_goals rfl

theorem atot2911 : totK PD2M8K2 D2M8K2.u2911 = [0, 196828358161, 780918905096, 663860945082, 87758934427, 1138244013, 0, 0] := by
  rw [show D2M8K2.u2911 = KTree.node D2M8K2.t2918 (nat_lit 7155511) (nat_lit 1604884070) (nat_lit 0) D2M8K2.t2919 from rfl, totK_node, tot2918, tot2919]
  decide +kernel

theorem arows2914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2914 = true := by
  rw [show D2M8K2.u2914 = KTree.node D2M8K2.t2920 (nat_lit 7158055) (nat_lit 2020490091) (nat_lit 0) D2M8K2.t2921 from rfl, allE_node, rows2920, irow2914, rows2921]
  all_goals rfl

theorem atot2914 : totK PD2M8K2 D2M8K2.u2914 = [0, 348529930130, 903972067024, 514597567216, 50125880291, 0, 0, 0] := by
  rw [show D2M8K2.u2914 = KTree.node D2M8K2.t2920 (nat_lit 7158055) (nat_lit 2020490091) (nat_lit 0) D2M8K2.t2921 from rfl, totK_node, tot2920, tot2921]
  decide +kernel

theorem arows2915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2915 = true := by
  rw [show D2M8K2.u2915 = KTree.node D2M8K2.t2922 (nat_lit 7161150) (nat_lit 3695374647) (nat_lit 0) D2M8K2.t2923 from rfl, allE_node, rows2922, irow2915, rows2923]
  all_goals rfl

theorem atot2915 : totK PD2M8K2 D2M8K2.u2915 = [0, 347333850852, 935597765709, 491840860276, 29292915931, 0, 0, 0] := by
  rw [show D2M8K2.u2915 = KTree.node D2M8K2.t2922 (nat_lit 7161150) (nat_lit 3695374647) (nat_lit 0) D2M8K2.t2923 from rfl, totK_node, tot2922, tot2923]
  decide +kernel

theorem arows2917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2917 = true := by
  rw [show D2M8K2.u2917 = KTree.node D2M8K2.t2924 (nat_lit 7164391) (nat_lit 2358954702) (nat_lit 0) D2M8K2.t2925 from rfl, allE_node, rows2924, irow2917, rows2925]
  all_goals rfl

theorem atot2917 : totK PD2M8K2 D2M8K2.u2917 = [0, 384167330094, 966423075142, 442618817633, 19878544093, 0, 0, 0] := by
  rw [show D2M8K2.u2917 = KTree.node D2M8K2.t2924 (nat_lit 7164391) (nat_lit 2358954702) (nat_lit 0) D2M8K2.t2925 from rfl, totK_node, tot2924, tot2925]
  decide +kernel

theorem arows2918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2918 = true := by
  rw [show D2M8K2.u2918 = KTree.node D2M8K2.t2926 (nat_lit 7168015) (nat_lit 1451181513) (nat_lit 0) D2M8K2.t2927 from rfl, allE_node, rows2926, irow2918, rows2927]
  all_goals rfl

theorem atot2918 : totK PD2M8K2 D2M8K2.u2918 = [0, 346509584811, 917208649204, 480119359997, 35402674992, 0, 0, 0] := by
  rw [show D2M8K2.u2918 = KTree.node D2M8K2.t2926 (nat_lit 7168015) (nat_lit 1451181513) (nat_lit 0) D2M8K2.t2927 from rfl, totK_node, tot2926, tot2927]
  decide +kernel

theorem arows2922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2922 = true := by
  rw [show D2M8K2.u2922 = KTree.node D2M8K2.t2928 (nat_lit 7169523) (nat_lit 2205159832) (nat_lit 0) D2M8K2.t2929 from rfl, allE_node, rows2928, irow2922, rows2929]
  all_goals rfl

theorem atot2922 : totK PD2M8K2 D2M8K2.u2922 = [0, 174583700023, 756260477096, 705767778103, 107826186247, 1095107716, 0, 0] := by
  rw [show D2M8K2.u2922 = KTree.node D2M8K2.t2928 (nat_lit 7169523) (nat_lit 2205159832) (nat_lit 0) D2M8K2.t2929 from rfl, totK_node, tot2928, tot2929]
  decide +kernel

theorem arows2923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2923 = true := by
  rw [show D2M8K2.u2923 = KTree.node D2M8K2.t2930 (nat_lit 7175248) (nat_lit 3423385323) (nat_lit 0) D2M8K2.t2931 from rfl, allE_node, rows2930, irow2923, rows2931]
  all_goals rfl

theorem atot2923 : totK PD2M8K2 D2M8K2.u2923 = [290561744210, 708245475360, 413590716465, 261774942918, 92815941467, 3882006667, 0, 0] := by
  rw [show D2M8K2.u2923 = KTree.node D2M8K2.t2930 (nat_lit 7175248) (nat_lit 3423385323) (nat_lit 0) D2M8K2.t2931 from rfl, totK_node, tot2930, tot2931]
  decide +kernel

theorem arows2925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2925 = true := by
  rw [show D2M8K2.u2925 = KTree.node D2M8K2.t2932 (nat_lit 7176630) (nat_lit 2670660989) (nat_lit 0) D2M8K2.t2933 from rfl, allE_node, rows2932, irow2925, rows2933]
  all_goals rfl

theorem atot2925 : totK PD2M8K2 D2M8K2.u2925 = [123007665639, 679309378030, 858072174138, 148474344413, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2925 = KTree.node D2M8K2.t2932 (nat_lit 7176630) (nat_lit 2670660989) (nat_lit 0) D2M8K2.t2933 from rfl, totK_node, tot2932, tot2933]
  decide +kernel

theorem arows2926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2926 = true := by
  rw [show D2M8K2.u2926 = KTree.node D2M8K2.t2934 (nat_lit 7179006) (nat_lit 3971616199) (nat_lit 0) D2M8K2.t2935 from rfl, allE_node, rows2934, irow2926, rows2935]
  all_goals rfl

theorem atot2926 : totK PD2M8K2 D2M8K2.u2926 = [382654054027, 940806348638, 481345886950, 40228872264, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2926 = KTree.node D2M8K2.t2934 (nat_lit 7179006) (nat_lit 3971616199) (nat_lit 0) D2M8K2.t2935 from rfl, totK_node, tot2934, tot2935]
  decide +kernel

theorem arows2929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2929 = true := by
  rw [show D2M8K2.u2929 = KTree.node D2M8K2.t2936 (nat_lit 7180519) (nat_lit 1459319044) (nat_lit 0) D2M8K2.t2937 from rfl, allE_node, rows2936, irow2929, rows2937]
  all_goals rfl

theorem atot2929 : totK PD2M8K2 D2M8K2.u2929 = [0, 434417581364, 945373489412, 417386320549, 29341012954, 0, 0, 0] := by
  rw [show D2M8K2.u2929 = KTree.node D2M8K2.t2936 (nat_lit 7180519) (nat_lit 1459319044) (nat_lit 0) D2M8K2.t2937 from rfl, totK_node, tot2936, tot2937]
  decide +kernel

theorem arows2930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2930 = true := by
  rw [show D2M8K2.u2930 = KTree.node D2M8K2.t2938 (nat_lit 7181898) (nat_lit 3673872447) (nat_lit 0) D2M8K2.t2939 from rfl, allE_node, rows2938, irow2930, rows2939]
  all_goals rfl

theorem atot2930 : totK PD2M8K2 D2M8K2.u2930 = [267357066781, 765173155301, 605091539095, 170207884721, 8213711289, 0, 0, 0] := by
  rw [show D2M8K2.u2930 = KTree.node D2M8K2.t2938 (nat_lit 7181898) (nat_lit 3673872447) (nat_lit 0) D2M8K2.t2939 from rfl, totK_node, tot2938, tot2939]
  decide +kernel

theorem arows2932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2932 = true := by
  rw [show D2M8K2.u2932 = KTree.node D2M8K2.t2940 (nat_lit 7183369) (nat_lit 1503105744) (nat_lit 0) D2M8K2.t2941 from rfl, allE_node, rows2940, irow2932, rows2941]
  all_goals rfl

theorem atot2932 : totK PD2M8K2 D2M8K2.u2932 = [157123059778, 672386709127, 775217212109, 186633670328, 7165314891, 0, 0, 0] := by
  rw [show D2M8K2.u2932 = KTree.node D2M8K2.t2940 (nat_lit 7183369) (nat_lit 1503105744) (nat_lit 0) D2M8K2.t2941 from rfl, totK_node, tot2940, tot2941]
  decide +kernel

theorem arows2933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2933 = true := by
  rw [show D2M8K2.u2933 = KTree.node D2M8K2.t2942 (nat_lit 7185246) (nat_lit 3987774429) (nat_lit 0) D2M8K2.t2943 from rfl, allE_node, rows2942, irow2933, rows2943]
  all_goals rfl

theorem atot2933 : totK PD2M8K2 D2M8K2.u2933 = [241171175727, 762613592607, 662694176701, 144814269777, 5878468449, 0, 0, 0] := by
  rw [show D2M8K2.u2933 = KTree.node D2M8K2.t2942 (nat_lit 7185246) (nat_lit 3987774429) (nat_lit 0) D2M8K2.t2943 from rfl, totK_node, tot2942, tot2943]
  decide +kernel

theorem arows2940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2940 = true := by
  rw [show D2M8K2.u2940 = KTree.node D2M8K2.t2944 (nat_lit 7187115) (nat_lit 3703598000) (nat_lit 0) D2M8K2.t2945 from rfl, allE_node, rows2944, irow2940, rows2945]
  all_goals rfl

theorem atot2940 : totK PD2M8K2 D2M8K2.u2940 = [125794280066, 633004264615, 829547580708, 226910308202, 9554697516, 0, 0, 0] := by
  rw [show D2M8K2.u2940 = KTree.node D2M8K2.t2944 (nat_lit 7187115) (nat_lit 3703598000) (nat_lit 0) D2M8K2.t2945 from rfl, totK_node, tot2944, tot2945]
  decide +kernel

theorem arows2941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2941 = true := by
  rw [show D2M8K2.u2941 = KTree.node D2M8K2.t2946 (nat_lit 7192569) (nat_lit 1753251315) (nat_lit 0) D2M8K2.t2947 from rfl, allE_node, rows2946, irow2941, rows2947]
  all_goals rfl

theorem atot2941 : totK PD2M8K2 D2M8K2.u2941 = [376230937298, 929631869376, 483092368109, 38064351904, 0, 0, 0, 0] := by
  rw [show D2M8K2.u2941 = KTree.node D2M8K2.t2946 (nat_lit 7192569) (nat_lit 1753251315) (nat_lit 0) D2M8K2.t2947 from rfl, totK_node, tot2946, tot2947]
  decide +kernel

theorem arows2943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2943 = true := by
  rw [show D2M8K2.u2943 = KTree.node D2M8K2.t2948 (nat_lit 7194083) (nat_lit 2969358193) (nat_lit 0) D2M8K2.t2949 from rfl, allE_node, rows2948, irow2943, rows2949]
  all_goals rfl

theorem atot2943 : totK PD2M8K2 D2M8K2.u2943 = [19735703396, 525088877264, 948672272798, 287124183417, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u2943 = KTree.node D2M8K2.t2948 (nat_lit 7194083) (nat_lit 2969358193) (nat_lit 0) D2M8K2.t2949 from rfl, totK_node, tot2948, tot2949]
  decide +kernel

theorem arows2944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2944 = true := by
  rw [show D2M8K2.u2944 = KTree.node D2M8K2.t2950 (nat_lit 7196020) (nat_lit 4062192081) (nat_lit 0) D2M8K2.t2951 from rfl, allE_node, rows2950, irow2944, rows2951]
  all_goals rfl

theorem atot2944 : totK PD2M8K2 D2M8K2.u2944 = [0, 363825033383, 933140669688, 444892942488, 23772366266, 0, 0, 0] := by
  rw [show D2M8K2.u2944 = KTree.node D2M8K2.t2950 (nat_lit 7196020) (nat_lit 4062192081) (nat_lit 0) D2M8K2.t2951 from rfl, totK_node, tot2950, tot2951]
  decide +kernel

theorem arows2947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2947 = true := by
  rw [show D2M8K2.u2947 = KTree.node D2M8K2.t2952 (nat_lit 7197745) (nat_lit 1506478905) (nat_lit 0) D2M8K2.t2953 from rfl, allE_node, rows2952, irow2947, rows2953]
  all_goals rfl

theorem atot2947 : totK PD2M8K2 D2M8K2.u2947 = [0, 155176606270, 709659976887, 802011692264, 119785977609, 1310285577, 0, 0] := by
  rw [show D2M8K2.u2947 = KTree.node D2M8K2.t2952 (nat_lit 7197745) (nat_lit 1506478905) (nat_lit 0) D2M8K2.t2953 from rfl, totK_node, tot2952, tot2953]
  decide +kernel

theorem arows2948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2948 = true := by
  rw [show D2M8K2.u2948 = KTree.node D2M8K2.t2954 (nat_lit 7199837) (nat_lit 1692137662) (nat_lit 0) D2M8K2.t2955 from rfl, allE_node, rows2954, irow2948, rows2955]
  all_goals rfl

theorem atot2948 : totK PD2M8K2 D2M8K2.u2948 = [0, 335086197735, 934272587912, 536672552985, 40243008005, 0, 0, 0] := by
  rw [show D2M8K2.u2948 = KTree.node D2M8K2.t2954 (nat_lit 7199837) (nat_lit 1692137662) (nat_lit 0) D2M8K2.t2955 from rfl, totK_node, tot2954, tot2955]
  decide +kernel

theorem arows2950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2950 = true := by
  rw [show D2M8K2.u2950 = KTree.node D2M8K2.t2956 (nat_lit 7202858) (nat_lit 4105264466) (nat_lit 0) D2M8K2.t2957 from rfl, allE_node, rows2956, irow2950, rows2957]
  all_goals rfl

theorem atot2950 : totK PD2M8K2 D2M8K2.u2950 = [0, 362199131840, 906157748669, 480273653860, 42515722811, 0, 0, 0] := by
  rw [show D2M8K2.u2950 = KTree.node D2M8K2.t2956 (nat_lit 7202858) (nat_lit 4105264466) (nat_lit 0) D2M8K2.t2957 from rfl, totK_node, tot2956, tot2957]
  decide +kernel

theorem arows2951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2951 = true := by
  rw [show D2M8K2.u2951 = KTree.node D2M8K2.t2958 (nat_lit 7204444) (nat_lit 3882993450) (nat_lit 0) D2M8K2.t2959 from rfl, allE_node, rows2958, irow2951, rows2959]
  all_goals rfl

theorem atot2951 : totK PD2M8K2 D2M8K2.u2951 = [0, 84310290542, 633039206672, 860024436019, 180201898072, 4879840392, 0, 0] := by
  rw [show D2M8K2.u2951 = KTree.node D2M8K2.t2958 (nat_lit 7204444) (nat_lit 3882993450) (nat_lit 0) D2M8K2.t2959 from rfl, totK_node, tot2958, tot2959]
  decide +kernel

theorem arows2955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2955 = true := by
  rw [show D2M8K2.u2955 = KTree.node D2M8K2.t2960 (nat_lit 7206741) (nat_lit 1645707257) (nat_lit 0) D2M8K2.t2961 from rfl, allE_node, rows2960, irow2955, rows2961]
  all_goals rfl

theorem atot2955 : totK PD2M8K2 D2M8K2.u2955 = [0, 302340313708, 881633259093, 589361364308, 57837681909, 0, 0, 0] := by
  rw [show D2M8K2.u2955 = KTree.node D2M8K2.t2960 (nat_lit 7206741) (nat_lit 1645707257) (nat_lit 0) D2M8K2.t2961 from rfl, totK_node, tot2960, tot2961]
  decide +kernel

theorem arows2956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2956 = true := by
  rw [show D2M8K2.u2956 = KTree.node D2M8K2.t2962 (nat_lit 7209065) (nat_lit 1540344693) (nat_lit 0) D2M8K2.t2963 from rfl, allE_node, rows2962, irow2956, rows2963]
  all_goals rfl

theorem atot2956 : totK PD2M8K2 D2M8K2.u2956 = [0, 183944966428, 704647357821, 731428235700, 163612536393, 4931404646, 0, 0] := by
  rw [show D2M8K2.u2956 = KTree.node D2M8K2.t2962 (nat_lit 7209065) (nat_lit 1540344693) (nat_lit 0) D2M8K2.t2963 from rfl, totK_node, tot2962, tot2963]
  decide +kernel

theorem arows2958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2958 = true := by
  rw [show D2M8K2.u2958 = KTree.node D2M8K2.t2964 (nat_lit 7214152) (nat_lit 3821762034) (nat_lit 0) D2M8K2.t2965 from rfl, allE_node, rows2964, irow2958, rows2965]
  all_goals rfl

theorem atot2958 : totK PD2M8K2 D2M8K2.u2958 = [0, 251615720192, 811504827883, 633181301585, 101311124869, 1242138600, 0, 0] := by
  rw [show D2M8K2.u2958 = KTree.node D2M8K2.t2964 (nat_lit 7214152) (nat_lit 3821762034) (nat_lit 0) D2M8K2.t2965 from rfl, totK_node, tot2964, tot2965]
  decide +kernel

theorem arows2959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2959 = true := by
  rw [show D2M8K2.u2959 = KTree.node D2M8K2.t2966 (nat_lit 7215858) (nat_lit 3224550533) (nat_lit 0) D2M8K2.t2967 from rfl, allE_node, rows2966, irow2959, rows2967]
  all_goals rfl

theorem atot2959 : totK PD2M8K2 D2M8K2.u2959 = [0, 120208286280, 557046305256, 769138500846, 293919044123, 20509029466, 0, 0] := by
  rw [show D2M8K2.u2959 = KTree.node D2M8K2.t2966 (nat_lit 7215858) (nat_lit 3224550533) (nat_lit 0) D2M8K2.t2967 from rfl, totK_node, tot2966, tot2967]
  decide +kernel

theorem arows2962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2962 = true := by
  rw [show D2M8K2.u2962 = KTree.node D2M8K2.t2968 (nat_lit 7217362) (nat_lit 2268420327) (nat_lit 0) D2M8K2.t2969 from rfl, allE_node, rows2968, irow2962, rows2969]
  all_goals rfl

theorem atot2962 : totK PD2M8K2 D2M8K2.u2962 = [0, 297310233710, 878759368554, 551840795678, 48181953626, 0, 0, 0] := by
  rw [show D2M8K2.u2962 = KTree.node D2M8K2.t2968 (nat_lit 7217362) (nat_lit 2268420327) (nat_lit 0) D2M8K2.t2969 from rfl, totK_node, tot2968, tot2969]
  decide +kernel

theorem arows2963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2963 = true := by
  rw [show D2M8K2.u2963 = KTree.node D2M8K2.t2970 (nat_lit 7219322) (nat_lit 3330842820) (nat_lit 0) D2M8K2.t2971 from rfl, allE_node, rows2970, irow2963, rows2971]
  all_goals rfl

theorem atot2963 : totK PD2M8K2 D2M8K2.u2963 = [0, 159897023672, 728160283703, 782717543211, 136428037779, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2963 = KTree.node D2M8K2.t2970 (nat_lit 7219322) (nat_lit 3330842820) (nat_lit 0) D2M8K2.t2971 from rfl, totK_node, tot2970, tot2971]
  decide +kernel

theorem arows2965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2965 = true := by
  rw [show D2M8K2.u2965 = KTree.node D2M8K2.t2972 (nat_lit 7224437) (nat_lit 2221120622) (nat_lit 0) D2M8K2.t2973 from rfl, allE_node, rows2972, irow2965, rows2973]
  all_goals rfl

theorem atot2965 : totK PD2M8K2 D2M8K2.u2965 = [0, 263322082821, 799224971343, 629933457348, 94134585698, 1164319620, 0, 0] := by
  rw [show D2M8K2.u2965 = KTree.node D2M8K2.t2972 (nat_lit 7224437) (nat_lit 2221120622) (nat_lit 0) D2M8K2.t2973 from rfl, totK_node, tot2972, tot2973]
  decide +kernel

theorem arows2966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2966 = true := by
  rw [show D2M8K2.u2966 = KTree.node D2M8K2.t2974 (nat_lit 7226114) (nat_lit 3617546541) (nat_lit 0) D2M8K2.t2975 from rfl, allE_node, rows2974, irow2966, rows2975]
  all_goals rfl

theorem atot2966 : totK PD2M8K2 D2M8K2.u2966 = [0, 153473951145, 636361673219, 751202020875, 216714861856, 11885407614, 0, 0] := by
  rw [show D2M8K2.u2966 = KTree.node D2M8K2.t2974 (nat_lit 7226114) (nat_lit 3617546541) (nat_lit 0) D2M8K2.t2975 from rfl, totK_node, tot2974, tot2975]
  decide +kernel

theorem arows2971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2971 = true := by
  rw [show D2M8K2.u2971 = KTree.node D2M8K2.t2976 (nat_lit 7231046) (nat_lit 2505608958) (nat_lit 0) D2M8K2.t2977 from rfl, allE_node, rows2976, irow2971, rows2977]
  all_goals rfl

theorem atot2971 : totK PD2M8K2 D2M8K2.u2971 = [0, 243138295128, 783163423964, 643006387336, 93279086841, 1096505104, 0, 0] := by
  rw [show D2M8K2.u2971 = KTree.node D2M8K2.t2976 (nat_lit 7231046) (nat_lit 2505608958) (nat_lit 0) D2M8K2.t2977 from rfl, totK_node, tot2976, tot2977]
  decide +kernel

theorem arows2972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2972 = true := by
  rw [show D2M8K2.u2972 = KTree.node D2M8K2.t2978 (nat_lit 7233058) (nat_lit 1606962963) (nat_lit 0) D2M8K2.t2979 from rfl, allE_node, rows2978, irow2972, rows2979]
  all_goals rfl

theorem atot2972 : totK PD2M8K2 D2M8K2.u2972 = [0, 190579556311, 731294758732, 738224173623, 134799760759, 3820764243, 0, 0] := by
  rw [show D2M8K2.u2972 = KTree.node D2M8K2.t2978 (nat_lit 7233058) (nat_lit 1606962963) (nat_lit 0) D2M8K2.t2979 from rfl, totK_node, tot2978, tot2979]
  decide +kernel

theorem arows2974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2974 = true := by
  rw [show D2M8K2.u2974 = KTree.node D2M8K2.t2980 (nat_lit 7234970) (nat_lit 4047264089) (nat_lit 0) D2M8K2.t2981 from rfl, allE_node, rows2980, irow2974, rows2981]
  all_goals rfl

theorem atot2974 : totK PD2M8K2 D2M8K2.u2974 = [0, 212280759857, 775414643333, 701164853986, 116057253262, 1268739303, 0, 0] := by
  rw [show D2M8K2.u2974 = KTree.node D2M8K2.t2980 (nat_lit 7234970) (nat_lit 4047264089) (nat_lit 0) D2M8K2.t2981 from rfl, totK_node, tot2980, tot2981]
  decide +kernel

theorem arows2975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2975 = true := by
  rw [show D2M8K2.u2975 = KTree.node D2M8K2.t2982 (nat_lit 7236793) (nat_lit 1386615146) (nat_lit 0) D2M8K2.t2983 from rfl, allE_node, rows2982, irow2975, rows2983]
  all_goals rfl

theorem atot2975 : totK PD2M8K2 D2M8K2.u2975 = [0, 0, 395177278272, 960477206901, 391096056024, 22062817559, 0, 0] := by
  rw [show D2M8K2.u2975 = KTree.node D2M8K2.t2982 (nat_lit 7236793) (nat_lit 1386615146) (nat_lit 0) D2M8K2.t2983 from rfl, totK_node, tot2982, tot2983]
  decide +kernel

theorem arows2978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2978 = true := by
  rw [show D2M8K2.u2978 = KTree.node D2M8K2.t2984 (nat_lit 7238394) (nat_lit 3693614493) (nat_lit 0) D2M8K2.t2985 from rfl, allE_node, rows2984, irow2978, rows2985]
  all_goals rfl

theorem atot2978 : totK PD2M8K2 D2M8K2.u2978 = [0, 0, 239722156149, 797504366821, 585761849770, 86558769187, 1275377855, 0] := by
  rw [show D2M8K2.u2978 = KTree.node D2M8K2.t2984 (nat_lit 7238394) (nat_lit 3693614493) (nat_lit 0) D2M8K2.t2985 from rfl, totK_node, tot2984, tot2985]
  decide +kernel

theorem arows2979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2979 = true := by
  rw [show D2M8K2.u2979 = KTree.node D2M8K2.t2986 (nat_lit 7244102) (nat_lit 4164973887) (nat_lit 0) D2M8K2.t2987 from rfl, allE_node, rows2986, irow2979, rows2987]
  all_goals rfl

theorem atot2979 : totK PD2M8K2 D2M8K2.u2979 = [0, 0, 302854343617, 905394549184, 505787316923, 33924260570, 0, 0] := by
  rw [show D2M8K2.u2979 = KTree.node D2M8K2.t2986 (nat_lit 7244102) (nat_lit 4164973887) (nat_lit 0) D2M8K2.t2987 from rfl, totK_node, tot2986, tot2987]
  decide +kernel

theorem arows2981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2981 = true := by
  rw [show D2M8K2.u2981 = KTree.node D2M8K2.t2988 (nat_lit 7250813) (nat_lit 2159182830) (nat_lit 0) D2M8K2.t2989 from rfl, allE_node, rows2988, irow2981, rows2989]
  all_goals rfl

theorem atot2981 : totK PD2M8K2 D2M8K2.u2981 = [0, 0, 355868961071, 942233075449, 414399756949, 23464679098, 0, 0] := by
  rw [show D2M8K2.u2981 = KTree.node D2M8K2.t2988 (nat_lit 7250813) (nat_lit 2159182830) (nat_lit 0) D2M8K2.t2989 from rfl, totK_node, tot2988, tot2989]
  decide +kernel

theorem arows2982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2982 = true := by
  rw [show D2M8K2.u2982 = KTree.node D2M8K2.t2990 (nat_lit 7254245) (nat_lit 2182607562) (nat_lit 0) D2M8K2.t2991 from rfl, allE_node, rows2990, irow2982, rows2991]
  all_goals rfl

theorem atot2982 : totK PD2M8K2 D2M8K2.u2982 = [0, 0, 426358676906, 982523804699, 345628638278, 10197400379, 0, 0] := by
  rw [show D2M8K2.u2982 = KTree.node D2M8K2.t2990 (nat_lit 7254245) (nat_lit 2182607562) (nat_lit 0) D2M8K2.t2991 from rfl, totK_node, tot2990, tot2991]
  decide +kernel

theorem arows2986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2986 = true := by
  rw [show D2M8K2.u2986 = KTree.node D2M8K2.t2992 (nat_lit 7261540) (nat_lit 4012699497) (nat_lit 0) D2M8K2.t2993 from rfl, allE_node, rows2992, irow2986, rows2993]
  all_goals rfl

theorem atot2986 : totK PD2M8K2 D2M8K2.u2986 = [0, 268356491922, 771943349853, 649143926786, 159223799206, 8859721110, 0, 0] := by
  rw [show D2M8K2.u2986 = KTree.node D2M8K2.t2992 (nat_lit 7261540) (nat_lit 4012699497) (nat_lit 0) D2M8K2.t2993 from rfl, totK_node, tot2992, tot2993]
  decide +kernel

theorem arows2987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2987 = true := by
  rw [show D2M8K2.u2987 = KTree.node D2M8K2.t2994 (nat_lit 7262718) (nat_lit 4010930859) (nat_lit 0) D2M8K2.t2995 from rfl, allE_node, rows2994, irow2987, rows2995]
  all_goals rfl

theorem atot2987 : totK PD2M8K2 D2M8K2.u2987 = [0, 176358198303, 685554666995, 717035757110, 233721890206, 21400436502, 0, 0] := by
  rw [show D2M8K2.u2987 = KTree.node D2M8K2.t2994 (nat_lit 7262718) (nat_lit 4010930859) (nat_lit 0) D2M8K2.t2995 from rfl, totK_node, tot2994, tot2995]
  decide +kernel

theorem arows2989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2989 = true := by
  rw [show D2M8K2.u2989 = KTree.node D2M8K2.t2996 (nat_lit 7264234) (nat_lit 3949781226) (nat_lit 0) D2M8K2.t2997 from rfl, allE_node, rows2996, irow2989, rows2997]
  all_goals rfl

theorem atot2989 : totK PD2M8K2 D2M8K2.u2989 = [0, 138229103118, 531793420275, 774658747545, 340677029635, 16099170968, 0, 0] := by
  rw [show D2M8K2.u2989 = KTree.node D2M8K2.t2996 (nat_lit 7264234) (nat_lit 3949781226) (nat_lit 0) D2M8K2.t2997 from rfl, totK_node, tot2996, tot2997]
  decide +kernel

theorem arows2990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2990 = true := by
  rw [show D2M8K2.u2990 = KTree.node D2M8K2.t2998 (nat_lit 7265724) (nat_lit 3113581972) (nat_lit 0) D2M8K2.t2999 from rfl, allE_node, rows2998, irow2990, rows2999]
  all_goals rfl

theorem atot2990 : totK PD2M8K2 D2M8K2.u2990 = [0, 287733081933, 879984236474, 589212650300, 56239329110, 0, 0, 0] := by
  rw [show D2M8K2.u2990 = KTree.node D2M8K2.t2998 (nat_lit 7265724) (nat_lit 3113581972) (nat_lit 0) D2M8K2.t2999 from rfl, totK_node, tot2998, tot2999]
  decide +kernel

theorem arows2993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2993 = true := by
  rw [show D2M8K2.u2993 = KTree.node D2M8K2.t3000 (nat_lit 7267491) (nat_lit 3637699960) (nat_lit 0) D2M8K2.t3001 from rfl, allE_node, rows3000, irow2993, rows3001]
  all_goals rfl

theorem atot2993 : totK PD2M8K2 D2M8K2.u2993 = [0, 90400450959, 591509335534, 892930606261, 247920324076, 11873025674, 0, 0] := by
  rw [show D2M8K2.u2993 = KTree.node D2M8K2.t3000 (nat_lit 7267491) (nat_lit 3637699960) (nat_lit 0) D2M8K2.t3001 from rfl, totK_node, tot3000, tot3001]
  decide +kernel

theorem arows2994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2994 = true := by
  rw [show D2M8K2.u2994 = KTree.node D2M8K2.t3002 (nat_lit 7269448) (nat_lit 3600272662) (nat_lit 0) D2M8K2.t3003 from rfl, allE_node, rows3002, irow2994, rows3003]
  all_goals rfl

theorem atot2994 : totK PD2M8K2 D2M8K2.u2994 = [0, 255988632237, 834428842321, 658659361503, 88648063072, 0, 0, 0] := by
  rw [show D2M8K2.u2994 = KTree.node D2M8K2.t3002 (nat_lit 7269448) (nat_lit 3600272662) (nat_lit 0) D2M8K2.t3003 from rfl, totK_node, tot3002, tot3003]
  decide +kernel

theorem arows2996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2996 = true := by
  rw [show D2M8K2.u2996 = KTree.node D2M8K2.t3004 (nat_lit 7271573) (nat_lit 2167391030) (nat_lit 0) D2M8K2.t3005 from rfl, allE_node, rows3004, irow2996, rows3005]
  all_goals rfl

theorem atot2996 : totK PD2M8K2 D2M8K2.u2996 = [0, 241155793433, 726174328245, 663248508921, 165213107952, 5439011083, 0, 0] := by
  rw [show D2M8K2.u2996 = KTree.node D2M8K2.t3004 (nat_lit 7271573) (nat_lit 2167391030) (nat_lit 0) D2M8K2.t3005 from rfl, totK_node, tot3004, tot3005]
  decide +kernel

theorem arows2997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2997 = true := by
  rw [show D2M8K2.u2997 = KTree.node D2M8K2.t3006 (nat_lit 7272816) (nat_lit 3373548254) (nat_lit 0) D2M8K2.t3007 from rfl, allE_node, rows3006, irow2997, rows3007]
  all_goals rfl

theorem atot2997 : totK PD2M8K2 D2M8K2.u2997 = [0, 170108921497, 811500018667, 750730990395, 84969815124, 0, 0, 0] := by
  rw [show D2M8K2.u2997 = KTree.node D2M8K2.t3006 (nat_lit 7272816) (nat_lit 3373548254) (nat_lit 0) D2M8K2.t3007 from rfl, totK_node, tot3006, tot3007]
  decide +kernel

theorem arows3003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3003 = true := by
  rw [show D2M8K2.u3003 = KTree.node D2M8K2.t3008 (nat_lit 7275271) (nat_lit 2159199382) (nat_lit 0) D2M8K2.t3009 from rfl, allE_node, rows3008, irow3003, rows3009]
  all_goals rfl

theorem atot3003 : totK PD2M8K2 D2M8K2.u3003 = [0, 302443277526, 805765425477, 592221539936, 120596309252, 3880716147, 0, 0] := by
  rw [show D2M8K2.u3003 = KTree.node D2M8K2.t3008 (nat_lit 7275271) (nat_lit 2159199382) (nat_lit 0) D2M8K2.t3009 from rfl, totK_node, tot3008, tot3009]
  decide +kernel

theorem arows3004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3004 = true := by
  rw [show D2M8K2.u3004 = KTree.node D2M8K2.t3010 (nat_lit 7276751) (nat_lit 2774660413) (nat_lit 0) D2M8K2.t3011 from rfl, allE_node, rows3010, irow3004, rows3011]
  all_goals rfl

theorem atot3004 : totK PD2M8K2 D2M8K2.u3004 = [0, 111042906525, 652236395400, 823716756094, 203461344034, 4925188030, 0, 0] := by
  rw [show D2M8K2.u3004 = KTree.node D2M8K2.t3010 (nat_lit 7276751) (nat_lit 2774660413) (nat_lit 0) D2M8K2.t3011 from rfl, totK_node, tot3010, tot3011]
  decide +kernel

theorem arows3006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3006 = true := by
  rw [show D2M8K2.u3006 = KTree.node D2M8K2.t3012 (nat_lit 7299197) (nat_lit 2283722222) (nat_lit 0) D2M8K2.t3013 from rfl, allE_node, rows3012, irow3006, rows3013]
  all_goals rfl

theorem atot3006 : totK PD2M8K2 D2M8K2.u3006 = [0, 231752941427, 702858135894, 628906145606, 197156982827, 12866082196, 0, 0] := by
  rw [show D2M8K2.u3006 = KTree.node D2M8K2.t3012 (nat_lit 7299197) (nat_lit 2283722222) (nat_lit 0) D2M8K2.t3013 from rfl, totK_node, tot3012, tot3013]
  decide +kernel

theorem arows3007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3007 = true := by
  rw [show D2M8K2.u3007 = KTree.node D2M8K2.t3014 (nat_lit 7300820) (nat_lit 3216646021) (nat_lit 0) D2M8K2.t3015 from rfl, allE_node, rows3014, irow3007, rows3015]
  all_goals rfl

theorem atot3007 : totK PD2M8K2 D2M8K2.u3007 = [0, 161010211928, 717674406704, 752280561209, 116491496616, 1334361349, 0, 0] := by
  rw [show D2M8K2.u3007 = KTree.node D2M8K2.t3014 (nat_lit 7300820) (nat_lit 3216646021) (nat_lit 0) D2M8K2.t3015 from rfl, totK_node, tot3014, tot3015]
  decide +kernel

theorem arows3010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3010 = true := by
  rw [show D2M8K2.u3010 = KTree.node D2M8K2.t3016 (nat_lit 7303164) (nat_lit 3112956706) (nat_lit 0) D2M8K2.t3017 from rfl, allE_node, rows3016, irow3010, rows3017]
  all_goals rfl

theorem atot3010 : totK PD2M8K2 D2M8K2.u3010 = [0, 338421404813, 892192430728, 568816623409, 52820868719, 0, 0, 0] := by
  rw [show D2M8K2.u3010 = KTree.node D2M8K2.t3016 (nat_lit 7303164) (nat_lit 3112956706) (nat_lit 0) D2M8K2.t3017 from rfl, totK_node, tot3016, tot3017]
  decide +kernel

theorem arows3011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3011 = true := by
  rw [show D2M8K2.u3011 = KTree.node D2M8K2.t3018 (nat_lit 7304723) (nat_lit 2709383176) (nat_lit 0) D2M8K2.t3019 from rfl, allE_node, rows3018, irow3011, rows3019]
  all_goals rfl

theorem atot3011 : totK PD2M8K2 D2M8K2.u3011 = [0, 87893730914, 593157281198, 831855707216, 289754002200, 18567029682, 0, 0] := by
  rw [show D2M8K2.u3011 = KTree.node D2M8K2.t3018 (nat_lit 7304723) (nat_lit 2709383176) (nat_lit 0) D2M8K2.t3019 from rfl, totK_node, tot3018, tot3019]
  decide +kernel

theorem arows3013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3013 = true := by
  rw [show D2M8K2.u3013 = KTree.node D2M8K2.t3020 (nat_lit 7306118) (nat_lit 3293395900) (nat_lit 0) D2M8K2.t3021 from rfl, allE_node, rows3020, irow3013, rows3021]
  all_goals rfl

theorem atot3013 : totK PD2M8K2 D2M8K2.u3013 = [0, 269165122283, 723058249948, 648496386903, 182594435551, 5521894595, 0, 0] := by
  rw [show D2M8K2.u3013 = KTree.node D2M8K2.t3020 (nat_lit 7306118) (nat_lit 3293395900) (nat_lit 0) D2M8K2.t3021 from rfl, totK_node, tot3020, tot3021]
  decide +kernel

theorem arows3014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3014 = true := by
  rw [show D2M8K2.u3014 = KTree.node D2M8K2.t3022 (nat_lit 7307586) (nat_lit 2691695053) (nat_lit 0) D2M8K2.t3023 from rfl, allE_node, rows3022, irow3014, rows3023]
  all_goals rfl

theorem atot3014 : totK PD2M8K2 D2M8K2.u3014 = [0, 176333444930, 768544812206, 746862285800, 118945106554, 1164319620, 0, 0] := by
  rw [show D2M8K2.u3014 = KTree.node D2M8K2.t3022 (nat_lit 7307586) (nat_lit 2691695053) (nat_lit 0) D2M8K2.t3023 from rfl, totK_node, tot3022, tot3023]
  decide +kernel

theorem arows3018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3018 = true := by
  rw [show D2M8K2.u3018 = KTree.node D2M8K2.t3024 (nat_lit 7309272) (nat_lit 3543776591) (nat_lit 0) D2M8K2.t3025 from rfl, allE_node, rows3024, irow3018, rows3025]
  all_goals rfl

theorem atot3018 : totK PD2M8K2 D2M8K2.u3018 = [0, 169592521413, 645713434051, 737975956613, 214859473262, 11885407614, 0, 0] := by
  rw [show D2M8K2.u3018 = KTree.node D2M8K2.t3024 (nat_lit 7309272) (nat_lit 3543776591) (nat_lit 0) D2M8K2.t3025 from rfl, totK_node, tot3024, tot3025]
  decide +kernel

theorem arows3019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3019 = true := by
  rw [show D2M8K2.u3019 = KTree.node D2M8K2.t3026 (nat_lit 7314100) (nat_lit 3992702721) (nat_lit 0) D2M8K2.t3027 from rfl, allE_node, rows3026, irow3019, rows3027]
  all_goals rfl

theorem atot3019 : totK PD2M8K2 D2M8K2.u3019 = [0, 245537113472, 796061132141, 644339890315, 88053400791, 1062926506, 0, 0] := by
  rw [show D2M8K2.u3019 = KTree.node D2M8K2.t3026 (nat_lit 7314100) (nat_lit 3992702721) (nat_lit 0) D2M8K2.t3027 from rfl, totK_node, tot3026, tot3027]
  decide +kernel

theorem arows3021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3021 = true := by
  rw [show D2M8K2.u3021 = KTree.node D2M8K2.t3028 (nat_lit 7316414) (nat_lit 3169116502) (nat_lit 0) D2M8K2.t3029 from rfl, allE_node, rows3028, irow3021, rows3029]
  all_goals rfl

theorem atot3021 : totK PD2M8K2 D2M8K2.u3021 = [0, 211455270809, 739315324949, 710926268147, 131335691920, 3783381897, 0, 0] := by
  rw [show D2M8K2.u3021 = KTree.node D2M8K2.t3028 (nat_lit 7316414) (nat_lit 3169116502) (nat_lit 0) D2M8K2.t3029 from rfl, totK_node, tot3028, tot3029]
  decide +kernel

theorem arows3022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3022 = true := by
  rw [show D2M8K2.u3022 = KTree.node D2M8K2.t3030 (nat_lit 7317926) (nat_lit 4024933322) (nat_lit 0) D2M8K2.t3031 from rfl, allE_node, rows3030, irow3022, rows3031]
  all_goals rfl

theorem atot3022 : totK PD2M8K2 D2M8K2.u3022 = [0, 209077519582, 769349920924, 700307874553, 113910670328, 1240621948, 0, 0] := by
  rw [show D2M8K2.u3022 = KTree.node D2M8K2.t3030 (nat_lit 7317926) (nat_lit 4024933322) (nat_lit 0) D2M8K2.t3031 from rfl, totK_node, tot3030, tot3031]
  decide +kernel

theorem arows3025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3025 = true := by
  rw [show D2M8K2.u3025 = KTree.node D2M8K2.t3032 (nat_lit 7319720) (nat_lit 2268883493) (nat_lit 0) D2M8K2.t3033 from rfl, allE_node, rows3032, irow3025, rows3033]
  all_goals rfl

theorem atot3025 : totK PD2M8K2 D2M8K2.u3025 = [0, 0, 406364575641, 962258164633, 391480240781, 20868119709, 0, 0] := by
  rw [show D2M8K2.u3025 = KTree.node D2M8K2.t3032 (nat_lit 7319720) (nat_lit 2268883493) (nat_lit 0) D2M8K2.t3033 from rfl, totK_node, tot3032, tot3033]
  decide +kernel

theorem arows3026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3026 = true := by
  rw [show D2M8K2.u3026 = KTree.node D2M8K2.t3034 (nat_lit 7321384) (nat_lit 3801061395) (nat_lit 0) D2M8K2.t3035 from rfl, allE_node, rows3034, irow3026, rows3035]
  all_goals rfl

theorem atot3026 : totK PD2M8K2 D2M8K2.u3026 = [0, 0, 214817750575, 758518612354, 610358371704, 91041440771, 1206465782, 0] := by
  rw [show D2M8K2.u3026 = KTree.node D2M8K2.t3034 (nat_lit 7321384) (nat_lit 3801061395) (nat_lit 0) D2M8K2.t3035 from rfl, totK_node, tot3034, tot3035]
  decide +kernel

theorem arows3028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3028 = true := by
  rw [show D2M8K2.u3028 = KTree.node D2M8K2.t3036 (nat_lit 7323834) (nat_lit 2082507044) (nat_lit 0) D2M8K2.t3037 from rfl, allE_node, rows3036, irow3028, rows3037]
  all_goals rfl

theorem atot3028 : totK PD2M8K2 D2M8K2.u3028 = [0, 0, 334307030451, 903365129834, 511078659935, 40309002397, 0, 0] := by
  rw [show D2M8K2.u3028 = KTree.node D2M8K2.t3036 (nat_lit 7323834) (nat_lit 2082507044) (nat_lit 0) D2M8K2.t3037 from rfl, totK_node, tot3036, tot3037]
  decide +kernel

theorem arows3029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3029 = true := by
  rw [show D2M8K2.u3029 = KTree.node D2M8K2.t3038 (nat_lit 7327048) (nat_lit 3875655435) (nat_lit 0) D2M8K2.t3039 from rfl, allE_node, rows3038, irow3029, rows3039]
  all_goals rfl

theorem atot3029 : totK PD2M8K2 D2M8K2.u3029 = [0, 0, 368672095649, 934962206892, 458592443499, 33840825529, 0, 0] := by
  rw [show D2M8K2.u3029 = KTree.node D2M8K2.t3038 (nat_lit 7327048) (nat_lit 3875655435) (nat_lit 0) D2M8K2.t3039 from rfl, totK_node, tot3038, tot3039]
  decide +kernel

theorem arows3034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3034 = true := by
  rw [show D2M8K2.u3034 = KTree.node D2M8K2.t3040 (nat_lit 7328518) (nat_lit 3490822427) (nat_lit 0) D2M8K2.t3041 from rfl, allE_node, rows3040, irow3034, rows3041]
  all_goals rfl

theorem atot3034 : totK PD2M8K2 D2M8K2.u3034 = [0, 0, 156513048187, 683536961796, 723562587877, 183828372590, 8137081540, 0] := by
  rw [show D2M8K2.u3034 = KTree.node D2M8K2.t3040 (nat_lit 7328518) (nat_lit 3490822427) (nat_lit 0) D2M8K2.t3041 from rfl, totK_node, tot3040, tot3041]
  decide +kernel

theorem arows3035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3035 = true := by
  rw [show D2M8K2.u3035 = KTree.node D2M8K2.t3042 (nat_lit 7333789) (nat_lit 1280524991) (nat_lit 0) D2M8K2.t3043 from rfl, allE_node, rows3042, irow3035, rows3043]
  all_goals rfl

theorem atot3035 : totK PD2M8K2 D2M8K2.u3035 = [0, 0, 254878633762, 778084868595, 586296246739, 111177923703, 4879115834, 0] := by
  rw [show D2M8K2.u3035 = KTree.node D2M8K2.t3042 (nat_lit 7333789) (nat_lit 1280524991) (nat_lit 0) D2M8K2.t3043 from rfl, totK_node, tot3042, tot3043]
  decide +kernel

theorem arows3037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3037 = true := by
  rw [show D2M8K2.u3037 = KTree.node D2M8K2.t3044 (nat_lit 7335429) (nat_lit 1497055351) (nat_lit 0) D2M8K2.t3045 from rfl, allE_node, rows3044, irow3037, rows3045]
  all_goals rfl

theorem atot3037 : totK PD2M8K2 D2M8K2.u3037 = [0, 0, 154179626819, 754326267308, 673652640163, 90653057521, 1021600638, 0] := by
  rw [show D2M8K2.u3037 = KTree.node D2M8K2.t3044 (nat_lit 7335429) (nat_lit 1497055351) (nat_lit 0) D2M8K2.t3045 from rfl, totK_node, tot3044, tot3045]
  decide +kernel

theorem arows3038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3038 = true := by
  rw [show D2M8K2.u3038 = KTree.node D2M8K2.t3046 (nat_lit 7337507) (nat_lit 2970155676) (nat_lit 0) D2M8K2.t3047 from rfl, allE_node, rows3046, irow3038, rows3047]
  all_goals rfl

theorem atot3038 : totK PD2M8K2 D2M8K2.u3038 = [0, 0, 359028659378, 844640153756, 462732323715, 80926605361, 3552795014, 0] := by
  rw [show D2M8K2.u3038 = KTree.node D2M8K2.t3046 (nat_lit 7337507) (nat_lit 2970155676) (nat_lit 0) D2M8K2.t3047 from rfl, totK_node, tot3046, tot3047]
  decide +kernel

theorem arows3041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3041 = true := by
  rw [show D2M8K2.u3041 = KTree.node D2M8K2.t3048 (nat_lit 7382691) (nat_lit 3346817874) (nat_lit 0) D2M8K2.t3049 from rfl, allE_node, rows3048, irow3041, rows3049]
  all_goals rfl

theorem atot3041 : totK PD2M8K2 D2M8K2.u3041 = [0, 323650174906, 808993659121, 506629155528, 125090611559, 8935385149, 0, 0] := by
  rw [show D2M8K2.u3041 = KTree.node D2M8K2.t3048 (nat_lit 7382691) (nat_lit 3346817874) (nat_lit 0) D2M8K2.t3049 from rfl, totK_node, tot3048, tot3049]
  decide +kernel

theorem arows3042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3042 = true := by
  rw [show D2M8K2.u3042 = KTree.node D2M8K2.t3050 (nat_lit 7384372) (nat_lit 4059120367) (nat_lit 0) D2M8K2.t3051 from rfl, allE_node, rows3050, irow3042, rows3051]
  all_goals rfl

theorem atot3042 : totK PD2M8K2 D2M8K2.u3042 = [0, 137743388721, 697789906647, 812599967081, 130529462933, 1310166938, 0, 0] := by
  rw [show D2M8K2.u3042 = KTree.node D2M8K2.t3050 (nat_lit 7384372) (nat_lit 4059120367) (nat_lit 0) D2M8K2.t3051 from rfl, totK_node, tot3050, tot3051]
  decide +kernel

theorem arows3044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3044 = true := by
  rw [show D2M8K2.u3044 = KTree.node D2M8K2.t3052 (nat_lit 7386458) (nat_lit 4021817023) (nat_lit 0) D2M8K2.t3053 from rfl, allE_node, rows3052, irow3044, rows3053]
  all_goals rfl

theorem atot3044 : totK PD2M8K2 D2M8K2.u3044 = [0, 334179363908, 931456629597, 531086259498, 43256039713, 0, 0, 0] := by
  rw [show D2M8K2.u3044 = KTree.node D2M8K2.t3052 (nat_lit 7386458) (nat_lit 4021817023) (nat_lit 0) D2M8K2.t3053 from rfl, totK_node, tot3052, tot3053]
  decide +kernel

theorem arows3045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3045 = true := by
  rw [show D2M8K2.u3045 = KTree.node D2M8K2.t3054 (nat_lit 7388037) (nat_lit 1112375572) (nat_lit 0) D2M8K2.t3055 from rfl, allE_node, rows3054, irow3045, rows3055]
  all_goals rfl

theorem atot3045 : totK PD2M8K2 D2M8K2.u3045 = [0, 33121773576, 474932004892, 958535405262, 354116005359, 15013989272, 0, 0] := by
  rw [show D2M8K2.u3045 = KTree.node D2M8K2.t3054 (nat_lit 7388037) (nat_lit 1112375572) (nat_lit 0) D2M8K2.t3055 from rfl, totK_node, tot3054, tot3055]
  decide +kernel

theorem arows3049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3049 = true := by
  rw [show D2M8K2.u3049 = KTree.node D2M8K2.t3056 (nat_lit 7389549) (nat_lit 1478205480) (nat_lit 0) D2M8K2.t3057 from rfl, allE_node, rows3056, irow3049, rows3057]
  all_goals rfl

theorem atot3049 : totK PD2M8K2 D2M8K2.u3049 = [0, 371084009493, 930047488807, 472258794459, 35100677637, 0, 0, 0] := by
  rw [show D2M8K2.u3049 = KTree.node D2M8K2.t3056 (nat_lit 7389549) (nat_lit 1478205480) (nat_lit 0) D2M8K2.t3057 from rfl, totK_node, tot3056, tot3057]
  decide +kernel

theorem arows3050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3050 = true := by
  rw [show D2M8K2.u3050 = KTree.node D2M8K2.t3058 (nat_lit 7391261) (nat_lit 2332668471) (nat_lit 0) D2M8K2.t3059 from rfl, allE_node, rows3058, irow3050, rows3059]
  all_goals rfl

theorem atot3050 : totK PD2M8K2 D2M8K2.u3050 = [0, 18811892075, 510002527112, 936374684625, 283349711033, 13049727234, 0, 0] := by
  rw [show D2M8K2.u3050 = KTree.node D2M8K2.t3058 (nat_lit 7391261) (nat_lit 2332668471) (nat_lit 0) D2M8K2.t3059 from rfl, totK_node, tot3058, tot3059]
  decide +kernel

theorem arows3052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3052 = true := by
  rw [show D2M8K2.u3052 = KTree.node D2M8K2.t3060 (nat_lit 7393294) (nat_lit 3702360550) (nat_lit 0) D2M8K2.t3061 from rfl, allE_node, rows3060, irow3052, rows3061]
  all_goals rfl

theorem atot3052 : totK PD2M8K2 D2M8K2.u3052 = [0, 327046332664, 912757906816, 539104462044, 39853266545, 0, 0, 0] := by
  rw [show D2M8K2.u3052 = KTree.node D2M8K2.t3060 (nat_lit 7393294) (nat_lit 3702360550) (nat_lit 0) D2M8K2.t3061 from rfl, totK_node, tot3060, tot3061]
  decide +kernel

theorem arows3053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3053 = true := by
  rw [show D2M8K2.u3053 = KTree.node D2M8K2.t3062 (nat_lit 7395440) (nat_lit 3698671542) (nat_lit 0) D2M8K2.t3063 from rfl, allE_node, rows3062, irow3053, rows3063]
  all_goals rfl

theorem atot3053 : totK PD2M8K2 D2M8K2.u3053 = [0, 172268089426, 677314581563, 760445760854, 171776107375, 4686148432, 0, 0] := by
  rw [show D2M8K2.u3053 = KTree.node D2M8K2.t3062 (nat_lit 7395440) (nat_lit 3698671542) (nat_lit 0) D2M8K2.t3063 from rfl, totK_node, tot3062, tot3063]
  decide +kernel

theorem arows3056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3056 = true := by
  rw [show D2M8K2.u3056 = KTree.node D2M8K2.t3064 (nat_lit 7396962) (nat_lit 3319678605) (nat_lit 0) D2M8K2.t3065 from rfl, allE_node, rows3064, irow3056, rows3065]
  all_goals rfl

theorem atot3056 : totK PD2M8K2 D2M8K2.u3056 = [0, 263188337172, 811441384325, 620745897959, 92338762625, 1096505104, 0, 0] := by
  rw [show D2M8K2.u3056 = KTree.node D2M8K2.t3064 (nat_lit 7396962) (nat_lit 3319678605) (nat_lit 0) D2M8K2.t3065 from rfl, totK_node, tot3064, tot3065]
  decide +kernel

theorem arows3057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3057 = true := by
  rw [show D2M8K2.u3057 = KTree.node D2M8K2.t3066 (nat_lit 7398893) (nat_lit 1711811678) (nat_lit 0) D2M8K2.t3067 from rfl, allE_node, rows3066, irow3057, rows3067]
  all_goals rfl

theorem atot3057 : totK PD2M8K2 D2M8K2.u3057 = [0, 0, 481139710230, 992146741164, 293739390573, 11162872812, 0, 0] := by
  rw [show D2M8K2.u3057 = KTree.node D2M8K2.t3066 (nat_lit 7398893) (nat_lit 1711811678) (nat_lit 0) D2M8K2.t3067 from rfl, totK_node, tot3066, tot3067]
  decide +kernel

theorem arows3059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3059 = true := by
  rw [show D2M8K2.u3059 = KTree.node D2M8K2.t3068 (nat_lit 7404347) (nat_lit 2284401434) (nat_lit 0) D2M8K2.t3069 from rfl, allE_node, rows3068, irow3059, rows3069]
  all_goals rfl

theorem atot3059 : totK PD2M8K2 D2M8K2.u3059 = [0, 0, 200685077174, 798160047285, 609741516748, 71877837511, 1103454931, 0] := by
  rw [show D2M8K2.u3059 = KTree.node D2M8K2.t3068 (nat_lit 7404347) (nat_lit 2284401434) (nat_lit 0) D2M8K2.t3069 from rfl, totK_node, tot3068, tot3069]
  decide +kernel

theorem arows3060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3060 = true := by
  rw [show D2M8K2.u3060 = KTree.node D2M8K2.t3070 (nat_lit 7406960) (nat_lit 3680307018) (nat_lit 0) D2M8K2.t3071 from rfl, allE_node, rows3070, irow3060, rows3071]
  all_goals rfl

theorem atot3060 : totK PD2M8K2 D2M8K2.u3060 = [0, 0, 432481395861, 935447419097, 417493165519, 21789099889, 0, 0] := by
  rw [show D2M8K2.u3060 = KTree.node D2M8K2.t3070 (nat_lit 7406960) (nat_lit 3680307018) (nat_lit 0) D2M8K2.t3071 from rfl, totK_node, tot3070, tot3071]
  decide +kernel

theorem arows3070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3070 = true := by
  rw [show D2M8K2.u3070 = KTree.node D2M8K2.t3072 (nat_lit 7410298) (nat_lit 3906565279) (nat_lit 0) D2M8K2.t3073 from rfl, allE_node, rows3072, irow3070, rows3073]
  all_goals rfl

theorem atot3070 : totK PD2M8K2 D2M8K2.u3070 = [0, 0, 386717263888, 945911317303, 408258039168, 23272095769, 0, 0] := by
  rw [show D2M8K2.u3070 = KTree.node D2M8K2.t3072 (nat_lit 7410298) (nat_lit 3906565279) (nat_lit 0) D2M8K2.t3073 from rfl, totK_node, tot3072, tot3073]
  decide +kernel

theorem arows3071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3071 = true := by
  rw [show D2M8K2.u3071 = KTree.node D2M8K2.t3074 (nat_lit 7414122) (nat_lit 3873004378) (nat_lit 0) D2M8K2.t3075 from rfl, allE_node, rows3074, irow3071, rows3075]
  all_goals rfl

theorem atot3071 : totK PD2M8K2 D2M8K2.u3071 = [0, 0, 448294395646, 963160819612, 319346940964, 10013033234, 0, 0] := by
  rw [show D2M8K2.u3071 = KTree.node D2M8K2.t3074 (nat_lit 7414122) (nat_lit 3873004378) (nat_lit 0) D2M8K2.t3075 from rfl, totK_node, tot3074, tot3075]
  decide +kernel

theorem arows3073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3073 = true := by
  rw [show D2M8K2.u3073 = KTree.node D2M8K2.t3076 (nat_lit 7417538) (nat_lit 4021558888) (nat_lit 0) D2M8K2.t3077 from rfl, allE_node, rows3076, irow3073, rows3077]
  all_goals rfl

theorem atot3073 : totK PD2M8K2 D2M8K2.u3073 = [0, 0, 303486988806, 876360452640, 504957025206, 46714702682, 0, 0] := by
  rw [show D2M8K2.u3073 = KTree.node D2M8K2.t3076 (nat_lit 7417538) (nat_lit 4021558888) (nat_lit 0) D2M8K2.t3077 from rfl, totK_node, tot3076, tot3077]
  decide +kernel

theorem arows3074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3074 = true := by
  rw [show D2M8K2.u3074 = KTree.node D2M8K2.t3078 (nat_lit 7419605) (nat_lit 2033961413) (nat_lit 0) D2M8K2.t3079 from rfl, allE_node, rows3078, irow3074, rows3079]
  all_goals rfl

theorem atot3074 : totK PD2M8K2 D2M8K2.u3074 = [0, 173180509234, 408332239585, 482839039382, 523551812355, 125572988479, 3718133097, 0] := by
  rw [show D2M8K2.u3074 = KTree.node D2M8K2.t3078 (nat_lit 7419605) (nat_lit 2033961413) (nat_lit 0) D2M8K2.t3079 from rfl, totK_node, tot3078, tot3079]
  decide +kernel

theorem arows3077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3077 = true := by
  rw [show D2M8K2.u3077 = KTree.node D2M8K2.t3080 (nat_lit 7425065) (nat_lit 1624471130) (nat_lit 0) D2M8K2.t3081 from rfl, allE_node, rows3080, irow3077, rows3081]
  all_goals rfl

theorem atot3077 : totK PD2M8K2 D2M8K2.u3077 = [0, 205348107480, 752516034272, 703775496256, 114925288015, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3077 = KTree.node D2M8K2.t3080 (nat_lit 7425065) (nat_lit 1624471130) (nat_lit 0) D2M8K2.t3081 from rfl, totK_node, tot3080, tot3081]
  decide +kernel

theorem arows3078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3078 = true := by
  rw [show D2M8K2.u3078 = KTree.node D2M8K2.t3082 (nat_lit 7427468) (nat_lit 3050441555) (nat_lit 0) D2M8K2.t3083 from rfl, allE_node, rows3082, irow3078, rows3083]
  all_goals rfl

theorem atot3078 : totK PD2M8K2 D2M8K2.u3078 = [0, 261155190359, 833343584213, 670922451099, 71778512802, 0, 0, 0] := by
  rw [show D2M8K2.u3078 = KTree.node D2M8K2.t3082 (nat_lit 7427468) (nat_lit 3050441555) (nat_lit 0) D2M8K2.t3083 from rfl, totK_node, tot3082, tot3083]
  decide +kernel

theorem arows3080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3080 = true := by
  rw [show D2M8K2.u3080 = KTree.node D2M8K2.t3084 (nat_lit 7429029) (nat_lit 1370821740) (nat_lit 0) D2M8K2.t3085 from rfl, allE_node, rows3084, irow3080, rows3085]
  all_goals rfl

theorem atot3080 : totK PD2M8K2 D2M8K2.u3080 = [0, 159406523291, 641846187248, 725548218992, 284098544434, 23322377560, 0, 0] := by
  rw [show D2M8K2.u3080 = KTree.node D2M8K2.t3084 (nat_lit 7429029) (nat_lit 1370821740) (nat_lit 0) D2M8K2.t3085 from rfl, totK_node, tot3084, tot3085]
  decide +kernel

theorem arows3081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3081 = true := by
  rw [show D2M8K2.u3081 = KTree.node D2M8K2.t3086 (nat_lit 7430321) (nat_lit 1185978409) (nat_lit 0) D2M8K2.t3087 from rfl, allE_node, rows3086, irow3081, rows3087]
  all_goals rfl

theorem atot3081 : totK PD2M8K2 D2M8K2.u3081 = [0, 171120547633, 621124254040, 750323364845, 258183653498, 9440021337, 0, 0] := by
  rw [show D2M8K2.u3081 = KTree.node D2M8K2.t3086 (nat_lit 7430321) (nat_lit 1185978409) (nat_lit 0) D2M8K2.t3087 from rfl, totK_node, tot3086, tot3087]
  decide +kernel

theorem arows3085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3085 = true := by
  rw [show D2M8K2.u3085 = KTree.node D2M8K2.t3088 (nat_lit 7431852) (nat_lit 3556017470) (nat_lit 0) D2M8K2.t3089 from rfl, allE_node, rows3088, irow3085, rows3089]
  all_goals rfl

theorem atot3085 : totK PD2M8K2 D2M8K2.u3085 = [0, 252605897231, 792054585360, 654645569422, 103269569631, 1164319620, 0, 0] := by
  rw [show D2M8K2.u3085 = KTree.node D2M8K2.t3088 (nat_lit 7431852) (nat_lit 3556017470) (nat_lit 0) D2M8K2.t3089 from rfl, totK_node, tot3088, tot3089]
  decide +kernel

theorem arows3086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3086 = true := by
  rw [show D2M8K2.u3086 = KTree.node D2M8K2.t3090 (nat_lit 7433632) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t3091 from rfl, allE_node, rows3090, irow3086, rows3091]
  all_goals rfl

theorem atot3086 : totK PD2M8K2 D2M8K2.u3086 = [0, 165657465514, 693821798549, 775900862086, 176479196974, 8419352411, 0, 0] := by
  rw [show D2M8K2.u3086 = KTree.node D2M8K2.t3090 (nat_lit 7433632) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t3091 from rfl, totK_node, tot3090, tot3091]
  decide +kernel

theorem arows3088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3088 = true := by
  rw [show D2M8K2.u3088 = KTree.node D2M8K2.t3092 (nat_lit 7435600) (nat_lit 3007294420) (nat_lit 0) D2M8K2.t3093 from rfl, allE_node, rows3092, irow3088, rows3093]
  all_goals rfl

theorem atot3088 : totK PD2M8K2 D2M8K2.u3088 = [0, 160294956958, 689736741290, 774979211522, 179869721054, 5228939780, 0, 0] := by
  rw [show D2M8K2.u3088 = KTree.node D2M8K2.t3092 (nat_lit 7435600) (nat_lit 3007294420) (nat_lit 0) D2M8K2.t3093 from rfl, totK_node, tot3092, tot3093]
  decide +kernel

theorem arows3089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3089 = true := by
  rw [show D2M8K2.u3089 = KTree.node D2M8K2.t3094 (nat_lit 7441234) (nat_lit 3994184913) (nat_lit 0) D2M8K2.t3095 from rfl, allE_node, rows3094, irow3089, rows3095]
  all_goals rfl

theorem atot3089 : totK PD2M8K2 D2M8K2.u3089 = [0, 346144049830, 902895096412, 528415958056, 54765075891, 0, 0, 0] := by
  rw [show D2M8K2.u3089 = KTree.node D2M8K2.t3094 (nat_lit 7441234) (nat_lit 3994184913) (nat_lit 0) D2M8K2.t3095 from rfl, totK_node, tot3094, tot3095]
  decide +kernel

theorem arows3092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3092 = true := by
  rw [show D2M8K2.u3092 = KTree.node D2M8K2.t3096 (nat_lit 7442658) (nat_lit 2567541942) (nat_lit 0) D2M8K2.t3097 from rfl, allE_node, rows3096, irow3092, rows3097]
  all_goals rfl

theorem atot3092 : totK PD2M8K2 D2M8K2.u3092 = [0, 93763323609, 625208864679, 862176856336, 214733900518, 4967996017, 0, 0] := by
  rw [show D2M8K2.u3092 = KTree.node D2M8K2.t3096 (nat_lit 7442658) (nat_lit 2567541942) (nat_lit 0) D2M8K2.t3097 from rfl, totK_node, tot3096, tot3097]
  decide +kernel

theorem arows3093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3093 = true := by
  rw [show D2M8K2.u3093 = KTree.node D2M8K2.t3098 (nat_lit 7465068) (nat_lit 3216297692) (nat_lit 0) D2M8K2.t3099 from rfl, allE_node, rows3098, irow3093, rows3099]
  all_goals rfl

theorem atot3093 : totK PD2M8K2 D2M8K2.u3093 = [250871743540, 578966563117, 359697282085, 375604254207, 202927325469, 17014456371, 0, 0] := by
  rw [show D2M8K2.u3093 = KTree.node D2M8K2.t3098 (nat_lit 7465068) (nat_lit 3216297692) (nat_lit 0) D2M8K2.t3099 from rfl, totK_node, tot3098, tot3099]
  decide +kernel

theorem arows3095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3095 = true := by
  rw [show D2M8K2.u3095 = KTree.node D2M8K2.t3100 (nat_lit 7466617) (nat_lit 1444012582) (nat_lit 0) D2M8K2.t3101 from rfl, allE_node, rows3100, irow3095, rows3101]
  all_goals rfl

theorem atot3095 : totK PD2M8K2 D2M8K2.u3095 = [170955329715, 739367470013, 750010394040, 127245900441, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3095 = KTree.node D2M8K2.t3100 (nat_lit 7466617) (nat_lit 1444012582) (nat_lit 0) D2M8K2.t3101 from rfl, totK_node, tot3100, tot3101]
  decide +kernel

theorem arows3096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3096 = true := by
  rw [show D2M8K2.u3096 = KTree.node D2M8K2.t3102 (nat_lit 7475654) (nat_lit 4164854252) (nat_lit 0) D2M8K2.t3103 from rfl, allE_node, rows3102, irow3096, rows3103]
  all_goals rfl

theorem atot3096 : totK PD2M8K2 D2M8K2.u3096 = [287300219701, 852637231872, 618717151307, 66606549359, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3096 = KTree.node D2M8K2.t3102 (nat_lit 7475654) (nat_lit 4164854252) (nat_lit 0) D2M8K2.t3103 from rfl, totK_node, tot3102, tot3103]
  decide +kernel

theorem arows3101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3101 = true := by
  rw [show D2M8K2.u3101 = KTree.node D2M8K2.t3104 (nat_lit 7477138) (nat_lit 3882366158) (nat_lit 0) D2M8K2.t3105 from rfl, allE_node, rows3104, irow3101, rows3105]
  all_goals rfl

theorem atot3101 : totK PD2M8K2 D2M8K2.u3101 = [137371426407, 653172275143, 776823331503, 208887670261, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u3101 = KTree.node D2M8K2.t3104 (nat_lit 7477138) (nat_lit 3882366158) (nat_lit 0) D2M8K2.t3105 from rfl, totK_node, tot3104, tot3105]
  decide +kernel

theorem arows3102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3102 = true := by
  rw [show D2M8K2.u3102 = KTree.node D2M8K2.t3106 (nat_lit 7478929) (nat_lit 1560874839) (nat_lit 0) D2M8K2.t3107 from rfl, allE_node, rows3106, irow3102, rows3107]
  all_goals rfl

theorem atot3102 : totK PD2M8K2 D2M8K2.u3102 = [231275134888, 738291393071, 663107487743, 137360427386, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u3102 = KTree.node D2M8K2.t3106 (nat_lit 7478929) (nat_lit 1560874839) (nat_lit 0) D2M8K2.t3107 from rfl, totK_node, tot3106, tot3107]
  decide +kernel

theorem arows3104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3104 = true := by
  rw [show D2M8K2.u3104 = KTree.node D2M8K2.t3108 (nat_lit 7480564) (nat_lit 3949179261) (nat_lit 0) D2M8K2.t3109 from rfl, allE_node, rows3108, irow3104, rows3109]
  all_goals rfl

theorem atot3104 : totK PD2M8K2 D2M8K2.u3104 = [166665214215, 749178656656, 759023732019, 118519720879, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u3104 = KTree.node D2M8K2.t3108 (nat_lit 7480564) (nat_lit 3949179261) (nat_lit 0) D2M8K2.t3109 from rfl, totK_node, tot3108, tot3109]
  decide +kernel

theorem arows3105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3105 = true := by
  rw [show D2M8K2.u3105 = KTree.node D2M8K2.t3110 (nat_lit 7482590) (nat_lit 3846374853) (nat_lit 0) D2M8K2.t3111 from rfl, allE_node, rows3110, irow3105, rows3111]
  all_goals rfl

theorem atot3105 : totK PD2M8K2 D2M8K2.u3105 = [311613818781, 811509688340, 562328148081, 118108279066, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u3105 = KTree.node D2M8K2.t3110 (nat_lit 7482590) (nat_lit 3846374853) (nat_lit 0) D2M8K2.t3111 from rfl, totK_node, tot3110, tot3111]
  decide +kernel

theorem arows3108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3108 = true := by
  rw [show D2M8K2.u3108 = KTree.node D2M8K2.t3112 (nat_lit 7484120) (nat_lit 3210042033) (nat_lit 0) D2M8K2.t3113 from rfl, allE_node, rows3112, irow3108, rows3113]
  all_goals rfl

theorem atot3108 : totK PD2M8K2 D2M8K2.u3108 = [91792297750, 621326196354, 860850908243, 217468726092, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u3108 = KTree.node D2M8K2.t3112 (nat_lit 7484120) (nat_lit 3210042033) (nat_lit 0) D2M8K2.t3113 from rfl, totK_node, tot3112, tot3113]
  decide +kernel

theorem arows3109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3109 = true := by
  rw [show D2M8K2.u3109 = KTree.node D2M8K2.t3114 (nat_lit 7485845) (nat_lit 2190013337) (nat_lit 0) D2M8K2.t3115 from rfl, allE_node, rows3114, irow3109, rows3115]
  all_goals rfl

theorem atot3109 : totK PD2M8K2 D2M8K2.u3109 = [0, 341166542185, 928587188893, 462149501233, 32608007988, 0, 0, 0] := by
  rw [show D2M8K2.u3109 = KTree.node D2M8K2.t3114 (nat_lit 7485845) (nat_lit 2190013337) (nat_lit 0) D2M8K2.t3115 from rfl, totK_node, tot3114, tot3115]
  decide +kernel

theorem arows3111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3111 = true := by
  rw [show D2M8K2.u3111 = KTree.node D2M8K2.t3116 (nat_lit 7487416) (nat_lit 3190507564) (nat_lit 0) D2M8K2.t3117 from rfl, allE_node, rows3116, irow3111, rows3117]
  all_goals rfl

theorem atot3111 : totK PD2M8K2 D2M8K2.u3111 = [0, 170439871730, 733084491707, 697398129771, 123003637273, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3111 = KTree.node D2M8K2.t3116 (nat_lit 7487416) (nat_lit 3190507564) (nat_lit 0) D2M8K2.t3117 from rfl, totK_node, tot3116, tot3117]
  decide +kernel

theorem arows3112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3112 = true := by
  rw [show D2M8K2.u3112 = KTree.node D2M8K2.t3118 (nat_lit 7496474) (nat_lit 4058634970) (nat_lit 0) D2M8K2.t3119 from rfl, allE_node, rows3118, irow3112, rows3119]
  all_goals rfl

theorem atot3112 : totK PD2M8K2 D2M8K2.u3112 = [0, 336950640142, 907762616442, 502378890115, 40004164644, 0, 0, 0] := by
  rw [show D2M8K2.u3112 = KTree.node D2M8K2.t3118 (nat_lit 7496474) (nat_lit 4058634970) (nat_lit 0) D2M8K2.t3119 from rfl, totK_node, tot3118, tot3119]
  decide +kernel

theorem arows3116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3116 = true := by
  rw [show D2M8K2.u3116 = KTree.node D2M8K2.t3120 (nat_lit 7499722) (nat_lit 2744318008) (nat_lit 0) D2M8K2.t3121 from rfl, allE_node, rows3120, irow3116, rows3121]
  all_goals rfl

theorem atot3116 : totK PD2M8K2 D2M8K2.u3116 = [0, 361085753457, 935486546772, 450428624296, 23722331541, 0, 0, 0] := by
  rw [show D2M8K2.u3116 = KTree.node D2M8K2.t3120 (nat_lit 7499722) (nat_lit 2744318008) (nat_lit 0) D2M8K2.t3121 from rfl, totK_node, tot3120, tot3121]
  decide +kernel

theorem arows3117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3117 = true := by
  rw [show D2M8K2.u3117 = KTree.node D2M8K2.t3122 (nat_lit 7503093) (nat_lit 1638620727) (nat_lit 0) D2M8K2.t3123 from rfl, allE_node, rows3122, irow3117, rows3123]
  all_goals rfl

theorem atot3117 : totK PD2M8K2 D2M8K2.u3117 = [0, 346915678690, 942628563628, 469622953417, 24683687388, 0, 0, 0] := by
  rw [show D2M8K2.u3117 = KTree.node D2M8K2.t3122 (nat_lit 7503093) (nat_lit 1638620727) (nat_lit 0) D2M8K2.t3123 from rfl, totK_node, tot3122, tot3123]
  decide +kernel

theorem arows3119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3119 = true := by
  rw [show D2M8K2.u3119 = KTree.node D2M8K2.t3124 (nat_lit 7510205) (nat_lit 2300159181) (nat_lit 0) D2M8K2.t3125 from rfl, allE_node, rows3124, irow3119, rows3125]
  all_goals rfl

theorem atot3119 : totK PD2M8K2 D2M8K2.u3119 = [179528440046, 637302925646, 736303582937, 271214481738, 17433533548, 0, 0, 0] := by
  rw [show D2M8K2.u3119 = KTree.node D2M8K2.t3124 (nat_lit 7510205) (nat_lit 2300159181) (nat_lit 0) D2M8K2.t3125 from rfl, totK_node, tot3124, tot3125]
  decide +kernel

theorem arows3120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3120 = true := by
  rw [show D2M8K2.u3120 = KTree.node D2M8K2.t3126 (nat_lit 7511358) (nat_lit 3895643063) (nat_lit 0) D2M8K2.t3127 from rfl, allE_node, rows3126, irow3120, rows3127]
  all_goals rfl

theorem atot3120 : totK PD2M8K2 D2M8K2.u3120 = [265578002599, 779438868206, 599888768363, 179294101409, 17186218589, 0, 0, 0] := by
  rw [show D2M8K2.u3120 = KTree.node D2M8K2.t3126 (nat_lit 7511358) (nat_lit 3895643063) (nat_lit 0) D2M8K2.t3127 from rfl, totK_node, tot3126, tot3127]
  decide +kernel

theorem arows3123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3123 = true := by
  rw [show D2M8K2.u3123 = KTree.node D2M8K2.t3128 (nat_lit 7512812) (nat_lit 3786797412) (nat_lit 0) D2M8K2.t3129 from rfl, allE_node, rows3128, irow3123, rows3129]
  all_goals rfl

theorem atot3123 : totK PD2M8K2 D2M8K2.u3123 = [64441704225, 441475766117, 900440543914, 400921907517, 20423179516, 0, 0, 0] := by
  rw [show D2M8K2.u3123 = KTree.node D2M8K2.t3128 (nat_lit 7512812) (nat_lit 3786797412) (nat_lit 0) D2M8K2.t3129 from rfl, totK_node, tot3128, tot3129]
  decide +kernel

theorem arows3124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3124 = true := by
  rw [show D2M8K2.u3124 = KTree.node D2M8K2.t3130 (nat_lit 7514566) (nat_lit 3104929542) (nat_lit 0) D2M8K2.t3131 from rfl, allE_node, rows3130, irow3124, rows3131]
  all_goals rfl

theorem atot3124 : totK PD2M8K2 D2M8K2.u3124 = [282475659463, 881421542234, 618285920695, 66413345836, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3124 = KTree.node D2M8K2.t3130 (nat_lit 7514566) (nat_lit 3104929542) (nat_lit 0) D2M8K2.t3131 from rfl, totK_node, tot3130, tot3131]
  decide +kernel

theorem arows3126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3126 = true := by
  rw [show D2M8K2.u3126 = KTree.node D2M8K2.t3132 (nat_lit 7516551) (nat_lit 3461015343) (nat_lit 0) D2M8K2.t3133 from rfl, allE_node, rows3132, irow3126, rows3133]
  all_goals rfl

theorem atot3126 : totK PD2M8K2 D2M8K2.u3126 = [161066439721, 651349872364, 767435031202, 223197238357, 11643020496, 0, 0, 0] := by
  rw [show D2M8K2.u3126 = KTree.node D2M8K2.t3132 (nat_lit 7516551) (nat_lit 3461015343) (nat_lit 0) D2M8K2.t3133 from rfl, totK_node, tot3132, tot3133]
  decide +kernel

theorem arows3127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3127 = true := by
  rw [show D2M8K2.u3127 = KTree.node D2M8K2.t3134 (nat_lit 7518195) (nat_lit 2986295984) (nat_lit 0) D2M8K2.t3135 from rfl, allE_node, rows3134, irow3127, rows3135]
  all_goals rfl

theorem atot3127 : totK PD2M8K2 D2M8K2.u3127 = [265819678958, 809146603039, 630502639141, 100959724140, 1197396724, 0, 0, 0] := by
  rw [show D2M8K2.u3127 = KTree.node D2M8K2.t3134 (nat_lit 7518195) (nat_lit 2986295984) (nat_lit 0) D2M8K2.t3135 from rfl, totK_node, tot3134, tot3135]
  decide +kernel

theorem arows3133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3133 = true := by
  rw [show D2M8K2.u3133 = KTree.node D2M8K2.t3136 (nat_lit 7519872) (nat_lit 2308031685) (nat_lit 0) D2M8K2.t3137 from rfl, allE_node, rows3136, irow3133, rows3137]
  all_goals rfl

theorem atot3133 : totK PD2M8K2 D2M8K2.u3133 = [154825709772, 632677103788, 764026347718, 229371281581, 12040273252, 0, 0, 0] := by
  rw [show D2M8K2.u3133 = KTree.node D2M8K2.t3136 (nat_lit 7519872) (nat_lit 2308031685) (nat_lit 0) D2M8K2.t3137 from rfl, totK_node, tot3136, tot3137]
  decide +kernel

theorem arows3134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3134 = true := by
  rw [show D2M8K2.u3134 = KTree.node D2M8K2.t3138 (nat_lit 7521275) (nat_lit 2075977946) (nat_lit 0) D2M8K2.t3139 from rfl, allE_node, rows3138, irow3134, rows3139]
  all_goals rfl

theorem atot3134 : totK PD2M8K2 D2M8K2.u3134 = [257043485040, 807880915994, 628078144298, 94546420787, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u3134 = KTree.node D2M8K2.t3138 (nat_lit 7521275) (nat_lit 2075977946) (nat_lit 0) D2M8K2.t3139 from rfl, totK_node, tot3138, tot3139]
  decide +kernel

theorem arows3136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3136 = true := by
  rw [show D2M8K2.u3136 = KTree.node D2M8K2.t3140 (nat_lit 7523241) (nat_lit 1920798711) (nat_lit 0) D2M8K2.t3141 from rfl, allE_node, rows3140, irow3136, rows3141]
  all_goals rfl

theorem atot3136 : totK PD2M8K2 D2M8K2.u3136 = [157245094994, 708756299696, 803412309377, 164708728892, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u3136 = KTree.node D2M8K2.t3140 (nat_lit 7523241) (nat_lit 1920798711) (nat_lit 0) D2M8K2.t3141 from rfl, totK_node, tot3140, tot3141]
  decide +kernel

theorem arows3137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3137 = true := by
  rw [show D2M8K2.u3137 = KTree.node D2M8K2.t3142 (nat_lit 7524844) (nat_lit 3181832901) (nat_lit 0) D2M8K2.t3143 from rfl, allE_node, rows3142, irow3137, rows3143]
  all_goals rfl

theorem atot3137 : totK PD2M8K2 D2M8K2.u3137 = [260280242241, 804047817113, 643713838664, 107770548345, 1267860612, 0, 0, 0] := by
  rw [show D2M8K2.u3137 = KTree.node D2M8K2.t3142 (nat_lit 7524844) (nat_lit 3181832901) (nat_lit 0) D2M8K2.t3143 from rfl, totK_node, tot3142, tot3143]
  decide +kernel

theorem arows3140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3140 = true := by
  rw [show D2M8K2.u3140 = KTree.node D2M8K2.t3144 (nat_lit 7526570) (nat_lit 3721593376) (nat_lit 0) D2M8K2.t3145 from rfl, allE_node, rows3144, irow3140, rows3145]
  all_goals rfl

theorem atot3140 : totK PD2M8K2 D2M8K2.u3140 = [0, 405604063483, 943198421619, 428146881632, 35662288602, 0, 0, 0] := by
  rw [show D2M8K2.u3140 = KTree.node D2M8K2.t3144 (nat_lit 7526570) (nat_lit 3721593376) (nat_lit 0) D2M8K2.t3145 from rfl, totK_node, tot3144, tot3145]
  decide +kernel

theorem arows3141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3141 = true := by
  rw [show D2M8K2.u3141 = KTree.node D2M8K2.t3146 (nat_lit 7531742) (nat_lit 2508595618) (nat_lit 0) D2M8K2.t3147 from rfl, allE_node, rows3146, irow3141, rows3147]
  all_goals rfl

theorem atot3141 : totK PD2M8K2 D2M8K2.u3141 = [0, 349876969871, 932601684186, 521592801120, 32068965003, 0, 0, 0] := by
  rw [show D2M8K2.u3141 = KTree.node D2M8K2.t3146 (nat_lit 7531742) (nat_lit 2508595618) (nat_lit 0) D2M8K2.t3147 from rfl, totK_node, tot3146, tot3147]
  decide +kernel

theorem arows3143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3143 = true := by
  rw [show D2M8K2.u3143 = KTree.node D2M8K2.t3148 (nat_lit 7533222) (nat_lit 3811333147) (nat_lit 0) D2M8K2.t3149 from rfl, allE_node, rows3148, irow3143, rows3149]
  all_goals rfl

theorem atot3143 : totK PD2M8K2 D2M8K2.u3143 = [0, 0, 397261830951, 942134895165, 433826904703, 30397782892, 0, 0] := by
  rw [show D2M8K2.u3143 = KTree.node D2M8K2.t3148 (nat_lit 7533222) (nat_lit 3811333147) (nat_lit 0) D2M8K2.t3149 from rfl, totK_node, tot3148, tot3149]
  decide +kernel

theorem arows3144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3144 = true := by
  rw [show D2M8K2.u3144 = KTree.node D2M8K2.t3150 (nat_lit 7534713) (nat_lit 1851009018) (nat_lit 0) D2M8K2.t3151 from rfl, allE_node, rows3150, irow3144, rows3151]
  all_goals rfl

theorem atot3144 : totK PD2M8K2 D2M8K2.u3144 = [0, 329932086194, 812482560217, 551501678977, 128943302790, 6524090962, 0, 0] := by
  rw [show D2M8K2.u3144 = KTree.node D2M8K2.t3150 (nat_lit 7534713) (nat_lit 1851009018) (nat_lit 0) D2M8K2.t3151 from rfl, totK_node, tot3150, tot3151]
  decide +kernel

theorem arows3148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3148 = true := by
  rw [show D2M8K2.u3148 = KTree.node D2M8K2.t3152 (nat_lit 7536964) (nat_lit 3607137499) (nat_lit 0) D2M8K2.t3153 from rfl, allE_node, rows3152, irow3148, rows3153]
  all_goals rfl

theorem atot3148 : totK PD2M8K2 D2M8K2.u3148 = [0, 93947773758, 633634081711, 864907699810, 205972213270, 5159868635, 0, 0] := by
  rw [show D2M8K2.u3148 = KTree.node D2M8K2.t3152 (nat_lit 7536964) (nat_lit 3607137499) (nat_lit 0) D2M8K2.t3153 from rfl, totK_node, tot3152, tot3153]
  decide +kernel

theorem arows3149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3149 = true := by
  rw [show D2M8K2.u3149 = KTree.node D2M8K2.t3154 (nat_lit 7538664) (nat_lit 3287359609) (nat_lit 0) D2M8K2.t3155 from rfl, allE_node, rows3154, irow3149, rows3155]
  all_goals rfl

theorem atot3149 : totK PD2M8K2 D2M8K2.u3149 = [0, 347194137431, 912219657590, 524995472013, 45875396605, 0, 0, 0] := by
  rw [show D2M8K2.u3149 = KTree.node D2M8K2.t3154 (nat_lit 7538664) (nat_lit 3287359609) (nat_lit 0) D2M8K2.t3155 from rfl, totK_node, tot3154, tot3155]
  decide +kernel

theorem arows3151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3151 = true := by
  rw [show D2M8K2.u3151 = KTree.node D2M8K2.t3156 (nat_lit 7540468) (nat_lit 3559640533) (nat_lit 0) D2M8K2.t3157 from rfl, allE_node, rows3156, irow3151, rows3157]
  all_goals rfl

theorem atot3151 : totK PD2M8K2 D2M8K2.u3151 = [0, 102243800671, 627241151670, 835953349881, 204825935332, 5218872685, 0, 0] := by
  rw [show D2M8K2.u3151 = KTree.node D2M8K2.t3156 (nat_lit 7540468) (nat_lit 3559640533) (nat_lit 0) D2M8K2.t3157 from rfl, totK_node, tot3156, tot3157]
  decide +kernel

theorem arows3152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3152 = true := by
  rw [show D2M8K2.u3152 = KTree.node D2M8K2.t3158 (nat_lit 7541935) (nat_lit 2447609201) (nat_lit 0) D2M8K2.t3159 from rfl, allE_node, rows3158, irow3152, rows3159]
  all_goals rfl

theorem atot3152 : totK PD2M8K2 D2M8K2.u3152 = [0, 308649551758, 894997387251, 555748718381, 46045214282, 0, 0, 0] := by
  rw [show D2M8K2.u3152 = KTree.node D2M8K2.t3158 (nat_lit 7541935) (nat_lit 2447609201) (nat_lit 0) D2M8K2.t3159 from rfl, totK_node, tot3158, tot3159]
  decide +kernel

theorem arows3155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3155 = true := by
  rw [show D2M8K2.u3155 = KTree.node D2M8K2.t3160 (nat_lit 7543970) (nat_lit 4067590321) (nat_lit 0) D2M8K2.t3161 from rfl, allE_node, rows3160, irow3155, rows3161]
  all_goals rfl

theorem atot3155 : totK PD2M8K2 D2M8K2.u3155 = [0, 156769431526, 715721887667, 811572073217, 150219462181, 1415142070, 0, 0] := by
  rw [show D2M8K2.u3155 = KTree.node D2M8K2.t3160 (nat_lit 7543970) (nat_lit 4067590321) (nat_lit 0) D2M8K2.t3161 from rfl, totK_node, tot3160, tot3161]
  decide +kernel

theorem arows3156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3156 = true := by
  rw [show D2M8K2.u3156 = KTree.node D2M8K2.t3162 (nat_lit 7545586) (nat_lit 4121195245) (nat_lit 0) D2M8K2.t3163 from rfl, allE_node, rows3162, irow3156, rows3163]
  all_goals rfl

theorem atot3156 : totK PD2M8K2 D2M8K2.u3156 = [0, 259665683680, 870690444675, 629600230439, 61146160044, 0, 0, 0] := by
  rw [show D2M8K2.u3156 = KTree.node D2M8K2.t3162 (nat_lit 7545586) (nat_lit 4121195245) (nat_lit 0) D2M8K2.t3163 from rfl, totK_node, tot3162, tot3163]
  decide +kernel

theorem arows3158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3158 = true := by
  rw [show D2M8K2.u3158 = KTree.node D2M8K2.t3164 (nat_lit 7547753) (nat_lit 1606595090) (nat_lit 0) D2M8K2.t3165 from rfl, allE_node, rows3164, irow3158, rows3165]
  all_goals rfl

theorem atot3158 : totK PD2M8K2 D2M8K2.u3158 = [157459612076, 362140913955, 374642305233, 607048376533, 243000628091, 9302370699, 0, 0] := by
  rw [show D2M8K2.u3158 = KTree.node D2M8K2.t3164 (nat_lit 7547753) (nat_lit 1606595090) (nat_lit 0) D2M8K2.t3165 from rfl, totK_node, tot3164, tot3165]
  decide +kernel

theorem arows3159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3159 = true := by
  rw [show D2M8K2.u3159 = KTree.node D2M8K2.t3166 (nat_lit 7590859) (nat_lit 1737728758) (nat_lit 0) D2M8K2.t3167 from rfl, allE_node, rows3166, irow3159, rows3167]
  all_goals rfl

theorem atot3159 : totK PD2M8K2 D2M8K2.u3159 = [240105137052, 788245124662, 637018070978, 105855674137, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3159 = KTree.node D2M8K2.t3166 (nat_lit 7590859) (nat_lit 1737728758) (nat_lit 0) D2M8K2.t3167 from rfl, totK_node, tot3166, tot3167]
  decide +kernel

theorem arows3164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3164 = true := by
  rw [show D2M8K2.u3164 = KTree.node D2M8K2.t3168 (nat_lit 7593230) (nat_lit 3885436770) (nat_lit 0) D2M8K2.t3169 from rfl, allE_node, rows3168, irow3164, rows3169]
  all_goals rfl

theorem atot3164 : totK PD2M8K2 D2M8K2.u3164 = [252616569578, 823313671752, 694201349457, 82171745333, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3164 = KTree.node D2M8K2.t3168 (nat_lit 7593230) (nat_lit 3885436770) (nat_lit 0) D2M8K2.t3169 from rfl, totK_node, tot3168, tot3169]
  decide +kernel

theorem arows3165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3165 = true := by
  rw [show D2M8K2.u3165 = KTree.node D2M8K2.t3170 (nat_lit 7594449) (nat_lit 1322804250) (nat_lit 0) D2M8K2.t3171 from rfl, allE_node, rows3170, irow3165, rows3171]
  all_goals rfl

theorem atot3165 : totK PD2M8K2 D2M8K2.u3165 = [174351684497, 694626369369, 707671356658, 229369206075, 21379198785, 0, 0, 0] := by
  rw [show D2M8K2.u3165 = KTree.node D2M8K2.t3170 (nat_lit 7594449) (nat_lit 1322804250) (nat_lit 0) D2M8K2.t3171 from rfl, totK_node, tot3170, tot3171]
  decide +kernel

theorem arows3167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3167 = true := by
  rw [show D2M8K2.u3167 = KTree.node D2M8K2.t3172 (nat_lit 7596001) (nat_lit 1495297859) (nat_lit 0) D2M8K2.t3173 from rfl, allE_node, rows3172, irow3167, rows3173]
  all_goals rfl

theorem atot3167 : totK PD2M8K2 D2M8K2.u3167 = [120687743152, 530788746530, 792880097541, 344202876254, 16157733738, 0, 0, 0] := by
  rw [show D2M8K2.u3167 = KTree.node D2M8K2.t3172 (nat_lit 7596001) (nat_lit 1495297859) (nat_lit 0) D2M8K2.t3173 from rfl, totK_node, tot3172, tot3173]
  decide +kernel

theorem arows3168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3168 = true := by
  rw [show D2M8K2.u3168 = KTree.node D2M8K2.t3174 (nat_lit 7600923) (nat_lit 3748895556) (nat_lit 0) D2M8K2.t3175 from rfl, allE_node, rows3174, irow3168, rows3175]
  all_goals rfl

theorem atot3168 : totK PD2M8K2 D2M8K2.u3168 = [325338371149, 906401219057, 558678211310, 50171928790, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3168 = KTree.node D2M8K2.t3174 (nat_lit 7600923) (nat_lit 3748895556) (nat_lit 0) D2M8K2.t3175 from rfl, totK_node, tot3174, tot3175]
  decide +kernel

theorem arows3171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3171 = true := by
  rw [show D2M8K2.u3171 = KTree.node D2M8K2.t3176 (nat_lit 7602572) (nat_lit 3172335785) (nat_lit 0) D2M8K2.t3177 from rfl, allE_node, rows3176, irow3171, rows3177]
  all_goals rfl

theorem atot3171 : totK PD2M8K2 D2M8K2.u3171 = [69131323710, 504079810831, 903036846510, 301867814669, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u3171 = KTree.node D2M8K2.t3176 (nat_lit 7602572) (nat_lit 3172335785) (nat_lit 0) D2M8K2.t3177 from rfl, totK_node, tot3176, tot3177]
  decide +kernel

theorem arows3172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3172 = true := by
  rw [show D2M8K2.u3172 = KTree.node D2M8K2.t3178 (nat_lit 7603927) (nat_lit 1156402997) (nat_lit 0) D2M8K2.t3179 from rfl, allE_node, rows3178, irow3172, rows3179]
  all_goals rfl

theorem atot3172 : totK PD2M8K2 D2M8K2.u3172 = [346978880099, 911046724767, 500651349572, 41137503729, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3172 = KTree.node D2M8K2.t3178 (nat_lit 7603927) (nat_lit 1156402997) (nat_lit 0) D2M8K2.t3179 from rfl, totK_node, tot3178, tot3179]
  decide +kernel

theorem arows3174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3174 = true := by
  rw [show D2M8K2.u3174 = KTree.node D2M8K2.t3180 (nat_lit 7605797) (nat_lit 1934481791) (nat_lit 0) D2M8K2.t3181 from rfl, allE_node, rows3180, irow3174, rows3181]
  all_goals rfl

theorem atot3174 : totK PD2M8K2 D2M8K2.u3174 = [83233391745, 608698839310, 874130806544, 204022290530, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u3174 = KTree.node D2M8K2.t3180 (nat_lit 7605797) (nat_lit 1934481791) (nat_lit 0) D2M8K2.t3181 from rfl, totK_node, tot3180, tot3181]
  decide +kernel

theorem arows3175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3175 = true := by
  rw [show D2M8K2.u3175 = KTree.node D2M8K2.t3182 (nat_lit 7607435) (nat_lit 2422604085) (nat_lit 0) D2M8K2.t3183 from rfl, allE_node, rows3182, irow3175, rows3183]
  all_goals rfl

theorem atot3175 : totK PD2M8K2 D2M8K2.u3175 = [337658146836, 915567731838, 529583041731, 42431901093, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3175 = KTree.node D2M8K2.t3182 (nat_lit 7607435) (nat_lit 2422604085) (nat_lit 0) D2M8K2.t3183 from rfl, totK_node, tot3182, tot3183]
  decide +kernel

theorem arows3179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3179 = true := by
  rw [show D2M8K2.u3179 = KTree.node D2M8K2.t3184 (nat_lit 7609114) (nat_lit 3709670711) (nat_lit 0) D2M8K2.t3185 from rfl, allE_node, rows3184, irow3179, rows3185]
  all_goals rfl

theorem atot3179 : totK PD2M8K2 D2M8K2.u3179 = [0, 437870209645, 972913512891, 349137414591, 12277443257, 0, 0, 0] := by
  rw [show D2M8K2.u3179 = KTree.node D2M8K2.t3184 (nat_lit 7609114) (nat_lit 3709670711) (nat_lit 0) D2M8K2.t3185 from rfl, totK_node, tot3184, tot3185]
  decide +kernel

theorem arows3180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3180 = true := by
  rw [show D2M8K2.u3180 = KTree.node D2M8K2.t3186 (nat_lit 7611080) (nat_lit 3869296688) (nat_lit 0) D2M8K2.t3187 from rfl, allE_node, rows3186, irow3180, rows3187]
  all_goals rfl

theorem atot3180 : totK PD2M8K2 D2M8K2.u3180 = [0, 395645674791, 932402253394, 403599524049, 24488118033, 0, 0, 0] := by
  rw [show D2M8K2.u3180 = KTree.node D2M8K2.t3186 (nat_lit 7611080) (nat_lit 3869296688) (nat_lit 0) D2M8K2.t3187 from rfl, totK_node, tot3186, tot3187]
  decide +kernel

theorem arows3182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3182 = true := by
  rw [show D2M8K2.u3182 = KTree.node D2M8K2.t3188 (nat_lit 7612828) (nat_lit 1843867016) (nat_lit 0) D2M8K2.t3189 from rfl, allE_node, rows3188, irow3182, rows3189]
  all_goals rfl

theorem atot3182 : totK PD2M8K2 D2M8K2.u3182 = [0, 93173791751, 704688099068, 840145483581, 123327871330, 1239866073, 0, 0] := by
  rw [show D2M8K2.u3182 = KTree.node D2M8K2.t3188 (nat_lit 7612828) (nat_lit 1843867016) (nat_lit 0) D2M8K2.t3189 from rfl, totK_node, tot3188, tot3189]
  decide +kernel

theorem arows3183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3183 = true := by
  rw [show D2M8K2.u3183 = KTree.node D2M8K2.t3190 (nat_lit 7614761) (nat_lit 1784789399) (nat_lit 0) D2M8K2.t3191 from rfl, allE_node, rows3190, irow3183, rows3191]
  all_goals rfl

theorem atot3183 : totK PD2M8K2 D2M8K2.u3183 = [0, 382224741743, 939740532041, 467485227880, 32728110868, 0, 0, 0] := by
  rw [show D2M8K2.u3183 = KTree.node D2M8K2.t3190 (nat_lit 7614761) (nat_lit 1784789399) (nat_lit 0) D2M8K2.t3191 from rfl, totK_node, tot3190, tot3191]
  decide +kernel

theorem arows3186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3186 = true := by
  rw [show D2M8K2.u3186 = KTree.node D2M8K2.t3192 (nat_lit 7621442) (nat_lit 4015663094) (nat_lit 0) D2M8K2.t3193 from rfl, allE_node, rows3192, irow3186, rows3193]
  all_goals rfl

theorem atot3186 : totK PD2M8K2 D2M8K2.u3186 = [0, 378092999592, 947594692011, 466569537276, 32359824416, 0, 0, 0] := by
  rw [show D2M8K2.u3186 = KTree.node D2M8K2.t3192 (nat_lit 7621442) (nat_lit 4015663094) (nat_lit 0) D2M8K2.t3193 from rfl, totK_node, tot3192, tot3193]
  decide +kernel

theorem arows3187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3187 = true := by
  rw [show D2M8K2.u3187 = KTree.node D2M8K2.t3194 (nat_lit 7623103) (nat_lit 2372499785) (nat_lit 0) D2M8K2.t3195 from rfl, allE_node, rows3194, irow3187, rows3195]
  all_goals rfl

theorem atot3187 : totK PD2M8K2 D2M8K2.u3187 = [0, 11795538417, 517632873328, 915432438917, 276430382034, 13105450397, 0, 0] := by
  rw [show D2M8K2.u3187 = KTree.node D2M8K2.t3194 (nat_lit 7623103) (nat_lit 2372499785) (nat_lit 0) D2M8K2.t3195 from rfl, totK_node, tot3194, tot3195]
  decide +kernel

theorem arows3189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3189 = true := by
  rw [show D2M8K2.u3189 = KTree.node D2M8K2.t3196 (nat_lit 7624494) (nat_lit 3764174906) (nat_lit 0) D2M8K2.t3197 from rfl, allE_node, rows3196, irow3189, rows3197]
  all_goals rfl

theorem atot3189 : totK PD2M8K2 D2M8K2.u3189 = [0, 376446820328, 918313963421, 464163463353, 31731663107, 0, 0, 0] := by
  rw [show D2M8K2.u3189 = KTree.node D2M8K2.t3196 (nat_lit 7624494) (nat_lit 3764174906) (nat_lit 0) D2M8K2.t3197 from rfl, totK_node, tot3196, tot3197]
  decide +kernel

theorem arows3190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3190 = true := by
  rw [show D2M8K2.u3190 = KTree.node D2M8K2.t3198 (nat_lit 7626272) (nat_lit 3674885567) (nat_lit 0) D2M8K2.t3199 from rfl, allE_node, rows3198, irow3190, rows3199]
  all_goals rfl

theorem atot3190 : totK PD2M8K2 D2M8K2.u3190 = [0, 101625843941, 649726219227, 791672108826, 159528243019, 4720618446, 0, 0] := by
  rw [show D2M8K2.u3190 = KTree.node D2M8K2.t3198 (nat_lit 7626272) (nat_lit 3674885567) (nat_lit 0) D2M8K2.t3199 from rfl, totK_node, tot3198, tot3199]
  decide +kernel

theorem arows3197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3197 = true := by
  rw [show D2M8K2.u3197 = KTree.node D2M8K2.t3200 (nat_lit 7628117) (nat_lit 1600603935) (nat_lit 0) D2M8K2.t3201 from rfl, allE_node, rows3200, irow3197, rows3201]
  all_goals rfl

theorem atot3197 : totK PD2M8K2 D2M8K2.u3197 = [0, 355377624508, 933800172822, 494279086982, 34349436993, 0, 0, 0] := by
  rw [show D2M8K2.u3197 = KTree.node D2M8K2.t3200 (nat_lit 7628117) (nat_lit 1600603935) (nat_lit 0) D2M8K2.t3201 from rfl, totK_node, tot3200, tot3201]
  decide +kernel

theorem arows3198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3198 = true := by
  rw [show D2M8K2.u3198 = KTree.node D2M8K2.t3202 (nat_lit 7631720) (nat_lit 3595937398) (nat_lit 0) D2M8K2.t3203 from rfl, allE_node, rows3202, irow3198, rows3203]
  all_goals rfl

theorem atot3198 : totK PD2M8K2 D2M8K2.u3198 = [358866886358, 861638177342, 441815588253, 99892533823, 12293754876, 0, 0, 0] := by
  rw [show D2M8K2.u3198 = KTree.node D2M8K2.t3202 (nat_lit 7631720) (nat_lit 3595937398) (nat_lit 0) D2M8K2.t3203 from rfl, totK_node, tot3202, tot3203]
  decide +kernel

theorem arows3200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3200 = true := by
  rw [show D2M8K2.u3200 = KTree.node D2M8K2.t3204 (nat_lit 7633525) (nat_lit 1229449748) (nat_lit 0) D2M8K2.t3205 from rfl, allE_node, rows3204, irow3200, rows3205]
  all_goals rfl

theorem atot3200 : totK PD2M8K2 D2M8K2.u3200 = [111118298925, 672383007227, 856716269727, 157260218204, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3200 = KTree.node D2M8K2.t3204 (nat_lit 7633525) (nat_lit 1229449748) (nat_lit 0) D2M8K2.t3205 from rfl, totK_node, tot3204, tot3205]
  decide +kernel

theorem arows3201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3201 = true := by
  rw [show D2M8K2.u3201 = KTree.node D2M8K2.t3206 (nat_lit 7635428) (nat_lit 3298374917) (nat_lit 0) D2M8K2.t3207 from rfl, allE_node, rows3206, irow3201, rows3207]
  all_goals rfl

theorem atot3201 : totK PD2M8K2 D2M8K2.u3201 = [326739692847, 914705703294, 544176539594, 48941572865, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3201 = KTree.node D2M8K2.t3206 (nat_lit 7635428) (nat_lit 3298374917) (nat_lit 0) D2M8K2.t3207 from rfl, totK_node, tot3206, tot3207]
  decide +kernel

theorem arows3204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3204 = true := by
  rw [show D2M8K2.u3204 = KTree.node D2M8K2.t3208 (nat_lit 7636975) (nat_lit 2447849823) (nat_lit 0) D2M8K2.t3209 from rfl, allE_node, rows3208, irow3204, rows3209]
  all_goals rfl

theorem atot3204 : totK PD2M8K2 D2M8K2.u3204 = [0, 380590115230, 948633745075, 460109624912, 30789563262, 0, 0, 0] := by
  rw [show D2M8K2.u3204 = KTree.node D2M8K2.t3208 (nat_lit 7636975) (nat_lit 2447849823) (nat_lit 0) D2M8K2.t3209 from rfl, totK_node, tot3208, tot3209]
  decide +kernel

theorem arows3205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3205 = true := by
  rw [show D2M8K2.u3205 = KTree.node D2M8K2.t3210 (nat_lit 7638319) (nat_lit 1660363945) (nat_lit 0) D2M8K2.t3211 from rfl, allE_node, rows3210, irow3205, rows3211]
  all_goals rfl

theorem atot3205 : totK PD2M8K2 D2M8K2.u3205 = [327098234359, 854143372819, 511706923422, 114080557667, 6778039233, 0, 0, 0] := by
  rw [show D2M8K2.u3205 = KTree.node D2M8K2.t3210 (nat_lit 7638319) (nat_lit 1660363945) (nat_lit 0) D2M8K2.t3211 from rfl, totK_node, tot3210, tot3211]
  decide +kernel

theorem arows3207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3207 = true := by
  rw [show D2M8K2.u3207 = KTree.node D2M8K2.t3212 (nat_lit 7640324) (nat_lit 3170316863) (nat_lit 0) D2M8K2.t3213 from rfl, allE_node, rows3212, irow3207, rows3213]
  all_goals rfl

theorem atot3207 : totK PD2M8K2 D2M8K2.u3207 = [117107903659, 568860876577, 807962469103, 256547133243, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u3207 = KTree.node D2M8K2.t3212 (nat_lit 7640324) (nat_lit 3170316863) (nat_lit 0) D2M8K2.t3213 from rfl, totK_node, tot3212, tot3213]
  decide +kernel

theorem arows3208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3208 = true := by
  rw [show D2M8K2.u3208 = KTree.node D2M8K2.t3214 (nat_lit 7642397) (nat_lit 2152366375) (nat_lit 0) D2M8K2.t3215 from rfl, allE_node, rows3214, irow3208, rows3215]
  all_goals rfl

theorem atot3208 : totK PD2M8K2 D2M8K2.u3208 = [306717314974, 888940019282, 571687518105, 52681554984, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3208 = KTree.node D2M8K2.t3214 (nat_lit 7642397) (nat_lit 2152366375) (nat_lit 0) D2M8K2.t3215 from rfl, totK_node, tot3214, tot3215]
  decide +kernel

theorem arows3212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3212 = true := by
  rw [show D2M8K2.u3212 = KTree.node D2M8K2.t3216 (nat_lit 7644097) (nat_lit 1544572333) (nat_lit 0) D2M8K2.t3217 from rfl, allE_node, rows3216, irow3212, rows3217]
  all_goals rfl

theorem atot3212 : totK PD2M8K2 D2M8K2.u3212 = [83604988011, 515075895541, 863744829712, 294358401581, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u3212 = KTree.node D2M8K2.t3216 (nat_lit 7644097) (nat_lit 1544572333) (nat_lit 0) D2M8K2.t3217 from rfl, totK_node, tot3216, tot3217]
  decide +kernel

theorem arows3213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3213 = true := by
  rw [show D2M8K2.u3213 = KTree.node D2M8K2.t3218 (nat_lit 7645451) (nat_lit 2209366539) (nat_lit 0) D2M8K2.t3219 from rfl, allE_node, rows3218, irow3213, rows3219]
  all_goals rfl

theorem atot3213 : totK PD2M8K2 D2M8K2.u3213 = [352134766608, 933099602400, 497491340859, 39920132328, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3213 = KTree.node D2M8K2.t3218 (nat_lit 7645451) (nat_lit 2209366539) (nat_lit 0) D2M8K2.t3219 from rfl, totK_node, tot3218, tot3219]
  decide +kernel

theorem arows3215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3215 = true := by
  rw [show D2M8K2.u3215 = KTree.node D2M8K2.t3220 (nat_lit 7647276) (nat_lit 3432462437) (nat_lit 0) D2M8K2.t3221 from rfl, allE_node, rows3220, irow3215, rows3221]
  all_goals rfl

theorem atot3215 : totK PD2M8K2 D2M8K2.u3215 = [0, 536477330309, 1007698960539, 242681148365, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u3215 = KTree.node D2M8K2.t3220 (nat_lit 7647276) (nat_lit 3432462437) (nat_lit 0) D2M8K2.t3221 from rfl, totK_node, tot3220, tot3221]
  decide +kernel

theorem arows3216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3216 = true := by
  rw [show D2M8K2.u3216 = KTree.node D2M8K2.t3222 (nat_lit 7652741) (nat_lit 2302964739) (nat_lit 0) D2M8K2.t3223 from rfl, allE_node, rows3222, irow3216, rows3223]
  all_goals rfl

theorem atot3216 : totK PD2M8K2 D2M8K2.u3216 = [0, 288923826367, 881384939059, 521967569268, 40431632527, 0, 0, 0] := by
  rw [show D2M8K2.u3216 = KTree.node D2M8K2.t3222 (nat_lit 7652741) (nat_lit 2302964739) (nat_lit 0) D2M8K2.t3223 from rfl, totK_node, tot3222, tot3223]
  decide +kernel

theorem arows3219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3219 = true := by
  rw [show D2M8K2.u3219 = KTree.node D2M8K2.t3224 (nat_lit 7655400) (nat_lit 2708596098) (nat_lit 0) D2M8K2.t3225 from rfl, allE_node, rows3224, irow3219, rows3225]
  all_goals rfl

theorem atot3219 : totK PD2M8K2 D2M8K2.u3219 = [0, 221316106115, 784809209869, 685457876730, 96371106598, 1138244013, 0, 0] := by
  rw [show D2M8K2.u3219 = KTree.node D2M8K2.t3224 (nat_lit 7655400) (nat_lit 2708596098) (nat_lit 0) D2M8K2.t3225 from rfl, totK_node, tot3224, tot3225]
  decide +kernel

theorem arows3220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3220 = true := by
  rw [show D2M8K2.u3220 = KTree.node D2M8K2.t3226 (nat_lit 7656623) (nat_lit 2771334004) (nat_lit 0) D2M8K2.t3227 from rfl, allE_node, rows3226, irow3220, rows3227]
  all_goals rfl

theorem atot3220 : totK PD2M8K2 D2M8K2.u3220 = [0, 353080843404, 959510088991, 479647400986, 28192607622, 0, 0, 0] := by
  rw [show D2M8K2.u3220 = KTree.node D2M8K2.t3226 (nat_lit 7656623) (nat_lit 2771334004) (nat_lit 0) D2M8K2.t3227 from rfl, totK_node, tot3226, tot3227]
  decide +kernel

theorem arows3222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3222 = true := by
  rw [show D2M8K2.u3222 = KTree.node D2M8K2.t3228 (nat_lit 7662010) (nat_lit 2082652809) (nat_lit 0) D2M8K2.t3229 from rfl, allE_node, rows3228, irow3222, rows3229]
  all_goals rfl

theorem atot3222 : totK PD2M8K2 D2M8K2.u3222 = [0, 393205654087, 950601507915, 433339542810, 23436716958, 0, 0, 0] := by
  rw [show D2M8K2.u3222 = KTree.node D2M8K2.t3228 (nat_lit 7662010) (nat_lit 2082652809) (nat_lit 0) D2M8K2.t3229 from rfl, totK_node, tot3228, tot3229]
  decide +kernel

theorem arows3223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3223 = true := by
  rw [show D2M8K2.u3223 = KTree.node D2M8K2.t3230 (nat_lit 7663519) (nat_lit 2338675932) (nat_lit 0) D2M8K2.t3231 from rfl, allE_node, rows3230, irow3223, rows3231]
  all_goals rfl

theorem atot3223 : totK PD2M8K2 D2M8K2.u3223 = [0, 367469398159, 952371887314, 441557050621, 25049557118, 0, 0, 0] := by
  rw [show D2M8K2.u3223 = KTree.node D2M8K2.t3230 (nat_lit 7663519) (nat_lit 2338675932) (nat_lit 0) D2M8K2.t3231 from rfl, totK_node, tot3230, tot3231]
  decide +kernel

theorem arows3228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3228 = true := by
  rw [show D2M8K2.u3228 = KTree.node D2M8K2.t3232 (nat_lit 7666507) (nat_lit 2140749232) (nat_lit 0) D2M8K2.t3233 from rfl, allE_node, rows3232, irow3228, rows3233]
  all_goals rfl

theorem atot3228 : totK PD2M8K2 D2M8K2.u3228 = [0, 262306509914, 815095597412, 592853750378, 82146436060, 1095107716, 0, 0] := by
  rw [show D2M8K2.u3228 = KTree.node D2M8K2.t3232 (nat_lit 7666507) (nat_lit 2140749232) (nat_lit 0) D2M8K2.t3233 from rfl, totK_node, tot3232, tot3233]
  decide +kernel

theorem arows3229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3229 = true := by
  rw [show D2M8K2.u3229 = KTree.node D2M8K2.t3234 (nat_lit 7668458) (nat_lit 3935122725) (nat_lit 0) D2M8K2.t3235 from rfl, allE_node, rows3234, irow3229, rows3235]
  all_goals rfl

theorem atot3229 : totK PD2M8K2 D2M8K2.u3229 = [174930887950, 422386189647, 493105677894, 543982609086, 130884614571, 3882006667, 0, 0] := by
  rw [show D2M8K2.u3229 = KTree.node D2M8K2.t3234 (nat_lit 7668458) (nat_lit 3935122725) (nat_lit 0) D2M8K2.t3235 from rfl, totK_node, tot3234, tot3235]
  decide +kernel

theorem arows3231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3231 = true := by
  rw [show D2M8K2.u3231 = KTree.node D2M8K2.t3236 (nat_lit 7673910) (nat_lit 3750743100) (nat_lit 0) D2M8K2.t3237 from rfl, allE_node, rows3236, irow3231, rows3237]
  all_goals rfl

theorem atot3231 : totK PD2M8K2 D2M8K2.u3231 = [200240550622, 751571939316, 715051126137, 121166938777, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3231 = KTree.node D2M8K2.t3236 (nat_lit 7673910) (nat_lit 3750743100) (nat_lit 0) D2M8K2.t3237 from rfl, totK_node, tot3236, tot3237]
  decide +kernel

theorem arows3232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3232 = true := by
  rw [show D2M8K2.u3232 = KTree.node D2M8K2.t3238 (nat_lit 7676307) (nat_lit 3700694319) (nat_lit 0) D2M8K2.t3239 from rfl, allE_node, rows3238, irow3232, rows3239]
  all_goals rfl

theorem atot3232 : totK PD2M8K2 D2M8K2.u3232 = [261592862323, 836047177847, 661499839006, 73160163472, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3232 = KTree.node D2M8K2.t3238 (nat_lit 7676307) (nat_lit 3700694319) (nat_lit 0) D2M8K2.t3239 from rfl, totK_node, tot3238, tot3239]
  decide +kernel

theorem arows3235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3235 = true := by
  rw [show D2M8K2.u3235 = KTree.node D2M8K2.t3240 (nat_lit 7677864) (nat_lit 2713312074) (nat_lit 0) D2M8K2.t3241 from rfl, allE_node, rows3240, irow3235, rows3241]
  all_goals rfl

theorem atot3235 : totK PD2M8K2 D2M8K2.u3235 = [159571904973, 645889946643, 732771980187, 283291173284, 25324944147, 0, 0, 0] := by
  rw [show D2M8K2.u3235 = KTree.node D2M8K2.t3240 (nat_lit 7677864) (nat_lit 2713312074) (nat_lit 0) D2M8K2.t3241 from rfl, totK_node, tot3240, tot3241]
  decide +kernel

theorem arows3236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3236 = true := by
  rw [show D2M8K2.u3236 = KTree.node D2M8K2.t3242 (nat_lit 7679139) (nat_lit 3458832716) (nat_lit 0) D2M8K2.t3243 from rfl, allE_node, rows3242, irow3236, rows3243]
  all_goals rfl

theorem atot3236 : totK PD2M8K2 D2M8K2.u3236 = [153501397625, 590933733772, 781293548026, 295222780528, 12229515597, 0, 0, 0] := by
  rw [show D2M8K2.u3236 = KTree.node D2M8K2.t3242 (nat_lit 7679139) (nat_lit 3458832716) (nat_lit 0) D2M8K2.t3243 from rfl, totK_node, tot3242, tot3243]
  decide +kernel

theorem arows3238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3238 = true := by
  rw [show D2M8K2.u3238 = KTree.node D2M8K2.t3244 (nat_lit 7680960) (nat_lit 3757117624) (nat_lit 0) D2M8K2.t3245 from rfl, allE_node, rows3244, irow3238, rows3245]
  all_goals rfl

theorem atot3238 : totK PD2M8K2 D2M8K2.u3238 = [176668855814, 693584643593, 760269417518, 179981601858, 7158193557, 0, 0, 0] := by
  rw [show D2M8K2.u3238 = KTree.node D2M8K2.t3244 (nat_lit 7680960) (nat_lit 3757117624) (nat_lit 0) D2M8K2.t3245 from rfl, totK_node, tot3244, tot3245]
  decide +kernel

theorem arows3239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3239 = true := by
  rw [show D2M8K2.u3239 = KTree.node D2M8K2.t3246 (nat_lit 7683107) (nat_lit 2953463228) (nat_lit 0) D2M8K2.t3247 from rfl, allE_node, rows3246, irow3239, rows3247]
  all_goals rfl

theorem atot3239 : totK PD2M8K2 D2M8K2.u3239 = [334933000222, 862988113720, 544924793208, 76875405204, 2316356541, 0, 0, 0] := by
  rw [show D2M8K2.u3239 = KTree.node D2M8K2.t3246 (nat_lit 7683107) (nat_lit 2953463228) (nat_lit 0) D2M8K2.t3247 from rfl, totK_node, tot3246, tot3247]
  decide +kernel

theorem arows3243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3243 = true := by
  rw [show D2M8K2.u3243 = KTree.node D2M8K2.t3248 (nat_lit 7684612) (nat_lit 2849788564) (nat_lit 0) D2M8K2.t3249 from rfl, allE_node, rows3248, irow3243, rows3249]
  all_goals rfl

theorem atot3243 : totK PD2M8K2 D2M8K2.u3243 = [89753051296, 626120217011, 843091346588, 223991504187, 9664716404, 0, 0, 0] := by
  rw [show D2M8K2.u3243 = KTree.node D2M8K2.t3248 (nat_lit 7684612) (nat_lit 2849788564) (nat_lit 0) D2M8K2.t3249 from rfl, totK_node, tot3248, tot3249]
  decide +kernel

theorem arows3244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3244 = true := by
  rw [show D2M8K2.u3244 = KTree.node D2M8K2.t3250 (nat_lit 7689933) (nat_lit 1422869584) (nat_lit 0) D2M8K2.t3251 from rfl, allE_node, rows3250, irow3244, rows3251]
  all_goals rfl

theorem atot3244 : totK PD2M8K2 D2M8K2.u3244 = [279514168584, 799074995318, 609321423974, 118513928905, 3579068459, 0, 0, 0] := by
  rw [show D2M8K2.u3244 = KTree.node D2M8K2.t3250 (nat_lit 7689933) (nat_lit 1422869584) (nat_lit 0) D2M8K2.t3251 from rfl, totK_node, tot3250, tot3251]
  decide +kernel

theorem arows3246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3246 = true := by
  rw [show D2M8K2.u3246 = KTree.node D2M8K2.t3252 (nat_lit 7691350) (nat_lit 3542039026) (nat_lit 0) D2M8K2.t3253 from rfl, allE_node, rows3252, irow3246, rows3253]
  all_goals rfl

theorem atot3246 : totK PD2M8K2 D2M8K2.u3246 = [157524901095, 694432145958, 788917219299, 169740357814, 2304167554, 0, 0, 0] := by
  rw [show D2M8K2.u3246 = KTree.node D2M8K2.t3252 (nat_lit 7691350) (nat_lit 3542039026) (nat_lit 0) D2M8K2.t3253 from rfl, totK_node, tot3252, tot3253]
  decide +kernel

theorem arows3247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3247 = true := by
  rw [show D2M8K2.u3247 = KTree.node D2M8K2.t3254 (nat_lit 7693032) (nat_lit 3417226095) (nat_lit 0) D2M8K2.t3255 from rfl, allE_node, rows3254, irow3247, rows3255]
  all_goals rfl

theorem atot3247 : totK PD2M8K2 D2M8K2.u3247 = [0, 385614345759, 943797350769, 430765751061, 25080681604, 0, 0, 0] := by
  rw [show D2M8K2.u3247 = KTree.node D2M8K2.t3254 (nat_lit 7693032) (nat_lit 3417226095) (nat_lit 0) D2M8K2.t3255 from rfl, totK_node, tot3254, tot3255]
  decide +kernel

theorem arows3250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3250 = true := by
  rw [show D2M8K2.u3250 = KTree.node D2M8K2.t3256 (nat_lit 7694718) (nat_lit 3995587691) (nat_lit 0) D2M8K2.t3257 from rfl, allE_node, rows3256, irow3250, rows3257]
  all_goals rfl

theorem atot3250 : totK PD2M8K2 D2M8K2.u3250 = [0, 173321245871, 754510073984, 722864401491, 102879224192, 1310285577, 0, 0] := by
  rw [show D2M8K2.u3250 = KTree.node D2M8K2.t3256 (nat_lit 7694718) (nat_lit 3995587691) (nat_lit 0) D2M8K2.t3257 from rfl, totK_node, tot3256, tot3257]
  decide +kernel

theorem arows3251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3251 = true := by
  rw [show D2M8K2.u3251 = KTree.node D2M8K2.t3258 (nat_lit 7697126) (nat_lit 4150634215) (nat_lit 0) D2M8K2.t3259 from rfl, allE_node, rows3258, irow3251, rows3259]
  all_goals rfl

theorem atot3251 : totK PD2M8K2 D2M8K2.u3251 = [0, 312351914018, 868469310517, 600489327479, 55758888283, 0, 0, 0] := by
  rw [show D2M8K2.u3251 = KTree.node D2M8K2.t3258 (nat_lit 7697126) (nat_lit 4150634215) (nat_lit 0) D2M8K2.t3259 from rfl, totK_node, tot3258, tot3259]
  decide +kernel

theorem arows3253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3253 = true := by
  rw [show D2M8K2.u3253 = KTree.node D2M8K2.t3260 (nat_lit 7700184) (nat_lit 3555296004) (nat_lit 0) D2M8K2.t3261 from rfl, allE_node, rows3260, irow3253, rows3261]
  all_goals rfl

theorem atot3253 : totK PD2M8K2 D2M8K2.u3253 = [0, 348168266060, 932585468300, 512916472713, 41699183030, 0, 0, 0] := by
  rw [show D2M8K2.u3253 = KTree.node D2M8K2.t3260 (nat_lit 7700184) (nat_lit 3555296004) (nat_lit 0) D2M8K2.t3261 from rfl, totK_node, tot3260, tot3261]
  decide +kernel

theorem arows3254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3254 = true := by
  rw [show D2M8K2.u3254 = KTree.node D2M8K2.t3262 (nat_lit 7702064) (nat_lit 2362125830) (nat_lit 0) D2M8K2.t3263 from rfl, allE_node, rows3262, irow3254, rows3263]
  all_goals rfl

theorem atot3254 : totK PD2M8K2 D2M8K2.u3254 = [0, 159881501421, 670162006643, 777153760454, 170229015191, 4879840392, 0, 0] := by
  rw [show D2M8K2.u3254 = KTree.node D2M8K2.t3262 (nat_lit 7702064) (nat_lit 2362125830) (nat_lit 0) D2M8K2.t3263 from rfl, totK_node, tot3262, tot3263]
  decide +kernel

theorem arows3260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3260 = true := by
  rw [show D2M8K2.u3260 = KTree.node D2M8K2.t3264 (nat_lit 7704421) (nat_lit 1347894443) (nat_lit 0) D2M8K2.t3265 from rfl, allE_node, rows3264, irow3260, rows3265]
  all_goals rfl

theorem atot3260 : totK PD2M8K2 D2M8K2.u3260 = [0, 348085576271, 941041292818, 494322994857, 34351569489, 0, 0, 0] := by
  rw [show D2M8K2.u3260 = KTree.node D2M8K2.t3264 (nat_lit 7704421) (nat_lit 1347894443) (nat_lit 0) D2M8K2.t3265 from rfl, totK_node, tot3264, tot3265]
  decide +kernel

theorem arows3261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3261 = true := by
  rw [show D2M8K2.u3261 = KTree.node D2M8K2.t3266 (nat_lit 7706155) (nat_lit 1620404758) (nat_lit 0) D2M8K2.t3267 from rfl, allE_node, rows3266, irow3261, rows3267]
  all_goals rfl

theorem atot3261 : totK PD2M8K2 D2M8K2.u3261 = [0, 84478000207, 632108098462, 834522364426, 181791453274, 4931404646, 0, 0] := by
  rw [show D2M8K2.u3261 = KTree.node D2M8K2.t3266 (nat_lit 7706155) (nat_lit 1620404758) (nat_lit 0) D2M8K2.t3267 from rfl, totK_node, tot3266, tot3267]
  decide +kernel

theorem arows3263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3263 = true := by
  rw [show D2M8K2.u3263 = KTree.node D2M8K2.t3268 (nat_lit 7711168) (nat_lit 3091549709) (nat_lit 0) D2M8K2.t3269 from rfl, allE_node, rows3268, irow3263, rows3269]
  all_goals rfl

theorem atot3263 : totK PD2M8K2 D2M8K2.u3263 = [0, 354241483738, 923084613313, 518865169412, 37703780097, 0, 0, 0] := by
  rw [show D2M8K2.u3263 = KTree.node D2M8K2.t3268 (nat_lit 7711168) (nat_lit 3091549709) (nat_lit 0) D2M8K2.t3269 from rfl, totK_node, tot3268, tot3269]
  decide +kernel

theorem arows3264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3264 = true := by
  rw [show D2M8K2.u3264 = KTree.node D2M8K2.t3270 (nat_lit 7712810) (nat_lit 3828568504) (nat_lit 0) D2M8K2.t3271 from rfl, allE_node, rows3270, irow3264, rows3271]
  all_goals rfl

theorem atot3264 : totK PD2M8K2 D2M8K2.u3264 = [0, 0, 433764312169, 955217537116, 333465890777, 12146940058, 0, 0] := by
  rw [show D2M8K2.u3264 = KTree.node D2M8K2.t3270 (nat_lit 7712810) (nat_lit 3828568504) (nat_lit 0) D2M8K2.t3271 from rfl, totK_node, tot3270, tot3271]
  decide +kernel

theorem arows3267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3267 = true := by
  rw [show D2M8K2.u3267 = KTree.node D2M8K2.t3272 (nat_lit 7714689) (nat_lit 1761246619) (nat_lit 0) D2M8K2.t3273 from rfl, allE_node, rows3272, irow3267, rows3273]
  all_goals rfl

theorem atot3267 : totK PD2M8K2 D2M8K2.u3267 = [0, 384011510599, 909425115807, 422628619325, 60898593958, 9604228008, 0, 0] := by
  rw [show D2M8K2.u3267 = KTree.node D2M8K2.t3272 (nat_lit 7714689) (nat_lit 1761246619) (nat_lit 0) D2M8K2.t3273 from rfl, totK_node, tot3272, tot3273]
  decide +kernel

theorem arows3268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3268 = true := by
  rw [show D2M8K2.u3268 = KTree.node D2M8K2.t3274 (nat_lit 7716223) (nat_lit 1663337437) (nat_lit 0) D2M8K2.t3275 from rfl, allE_node, rows3274, irow3268, rows3275]
  all_goals rfl

theorem atot3268 : totK PD2M8K2 D2M8K2.u3268 = [0, 106248080451, 672849136817, 863317191529, 151617866219, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3268 = KTree.node D2M8K2.t3274 (nat_lit 7716223) (nat_lit 1663337437) (nat_lit 0) D2M8K2.t3275 from rfl, totK_node, tot3274, tot3275]
  decide +kernel

theorem arows3270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3270 = true := by
  rw [show D2M8K2.u3270 = KTree.node D2M8K2.t3276 (nat_lit 7725180) (nat_lit 3174028253) (nat_lit 0) D2M8K2.t3277 from rfl, allE_node, rows3276, irow3270, rows3277]
  all_goals rfl

theorem atot3270 : totK PD2M8K2 D2M8K2.u3270 = [0, 355086897741, 935031498369, 486168462100, 33115975954, 0, 0, 0] := by
  rw [show D2M8K2.u3270 = KTree.node D2M8K2.t3276 (nat_lit 7725180) (nat_lit 3174028253) (nat_lit 0) D2M8K2.t3277 from rfl, totK_node, tot3276, tot3277]
  decide +kernel

theorem arows3271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3271 = true := by
  rw [show D2M8K2.u3271 = KTree.node D2M8K2.t3278 (nat_lit 7726862) (nat_lit 3603420398) (nat_lit 0) D2M8K2.t3279 from rfl, allE_node, rows3278, irow3271, rows3279]
  all_goals rfl

theorem atot3271 : totK PD2M8K2 D2M8K2.u3271 = [0, 3756869540, 469028030114, 970811483004, 304178088313, 13189998508, 0, 0] := by
  rw [show D2M8K2.u3271 = KTree.node D2M8K2.t3278 (nat_lit 7726862) (nat_lit 3603420398) (nat_lit 0) D2M8K2.t3279 from rfl, totK_node, tot3278, tot3279]
  decide +kernel

theorem arows3275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3275 = true := by
  rw [show D2M8K2.u3275 = KTree.node D2M8K2.t3280 (nat_lit 7728292) (nat_lit 3867998432) (nat_lit 0) D2M8K2.t3281 from rfl, allE_node, rows3280, irow3275, rows3281]
  all_goals rfl

theorem atot3275 : totK PD2M8K2 D2M8K2.u3275 = [0, 389608506584, 930323833437, 439807874596, 29459127622, 0, 0, 0] := by
  rw [show D2M8K2.u3275 = KTree.node D2M8K2.t3280 (nat_lit 7728292) (nat_lit 3867998432) (nat_lit 0) D2M8K2.t3281 from rfl, totK_node, tot3280, tot3281]
  decide +kernel

theorem arows3276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3276 = true := by
  rw [show D2M8K2.u3276 = KTree.node D2M8K2.t3282 (nat_lit 7730216) (nat_lit 3607397541) (nat_lit 0) D2M8K2.t3283 from rfl, allE_node, rows3282, irow3276, rows3283]
  all_goals rfl

theorem atot3276 : totK PD2M8K2 D2M8K2.u3276 = [0, 85921845309, 621071908172, 870481211034, 182827230707, 4917684815, 0, 0] := by
  rw [show D2M8K2.u3276 = KTree.node D2M8K2.t3282 (nat_lit 7730216) (nat_lit 3607397541) (nat_lit 0) D2M8K2.t3283 from rfl, totK_node, tot3282, tot3283]
  decide +kernel

theorem arows3278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3278 = true := by
  rw [show D2M8K2.u3278 = KTree.node D2M8K2.t3284 (nat_lit 7731969) (nat_lit 1486108042) (nat_lit 0) D2M8K2.t3285 from rfl, allE_node, rows3284, irow3278, rows3285]
  all_goals rfl

theorem atot3278 : totK PD2M8K2 D2M8K2.u3278 = [0, 317439273682, 909349279922, 548495061629, 46007599558, 0, 0, 0] := by
  rw [show D2M8K2.u3278 = KTree.node D2M8K2.t3284 (nat_lit 7731969) (nat_lit 1486108042) (nat_lit 0) D2M8K2.t3285 from rfl, totK_node, tot3284, tot3285]
  decide +kernel

theorem arows3279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3279 = true := by
  rw [show D2M8K2.u3279 = KTree.node D2M8K2.t3286 (nat_lit 7733784) (nat_lit 3507304777) (nat_lit 0) D2M8K2.t3287 from rfl, allE_node, rows3286, irow3279, rows3287]
  all_goals rfl

theorem atot3279 : totK PD2M8K2 D2M8K2.u3279 = [0, 0, 466914143127, 982612847988, 317960239776, 13750795750, 0, 0] := by
  rw [show D2M8K2.u3279 = KTree.node D2M8K2.t3286 (nat_lit 7733784) (nat_lit 3507304777) (nat_lit 0) D2M8K2.t3287 from rfl, totK_node, tot3286, tot3287]
  decide +kernel

theorem arows3282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3282 = true := by
  rw [show D2M8K2.u3282 = KTree.node D2M8K2.t3288 (nat_lit 7735662) (nat_lit 3903036288) (nat_lit 0) D2M8K2.t3289 from rfl, allE_node, rows3288, irow3282, rows3289]
  all_goals rfl

theorem atot3282 : totK PD2M8K2 D2M8K2.u3282 = [0, 0, 326749502356, 934014483068, 449485475773, 24762653777, 0, 0] := by
  rw [show D2M8K2.u3282 = KTree.node D2M8K2.t3288 (nat_lit 7735662) (nat_lit 3903036288) (nat_lit 0) D2M8K2.t3289 from rfl, totK_node, tot3288, tot3289]
  decide +kernel

theorem arows3283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3283 = true := by
  rw [show D2M8K2.u3283 = KTree.node D2M8K2.t3290 (nat_lit 7737525) (nat_lit 1597360041) (nat_lit 0) D2M8K2.t3291 from rfl, allE_node, rows3290, irow3283, rows3291]
  all_goals rfl

theorem atot3283 : totK PD2M8K2 D2M8K2.u3283 = [0, 0, 158343603214, 755268492210, 696233931143, 98854127129, 1310517177, 0] := by
  rw [show D2M8K2.u3283 = KTree.node D2M8K2.t3290 (nat_lit 7737525) (nat_lit 1597360041) (nat_lit 0) D2M8K2.t3291 from rfl, totK_node, tot3290, tot3291]
  decide +kernel

theorem arows3285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3285 = true := by
  rw [show D2M8K2.u3285 = KTree.node D2M8K2.t3292 (nat_lit 7746342) (nat_lit 3802709462) (nat_lit 0) D2M8K2.t3293 from rfl, allE_node, rows3292, irow3285, rows3293]
  all_goals rfl

theorem atot3285 : totK PD2M8K2 D2M8K2.u3285 = [0, 0, 386345212827, 945631378169, 406780055877, 22342706985, 0, 0] := by
  rw [show D2M8K2.u3285 = KTree.node D2M8K2.t3292 (nat_lit 7746342) (nat_lit 3802709462) (nat_lit 0) D2M8K2.t3293 from rfl, totK_node, tot3292, tot3293]
  decide +kernel

theorem arows3286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3286 = true := by
  rw [show D2M8K2.u3286 = KTree.node D2M8K2.t3294 (nat_lit 7749468) (nat_lit 2805128797) (nat_lit 0) D2M8K2.t3295 from rfl, allE_node, rows3294, irow3286, rows3295]
  all_goals rfl

theorem atot3286 : totK PD2M8K2 D2M8K2.u3286 = [0, 0, 372557331229, 968567549416, 388452858206, 16065517891, 0, 0] := by
  rw [show D2M8K2.u3286 = KTree.node D2M8K2.t3294 (nat_lit 7749468) (nat_lit 2805128797) (nat_lit 0) D2M8K2.t3295 from rfl, totK_node, tot3294, tot3295]
  decide +kernel

theorem arows3291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3291 = true := by
  rw [show D2M8K2.u3291 = KTree.node D2M8K2.t3296 (nat_lit 7753316) (nat_lit 1935960728) (nat_lit 0) D2M8K2.t3297 from rfl, allE_node, rows3296, irow3291, rows3297]
  all_goals rfl

theorem atot3291 : totK PD2M8K2 D2M8K2.u3291 = [0, 135735544409, 594318091165, 828752041570, 270516943283, 12810146349, 0, 0] := by
  rw [show D2M8K2.u3291 = KTree.node D2M8K2.t3296 (nat_lit 7753316) (nat_lit 1935960728) (nat_lit 0) D2M8K2.t3297 from rfl, totK_node, tot3296, tot3297]
  decide +kernel

theorem arows3292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3292 = true := by
  rw [show D2M8K2.u3292 = KTree.node D2M8K2.t3298 (nat_lit 7759946) (nat_lit 4048780173) (nat_lit 0) D2M8K2.t3299 from rfl, allE_node, rows3298, irow3292, rows3299]
  all_goals rfl

theorem atot3292 : totK PD2M8K2 D2M8K2.u3292 = [0, 309120940335, 918953283710, 555644652683, 50114532120, 0, 0, 0] := by
  rw [show D2M8K2.u3292 = KTree.node D2M8K2.t3298 (nat_lit 7759946) (nat_lit 4048780173) (nat_lit 0) D2M8K2.t3299 from rfl, totK_node, tot3298, tot3299]
  decide +kernel

theorem arows3294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3294 = true := by
  rw [show D2M8K2.u3294 = KTree.node D2M8K2.t3300 (nat_lit 7761428) (nat_lit 3645792171) (nat_lit 0) D2M8K2.t3301 from rfl, allE_node, rows3300, irow3294, rows3301]
  all_goals rfl

theorem atot3294 : totK PD2M8K2 D2M8K2.u3294 = [0, 0, 367878538678, 962622529505, 456394053485, 30738595721, 0, 0] := by
  rw [show D2M8K2.u3294 = KTree.node D2M8K2.t3300 (nat_lit 7761428) (nat_lit 3645792171) (nat_lit 0) D2M8K2.t3301 from rfl, totK_node, tot3300, tot3301]
  decide +kernel

theorem arows3295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3295 = true := by
  rw [show D2M8K2.u3295 = KTree.node D2M8K2.t3302 (nat_lit 7762924) (nat_lit 3939139242) (nat_lit 0) D2M8K2.t3303 from rfl, allE_node, rows3302, irow3295, rows3303]
  all_goals rfl

theorem atot3295 : totK PD2M8K2 D2M8K2.u3295 = [0, 346386984557, 870529455513, 502212828304, 108686434311, 6761411919, 0, 0] := by
  rw [show D2M8K2.u3295 = KTree.node D2M8K2.t3302 (nat_lit 7762924) (nat_lit 3939139242) (nat_lit 0) D2M8K2.t3303 from rfl, totK_node, tot3302, tot3303]
  decide +kernel

theorem arows3298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3298 = true := by
  rw [show D2M8K2.u3298 = KTree.node D2M8K2.t3304 (nat_lit 7765160) (nat_lit 3943017048) (nat_lit 0) D2M8K2.t3305 from rfl, allE_node, rows3304, irow3298, rows3305]
  all_goals rfl

theorem atot3298 : totK PD2M8K2 D2M8K2.u3298 = [0, 142183269315, 644914715626, 817923702524, 206044666026, 5370412161, 0, 0] := by
  rw [show D2M8K2.u3298 = KTree.node D2M8K2.t3304 (nat_lit 7765160) (nat_lit 3943017048) (nat_lit 0) D2M8K2.t3305 from rfl, totK_node, tot3304, tot3305]
  decide +kernel

theorem arows3299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3299 = true := by
  rw [show D2M8K2.u3299 = KTree.node D2M8K2.t3306 (nat_lit 7766857) (nat_lit 1449430356) (nat_lit 0) D2M8K2.t3307 from rfl, allE_node, rows3306, irow3299, rows3307]
  all_goals rfl

theorem atot3299 : totK PD2M8K2 D2M8K2.u3299 = [0, 284160187792, 877312723646, 597877187565, 57820751700, 0, 0, 0] := by
  rw [show D2M8K2.u3299 = KTree.node D2M8K2.t3306 (nat_lit 7766857) (nat_lit 1449430356) (nat_lit 0) D2M8K2.t3307 from rfl, totK_node, tot3306, tot3307]
  decide +kernel

theorem arows3301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3301 = true := by
  rw [show D2M8K2.u3301 = KTree.node D2M8K2.t3308 (nat_lit 7768550) (nat_lit 4113698729) (nat_lit 0) D2M8K2.t3309 from rfl, allE_node, rows3308, irow3301, rows3309]
  all_goals rfl

theorem atot3301 : totK PD2M8K2 D2M8K2.u3301 = [0, 84648349195, 534436512603, 855812823465, 286345996506, 13183084702, 0, 0] := by
  rw [show D2M8K2.u3301 = KTree.node D2M8K2.t3308 (nat_lit 7768550) (nat_lit 4113698729) (nat_lit 0) D2M8K2.t3309 from rfl, totK_node, tot3308, tot3309]
  decide +kernel

theorem arows3302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3302 = true := by
  rw [show D2M8K2.u3302 = KTree.node D2M8K2.t3310 (nat_lit 7769983) (nat_lit 2366502261) (nat_lit 0) D2M8K2.t3311 from rfl, allE_node, rows3310, irow3302, rows3311]
  all_goals rfl

theorem atot3302 : totK PD2M8K2 D2M8K2.u3302 = [0, 326862802260, 913000466388, 529233713214, 45591791065, 0, 0, 0] := by
  rw [show D2M8K2.u3302 = KTree.node D2M8K2.t3310 (nat_lit 7769983) (nat_lit 2366502261) (nat_lit 0) D2M8K2.t3311 from rfl, totK_node, tot3310, tot3311]
  decide +kernel

theorem arows3306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3306 = true := by
  rw [show D2M8K2.u3306 = KTree.node D2M8K2.t3312 (nat_lit 7772032) (nat_lit 3579397313) (nat_lit 0) D2M8K2.t3313 from rfl, allE_node, rows3312, irow3306, rows3313]
  all_goals rfl

theorem atot3306 : totK PD2M8K2 D2M8K2.u3306 = [0, 157181858693, 711077243238, 796292612710, 165424909212, 3880716147, 0, 0] := by
  rw [show D2M8K2.u3306 = KTree.node D2M8K2.t3312 (nat_lit 7772032) (nat_lit 3579397313) (nat_lit 0) D2M8K2.t3313 from rfl, totK_node, tot3312, tot3313]
  decide +kernel

theorem arows3307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3307 = true := by
  rw [show D2M8K2.u3307 = KTree.node D2M8K2.t3314 (nat_lit 7773631) (nat_lit 2437711975) (nat_lit 0) D2M8K2.t3315 from rfl, allE_node, rows3314, irow3307, rows3315]
  all_goals rfl

theorem atot3307 : totK PD2M8K2 D2M8K2.u3307 = [0, 260167665621, 806879714012, 641375546629, 98363343935, 1231730743, 0, 0] := by
  rw [show D2M8K2.u3307 = KTree.node D2M8K2.t3314 (nat_lit 7773631) (nat_lit 2437711975) (nat_lit 0) D2M8K2.t3315 from rfl, totK_node, tot3314, tot3315]
  decide +kernel

theorem arows3309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3309 = true := by
  rw [show D2M8K2.u3309 = KTree.node D2M8K2.t3316 (nat_lit 7775353) (nat_lit 1386487254) (nat_lit 0) D2M8K2.t3317 from rfl, allE_node, rows3316, irow3309, rows3317]
  all_goals rfl

theorem atot3309 : totK PD2M8K2 D2M8K2.u3309 = [0, 89126311553, 522750708302, 843591804124, 314192689014, 16594763897, 0, 0] := by
  rw [show D2M8K2.u3309 = KTree.node D2M8K2.t3316 (nat_lit 7775353) (nat_lit 1386487254) (nat_lit 0) D2M8K2.t3317 from rfl, totK_node, tot3316, tot3317]
  decide +kernel

theorem arows3310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3310 = true := by
  rw [show D2M8K2.u3310 = KTree.node D2M8K2.t3318 (nat_lit 7839430) (nat_lit 1361386197) (nat_lit 0) D2M8K2.t3319 from rfl, allE_node, rows3318, irow3310, rows3319]
  all_goals rfl

theorem atot3310 : totK PD2M8K2 D2M8K2.u3310 = [0, 307463687513, 895837180801, 522388097565, 36370369566, 0, 0, 0] := by
  rw [show D2M8K2.u3310 = KTree.node D2M8K2.t3318 (nat_lit 7839430) (nat_lit 1361386197) (nat_lit 0) D2M8K2.t3319 from rfl, totK_node, tot3318, tot3319]
  decide +kernel

theorem arows3313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3313 = true := by
  rw [show D2M8K2.u3313 = KTree.node D2M8K2.t3320 (nat_lit 7841423) (nat_lit 1982603284) (nat_lit 0) D2M8K2.t3321 from rfl, allE_node, rows3320, irow3313, rows3321]
  all_goals rfl

theorem atot3313 : totK PD2M8K2 D2M8K2.u3313 = [0, 162641084511, 708712039375, 810629435423, 135049773126, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3313 = KTree.node D2M8K2.t3320 (nat_lit 7841423) (nat_lit 1982603284) (nat_lit 0) D2M8K2.t3321 from rfl, totK_node, tot3320, tot3321]
  decide +kernel

theorem arows3314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3314 = true := by
  rw [show D2M8K2.u3314 = KTree.node D2M8K2.t3322 (nat_lit 7843062) (nat_lit 3739328852) (nat_lit 0) D2M8K2.t3323 from rfl, allE_node, rows3322, irow3314, rows3323]
  all_goals rfl

theorem atot3314 : totK PD2M8K2 D2M8K2.u3314 = [0, 263729926790, 803365131672, 596070272165, 137682945418, 13504285842, 0, 0] := by
  rw [show D2M8K2.u3314 = KTree.node D2M8K2.t3322 (nat_lit 7843062) (nat_lit 3739328852) (nat_lit 0) D2M8K2.t3323 from rfl, totK_node, tot3322, tot3323]
  decide +kernel

theorem arows3316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3316 = true := by
  rw [show D2M8K2.u3316 = KTree.node D2M8K2.t3324 (nat_lit 7844590) (nat_lit 3398992035) (nat_lit 0) D2M8K2.t3325 from rfl, allE_node, rows3324, irow3316, rows3325]
  all_goals rfl

theorem atot3316 : totK PD2M8K2 D2M8K2.u3316 = [0, 67693118168, 422183866352, 877296168103, 399067502264, 16646887132, 0, 0] := by
  rw [show D2M8K2.u3316 = KTree.node D2M8K2.t3324 (nat_lit 7844590) (nat_lit 3398992035) (nat_lit 0) D2M8K2.t3325 from rfl, totK_node, tot3324, tot3325]
  decide +kernel

theorem arows3317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3317 = true := by
  rw [show D2M8K2.u3317 = KTree.node D2M8K2.t3326 (nat_lit 7849557) (nat_lit 1734347021) (nat_lit 0) D2M8K2.t3327 from rfl, allE_node, rows3326, irow3317, rows3327]
  all_goals rfl

theorem atot3317 : totK PD2M8K2 D2M8K2.u3317 = [0, 377937047916, 952580912707, 480567548827, 35156394509, 0, 0, 0] := by
  rw [show D2M8K2.u3317 = KTree.node D2M8K2.t3326 (nat_lit 7849557) (nat_lit 1734347021) (nat_lit 0) D2M8K2.t3327 from rfl, totK_node, tot3326, tot3327]
  decide +kernel

theorem arows3325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3325 = true := by
  rw [show D2M8K2.u3325 = KTree.node D2M8K2.t3328 (nat_lit 7851200) (nat_lit 3717808584) (nat_lit 0) D2M8K2.t3329 from rfl, allE_node, rows3328, irow3325, rows3329]
  all_goals rfl

theorem atot3325 : totK PD2M8K2 D2M8K2.u3325 = [0, 0, 495410112822, 970434514869, 301989016645, 13250685261, 0, 0] := by
  rw [show D2M8K2.u3325 = KTree.node D2M8K2.t3328 (nat_lit 7851200) (nat_lit 3717808584) (nat_lit 0) D2M8K2.t3329 from rfl, totK_node, tot3328, tot3329]
  decide +kernel

theorem arows3326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3326 = true := by
  rw [show D2M8K2.u3326 = KTree.node D2M8K2.t3330 (nat_lit 7852555) (nat_lit 1742869688) (nat_lit 0) D2M8K2.t3331 from rfl, allE_node, rows3330, irow3326, rows3331]
  all_goals rfl

theorem atot3326 : totK PD2M8K2 D2M8K2.u3326 = [0, 341642900289, 890745606227, 511283278761, 49048235403, 0, 0, 0] := by
  rw [show D2M8K2.u3326 = KTree.node D2M8K2.t3330 (nat_lit 7852555) (nat_lit 1742869688) (nat_lit 0) D2M8K2.t3331 from rfl, totK_node, tot3330, tot3331]
  decide +kernel

theorem arows3328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3328 = true := by
  rw [show D2M8K2.u3328 = KTree.node D2M8K2.t3332 (nat_lit 7854148) (nat_lit 3694473237) (nat_lit 0) D2M8K2.t3333 from rfl, allE_node, rows3332, irow3328, rows3333]
  all_goals rfl

theorem atot3328 : totK PD2M8K2 D2M8K2.u3328 = [0, 73553217827, 614504779853, 892356286865, 187817209880, 4980514959, 0, 0] := by
  rw [show D2M8K2.u3328 = KTree.node D2M8K2.t3332 (nat_lit 7854148) (nat_lit 3694473237) (nat_lit 0) D2M8K2.t3333 from rfl, totK_node, tot3332, tot3333]
  decide +kernel

theorem arows3329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3329 = true := by
  rw [show D2M8K2.u3329 = KTree.node D2M8K2.t3334 (nat_lit 7856075) (nat_lit 2902669009) (nat_lit 0) D2M8K2.t3335 from rfl, allE_node, rows3334, irow3329, rows3335]
  all_goals rfl

theorem atot3329 : totK PD2M8K2 D2M8K2.u3329 = [0, 382108889677, 930122484122, 462337029400, 35173343073, 0, 0, 0] := by
  rw [show D2M8K2.u3329 = KTree.node D2M8K2.t3334 (nat_lit 7856075) (nat_lit 2902669009) (nat_lit 0) D2M8K2.t3335 from rfl, totK_node, tot3334, tot3335]
  decide +kernel

theorem arows3332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3332 = true := by
  rw [show D2M8K2.u3332 = KTree.node D2M8K2.t3336 (nat_lit 7857628) (nat_lit 3804538969) (nat_lit 0) D2M8K2.t3337 from rfl, allE_node, rows3336, irow3332, rows3337]
  all_goals rfl

theorem atot3332 : totK PD2M8K2 D2M8K2.u3332 = [0, 30722815107, 530697188717, 941353163431, 258219855514, 5952729029, 0, 0] := by
  rw [show D2M8K2.u3332 = KTree.node D2M8K2.t3336 (nat_lit 7857628) (nat_lit 3804538969) (nat_lit 0) D2M8K2.t3337 from rfl, totK_node, tot3336, tot3337]
  decide +kernel

theorem arows3333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3333 = true := by
  rw [show D2M8K2.u3333 = KTree.node D2M8K2.t3338 (nat_lit 7859682) (nat_lit 1522294067) (nat_lit 0) D2M8K2.t3339 from rfl, allE_node, rows3338, irow3333, rows3339]
  all_goals rfl

theorem atot3333 : totK PD2M8K2 D2M8K2.u3333 = [0, 0, 342316981706, 923492497737, 429019494689, 25958606185, 0, 0] := by
  rw [show D2M8K2.u3333 = KTree.node D2M8K2.t3338 (nat_lit 7859682) (nat_lit 1522294067) (nat_lit 0) D2M8K2.t3339 from rfl, totK_node, tot3338, tot3339]
  decide +kernel

theorem arows3335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3335 = true := by
  rw [show D2M8K2.u3335 = KTree.node D2M8K2.t3340 (nat_lit 7861378) (nat_lit 3998988920) (nat_lit 0) D2M8K2.t3341 from rfl, allE_node, rows3340, irow3335, rows3341]
  all_goals rfl

theorem atot3335 : totK PD2M8K2 D2M8K2.u3335 = [0, 0, 172588744140, 734936649778, 710652798920, 105357851026, 1217496766, 0] := by
  rw [show D2M8K2.u3335 = KTree.node D2M8K2.t3340 (nat_lit 7861378) (nat_lit 3998988920) (nat_lit 0) D2M8K2.t3341 from rfl, totK_node, tot3340, tot3341]
  decide +kernel

theorem arows3336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3336 = true := by
  rw [show D2M8K2.u3336 = KTree.node D2M8K2.t3342 (nat_lit 7863598) (nat_lit 3439000623) (nat_lit 0) D2M8K2.t3343 from rfl, allE_node, rows3342, irow3336, rows3343]
  all_goals rfl

theorem atot3336 : totK PD2M8K2 D2M8K2.u3336 = [0, 0, 408864076642, 944714571169, 421878483293, 30658984176, 0, 0] := by
  rw [show D2M8K2.u3336 = KTree.node D2M8K2.t3342 (nat_lit 7863598) (nat_lit 3439000623) (nat_lit 0) D2M8K2.t3343 from rfl, totK_node, tot3342, tot3343]
  decide +kernel

theorem arows3340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3340 = true := by
  rw [show D2M8K2.u3340 = KTree.node D2M8K2.t3344 (nat_lit 7870326) (nat_lit 3827012122) (nat_lit 0) D2M8K2.t3345 from rfl, allE_node, rows3344, irow3340, rows3345]
  all_goals rfl

theorem atot3340 : totK PD2M8K2 D2M8K2.u3340 = [0, 0, 358734833123, 951170635292, 472399205549, 29932460603, 0, 0] := by
  rw [show D2M8K2.u3340 = KTree.node D2M8K2.t3344 (nat_lit 7870326) (nat_lit 3827012122) (nat_lit 0) D2M8K2.t3345 from rfl, totK_node, tot3344, tot3345]
  decide +kernel

theorem arows3341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3341 = true := by
  rw [show D2M8K2.u3341 = KTree.node D2M8K2.t3346 (nat_lit 7872020) (nat_lit 3523512440) (nat_lit 0) D2M8K2.t3347 from rfl, allE_node, rows3346, irow3341, rows3347]
  all_goals rfl

theorem atot3341 : totK PD2M8K2 D2M8K2.u3341 = [0, 0, 18351256589, 509926355969, 908451826503, 279808477702, 13105450397, 0] := by
  rw [show D2M8K2.u3341 = KTree.node D2M8K2.t3346 (nat_lit 7872020) (nat_lit 3523512440) (nat_lit 0) D2M8K2.t3347 from rfl, totK_node, tot3346, tot3347]
  decide +kernel

theorem arows3343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3343 = true := by
  rw [show D2M8K2.u3343 = KTree.node D2M8K2.t3348 (nat_lit 7873444) (nat_lit 3628863352) (nat_lit 0) D2M8K2.t3349 from rfl, allE_node, rows3348, irow3343, rows3349]
  all_goals rfl

theorem atot3343 : totK PD2M8K2 D2M8K2.u3343 = [0, 0, 387520180328, 931522429491, 397638500800, 24037258637, 0, 0] := by
  rw [show D2M8K2.u3343 = KTree.node D2M8K2.t3348 (nat_lit 7873444) (nat_lit 3628863352) (nat_lit 0) D2M8K2.t3349 from rfl, totK_node, tot3348, tot3349]
  decide +kernel

theorem arows3344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3344 = true := by
  rw [show D2M8K2.u3344 = KTree.node D2M8K2.t3350 (nat_lit 7875434) (nat_lit 3992726487) (nat_lit 0) D2M8K2.t3351 from rfl, allE_node, rows3350, irow3344, rows3351]
  all_goals rfl

theorem atot3344 : totK PD2M8K2 D2M8K2.u3344 = [0, 0, 82235261621, 654034543760, 762572461773, 152202106450, 4630915822, 0] := by
  rw [show D2M8K2.u3344 = KTree.node D2M8K2.t3350 (nat_lit 7875434) (nat_lit 3992726487) (nat_lit 0) D2M8K2.t3351 from rfl, totK_node, tot3350, tot3351]
  decide +kernel

theorem arows3347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3347 = true := by
  rw [show D2M8K2.u3347 = KTree.node D2M8K2.t3352 (nat_lit 7877260) (nat_lit 2943865531) (nat_lit 0) D2M8K2.t3353 from rfl, allE_node, rows3352, irow3347, rows3353]
  all_goals rfl

theorem atot3347 : totK PD2M8K2 D2M8K2.u3347 = [0, 87253921853, 508338337502, 825473251037, 364595603337, 25140543007, 0, 0] := by
  rw [show D2M8K2.u3347 = KTree.node D2M8K2.t3352 (nat_lit 7877260) (nat_lit 2943865531) (nat_lit 0) D2M8K2.t3353 from rfl, totK_node, tot3352, tot3353]
  decide +kernel

theorem arows3348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3348 = true := by
  rw [show D2M8K2.u3348 = KTree.node D2M8K2.t3354 (nat_lit 7880861) (nat_lit 2194672649) (nat_lit 0) D2M8K2.t3355 from rfl, allE_node, rows3354, irow3348, rows3355]
  all_goals rfl

theorem atot3348 : totK PD2M8K2 D2M8K2.u3348 = [0, 289657558070, 867775501539, 553218146451, 52236912968, 0, 0, 0] := by
  rw [show D2M8K2.u3348 = KTree.node D2M8K2.t3354 (nat_lit 7880861) (nat_lit 2194672649) (nat_lit 0) D2M8K2.t3355 from rfl, totK_node, tot3354, tot3355]
  decide +kernel

theorem arows3350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3350 = true := by
  rw [show D2M8K2.u3350 = KTree.node D2M8K2.t3356 (nat_lit 7882991) (nat_lit 2305520964) (nat_lit 0) D2M8K2.t3357 from rfl, allE_node, rows3356, irow3350, rows3357]
  all_goals rfl

theorem atot3350 : totK PD2M8K2 D2M8K2.u3350 = [0, 176578327322, 732653090386, 778602452413, 125770498859, 1310517177, 0, 0] := by
  rw [show D2M8K2.u3350 = KTree.node D2M8K2.t3356 (nat_lit 7882991) (nat_lit 2305520964) (nat_lit 0) D2M8K2.t3357 from rfl, totK_node, tot3356, tot3357]
  decide +kernel

theorem arows3351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3351 = true := by
  rw [show D2M8K2.u3351 = KTree.node D2M8K2.t3358 (nat_lit 7884627) (nat_lit 3652879915) (nat_lit 0) D2M8K2.t3359 from rfl, allE_node, rows3358, irow3351, rows3359]
  all_goals rfl

theorem atot3351 : totK PD2M8K2 D2M8K2.u3351 = [0, 243087268148, 783931224035, 642628116197, 162764597668, 9654694938, 0, 0] := by
  rw [show D2M8K2.u3351 = KTree.node D2M8K2.t3358 (nat_lit 7884627) (nat_lit 3652879915) (nat_lit 0) D2M8K2.t3359 from rfl, totK_node, tot3358, tot3359]
  decide +kernel

theorem arows3356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3356 = true := by
  rw [show D2M8K2.u3356 = KTree.node D2M8K2.t3360 (nat_lit 7886343) (nat_lit 3628263446) (nat_lit 0) D2M8K2.t3361 from rfl, allE_node, rows3360, irow3356, rows3361]
  all_goals rfl

theorem atot3356 : totK PD2M8K2 D2M8K2.u3356 = [0, 152271798246, 657933035288, 792941019421, 220557028080, 5411637735, 0, 0] := by
  rw [show D2M8K2.u3356 = KTree.node D2M8K2.t3360 (nat_lit 7886343) (nat_lit 3628263446) (nat_lit 0) D2M8K2.t3361 from rfl, totK_node, tot3360, tot3361]
  decide +kernel

theorem arows3357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3357 = true := by
  rw [show D2M8K2.u3357 = KTree.node D2M8K2.t3362 (nat_lit 7888371) (nat_lit 2589093393) (nat_lit 0) D2M8K2.t3363 from rfl, allE_node, rows3362, irow3357, rows3363]
  all_goals rfl

theorem atot3357 : totK PD2M8K2 D2M8K2.u3357 = [0, 171049211041, 759507422548, 750025569352, 110750463036, 1070790515, 0, 0] := by
  rw [show D2M8K2.u3357 = KTree.node D2M8K2.t3362 (nat_lit 7888371) (nat_lit 2589093393) (nat_lit 0) D2M8K2.t3363 from rfl, totK_node, tot3362, tot3363]
  decide +kernel

theorem arows3359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3359 = true := by
  rw [show D2M8K2.u3359 = KTree.node D2M8K2.t3364 (nat_lit 7890539) (nat_lit 2091966135) (nat_lit 0) D2M8K2.t3365 from rfl, allE_node, rows3364, irow3359, rows3365]
  all_goals rfl

theorem atot3359 : totK PD2M8K2 D2M8K2.u3359 = [0, 351805924259, 837194489545, 511081282982, 90537429319, 3462014130, 0, 0] := by
  rw [show D2M8K2.u3359 = KTree.node D2M8K2.t3364 (nat_lit 7890539) (nat_lit 2091966135) (nat_lit 0) D2M8K2.t3365 from rfl, totK_node, tot3364, tot3365]
  decide +kernel

theorem arows3360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3360 = true := by
  rw [show D2M8K2.u3360 = KTree.node D2M8K2.t3366 (nat_lit 7892098) (nat_lit 3961226203) (nat_lit 0) D2M8K2.t3367 from rfl, allE_node, rows3366, irow3360, rows3367]
  all_goals rfl

theorem atot3360 : totK PD2M8K2 D2M8K2.u3360 = [0, 71795413511, 598697338209, 871890362726, 228473294939, 9668735432, 0, 0] := by
  rw [show D2M8K2.u3360 = KTree.node D2M8K2.t3366 (nat_lit 7892098) (nat_lit 3961226203) (nat_lit 0) D2M8K2.t3367 from rfl, totK_node, tot3366, tot3367]
  decide +kernel

theorem arows3363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3363 = true := by
  rw [show D2M8K2.u3363 = KTree.node D2M8K2.t3368 (nat_lit 7893884) (nat_lit 3364050675) (nat_lit 0) D2M8K2.t3369 from rfl, allE_node, rows3368, irow3363, rows3369]
  all_goals rfl

theorem atot3363 : totK PD2M8K2 D2M8K2.u3363 = [0, 310058167876, 805165994998, 557161806876, 112195038616, 3581949829, 0, 0] := by
  rw [show D2M8K2.u3363 = KTree.node D2M8K2.t3368 (nat_lit 7893884) (nat_lit 3364050675) (nat_lit 0) D2M8K2.t3369 from rfl, totK_node, tot3368, tot3369]
  decide +kernel

theorem arows3364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3364 = true := by
  rw [show D2M8K2.u3364 = KTree.node D2M8K2.t3370 (nat_lit 7895346) (nat_lit 3337029642) (nat_lit 0) D2M8K2.t3371 from rfl, allE_node, rows3370, irow3364, rows3371]
  all_goals rfl

theorem atot3364 : totK PD2M8K2 D2M8K2.u3364 = [0, 125607234435, 733425904904, 821548490112, 123112201321, 1096505104, 0, 0] := by
  rw [show D2M8K2.u3364 = KTree.node D2M8K2.t3370 (nat_lit 7895346) (nat_lit 3337029642) (nat_lit 0) D2M8K2.t3371 from rfl, totK_node, tot3370, tot3371]
  decide +kernel

theorem arows3366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3366 = true := by
  rw [show D2M8K2.u3366 = KTree.node D2M8K2.t3372 (nat_lit 7901062) (nat_lit 2850786478) (nat_lit 0) D2M8K2.t3373 from rfl, allE_node, rows3372, irow3366, rows3373]
  all_goals rfl

theorem atot3366 : totK PD2M8K2 D2M8K2.u3366 = [0, 0, 394468313474, 957963244976, 371464878899, 15876203078, 0, 0] := by
  rw [show D2M8K2.u3366 = KTree.node D2M8K2.t3372 (nat_lit 7901062) (nat_lit 2850786478) (nat_lit 0) D2M8K2.t3373 from rfl, totK_node, tot3372, tot3373]
  decide +kernel

theorem arows3367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3367 = true := by
  rw [show D2M8K2.u3367 = KTree.node D2M8K2.t3374 (nat_lit 7903030) (nat_lit 2697368598) (nat_lit 0) D2M8K2.t3375 from rfl, allE_node, rows3374, irow3367, rows3375]
  all_goals rfl

theorem atot3367 : totK PD2M8K2 D2M8K2.u3367 = [0, 0, 144256503638, 767715706946, 710481408082, 85230441518, 1138244013, 0] := by
  rw [show D2M8K2.u3367 = KTree.node D2M8K2.t3374 (nat_lit 7903030) (nat_lit 2697368598) (nat_lit 0) D2M8K2.t3375 from rfl, totK_node, tot3374, tot3375]
  decide +kernel

theorem arows3371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3371 = true := by
  rw [show D2M8K2.u3371 = KTree.node D2M8K2.t3376 (nat_lit 7905203) (nat_lit 1257741730) (nat_lit 0) D2M8K2.t3377 from rfl, allE_node, rows3376, irow3371, rows3377]
  all_goals rfl

theorem atot3371 : totK PD2M8K2 D2M8K2.u3371 = [0, 0, 527030226059, 967246843518, 301106347847, 7966418186, 0, 0] := by
  rw [show D2M8K2.u3371 = KTree.node D2M8K2.t3376 (nat_lit 7905203) (nat_lit 1257741730) (nat_lit 0) D2M8K2.t3377 from rfl, totK_node, tot3376, tot3377]
  decide +kernel

theorem arows3372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3372 = true := by
  rw [show D2M8K2.u3372 = KTree.node D2M8K2.t3378 (nat_lit 7910927) (nat_lit 2192456569) (nat_lit 0) D2M8K2.t3379 from rfl, allE_node, rows3378, irow3372, rows3379]
  all_goals rfl

theorem atot3372 : totK PD2M8K2 D2M8K2.u3372 = [0, 0, 377955262960, 958015420672, 396437188889, 19430336458, 0, 0] := by
  rw [show D2M8K2.u3372 = KTree.node D2M8K2.t3378 (nat_lit 7910927) (nat_lit 2192456569) (nat_lit 0) D2M8K2.t3379 from rfl, totK_node, tot3378, tot3379]
  decide +kernel

theorem arows3374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3374 = true := by
  rw [show D2M8K2.u3374 = KTree.node D2M8K2.t3380 (nat_lit 7914248) (nat_lit 3643078003) (nat_lit 0) D2M8K2.t3381 from rfl, allE_node, rows3380, irow3374, rows3381]
  all_goals rfl

theorem atot3374 : totK PD2M8K2 D2M8K2.u3374 = [0, 0, 370410668783, 926556791986, 429520933010, 25889854211, 0, 0] := by
  rw [show D2M8K2.u3374 = KTree.node D2M8K2.t3380 (nat_lit 7914248) (nat_lit 3643078003) (nat_lit 0) D2M8K2.t3381 from rfl, totK_node, tot3380, tot3381]
  decide +kernel

theorem arows3375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3375 = true := by
  rw [show D2M8K2.u3375 = KTree.node D2M8K2.t3382 (nat_lit 7915484) (nat_lit 3415495349) (nat_lit 0) D2M8K2.t3383 from rfl, allE_node, rows3382, irow3375, rows3383]
  all_goals rfl

theorem atot3375 : totK PD2M8K2 D2M8K2.u3375 = [0, 0, 213427627015, 809633004425, 602607905572, 76514850695, 1095107716, 0] := by
  rw [show D2M8K2.u3375 = KTree.node D2M8K2.t3382 (nat_lit 7915484) (nat_lit 3415495349) (nat_lit 0) D2M8K2.t3383 from rfl, totK_node, tot3382, tot3383]
  decide +kernel

theorem arows3378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3378 = true := by
  rw [show D2M8K2.u3378 = KTree.node D2M8K2.t3384 (nat_lit 7921290) (nat_lit 3769800760) (nat_lit 0) D2M8K2.t3385 from rfl, allE_node, rows3384, irow3378, rows3385]
  all_goals rfl

theorem atot3378 : totK PD2M8K2 D2M8K2.u3378 = [0, 238763643205, 596798039892, 463477609353, 354159602341, 93603305476, 3819176523, 0] := by
  rw [show D2M8K2.u3378 = KTree.node D2M8K2.t3384 (nat_lit 7921290) (nat_lit 3769800760) (nat_lit 0) D2M8K2.t3385 from rfl, totK_node, tot3384, tot3385]
  decide +kernel

theorem arows3379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3379 = true := by
  rw [show D2M8K2.u3379 = KTree.node D2M8K2.t3386 (nat_lit 7922980) (nat_lit 2756030232) (nat_lit 0) D2M8K2.t3387 from rfl, allE_node, rows3386, irow3379, rows3387]
  all_goals rfl

theorem atot3379 : totK PD2M8K2 D2M8K2.u3379 = [0, 140073074235, 706572276640, 804795936159, 130183031438, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3379 = KTree.node D2M8K2.t3386 (nat_lit 7922980) (nat_lit 2756030232) (nat_lit 0) D2M8K2.t3387 from rfl, totK_node, tot3386, tot3387]
  decide +kernel

theorem arows3381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3381 = true := by
  rw [show D2M8K2.u3381 = KTree.node D2M8K2.t3388 (nat_lit 7925376) (nat_lit 3070306666) (nat_lit 0) D2M8K2.t3389 from rfl, allE_node, rows3388, irow3381, rows3389]
  all_goals rfl

theorem atot3381 : totK PD2M8K2 D2M8K2.u3381 = [0, 345653182739, 912175634501, 540050399258, 50367970442, 0, 0, 0] := by
  rw [show D2M8K2.u3381 = KTree.node D2M8K2.t3388 (nat_lit 7925376) (nat_lit 3070306666) (nat_lit 0) D2M8K2.t3389 from rfl, totK_node, tot3388, tot3389]
  decide +kernel

theorem arows3382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3382 = true := by
  rw [show D2M8K2.u3382 = KTree.node D2M8K2.t3390 (nat_lit 7926899) (nat_lit 2813750243) (nat_lit 0) D2M8K2.t3391 from rfl, allE_node, rows3390, irow3382, rows3391]
  all_goals rfl

theorem atot3382 : totK PD2M8K2 D2M8K2.u3382 = [0, 70862748273, 510447232306, 853856689192, 360192392512, 24726425107, 0, 0] := by
  rw [show D2M8K2.u3382 = KTree.node D2M8K2.t3390 (nat_lit 7926899) (nat_lit 2813750243) (nat_lit 0) D2M8K2.t3391 from rfl, totK_node, tot3390, tot3391]
  decide +kernel

theorem arows3388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3388 = true := by
  rw [show D2M8K2.u3388 = KTree.node D2M8K2.t3392 (nat_lit 7928287) (nat_lit 1945860026) (nat_lit 0) D2M8K2.t3393 from rfl, allE_node, rows3392, irow3388, rows3393]
  all_goals rfl

theorem atot3388 : totK PD2M8K2 D2M8K2.u3388 = [0, 240762326468, 717176245771, 661626754699, 194637389683, 8078182869, 0, 0] := by
  rw [show D2M8K2.u3388 = KTree.node D2M8K2.t3392 (nat_lit 7928287) (nat_lit 1945860026) (nat_lit 0) D2M8K2.t3393 from rfl, totK_node, tot3392, tot3393]
  decide +kernel

theorem arows3389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3389 = true := by
  rw [show D2M8K2.u3389 = KTree.node D2M8K2.t3394 (nat_lit 7930170) (nat_lit 3727115493) (nat_lit 0) D2M8K2.t3395 from rfl, allE_node, rows3394, irow3389, rows3395]
  all_goals rfl

theorem atot3389 : totK PD2M8K2 D2M8K2.u3389 = [0, 149847961124, 648049084011, 813183645669, 190789840159, 5172807878, 0, 0] := by
  rw [show D2M8K2.u3389 = KTree.node D2M8K2.t3394 (nat_lit 7930170) (nat_lit 3727115493) (nat_lit 0) D2M8K2.t3395 from rfl, totK_node, tot3394, tot3395]
  decide +kernel

theorem arows3391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3391 = true := by
  rw [show D2M8K2.u3391 = KTree.node D2M8K2.t3396 (nat_lit 7932494) (nat_lit 3746255792) (nat_lit 0) D2M8K2.t3397 from rfl, allE_node, rows3396, irow3391, rows3397]
  all_goals rfl

theorem atot3391 : totK PD2M8K2 D2M8K2.u3391 = [0, 363324727061, 933036744633, 486752940665, 36396979364, 0, 0, 0] := by
  rw [show D2M8K2.u3391 = KTree.node D2M8K2.t3396 (nat_lit 7932494) (nat_lit 3746255792) (nat_lit 0) D2M8K2.t3397 from rfl, totK_node, tot3396, tot3397]
  decide +kernel

theorem arows3392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3392 = true := by
  rw [show D2M8K2.u3392 = KTree.node D2M8K2.t3398 (nat_lit 7934190) (nat_lit 4086215485) (nat_lit 0) D2M8K2.t3399 from rfl, allE_node, rows3398, irow3392, rows3399]
  all_goals rfl

theorem atot3392 : totK PD2M8K2 D2M8K2.u3392 = [0, 0, 492171619741, 967120846755, 300674018366, 13183098110, 0, 0] := by
  rw [show D2M8K2.u3392 = KTree.node D2M8K2.t3398 (nat_lit 7934190) (nat_lit 4086215485) (nat_lit 0) D2M8K2.t3399 from rfl, totK_node, tot3398, tot3399]
  decide +kernel

theorem arows3395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3395 = true := by
  rw [show D2M8K2.u3395 = KTree.node D2M8K2.t3400 (nat_lit 7939015) (nat_lit 1920152753) (nat_lit 0) D2M8K2.t3401 from rfl, allE_node, rows3400, irow3395, rows3401]
  all_goals rfl

theorem atot3395 : totK PD2M8K2 D2M8K2.u3395 = [0, 379278281100, 924745232685, 480119078128, 41770700026, 0, 0, 0] := by
  rw [show D2M8K2.u3395 = KTree.node D2M8K2.t3400 (nat_lit 7939015) (nat_lit 1920152753) (nat_lit 0) D2M8K2.t3401 from rfl, totK_node, tot3400, tot3401]
  decide +kernel

theorem arows3396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3396 = true := by
  rw [show D2M8K2.u3396 = KTree.node D2M8K2.t3402 (nat_lit 7940521) (nat_lit 1207327884) (nat_lit 0) D2M8K2.t3403 from rfl, allE_node, rows3402, irow3396, rows3403]
  all_goals rfl

theorem atot3396 : totK PD2M8K2 D2M8K2.u3396 = [0, 56674804355, 548080094195, 899586253858, 267755455355, 8644676715, 0, 0] := by
  rw [show D2M8K2.u3396 = KTree.node D2M8K2.t3402 (nat_lit 7940521) (nat_lit 1207327884) (nat_lit 0) D2M8K2.t3403 from rfl, totK_node, tot3402, tot3403]
  decide +kernel

theorem arows3398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3398 = true := by
  rw [show D2M8K2.u3398 = KTree.node D2M8K2.t3404 (nat_lit 7962898) (nat_lit 4073638830) (nat_lit 0) D2M8K2.t3405 from rfl, allE_node, rows3404, irow3398, rows3405]
  all_goals rfl

theorem atot3398 : totK PD2M8K2 D2M8K2.u3398 = [280299925571, 676101559317, 410391405230, 270429457341, 143151875035, 13338039113, 0, 0] := by
  rw [show D2M8K2.u3398 = KTree.node D2M8K2.t3404 (nat_lit 7962898) (nat_lit 4073638830) (nat_lit 0) D2M8K2.t3405 from rfl, totK_node, tot3404, tot3405]
  decide +kernel

theorem arows3399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3399 = true := by
  rw [show D2M8K2.u3399 = KTree.node D2M8K2.t3406 (nat_lit 7964436) (nat_lit 3249269530) (nat_lit 0) D2M8K2.t3407 from rfl, allE_node, rows3406, irow3399, rows3407]
  all_goals rfl

theorem atot3399 : totK PD2M8K2 D2M8K2.u3399 = [141262338374, 720764445865, 790892543540, 135304836385, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3399 = KTree.node D2M8K2.t3406 (nat_lit 7964436) (nat_lit 3249269530) (nat_lit 0) D2M8K2.t3407 from rfl, totK_node, tot3406, tot3407]
  decide +kernel

theorem arows3403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3403 = true := by
  rw [show D2M8K2.u3403 = KTree.node D2M8K2.t3408 (nat_lit 7970017) (nat_lit 1208017286) (nat_lit 0) D2M8K2.t3409 from rfl, allE_node, rows3408, irow3403, rows3409]
  all_goals rfl

theorem atot3403 : totK PD2M8K2 D2M8K2.u3403 = [331633402803, 889339968160, 536771439229, 49525475856, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3403 = KTree.node D2M8K2.t3408 (nat_lit 7970017) (nat_lit 1208017286) (nat_lit 0) D2M8K2.t3409 from rfl, totK_node, tot3408, tot3409]
  decide +kernel

theorem arows3404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3404 = true := by
  rw [show D2M8K2.u3404 = KTree.node D2M8K2.t3410 (nat_lit 7971609) (nat_lit 1798241795) (nat_lit 0) D2M8K2.t3411 from rfl, allE_node, rows3410, irow3404, rows3411]
  all_goals rfl

theorem atot3404 : totK PD2M8K2 D2M8K2.u3404 = [68371975852, 547829003013, 885682410982, 256454081183, 10568566766, 0, 0, 0] := by
  rw [show D2M8K2.u3404 = KTree.node D2M8K2.t3410 (nat_lit 7971609) (nat_lit 1798241795) (nat_lit 0) D2M8K2.t3411 from rfl, totK_node, tot3410, tot3411]
  decide +kernel

theorem arows3406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3406 = true := by
  rw [show D2M8K2.u3406 = KTree.node D2M8K2.t3412 (nat_lit 7973506) (nat_lit 3727610308) (nat_lit 0) D2M8K2.t3413 from rfl, allE_node, rows3412, irow3406, rows3413]
  all_goals rfl

theorem atot3406 : totK PD2M8K2 D2M8K2.u3406 = [331807364657, 882693801784, 518168907456, 71034040764, 2481160468, 0, 0, 0] := by
  rw [show D2M8K2.u3406 = KTree.node D2M8K2.t3412 (nat_lit 7973506) (nat_lit 3727610308) (nat_lit 0) D2M8K2.t3413 from rfl, totK_node, tot3412, tot3413]
  decide +kernel

theorem arows3407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3407 = true := by
  rw [show D2M8K2.u3407 = KTree.node D2M8K2.t3414 (nat_lit 7975098) (nat_lit 3918748990) (nat_lit 0) D2M8K2.t3415 from rfl, allE_node, rows3414, irow3407, rows3415]
  all_goals rfl

theorem atot3407 : totK PD2M8K2 D2M8K2.u3407 = [68433758957, 539230873679, 885601575282, 267390122424, 10680993762, 0, 0, 0] := by
  rw [show D2M8K2.u3407 = KTree.node D2M8K2.t3414 (nat_lit 7975098) (nat_lit 3918748990) (nat_lit 0) D2M8K2.t3415 from rfl, totK_node, tot3414, tot3415]
  decide +kernel

theorem arows3410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3410 = true := by
  rw [show D2M8K2.u3410 = KTree.node D2M8K2.t3416 (nat_lit 7976936) (nat_lit 3683002312) (nat_lit 0) D2M8K2.t3417 from rfl, allE_node, rows3416, irow3410, rows3417]
  all_goals rfl

theorem atot3410 : totK PD2M8K2 D2M8K2.u3410 = [330880180161, 882009472471, 519309294320, 71371234292, 2569691499, 0, 0, 0] := by
  rw [show D2M8K2.u3410 = KTree.node D2M8K2.t3416 (nat_lit 7976936) (nat_lit 3683002312) (nat_lit 0) D2M8K2.t3417 from rfl, totK_node, tot3416, tot3417]
  decide +kernel

theorem arows3411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3411 = true := by
  rw [show D2M8K2.u3411 = KTree.node D2M8K2.t3418 (nat_lit 7978497) (nat_lit 1787250882) (nat_lit 0) D2M8K2.t3419 from rfl, allE_node, rows3418, irow3411, rows3419]
  all_goals rfl

theorem atot3411 : totK PD2M8K2 D2M8K2.u3411 = [91637619653, 681040239440, 877209503801, 146603596783, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u3411 = KTree.node D2M8K2.t3418 (nat_lit 7978497) (nat_lit 1787250882) (nat_lit 0) D2M8K2.t3419 from rfl, totK_node, tot3418, tot3419]
  decide +kernel

theorem arows3413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3413 = true := by
  rw [show D2M8K2.u3413 = KTree.node D2M8K2.t3420 (nat_lit 7984142) (nat_lit 2211557045) (nat_lit 0) D2M8K2.t3421 from rfl, allE_node, rows3420, irow3413, rows3421]
  all_goals rfl

theorem atot3413 : totK PD2M8K2 D2M8K2.u3413 = [0, 348371078767, 943235726463, 433915667663, 22968107762, 0, 0, 0] := by
  rw [show D2M8K2.u3413 = KTree.node D2M8K2.t3420 (nat_lit 7984142) (nat_lit 2211557045) (nat_lit 0) D2M8K2.t3421 from rfl, totK_node, tot3420, tot3421]
  decide +kernel

theorem arows3414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3414 = true := by
  rw [show D2M8K2.u3414 = KTree.node D2M8K2.t3422 (nat_lit 7985716) (nat_lit 4059120367) (nat_lit 0) D2M8K2.t3423 from rfl, allE_node, rows3422, irow3414, rows3423]
  all_goals rfl

theorem atot3414 : totK PD2M8K2 D2M8K2.u3414 = [0, 122571661983, 676593877129, 782271818634, 145401435901, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3414 = KTree.node D2M8K2.t3422 (nat_lit 7985716) (nat_lit 4059120367) (nat_lit 0) D2M8K2.t3423 from rfl, totK_node, tot3422, tot3423]
  decide +kernel

theorem arows3419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3419 = true := by
  rw [show D2M8K2.u3419 = KTree.node D2M8K2.t3424 (nat_lit 7991023) (nat_lit 940685285) (nat_lit 0) D2M8K2.t3425 from rfl, allE_node, rows3424, irow3419, rows3425]
  all_goals rfl

theorem atot3419 : totK PD2M8K2 D2M8K2.u3419 = [0, 344891071219, 939878820758, 471012633609, 22786786411, 0, 0, 0] := by
  rw [show D2M8K2.u3419 = KTree.node D2M8K2.t3424 (nat_lit 7991023) (nat_lit 940685285) (nat_lit 0) D2M8K2.t3425 from rfl, totK_node, tot3424, tot3425]
  decide +kernel

theorem arows3420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3420 = true := by
  rw [show D2M8K2.u3420 = KTree.node D2M8K2.t3426 (nat_lit 7994691) (nat_lit 3545398558) (nat_lit 0) D2M8K2.t3427 from rfl, allE_node, rows3426, irow3420, rows3427]
  all_goals rfl

theorem atot3420 : totK PD2M8K2 D2M8K2.u3420 = [0, 399547251751, 956259524730, 415651449230, 20055071138, 0, 0, 0] := by
  rw [show D2M8K2.u3420 = KTree.node D2M8K2.t3426 (nat_lit 7994691) (nat_lit 3545398558) (nat_lit 0) D2M8K2.t3427 from rfl, totK_node, tot3426, tot3427]
  decide +kernel

theorem arows3422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3422 = true := by
  rw [show D2M8K2.u3422 = KTree.node D2M8K2.t3428 (nat_lit 7997768) (nat_lit 3625956652) (nat_lit 0) D2M8K2.t3429 from rfl, allE_node, rows3428, irow3422, rows3429]
  all_goals rfl

theorem atot3422 : totK PD2M8K2 D2M8K2.u3422 = [0, 351876339689, 929151994669, 462612362840, 28443192514, 0, 0, 0] := by
  rw [show D2M8K2.u3422 = KTree.node D2M8K2.t3428 (nat_lit 7997768) (nat_lit 3625956652) (nat_lit 0) D2M8K2.t3429 from rfl, totK_node, tot3428, tot3429]
  decide +kernel

theorem arows3423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3423 = true := by
  rw [show D2M8K2.u3423 = KTree.node D2M8K2.t3430 (nat_lit 8008138) (nat_lit 3516771506) (nat_lit 0) D2M8K2.t3431 from rfl, allE_node, rows3430, irow3423, rows3431]
  all_goals rfl

theorem atot3423 : totK PD2M8K2 D2M8K2.u3423 = [292455968535, 792053045548, 611080926625, 136916754601, 3896246883, 0, 0, 0] := by
  rw [show D2M8K2.u3423 = KTree.node D2M8K2.t3430 (nat_lit 8008138) (nat_lit 3516771506) (nat_lit 0) D2M8K2.t3431 from rfl, totK_node, tot3430, tot3431]
  decide +kernel

theorem arows3426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3426 = true := by
  rw [show D2M8K2.u3426 = KTree.node D2M8K2.t3432 (nat_lit 8009638) (nat_lit 3752079633) (nat_lit 0) D2M8K2.t3433 from rfl, allE_node, rows3432, irow3426, rows3433]
  all_goals rfl

theorem atot3426 : totK PD2M8K2 D2M8K2.u3426 = [148575475728, 635646789895, 740098841173, 288488487618, 25373788367, 0, 0, 0] := by
  rw [show D2M8K2.u3426 = KTree.node D2M8K2.t3432 (nat_lit 8009638) (nat_lit 3752079633) (nat_lit 0) D2M8K2.t3433 from rfl, totK_node, tot3432, tot3433]
  decide +kernel

theorem arows3427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3427 = true := by
  rw [show D2M8K2.u3427 = KTree.node D2M8K2.t3434 (nat_lit 8010841) (nat_lit 1306317421) (nat_lit 0) D2M8K2.t3435 from rfl, allE_node, rows3434, irow3427, rows3435]
  all_goals rfl

theorem atot3427 : totK PD2M8K2 D2M8K2.u3427 = [155694565819, 590348593695, 766378761068, 300430373165, 12235609738, 0, 0, 0] := by
  rw [show D2M8K2.u3427 = KTree.node D2M8K2.t3434 (nat_lit 8010841) (nat_lit 1306317421) (nat_lit 0) D2M8K2.t3435 from rfl, totK_node, tot3434, tot3435]
  decide +kernel

theorem arows3429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3429 = true := by
  rw [show D2M8K2.u3429 = KTree.node D2M8K2.t3436 (nat_lit 8012360) (nat_lit 3780826017) (nat_lit 0) D2M8K2.t3437 from rfl, allE_node, rows3436, irow3429, rows3437]
  all_goals rfl

theorem atot3429 : totK PD2M8K2 D2M8K2.u3429 = [258270991104, 806024901491, 636778482380, 101845179933, 1163840124, 0, 0, 0] := by
  rw [show D2M8K2.u3429 = KTree.node D2M8K2.t3436 (nat_lit 8012360) (nat_lit 3780826017) (nat_lit 0) D2M8K2.t3437 from rfl, totK_node, tot3436, tot3437]
  decide +kernel

theorem arows3430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3430 = true := by
  rw [show D2M8K2.u3430 = KTree.node D2M8K2.t3438 (nat_lit 8014085) (nat_lit 2343373989) (nat_lit 0) D2M8K2.t3439 from rfl, allE_node, rows3438, irow3430, rows3439]
  all_goals rfl

theorem atot3430 : totK PD2M8K2 D2M8K2.u3430 = [155785623112, 640192790316, 768392992242, 224759603415, 11873025674, 0, 0, 0] := by
  rw [show D2M8K2.u3430 = KTree.node D2M8K2.t3438 (nat_lit 8014085) (nat_lit 2343373989) (nat_lit 0) D2M8K2.t3439 from rfl, totK_node, tot3438, tot3439]
  decide +kernel

theorem arows3434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3434 = true := by
  rw [show D2M8K2.u3434 = KTree.node D2M8K2.t3440 (nat_lit 8015768) (nat_lit 3606369837) (nat_lit 0) D2M8K2.t3441 from rfl, allE_node, rows3440, irow3434, rows3441]
  all_goals rfl

theorem atot3434 : totK PD2M8K2 D2M8K2.u3434 = [258423083582, 815022695254, 634989433630, 96042242286, 1197396724, 0, 0, 0] := by
  rw [show D2M8K2.u3434 = KTree.node D2M8K2.t3440 (nat_lit 8015768) (nat_lit 3606369837) (nat_lit 0) D2M8K2.t3441 from rfl, totK_node, tot3440, tot3441]
  decide +kernel

theorem arows3435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3435 = true := by
  rw [show D2M8K2.u3435 = KTree.node D2M8K2.t3442 (nat_lit 8017488) (nat_lit 3525469540) (nat_lit 0) D2M8K2.t3443 from rfl, allE_node, rows3442, irow3435, rows3443]
  all_goals rfl

theorem atot3435 : totK PD2M8K2 D2M8K2.u3435 = [144445137846, 607765436623, 788462500071, 240372575290, 12040273252, 0, 0, 0] := by
  rw [show D2M8K2.u3435 = KTree.node D2M8K2.t3442 (nat_lit 8017488) (nat_lit 3525469540) (nat_lit 0) D2M8K2.t3443 from rfl, totK_node, tot3442, tot3443]
  decide +kernel

theorem arows3437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3437 = true := by
  rw [show D2M8K2.u3437 = KTree.node D2M8K2.t3444 (nat_lit 8018888) (nat_lit 3909129062) (nat_lit 0) D2M8K2.t3445 from rfl, allE_node, rows3444, irow3437, rows3445]
  all_goals rfl

theorem atot3437 : totK PD2M8K2 D2M8K2.u3437 = [279972474103, 871256508541, 602572278918, 62565999334, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3437 = KTree.node D2M8K2.t3444 (nat_lit 8018888) (nat_lit 3909129062) (nat_lit 0) D2M8K2.t3445 from rfl, totK_node, tot3444, tot3445]
  decide +kernel

theorem arows3438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3438 = true := by
  rw [show D2M8K2.u3438 = KTree.node D2M8K2.t3446 (nat_lit 8020848) (nat_lit 3400445438) (nat_lit 0) D2M8K2.t3447 from rfl, allE_node, rows3446, irow3438, rows3447]
  all_goals rfl

theorem atot3438 : totK PD2M8K2 D2M8K2.u3438 = [126224852308, 639772801018, 868087694587, 201787243191, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u3438 = KTree.node D2M8K2.t3446 (nat_lit 8020848) (nat_lit 3400445438) (nat_lit 0) D2M8K2.t3447 from rfl, totK_node, tot3446, tot3447]
  decide +kernel

theorem arows3441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3441 = true := by
  rw [show D2M8K2.u3441 = KTree.node D2M8K2.t3448 (nat_lit 8022898) (nat_lit 4023268641) (nat_lit 0) D2M8K2.t3449 from rfl, allE_node, rows3448, irow3441, rows3449]
  all_goals rfl

theorem atot3441 : totK PD2M8K2 D2M8K2.u3441 = [218196713264, 785962215288, 691871616140, 131162361864, 3593478102, 0, 0, 0] := by
  rw [show D2M8K2.u3441 = KTree.node D2M8K2.t3448 (nat_lit 8022898) (nat_lit 4023268641) (nat_lit 0) D2M8K2.t3449 from rfl, totK_node, tot3448, tot3449]
  decide +kernel

theorem arows3442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3442 = true := by
  rw [show D2M8K2.u3442 = KTree.node D2M8K2.t3450 (nat_lit 8028611) (nat_lit 2870342021) (nat_lit 0) D2M8K2.t3451 from rfl, allE_node, rows3450, irow3442, rows3451]
  all_goals rfl

theorem atot3442 : totK PD2M8K2 D2M8K2.u3442 = [0, 355344354365, 916842757548, 504980057194, 45270138924, 0, 0, 0] := by
  rw [show D2M8K2.u3442 = KTree.node D2M8K2.t3450 (nat_lit 8028611) (nat_lit 2870342021) (nat_lit 0) D2M8K2.t3451 from rfl, totK_node, tot3450, tot3451]
  decide +kernel

theorem arows3444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3444 = true := by
  rw [show D2M8K2.u3444 = KTree.node D2M8K2.t3452 (nat_lit 8029768) (nat_lit 3828653959) (nat_lit 0) D2M8K2.t3453 from rfl, allE_node, rows3452, irow3444, rows3453]
  all_goals rfl

theorem atot3444 : totK PD2M8K2 D2M8K2.u3444 = [0, 261688717314, 781414581918, 592077363658, 183455667110, 21385604922, 0, 0] := by
  rw [show D2M8K2.u3444 = KTree.node D2M8K2.t3452 (nat_lit 8029768) (nat_lit 3828653959) (nat_lit 0) D2M8K2.t3453 from rfl, totK_node, tot3452, tot3453]
  decide +kernel

theorem arows3445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3445 = true := by
  rw [show D2M8K2.u3445 = KTree.node D2M8K2.t3454 (nat_lit 8031227) (nat_lit 2052767670) (nat_lit 0) D2M8K2.t3455 from rfl, allE_node, rows3454, irow3445, rows3455]
  all_goals rfl

theorem atot3445 : totK PD2M8K2 D2M8K2.u3445 = [0, 65194258425, 449155180585, 879417599067, 365969807135, 15536268932, 0, 0] := by
  rw [show D2M8K2.u3445 = KTree.node D2M8K2.t3454 (nat_lit 8031227) (nat_lit 2052767670) (nat_lit 0) D2M8K2.t3455 from rfl, totK_node, tot3454, tot3455]
  decide +kernel

theorem arows3452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3452 = true := by
  rw [show D2M8K2.u3452 = KTree.node D2M8K2.t3456 (nat_lit 8032512) (nat_lit 3401275093) (nat_lit 0) D2M8K2.t3457 from rfl, allE_node, rows3456, irow3452, rows3457]
  all_goals rfl

theorem atot3452 : totK PD2M8K2 D2M8K2.u3452 = [0, 347794226139, 923846084825, 517592780369, 39015271457, 0, 0, 0] := by
  rw [show D2M8K2.u3452 = KTree.node D2M8K2.t3456 (nat_lit 8032512) (nat_lit 3401275093) (nat_lit 0) D2M8K2.t3457 from rfl, totK_node, tot3456, tot3457]
  decide +kernel

theorem arows3453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3453 = true := by
  rw [show D2M8K2.u3453 = KTree.node D2M8K2.t3458 (nat_lit 8034640) (nat_lit 3304765738) (nat_lit 0) D2M8K2.t3459 from rfl, allE_node, rows3458, irow3453, rows3459]
  all_goals rfl

theorem atot3453 : totK PD2M8K2 D2M8K2.u3453 = [0, 85074305833, 611931159037, 873370356554, 205388853433, 5159868635, 0, 0] := by
  rw [show D2M8K2.u3453 = KTree.node D2M8K2.t3458 (nat_lit 8034640) (nat_lit 3304765738) (nat_lit 0) D2M8K2.t3459 from rfl, totK_node, tot3458, tot3459]
  decide +kernel

theorem arows3455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3455 = true := by
  rw [show D2M8K2.u3455 = KTree.node D2M8K2.t3460 (nat_lit 8036358) (nat_lit 3721893022) (nat_lit 0) D2M8K2.t3461 from rfl, allE_node, rows3460, irow3455, rows3461]
  all_goals rfl

theorem atot3455 : totK PD2M8K2 D2M8K2.u3455 = [0, 328160024204, 907864105372, 543399053195, 47014310542, 0, 0, 0] := by
  rw [show D2M8K2.u3455 = KTree.node D2M8K2.t3460 (nat_lit 8036358) (nat_lit 3721893022) (nat_lit 0) D2M8K2.t3461 from rfl, totK_node, tot3460, tot3461]
  decide +kernel

theorem arows3456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3456 = true := by
  rw [show D2M8K2.u3456 = KTree.node D2M8K2.t3462 (nat_lit 8038176) (nat_lit 3255007763) (nat_lit 0) D2M8K2.t3463 from rfl, allE_node, rows3462, irow3456, rows3463]
  all_goals rfl

theorem atot3456 : totK PD2M8K2 D2M8K2.u3456 = [0, 136082462504, 632520151839, 805461765568, 203259680132, 5218872685, 0, 0] := by
  rw [show D2M8K2.u3456 = KTree.node D2M8K2.t3462 (nat_lit 8038176) (nat_lit 3255007763) (nat_lit 0) D2M8K2.t3463 from rfl, totK_node, tot3462, tot3463]
  decide +kernel

theorem arows3459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3459 = true := by
  rw [show D2M8K2.u3459 = KTree.node D2M8K2.t3464 (nat_lit 8039618) (nat_lit 4021558888) (nat_lit 0) D2M8K2.t3465 from rfl, allE_node, rows3464, irow3459, rows3465]
  all_goals rfl

theorem atot3459 : totK PD2M8K2 D2M8K2.u3459 = [0, 283098786786, 888184243922, 587771887116, 47480207112, 0, 0, 0] := by
  rw [show D2M8K2.u3459 = KTree.node D2M8K2.t3464 (nat_lit 8039618) (nat_lit 4021558888) (nat_lit 0) D2M8K2.t3465 from rfl, totK_node, tot3464, tot3465]
  decide +kernel

theorem arows3460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3460 = true := by
  rw [show D2M8K2.u3460 = KTree.node D2M8K2.t3466 (nat_lit 8041639) (nat_lit 2363600661) (nat_lit 0) D2M8K2.t3467 from rfl, allE_node, rows3466, irow3460, rows3467]
  all_goals rfl

theorem atot3460 : totK PD2M8K2 D2M8K2.u3460 = [0, 174023795246, 705703925665, 814466728899, 153882590114, 1415142070, 0, 0] := by
  rw [show D2M8K2.u3460 = KTree.node D2M8K2.t3466 (nat_lit 8041639) (nat_lit 2363600661) (nat_lit 0) D2M8K2.t3467 from rfl, totK_node, tot3466, tot3467]
  decide +kernel

theorem arows3462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3462 = true := by
  rw [show D2M8K2.u3462 = KTree.node D2M8K2.t3468 (nat_lit 8043747) (nat_lit 3476449182) (nat_lit 0) D2M8K2.t3469 from rfl, allE_node, rows3468, irow3462, rows3469]
  all_goals rfl

theorem atot3462 : totK PD2M8K2 D2M8K2.u3462 = [0, 173459609035, 753454225171, 762366336333, 135581165481, 1238673482, 0, 0] := by
  rw [show D2M8K2.u3462 = KTree.node D2M8K2.t3468 (nat_lit 8043747) (nat_lit 3476449182) (nat_lit 0) D2M8K2.t3469 from rfl, totK_node, tot3468, tot3469]
  decide +kernel

theorem arows3463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3463 = true := by
  rw [show D2M8K2.u3463 = KTree.node D2M8K2.t3470 (nat_lit 8045720) (nat_lit 3514548927) (nat_lit 0) D2M8K2.t3471 from rfl, allE_node, rows3470, irow3463, rows3471]
  all_goals rfl

theorem atot3463 : totK PD2M8K2 D2M8K2.u3463 = [244726993122, 597082281762, 389399710092, 359751678160, 160725350238, 8063697217, 0, 0] := by
  rw [show D2M8K2.u3463 = KTree.node D2M8K2.t3470 (nat_lit 8045720) (nat_lit 3514548927) (nat_lit 0) D2M8K2.t3471 from rfl, totK_node, tot3470, tot3471]
  decide +kernel

theorem arows3467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3467 = true := by
  rw [show D2M8K2.u3467 = KTree.node D2M8K2.t3472 (nat_lit 8047412) (nat_lit 3476848073) (nat_lit 0) D2M8K2.t3473 from rfl, allE_node, rows3472, irow3467, rows3473]
  all_goals rfl

theorem atot3467 : totK PD2M8K2 D2M8K2.u3467 = [132447351264, 708750442370, 806861837099, 135301365924, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3467 = KTree.node D2M8K2.t3472 (nat_lit 8047412) (nat_lit 3476848073) (nat_lit 0) D2M8K2.t3473 from rfl, totK_node, tot3472, tot3473]
  decide +kernel

theorem arows3468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3468 = true := by
  rw [show D2M8K2.u3468 = KTree.node D2M8K2.t3474 (nat_lit 8049792) (nat_lit 3318258776) (nat_lit 0) D2M8K2.t3475 from rfl, allE_node, rows3474, irow3468, rows3475]
  all_goals rfl

theorem atot3468 : totK PD2M8K2 D2M8K2.u3468 = [349324489638, 906702249827, 533025116812, 51461201567, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3468 = KTree.node D2M8K2.t3474 (nat_lit 8049792) (nat_lit 3318258776) (nat_lit 0) D2M8K2.t3475 from rfl, totK_node, tot3474, tot3475]
  decide +kernel

theorem arows3470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3470 = true := by
  rw [show D2M8K2.u3470 = KTree.node D2M8K2.t3476 (nat_lit 8051327) (nat_lit 2007904550) (nat_lit 0) D2M8K2.t3477 from rfl, allE_node, rows3476, irow3470, rows3477]
  all_goals rfl

theorem atot3470 : totK PD2M8K2 D2M8K2.u3470 = [70684700304, 506332682739, 846641663775, 383523015493, 29376414733, 0, 0, 0] := by
  rw [show D2M8K2.u3470 = KTree.node D2M8K2.t3476 (nat_lit 8051327) (nat_lit 2007904550) (nat_lit 0) D2M8K2.t3477 from rfl, totK_node, tot3476, tot3477]
  decide +kernel

theorem arows3471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3471 = true := by
  rw [show D2M8K2.u3471 = KTree.node D2M8K2.t3478 (nat_lit 8052632) (nat_lit 3491782222) (nat_lit 0) D2M8K2.t3479 from rfl, allE_node, rows3478, irow3471, rows3479]
  all_goals rfl

theorem atot3471 : totK PD2M8K2 D2M8K2.u3471 = [266448675464, 721857162354, 626546887878, 200165230352, 8188124600, 0, 0, 0] := by
  rw [show D2M8K2.u3471 = KTree.node D2M8K2.t3478 (nat_lit 8052632) (nat_lit 3491782222) (nat_lit 0) D2M8K2.t3479 from rfl, totK_node, tot3478, tot3479]
  decide +kernel

theorem arows3474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3474 = true := by
  rw [show D2M8K2.u3474 = KTree.node D2M8K2.t3480 (nat_lit 8054117) (nat_lit 2374331571) (nat_lit 0) D2M8K2.t3481 from rfl, allE_node, rows3480, irow3474, rows3481]
  all_goals rfl

theorem atot3474 : totK PD2M8K2 D2M8K2.u3474 = [171268294425, 757639681624, 752357875583, 124399083612, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u3474 = KTree.node D2M8K2.t3480 (nat_lit 8054117) (nat_lit 2374331571) (nat_lit 0) D2M8K2.t3481 from rfl, totK_node, tot3480, tot3481]
  decide +kernel

theorem arows3475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3475 = true := by
  rw [show D2M8K2.u3475 = KTree.node D2M8K2.t3482 (nat_lit 8059398) (nat_lit 3658516307) (nat_lit 0) D2M8K2.t3483 from rfl, allE_node, rows3482, irow3475, rows3483]
  all_goals rfl

theorem atot3475 : totK PD2M8K2 D2M8K2.u3475 = [187726090752, 642370269106, 720934075648, 214141718502, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u3475 = KTree.node D2M8K2.t3482 (nat_lit 8059398) (nat_lit 3658516307) (nat_lit 0) D2M8K2.t3483 from rfl, totK_node, tot3482, tot3483]
  decide +kernel

theorem arows3477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3477 = true := by
  rw [show D2M8K2.u3477 = KTree.node D2M8K2.t3484 (nat_lit 8060606) (nat_lit 3843185347) (nat_lit 0) D2M8K2.t3485 from rfl, allE_node, rows3484, irow3477, rows3485]
  all_goals rfl

theorem atot3477 : totK PD2M8K2 D2M8K2.u3477 = [234130774805, 796723445966, 659965378573, 100666037170, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u3477 = KTree.node D2M8K2.t3484 (nat_lit 8060606) (nat_lit 3843185347) (nat_lit 0) D2M8K2.t3485 from rfl, totK_node, tot3484, tot3485]
  decide +kernel

theorem arows3478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3478 = true := by
  rw [show D2M8K2.u3478 = KTree.node D2M8K2.t3486 (nat_lit 8062906) (nat_lit 3921725541) (nat_lit 0) D2M8K2.t3487 from rfl, allE_node, rows3486, irow3478, rows3487]
  all_goals rfl

theorem atot3478 : totK PD2M8K2 D2M8K2.u3478 = [222941632552, 744677888950, 714033084734, 145447781285, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u3478 = KTree.node D2M8K2.t3486 (nat_lit 8062906) (nat_lit 3921725541) (nat_lit 0) D2M8K2.t3487 from rfl, totK_node, tot3486, tot3487]
  decide +kernel

theorem arows3483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3483 = true := by
  rw [show D2M8K2.u3483 = KTree.node D2M8K2.t3488 (nat_lit 8064729) (nat_lit 1256586072) (nat_lit 0) D2M8K2.t3489 from rfl, allE_node, rows3488, irow3483, rows3489]
  all_goals rfl

theorem atot3483 : totK PD2M8K2 D2M8K2.u3483 = [103540504535, 642083063890, 842445030574, 209473462833, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u3483 = KTree.node D2M8K2.t3488 (nat_lit 8064729) (nat_lit 1256586072) (nat_lit 0) D2M8K2.t3489 from rfl, totK_node, tot3488, tot3489]
  decide +kernel

theorem arows3484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3484 = true := by
  rw [show D2M8K2.u3484 = KTree.node D2M8K2.t3490 (nat_lit 8067003) (nat_lit 3193242108) (nat_lit 0) D2M8K2.t3491 from rfl, allE_node, rows3490, irow3484, rows3491]
  all_goals rfl

theorem atot3484 : totK PD2M8K2 D2M8K2.u3484 = [0, 348857229180, 922256277885, 447233211062, 28046619281, 0, 0, 0] := by
  rw [show D2M8K2.u3484 = KTree.node D2M8K2.t3490 (nat_lit 8067003) (nat_lit 3193242108) (nat_lit 0) D2M8K2.t3491 from rfl, totK_node, tot3490, tot3491]
  decide +kernel

theorem arows3486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3486 = true := by
  rw [show D2M8K2.u3486 = KTree.node D2M8K2.t3492 (nat_lit 8068732) (nat_lit 3930662508) (nat_lit 0) D2M8K2.t3493 from rfl, allE_node, rows3492, irow3486, rows3493]
  all_goals rfl

theorem atot3486 : totK PD2M8K2 D2M8K2.u3486 = [0, 150650280000, 716464606281, 777340535127, 118707873272, 1206465782, 0, 0] := by
  rw [show D2M8K2.u3486 = KTree.node D2M8K2.t3492 (nat_lit 8068732) (nat_lit 3930662508) (nat_lit 0) D2M8K2.t3493 from rfl, totK_node, tot3492, tot3493]
  decide +kernel

theorem arows3487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3487 = true := by
  rw [show D2M8K2.u3487 = KTree.node D2M8K2.t3494 (nat_lit 8070899) (nat_lit 2877667170) (nat_lit 0) D2M8K2.t3495 from rfl, allE_node, rows3494, irow3487, rows3495]
  all_goals rfl

theorem atot3487 : totK PD2M8K2 D2M8K2.u3487 = [0, 362900269858, 940797039300, 492915546491, 34114009339, 0, 0, 0] := by
  rw [show D2M8K2.u3487 = KTree.node D2M8K2.t3494 (nat_lit 8070899) (nat_lit 2877667170) (nat_lit 0) D2M8K2.t3495 from rfl, totK_node, tot3494, tot3495]
  decide +kernel

theorem arows3490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3490 = true := by
  rw [show D2M8K2.u3490 = KTree.node D2M8K2.t3496 (nat_lit 8073856) (nat_lit 3781001236) (nat_lit 0) D2M8K2.t3497 from rfl, allE_node, rows3496, irow3490, rows3497]
  all_goals rfl

theorem atot3490 : totK PD2M8K2 D2M8K2.u3490 = [0, 379448946295, 945441838392, 447423731344, 28288117611, 0, 0, 0] := by
  rw [show D2M8K2.u3490 = KTree.node D2M8K2.t3496 (nat_lit 8073856) (nat_lit 3781001236) (nat_lit 0) D2M8K2.t3497 from rfl, totK_node, tot3496, tot3497]
  decide +kernel

theorem arows3491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3491 = true := by
  rw [show D2M8K2.u3491 = KTree.node D2M8K2.t3498 (nat_lit 8075558) (nat_lit 3952843070) (nat_lit 0) D2M8K2.t3499 from rfl, allE_node, rows3498, irow3491, rows3499]
  all_goals rfl

theorem atot3491 : totK PD2M8K2 D2M8K2.u3491 = [0, 19230754378, 508256317890, 905616999041, 274994357552, 13016197374, 0, 0] := by
  rw [show D2M8K2.u3491 = KTree.node D2M8K2.t3498 (nat_lit 8075558) (nat_lit 3952843070) (nat_lit 0) D2M8K2.t3499 from rfl, totK_node, tot3498, tot3499]
  decide +kernel

theorem arows3493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3493 = true := by
  rw [show D2M8K2.u3493 = KTree.node D2M8K2.t3500 (nat_lit 8080709) (nat_lit 2337965196) (nat_lit 0) D2M8K2.t3501 from rfl, allE_node, rows3500, irow3493, rows3501]
  all_goals rfl

theorem atot3493 : totK PD2M8K2 D2M8K2.u3493 = [0, 383332021173, 937678521454, 445668915145, 28195252177, 0, 0, 0] := by
  rw [show D2M8K2.u3493 = KTree.node D2M8K2.t3500 (nat_lit 8080709) (nat_lit 2337965196) (nat_lit 0) D2M8K2.t3501 from rfl, totK_node, tot3500, tot3501]
  decide +kernel

theorem arows3494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3494 = true := by
  rw [show D2M8K2.u3494 = KTree.node D2M8K2.t3502 (nat_lit 8082466) (nat_lit 3504793056) (nat_lit 0) D2M8K2.t3503 from rfl, allE_node, rows3502, irow3494, rows3503]
  all_goals rfl

theorem atot3494 : totK PD2M8K2 D2M8K2.u3494 = [0, 103139165848, 666333977862, 781589261669, 152576501977, 4574395652, 0, 0] := by
  rw [show D2M8K2.u3494 = KTree.node D2M8K2.t3502 (nat_lit 8082466) (nat_lit 3504793056) (nat_lit 0) D2M8K2.t3503 from rfl, totK_node, tot3502, tot3503]
  decide +kernel

theorem arows3498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3498 = true := by
  rw [show D2M8K2.u3498 = KTree.node D2M8K2.t3504 (nat_lit 8084353) (nat_lit 1419478073) (nat_lit 0) D2M8K2.t3505 from rfl, allE_node, rows3504, irow3498, rows3505]
  all_goals rfl

theorem atot3498 : totK PD2M8K2 D2M8K2.u3498 = [87379608540, 449268731804, 799151017245, 447655731457, 40252704969, 0, 0, 0] := by
  rw [show D2M8K2.u3498 = KTree.node D2M8K2.t3504 (nat_lit 8084353) (nat_lit 1419478073) (nat_lit 0) D2M8K2.t3505 from rfl, totK_node, tot3504, tot3505]
  decide +kernel

theorem arows3499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3499 = true := by
  rw [show D2M8K2.u3499 = KTree.node D2M8K2.t3506 (nat_lit 8088253) (nat_lit 1210781706) (nat_lit 0) D2M8K2.t3507 from rfl, allE_node, rows3506, irow3499, rows3507]
  all_goals rfl

theorem atot3499 : totK PD2M8K2 D2M8K2.u3499 = [289883559307, 860895496987, 564660159304, 58386644521, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3499 = KTree.node D2M8K2.t3506 (nat_lit 8088253) (nat_lit 1210781706) (nat_lit 0) D2M8K2.t3507 from rfl, totK_node, tot3506, tot3507]
  decide +kernel

theorem arows3501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3501 = true := by
  rw [show D2M8K2.u3501 = KTree.node D2M8K2.t3508 (nat_lit 8090350) (nat_lit 4028020860) (nat_lit 0) D2M8K2.t3509 from rfl, allE_node, rows3508, irow3501, rows3509]
  all_goals rfl

theorem atot3501 : totK PD2M8K2 D2M8K2.u3501 = [185044317917, 734812618696, 779288875088, 131386096350, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3501 = KTree.node D2M8K2.t3508 (nat_lit 8090350) (nat_lit 4028020860) (nat_lit 0) D2M8K2.t3509 from rfl, totK_node, tot3508, tot3509]
  decide +kernel

theorem arows3502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3502 = true := by
  rw [show D2M8K2.u3502 = KTree.node D2M8K2.t3510 (nat_lit 8091994) (nat_lit 3932886106) (nat_lit 0) D2M8K2.t3511 from rfl, allE_node, rows3510, irow3502, rows3511]
  all_goals rfl

theorem atot3502 : totK PD2M8K2 D2M8K2.u3502 = [235036726497, 760613756224, 621203669110, 198471595468, 21383147344, 0, 0, 0] := by
  rw [show D2M8K2.u3502 = KTree.node D2M8K2.t3510 (nat_lit 8091994) (nat_lit 3932886106) (nat_lit 0) D2M8K2.t3511 from rfl, totK_node, tot3510, tot3511]
  decide +kernel

theorem arows3505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3505 = true := by
  rw [show D2M8K2.u3505 = KTree.node D2M8K2.t3512 (nat_lit 8093488) (nat_lit 3338320596) (nat_lit 0) D2M8K2.t3513 from rfl, allE_node, rows3512, irow3505, rows3513]
  all_goals rfl

theorem atot3505 : totK PD2M8K2 D2M8K2.u3505 = [84104726401, 474556218173, 852772998434, 374379881325, 16179348042, 0, 0, 0] := by
  rw [show D2M8K2.u3505 = KTree.node D2M8K2.t3512 (nat_lit 8093488) (nat_lit 3338320596) (nat_lit 0) D2M8K2.t3513 from rfl, totK_node, tot3512, tot3513]
  decide +kernel

theorem arows3506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3506 = true := by
  rw [show D2M8K2.u3506 = KTree.node D2M8K2.t3514 (nat_lit 8098507) (nat_lit 2224574032) (nat_lit 0) D2M8K2.t3515 from rfl, allE_node, rows3514, irow3506, rows3515]
  all_goals rfl

theorem atot3506 : totK PD2M8K2 D2M8K2.u3506 = [353798988194, 933042505991, 513178324909, 38952519691, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3506 = KTree.node D2M8K2.t3514 (nat_lit 8098507) (nat_lit 2224574032) (nat_lit 0) D2M8K2.t3515 from rfl, totK_node, tot3514, tot3515]
  decide +kernel

theorem arows3508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3508 = true := by
  rw [show D2M8K2.u3508 = KTree.node D2M8K2.t3516 (nat_lit 8100143) (nat_lit 2581241356) (nat_lit 0) D2M8K2.t3517 from rfl, allE_node, rows3516, irow3508, rows3517]
  all_goals rfl

theorem atot3508 : totK PD2M8K2 D2M8K2.u3508 = [33838848500, 478657342190, 943977222403, 309618550003, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u3508 = KTree.node D2M8K2.t3516 (nat_lit 8100143) (nat_lit 2581241356) (nat_lit 0) D2M8K2.t3517 from rfl, totK_node, tot3516, tot3517]
  decide +kernel

theorem arows3509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3509 = true := by
  rw [show D2M8K2.u3509 = KTree.node D2M8K2.t3518 (nat_lit 8101488) (nat_lit 3500565252) (nat_lit 0) D2M8K2.t3519 from rfl, allE_node, rows3518, irow3509, rows3519]
  all_goals rfl

theorem atot3509 : totK PD2M8K2 D2M8K2.u3509 = [368884694842, 914990551167, 482656496476, 40237567013, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3509 = KTree.node D2M8K2.t3518 (nat_lit 8101488) (nat_lit 3500565252) (nat_lit 0) D2M8K2.t3519 from rfl, totK_node, tot3518, tot3519]
  decide +kernel

theorem arows3515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3515 = true := by
  rw [show D2M8K2.u3515 = KTree.node D2M8K2.t3520 (nat_lit 8103206) (nat_lit 4091745354) (nat_lit 0) D2M8K2.t3521 from rfl, allE_node, rows3520, irow3515, rows3521]
  all_goals rfl

theorem atot3515 : totK PD2M8K2 D2M8K2.u3515 = [67949479629, 614759337626, 895159305726, 205826244959, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u3515 = KTree.node D2M8K2.t3520 (nat_lit 8103206) (nat_lit 4091745354) (nat_lit 0) D2M8K2.t3521 from rfl, totK_node, tot3520, tot3521]
  decide +kernel

theorem arows3516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3516 = true := by
  rw [show D2M8K2.u3516 = KTree.node D2M8K2.t3522 (nat_lit 8105334) (nat_lit 3812646336) (nat_lit 0) D2M8K2.t3523 from rfl, allE_node, rows3522, irow3516, rows3523]
  all_goals rfl

theorem atot3516 : totK PD2M8K2 D2M8K2.u3516 = [281393496540, 841715784339, 620213687986, 89119503813, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u3516 = KTree.node D2M8K2.t3522 (nat_lit 8105334) (nat_lit 3812646336) (nat_lit 0) D2M8K2.t3523 from rfl, totK_node, tot3522, tot3523]
  decide +kernel

theorem arows3518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3518 = true := by
  rw [show D2M8K2.u3518 = KTree.node D2M8K2.t3524 (nat_lit 8107621) (nat_lit 1364819205) (nat_lit 0) D2M8K2.t3525 from rfl, allE_node, rows3524, irow3518, rows3525]
  all_goals rfl

theorem atot3518 : totK PD2M8K2 D2M8K2.u3518 = [0, 414618899731, 957920513646, 383742924414, 19485467738, 0, 0, 0] := by
  rw [show D2M8K2.u3518 = KTree.node D2M8K2.t3524 (nat_lit 8107621) (nat_lit 1364819205) (nat_lit 0) D2M8K2.t3525 from rfl, totK_node, tot3524, tot3525]
  decide +kernel

theorem arows3519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3519 = true := by
  rw [show D2M8K2.u3519 = KTree.node D2M8K2.t3526 (nat_lit 8109263) (nat_lit 2105554530) (nat_lit 0) D2M8K2.t3527 from rfl, allE_node, rows3526, irow3519, rows3527]
  all_goals rfl

theorem atot3519 : totK PD2M8K2 D2M8K2.u3519 = [0, 222857565217, 783065607200, 654087017957, 88971158940, 1239866073, 0, 0] := by
  rw [show D2M8K2.u3519 = KTree.node D2M8K2.t3526 (nat_lit 8109263) (nat_lit 2105554530) (nat_lit 0) D2M8K2.t3527 from rfl, totK_node, tot3526, tot3527]
  decide +kernel

theorem arows3522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3522 = true := by
  rw [show D2M8K2.u3522 = KTree.node D2M8K2.t3528 (nat_lit 8111758) (nat_lit 3602972963) (nat_lit 0) D2M8K2.t3529 from rfl, allE_node, rows3528, irow3522, rows3529]
  all_goals rfl

theorem atot3522 : totK PD2M8K2 D2M8K2.u3522 = [0, 264809150759, 844466257757, 645721148998, 66364385274, 0, 0, 0] := by
  rw [show D2M8K2.u3522 = KTree.node D2M8K2.t3528 (nat_lit 8111758) (nat_lit 3602972963) (nat_lit 0) D2M8K2.t3529 from rfl, totK_node, tot3528, tot3529]
  decide +kernel

theorem arows3523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3523 = true := by
  rw [show D2M8K2.u3523 = KTree.node D2M8K2.t3530 (nat_lit 8118234) (nat_lit 3901361371) (nat_lit 0) D2M8K2.t3531 from rfl, allE_node, rows3530, irow3523, rows3531]
  all_goals rfl

theorem atot3523 : totK PD2M8K2 D2M8K2.u3523 = [0, 382668325306, 940206040417, 464694455050, 34055895214, 0, 0, 0] := by
  rw [show D2M8K2.u3523 = KTree.node D2M8K2.t3530 (nat_lit 8118234) (nat_lit 3901361371) (nat_lit 0) D2M8K2.t3531 from rfl, totK_node, tot3530, tot3531]
  decide +kernel

theorem arows3525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3525 = true := by
  rw [show D2M8K2.u3525 = KTree.node D2M8K2.t3532 (nat_lit 8119709) (nat_lit 1867072274) (nat_lit 0) D2M8K2.t3533 from rfl, allE_node, rows3532, irow3525, rows3533]
  all_goals rfl

theorem atot3525 : totK PD2M8K2 D2M8K2.u3525 = [0, 203626805219, 787875330898, 681622804306, 101501405923, 1171084559, 0, 0] := by
  rw [show D2M8K2.u3525 = KTree.node D2M8K2.t3532 (nat_lit 8119709) (nat_lit 1867072274) (nat_lit 0) D2M8K2.t3533 from rfl, totK_node, tot3532, tot3533]
  decide +kernel

theorem arows3526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3526 = true := by
  rw [show D2M8K2.u3526 = KTree.node D2M8K2.t3534 (nat_lit 8121397) (nat_lit 1168595738) (nat_lit 0) D2M8K2.t3535 from rfl, allE_node, rows3534, irow3526, rows3535]
  all_goals rfl

theorem atot3526 : totK PD2M8K2 D2M8K2.u3526 = [0, 176997651882, 656349235250, 703542984519, 203921861303, 11934365838, 0, 0] := by
  rw [show D2M8K2.u3526 = KTree.node D2M8K2.t3534 (nat_lit 8121397) (nat_lit 1168595738) (nat_lit 0) D2M8K2.t3535 from rfl, totK_node, tot3534, tot3535]
  decide +kernel

theorem arows3530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3530 = true := by
  rw [show D2M8K2.u3530 = KTree.node D2M8K2.t3536 (nat_lit 8122814) (nat_lit 3781039000) (nat_lit 0) D2M8K2.t3537 from rfl, allE_node, rows3536, irow3530, rows3537]
  all_goals rfl

theorem atot3530 : totK PD2M8K2 D2M8K2.u3530 = [0, 242903046821, 827107182992, 610217731841, 74438346877, 1053411165, 0, 0] := by
  rw [show D2M8K2.u3530 = KTree.node D2M8K2.t3536 (nat_lit 8122814) (nat_lit 3781039000) (nat_lit 0) D2M8K2.t3537 from rfl, totK_node, tot3536, tot3537]
  decide +kernel

theorem arows3531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3531 = true := by
  rw [show D2M8K2.u3531 = KTree.node D2M8K2.t3538 (nat_lit 8125190) (nat_lit 3350606036) (nat_lit 0) D2M8K2.t3539 from rfl, allE_node, rows3538, irow3531, rows3539]
  all_goals rfl

theorem atot3531 : totK PD2M8K2 D2M8K2.u3531 = [0, 240995571142, 755262674119, 662515836070, 119436198196, 3667207281, 0, 0] := by
  rw [show D2M8K2.u3531 = KTree.node D2M8K2.t3538 (nat_lit 8125190) (nat_lit 3350606036) (nat_lit 0) D2M8K2.t3539 from rfl, totK_node, tot3538, tot3539]
  decide +kernel

theorem arows3533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3533 = true := by
  rw [show D2M8K2.u3533 = KTree.node D2M8K2.t3540 (nat_lit 8128709) (nat_lit 2340079793) (nat_lit 0) D2M8K2.t3541 from rfl, allE_node, rows3540, irow3533, rows3541]
  all_goals rfl

theorem atot3533 : totK PD2M8K2 D2M8K2.u3533 = [257732979108, 720191017146, 573675238310, 220862312041, 20790672307, 0, 0, 0] := by
  rw [show D2M8K2.u3533 = KTree.node D2M8K2.t3540 (nat_lit 8128709) (nat_lit 2340079793) (nat_lit 0) D2M8K2.t3541 from rfl, totK_node, tot3540, tot3541]
  decide +kernel

theorem arows3534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3534 = true := by
  rw [show D2M8K2.u3534 = KTree.node D2M8K2.t3542 (nat_lit 8130332) (nat_lit 3136601931) (nat_lit 0) D2M8K2.t3543 from rfl, allE_node, rows3542, irow3534, rows3543]
  all_goals rfl

theorem atot3534 : totK PD2M8K2 D2M8K2.u3534 = [138678414711, 700888423422, 786715431828, 133658649246, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3534 = KTree.node D2M8K2.t3542 (nat_lit 8130332) (nat_lit 3136601931) (nat_lit 0) D2M8K2.t3543 from rfl, totK_node, tot3542, tot3543]
  decide +kernel

theorem arows3537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3537 = true := by
  rw [show D2M8K2.u3537 = KTree.node D2M8K2.t3544 (nat_lit 8132670) (nat_lit 2594735448) (nat_lit 0) D2M8K2.t3545 from rfl, allE_node, rows3544, irow3537, rows3545]
  all_goals rfl

theorem atot3537 : totK PD2M8K2 D2M8K2.u3537 = [356478244051, 894991614456, 535297963481, 48913759280, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3537 = KTree.node D2M8K2.t3544 (nat_lit 8132670) (nat_lit 2594735448) (nat_lit 0) D2M8K2.t3545 from rfl, totK_node, tot3544, tot3545]
  decide +kernel

theorem arows3538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3538 = true := by
  rw [show D2M8K2.u3538 = KTree.node D2M8K2.t3546 (nat_lit 8134201) (nat_lit 804043985) (nat_lit 0) D2M8K2.t3547 from rfl, allE_node, rows3546, irow3538, rows3547]
  all_goals rfl

theorem atot3538 : totK PD2M8K2 D2M8K2.u3538 = [69851549050, 537552823656, 836368433982, 347021596147, 28232996955, 0, 0, 0] := by
  rw [show D2M8K2.u3538 = KTree.node D2M8K2.t3546 (nat_lit 8134201) (nat_lit 804043985) (nat_lit 0) D2M8K2.t3547 from rfl, totK_node, tot3546, tot3547]
  decide +kernel

theorem arows3540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3540 = true := by
  rw [show D2M8K2.u3540 = KTree.node D2M8K2.t3548 (nat_lit 8135493) (nat_lit 1511480967) (nat_lit 0) D2M8K2.t3549 from rfl, allE_node, rows3548, irow3540, rows3549]
  all_goals rfl

theorem atot3540 : totK PD2M8K2 D2M8K2.u3540 = [218954739359, 658993502826, 683141448910, 242265314908, 9326398835, 0, 0, 0] := by
  rw [show D2M8K2.u3540 = KTree.node D2M8K2.t3548 (nat_lit 8135493) (nat_lit 1511480967) (nat_lit 0) D2M8K2.t3549 from rfl, totK_node, tot3548, tot3549]
  decide +kernel

theorem arows3541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3541 = true := by
  rw [show D2M8K2.u3541 = KTree.node D2M8K2.t3550 (nat_lit 8136984) (nat_lit 2791722214) (nat_lit 0) D2M8K2.t3551 from rfl, allE_node, rows3550, irow3541, rows3551]
  all_goals rfl

theorem atot3541 : totK PD2M8K2 D2M8K2.u3541 = [198577029588, 771181637165, 696734162352, 113121103401, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u3541 = KTree.node D2M8K2.t3550 (nat_lit 8136984) (nat_lit 2791722214) (nat_lit 0) D2M8K2.t3551 from rfl, totK_node, tot3550, tot3551]
  decide +kernel

theorem arows3546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3546 = true := by
  rw [show D2M8K2.u3546 = KTree.node D2M8K2.t3552 (nat_lit 8138714) (nat_lit 3902906445) (nat_lit 0) D2M8K2.t3553 from rfl, allE_node, rows3552, irow3546, rows3553]
  all_goals rfl

theorem atot3546 : totK PD2M8K2 D2M8K2.u3546 = [170590953727, 645908676209, 733031448918, 216203405408, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u3546 = KTree.node D2M8K2.t3552 (nat_lit 8138714) (nat_lit 3902906445) (nat_lit 0) D2M8K2.t3553 from rfl, totK_node, tot3552, tot3553]
  decide +kernel

theorem arows3547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3547 = true := by
  rw [show D2M8K2.u3547 = KTree.node D2M8K2.t3554 (nat_lit 8140331) (nat_lit 2262757415) (nat_lit 0) D2M8K2.t3555 from rfl, allE_node, rows3554, irow3547, rows3555]
  all_goals rfl

theorem atot3547 : totK PD2M8K2 D2M8K2.u3547 = [247149563842, 787416505021, 644239216606, 107762381831, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u3547 = KTree.node D2M8K2.t3554 (nat_lit 8140331) (nat_lit 2262757415) (nat_lit 0) D2M8K2.t3555 from rfl, totK_node, tot3554, tot3555]
  decide +kernel

theorem arows3549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3549 = true := by
  rw [show D2M8K2.u3549 = KTree.node D2M8K2.t3556 (nat_lit 8142055) (nat_lit 2353804635) (nat_lit 0) D2M8K2.t3557 from rfl, allE_node, rows3556, irow3549, rows3557]
  all_goals rfl

theorem atot3549 : totK PD2M8K2 D2M8K2.u3549 = [175160306834, 653419557636, 727059228350, 228550490059, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u3549 = KTree.node D2M8K2.t3556 (nat_lit 8142055) (nat_lit 2353804635) (nat_lit 0) D2M8K2.t3557 from rfl, totK_node, tot3556, tot3557]
  decide +kernel

theorem arows3550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3550 = true := by
  rw [show D2M8K2.u3550 = KTree.node D2M8K2.t3558 (nat_lit 8143379) (nat_lit 2494970614) (nat_lit 0) D2M8K2.t3559 from rfl, allE_node, rows3558, irow3550, rows3559]
  all_goals rfl

theorem atot3550 : totK PD2M8K2 D2M8K2.u3550 = [269119064056, 821465554563, 628841234568, 86706227058, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u3550 = KTree.node D2M8K2.t3558 (nat_lit 8143379) (nat_lit 2494970614) (nat_lit 0) D2M8K2.t3559 from rfl, totK_node, tot3558, tot3559]
  decide +kernel

theorem arows3553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3553 = true := by
  rw [show D2M8K2.u3553 = KTree.node D2M8K2.t3560 (nat_lit 8145307) (nat_lit 2118184586) (nat_lit 0) D2M8K2.t3561 from rfl, allE_node, rows3560, irow3553, rows3561]
  all_goals rfl

theorem atot3553 : totK PD2M8K2 D2M8K2.u3553 = [0, 526997437316, 1018496263001, 264596862026, 5253830308, 0, 0, 0] := by
  rw [show D2M8K2.u3553 = KTree.node D2M8K2.t3560 (nat_lit 8145307) (nat_lit 2118184586) (nat_lit 0) D2M8K2.t3561 from rfl, totK_node, tot3560, tot3561]
  decide +kernel

theorem arows3554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3554 = true := by
  rw [show D2M8K2.u3554 = KTree.node D2M8K2.t3562 (nat_lit 8150592) (nat_lit 3400442353) (nat_lit 0) D2M8K2.t3563 from rfl, allE_node, rows3562, irow3554, rows3563]
  all_goals rfl

theorem atot3554 : totK PD2M8K2 D2M8K2.u3554 = [0, 222037156412, 789274957301, 611422322017, 83306070088, 1138244013, 0, 0] := by
  rw [show D2M8K2.u3554 = KTree.node D2M8K2.t3562 (nat_lit 8150592) (nat_lit 3400442353) (nat_lit 0) D2M8K2.t3563 from rfl, totK_node, tot3562, tot3563]
  decide +kernel

theorem arows3556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3556 = true := by
  rw [show D2M8K2.u3556 = KTree.node D2M8K2.t3564 (nat_lit 8153217) (nat_lit 1795495423) (nat_lit 0) D2M8K2.t3565 from rfl, allE_node, rows3564, irow3556, rows3565]
  all_goals rfl

theorem atot3556 : totK PD2M8K2 D2M8K2.u3556 = [0, 266949237983, 870161252935, 606912068893, 59313016744, 0, 0, 0] := by
  rw [show D2M8K2.u3556 = KTree.node D2M8K2.t3564 (nat_lit 8153217) (nat_lit 1795495423) (nat_lit 0) D2M8K2.t3565 from rfl, totK_node, tot3564, tot3565]
  decide +kernel

theorem arows3557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3557 = true := by
  rw [show D2M8K2.u3557 = KTree.node D2M8K2.t3566 (nat_lit 8156224) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t3567 from rfl, allE_node, rows3566, irow3557, rows3567]
  all_goals rfl

theorem atot3557 : totK PD2M8K2 D2M8K2.u3557 = [0, 387608832282, 952911804868, 446846134814, 23336331855, 0, 0, 0] := by
  rw [show D2M8K2.u3557 = KTree.node D2M8K2.t3566 (nat_lit 8156224) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t3567 from rfl, totK_node, tot3566, tot3567]
  decide +kernel

theorem arows3561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3561 = true := by
  rw [show D2M8K2.u3561 = KTree.node D2M8K2.t3568 (nat_lit 8157744) (nat_lit 3651535765) (nat_lit 0) D2M8K2.t3569 from rfl, allE_node, rows3568, irow3561, rows3569]
  all_goals rfl

theorem atot3561 : totK PD2M8K2 D2M8K2.u3561 = [0, 356369995543, 940028653969, 454404705850, 25790587952, 0, 0, 0] := by
  rw [show D2M8K2.u3561 = KTree.node D2M8K2.t3568 (nat_lit 8157744) (nat_lit 3651535765) (nat_lit 0) D2M8K2.t3569 from rfl, totK_node, tot3568, tot3569]
  decide +kernel

theorem arows3562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3562 = true := by
  rw [show D2M8K2.u3562 = KTree.node D2M8K2.t3570 (nat_lit 8161013) (nat_lit 2163562762) (nat_lit 0) D2M8K2.t3571 from rfl, allE_node, rows3570, irow3562, rows3571]
  all_goals rfl

theorem atot3562 : totK PD2M8K2 D2M8K2.u3562 = [0, 386885942537, 952589333623, 434742973903, 18931416259, 0, 0, 0] := by
  rw [show D2M8K2.u3562 = KTree.node D2M8K2.t3570 (nat_lit 8161013) (nat_lit 2163562762) (nat_lit 0) D2M8K2.t3571 from rfl, totK_node, tot3570, tot3571]
  decide +kernel

theorem arows3564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3564 = true := by
  rw [show D2M8K2.u3564 = KTree.node D2M8K2.t3572 (nat_lit 8164030) (nat_lit 3601078835) (nat_lit 0) D2M8K2.t3573 from rfl, allE_node, rows3572, irow3564, rows3573]
  all_goals rfl

theorem atot3564 : totK PD2M8K2 D2M8K2.u3564 = [0, 301105318280, 896319079683, 548507116153, 47065631173, 0, 0, 0] := by
  rw [show D2M8K2.u3564 = KTree.node D2M8K2.t3572 (nat_lit 8164030) (nat_lit 3601078835) (nat_lit 0) D2M8K2.t3573 from rfl, totK_node, tot3572, tot3573]
  decide +kernel

theorem arows3565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3565 = true := by
  rw [show D2M8K2.u3565 = KTree.node D2M8K2.t3574 (nat_lit 8165993) (nat_lit 1651933922) (nat_lit 0) D2M8K2.t3575 from rfl, allE_node, rows3574, irow3565, rows3575]
  all_goals rfl

theorem atot3565 : totK PD2M8K2 D2M8K2.u3565 = [0, 155865311620, 676814592232, 742985684006, 177774635135, 4977114383, 0, 0] := by
  rw [show D2M8K2.u3565 = KTree.node D2M8K2.t3574 (nat_lit 8165993) (nat_lit 1651933922) (nat_lit 0) D2M8K2.t3575 from rfl, totK_node, tot3574, tot3575]
  decide +kernel

theorem arows3568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3568 = true := by
  rw [show D2M8K2.u3568 = KTree.node D2M8K2.t3576 (nat_lit 8212706) (nat_lit 3745630578) (nat_lit 0) D2M8K2.t3577 from rfl, allE_node, rows3576, irow3568, rows3577]
  all_goals rfl

theorem atot3568 : totK PD2M8K2 D2M8K2.u3568 = [0, 261129553261, 840662366053, 586655944435, 79947656534, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3568 = KTree.node D2M8K2.t3576 (nat_lit 8212706) (nat_lit 3745630578) (nat_lit 0) D2M8K2.t3577 from rfl, totK_node, tot3576, tot3577]
  decide +kernel

theorem arows3569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3569 = true := by
  rw [show D2M8K2.u3569 = KTree.node D2M8K2.t3578 (nat_lit 8214703) (nat_lit 2414986276) (nat_lit 0) D2M8K2.t3579 from rfl, allE_node, rows3578, irow3569, rows3579]
  all_goals rfl

theorem atot3569 : totK PD2M8K2 D2M8K2.u3569 = [0, 180339226645, 754166904822, 766198905895, 103466916747, 0, 0, 0] := by
  rw [show D2M8K2.u3569 = KTree.node D2M8K2.t3578 (nat_lit 8214703) (nat_lit 2414986276) (nat_lit 0) D2M8K2.t3579 from rfl, totK_node, tot3578, tot3579]
  decide +kernel

theorem arows3571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3571 = true := by
  rw [show D2M8K2.u3571 = KTree.node D2M8K2.t3580 (nat_lit 8219857) (nat_lit 1487015166) (nat_lit 0) D2M8K2.t3581 from rfl, allE_node, rows3580, irow3571, rows3581]
  all_goals rfl

theorem atot3571 : totK PD2M8K2 D2M8K2.u3571 = [0, 216360622852, 778725398717, 682079953896, 99402936601, 1164319620, 0, 0] := by
  rw [show D2M8K2.u3571 = KTree.node D2M8K2.t3580 (nat_lit 8219857) (nat_lit 1487015166) (nat_lit 0) D2M8K2.t3581 from rfl, totK_node, tot3580, tot3581]
  decide +kernel

theorem arows3572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3572 = true := by
  rw [show D2M8K2.u3572 = KTree.node D2M8K2.t3582 (nat_lit 8221667) (nat_lit 2985155367) (nat_lit 0) D2M8K2.t3583 from rfl, allE_node, rows3582, irow3572, rows3583]
  all_goals rfl

theorem atot3572 : totK PD2M8K2 D2M8K2.u3572 = [0, 201689224253, 665895265116, 703094130310, 192355809579, 11819130176, 0, 0] := by
  rw [show D2M8K2.u3572 = KTree.node D2M8K2.t3582 (nat_lit 8221667) (nat_lit 2985155367) (nat_lit 0) D2M8K2.t3583 from rfl, totK_node, tot3582, tot3583]
  decide +kernel

theorem arows3581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3581 = true := by
  rw [show D2M8K2.u3581 = KTree.node D2M8K2.t3584 (nat_lit 8223390) (nat_lit 3937483510) (nat_lit 0) D2M8K2.t3585 from rfl, allE_node, rows3584, irow3581, rows3585]
  all_goals rfl

theorem atot3581 : totK PD2M8K2 D2M8K2.u3581 = [0, 193564783760, 769375022309, 712723433268, 110073554334, 1198073392, 0, 0] := by
  rw [show D2M8K2.u3581 = KTree.node D2M8K2.t3584 (nat_lit 8223390) (nat_lit 3937483510) (nat_lit 0) D2M8K2.t3585 from rfl, totK_node, tot3584, tot3585]
  decide +kernel

theorem arows3582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3582 = true := by
  rw [show D2M8K2.u3582 = KTree.node D2M8K2.t3586 (nat_lit 8225296) (nat_lit 3371086046) (nat_lit 0) D2M8K2.t3587 from rfl, allE_node, rows3586, irow3582, rows3587]
  all_goals rfl

theorem atot3582 : totK PD2M8K2 D2M8K2.u3582 = [0, 212179334356, 671786592279, 679250010917, 193709496846, 11986244008, 0, 0] := by
  rw [show D2M8K2.u3582 = KTree.node D2M8K2.t3586 (nat_lit 8225296) (nat_lit 3371086046) (nat_lit 0) D2M8K2.t3587 from rfl, totK_node, tot3586, tot3587]
  decide +kernel

theorem arows3584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3584 = true := by
  rw [show D2M8K2.u3584 = KTree.node D2M8K2.t3588 (nat_lit 8226517) (nat_lit 1250220224) (nat_lit 0) D2M8K2.t3589 from rfl, allE_node, rows3588, irow3584, rows3589]
  all_goals rfl

theorem atot3584 : totK PD2M8K2 D2M8K2.u3584 = [0, 208161238117, 776624974962, 688876373534, 100558825676, 1096505104, 0, 0] := by
  rw [show D2M8K2.u3584 = KTree.node D2M8K2.t3588 (nat_lit 8226517) (nat_lit 1250220224) (nat_lit 0) D2M8K2.t3589 from rfl, totK_node, tot3588, tot3589]
  decide +kernel

theorem arows3585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3585 = true := by
  rw [show D2M8K2.u3585 = KTree.node D2M8K2.t3590 (nat_lit 8232275) (nat_lit 2861354393) (nat_lit 0) D2M8K2.t3591 from rfl, allE_node, rows3590, irow3585, rows3591]
  all_goals rfl

theorem atot3585 : totK PD2M8K2 D2M8K2.u3585 = [0, 0, 475457036772, 972683912878, 307231849421, 13436758262, 0, 0] := by
  rw [show D2M8K2.u3585 = KTree.node D2M8K2.t3590 (nat_lit 8232275) (nat_lit 2861354393) (nat_lit 0) D2M8K2.t3591 from rfl, totK_node, tot3590, tot3591]
  decide +kernel

theorem arows3588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3588 = true := by
  rw [show D2M8K2.u3588 = KTree.node D2M8K2.t3592 (nat_lit 8233855) (nat_lit 2310587572) (nat_lit 0) D2M8K2.t3593 from rfl, allE_node, rows3592, irow3588, rows3593]
  all_goals rfl

theorem atot3588 : totK PD2M8K2 D2M8K2.u3588 = [0, 0, 155570583904, 785229624787, 654021940534, 91143837986, 1209030869, 0] := by
  rw [show D2M8K2.u3588 = KTree.node D2M8K2.t3592 (nat_lit 8233855) (nat_lit 2310587572) (nat_lit 0) D2M8K2.t3593 from rfl, totK_node, tot3592, tot3593]
  decide +kernel

theorem arows3589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3589 = true := by
  rw [show D2M8K2.u3589 = KTree.node D2M8K2.t3594 (nat_lit 8239730) (nat_lit 4030184258) (nat_lit 0) D2M8K2.t3595 from rfl, allE_node, rows3594, irow3589, rows3595]
  all_goals rfl

theorem atot3589 : totK PD2M8K2 D2M8K2.u3589 = [0, 0, 392866326747, 947896097355, 392595479775, 22373439350, 0, 0] := by
  rw [show D2M8K2.u3589 = KTree.node D2M8K2.t3594 (nat_lit 8239730) (nat_lit 4030184258) (nat_lit 0) D2M8K2.t3595 from rfl, totK_node, tot3594, tot3595]
  decide +kernel

theorem arows3591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3591 = true := by
  rw [show D2M8K2.u3591 = KTree.node D2M8K2.t3596 (nat_lit 8243594) (nat_lit 4051115475) (nat_lit 0) D2M8K2.t3597 from rfl, allE_node, rows3596, irow3591, rows3597]
  all_goals rfl

theorem atot3591 : totK PD2M8K2 D2M8K2.u3591 = [0, 0, 465601443337, 980260368102, 320382328137, 13622890437, 0, 0] := by
  rw [show D2M8K2.u3591 = KTree.node D2M8K2.t3596 (nat_lit 8243594) (nat_lit 4051115475) (nat_lit 0) D2M8K2.t3597 from rfl, totK_node, tot3596, tot3597]
  decide +kernel

theorem arows3592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3592 = true := by
  rw [show D2M8K2.u3592 = KTree.node D2M8K2.t3598 (nat_lit 8246805) (nat_lit 1459528500) (nat_lit 0) D2M8K2.t3599 from rfl, allE_node, rows3598, irow3592, rows3599]
  all_goals rfl

theorem atot3592 : totK PD2M8K2 D2M8K2.u3592 = [0, 0, 351034962175, 952164211834, 414931323640, 21592980163, 0, 0] := by
  rw [show D2M8K2.u3592 = KTree.node D2M8K2.t3598 (nat_lit 8246805) (nat_lit 1459528500) (nat_lit 0) D2M8K2.t3599 from rfl, totK_node, tot3598, tot3599]
  decide +kernel

end QECKChecks.D2M8K2
