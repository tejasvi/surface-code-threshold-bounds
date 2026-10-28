import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A1

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows2396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2396 = true := by
  rw [show A10K2.u2396 = KTree.node A10K2.t2400 (nat_lit 41498004) (nat_lit 9123488976) (nat_lit 0) A10K2.t2401 from rfl, allE_node, rows2400, irow2396, rows2401]
  all_goals rfl

theorem atot2396 : totK PA10K2 A10K2.u2396 = [0, 296440474885, 1928478604325, 4015613533599, 2891087706964, 594904278021, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2396 = KTree.node A10K2.t2400 (nat_lit 41498004) (nat_lit 9123488976) (nat_lit 0) A10K2.t2401 from rfl, totK_node, tot2400, tot2401]
  decide +kernel

theorem arows2397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2397 = true := by
  rw [show A10K2.u2397 = KTree.node A10K2.t2402 (nat_lit 41503041) (nat_lit 9174369477) (nat_lit 0) A10K2.t2403 from rfl, allE_node, rows2402, irow2397, rows2403]
  all_goals rfl

theorem atot2397 : totK PA10K2 A10K2.u2397 = [0, 554851874388, 2689151089695, 4132276516196, 1983908165877, 192329549857, 0, 0, 0, 0] := by
  rw [show A10K2.u2397 = KTree.node A10K2.t2402 (nat_lit 41503041) (nat_lit 9174369477) (nat_lit 0) A10K2.t2403 from rfl, totK_node, tot2402, tot2403]
  decide +kernel

theorem arows2399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2399 = true := by
  rw [show A10K2.u2399 = KTree.node A10K2.t2404 (nat_lit 41510841) (nat_lit 6061498254) (nat_lit 0) A10K2.t2405 from rfl, allE_node, rows2404, irow2399, rows2405]
  all_goals rfl

theorem atot2399 : totK PA10K2 A10K2.u2399 = [0, 815136327260, 3199081684325, 4007124910213, 1799598477521, 297096316749, 12567399571, 0, 0, 0] := by
  rw [show A10K2.u2399 = KTree.node A10K2.t2404 (nat_lit 41510841) (nat_lit 6061498254) (nat_lit 0) A10K2.t2405 from rfl, totK_node, tot2404, tot2405]
  decide +kernel

theorem arows2400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2400 = true := by
  rw [show A10K2.u2400 = KTree.node A10K2.t2406 (nat_lit 41516606) (nat_lit 15987297147) (nat_lit 0) A10K2.t2407 from rfl, allE_node, rows2406, irow2400, rows2407]
  all_goals rfl

theorem atot2400 : totK PA10K2 A10K2.u2400 = [0, 0, 1036405264889, 3685335511108, 3944769924740, 1218630186090, 82605879954, 0, 0, 0] := by
  rw [show A10K2.u2400 = KTree.node A10K2.t2406 (nat_lit 41516606) (nat_lit 15987297147) (nat_lit 0) A10K2.t2407 from rfl, totK_node, tot2406, tot2407]
  decide +kernel

theorem arows2403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2403 = true := by
  rw [show A10K2.u2403 = KTree.node A10K2.t2408 (nat_lit 41530515) (nat_lit 11041069466) (nat_lit 0) A10K2.t2409 from rfl, allE_node, rows2408, irow2403, rows2409]
  all_goals rfl

theorem atot2403 : totK PA10K2 A10K2.u2403 = [0, 0, 421128020257, 2288126842203, 3933598133685, 2377614260071, 463536891027, 25565504801, 0, 0] := by
  rw [show A10K2.u2403 = KTree.node A10K2.t2408 (nat_lit 41530515) (nat_lit 11041069466) (nat_lit 0) A10K2.t2409 from rfl, totK_node, tot2408, tot2409]
  decide +kernel

theorem arows2404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2404 = true := by
  rw [show A10K2.u2404 = KTree.node A10K2.t2410 (nat_lit 41535639) (nat_lit 10902241593) (nat_lit 0) A10K2.t2411 from rfl, allE_node, rows2410, irow2404, rows2411]
  all_goals rfl

theorem atot2404 : totK PA10K2 A10K2.u2404 = [0, 0, 554059125218, 2857485425597, 4167167183194, 1758478890375, 204076055981, 5517381808, 0, 0] := by
  rw [show A10K2.u2404 = KTree.node A10K2.t2410 (nat_lit 41535639) (nat_lit 10902241593) (nat_lit 0) A10K2.t2411 from rfl, totK_node, tot2410, tot2411]
  decide +kernel

theorem arows2406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2406 = true := by
  rw [show A10K2.u2406 = KTree.node A10K2.t2412 (nat_lit 41543392) (nat_lit 3141633841) (nat_lit 0) A10K2.t2413 from rfl, allE_node, rows2412, irow2406, rows2413]
  all_goals rfl

theorem atot2406 : totK PA10K2 A10K2.u2406 = [0, 143089868794, 1138822313347, 3165749953914, 3650082420171, 1609591346160, 212015112828, 5885702948, 0, 0] := by
  rw [show A10K2.u2406 = KTree.node A10K2.t2412 (nat_lit 41543392) (nat_lit 3141633841) (nat_lit 0) A10K2.t2413 from rfl, totK_node, tot2412, tot2413]
  decide +kernel

theorem arows2407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2407 = true := by
  rw [show A10K2.u2407 = KTree.node A10K2.t2414 (nat_lit 41619328) (nat_lit 15055867731) (nat_lit 0) A10K2.t2415 from rfl, allE_node, rows2414, irow2407, rows2415]
  all_goals rfl

theorem atot2407 : totK PA10K2 A10K2.u2407 = [0, 482646624243, 2604444973913, 4274043623312, 2319455996341, 380544889701, 12473006693, 0, 0, 0] := by
  rw [show A10K2.u2407 = KTree.node A10K2.t2414 (nat_lit 41619328) (nat_lit 15055867731) (nat_lit 0) A10K2.t2415 from rfl, totK_node, tot2414, tot2415]
  decide +kernel

theorem arows2411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2411 = true := by
  rw [show A10K2.u2411 = KTree.node A10K2.t2416 (nat_lit 41626469) (nat_lit 7170390638) (nat_lit 0) A10K2.t2417 from rfl, allE_node, rows2416, irow2411, rows2417]
  all_goals rfl

theorem atot2411 : totK PA10K2 A10K2.u2411 = [0, 784243300034, 3179686153864, 4095664672146, 1738566544993, 156079328940, 0, 0, 0, 0] := by
  rw [show A10K2.u2411 = KTree.node A10K2.t2416 (nat_lit 41626469) (nat_lit 7170390638) (nat_lit 0) A10K2.t2417 from rfl, totK_node, tot2416, tot2417]
  decide +kernel

theorem arows2412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2412 = true := by
  rw [show A10K2.u2412 = KTree.node A10K2.t2418 (nat_lit 41639995) (nat_lit 5455790481) (nat_lit 0) A10K2.t2419 from rfl, allE_node, rows2418, irow2412, rows2419]
  all_goals rfl

theorem atot2412 : totK PA10K2 A10K2.u2412 = [0, 542937375368, 2431712035174, 3763839380714, 2396736996835, 551321673415, 31452269383, 0, 0, 0] := by
  rw [show A10K2.u2412 = KTree.node A10K2.t2418 (nat_lit 41639995) (nat_lit 5455790481) (nat_lit 0) A10K2.t2419 from rfl, totK_node, tot2418, tot2419]
  decide +kernel

theorem arows2414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2414 = true := by
  rw [show A10K2.u2414 = KTree.node A10K2.t2420 (nat_lit 41644486) (nat_lit 15671917983) (nat_lit 0) A10K2.t2421 from rfl, allE_node, rows2420, irow2414, rows2421]
  all_goals rfl

theorem atot2414 : totK PA10K2 A10K2.u2414 = [0, 330865856800, 2046769352859, 4136705162406, 2939273859374, 534445174802, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u2414 = KTree.node A10K2.t2420 (nat_lit 41644486) (nat_lit 15671917983) (nat_lit 0) A10K2.t2421 from rfl, totK_node, tot2420, tot2421]
  decide +kernel

theorem arows2415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2415 = true := by
  rw [show A10K2.u2415 = KTree.node A10K2.t2422 (nat_lit 41650233) (nat_lit 7278917638) (nat_lit 0) A10K2.t2423 from rfl, allE_node, rows2422, irow2415, rows2423]
  all_goals rfl

theorem atot2415 : totK PA10K2 A10K2.u2415 = [0, 0, 708764235281, 3158470756951, 4297125265346, 1734055061082, 131580336605, 0, 0, 0] := by
  rw [show A10K2.u2415 = KTree.node A10K2.t2422 (nat_lit 41650233) (nat_lit 7278917638) (nat_lit 0) A10K2.t2423 from rfl, totK_node, tot2422, tot2423]
  decide +kernel

theorem arows2418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2418 = true := by
  rw [show A10K2.u2418 = KTree.node A10K2.t2424 (nat_lit 41658070) (nat_lit 13666555834) (nat_lit 0) A10K2.t2425 from rfl, allE_node, rows2424, irow2418, rows2425]
  all_goals rfl

theorem atot2418 : totK PA10K2 A10K2.u2418 = [0, 0, 783233468008, 3123695784121, 3952180576333, 1783679820045, 243981064132, 6632180018, 0, 0] := by
  rw [show A10K2.u2418 = KTree.node A10K2.t2424 (nat_lit 41658070) (nat_lit 13666555834) (nat_lit 0) A10K2.t2425 from rfl, totK_node, tot2424, tot2425]
  decide +kernel

theorem arows2419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2419 = true := by
  rw [show A10K2.u2419 = KTree.node A10K2.t2426 (nat_lit 41663672) (nat_lit 10897718391) (nat_lit 0) A10K2.t2427 from rfl, allE_node, rows2426, irow2419, rows2427]
  all_goals rfl

theorem atot2419 : totK PA10K2 A10K2.u2419 = [0, 0, 542492176839, 2562454406730, 4038994689676, 2324917076781, 339160959142, 7047025452, 0, 0] := by
  rw [show A10K2.u2419 = KTree.node A10K2.t2426 (nat_lit 41663672) (nat_lit 10897718391) (nat_lit 0) A10K2.t2427 from rfl, totK_node, tot2426, tot2427]
  decide +kernel

theorem arows2421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2421 = true := by
  rw [show A10K2.u2421 = KTree.node A10K2.t2428 (nat_lit 41676804) (nat_lit 10494727983) (nat_lit 0) A10K2.t2429 from rfl, allE_node, rows2428, irow2421, rows2429]
  all_goals rfl

theorem atot2421 : totK PA10K2 A10K2.u2421 = [0, 0, 330021797788, 2130498645652, 4187744136451, 2729799482319, 457197410105, 12224107035, 0, 0] := by
  rw [show A10K2.u2421 = KTree.node A10K2.t2428 (nat_lit 41676804) (nat_lit 10494727983) (nat_lit 0) A10K2.t2429 from rfl, totK_node, tot2428, tot2429]
  decide +kernel

theorem arows2422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2422 = true := by
  rw [show A10K2.u2422 = KTree.node A10K2.t2430 (nat_lit 41943543) (nat_lit 14756295669) (nat_lit 0) A10K2.t2431 from rfl, allE_node, rows2430, irow2422, rows2431]
  all_goals rfl

theorem atot2422 : totK PA10K2 A10K2.u2422 = [796021182214, 2610860683949, 2441523887130, 869144423176, 1110852024914, 1354449336259, 522441368230, 48886019071, 0, 0] := by
  rw [show A10K2.u2422 = KTree.node A10K2.t2430 (nat_lit 41943543) (nat_lit 14756295669) (nat_lit 0) A10K2.t2431 from rfl, totK_node, tot2430, tot2431]
  decide +kernel

theorem arows2429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2429 = true := by
  rw [show A10K2.u2429 = KTree.node A10K2.t2432 (nat_lit 41949188) (nat_lit 12641517020) (nat_lit 0) A10K2.t2433 from rfl, allE_node, rows2432, irow2429, rows2433]
  all_goals rfl

theorem atot2429 : totK PA10K2 A10K2.u2429 = [257964219154, 1856685338961, 3980305125768, 2908058462978, 592238963306, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2429 = KTree.node A10K2.t2432 (nat_lit 41949188) (nat_lit 12641517020) (nat_lit 0) A10K2.t2433 from rfl, totK_node, tot2432, tot2433]
  decide +kernel

theorem arows2430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2430 = true := by
  rw [show A10K2.u2430 = KTree.node A10K2.t2434 (nat_lit 41961756) (nat_lit 12251271232) (nat_lit 0) A10K2.t2435 from rfl, allE_node, rows2434, irow2430, rows2435]
  all_goals rfl

theorem atot2430 : totK PA10K2 A10K2.u2430 = [517023842798, 2781232468774, 4215729950603, 1757549158386, 153363476219, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2430 = KTree.node A10K2.t2434 (nat_lit 41961756) (nat_lit 12251271232) (nat_lit 0) A10K2.t2435 from rfl, totK_node, tot2434, tot2435]
  decide +kernel

theorem arows2432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2432 = true := by
  rw [show A10K2.u2432 = KTree.node A10K2.t2436 (nat_lit 41970757) (nat_lit 5270838583) (nat_lit 0) A10K2.t2437 from rfl, allE_node, rows2436, irow2432, rows2437]
  all_goals rfl

theorem atot2432 : totK PA10K2 A10K2.u2432 = [593902697676, 2586840774549, 3959654297068, 2376329277647, 432443601875, 13207830636, 0, 0, 0, 0] := by
  rw [show A10K2.u2432 = KTree.node A10K2.t2436 (nat_lit 41970757) (nat_lit 5270838583) (nat_lit 0) A10K2.t2437 from rfl, totK_node, tot2436, tot2437]
  decide +kernel

theorem arows2433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2433 = true := by
  rw [show A10K2.u2433 = KTree.node A10K2.t2438 (nat_lit 41976242) (nat_lit 11559200774) (nat_lit 0) A10K2.t2439 from rfl, allE_node, rows2438, irow2433, rows2439]
  all_goals rfl

theorem atot2433 : totK PA10K2 A10K2.u2433 = [0, 1022360188027, 3732224961779, 3910287033447, 1113653508125, 80269645312, 0, 0, 0, 0] := by
  rw [show A10K2.u2433 = KTree.node A10K2.t2438 (nat_lit 41976242) (nat_lit 11559200774) (nat_lit 0) A10K2.t2439 from rfl, totK_node, tot2438, tot2439]
  decide +kernel

theorem arows2436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2436 = true := by
  rw [show A10K2.u2436 = KTree.node A10K2.t2440 (nat_lit 41980855) (nat_lit 13252002709) (nat_lit 0) A10K2.t2441 from rfl, allE_node, rows2440, irow2436, rows2441]
  all_goals rfl

theorem atot2436 : totK PA10K2 A10K2.u2436 = [0, 362236152074, 2000222314150, 3881749458073, 2635676769280, 549802920840, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u2436 = KTree.node A10K2.t2440 (nat_lit 41980855) (nat_lit 13252002709) (nat_lit 0) A10K2.t2441 from rfl, totK_node, tot2440, tot2441]
  decide +kernel

theorem arows2437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2437 = true := by
  rw [show A10K2.u2437 = KTree.node A10K2.t2442 (nat_lit 41994604) (nat_lit 12782193965) (nat_lit 0) A10K2.t2443 from rfl, allE_node, rows2442, irow2437, rows2443]
  all_goals rfl

theorem atot2437 : totK PA10K2 A10K2.u2437 = [0, 491424974411, 2818287309653, 4309631591912, 1620475933102, 109248714315, 0, 0, 0, 0] := by
  rw [show A10K2.u2437 = KTree.node A10K2.t2442 (nat_lit 41994604) (nat_lit 12782193965) (nat_lit 0) A10K2.t2443 from rfl, totK_node, tot2442, tot2443]
  decide +kernel

theorem arows2439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2439 = true := by
  rw [show A10K2.u2439 = KTree.node A10K2.t2444 (nat_lit 42003912) (nat_lit 13815362515) (nat_lit 0) A10K2.t2445 from rfl, allE_node, rows2444, irow2439, rows2445]
  all_goals rfl

theorem atot2439 : totK PA10K2 A10K2.u2439 = [342125450654, 1757452930239, 3377233095188, 2990757222181, 1249032958195, 191964764713, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u2439 = KTree.node A10K2.t2444 (nat_lit 42003912) (nat_lit 13815362515) (nat_lit 0) A10K2.t2445 from rfl, totK_node, tot2444, tot2445]
  decide +kernel

theorem arows2440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2440 = true := by
  rw [show A10K2.u2440 = KTree.node A10K2.t2446 (nat_lit 42078281) (nat_lit 9594707706) (nat_lit 0) A10K2.t2447 from rfl, allE_node, rows2446, irow2440, rows2447]
  all_goals rfl

theorem atot2440 : totK PA10K2 A10K2.u2440 = [410979354435, 2205314114003, 3886304371398, 2538388549651, 494590452291, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u2440 = KTree.node A10K2.t2446 (nat_lit 42078281) (nat_lit 9594707706) (nat_lit 0) A10K2.t2447 from rfl, totK_node, tot2446, tot2447]
  decide +kernel

theorem arows2444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2444 = true := by
  rw [show A10K2.u2444 = KTree.node A10K2.t2448 (nat_lit 42084608) (nat_lit 13190885984) (nat_lit 0) A10K2.t2449 from rfl, allE_node, rows2448, irow2444, rows2449]
  all_goals rfl

theorem atot2444 : totK PA10K2 A10K2.u2444 = [562074292173, 2648509003575, 3903660085104, 2127474322852, 478442077023, 31195026185, 0, 0, 0, 0] := by
  rw [show A10K2.u2444 = KTree.node A10K2.t2448 (nat_lit 42084608) (nat_lit 13190885984) (nat_lit 0) A10K2.t2449 from rfl, totK_node, tot2448, tot2449]
  decide +kernel

theorem arows2445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2445 = true := by
  rw [show A10K2.u2445 = KTree.node A10K2.t2450 (nat_lit 42091681) (nat_lit 7159949456) (nat_lit 0) A10K2.t2451 from rfl, allE_node, rows2450, irow2445, rows2451]
  all_goals rfl

theorem atot2445 : totK PA10K2 A10K2.u2445 = [818556818924, 3081053760619, 3687455656888, 1626730697548, 222989547628, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u2445 = KTree.node A10K2.t2450 (nat_lit 42091681) (nat_lit 7159949456) (nat_lit 0) A10K2.t2451 from rfl, totK_node, tot2450, tot2451]
  decide +kernel

theorem arows2447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2447 = true := by
  rw [show A10K2.u2447 = KTree.node A10K2.t2452 (nat_lit 42097164) (nat_lit 11521543738) (nat_lit 0) A10K2.t2453 from rfl, allE_node, rows2452, irow2447, rows2453]
  all_goals rfl

theorem atot2447 : totK PA10K2 A10K2.u2447 = [0, 1328150959023, 4162651632363, 3272695995015, 665028935457, 31987755669, 0, 0, 0, 0] := by
  rw [show A10K2.u2447 = KTree.node A10K2.t2452 (nat_lit 42097164) (nat_lit 11521543738) (nat_lit 0) A10K2.t2453 from rfl, totK_node, tot2452, tot2453]
  decide +kernel

theorem arows2448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2448 = true := by
  rw [show A10K2.u2448 = KTree.node A10K2.t2454 (nat_lit 42116607) (nat_lit 12677777258) (nat_lit 0) A10K2.t2455 from rfl, allE_node, rows2454, irow2448, rows2455]
  all_goals rfl

theorem atot2448 : totK PA10K2 A10K2.u2448 = [0, 1063323317173, 3774861401064, 3822025357290, 998784145715, 45620856191, 0, 0, 0, 0] := by
  rw [show A10K2.u2448 = KTree.node A10K2.t2454 (nat_lit 42116607) (nat_lit 12677777258) (nat_lit 0) A10K2.t2455 from rfl, totK_node, tot2454, tot2455]
  decide +kernel

theorem arows2451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2451 = true := by
  rw [show A10K2.u2451 = KTree.node A10K2.t2456 (nat_lit 42125469) (nat_lit 6266801282) (nat_lit 0) A10K2.t2457 from rfl, allE_node, rows2456, irow2451, rows2457]
  all_goals rfl

theorem atot2451 : totK PA10K2 A10K2.u2451 = [0, 604584213950, 3040407963124, 4169333054563, 1391230309603, 108770940573, 0, 0, 0, 0] := by
  rw [show A10K2.u2451 = KTree.node A10K2.t2456 (nat_lit 42125469) (nat_lit 6266801282) (nat_lit 0) A10K2.t2457 from rfl, totK_node, tot2456, tot2457]
  decide +kernel

theorem arows2452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2452 = true := by
  rw [show A10K2.u2452 = KTree.node A10K2.t2458 (nat_lit 42205980) (nat_lit 10746809945) (nat_lit 0) A10K2.t2459 from rfl, allE_node, rows2458, irow2452, rows2459]
  all_goals rfl

theorem atot2452 : totK PA10K2 A10K2.u2452 = [0, 838183272892, 3108276989101, 3745335453169, 1566999315746, 239193241337, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2452 = KTree.node A10K2.t2458 (nat_lit 42205980) (nat_lit 10746809945) (nat_lit 0) A10K2.t2459 from rfl, totK_node, tot2458, tot2459]
  decide +kernel

theorem arows2454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2454 = true := by
  rw [show A10K2.u2454 = KTree.node A10K2.t2460 (nat_lit 42211584) (nat_lit 14397781664) (nat_lit 0) A10K2.t2461 from rfl, allE_node, rows2460, irow2454, rows2461]
  all_goals rfl

theorem atot2454 : totK PA10K2 A10K2.u2454 = [0, 290159622867, 1860158776345, 3915366404705, 2834868949907, 577973070648, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2454 = KTree.node A10K2.t2460 (nat_lit 42211584) (nat_lit 14397781664) (nat_lit 0) A10K2.t2461 from rfl, totK_node, tot2460, tot2461]
  decide +kernel

theorem arows2455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2455 = true := by
  rw [show A10K2.u2455 = KTree.node A10K2.t2462 (nat_lit 42224418) (nat_lit 12605557247) (nat_lit 0) A10K2.t2463 from rfl, allE_node, rows2462, irow2455, rows2463]
  all_goals rfl

theorem atot2455 : totK PA10K2 A10K2.u2455 = [0, 454845815706, 2560711841861, 4199755191405, 1883032179986, 146796540094, 0, 0, 0, 0] := by
  rw [show A10K2.u2455 = KTree.node A10K2.t2462 (nat_lit 42224418) (nat_lit 12605557247) (nat_lit 0) A10K2.t2463 from rfl, totK_node, tot2462, tot2463]
  decide +kernel

theorem arows2460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2460 = true := by
  rw [show A10K2.u2460 = KTree.node A10K2.t2464 (nat_lit 42233358) (nat_lit 14635108191) (nat_lit 0) A10K2.t2465 from rfl, allE_node, rows2464, irow2460, rows2465]
  all_goals rfl

theorem atot2460 : totK PA10K2 A10K2.u2460 = [0, 592958361815, 2652949811964, 4050786034974, 2389882392363, 409783430258, 12558367923, 0, 0, 0] := by
  rw [show A10K2.u2460 = KTree.node A10K2.t2464 (nat_lit 42233358) (nat_lit 14635108191) (nat_lit 0) A10K2.t2465 from rfl, totK_node, tot2464, tot2465]
  decide +kernel

theorem arows2461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2461 = true := by
  rw [show A10K2.u2461 = KTree.node A10K2.t2466 (nat_lit 42238866) (nat_lit 5360138338) (nat_lit 0) A10K2.t2467 from rfl, allE_node, rows2466, irow2461, rows2467]
  all_goals rfl

theorem atot2461 : totK PA10K2 A10K2.u2461 = [0, 0, 949591693157, 3630040239874, 3895790469524, 1093781628313, 66195545706, 0, 0, 0] := by
  rw [show A10K2.u2461 = KTree.node A10K2.t2466 (nat_lit 42238866) (nat_lit 5360138338) (nat_lit 0) A10K2.t2467 from rfl, totK_node, tot2466, tot2467]
  decide +kernel

theorem arows2463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2463 = true := by
  rw [show A10K2.u2463 = KTree.node A10K2.t2468 (nat_lit 42244645) (nat_lit 7034150879) (nat_lit 0) A10K2.t2469 from rfl, allE_node, rows2468, irow2463, rows2469]
  all_goals rfl

theorem atot2463 : totK PA10K2 A10K2.u2463 = [0, 0, 314393602148, 1871877498325, 3832583592189, 2653987796950, 563351753241, 30605747850, 0, 0] := by
  rw [show A10K2.u2463 = KTree.node A10K2.t2468 (nat_lit 42244645) (nat_lit 7034150879) (nat_lit 0) A10K2.t2469 from rfl, totK_node, tot2468, tot2469]
  decide +kernel

theorem arows2464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2464 = true := by
  rw [show A10K2.u2464 = KTree.node A10K2.t2470 (nat_lit 42258709) (nat_lit 6609276885) (nat_lit 0) A10K2.t2471 from rfl, allE_node, rows2470, irow2464, rows2471]
  all_goals rfl

theorem atot2464 : totK PA10K2 A10K2.u2464 = [0, 0, 615127702449, 2820916898487, 3806314461832, 1570128790300, 202021134378, 5528811039, 0, 0] := by
  rw [show A10K2.u2464 = KTree.node A10K2.t2470 (nat_lit 42258709) (nat_lit 6609276885) (nat_lit 0) A10K2.t2471 from rfl, totK_node, tot2470, tot2471]
  decide +kernel

theorem arows2467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2467 = true := by
  rw [show A10K2.u2467 = KTree.node A10K2.t2472 (nat_lit 42336353) (nat_lit 10022573639) (nat_lit 0) A10K2.t2473 from rfl, allE_node, rows2472, irow2467, rows2473]
  all_goals rfl

theorem atot2467 : totK PA10K2 A10K2.u2467 = [0, 579499743383, 2497149561081, 3721199432659, 2466110015480, 607251225579, 43911449185, 0, 0, 0] := by
  rw [show A10K2.u2467 = KTree.node A10K2.t2472 (nat_lit 42336353) (nat_lit 10022573639) (nat_lit 0) A10K2.t2473 from rfl, totK_node, tot2472, tot2473]
  decide +kernel

theorem arows2468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2468 = true := by
  rw [show A10K2.u2468 = KTree.node A10K2.t2474 (nat_lit 42341228) (nat_lit 11004952698) (nat_lit 0) A10K2.t2475 from rfl, allE_node, rows2474, irow2468, rows2475]
  all_goals rfl

theorem atot2468 : totK PA10K2 A10K2.u2468 = [0, 435678917492, 2031266877172, 3814399323136, 2753982059304, 570533025695, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2468 = KTree.node A10K2.t2474 (nat_lit 42341228) (nat_lit 11004952698) (nat_lit 0) A10K2.t2475 from rfl, totK_node, tot2474, tot2475]
  decide +kernel

theorem arows2470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2470 = true := by
  rw [show A10K2.u2470 = KTree.node A10K2.t2476 (nat_lit 42349837) (nat_lit 5454674742) (nat_lit 0) A10K2.t2477 from rfl, allE_node, rows2476, irow2470, rows2477]
  all_goals rfl

theorem atot2470 : totK PA10K2 A10K2.u2470 = [0, 589033374884, 2789221286547, 4052951560096, 1909594143602, 234653363438, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u2470 = KTree.node A10K2.t2476 (nat_lit 42349837) (nat_lit 5454674742) (nat_lit 0) A10K2.t2477 from rfl, totK_node, tot2476, tot2477]
  decide +kernel

theorem arows2471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2471 = true := by
  rw [show A10K2.u2471 = KTree.node A10K2.t2478 (nat_lit 42354956) (nat_lit 12145468572) (nat_lit 0) A10K2.t2479 from rfl, allE_node, rows2478, irow2471, rows2479]
  all_goals rfl

theorem atot2471 : totK PA10K2 A10K2.u2471 = [0, 542356940553, 2797321434320, 4186188685551, 1689016694791, 137572876326, 0, 0, 0, 0] := by
  rw [show A10K2.u2471 = KTree.node A10K2.t2478 (nat_lit 42354956) (nat_lit 12145468572) (nat_lit 0) A10K2.t2479 from rfl, totK_node, tot2478, tot2479]
  decide +kernel

theorem arows2475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2475 = true := by
  rw [show A10K2.u2475 = KTree.node A10K2.t2480 (nat_lit 42369900) (nat_lit 11270927806) (nat_lit 0) A10K2.t2481 from rfl, allE_node, rows2480, irow2475, rows2481]
  all_goals rfl

theorem atot2475 : totK PA10K2 A10K2.u2475 = [0, 0, 1073175582326, 3770394461503, 3662306305353, 908819616557, 44905858284, 0, 0, 0] := by
  rw [show A10K2.u2475 = KTree.node A10K2.t2480 (nat_lit 42369900) (nat_lit 11270927806) (nat_lit 0) A10K2.t2481 from rfl, totK_node, tot2480, tot2481]
  decide +kernel

theorem arows2476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2476 = true := by
  rw [show A10K2.u2476 = KTree.node A10K2.t2482 (nat_lit 42385805) (nat_lit 5051781884) (nat_lit 0) A10K2.t2483 from rfl, allE_node, rows2482, irow2476, rows2483]
  all_goals rfl

theorem atot2476 : totK PA10K2 A10K2.u2476 = [0, 0, 1243721157798, 3980126489893, 3417937572363, 713268006733, 36877445968, 0, 0, 0] := by
  rw [show A10K2.u2476 = KTree.node A10K2.t2482 (nat_lit 42385805) (nat_lit 5051781884) (nat_lit 0) A10K2.t2483 from rfl, totK_node, tot2482, tot2483]
  decide +kernel

theorem arows2478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2478 = true := by
  rw [show A10K2.u2478 = KTree.node A10K2.t2484 (nat_lit 42391879) (nat_lit 4116412257) (nat_lit 0) A10K2.t2485 from rfl, allE_node, rows2484, irow2478, rows2485]
  all_goals rfl

theorem atot2478 : totK PA10K2 A10K2.u2478 = [482054232543, 1456573791262, 1411728573448, 1650072553564, 2761482992385, 1382595422472, 192289909650, 5676195732, 0, 0] := by
  rw [show A10K2.u2478 = KTree.node A10K2.t2484 (nat_lit 42391879) (nat_lit 4116412257) (nat_lit 0) A10K2.t2485 from rfl, totK_node, tot2484, tot2485]
  decide +kernel

theorem arows2479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2479 = true := by
  rw [show A10K2.u2479 = KTree.node A10K2.t2486 (nat_lit 42546333) (nat_lit 6111184690) (nat_lit 0) A10K2.t2487 from rfl, allE_node, rows2486, irow2479, rows2487]
  all_goals rfl

theorem atot2479 : totK PA10K2 A10K2.u2479 = [378150862450, 2266259758744, 4074784734883, 2536113358140, 472183664826, 25734533292, 0, 0, 0, 0] := by
  rw [show A10K2.u2479 = KTree.node A10K2.t2486 (nat_lit 42546333) (nat_lit 6111184690) (nat_lit 0) A10K2.t2487 from rfl, totK_node, tot2486, tot2487]
  decide +kernel

theorem arows2482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2482 = true := by
  rw [show A10K2.u2482 = KTree.node A10K2.t2488 (nat_lit 42550627) (nat_lit 9355842215) (nat_lit 0) A10K2.t2489 from rfl, allE_node, rows2488, irow2482, rows2489]
  all_goals rfl

theorem atot2482 : totK PA10K2 A10K2.u2482 = [742937934308, 3041776899629, 3816836910521, 1642500652719, 234421050524, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u2482 = KTree.node A10K2.t2488 (nat_lit 42550627) (nat_lit 9355842215) (nat_lit 0) A10K2.t2489 from rfl, totK_node, tot2488, tot2489]
  decide +kernel

theorem arows2483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2483 = true := by
  rw [show A10K2.u2483 = KTree.node A10K2.t2490 (nat_lit 42557847) (nat_lit 14568056812) (nat_lit 0) A10K2.t2491 from rfl, allE_node, rows2490, irow2483, rows2491]
  all_goals rfl

theorem atot2483 : totK PA10K2 A10K2.u2483 = [695123071544, 2843720437240, 4012522063582, 2021072354646, 280302480262, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2483 = KTree.node A10K2.t2490 (nat_lit 42557847) (nat_lit 14568056812) (nat_lit 0) A10K2.t2491 from rfl, totK_node, tot2490, tot2491]
  decide +kernel

theorem arows2485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2485 = true := by
  rw [show A10K2.u2485 = KTree.node A10K2.t2492 (nat_lit 42563370) (nat_lit 10194658962) (nat_lit 0) A10K2.t2493 from rfl, allE_node, rows2492, irow2485, rows2493]
  all_goals rfl

theorem atot2485 : totK PA10K2 A10K2.u2485 = [0, 1387678335524, 4284211664407, 3621831899203, 903072279837, 55252400496, 0, 0, 0, 0] := by
  rw [show A10K2.u2485 = KTree.node A10K2.t2492 (nat_lit 42563370) (nat_lit 10194658962) (nat_lit 0) A10K2.t2493 from rfl, totK_node, tot2492, tot2493]
  decide +kernel

theorem arows2486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2486 = true := by
  rw [show A10K2.u2486 = KTree.node A10K2.t2494 (nat_lit 42577285) (nat_lit 532621612) (nat_lit 0) A10K2.t2495 from rfl, allE_node, rows2494, irow2486, rows2495]
  all_goals rfl

theorem atot2486 : totK PA10K2 A10K2.u2486 = [0, 538210955376, 2667112740048, 4038670385489, 2027000390112, 379893934907, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u2486 = KTree.node A10K2.t2494 (nat_lit 42577285) (nat_lit 532621612) (nat_lit 0) A10K2.t2495 from rfl, totK_node, tot2494, tot2495]
  decide +kernel

theorem arows2492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2492 = true := by
  rw [show A10K2.u2492 = KTree.node A10K2.t2496 (nat_lit 42582563) (nat_lit 4755895041) (nat_lit 0) A10K2.t2497 from rfl, allE_node, rows2496, irow2492, rows2497]
  all_goals rfl

theorem atot2492 : totK PA10K2 A10K2.u2492 = [0, 742362137899, 2863215556057, 3751568520125, 1832954676621, 248504993387, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u2492 = KTree.node A10K2.t2496 (nat_lit 42582563) (nat_lit 4755895041) (nat_lit 0) A10K2.t2497 from rfl, totK_node, tot2496, tot2497]
  decide +kernel

theorem arows2493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2493 = true := by
  rw [show A10K2.u2493 = KTree.node A10K2.t2498 (nat_lit 42588446) (nat_lit 8519506326) (nat_lit 0) A10K2.t2499 from rfl, allE_node, rows2498, irow2493, rows2499]
  all_goals rfl

theorem atot2493 : totK PA10K2 A10K2.u2493 = [0, 399120657157, 2522905898176, 4289858118761, 2053206395330, 245194492484, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2493 = KTree.node A10K2.t2498 (nat_lit 42588446) (nat_lit 8519506326) (nat_lit 0) A10K2.t2499 from rfl, totK_node, tot2498, tot2499]
  decide +kernel

theorem arows2495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2495 = true := by
  rw [show A10K2.u2495 = KTree.node A10K2.t2500 (nat_lit 42598969) (nat_lit 7193401148) (nat_lit 0) A10K2.t2501 from rfl, allE_node, rows2500, irow2495, rows2501]
  all_goals rfl

theorem atot2495 : totK PA10K2 A10K2.u2495 = [516552094339, 2403605629230, 3725843396060, 2325047739212, 641366840200, 49652399959, 0, 0, 0, 0] := by
  rw [show A10K2.u2495 = KTree.node A10K2.t2500 (nat_lit 42598969) (nat_lit 7193401148) (nat_lit 0) A10K2.t2501 from rfl, totK_node, tot2500, tot2501]
  decide +kernel

theorem arows2496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2496 = true := by
  rw [show A10K2.u2496 = KTree.node A10K2.t2502 (nat_lit 42608054) (nat_lit 16278480976) (nat_lit 0) A10K2.t2503 from rfl, allE_node, rows2502, irow2496, rows2503]
  all_goals rfl

theorem atot2496 : totK PA10K2 A10K2.u2496 = [707957226188, 2728924508599, 3582825931480, 2001302306725, 452214274084, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2496 = KTree.node A10K2.t2502 (nat_lit 42608054) (nat_lit 16278480976) (nat_lit 0) A10K2.t2503 from rfl, totK_node, tot2502, tot2503]
  decide +kernel

theorem arows2499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2499 = true := by
  rw [show A10K2.u2499 = KTree.node A10K2.t2504 (nat_lit 42612884) (nat_lit 12714679208) (nat_lit 0) A10K2.t2505 from rfl, allE_node, rows2504, irow2499, rows2505]
  all_goals rfl

theorem atot2499 : totK PA10K2 A10K2.u2499 = [293303898517, 1914000391169, 3921027430807, 2914559397527, 616063758146, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2499 = KTree.node A10K2.t2504 (nat_lit 42612884) (nat_lit 12714679208) (nat_lit 0) A10K2.t2505 from rfl, totK_node, tot2504, tot2505]
  decide +kernel

theorem arows2500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2500 = true := by
  rw [show A10K2.u2500 = KTree.node A10K2.t2506 (nat_lit 42617108) (nat_lit 13357073411) (nat_lit 0) A10K2.t2507 from rfl, allE_node, rows2506, irow2500, rows2507]
  all_goals rfl

theorem atot2500 : totK PA10K2 A10K2.u2500 = [583209941258, 2849563641047, 4131274448599, 1737114348682, 145860085679, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2500 = KTree.node A10K2.t2506 (nat_lit 42617108) (nat_lit 13357073411) (nat_lit 0) A10K2.t2507 from rfl, totK_node, tot2506, tot2507]
  decide +kernel

theorem arows2502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2502 = true := by
  rw [show A10K2.u2502 = KTree.node A10K2.t2508 (nat_lit 42633258) (nat_lit 8423341369) (nat_lit 0) A10K2.t2509 from rfl, allE_node, rows2508, irow2502, rows2509]
  all_goals rfl

theorem atot2502 : totK PA10K2 A10K2.u2502 = [0, 1030834602867, 3718391458851, 3647014718063, 962496929537, 58931901996, 0, 0, 0, 0] := by
  rw [show A10K2.u2502 = KTree.node A10K2.t2508 (nat_lit 42633258) (nat_lit 8423341369) (nat_lit 0) A10K2.t2509 from rfl, totK_node, tot2508, tot2509]
  decide +kernel

theorem arows2503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2503 = true := by
  rw [show A10K2.u2503 = KTree.node A10K2.t2510 (nat_lit 42643383) (nat_lit 15100918269) (nat_lit 0) A10K2.t2511 from rfl, allE_node, rows2510, irow2503, rows2511]
  all_goals rfl

theorem atot2503 : totK PA10K2 A10K2.u2503 = [0, 987663185609, 3618248724994, 3837471383919, 1030703013816, 63118289004, 0, 0, 0, 0] := by
  rw [show A10K2.u2503 = KTree.node A10K2.t2510 (nat_lit 42643383) (nat_lit 15100918269) (nat_lit 0) A10K2.t2511 from rfl, totK_node, tot2510, tot2511]
  decide +kernel

theorem arows2507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2507 = true := by
  rw [show A10K2.u2507 = KTree.node A10K2.t2512 (nat_lit 42652897) (nat_lit 4479023984) (nat_lit 0) A10K2.t2513 from rfl, allE_node, rows2512, irow2507, rows2513]
  all_goals rfl

theorem atot2507 : totK PA10K2 A10K2.u2507 = [311517321411, 1051091343942, 2333880023776, 3557699166734, 1799574031588, 271677105452, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2507 = KTree.node A10K2.t2512 (nat_lit 42652897) (nat_lit 4479023984) (nat_lit 0) A10K2.t2513 from rfl, totK_node, tot2512, tot2513]
  decide +kernel

theorem arows2508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2508 = true := by
  rw [show A10K2.u2508 = KTree.node A10K2.t2514 (nat_lit 42675678) (nat_lit 15095619344) (nat_lit 0) A10K2.t2515 from rfl, allE_node, rows2514, irow2508, rows2515]
  all_goals rfl

theorem atot2508 : totK PA10K2 A10K2.u2508 = [499730976493, 2645647884191, 4217717232977, 2263760265761, 430650867576, 25715051306, 0, 0, 0, 0] := by
  rw [show A10K2.u2508 = KTree.node A10K2.t2514 (nat_lit 42675678) (nat_lit 15095619344) (nat_lit 0) A10K2.t2515 from rfl, totK_node, tot2514, tot2515]
  decide +kernel

theorem arows2510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2510 = true := by
  rw [show A10K2.u2510 = KTree.node A10K2.t2516 (nat_lit 42689690) (nat_lit 15217013153) (nat_lit 0) A10K2.t2517 from rfl, allE_node, rows2516, irow2510, rows2517]
  all_goals rfl

theorem atot2510 : totK PA10K2 A10K2.u2510 = [798450316783, 3106385908753, 4071036874286, 1960159826736, 269969587793, 6032141194, 0, 0, 0, 0] := by
  rw [show A10K2.u2510 = KTree.node A10K2.t2516 (nat_lit 42689690) (nat_lit 15217013153) (nat_lit 0) A10K2.t2517 from rfl, totK_node, tot2516, tot2517]
  decide +kernel

theorem arows2511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2511 = true := by
  rw [show A10K2.u2511 = KTree.node A10K2.t2518 (nat_lit 42694371) (nat_lit 6040678905) (nat_lit 0) A10K2.t2519 from rfl, allE_node, rows2518, irow2511, rows2519]
  all_goals rfl

theorem atot2511 : totK PA10K2 A10K2.u2511 = [0, 1208476101531, 4053137910620, 3827430456247, 1046669585380, 62996513375, 0, 0, 0, 0] := by
  rw [show A10K2.u2511 = KTree.node A10K2.t2518 (nat_lit 42694371) (nat_lit 6040678905) (nat_lit 0) A10K2.t2519 from rfl, totK_node, tot2518, tot2519]
  decide +kernel

theorem arows2514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2514 = true := by
  rw [show A10K2.u2514 = KTree.node A10K2.t2520 (nat_lit 42708380) (nat_lit 7956558187) (nat_lit 0) A10K2.t2521 from rfl, allE_node, rows2520, irow2514, rows2521]
  all_goals rfl

theorem atot2514 : totK PA10K2 A10K2.u2514 = [0, 598612751440, 2835960784598, 4188044963166, 2120960910241, 302480227372, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u2514 = KTree.node A10K2.t2520 (nat_lit 42708380) (nat_lit 7956558187) (nat_lit 0) A10K2.t2521 from rfl, totK_node, tot2520, tot2521]
  decide +kernel

theorem arows2515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2515 = true := by
  rw [show A10K2.u2515 = KTree.node A10K2.t2522 (nat_lit 42722716) (nat_lit 8365571151) (nat_lit 0) A10K2.t2523 from rfl, allE_node, rows2522, irow2515, rows2523]
  all_goals rfl

theorem atot2515 : totK PA10K2 A10K2.u2515 = [0, 797739579589, 3322192590547, 4322266936205, 1652133155418, 110364554474, 0, 0, 0, 0] := by
  rw [show A10K2.u2515 = KTree.node A10K2.t2522 (nat_lit 42722716) (nat_lit 8365571151) (nat_lit 0) A10K2.t2523 from rfl, totK_node, tot2522, tot2523]
  decide +kernel

theorem arows2517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2517 = true := by
  rw [show A10K2.u2517 = KTree.node A10K2.t2524 (nat_lit 42728630) (nat_lit 16606316129) (nat_lit 0) A10K2.t2525 from rfl, allE_node, rows2524, irow2517, rows2525]
  all_goals rfl

theorem atot2517 : totK PA10K2 A10K2.u2517 = [0, 319639362920, 1759207366021, 3675886899161, 3306351439308, 948692079249, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u2517 = KTree.node A10K2.t2524 (nat_lit 42728630) (nat_lit 16606316129) (nat_lit 0) A10K2.t2525 from rfl, totK_node, tot2524, tot2525]
  decide +kernel

theorem arows2518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2518 = true := by
  rw [show A10K2.u2518 = KTree.node A10K2.t2526 (nat_lit 42806838) (nat_lit 16214281486) (nat_lit 0) A10K2.t2527 from rfl, allE_node, rows2526, irow2518, rows2527]
  all_goals rfl

theorem atot2518 : totK PA10K2 A10K2.u2518 = [0, 538071541683, 2619182355587, 3982304473065, 2120061979310, 407480087677, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u2518 = KTree.node A10K2.t2526 (nat_lit 42806838) (nat_lit 16214281486) (nat_lit 0) A10K2.t2527 from rfl, totK_node, tot2526, tot2527]
  decide +kernel

theorem arows2523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2523 = true := by
  rw [show A10K2.u2523 = KTree.node A10K2.t2528 (nat_lit 42812245) (nat_lit 6365417349) (nat_lit 0) A10K2.t2529 from rfl, allE_node, rows2528, irow2523, rows2529]
  all_goals rfl

theorem atot2523 : totK PA10K2 A10K2.u2523 = [0, 742273277851, 2888361989852, 3744274386859, 1845892472947, 256782966006, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u2523 = KTree.node A10K2.t2528 (nat_lit 42812245) (nat_lit 6365417349) (nat_lit 0) A10K2.t2529 from rfl, totK_node, tot2528, tot2529]
  decide +kernel

theorem arows2524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2524 = true := by
  rw [show A10K2.u2524 = KTree.node A10K2.t2530 (nat_lit 42818061) (nat_lit 5466955875) (nat_lit 0) A10K2.t2531 from rfl, allE_node, rows2530, irow2524, rows2531]
  all_goals rfl

theorem atot2524 : totK PA10K2 A10K2.u2524 = [0, 469511191713, 2567138336821, 4289117818949, 2111690392804, 246821382421, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u2524 = KTree.node A10K2.t2530 (nat_lit 42818061) (nat_lit 5466955875) (nat_lit 0) A10K2.t2531 from rfl, totK_node, tot2530, tot2531]
  decide +kernel

theorem arows2526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2526 = true := by
  rw [show A10K2.u2526 = KTree.node A10K2.t2532 (nat_lit 42825144) (nat_lit 12472043129) (nat_lit 0) A10K2.t2533 from rfl, allE_node, rows2532, irow2526, rows2533]
  all_goals rfl

theorem atot2526 : totK PA10K2 A10K2.u2526 = [0, 224689426326, 1748219261490, 4047028478920, 3382893579440, 832517566718, 41062513076, 0, 0, 0] := by
  rw [show A10K2.u2526 = KTree.node A10K2.t2532 (nat_lit 42825144) (nat_lit 12472043129) (nat_lit 0) A10K2.t2533 from rfl, totK_node, tot2532, tot2533]
  decide +kernel

theorem arows2527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2527 = true := by
  rw [show A10K2.u2527 = KTree.node A10K2.t2534 (nat_lit 42838869) (nat_lit 6626725597) (nat_lit 0) A10K2.t2535 from rfl, allE_node, rows2534, irow2527, rows2535]
  all_goals rfl

theorem atot2527 : totK PA10K2 A10K2.u2527 = [0, 0, 733432520855, 3119144843182, 3955253812234, 1591301862648, 201344793106, 9729745405, 0, 0] := by
  rw [show A10K2.u2527 = KTree.node A10K2.t2534 (nat_lit 42838869) (nat_lit 6626725597) (nat_lit 0) A10K2.t2535 from rfl, totK_node, tot2534, tot2535]
  decide +kernel

theorem arows2530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2530 = true := by
  rw [show A10K2.u2530 = KTree.node A10K2.t2536 (nat_lit 42844417) (nat_lit 9993845645) (nat_lit 0) A10K2.t2537 from rfl, allE_node, rows2536, irow2530, rows2537]
  all_goals rfl

theorem atot2530 : totK PA10K2 A10K2.u2530 = [0, 0, 629458764620, 2553572619047, 3590318228954, 2011151410785, 418191263497, 15847424528, 0, 0] := by
  rw [show A10K2.u2530 = KTree.node A10K2.t2536 (nat_lit 42844417) (nat_lit 9993845645) (nat_lit 0) A10K2.t2537 from rfl, totK_node, tot2536, tot2537]
  decide +kernel

theorem arows2531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2531 = true := by
  rw [show A10K2.u2531 = KTree.node A10K2.t2538 (nat_lit 42850530) (nat_lit 13231179754) (nat_lit 0) A10K2.t2539 from rfl, allE_node, rows2538, irow2531, rows2539]
  all_goals rfl

theorem atot2531 : totK PA10K2 A10K2.u2531 = [0, 0, 518259376290, 2711394396354, 4192034826519, 1817974987403, 220211641996, 5685526223, 0, 0] := by
  rw [show A10K2.u2531 = KTree.node A10K2.t2538 (nat_lit 42850530) (nat_lit 13231179754) (nat_lit 0) A10K2.t2539 from rfl, totK_node, tot2538, tot2539]
  decide +kernel

theorem arows2533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2533 = true := by
  rw [show A10K2.u2533 = KTree.node A10K2.t2540 (nat_lit 42861332) (nat_lit 12485180901) (nat_lit 0) A10K2.t2541 from rfl, allE_node, rows2540, irow2533, rows2541]
  all_goals rfl

theorem atot2533 : totK PA10K2 A10K2.u2533 = [0, 516552094339, 2486750701693, 3847661869710, 2194809478938, 484526209590, 31276155898, 0, 0, 0] := by
  rw [show A10K2.u2533 = KTree.node A10K2.t2540 (nat_lit 42861332) (nat_lit 12485180901) (nat_lit 0) A10K2.t2541 from rfl, totK_node, tot2540, tot2541]
  decide +kernel

theorem arows2534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2534 = true := by
  rw [show A10K2.u2534 = KTree.node A10K2.t2542 (nat_lit 42870713) (nat_lit 3391390363) (nat_lit 0) A10K2.t2543 from rfl, allE_node, rows2542, irow2534, rows2543]
  all_goals rfl

theorem atot2534 : totK PA10K2 A10K2.u2534 = [0, 789671577276, 3118546510306, 3949188035046, 1685134212519, 201488322015, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u2534 = KTree.node A10K2.t2542 (nat_lit 42870713) (nat_lit 3391390363) (nat_lit 0) A10K2.t2543 from rfl, totK_node, tot2542, tot2543]
  decide +kernel

theorem arows2538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2538 = true := by
  rw [show A10K2.u2538 = KTree.node A10K2.t2544 (nat_lit 42875661) (nat_lit 5525794705) (nat_lit 0) A10K2.t2545 from rfl, allE_node, rows2544, irow2538, rows2545]
  all_goals rfl

theorem atot2538 : totK PA10K2 A10K2.u2538 = [0, 425404870383, 1956946144357, 3688913011043, 2732625763482, 594743577026, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2538 = KTree.node A10K2.t2544 (nat_lit 42875661) (nat_lit 5525794705) (nat_lit 0) A10K2.t2545 from rfl, totK_node, tot2544, tot2545]
  decide +kernel

theorem arows2539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2539 = true := by
  rw [show A10K2.u2539 = KTree.node A10K2.t2546 (nat_lit 42881060) (nat_lit 13324647755) (nat_lit 0) A10K2.t2547 from rfl, allE_node, rows2546, irow2539, rows2547]
  all_goals rfl

theorem atot2539 : totK PA10K2 A10K2.u2539 = [0, 370680369222, 2511206032154, 4298845533012, 2037700618277, 189139460711, 0, 0, 0, 0] := by
  rw [show A10K2.u2539 = KTree.node A10K2.t2546 (nat_lit 42881060) (nat_lit 13324647755) (nat_lit 0) A10K2.t2547 from rfl, totK_node, tot2546, tot2547]
  decide +kernel

theorem arows2541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2541 = true := by
  rw [show A10K2.u2541 = KTree.node A10K2.t2548 (nat_lit 42896157) (nat_lit 6094553220) (nat_lit 0) A10K2.t2549 from rfl, allE_node, rows2548, irow2541, rows2549]
  all_goals rfl

theorem atot2541 : totK PA10K2 A10K2.u2541 = [0, 0, 1094392743633, 3787833790511, 3596932931955, 841814364766, 43979604281, 0, 0, 0] := by
  rw [show A10K2.u2541 = KTree.node A10K2.t2548 (nat_lit 42896157) (nat_lit 6094553220) (nat_lit 0) A10K2.t2549 from rfl, totK_node, tot2548, tot2549]
  decide +kernel

theorem arows2542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2542 = true := by
  rw [show A10K2.u2542 = KTree.node A10K2.t2550 (nat_lit 42910572) (nat_lit 11348012497) (nat_lit 0) A10K2.t2551 from rfl, allE_node, rows2550, irow2542, rows2551]
  all_goals rfl

theorem atot2542 : totK PA10K2 A10K2.u2542 = [0, 0, 1009772677879, 3740419989225, 3820256726019, 875062637291, 44066702005, 0, 0, 0] := by
  rw [show A10K2.u2542 = KTree.node A10K2.t2550 (nat_lit 42910572) (nat_lit 11348012497) (nat_lit 0) A10K2.t2551 from rfl, totK_node, tot2550, tot2551]
  decide +kernel

theorem arows2545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2545 = true := by
  rw [show A10K2.u2545 = KTree.node A10K2.t2552 (nat_lit 42916400) (nat_lit 11448396421) (nat_lit 0) A10K2.t2553 from rfl, allE_node, rows2552, irow2545, rows2553]
  all_goals rfl

theorem atot2545 : totK PA10K2 A10K2.u2545 = [0, 512527576312, 1669874681946, 2487604313471, 2996533677510, 1481361902221, 214649257949, 6239673734, 0, 0] := by
  rw [show A10K2.u2545 = KTree.node A10K2.t2552 (nat_lit 42916400) (nat_lit 11448396421) (nat_lit 0) A10K2.t2553 from rfl, totK_node, tot2552, tot2553]
  decide +kernel

theorem arows2546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2546 = true := by
  rw [show A10K2.u2546 = KTree.node A10K2.t2554 (nat_lit 42939756) (nat_lit 11370397930) (nat_lit 0) A10K2.t2555 from rfl, allE_node, rows2554, irow2546, rows2555]
  all_goals rfl

theorem atot2546 : totK PA10K2 A10K2.u2546 = [0, 295617662505, 2082091043224, 4195053645823, 2818599451626, 577288675099, 31285368086, 0, 0, 0] := by
  rw [show A10K2.u2546 = KTree.node A10K2.t2554 (nat_lit 42939756) (nat_lit 11370397930) (nat_lit 0) A10K2.t2555 from rfl, totK_node, tot2554, tot2555]
  decide +kernel

theorem arows2548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2548 = true := by
  rw [show A10K2.u2548 = KTree.node A10K2.t2556 (nat_lit 42952639) (nat_lit 14171926471) (nat_lit 0) A10K2.t2557 from rfl, allE_node, rows2556, irow2548, rows2557]
  all_goals rfl

theorem atot2548 : totK PA10K2 A10K2.u2548 = [0, 797527500186, 3128626744643, 4118785746070, 1983390379238, 284487926266, 6281495166, 0, 0, 0] := by
  rw [show A10K2.u2548 = KTree.node A10K2.t2556 (nat_lit 42952639) (nat_lit 14171926471) (nat_lit 0) A10K2.t2557 from rfl, totK_node, tot2556, tot2557]
  decide +kernel

theorem arows2549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2549 = true := by
  rw [show A10K2.u2549 = KTree.node A10K2.t2558 (nat_lit 42958486) (nat_lit 15374033004) (nat_lit 0) A10K2.t2559 from rfl, allE_node, rows2558, irow2549, rows2559]
  all_goals rfl

theorem atot2549 : totK PA10K2 A10K2.u2549 = [444521281299, 1437000435320, 1991145535163, 2628372201377, 2538206151002, 804869990546, 56100664475, 0, 0, 0] := by
  rw [show A10K2.u2549 = KTree.node A10K2.t2558 (nat_lit 42958486) (nat_lit 15374033004) (nat_lit 0) A10K2.t2559 from rfl, totK_node, tot2558, tot2559]
  decide +kernel

theorem arows2558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2558 = true := by
  rw [show A10K2.u2558 = KTree.node A10K2.t2560 (nat_lit 42996069) (nat_lit 7092176176) (nat_lit 0) A10K2.t2561 from rfl, allE_node, rows2560, irow2558, rows2561]
  all_goals rfl

theorem atot2558 : totK PA10K2 A10K2.u2558 = [305225869305, 2026567672091, 3950419335195, 2683410140610, 555429722137, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2558 = KTree.node A10K2.t2560 (nat_lit 42996069) (nat_lit 7092176176) (nat_lit 0) A10K2.t2561 from rfl, totK_node, tot2560, tot2561]
  decide +kernel

theorem arows2559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2559 = true := by
  rw [show A10K2.u2559 = KTree.node A10K2.t2562 (nat_lit 43009770) (nat_lit 12263698521) (nat_lit 0) A10K2.t2563 from rfl, allE_node, rows2562, irow2559, rows2563]
  all_goals rfl

theorem atot2559 : totK PA10K2 A10K2.u2559 = [779949739936, 3211402279246, 3985714981162, 1483272074739, 124703173831, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2559 = KTree.node A10K2.t2562 (nat_lit 43009770) (nat_lit 12263698521) (nat_lit 0) A10K2.t2563 from rfl, totK_node, tot2562, tot2563]
  decide +kernel

theorem arows2561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2561 = true := by
  rw [show A10K2.u2561 = KTree.node A10K2.t2564 (nat_lit 43016647) (nat_lit 14390858342) (nat_lit 0) A10K2.t2565 from rfl, allE_node, rows2564, irow2561, rows2565]
  all_goals rfl

theorem atot2561 : totK PA10K2 A10K2.u2561 = [266424507814, 1908029592418, 4112760656722, 2809277607869, 514305873752, 13207830636, 0, 0, 0, 0] := by
  rw [show A10K2.u2561 = KTree.node A10K2.t2564 (nat_lit 43016647) (nat_lit 14390858342) (nat_lit 0) A10K2.t2565 from rfl, totK_node, tot2564, tot2565]
  decide +kernel

theorem arows2562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2562 = true := by
  rw [show A10K2.u2562 = KTree.node A10K2.t2566 (nat_lit 43027556) (nat_lit 11925582992) (nat_lit 0) A10K2.t2567 from rfl, allE_node, rows2566, irow2562, rows2567]
  all_goals rfl

theorem atot2562 : totK PA10K2 A10K2.u2562 = [0, 545977803608, 2597638806238, 3915557883535, 1992900161023, 390426446666, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u2562 = KTree.node A10K2.t2566 (nat_lit 43027556) (nat_lit 11925582992) (nat_lit 0) A10K2.t2567 from rfl, totK_node, tot2566, tot2567]
  decide +kernel

theorem arows2565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2565 = true := by
  rw [show A10K2.u2565 = KTree.node A10K2.t2568 (nat_lit 43041345) (nat_lit 10282547901) (nat_lit 0) A10K2.t2569 from rfl, allE_node, rows2568, irow2565, rows2569]
  all_goals rfl

theorem atot2565 : totK PA10K2 A10K2.u2565 = [0, 778410583582, 3050749518891, 3778800911328, 1616803714342, 222207683015, 5410721913, 0, 0, 0] := by
  rw [show A10K2.u2565 = KTree.node A10K2.t2568 (nat_lit 43041345) (nat_lit 10282547901) (nat_lit 0) A10K2.t2569 from rfl, totK_node, tot2568, tot2569]
  decide +kernel

theorem arows2566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2566 = true := by
  rw [show A10K2.u2566 = KTree.node A10K2.t2570 (nat_lit 43047687) (nat_lit 4736134070) (nat_lit 0) A10K2.t2571 from rfl, allE_node, rows2570, irow2566, rows2571]
  all_goals rfl

theorem atot2566 : totK PA10K2 A10K2.u2566 = [311769148082, 1172192212502, 2484266874519, 3516798368388, 1756140217462, 219178372242, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u2566 = KTree.node A10K2.t2570 (nat_lit 43047687) (nat_lit 4736134070) (nat_lit 0) A10K2.t2571 from rfl, totK_node, tot2570, tot2571]
  decide +kernel

theorem arows2568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2568 = true := by
  rw [show A10K2.u2568 = KTree.node A10K2.t2572 (nat_lit 43068914) (nat_lit 14140600527) (nat_lit 0) A10K2.t2573 from rfl, allE_node, rows2572, irow2568, rows2573]
  all_goals rfl

theorem atot2568 : totK PA10K2 A10K2.u2568 = [503939570210, 2527675430112, 3985792196885, 2219479105581, 425120212331, 25734533292, 0, 0, 0, 0] := by
  rw [show A10K2.u2568 = KTree.node A10K2.t2572 (nat_lit 43068914) (nat_lit 14140600527) (nat_lit 0) A10K2.t2573 from rfl, totK_node, tot2572, tot2573]
  decide +kernel

theorem arows2569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2569 = true := by
  rw [show A10K2.u2569 = KTree.node A10K2.t2574 (nat_lit 43074313) (nat_lit 9697184672) (nat_lit 0) A10K2.t2575 from rfl, allE_node, rows2574, irow2569, rows2575]
  all_goals rfl

theorem atot2569 : totK PA10K2 A10K2.u2569 = [781826896359, 2896582213791, 3695091974712, 1933281349199, 275375495207, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u2569 = KTree.node A10K2.t2574 (nat_lit 43074313) (nat_lit 9697184672) (nat_lit 0) A10K2.t2575 from rfl, totK_node, tot2574, tot2575]
  decide +kernel

theorem arows2573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2573 = true := by
  rw [show A10K2.u2573 = KTree.node A10K2.t2576 (nat_lit 43079950) (nat_lit 6011670918) (nat_lit 0) A10K2.t2577 from rfl, allE_node, rows2576, irow2573, rows2577]
  all_goals rfl

theorem atot2573 : totK PA10K2 A10K2.u2573 = [418857662174, 2439919742636, 4294836144663, 2227209309665, 301874974759, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2573 = KTree.node A10K2.t2576 (nat_lit 43079950) (nat_lit 6011670918) (nat_lit 0) A10K2.t2577 from rfl, totK_node, tot2576, tot2577]
  decide +kernel

theorem arows2574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2574 = true := by
  rw [show A10K2.u2574 = KTree.node A10K2.t2578 (nat_lit 43089329) (nat_lit 8257112776) (nat_lit 0) A10K2.t2579 from rfl, allE_node, rows2578, irow2574, rows2579]
  all_goals rfl

theorem atot2574 : totK PA10K2 A10K2.u2574 = [83865859844, 1343413501457, 3912347331993, 3621594930795, 1045876414670, 76080780157, 0, 0, 0, 0] := by
  rw [show A10K2.u2574 = KTree.node A10K2.t2578 (nat_lit 43089329) (nat_lit 8257112776) (nat_lit 0) A10K2.t2579 from rfl, totK_node, tot2578, tot2579]
  decide +kernel

theorem arows2576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2576 = true := by
  rw [show A10K2.u2576 = KTree.node A10K2.t2580 (nat_lit 43103405) (nat_lit 6117780252) (nat_lit 0) A10K2.t2581 from rfl, allE_node, rows2580, irow2576, rows2581]
  all_goals rfl

theorem atot2576 : totK PA10K2 A10K2.u2576 = [0, 442221634930, 2268008348503, 3956224443606, 2403668298288, 464738533586, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u2576 = KTree.node A10K2.t2580 (nat_lit 43103405) (nat_lit 6117780252) (nat_lit 0) A10K2.t2581 from rfl, totK_node, tot2580, tot2581]
  decide +kernel

theorem arows2577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2577 = true := by
  rw [show A10K2.u2577 = KTree.node A10K2.t2582 (nat_lit 43107990) (nat_lit 14090307283) (nat_lit 0) A10K2.t2583 from rfl, allE_node, rows2582, irow2577, rows2583]
  all_goals rfl

theorem atot2577 : totK PA10K2 A10K2.u2577 = [0, 781409246072, 3259735778862, 3953271578515, 1395815491605, 156725234070, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u2577 = KTree.node A10K2.t2582 (nat_lit 43107990) (nat_lit 14090307283) (nat_lit 0) A10K2.t2583 from rfl, totK_node, tot2582, tot2583]
  decide +kernel

theorem arows2580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2580 = true := by
  rw [show A10K2.u2580 = KTree.node A10K2.t2584 (nat_lit 43115805) (nat_lit 6220924820) (nat_lit 0) A10K2.t2585 from rfl, allE_node, rows2584, irow2580, rows2585]
  all_goals rfl

theorem atot2580 : totK PA10K2 A10K2.u2580 = [113616355882, 764918460923, 2566938021995, 3952073119983, 2092668717045, 277345430120, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2580 = KTree.node A10K2.t2584 (nat_lit 43115805) (nat_lit 6220924820) (nat_lit 0) A10K2.t2585 from rfl, totK_node, tot2584, tot2585]
  decide +kernel

theorem arows2581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2581 = true := by
  rw [show A10K2.u2581 = KTree.node A10K2.t2586 (nat_lit 43125586) (nat_lit 12982176605) (nat_lit 0) A10K2.t2587 from rfl, allE_node, rows2586, irow2581, rows2587]
  all_goals rfl

theorem atot2581 : totK PA10K2 A10K2.u2581 = [583007662816, 2653630313471, 3720225662519, 1854812348296, 376887829007, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u2581 = KTree.node A10K2.t2586 (nat_lit 43125586) (nat_lit 12982176605) (nat_lit 0) A10K2.t2587 from rfl, totK_node, tot2586, tot2587]
  decide +kernel

theorem arows2583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2583 = true := by
  rw [show A10K2.u2583 = KTree.node A10K2.t2588 (nat_lit 43132606) (nat_lit 14171407639) (nat_lit 0) A10K2.t2589 from rfl, allE_node, rows2588, irow2583, rows2589]
  all_goals rfl

theorem atot2583 : totK PA10K2 A10K2.u2583 = [749997641183, 2984072570908, 3872326034637, 1740533416644, 216667155580, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u2583 = KTree.node A10K2.t2588 (nat_lit 43132606) (nat_lit 14171407639) (nat_lit 0) A10K2.t2589 from rfl, totK_node, tot2588, tot2589]
  decide +kernel

theorem arows2584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2584 = true := by
  rw [show A10K2.u2584 = KTree.node A10K2.t2590 (nat_lit 43137364) (nat_lit 13077887333) (nat_lit 0) A10K2.t2591 from rfl, allE_node, rows2590, irow2584, rows2591]
  all_goals rfl

theorem atot2584 : totK PA10K2 A10K2.u2584 = [281821911550, 1778384130648, 3857803830134, 2941103378250, 628707552593, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2584 = KTree.node A10K2.t2590 (nat_lit 43137364) (nat_lit 13077887333) (nat_lit 0) A10K2.t2591 from rfl, totK_node, tot2590, tot2591]
  decide +kernel

theorem arows2589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2589 = true := by
  rw [show A10K2.u2589 = KTree.node A10K2.t2592 (nat_lit 43141794) (nat_lit 13905161396) (nat_lit 0) A10K2.t2593 from rfl, allE_node, rows2592, irow2589, rows2593]
  all_goals rfl

theorem atot2589 : totK PA10K2 A10K2.u2589 = [568096137437, 2911145750139, 4191390690205, 1722693107093, 140464755192, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2589 = KTree.node A10K2.t2592 (nat_lit 43141794) (nat_lit 13905161396) (nat_lit 0) A10K2.t2593 from rfl, totK_node, tot2592, tot2593]
  decide +kernel

theorem arows2590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2590 = true := by
  rw [show A10K2.u2590 = KTree.node A10K2.t2594 (nat_lit 43157604) (nat_lit 13462219180) (nat_lit 0) A10K2.t2595 from rfl, allE_node, rows2594, irow2590, rows2595]
  all_goals rfl

theorem atot2590 : totK PA10K2 A10K2.u2590 = [0, 1028681168093, 3738374744717, 3620286063057, 916599966527, 45137667897, 0, 0, 0, 0] := by
  rw [show A10K2.u2590 = KTree.node A10K2.t2594 (nat_lit 43157604) (nat_lit 13462219180) (nat_lit 0) A10K2.t2595 from rfl, totK_node, tot2594, tot2595]
  decide +kernel

theorem arows2592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2592 = true := by
  rw [show A10K2.u2592 = KTree.node A10K2.t2596 (nat_lit 43167154) (nat_lit 14586405808) (nat_lit 0) A10K2.t2597 from rfl, allE_node, rows2596, irow2592, rows2597]
  all_goals rfl

theorem atot2592 : totK PA10K2 A10K2.u2592 = [0, 965096515049, 3576456540557, 3866055474718, 1074998204189, 64078106957, 0, 0, 0, 0] := by
  rw [show A10K2.u2592 = KTree.node A10K2.t2596 (nat_lit 43167154) (nat_lit 14586405808) (nat_lit 0) A10K2.t2597 from rfl, totK_node, tot2596, tot2597]
  decide +kernel

theorem arows2593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2593 = true := by
  rw [show A10K2.u2593 = KTree.node A10K2.t2598 (nat_lit 43176050) (nat_lit 2756781618) (nat_lit 0) A10K2.t2599 from rfl, allE_node, rows2598, irow2593, rows2599]
  all_goals rfl

theorem atot2593 : totK PA10K2 A10K2.u2593 = [0, 433254466813, 2463587040726, 4151472781209, 1981067123031, 291306829918, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2593 = KTree.node A10K2.t2598 (nat_lit 43176050) (nat_lit 2756781618) (nat_lit 0) A10K2.t2599 from rfl, totK_node, tot2598, tot2599]
  decide +kernel

theorem arows2596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2596 = true := by
  rw [show A10K2.u2596 = KTree.node A10K2.t2600 (nat_lit 43256584) (nat_lit 12478511528) (nat_lit 0) A10K2.t2601 from rfl, allE_node, rows2600, irow2596, rows2601]
  all_goals rfl

theorem atot2596 : totK PA10K2 A10K2.u2596 = [0, 659136679848, 2928970835393, 3916783706127, 1736163520400, 292184906232, 20070762815, 0, 0, 0] := by
  rw [show A10K2.u2596 = KTree.node A10K2.t2600 (nat_lit 43256584) (nat_lit 12478511528) (nat_lit 0) A10K2.t2601 from rfl, totK_node, tot2600, tot2601]
  decide +kernel

theorem arows2597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2597 = true := by
  rw [show A10K2.u2597 = KTree.node A10K2.t2602 (nat_lit 43270464) (nat_lit 14719979032) (nat_lit 0) A10K2.t2603 from rfl, allE_node, rows2602, irow2597, rows2603]
  all_goals rfl

theorem atot2597 : totK PA10K2 A10K2.u2597 = [0, 667729632621, 2609897370612, 3689399096448, 2121425036407, 359176085233, 10747604052, 0, 0, 0] := by
  rw [show A10K2.u2597 = KTree.node A10K2.t2602 (nat_lit 43270464) (nat_lit 14719979032) (nat_lit 0) A10K2.t2603 from rfl, totK_node, tot2602, tot2603]
  decide +kernel

theorem arows2599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2599 = true := by
  rw [show A10K2.u2599 = KTree.node A10K2.t2604 (nat_lit 43276384) (nat_lit 12991034545) (nat_lit 0) A10K2.t2605 from rfl, allE_node, rows2604, irow2599, rows2605]
  all_goals rfl

theorem atot2599 : totK PA10K2 A10K2.u2599 = [0, 376621293944, 2411223107826, 4215665751739, 2163067836697, 300094393860, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2599 = KTree.node A10K2.t2604 (nat_lit 43276384) (nat_lit 12991034545) (nat_lit 0) A10K2.t2605 from rfl, totK_node, tot2604, tot2605]
  decide +kernel

theorem arows2600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2600 = true := by
  rw [show A10K2.u2600 = KTree.node A10K2.t2606 (nat_lit 43329303) (nat_lit 10232697517) (nat_lit 0) A10K2.t2607 from rfl, allE_node, rows2606, irow2600, rows2607]
  all_goals rfl

theorem atot2600 : totK PA10K2 A10K2.u2600 = [0, 815102302593, 3152973145786, 3836952301492, 1689046796472, 245798404739, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u2600 = KTree.node A10K2.t2606 (nat_lit 43329303) (nat_lit 10232697517) (nat_lit 0) A10K2.t2607 from rfl, totK_node, tot2606, tot2607]
  decide +kernel

theorem arows2604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2604 = true := by
  rw [show A10K2.u2604 = KTree.node A10K2.t2608 (nat_lit 43333914) (nat_lit 14174292022) (nat_lit 0) A10K2.t2609 from rfl, allE_node, rows2608, irow2604, rows2609]
  all_goals rfl

theorem atot2604 : totK PA10K2 A10K2.u2604 = [0, 274164759194, 1730245365715, 3856062274618, 2995948184649, 616468001294, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u2604 = KTree.node A10K2.t2608 (nat_lit 43333914) (nat_lit 14174292022) (nat_lit 0) A10K2.t2609 from rfl, totK_node, tot2608, tot2609]
  decide +kernel

theorem arows2605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2605 = true := by
  rw [show A10K2.u2605 = KTree.node A10K2.t2610 (nat_lit 43338496) (nat_lit 13478411563) (nat_lit 0) A10K2.t2611 from rfl, allE_node, rows2610, irow2605, rows2611]
  all_goals rfl

theorem atot2605 : totK PA10K2 A10K2.u2605 = [0, 505638907190, 2771391638719, 4274262517761, 1803753635630, 153449512320, 0, 0, 0, 0] := by
  rw [show A10K2.u2605 = KTree.node A10K2.t2610 (nat_lit 43338496) (nat_lit 13478411563) (nat_lit 0) A10K2.t2611 from rfl, totK_node, tot2610, tot2611]
  decide +kernel

theorem arows2607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2607 = true := by
  rw [show A10K2.u2607 = KTree.node A10K2.t2612 (nat_lit 43347610) (nat_lit 14994479584) (nat_lit 0) A10K2.t2613 from rfl, allE_node, rows2612, irow2607, rows2613]
  all_goals rfl

theorem atot2607 : totK PA10K2 A10K2.u2607 = [0, 595189095497, 2488175853075, 3969663196559, 2593805932568, 482791583034, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u2607 = KTree.node A10K2.t2612 (nat_lit 43347610) (nat_lit 14994479584) (nat_lit 0) A10K2.t2613 from rfl, totK_node, tot2612, tot2613]
  decide +kernel

theorem arows2608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2608 = true := by
  rw [show A10K2.u2608 = KTree.node A10K2.t2614 (nat_lit 43387660) (nat_lit 11880854829) (nat_lit 0) A10K2.t2615 from rfl, allE_node, rows2614, irow2608, rows2615]
  all_goals rfl

theorem atot2608 : totK PA10K2 A10K2.u2608 = [0, 596783238806, 2726912677028, 3739090506034, 1758252415329, 315715164071, 24614390653, 0, 0, 0] := by
  rw [show A10K2.u2608 = KTree.node A10K2.t2614 (nat_lit 43387660) (nat_lit 11880854829) (nat_lit 0) A10K2.t2615 from rfl, totK_node, tot2614, tot2615]
  decide +kernel

theorem arows2611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2611 = true := by
  rw [show A10K2.u2611 = KTree.node A10K2.t2616 (nat_lit 43394728) (nat_lit 6199736544) (nat_lit 0) A10K2.t2617 from rfl, allE_node, rows2616, irow2611, rows2617]
  all_goals rfl

theorem atot2611 : totK PA10K2 A10K2.u2611 = [0, 748998944922, 2986483966478, 3854719619279, 1689671433044, 210133399220, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u2611 = KTree.node A10K2.t2616 (nat_lit 43394728) (nat_lit 6199736544) (nat_lit 0) A10K2.t2617 from rfl, totK_node, tot2616, tot2617]
  decide +kernel

theorem arows2612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2612 = true := by
  rw [show A10K2.u2612 = KTree.node A10K2.t2618 (nat_lit 43399528) (nat_lit 9195671947) (nat_lit 0) A10K2.t2619 from rfl, allE_node, rows2618, irow2612, rows2619]
  all_goals rfl

theorem atot2612 : totK PA10K2 A10K2.u2612 = [0, 342241960375, 1888166638666, 3908404543875, 2701821558746, 513559548322, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u2612 = KTree.node A10K2.t2618 (nat_lit 43399528) (nat_lit 9195671947) (nat_lit 0) A10K2.t2619 from rfl, totK_node, tot2618, tot2619]
  decide +kernel

theorem arows2614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2614 = true := by
  rw [show A10K2.u2614 = KTree.node A10K2.t2620 (nat_lit 43404036) (nat_lit 13244202344) (nat_lit 0) A10K2.t2621 from rfl, allE_node, rows2620, irow2614, rows2621]
  all_goals rfl

theorem atot2614 : totK PA10K2 A10K2.u2614 = [0, 504455776963, 2838230705060, 4240030705576, 1674200863577, 138456623420, 0, 0, 0, 0] := by
  rw [show A10K2.u2614 = KTree.node A10K2.t2620 (nat_lit 43404036) (nat_lit 13244202344) (nat_lit 0) A10K2.t2621 from rfl, totK_node, tot2620, tot2621]
  decide +kernel

theorem arows2615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2615 = true := by
  rw [show A10K2.u2615 = KTree.node A10K2.t2622 (nat_lit 43419816) (nat_lit 8885272639) (nat_lit 0) A10K2.t2623 from rfl, allE_node, rows2622, irow2615, rows2623]
  all_goals rfl

theorem atot2615 : totK PA10K2 A10K2.u2615 = [0, 0, 984255550314, 3668313883744, 3612772309109, 872317462752, 57372072225, 0, 0, 0] := by
  rw [show A10K2.u2615 = KTree.node A10K2.t2622 (nat_lit 43419816) (nat_lit 8885272639) (nat_lit 0) A10K2.t2623 from rfl, totK_node, tot2622, tot2623]
  decide +kernel

theorem arows2621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2621 = true := by
  rw [show A10K2.u2621 = KTree.node A10K2.t2624 (nat_lit 43434272) (nat_lit 13375405213) (nat_lit 0) A10K2.t2625 from rfl, allE_node, rows2624, irow2621, rows2625]
  all_goals rfl

theorem atot2621 : totK PA10K2 A10K2.u2621 = [0, 0, 1074440171837, 3684685003452, 3533815626843, 924819449785, 61975941459, 0, 0, 0] := by
  rw [show A10K2.u2621 = KTree.node A10K2.t2624 (nat_lit 43434272) (nat_lit 13375405213) (nat_lit 0) A10K2.t2625 from rfl, totK_node, tot2624, tot2625]
  decide +kernel

theorem arows2622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2622 = true := by
  rw [show A10K2.u2622 = KTree.node A10K2.t2626 (nat_lit 43440140) (nat_lit 11759478708) (nat_lit 0) A10K2.t2627 from rfl, allE_node, rows2626, irow2622, rows2627]
  all_goals rfl

theorem atot2622 : totK PA10K2 A10K2.u2622 = [0, 317769054122, 1167724888154, 2516453523063, 3346622949428, 1658335102020, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u2622 = KTree.node A10K2.t2626 (nat_lit 43440140) (nat_lit 11759478708) (nat_lit 0) A10K2.t2627 from rfl, totK_node, tot2626, tot2627]
  decide +kernel

theorem arows2624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2624 = true := by
  rw [show A10K2.u2624 = KTree.node A10K2.t2628 (nat_lit 44043824) (nat_lit 14893807136) (nat_lit 0) A10K2.t2629 from rfl, allE_node, rows2628, irow2624, rows2629]
  all_goals rfl

theorem atot2624 : totK PA10K2 A10K2.u2624 = [0, 522958244919, 2557460409051, 3978140465816, 2152143867386, 407811221501, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u2624 = KTree.node A10K2.t2628 (nat_lit 44043824) (nat_lit 14893807136) (nat_lit 0) A10K2.t2629 from rfl, totK_node, tot2628, tot2629]
  decide +kernel

theorem arows2625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2625 = true := by
  rw [show A10K2.u2625 = KTree.node A10K2.t2630 (nat_lit 44057132) (nat_lit 11786147444) (nat_lit 0) A10K2.t2631 from rfl, allE_node, rows2630, irow2625, rows2631]
  all_goals rfl

theorem atot2625 : totK PA10K2 A10K2.u2625 = [0, 744326850038, 2892202170687, 3756831077529, 1802658021000, 243601624091, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u2625 = KTree.node A10K2.t2630 (nat_lit 44057132) (nat_lit 11786147444) (nat_lit 0) A10K2.t2631 from rfl, totK_node, tot2630, tot2631]
  decide +kernel

theorem arows2628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2628 = true := by
  rw [show A10K2.u2628 = KTree.node A10K2.t2632 (nat_lit 44063237) (nat_lit 6792117870) (nat_lit 0) A10K2.t2633 from rfl, allE_node, rows2632, irow2628, rows2633]
  all_goals rfl

theorem atot2628 : totK PA10K2 A10K2.u2628 = [0, 514294859655, 2543026783931, 4085142656433, 2140007124272, 300511238796, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2628 = KTree.node A10K2.t2632 (nat_lit 44063237) (nat_lit 6792117870) (nat_lit 0) A10K2.t2633 from rfl, totK_node, tot2632, tot2633]
  decide +kernel

theorem arows2629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2629 = true := by
  rw [show A10K2.u2629 = KTree.node A10K2.t2634 (nat_lit 44071973) (nat_lit 5137640082) (nat_lit 0) A10K2.t2635 from rfl, allE_node, rows2634, irow2629, rows2635]
  all_goals rfl

theorem atot2629 : totK PA10K2 A10K2.u2629 = [0, 65520693115, 1452520675375, 4123109143732, 3579269033729, 838610350207, 40858060673, 0, 0, 0] := by
  rw [show A10K2.u2629 = KTree.node A10K2.t2634 (nat_lit 44071973) (nat_lit 5137640082) (nat_lit 0) A10K2.t2635 from rfl, totK_node, tot2634, tot2635]
  decide +kernel

theorem arows2631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2631 = true := by
  rw [show A10K2.u2631 = KTree.node A10K2.t2636 (nat_lit 44076544) (nat_lit 15548134428) (nat_lit 0) A10K2.t2637 from rfl, allE_node, rows2636, irow2631, rows2637]
  all_goals rfl

theorem atot2631 : totK PA10K2 A10K2.u2631 = [0, 0, 521496223102, 2563782927717, 3921515922260, 2071187679153, 411082756590, 25239774317, 0, 0] := by
  rw [show A10K2.u2631 = KTree.node A10K2.t2636 (nat_lit 44076544) (nat_lit 15548134428) (nat_lit 0) A10K2.t2637 from rfl, totK_node, tot2636, tot2637]
  decide +kernel

theorem arows2632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2632 = true := by
  rw [show A10K2.u2632 = KTree.node A10K2.t2638 (nat_lit 44089932) (nat_lit 10647355950) (nat_lit 0) A10K2.t2639 from rfl, allE_node, rows2638, irow2632, rows2639]
  all_goals rfl

theorem atot2632 : totK PA10K2 A10K2.u2632 = [0, 0, 741491722285, 3002691649003, 3802098970016, 1560827106652, 201055323495, 5410721913, 0, 0] := by
  rw [show A10K2.u2632 = KTree.node A10K2.t2638 (nat_lit 44089932) (nat_lit 10647355950) (nat_lit 0) A10K2.t2639 from rfl, totK_node, tot2638, tot2639]
  decide +kernel

theorem arows2636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2636 = true := by
  rw [show A10K2.u2636 = KTree.node A10K2.t2640 (nat_lit 44096352) (nat_lit 10975463192) (nat_lit 0) A10K2.t2641 from rfl, allE_node, rows2640, irow2636, rows2641]
  all_goals rfl

theorem atot2636 : totK PA10K2 A10K2.u2636 = [0, 0, 591060099811, 2766948070491, 4156998515144, 1902730522486, 225868453972, 5546304973, 0, 0] := by
  rw [show A10K2.u2636 = KTree.node A10K2.t2640 (nat_lit 44096352) (nat_lit 10975463192) (nat_lit 0) A10K2.t2641 from rfl, totK_node, tot2640, tot2641]
  decide +kernel

theorem arows2637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2637 = true := by
  rw [show A10K2.u2637 = KTree.node A10K2.t2642 (nat_lit 44173587) (nat_lit 9868149628) (nat_lit 0) A10K2.t2643 from rfl, allE_node, rows2642, irow2637, rows2643]
  all_goals rfl

theorem atot2637 : totK PA10K2 A10K2.u2637 = [0, 767063984985, 3093595445956, 3899776802007, 1689707578444, 311302603427, 23009379923, 0, 0, 0] := by
  rw [show A10K2.u2637 = KTree.node A10K2.t2642 (nat_lit 44173587) (nat_lit 9868149628) (nat_lit 0) A10K2.t2643 from rfl, totK_node, tot2642, tot2643]
  decide +kernel

theorem arows2639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2639 = true := by
  rw [show A10K2.u2639 = KTree.node A10K2.t2644 (nat_lit 44178931) (nat_lit 5836292735) (nat_lit 0) A10K2.t2645 from rfl, allE_node, rows2644, irow2639, rows2645]
  all_goals rfl

theorem atot2639 : totK PA10K2 A10K2.u2639 = [0, 559356954831, 2408669303355, 3669854358346, 2371864232839, 541267895343, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2639 = KTree.node A10K2.t2644 (nat_lit 44178931) (nat_lit 5836292735) (nat_lit 0) A10K2.t2645 from rfl, totK_node, tot2644, tot2645]
  decide +kernel

theorem arows2640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2640 = true := by
  rw [show A10K2.u2640 = KTree.node A10K2.t2646 (nat_lit 44186156) (nat_lit 12006415954) (nat_lit 0) A10K2.t2647 from rfl, allE_node, rows2646, irow2640, rows2647]
  all_goals rfl

theorem atot2640 : totK PA10K2 A10K2.u2640 = [0, 511776002785, 2265650581529, 3699480040620, 2442391948673, 494975186387, 31333686660, 0, 0, 0] := by
  rw [show A10K2.u2640 = KTree.node A10K2.t2646 (nat_lit 44186156) (nat_lit 12006415954) (nat_lit 0) A10K2.t2647 from rfl, totK_node, tot2646, tot2647]
  decide +kernel

theorem arows2643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2643 = true := by
  rw [show A10K2.u2643 = KTree.node A10K2.t2648 (nat_lit 44192033) (nat_lit 9870704603) (nat_lit 0) A10K2.t2649 from rfl, allE_node, rows2648, irow2643, rows2649]
  all_goals rfl

theorem atot2643 : totK PA10K2 A10K2.u2643 = [0, 304053839609, 2225615154274, 4207289441607, 2263468979473, 308389350762, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2643 = KTree.node A10K2.t2648 (nat_lit 44192033) (nat_lit 9870704603) (nat_lit 0) A10K2.t2649 from rfl, totK_node, tot2648, tot2649]
  decide +kernel

theorem arows2644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2644 = true := by
  rw [show A10K2.u2644 = KTree.node A10K2.t2650 (nat_lit 44206854) (nat_lit 8384098252) (nat_lit 0) A10K2.t2651 from rfl, allE_node, rows2650, irow2644, rows2651]
  all_goals rfl

theorem atot2644 : totK PA10K2 A10K2.u2644 = [0, 0, 966836738932, 3669636910727, 3938496860063, 1060450297279, 64464457937, 0, 0, 0] := by
  rw [show A10K2.u2644 = KTree.node A10K2.t2650 (nat_lit 44206854) (nat_lit 8384098252) (nat_lit 0) A10K2.t2651 from rfl, totK_node, tot2650, tot2651]
  decide +kernel

theorem arows2646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2646 = true := by
  rw [show A10K2.u2646 = KTree.node A10K2.t2652 (nat_lit 44221213) (nat_lit 6017451388) (nat_lit 0) A10K2.t2653 from rfl, allE_node, rows2652, irow2646, rows2653]
  all_goals rfl

theorem atot2646 : totK PA10K2 A10K2.u2646 = [0, 0, 1091393741568, 3743522356551, 3586566616537, 871440302220, 56621979327, 0, 0, 0] := by
  rw [show A10K2.u2646 = KTree.node A10K2.t2652 (nat_lit 44221213) (nat_lit 6017451388) (nat_lit 0) A10K2.t2653 from rfl, totK_node, tot2652, tot2653]
  decide +kernel

theorem arows2647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2647 = true := by
  rw [show A10K2.u2647 = KTree.node A10K2.t2654 (nat_lit 44226913) (nat_lit 8845514092) (nat_lit 0) A10K2.t2655 from rfl, allE_node, rows2654, irow2647, rows2655]
  all_goals rfl

theorem atot2647 : totK PA10K2 A10K2.u2647 = [0, 482054232543, 1456573791262, 2405386273093, 3129464360115, 1638801276961, 265773289542, 6354482628, 0, 0] := by
  rw [show A10K2.u2647 = KTree.node A10K2.t2654 (nat_lit 44226913) (nat_lit 8845514092) (nat_lit 0) A10K2.t2655 from rfl, totK_node, tot2654, tot2655]
  decide +kernel

theorem arows2652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2652 = true := by
  rw [show A10K2.u2652 = KTree.node A10K2.t2656 (nat_lit 44643485) (nat_lit 6111184690) (nat_lit 0) A10K2.t2657 from rfl, allE_node, rows2656, irow2652, rows2657]
  all_goals rfl

theorem atot2652 : totK PA10K2 A10K2.u2652 = [0, 378150862450, 2266259758744, 4074784734883, 2535629175504, 470053467805, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u2652 = KTree.node A10K2.t2656 (nat_lit 44643485) (nat_lit 6111184690) (nat_lit 0) A10K2.t2657 from rfl, totK_node, tot2656, tot2657]
  decide +kernel

theorem arows2653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2653 = true := by
  rw [show A10K2.u2653 = KTree.node A10K2.t2658 (nat_lit 44647779) (nat_lit 9355842215) (nat_lit 0) A10K2.t2659 from rfl, allE_node, rows2658, irow2653, rows2659]
  all_goals rfl

theorem atot2653 : totK PA10K2 A10K2.u2653 = [0, 742937934308, 3040787558816, 3813502357015, 1639071159739, 231387184689, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u2653 = KTree.node A10K2.t2658 (nat_lit 44647779) (nat_lit 9355842215) (nat_lit 0) A10K2.t2659 from rfl, totK_node, tot2658, tot2659]
  decide +kernel

theorem arows2655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2655 = true := by
  rw [show A10K2.u2655 = KTree.node A10K2.t2660 (nat_lit 44654999) (nat_lit 14568056812) (nat_lit 0) A10K2.t2661 from rfl, allE_node, rows2660, irow2655, rows2661]
  all_goals rfl

theorem atot2655 : totK PA10K2 A10K2.u2655 = [0, 695123071544, 2843720437240, 4008821290846, 2021072354646, 280302480262, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2655 = KTree.node A10K2.t2660 (nat_lit 44654999) (nat_lit 14568056812) (nat_lit 0) A10K2.t2661 from rfl, totK_node, tot2660, tot2661]
  decide +kernel

theorem arows2656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2656 = true := by
  rw [show A10K2.u2656 = KTree.node A10K2.t2662 (nat_lit 44660522) (nat_lit 10194658962) (nat_lit 0) A10K2.t2663 from rfl, allE_node, rows2662, irow2656, rows2663]
  all_goals rfl

theorem atot2656 : totK PA10K2 A10K2.u2656 = [0, 0, 1386915923789, 4305892366628, 3636748363237, 866667093361, 42079891856, 0, 0, 0] := by
  rw [show A10K2.u2656 = KTree.node A10K2.t2662 (nat_lit 44660522) (nat_lit 10194658962) (nat_lit 0) A10K2.t2663 from rfl, totK_node, tot2662, tot2663]
  decide +kernel

theorem arows2659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2659 = true := by
  rw [show A10K2.u2659 = KTree.node A10K2.t2664 (nat_lit 44674441) (nat_lit 5014726663) (nat_lit 0) A10K2.t2665 from rfl, allE_node, rows2664, irow2659, rows2665]
  all_goals rfl

theorem atot2659 : totK PA10K2 A10K2.u2659 = [0, 0, 538210955376, 2640566454164, 4036917042943, 2024917357963, 382927601279, 25565504801, 0, 0] := by
  rw [show A10K2.u2659 = KTree.node A10K2.t2664 (nat_lit 44674441) (nat_lit 5014726663) (nat_lit 0) A10K2.t2665 from rfl, totK_node, tot2664, tot2665]
  decide +kernel

theorem arows2660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2660 = true := by
  rw [show A10K2.u2660 = KTree.node A10K2.t2666 (nat_lit 44679944) (nat_lit 12218103373) (nat_lit 0) A10K2.t2667 from rfl, allE_node, rows2666, irow2660, rows2667]
  all_goals rfl

theorem atot2660 : totK PA10K2 A10K2.u2660 = [0, 0, 742362137899, 2928074884035, 3740148185238, 1720360575587, 247923639678, 5517381808, 0, 0] := by
  rw [show A10K2.u2660 = KTree.node A10K2.t2666 (nat_lit 44679944) (nat_lit 12218103373) (nat_lit 0) A10K2.t2667 from rfl, totK_node, tot2666, tot2667]
  decide +kernel

theorem arows2662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2662 = true := by
  rw [show A10K2.u2662 = KTree.node A10K2.t2668 (nat_lit 44685825) (nat_lit 9518745061) (nat_lit 0) A10K2.t2669 from rfl, allE_node, rows2668, irow2662, rows2669]
  all_goals rfl

theorem atot2662 : totK PA10K2 A10K2.u2662 = [0, 0, 468465284177, 2629802296431, 4327967486417, 1977539766284, 227028873868, 6121173289, 0, 0] := by
  rw [show A10K2.u2662 = KTree.node A10K2.t2668 (nat_lit 44685825) (nat_lit 9518745061) (nat_lit 0) A10K2.t2669 from rfl, totK_node, tot2668, tot2669]
  decide +kernel

theorem arows2663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2663 = true := by
  rw [show A10K2.u2663 = KTree.node A10K2.t2670 (nat_lit 44696352) (nat_lit 13341661698) (nat_lit 0) A10K2.t2671 from rfl, allE_node, rows2670, irow2663, rows2671]
  all_goals rfl

theorem atot2663 : totK PA10K2 A10K2.u2663 = [0, 516552094339, 2332669995983, 3578302137447, 2328327638472, 683620689881, 55419628428, 0, 0, 0] := by
  rw [show A10K2.u2663 = KTree.node A10K2.t2670 (nat_lit 44696352) (nat_lit 13341661698) (nat_lit 0) A10K2.t2671 from rfl, totK_node, tot2670, tot2671]
  decide +kernel

theorem arows2667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2667 = true := by
  rw [show A10K2.u2667 = KTree.node A10K2.t2672 (nat_lit 44705448) (nat_lit 6199736544) (nat_lit 0) A10K2.t2673 from rfl, allE_node, rows2672, irow2667, rows2673]
  all_goals rfl

theorem atot2667 : totK PA10K2 A10K2.u2667 = [0, 789671577276, 2979042892092, 3729613502323, 1806086125662, 300996657597, 10760911071, 0, 0, 0] := by
  rw [show A10K2.u2667 = KTree.node A10K2.t2672 (nat_lit 44705448) (nat_lit 6199736544) (nat_lit 0) A10K2.t2673 from rfl, totK_node, tot2672, tot2673]
  decide +kernel

theorem arows2668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2668 = true := by
  rw [show A10K2.u2668 = KTree.node A10K2.t2674 (nat_lit 44710134) (nat_lit 13253344472) (nat_lit 0) A10K2.t2675 from rfl, allE_node, rows2674, irow2668, rows2675]
  all_goals rfl

theorem atot2668 : totK PA10K2 A10K2.u2668 = [0, 226848922415, 1752740451813, 3930084404082, 3009068862517, 630294314217, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2668 = KTree.node A10K2.t2674 (nat_lit 44710134) (nat_lit 13253344472) (nat_lit 0) A10K2.t2675 from rfl, totK_node, tot2674, tot2675]
  decide +kernel

theorem arows2670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2670 = true := by
  rw [show A10K2.u2670 = KTree.node A10K2.t2676 (nat_lit 44714509) (nat_lit 5801448251) (nat_lit 0) A10K2.t2677 from rfl, allE_node, rows2676, irow2670, rows2677]
  all_goals rfl

theorem atot2670 : totK PA10K2 A10K2.u2670 = [0, 583209941258, 2847482009321, 4140981202345, 1747241704729, 139443496976, 0, 0, 0, 0] := by
  rw [show A10K2.u2670 = KTree.node A10K2.t2676 (nat_lit 44714509) (nat_lit 5801448251) (nat_lit 0) A10K2.t2677 from rfl, totK_node, tot2676, tot2677]
  decide +kernel

theorem arows2671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2671 = true := by
  rw [show A10K2.u2671 = KTree.node A10K2.t2678 (nat_lit 44730533) (nat_lit 7321820484) (nat_lit 0) A10K2.t2679 from rfl, allE_node, rows2678, irow2671, rows2679]
  all_goals rfl

theorem atot2671 : totK PA10K2 A10K2.u2671 = [0, 0, 944849383794, 3583418171206, 3787057400961, 1031272854205, 64029076578, 0, 0, 0] := by
  rw [show A10K2.u2671 = KTree.node A10K2.t2678 (nat_lit 44730533) (nat_lit 7321820484) (nat_lit 0) A10K2.t2679 from rfl, totK_node, tot2678, tot2679]
  decide +kernel

theorem arows2674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2674 = true := by
  rw [show A10K2.u2674 = KTree.node A10K2.t2680 (nat_lit 44744801) (nat_lit 9996329722) (nat_lit 0) A10K2.t2681 from rfl, allE_node, rows2680, irow2674, rows2681]
  all_goals rfl

theorem atot2674 : totK PA10K2 A10K2.u2674 = [0, 0, 1011647671724, 3642762552211, 3793406008374, 1006908456412, 63495312472, 0, 0, 0] := by
  rw [show A10K2.u2674 = KTree.node A10K2.t2680 (nat_lit 44744801) (nat_lit 9996329722) (nat_lit 0) A10K2.t2681 from rfl, totK_node, tot2680, tot2681]
  decide +kernel

theorem arows2675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2675 = true := by
  rw [show A10K2.u2675 = KTree.node A10K2.t2682 (nat_lit 44750179) (nat_lit 9322188191) (nat_lit 0) A10K2.t2683 from rfl, allE_node, rows2682, irow2675, rows2683]
  all_goals rfl

theorem atot2675 : totK PA10K2 A10K2.u2675 = [0, 311517321411, 1197977423115, 2530179886249, 3366098931250, 1679617378936, 265773289542, 6354482628, 0, 0] := by
  rw [show A10K2.u2675 = KTree.node A10K2.t2682 (nat_lit 44750179) (nat_lit 9322188191) (nat_lit 0) A10K2.t2683 from rfl, totK_node, tot2682, tot2683]
  decide +kernel

theorem arows2677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2677 = true := by
  rw [show A10K2.u2677 = KTree.node A10K2.t2684 (nat_lit 44773027) (nat_lit 10267743209) (nat_lit 0) A10K2.t2685 from rfl, allE_node, rows2684, irow2677, rows2685]
  all_goals rfl

theorem atot2677 : totK PA10K2 A10K2.u2677 = [0, 499730976493, 2541257782409, 4147534527620, 2360349360687, 450693966592, 25715051306, 0, 0, 0] := by
  rw [show A10K2.u2677 = KTree.node A10K2.t2684 (nat_lit 44773027) (nat_lit 10267743209) (nat_lit 0) A10K2.t2685 from rfl, totK_node, tot2684, tot2685]
  decide +kernel

theorem arows2678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2678 = true := by
  rw [show A10K2.u2678 = KTree.node A10K2.t2686 (nat_lit 44786967) (nat_lit 10676854008) (nat_lit 0) A10K2.t2687 from rfl, allE_node, rows2686, irow2678, rows2687]
  all_goals rfl

theorem atot2678 : totK PA10K2 A10K2.u2678 = [0, 798450316783, 3150586788700, 4107724972706, 1910953939120, 246381534095, 5807182206, 0, 0, 0] := by
  rw [show A10K2.u2678 = KTree.node A10K2.t2686 (nat_lit 44786967) (nat_lit 10676854008) (nat_lit 0) A10K2.t2687 from rfl, totK_node, tot2686, tot2687]
  decide +kernel

theorem arows2685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2685 = true := by
  rw [show A10K2.u2685 = KTree.node A10K2.t2688 (nat_lit 44792845) (nat_lit 1731163263) (nat_lit 0) A10K2.t2689 from rfl, allE_node, rows2688, irow2685, rows2689]
  all_goals rfl

theorem atot2685 : totK PA10K2 A10K2.u2685 = [0, 0, 1189939393920, 4018616960961, 3903411380786, 1065046480154, 62730155814, 0, 0, 0] := by
  rw [show A10K2.u2685 = KTree.node A10K2.t2688 (nat_lit 44792845) (nat_lit 1731163263) (nat_lit 0) A10K2.t2689 from rfl, totK_node, tot2688, tot2689]
  decide +kernel

theorem arows2686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2686 = true := by
  rw [show A10K2.u2686 = KTree.node A10K2.t2690 (nat_lit 44805690) (nat_lit 11540279771) (nat_lit 0) A10K2.t2691 from rfl, allE_node, rows2690, irow2686, rows2691]
  all_goals rfl

theorem atot2686 : totK PA10K2 A10K2.u2686 = [0, 0, 498848097945, 2717314811217, 4288913735713, 2121426642881, 288813059034, 7047025452, 0, 0] := by
  rw [show A10K2.u2686 = KTree.node A10K2.t2690 (nat_lit 44805690) (nat_lit 11540279771) (nat_lit 0) A10K2.t2691 from rfl, totK_node, tot2690, tot2691]
  decide +kernel

theorem arows2688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2688 = true := by
  rw [show A10K2.u2688 = KTree.node A10K2.t2692 (nat_lit 44820214) (nat_lit 15332984950) (nat_lit 0) A10K2.t2693 from rfl, allE_node, rows2692, irow2688, rows2693]
  all_goals rfl

theorem atot2688 : totK PA10K2 A10K2.u2688 = [0, 213371739588, 1264593433986, 3333487689590, 3865515569159, 1421654194449, 106354319534, 0, 0, 0] := by
  rw [show A10K2.u2688 = KTree.node A10K2.t2692 (nat_lit 44820214) (nat_lit 15332984950) (nat_lit 0) A10K2.t2693 from rfl, totK_node, tot2692, tot2693]
  decide +kernel

theorem arows2689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2689 = true := by
  rw [show A10K2.u2689 = KTree.node A10K2.t2694 (nat_lit 45091889) (nat_lit 9866223381) (nat_lit 0) A10K2.t2695 from rfl, allE_node, rows2694, irow2689, rows2695]
  all_goals rfl

theorem atot2689 : totK PA10K2 A10K2.u2689 = [0, 547634011717, 2632289338306, 3902495805237, 2017237733534, 401565774773, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u2689 = KTree.node A10K2.t2694 (nat_lit 45091889) (nat_lit 9866223381) (nat_lit 0) A10K2.t2695 from rfl, totK_node, tot2694, tot2695]
  decide +kernel

theorem arows2692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2692 = true := by
  rw [show A10K2.u2692 = KTree.node A10K2.t2696 (nat_lit 45105663) (nat_lit 10311184603) (nat_lit 0) A10K2.t2697 from rfl, allE_node, rows2696, irow2692, rows2697]
  all_goals rfl

theorem atot2692 : totK PA10K2 A10K2.u2692 = [0, 778583728134, 2889836014167, 3734003649398, 1867239511026, 258823765116, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u2692 = KTree.node A10K2.t2696 (nat_lit 45105663) (nat_lit 10311184603) (nat_lit 0) A10K2.t2697 from rfl, totK_node, tot2696, tot2697]
  decide +kernel

theorem arows2693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2693 = true := by
  rw [show A10K2.u2693 = KTree.node A10K2.t2698 (nat_lit 45111553) (nat_lit 10064293788) (nat_lit 0) A10K2.t2699 from rfl, allE_node, rows2698, irow2693, rows2699]
  all_goals rfl

theorem atot2693 : totK PA10K2 A10K2.u2693 = [0, 266424507814, 2239022986263, 4346294415303, 2350720624184, 321432103043, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2693 = KTree.node A10K2.t2698 (nat_lit 45111553) (nat_lit 10064293788) (nat_lit 0) A10K2.t2699 from rfl, totK_node, tot2698, tot2699]
  decide +kernel

theorem arows2695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2695 = true := by
  rw [show A10K2.u2695 = KTree.node A10K2.t2700 (nat_lit 45123589) (nat_lit 6786139667) (nat_lit 0) A10K2.t2701 from rfl, allE_node, rows2700, irow2695, rows2701]
  all_goals rfl

theorem atot2695 : totK PA10K2 A10K2.u2695 = [0, 0, 885787242533, 3577873716587, 3992034116920, 1111916942272, 65406092412, 0, 0, 0] := by
  rw [show A10K2.u2695 = KTree.node A10K2.t2700 (nat_lit 45123589) (nat_lit 6786139667) (nat_lit 0) A10K2.t2701 from rfl, totK_node, tot2700, tot2701]
  decide +kernel

theorem arows2696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2696 = true := by
  rw [show A10K2.u2696 = KTree.node A10K2.t2702 (nat_lit 45129088) (nat_lit 15104162539) (nat_lit 0) A10K2.t2703 from rfl, allE_node, rows2702, irow2696, rows2703]
  all_goals rfl

theorem atot2696 : totK PA10K2 A10K2.u2696 = [0, 0, 478777902291, 2308726352295, 3787404030991, 2185101950860, 446711622520, 30220878370, 0, 0] := by
  rw [show A10K2.u2696 = KTree.node A10K2.t2702 (nat_lit 45129088) (nat_lit 15104162539) (nat_lit 0) A10K2.t2703 from rfl, totK_node, tot2702, tot2703]
  decide +kernel

theorem arows2700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2700 = true := by
  rw [show A10K2.u2700 = KTree.node A10K2.t2704 (nat_lit 45143396) (nat_lit 13688968780) (nat_lit 0) A10K2.t2705 from rfl, allE_node, rows2704, irow2700, rows2705]
  all_goals rfl

theorem atot2700 : totK PA10K2 A10K2.u2700 = [0, 0, 545251647197, 2779188101415, 4089841459279, 1745348133279, 213555341488, 5546304973, 0, 0] := by
  rw [show A10K2.u2700 = KTree.node A10K2.t2704 (nat_lit 45143396) (nat_lit 13688968780) (nat_lit 0) A10K2.t2705 from rfl, totK_node, tot2704, tot2705]
  decide +kernel

theorem arows2701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2701 = true := by
  rw [show A10K2.u2701 = KTree.node A10K2.t2706 (nat_lit 45165101) (nat_lit 6488313724) (nat_lit 0) A10K2.t2707 from rfl, allE_node, rows2706, irow2701, rows2707]
  all_goals rfl

theorem atot2701 : totK PA10K2 A10K2.u2701 = [0, 814371176014, 3293384706925, 4030083908562, 1482226414416, 121216759029, 0, 0, 0, 0] := by
  rw [show A10K2.u2701 = KTree.node A10K2.t2706 (nat_lit 45165101) (nat_lit 6488313724) (nat_lit 0) A10K2.t2707 from rfl, totK_node, tot2706, tot2707]
  decide +kernel

theorem arows2703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2703 = true := by
  rw [show A10K2.u2703 = KTree.node A10K2.t2708 (nat_lit 45170116) (nat_lit 11933677) (nat_lit 0) A10K2.t2709 from rfl, allE_node, rows2708, irow2703, rows2709]
  all_goals rfl

theorem atot2703 : totK PA10K2 A10K2.u2703 = [0, 482403941286, 2185732222924, 3670499621575, 2600674931272, 585729197898, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2703 = KTree.node A10K2.t2708 (nat_lit 45170116) (nat_lit 11933677) (nat_lit 0) A10K2.t2709 from rfl, totK_node, tot2708, tot2709]
  decide +kernel

theorem arows2704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2704 = true := by
  rw [show A10K2.u2704 = KTree.node A10K2.t2710 (nat_lit 45176082) (nat_lit 14993366649) (nat_lit 0) A10K2.t2711 from rfl, allE_node, rows2710, irow2704, rows2711]
  all_goals rfl

theorem atot2704 : totK PA10K2 A10K2.u2704 = [0, 582612917173, 2664496107280, 4020306209440, 2031813712268, 281404758551, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2704 = KTree.node A10K2.t2710 (nat_lit 45176082) (nat_lit 14993366649) (nat_lit 0) A10K2.t2711 from rfl, totK_node, tot2710, tot2711]
  decide +kernel

theorem arows2707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2707 = true := by
  rw [show A10K2.u2707 = KTree.node A10K2.t2712 (nat_lit 45184661) (nat_lit 5867099364) (nat_lit 0) A10K2.t2713 from rfl, allE_node, rows2712, irow2707, rows2713]
  all_goals rfl

theorem atot2707 : totK PA10K2 A10K2.u2707 = [0, 218175288971, 1915118634121, 4368281296634, 3082678829668, 543750290902, 12926121504, 0, 0, 0] := by
  rw [show A10K2.u2707 = KTree.node A10K2.t2712 (nat_lit 45184661) (nat_lit 5867099364) (nat_lit 0) A10K2.t2713 from rfl, totK_node, tot2712, tot2713]
  decide +kernel

theorem arows2708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2708 = true := by
  rw [show A10K2.u2708 = KTree.node A10K2.t2714 (nat_lit 45198996) (nat_lit 10746150214) (nat_lit 0) A10K2.t2715 from rfl, allE_node, rows2714, irow2708, rows2715]
  all_goals rfl

theorem atot2708 : totK PA10K2 A10K2.u2708 = [0, 0, 502246750619, 2592389518424, 4044750361414, 1966766479472, 342564694874, 25130442608, 0, 0] := by
  rw [show A10K2.u2708 = KTree.node A10K2.t2714 (nat_lit 45198996) (nat_lit 10746150214) (nat_lit 0) A10K2.t2715 from rfl, totK_node, tot2714, tot2715]
  decide +kernel

theorem arows2710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2710 = true := by
  rw [show A10K2.u2710 = KTree.node A10K2.t2716 (nat_lit 45204893) (nat_lit 5236069125) (nat_lit 0) A10K2.t2717 from rfl, allE_node, rows2716, irow2710, rows2717]
  all_goals rfl

theorem atot2710 : totK PA10K2 A10K2.u2710 = [0, 0, 777042948740, 3177934321480, 3836491358884, 1488984159889, 185642791286, 5517381808, 0, 0] := by
  rw [show A10K2.u2710 = KTree.node A10K2.t2716 (nat_lit 45204893) (nat_lit 5236069125) (nat_lit 0) A10K2.t2717 from rfl, totK_node, tot2716, tot2717]
  decide +kernel

theorem arows2711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2711 = true := by
  rw [show A10K2.u2711 = KTree.node A10K2.t2718 (nat_lit 45212890) (nat_lit 14138365153) (nat_lit 0) A10K2.t2719 from rfl, allE_node, rows2718, irow2711, rows2719]
  all_goals rfl

theorem atot2711 : totK PA10K2 A10K2.u2711 = [0, 162078939081, 864652973038, 2674173632631, 3941895172757, 1833238487260, 234419349755, 6121173289, 0, 0] := by
  rw [show A10K2.u2711 = KTree.node A10K2.t2718 (nat_lit 45212890) (nat_lit 14138365153) (nat_lit 0) A10K2.t2719 from rfl, totK_node, tot2718, tot2719]
  decide +kernel

theorem arows2716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2716 = true := by
  rw [show A10K2.u2716 = KTree.node A10K2.t2720 (nat_lit 45222919) (nat_lit 13239498858) (nat_lit 0) A10K2.t2721 from rfl, allE_node, rows2720, irow2716, rows2721]
  all_goals rfl

theorem atot2716 : totK PA10K2 A10K2.u2716 = [0, 534545079617, 2544219667764, 3752054129922, 1962361631845, 370500585815, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u2716 = KTree.node A10K2.t2720 (nat_lit 45222919) (nat_lit 13239498858) (nat_lit 0) A10K2.t2721 from rfl, totK_node, tot2720, tot2721]
  decide +kernel

theorem arows2717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2717 = true := by
  rw [show A10K2.u2717 = KTree.node A10K2.t2722 (nat_lit 45229805) (nat_lit 5399166982) (nat_lit 0) A10K2.t2723 from rfl, allE_node, rows2722, irow2717, rows2723]
  all_goals rfl

theorem atot2717 : totK PA10K2 A10K2.u2717 = [0, 745920107432, 3007787921648, 3868843039723, 1701385181787, 202865968225, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u2717 = KTree.node A10K2.t2722 (nat_lit 45229805) (nat_lit 5399166982) (nat_lit 0) A10K2.t2723 from rfl, totK_node, tot2722, tot2723]
  decide +kernel

theorem arows2719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2719 = true := by
  rw [show A10K2.u2719 = KTree.node A10K2.t2724 (nat_lit 45234725) (nat_lit 7243941307) (nat_lit 0) A10K2.t2725 from rfl, allE_node, rows2724, irow2719, rows2725]
  all_goals rfl

theorem atot2719 : totK PA10K2 A10K2.u2719 = [0, 374286759930, 1918429011340, 3765409320600, 2798910742478, 561534993927, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2719 = KTree.node A10K2.t2724 (nat_lit 45234725) (nat_lit 7243941307) (nat_lit 0) A10K2.t2725 from rfl, totK_node, tot2724, tot2725]
  decide +kernel

theorem arows2720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2720 = true := by
  rw [show A10K2.u2720 = KTree.node A10K2.t2726 (nat_lit 45239063) (nat_lit 6860392242) (nat_lit 0) A10K2.t2727 from rfl, allE_node, rows2726, irow2720, rows2727]
  all_goals rfl

theorem atot2720 : totK PA10K2 A10K2.u2720 = [0, 474263259421, 2782447843151, 4327685197517, 1780526108748, 140464755192, 0, 0, 0, 0] := by
  rw [show A10K2.u2720 = KTree.node A10K2.t2726 (nat_lit 45239063) (nat_lit 6860392242) (nat_lit 0) A10K2.t2727 from rfl, totK_node, tot2726, tot2727]
  decide +kernel

theorem arows2723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2723 = true := by
  rw [show A10K2.u2723 = KTree.node A10K2.t2728 (nat_lit 45254869) (nat_lit 6356134920) (nat_lit 0) A10K2.t2729 from rfl, allE_node, rows2728, irow2723, rows2729]
  all_goals rfl

theorem atot2723 : totK PA10K2 A10K2.u2723 = [0, 0, 985936629379, 3650355401283, 3727670583897, 895413543498, 44706613546, 0, 0, 0] := by
  rw [show A10K2.u2723 = KTree.node A10K2.t2728 (nat_lit 45254869) (nat_lit 6356134920) (nat_lit 0) A10K2.t2729 from rfl, totK_node, tot2728, tot2729]
  decide +kernel

theorem arows2724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2724 = true := by
  rw [show A10K2.u2724 = KTree.node A10K2.t2730 (nat_lit 45264549) (nat_lit 6485606707) (nat_lit 0) A10K2.t2731 from rfl, allE_node, rows2730, irow2724, rows2731]
  all_goals rfl

theorem atot2724 : totK PA10K2 A10K2.u2724 = [0, 0, 986622330448, 3632110888507, 3815570985437, 972305428209, 63640705285, 0, 0, 0] := by
  rw [show A10K2.u2724 = KTree.node A10K2.t2730 (nat_lit 45264549) (nat_lit 6485606707) (nat_lit 0) A10K2.t2731 from rfl, totK_node, tot2730, tot2731]
  decide +kernel

theorem arows2726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2726 = true := by
  rw [show A10K2.u2726 = KTree.node A10K2.t2732 (nat_lit 45273444) (nat_lit 13775768551) (nat_lit 0) A10K2.t2733 from rfl, allE_node, rows2732, irow2726, rows2733]
  all_goals rfl

theorem atot2726 : totK PA10K2 A10K2.u2726 = [0, 0, 464498052187, 2496662937056, 4083280001793, 1970434179893, 291306829918, 6354482628, 0, 0] := by
  rw [show A10K2.u2726 = KTree.node A10K2.t2732 (nat_lit 45273444) (nat_lit 13775768551) (nat_lit 0) A10K2.t2733 from rfl, totK_node, tot2732, tot2733]
  decide +kernel

theorem arows2727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2727 = true := by
  rw [show A10K2.u2727 = KTree.node A10K2.t2734 (nat_lit 45353837) (nat_lit 6354603908) (nat_lit 0) A10K2.t2735 from rfl, allE_node, rows2734, irow2727, rows2735]
  all_goals rfl

theorem atot2727 : totK PA10K2 A10K2.u2727 = [0, 0, 602760228364, 2765871732957, 3912784704690, 1827806513888, 316490265446, 24941563133, 0, 0] := by
  rw [show A10K2.u2727 = KTree.node A10K2.t2734 (nat_lit 45353837) (nat_lit 6354603908) (nat_lit 0) A10K2.t2735 from rfl, totK_node, tot2734, tot2735]
  decide +kernel

theorem arows2731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2731 = true := by
  rw [show A10K2.u2731 = KTree.node A10K2.t2736 (nat_lit 45367870) (nat_lit 13862171569) (nat_lit 0) A10K2.t2737 from rfl, allE_node, rows2736, irow2731, rows2737]
  all_goals rfl

theorem atot2731 : totK PA10K2 A10K2.u2731 = [0, 0, 773650122319, 2986458897085, 3735961433199, 1673354702635, 220572656674, 5447185874, 0, 0] := by
  rw [show A10K2.u2731 = KTree.node A10K2.t2736 (nat_lit 45367870) (nat_lit 13862171569) (nat_lit 0) A10K2.t2737 from rfl, totK_node, tot2736, tot2737]
  decide +kernel

theorem arows2732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2732 = true := by
  rw [show A10K2.u2732 = KTree.node A10K2.t2738 (nat_lit 45373783) (nat_lit 3934686242) (nat_lit 0) A10K2.t2739 from rfl, allE_node, rows2738, irow2732, rows2739]
  all_goals rfl

theorem atot2732 : totK PA10K2 A10K2.u2732 = [0, 0, 480593849206, 2511107465267, 4083318232650, 2083720159066, 299643189944, 6354482628, 0, 0] := by
  rw [show A10K2.u2732 = KTree.node A10K2.t2738 (nat_lit 45373783) (nat_lit 3934686242) (nat_lit 0) A10K2.t2739 from rfl, totK_node, tot2738, tot2739]
  decide +kernel

theorem arows2734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2734 = true := by
  rw [show A10K2.u2734 = KTree.node A10K2.t2740 (nat_lit 45427891) (nat_lit 10186011321) (nat_lit 0) A10K2.t2741 from rfl, allE_node, rows2740, irow2734, rows2741]
  all_goals rfl

theorem atot2734 : totK PA10K2 A10K2.u2734 = [0, 0, 598710966618, 2740002936948, 4006762546317, 1874245508043, 324870988370, 25299471099, 0, 0] := by
  rw [show A10K2.u2734 = KTree.node A10K2.t2740 (nat_lit 45427891) (nat_lit 10186011321) (nat_lit 0) A10K2.t2741 from rfl, totK_node, tot2740, tot2741]
  decide +kernel

theorem arows2735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2735 = true := by
  rw [show A10K2.u2735 = KTree.node A10K2.t2742 (nat_lit 45433629) (nat_lit 6017451388) (nat_lit 0) A10K2.t2743 from rfl, allE_node, rows2742, irow2735, rows2743]
  all_goals rfl

theorem atot2735 : totK PA10K2 A10K2.u2735 = [0, 0, 775529322910, 3019694783431, 3743507404570, 1691867341098, 223753067196, 5718040558, 0, 0] := by
  rw [show A10K2.u2735 = KTree.node A10K2.t2742 (nat_lit 45433629) (nat_lit 6017451388) (nat_lit 0) A10K2.t2743 from rfl, totK_node, tot2742, tot2743]
  decide +kernel

theorem arows2738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2738 = true := by
  rw [show A10K2.u2738 = KTree.node A10K2.t2744 (nat_lit 45439267) (nat_lit 10039663998) (nat_lit 0) A10K2.t2745 from rfl, allE_node, rows2744, irow2738, rows2745]
  all_goals rfl

theorem atot2738 : totK PA10K2 A10K2.u2738 = [0, 0, 485543652834, 2492139093253, 4194367451045, 2121722678615, 300138146545, 6354482628, 0, 0] := by
  rw [show A10K2.u2738 = KTree.node A10K2.t2744 (nat_lit 45439267) (nat_lit 10039663998) (nat_lit 0) A10K2.t2745 from rfl, totK_node, tot2744, tot2745]
  decide +kernel

theorem arows2739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2739 = true := by
  rw [show A10K2.u2739 = KTree.node A10K2.t2746 (nat_lit 45484202) (nat_lit 12445260178) (nat_lit 0) A10K2.t2747 from rfl, allE_node, rows2746, irow2739, rows2747]
  all_goals rfl

theorem atot2739 : totK PA10K2 A10K2.u2739 = [0, 0, 694239297347, 3148517304328, 4040189745093, 1375997447793, 98535429315, 0, 0, 0] := by
  rw [show A10K2.u2739 = KTree.node A10K2.t2746 (nat_lit 45484202) (nat_lit 12445260178) (nat_lit 0) A10K2.t2747 from rfl, totK_node, tot2746, tot2747]
  decide +kernel

theorem arows2741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2741 = true := by
  rw [show A10K2.u2741 = KTree.node A10K2.t2748 (nat_lit 45491492) (nat_lit 13742643306) (nat_lit 0) A10K2.t2749 from rfl, allE_node, rows2748, irow2741, rows2749]
  all_goals rfl

theorem atot2741 : totK PA10K2 A10K2.u2741 = [0, 0, 642894642644, 2594752317119, 3622342599572, 1951292933151, 415903726467, 30074883546, 0, 0] := by
  rw [show A10K2.u2741 = KTree.node A10K2.t2748 (nat_lit 45491492) (nat_lit 13742643306) (nat_lit 0) A10K2.t2749 from rfl, totK_node, tot2748, tot2749]
  decide +kernel

theorem arows2742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2742 = true := by
  rw [show A10K2.u2742 = KTree.node A10K2.t2750 (nat_lit 45496566) (nat_lit 11641385671) (nat_lit 0) A10K2.t2751 from rfl, allE_node, rows2750, irow2742, rows2751]
  all_goals rfl

theorem atot2742 : totK PA10K2 A10K2.u2742 = [0, 0, 364280787783, 2109512307503, 3878591178081, 2375732094632, 491277568576, 31003444686, 0, 0] := by
  rw [show A10K2.u2742 = KTree.node A10K2.t2750 (nat_lit 45496566) (nat_lit 11641385671) (nat_lit 0) A10K2.t2751 from rfl, totK_node, tot2750, tot2751]
  decide +kernel

theorem arows2748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2748 = true := by
  rw [show A10K2.u2748 = KTree.node A10K2.t2752 (nat_lit 45501084) (nat_lit 11847789036) (nat_lit 0) A10K2.t2753 from rfl, allE_node, rows2752, irow2748, rows2753]
  all_goals rfl

theorem atot2748 : totK PA10K2 A10K2.u2748 = [0, 0, 577154384443, 2903948845714, 4136678275494, 1621317710032, 138456623420, 0, 0, 0] := by
  rw [show A10K2.u2748 = KTree.node A10K2.t2752 (nat_lit 45501084) (nat_lit 11847789036) (nat_lit 0) A10K2.t2753 from rfl, totK_node, tot2752, tot2753]
  decide +kernel

theorem arows2749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2749 = true := by
  rw [show A10K2.u2749 = KTree.node A10K2.t2754 (nat_lit 45516960) (nat_lit 9074948959) (nat_lit 0) A10K2.t2755 from rfl, allE_node, rows2754, irow2749, rows2755]
  all_goals rfl

theorem atot2749 : totK PA10K2 A10K2.u2749 = [0, 0, 0, 1020512991679, 3777624774510, 3406186747066, 863644248879, 57372072225, 0, 0] := by
  rw [show A10K2.u2749 = KTree.node A10K2.t2754 (nat_lit 45516960) (nat_lit 9074948959) (nat_lit 0) A10K2.t2755 from rfl, totK_node, tot2754, tot2755]
  decide +kernel

theorem arows2751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2751 = true := by
  rw [show A10K2.u2751 = KTree.node A10K2.t2756 (nat_lit 45531532) (nat_lit 8984221948) (nat_lit 0) A10K2.t2757 from rfl, allE_node, rows2756, irow2751, rows2757]
  all_goals rfl

theorem atot2751 : totK PA10K2 A10K2.u2751 = [0, 0, 0, 1164259384918, 3709236714952, 3296928660264, 894535529376, 61975941459, 0, 0] := by
  rw [show A10K2.u2751 = KTree.node A10K2.t2756 (nat_lit 45531532) (nat_lit 8984221948) (nat_lit 0) A10K2.t2757 from rfl, totK_node, tot2756, tot2757]
  decide +kernel

theorem arows2752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2752 = true := by
  rw [show A10K2.u2752 = KTree.node A10K2.t2758 (nat_lit 45537429) (nat_lit 6840212376) (nat_lit 0) A10K2.t2759 from rfl, allE_node, rows2758, irow2752, rows2759]
  all_goals rfl

theorem atot2752 : totK PA10K2 A10K2.u2752 = [317619887890, 1050935918641, 1065760272256, 442836734616, 1483946118219, 2977446566964, 1629215267000, 265614550179, 6354482628, 0] := by
  rw [show A10K2.u2752 = KTree.node A10K2.t2758 (nat_lit 45537429) (nat_lit 6840212376) (nat_lit 0) A10K2.t2759 from rfl, totK_node, tot2758, tot2759]
  decide +kernel

theorem arows2755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2755 = true := by
  rw [show A10K2.u2755 = KTree.node A10K2.t2760 (nat_lit 46141147) (nat_lit 5546299430) (nat_lit 0) A10K2.t2761 from rfl, allE_node, rows2760, irow2755, rows2761]
  all_goals rfl

theorem atot2755 : totK PA10K2 A10K2.u2755 = [527099952449, 2587534280637, 3983681691365, 2170532921893, 416692078299, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u2755 = KTree.node A10K2.t2760 (nat_lit 46141147) (nat_lit 5546299430) (nat_lit 0) A10K2.t2761 from rfl, totK_node, tot2760, tot2761]
  decide +kernel

theorem arows2756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2756 = true := by
  rw [show A10K2.u2756 = KTree.node A10K2.t2762 (nat_lit 46154503) (nat_lit 9283655666) (nat_lit 0) A10K2.t2763 from rfl, allE_node, rows2762, irow2756, rows2763]
  all_goals rfl

theorem atot2756 : totK PA10K2 A10K2.u2756 = [560480332012, 2693372887702, 4087943222815, 2054505729990, 260117293925, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u2756 = KTree.node A10K2.t2762 (nat_lit 46154503) (nat_lit 9283655666) (nat_lit 0) A10K2.t2763 from rfl, totK_node, tot2762, tot2763]
  decide +kernel

theorem arows2758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2758 = true := by
  rw [show A10K2.u2758 = KTree.node A10K2.t2764 (nat_lit 46162822) (nat_lit 15721197482) (nat_lit 0) A10K2.t2765 from rfl, allE_node, rows2764, irow2758, rows2765]
  all_goals rfl

theorem atot2758 : totK PA10K2 A10K2.u2758 = [800656750727, 3089977328313, 3958812179078, 1777940802463, 261025094270, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2758 = KTree.node A10K2.t2764 (nat_lit 46162822) (nat_lit 15721197482) (nat_lit 0) A10K2.t2765 from rfl, totK_node, tot2764, tot2765]
  decide +kernel

theorem arows2759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2759 = true := by
  rw [show A10K2.u2759 = KTree.node A10K2.t2766 (nat_lit 46169096) (nat_lit 14297581217) (nat_lit 0) A10K2.t2767 from rfl, allE_node, rows2766, irow2759, rows2767]
  all_goals rfl

theorem atot2759 : totK PA10K2 A10K2.u2759 = [0, 1146236511687, 3936010887287, 3877280458591, 1051017863380, 62915010970, 0, 0, 0, 0] := by
  rw [show A10K2.u2759 = KTree.node A10K2.t2766 (nat_lit 46169096) (nat_lit 14297581217) (nat_lit 0) A10K2.t2767 from rfl, totK_node, tot2766, tot2767]
  decide +kernel

theorem arows2763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2763 = true := by
  rw [show A10K2.u2763 = KTree.node A10K2.t2768 (nat_lit 46173627) (nat_lit 6474745540) (nat_lit 0) A10K2.t2769 from rfl, allE_node, rows2768, irow2763, rows2769]
  all_goals rfl

theorem atot2763 : totK PA10K2 A10K2.u2763 = [0, 526397487994, 2637728349850, 4021260684046, 2008302443967, 390426446666, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u2763 = KTree.node A10K2.t2768 (nat_lit 46173627) (nat_lit 6474745540) (nat_lit 0) A10K2.t2769 from rfl, totK_node, tot2768, tot2769]
  decide +kernel

theorem arows2764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2764 = true := by
  rw [show A10K2.u2764 = KTree.node A10K2.t2770 (nat_lit 46187013) (nat_lit 6386651307) (nat_lit 0) A10K2.t2771 from rfl, allE_node, rows2770, irow2764, rows2771]
  all_goals rfl

theorem atot2764 : totK PA10K2 A10K2.u2764 = [0, 558424267006, 2662919569553, 4000464198816, 1943963484109, 249180608034, 5410721913, 0, 0, 0] := by
  rw [show A10K2.u2764 = KTree.node A10K2.t2770 (nat_lit 46187013) (nat_lit 6386651307) (nat_lit 0) A10K2.t2771 from rfl, totK_node, tot2770, tot2771]
  decide +kernel

theorem arows2766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2766 = true := by
  rw [show A10K2.u2766 = KTree.node A10K2.t2772 (nat_lit 46195312) (nat_lit 14537219996) (nat_lit 0) A10K2.t2773 from rfl, allE_node, rows2772, irow2766, rows2773]
  all_goals rfl

theorem atot2766 : totK PA10K2 A10K2.u2766 = [0, 798956649672, 3145446373234, 4042936033559, 1693212810248, 199998203163, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u2766 = KTree.node A10K2.t2772 (nat_lit 46195312) (nat_lit 14537219996) (nat_lit 0) A10K2.t2773 from rfl, totK_node, tot2772, tot2773]
  decide +kernel

theorem arows2767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2767 = true := by
  rw [show A10K2.u2767 = KTree.node A10K2.t2774 (nat_lit 46336557) (nat_lit 6473004654) (nat_lit 0) A10K2.t2775 from rfl, allE_node, rows2774, irow2767, rows2775]
  all_goals rfl

theorem atot2767 : totK PA10K2 A10K2.u2767 = [783941292525, 3112511712472, 3869069552777, 1718324127242, 363658291365, 37646807062, 0, 0, 0, 0] := by
  rw [show A10K2.u2767 = KTree.node A10K2.t2774 (nat_lit 46336557) (nat_lit 6473004654) (nat_lit 0) A10K2.t2775 from rfl, totK_node, tot2774, tot2775]
  decide +kernel

theorem arows2770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2770 = true := by
  rw [show A10K2.u2770 = KTree.node A10K2.t2776 (nat_lit 46341625) (nat_lit 6324186901) (nat_lit 0) A10K2.t2777 from rfl, allE_node, rows2776, irow2770, rows2777]
  all_goals rfl

theorem atot2770 : totK PA10K2 A10K2.u2770 = [594570731468, 2502214583403, 3880195347265, 2475881182185, 533377471677, 30810868011, 0, 0, 0, 0] := by
  rw [show A10K2.u2770 = KTree.node A10K2.t2776 (nat_lit 46341625) (nat_lit 6324186901) (nat_lit 0) A10K2.t2777 from rfl, totK_node, tot2776, tot2777]
  decide +kernel

theorem arows2771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2771 = true := by
  rw [show A10K2.u2771 = KTree.node A10K2.t2778 (nat_lit 46349703) (nat_lit 14613679133) (nat_lit 0) A10K2.t2779 from rfl, allE_node, rows2778, irow2771, rows2779]
  all_goals rfl

theorem atot2771 : totK PA10K2 A10K2.u2771 = [539000210498, 2574257579500, 4095152291842, 2399414284615, 457498833087, 25581633552, 0, 0, 0, 0] := by
  rw [show A10K2.u2771 = KTree.node A10K2.t2778 (nat_lit 46349703) (nat_lit 14613679133) (nat_lit 0) A10K2.t2779 from rfl, totK_node, tot2778, tot2779]
  decide +kernel

theorem arows2773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2773 = true := by
  rw [show A10K2.u2773 = KTree.node A10K2.t2780 (nat_lit 46362695) (nat_lit 11122647682) (nat_lit 0) A10K2.t2781 from rfl, allE_node, rows2780, irow2773, rows2781]
  all_goals rfl

theorem atot2773 : totK PA10K2 A10K2.u2773 = [327737319032, 2058044318598, 4138939540657, 2896299621356, 555882314379, 13816090359, 0, 0, 0, 0] := by
  rw [show A10K2.u2773 = KTree.node A10K2.t2780 (nat_lit 46362695) (nat_lit 11122647682) (nat_lit 0) A10K2.t2781 from rfl, totK_node, tot2780, tot2781]
  decide +kernel

theorem arows2774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2774 = true := by
  rw [show A10K2.u2774 = KTree.node A10K2.t2782 (nat_lit 46367282) (nat_lit 9644579791) (nat_lit 0) A10K2.t2783 from rfl, allE_node, rows2782, irow2774, rows2783]
  all_goals rfl

theorem atot2774 : totK PA10K2 A10K2.u2774 = [0, 1005783725496, 3647706995745, 3943101930889, 1237522490728, 87056475289, 0, 0, 0, 0] := by
  rw [show A10K2.u2774 = KTree.node A10K2.t2782 (nat_lit 46367282) (nat_lit 9644579791) (nat_lit 0) A10K2.t2783 from rfl, totK_node, tot2782, tot2783]
  decide +kernel

theorem arows2779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2779 = true := by
  rw [show A10K2.u2779 = KTree.node A10K2.t2784 (nat_lit 46373951) (nat_lit 14140654769) (nat_lit 0) A10K2.t2785 from rfl, allE_node, rows2784, irow2779, rows2785]
  all_goals rfl

theorem atot2779 : totK PA10K2 A10K2.u2779 = [0, 474622751017, 2447555459303, 4217576022387, 2424413028961, 355227708527, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u2779 = KTree.node A10K2.t2784 (nat_lit 46373951) (nat_lit 14140654769) (nat_lit 0) A10K2.t2785 from rfl, totK_node, tot2784, tot2785]
  decide +kernel

theorem arows2780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2780 = true := by
  rw [show A10K2.u2780 = KTree.node A10K2.t2786 (nat_lit 46380984) (nat_lit 8095560237) (nat_lit 0) A10K2.t2787 from rfl, allE_node, rows2786, irow2780, rows2787]
  all_goals rfl

theorem atot2780 : totK PA10K2 A10K2.u2780 = [0, 508451460378, 2563340325584, 4211448041762, 2394621197243, 339196577975, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u2780 = KTree.node A10K2.t2786 (nat_lit 46380984) (nat_lit 8095560237) (nat_lit 0) A10K2.t2787 from rfl, totK_node, tot2786, tot2787]
  decide +kernel

theorem arows2782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2782 = true := by
  rw [show A10K2.u2782 = KTree.node A10K2.t2788 (nat_lit 46395282) (nat_lit 15002957260) (nat_lit 0) A10K2.t2789 from rfl, allE_node, rows2788, irow2782, rows2789]
  all_goals rfl

theorem atot2782 : totK PA10K2 A10K2.u2782 = [0, 476398299135, 2433240904256, 4084972485379, 2537751984749, 404296096734, 12224107035, 0, 0, 0] := by
  rw [show A10K2.u2782 = KTree.node A10K2.t2788 (nat_lit 46395282) (nat_lit 15002957260) (nat_lit 0) A10K2.t2789 from rfl, totK_node, tot2788, tot2789]
  decide +kernel

theorem arows2783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2783 = true := by
  rw [show A10K2.u2783 = KTree.node A10K2.t2790 (nat_lit 46399853) (nat_lit 6364409994) (nat_lit 0) A10K2.t2791 from rfl, allE_node, rows2790, irow2783, rows2791]
  all_goals rfl

theorem atot2783 : totK PA10K2 A10K2.u2783 = [0, 701419322423, 2675363007911, 3575505726698, 2144315939506, 597429234900, 48886019071, 0, 0, 0] := by
  rw [show A10K2.u2783 = KTree.node A10K2.t2790 (nat_lit 46399853) (nat_lit 6364409994) (nat_lit 0) A10K2.t2791 from rfl, totK_node, tot2790, tot2791]
  decide +kernel

theorem arows2786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2786 = true := by
  rw [show A10K2.u2786 = KTree.node A10K2.t2792 (nat_lit 46404380) (nat_lit 9640230043) (nat_lit 0) A10K2.t2793 from rfl, allE_node, rows2792, irow2786, rows2793]
  all_goals rfl

theorem atot2786 : totK PA10K2 A10K2.u2786 = [0, 256867394879, 1852444194355, 4024062237320, 2896235607854, 585145896603, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2786 = KTree.node A10K2.t2792 (nat_lit 46404380) (nat_lit 9640230043) (nat_lit 0) A10K2.t2793 from rfl, totK_node, tot2792, tot2793]
  decide +kernel

theorem arows2787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2787 = true := by
  rw [show A10K2.u2787 = KTree.node A10K2.t2794 (nat_lit 46419980) (nat_lit 11556653982) (nat_lit 0) A10K2.t2795 from rfl, allE_node, rows2794, irow2787, rows2795]
  all_goals rfl

theorem atot2787 : totK PA10K2 A10K2.u2787 = [0, 670628535449, 2837652523405, 3948245198400, 1817236387764, 219992518247, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u2787 = KTree.node A10K2.t2794 (nat_lit 46419980) (nat_lit 11556653982) (nat_lit 0) A10K2.t2795 from rfl, totK_node, tot2794, tot2795]
  decide +kernel

theorem arows2789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2789 = true := by
  rw [show A10K2.u2789 = KTree.node A10K2.t2796 (nat_lit 46427583) (nat_lit 14319036847) (nat_lit 0) A10K2.t2797 from rfl, allE_node, rows2796, irow2789, rows2797]
  all_goals rfl

theorem atot2789 : totK PA10K2 A10K2.u2789 = [0, 576941670327, 2779022480602, 4252248183630, 2215351282110, 317798634391, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u2789 = KTree.node A10K2.t2796 (nat_lit 46427583) (nat_lit 14319036847) (nat_lit 0) A10K2.t2797 from rfl, totK_node, tot2796, tot2797]
  decide +kernel

theorem arows2790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2790 = true := by
  rw [show A10K2.u2790 = KTree.node A10K2.t2798 (nat_lit 46432648) (nat_lit 14332909434) (nat_lit 0) A10K2.t2799 from rfl, allE_node, rows2798, irow2790, rows2799]
  all_goals rfl

theorem atot2790 : totK PA10K2 A10K2.u2790 = [0, 0, 1143207909887, 3860399524640, 3704221806395, 959325418454, 59400237386, 0, 0, 0] := by
  rw [show A10K2.u2790 = KTree.node A10K2.t2798 (nat_lit 46432648) (nat_lit 14332909434) (nat_lit 0) A10K2.t2799 from rfl, totK_node, tot2798, tot2799]
  decide +kernel

theorem arows2794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2794 = true := by
  rw [show A10K2.u2794 = KTree.node A10K2.t2800 (nat_lit 46437305) (nat_lit 6469135702) (nat_lit 0) A10K2.t2801 from rfl, allE_node, rows2800, irow2794, rows2801]
  all_goals rfl

theorem atot2794 : totK PA10K2 A10K2.u2794 = [0, 0, 398309320664, 2119097885160, 3746275554630, 2508224916389, 544436471612, 30605747850, 0, 0] := by
  rw [show A10K2.u2794 = KTree.node A10K2.t2800 (nat_lit 46437305) (nat_lit 6469135702) (nat_lit 0) A10K2.t2801 from rfl, totK_node, tot2800, tot2801]
  decide +kernel

theorem arows2795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2795 = true := by
  rw [show A10K2.u2795 = KTree.node A10K2.t2802 (nat_lit 46453060) (nat_lit 12564045994) (nat_lit 0) A10K2.t2803 from rfl, allE_node, rows2802, irow2795, rows2803]
  all_goals rfl

theorem atot2795 : totK PA10K2 A10K2.u2795 = [0, 0, 560945273366, 2738579638679, 4061841715169, 1763336170856, 216690311606, 5528811039, 0, 0] := by
  rw [show A10K2.u2795 = KTree.node A10K2.t2802 (nat_lit 46453060) (nat_lit 12564045994) (nat_lit 0) A10K2.t2803 from rfl, totK_node, tot2802, tot2803]
  decide +kernel

theorem arows2797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2797 = true := by
  rw [show A10K2.u2797 = KTree.node A10K2.t2804 (nat_lit 46596197) (nat_lit 6793233870) (nat_lit 0) A10K2.t2805 from rfl, allE_node, rows2804, irow2797, rows2805]
  all_goals rfl

theorem atot2797 : totK PA10K2 A10K2.u2797 = [0, 665606867905, 2669383209223, 3742328858557, 2311931307816, 564986652201, 43911449185, 0, 0, 0] := by
  rw [show A10K2.u2797 = KTree.node A10K2.t2804 (nat_lit 46596197) (nat_lit 6793233870) (nat_lit 0) A10K2.t2805 from rfl, totK_node, tot2804, tot2805]
  decide +kernel

theorem arows2798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2798 = true := by
  rw [show A10K2.u2798 = KTree.node A10K2.t2806 (nat_lit 46601000) (nat_lit 12125181710) (nat_lit 0) A10K2.t2807 from rfl, allE_node, rows2806, irow2798, rows2807]
  all_goals rfl

theorem atot2798 : totK PA10K2 A10K2.u2798 = [0, 405596897910, 2361694757936, 4169074527925, 2488878773757, 461086865011, 25313348169, 0, 0, 0] := by
  rw [show A10K2.u2798 = KTree.node A10K2.t2806 (nat_lit 46601000) (nat_lit 12125181710) (nat_lit 0) A10K2.t2807 from rfl, totK_node, tot2806, tot2807]
  decide +kernel

theorem arows2801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2801 = true := by
  rw [show A10K2.u2801 = KTree.node A10K2.t2808 (nat_lit 46609698) (nat_lit 13708722487) (nat_lit 0) A10K2.t2809 from rfl, allE_node, rows2808, irow2801, rows2809]
  all_goals rfl

theorem atot2801 : totK PA10K2 A10K2.u2801 = [0, 591458955066, 2674260355761, 4183387234916, 2392771408458, 348914791560, 7151180950, 0, 0, 0] := by
  rw [show A10K2.u2801 = KTree.node A10K2.t2808 (nat_lit 46609698) (nat_lit 13708722487) (nat_lit 0) A10K2.t2809 from rfl, totK_node, tot2808, tot2809]
  decide +kernel

theorem arows2802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2802 = true := by
  rw [show A10K2.u2802 = KTree.node A10K2.t2810 (nat_lit 46624147) (nat_lit 10296413891) (nat_lit 0) A10K2.t2811 from rfl, allE_node, rows2810, irow2802, rows2811]
  all_goals rfl

theorem atot2802 : totK PA10K2 A10K2.u2802 = [0, 582309330060, 2724851322812, 4171083784877, 2178544413540, 320904777159, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u2802 = KTree.node A10K2.t2810 (nat_lit 46624147) (nat_lit 10296413891) (nat_lit 0) A10K2.t2811 from rfl, totK_node, tot2810, tot2811]
  decide +kernel

theorem arows2804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2804 = true := by
  rw [show A10K2.u2804 = KTree.node A10K2.t2812 (nat_lit 46628742) (nat_lit 15945280963) (nat_lit 0) A10K2.t2813 from rfl, allE_node, rows2812, irow2804, rows2813]
  all_goals rfl

theorem atot2804 : totK PA10K2 A10K2.u2804 = [555041905076, 1680731194753, 2097362270384, 2469454971850, 2304105743344, 733817356536, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u2804 = KTree.node A10K2.t2812 (nat_lit 46628742) (nat_lit 15945280963) (nat_lit 0) A10K2.t2813 from rfl, totK_node, tot2812, tot2813]
  decide +kernel

theorem arows2805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2805 = true := by
  rw [show A10K2.u2805 = KTree.node A10K2.t2814 (nat_lit 46740716) (nat_lit 11455311571) (nat_lit 0) A10K2.t2815 from rfl, allE_node, rows2814, irow2805, rows2815]
  all_goals rfl

theorem atot2805 : totK PA10K2 A10K2.u2805 = [306854769851, 2060011437625, 3966121251271, 2738646375779, 580593839568, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2805 = KTree.node A10K2.t2814 (nat_lit 46740716) (nat_lit 11455311571) (nat_lit 0) A10K2.t2815 from rfl, totK_node, tot2814, tot2815]
  decide +kernel

theorem arows2813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2813 = true := by
  rw [show A10K2.u2813 = KTree.node A10K2.t2816 (nat_lit 46745408) (nat_lit 7653888204) (nat_lit 0) A10K2.t2817 from rfl, allE_node, rows2816, irow2813, rows2817]
  all_goals rfl

theorem atot2813 : totK PA10K2 A10K2.u2813 = [643544332899, 2987735227292, 4210825044429, 1762835205591, 143224483493, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2813 = KTree.node A10K2.t2816 (nat_lit 46745408) (nat_lit 7653888204) (nat_lit 0) A10K2.t2817 from rfl, totK_node, tot2816, tot2817]
  decide +kernel

theorem arows2814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2814 = true := by
  rw [show A10K2.u2814 = KTree.node A10K2.t2818 (nat_lit 46753050) (nat_lit 14731252833) (nat_lit 0) A10K2.t2819 from rfl, allE_node, rows2818, irow2814, rows2819]
  all_goals rfl

theorem atot2814 : totK PA10K2 A10K2.u2814 = [800212678090, 3089624591469, 3966906920439, 1765757286423, 257289106816, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2814 = KTree.node A10K2.t2818 (nat_lit 46753050) (nat_lit 14731252833) (nat_lit 0) A10K2.t2819 from rfl, totK_node, tot2818, tot2819]
  decide +kernel

theorem arows2816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2816 = true := by
  rw [show A10K2.u2816 = KTree.node A10K2.t2820 (nat_lit 46757808) (nat_lit 12433497429) (nat_lit 0) A10K2.t2821 from rfl, allE_node, rows2820, irow2816, rows2821]
  all_goals rfl

theorem atot2816 : totK PA10K2 A10K2.u2816 = [0, 1236542116689, 4007133939406, 3742827117696, 1024165231107, 62911296571, 0, 0, 0, 0] := by
  rw [show A10K2.u2816 = KTree.node A10K2.t2820 (nat_lit 46757808) (nat_lit 12433497429) (nat_lit 0) A10K2.t2821 from rfl, totK_node, tot2820, tot2821]
  decide +kernel

theorem arows2817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2817 = true := by
  rw [show A10K2.u2817 = KTree.node A10K2.t2822 (nat_lit 46771446) (nat_lit 16319387176) (nat_lit 0) A10K2.t2823 from rfl, allE_node, rows2822, irow2817, rows2823]
  all_goals rfl

theorem atot2817 : totK PA10K2 A10K2.u2817 = [0, 540703734976, 2689342038716, 4043110765562, 1998052653953, 379893934907, 20331139758, 0, 0, 0] := by
  rw [show A10K2.u2817 = KTree.node A10K2.t2822 (nat_lit 46771446) (nat_lit 16319387176) (nat_lit 0) A10K2.t2823 from rfl, totK_node, tot2822, tot2823]
  decide +kernel

theorem arows2820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2820 = true := by
  rw [show A10K2.u2820 = KTree.node A10K2.t2824 (nat_lit 46777506) (nat_lit 14377112747) (nat_lit 0) A10K2.t2825 from rfl, allE_node, rows2824, irow2820, rows2825]
  all_goals rfl

theorem atot2820 : totK PA10K2 A10K2.u2820 = [0, 642960298004, 2812668144279, 3899474394792, 1891083938079, 256434154755, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u2820 = KTree.node A10K2.t2824 (nat_lit 46777506) (nat_lit 14377112747) (nat_lit 0) A10K2.t2825 from rfl, totK_node, tot2824, tot2825]
  decide +kernel

theorem arows2821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2821 = true := by
  rw [show A10K2.u2821 = KTree.node A10K2.t2826 (nat_lit 46784560) (nat_lit 14775661840) (nat_lit 0) A10K2.t2827 from rfl, allE_node, rows2826, irow2821, rows2827]
  all_goals rfl

theorem atot2821 : totK PA10K2 A10K2.u2821 = [0, 572337322825, 2659206779346, 4141483896586, 2029145679774, 246669431517, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2821 = KTree.node A10K2.t2826 (nat_lit 46784560) (nat_lit 14775661840) (nat_lit 0) A10K2.t2827 from rfl, totK_node, tot2826, tot2827]
  decide +kernel

theorem arows2823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2823 = true := by
  rw [show A10K2.u2823 = KTree.node A10K2.t2828 (nat_lit 46802616) (nat_lit 7529829957) (nat_lit 0) A10K2.t2829 from rfl, allE_node, rows2828, irow2823, rows2829]
  all_goals rfl

theorem atot2823 : totK PA10K2 A10K2.u2823 = [796494680594, 2981445029882, 3653915149753, 1965460404691, 580463418019, 50499610055, 0, 0, 0, 0] := by
  rw [show A10K2.u2823 = KTree.node A10K2.t2828 (nat_lit 46802616) (nat_lit 7529829957) (nat_lit 0) A10K2.t2829 from rfl, totK_node, tot2828, tot2829]
  decide +kernel

theorem arows2824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2824 = true := by
  rw [show A10K2.u2824 = KTree.node A10K2.t2830 (nat_lit 46807304) (nat_lit 10856025748) (nat_lit 0) A10K2.t2831 from rfl, allE_node, rows2830, irow2824, rows2831]
  all_goals rfl

theorem atot2824 : totK PA10K2 A10K2.u2824 = [282932941769, 1775882412221, 3931444301840, 3094498569033, 653784047167, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2824 = KTree.node A10K2.t2830 (nat_lit 46807304) (nat_lit 10856025748) (nat_lit 0) A10K2.t2831 from rfl, totK_node, tot2830, tot2831]
  decide +kernel

theorem arows2828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2828 = true := by
  rw [show A10K2.u2828 = KTree.node A10K2.t2832 (nat_lit 46811948) (nat_lit 13455571302) (nat_lit 0) A10K2.t2833 from rfl, allE_node, rows2832, irow2828, rows2833]
  all_goals rfl

theorem atot2828 : totK PA10K2 A10K2.u2828 = [459144823843, 2586685038928, 4267114183186, 2028566544505, 195863061533, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2828 = KTree.node A10K2.t2832 (nat_lit 46811948) (nat_lit 13455571302) (nat_lit 0) A10K2.t2833 from rfl, totK_node, tot2832, tot2833]
  decide +kernel

theorem arows2829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2829 = true := by
  rw [show A10K2.u2829 = KTree.node A10K2.t2834 (nat_lit 46836225) (nat_lit 8566103691) (nat_lit 0) A10K2.t2835 from rfl, allE_node, rows2834, irow2829, rows2835]
  all_goals rfl

theorem atot2829 : totK PA10K2 A10K2.u2829 = [0, 1010356000769, 3599887520491, 3949491840543, 1168545641978, 70432589585, 0, 0, 0, 0] := by
  rw [show A10K2.u2829 = KTree.node A10K2.t2834 (nat_lit 46836225) (nat_lit 8566103691) (nat_lit 0) A10K2.t2835 from rfl, totK_node, tot2834, tot2835]
  decide +kernel

theorem arows2831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2831 = true := by
  rw [show A10K2.u2831 = KTree.node A10K2.t2836 (nat_lit 46844680) (nat_lit 12220830380) (nat_lit 0) A10K2.t2837 from rfl, allE_node, rows2836, irow2831, rows2837]
  all_goals rfl

theorem atot2831 : totK PA10K2 A10K2.u2831 = [0, 524228399719, 2740108291046, 4141485157026, 1751434042573, 185148109097, 0, 0, 0, 0] := by
  rw [show A10K2.u2831 = KTree.node A10K2.t2836 (nat_lit 46844680) (nat_lit 12220830380) (nat_lit 0) A10K2.t2837 from rfl, totK_node, tot2836, tot2837]
  decide +kernel

theorem arows2832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2832 = true := by
  rw [show A10K2.u2832 = KTree.node A10K2.t2838 (nat_lit 46861894) (nat_lit 15109149156) (nat_lit 0) A10K2.t2839 from rfl, allE_node, rows2838, irow2832, rows2839]
  all_goals rfl

theorem atot2832 : totK PA10K2 A10K2.u2832 = [556621861187, 2603666873384, 3941417934710, 2120763081251, 540280912651, 125622035440, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2832 = KTree.node A10K2.t2838 (nat_lit 46861894) (nat_lit 15109149156) (nat_lit 0) A10K2.t2839 from rfl, totK_node, tot2838, tot2839]
  decide +kernel

theorem arows2835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2835 = true := by
  rw [show A10K2.u2835 = KTree.node A10K2.t2840 (nat_lit 46869288) (nat_lit 7971636270) (nat_lit 0) A10K2.t2841 from rfl, allE_node, rows2840, irow2835, rows2841]
  all_goals rfl

theorem atot2835 : totK PA10K2 A10K2.u2835 = [804252991483, 3256681530258, 4120114764021, 1690499092181, 150198929770, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2835 = KTree.node A10K2.t2840 (nat_lit 46869288) (nat_lit 7971636270) (nat_lit 0) A10K2.t2841 from rfl, totK_node, tot2840, tot2841]
  decide +kernel

theorem arows2836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2836 = true := by
  rw [show A10K2.u2836 = KTree.node A10K2.t2842 (nat_lit 46882820) (nat_lit 9958890834) (nat_lit 0) A10K2.t2843 from rfl, allE_node, rows2842, irow2836, rows2843]
  all_goals rfl

theorem atot2836 : totK PA10K2 A10K2.u2836 = [534680748697, 2348226191859, 3795423199785, 2533921480222, 573312394672, 31747192500, 0, 0, 0, 0] := by
  rw [show A10K2.u2836 = KTree.node A10K2.t2842 (nat_lit 46882820) (nat_lit 9958890834) (nat_lit 0) A10K2.t2843 from rfl, totK_node, tot2842, tot2843]
  decide +kernel

theorem arows2838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2838 = true := by
  rw [show A10K2.u2838 = KTree.node A10K2.t2844 (nat_lit 46887352) (nat_lit 14479854271) (nat_lit 0) A10K2.t2845 from rfl, allE_node, rows2844, irow2838, rows2845]
  all_goals rfl

theorem atot2838 : totK PA10K2 A10K2.u2838 = [327742824672, 2055788433235, 4139433196931, 2917719183199, 543496866073, 13816090359, 0, 0, 0, 0] := by
  rw [show A10K2.u2838 = KTree.node A10K2.t2844 (nat_lit 46887352) (nat_lit 14479854271) (nat_lit 0) A10K2.t2845 from rfl, totK_node, tot2844, tot2845]
  decide +kernel

theorem arows2839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2839 = true := by
  rw [show A10K2.u2839 = KTree.node A10K2.t2846 (nat_lit 46894092) (nat_lit 9713778168) (nat_lit 0) A10K2.t2847 from rfl, allE_node, rows2846, irow2839, rows2847]
  all_goals rfl

theorem atot2839 : totK PA10K2 A10K2.u2839 = [0, 677048760558, 2940678091824, 4184518504587, 1947342466479, 209080333852, 0, 0, 0, 0] := by
  rw [show A10K2.u2839 = KTree.node A10K2.t2846 (nat_lit 46894092) (nat_lit 9713778168) (nat_lit 0) A10K2.t2847 from rfl, totK_node, tot2846, tot2847]
  decide +kernel

theorem arows2844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2844 = true := by
  rw [show A10K2.u2844 = KTree.node A10K2.t2848 (nat_lit 46901126) (nat_lit 15177441148) (nat_lit 0) A10K2.t2849 from rfl, allE_node, rows2848, irow2844, rows2849]
  all_goals rfl

theorem atot2844 : totK PA10K2 A10K2.u2844 = [0, 804109052366, 3246310262625, 4057362382946, 1655000175697, 210110862211, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u2844 = KTree.node A10K2.t2848 (nat_lit 46901126) (nat_lit 15177441148) (nat_lit 0) A10K2.t2849 from rfl, totK_node, tot2848, tot2849]
  decide +kernel

theorem arows2845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2845 = true := by
  rw [show A10K2.u2845 = KTree.node A10K2.t2850 (nat_lit 46906781) (nat_lit 3737298224) (nat_lit 0) A10K2.t2851 from rfl, allE_node, rows2850, irow2845, rows2851]
  all_goals rfl

theorem atot2845 : totK PA10K2 A10K2.u2845 = [0, 534421757282, 2585884421929, 4083610936939, 2320999264183, 341587519758, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u2845 = KTree.node A10K2.t2850 (nat_lit 46906781) (nat_lit 3737298224) (nat_lit 0) A10K2.t2851 from rfl, totK_node, tot2850, tot2851]
  decide +kernel

theorem arows2847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2847 = true := by
  rw [show A10K2.u2847 = KTree.node A10K2.t2852 (nat_lit 46919940) (nat_lit 5136415484) (nat_lit 0) A10K2.t2853 from rfl, allE_node, rows2852, irow2847, rows2853]
  all_goals rfl

theorem atot2847 : totK PA10K2 A10K2.u2847 = [0, 327291078893, 2107515041981, 4180804772306, 2786655212586, 456796721927, 12224107035, 0, 0, 0] := by
  rw [show A10K2.u2847 = KTree.node A10K2.t2852 (nat_lit 46919940) (nat_lit 5136415484) (nat_lit 0) A10K2.t2853 from rfl, totK_node, tot2852, tot2853]
  decide +kernel

theorem arows2848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2848 = true := by
  rw [show A10K2.u2848 = KTree.node A10K2.t2854 (nat_lit 46999287) (nat_lit 10803467008) (nat_lit 0) A10K2.t2855 from rfl, allE_node, rows2854, irow2848, rows2855]
  all_goals rfl

theorem atot2848 : totK PA10K2 A10K2.u2848 = [0, 861409662052, 3050927003127, 3470602550205, 1826618254779, 544575990544, 48886019071, 0, 0, 0] := by
  rw [show A10K2.u2848 = KTree.node A10K2.t2854 (nat_lit 46999287) (nat_lit 10803467008) (nat_lit 0) A10K2.t2855 from rfl, totK_node, tot2854, tot2855]
  decide +kernel

theorem arows2851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2851 = true := by
  rw [show A10K2.u2851 = KTree.node A10K2.t2856 (nat_lit 47003821) (nat_lit 6524584172) (nat_lit 0) A10K2.t2857 from rfl, allE_node, rows2856, irow2851, rows2857]
  all_goals rfl

theorem atot2851 : totK PA10K2 A10K2.u2851 = [0, 199895226948, 1680506066749, 4019691890293, 3098956974119, 625753942270, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2851 = KTree.node A10K2.t2856 (nat_lit 47003821) (nat_lit 6524584172) (nat_lit 0) A10K2.t2857 from rfl, totK_node, tot2856, tot2857]
  decide +kernel

theorem arows2852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2852 = true := by
  rw [show A10K2.u2852 = KTree.node A10K2.t2858 (nat_lit 47010057) (nat_lit 8002362118) (nat_lit 0) A10K2.t2859 from rfl, allE_node, rows2858, irow2852, rows2859]
  all_goals rfl

theorem atot2852 : totK PA10K2 A10K2.u2852 = [0, 586261023801, 2688039128896, 4018509856397, 1977589492922, 241761313869, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u2852 = KTree.node A10K2.t2858 (nat_lit 47010057) (nat_lit 8002362118) (nat_lit 0) A10K2.t2859 from rfl, totK_node, tot2858, tot2859]
  decide +kernel

theorem arows2854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2854 = true := by
  rw [show A10K2.u2854 = KTree.node A10K2.t2860 (nat_lit 47017180) (nat_lit 9553192736) (nat_lit 0) A10K2.t2861 from rfl, allE_node, rows2860, irow2854, rows2861]
  all_goals rfl

theorem atot2854 : totK PA10K2 A10K2.u2854 = [0, 656132540036, 3006230936986, 4340965926404, 1959227329456, 195805753744, 0, 0, 0, 0] := by
  rw [show A10K2.u2854 = KTree.node A10K2.t2860 (nat_lit 47017180) (nat_lit 9553192736) (nat_lit 0) A10K2.t2861 from rfl, totK_node, tot2860, tot2861]
  decide +kernel

theorem arows2855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2855 = true := by
  rw [show A10K2.u2855 = KTree.node A10K2.t2862 (nat_lit 47031451) (nat_lit 10068108498) (nat_lit 0) A10K2.t2863 from rfl, allE_node, rows2862, irow2855, rows2863]
  all_goals rfl

theorem atot2855 : totK PA10K2 A10K2.u2855 = [0, 0, 986255946873, 3682606622611, 3939644597203, 1127770417641, 67541609336, 0, 0, 0] := by
  rw [show A10K2.u2855 = KTree.node A10K2.t2862 (nat_lit 47031451) (nat_lit 10068108498) (nat_lit 0) A10K2.t2863 from rfl, totK_node, tot2862, tot2863]
  decide +kernel

theorem arows2859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2859 = true := by
  rw [show A10K2.u2859 = KTree.node A10K2.t2864 (nat_lit 47036050) (nat_lit 15803640172) (nat_lit 0) A10K2.t2865 from rfl, allE_node, rows2864, irow2859, rows2865]
  all_goals rfl

theorem atot2859 : totK PA10K2 A10K2.u2859 = [0, 0, 296412983875, 1945422688283, 3941571806174, 2684446131677, 561235661447, 31018567651, 0, 0] := by
  rw [show A10K2.u2859 = KTree.node A10K2.t2864 (nat_lit 47036050) (nat_lit 15803640172) (nat_lit 0) A10K2.t2865 from rfl, totK_node, tot2864, tot2865]
  decide +kernel

theorem arows2860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2860 = true := by
  rw [show A10K2.u2860 = KTree.node A10K2.t2866 (nat_lit 47040797) (nat_lit 6440772232) (nat_lit 0) A10K2.t2867 from rfl, allE_node, rows2866, irow2860, rows2867]
  all_goals rfl

theorem atot2860 : totK PA10K2 A10K2.u2860 = [0, 0, 627916420122, 2937960614397, 4112601786096, 1565593215404, 109738100044, 0, 0, 0] := by
  rw [show A10K2.u2860 = KTree.node A10K2.t2866 (nat_lit 47040797) (nat_lit 6440772232) (nat_lit 0) A10K2.t2867 from rfl, totK_node, tot2866, tot2867]
  decide +kernel

theorem arows2862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2862 = true := by
  rw [show A10K2.u2862 = KTree.node A10K2.t2868 (nat_lit 47049898) (nat_lit 12499976433) (nat_lit 0) A10K2.t2869 from rfl, allE_node, rows2868, irow2862, rows2869]
  all_goals rfl

theorem atot2862 : totK PA10K2 A10K2.u2862 = [0, 308899695994, 1832138416960, 3588067395851, 2988624691982, 1109863468373, 167423295067, 5685526223, 0, 0] := by
  rw [show A10K2.u2862 = KTree.node A10K2.t2868 (nat_lit 47049898) (nat_lit 12499976433) (nat_lit 0) A10K2.t2869 from rfl, totK_node, tot2868, tot2869]
  decide +kernel

theorem arows2863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2863 = true := by
  rw [show A10K2.u2863 = KTree.node A10K2.t2870 (nat_lit 47067063) (nat_lit 15100918269) (nat_lit 0) A10K2.t2871 from rfl, allE_node, rows2870, irow2863, rows2871]
  all_goals rfl

theorem atot2863 : totK PA10K2 A10K2.u2863 = [0, 487128049630, 2449122511473, 4070547141156, 2355073038096, 429967939826, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u2863 = KTree.node A10K2.t2870 (nat_lit 47067063) (nat_lit 15100918269) (nat_lit 0) A10K2.t2871 from rfl, totK_node, tot2870, tot2871]
  decide +kernel

theorem arows2866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2866 = true := by
  rw [show A10K2.u2866 = KTree.node A10K2.t2872 (nat_lit 47072608) (nat_lit 10846661124) (nat_lit 0) A10K2.t2873 from rfl, allE_node, rows2872, irow2866, rows2873]
  all_goals rfl

theorem atot2866 : totK PA10K2 A10K2.u2866 = [0, 742077765612, 2985504719478, 3832575876996, 1803265156037, 259178108956, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u2866 = KTree.node A10K2.t2872 (nat_lit 47072608) (nat_lit 10846661124) (nat_lit 0) A10K2.t2873 from rfl, totK_node, tot2872, tot2873]
  decide +kernel

theorem arows2867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2867 = true := by
  rw [show A10K2.u2867 = KTree.node A10K2.t2874 (nat_lit 47097014) (nat_lit 15390350620) (nat_lit 0) A10K2.t2875 from rfl, allE_node, rows2874, irow2867, rows2875]
  all_goals rfl

theorem atot2867 : totK PA10K2 A10K2.u2867 = [0, 0, 1238061333949, 4072638000547, 3451374832054, 717588309021, 32470817489, 0, 0, 0] := by
  rw [show A10K2.u2867 = KTree.node A10K2.t2874 (nat_lit 47097014) (nat_lit 15390350620) (nat_lit 0) A10K2.t2875 from rfl, totK_node, tot2874, tot2875]
  decide +kernel

theorem arows2869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2869 = true := by
  rw [show A10K2.u2869 = KTree.node A10K2.t2876 (nat_lit 47105379) (nat_lit 9355842215) (nat_lit 0) A10K2.t2877 from rfl, allE_node, rows2876, irow2869, rows2877]
  all_goals rfl

theorem atot2869 : totK PA10K2 A10K2.u2869 = [0, 0, 957998340937, 3638073937372, 3923829558968, 1046562250199, 55821685186, 0, 0, 0] := by
  rw [show A10K2.u2869 = KTree.node A10K2.t2876 (nat_lit 47105379) (nat_lit 9355842215) (nat_lit 0) A10K2.t2877 from rfl, totK_node, tot2876, tot2877]
  decide +kernel

theorem arows2870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2870 = true := by
  rw [show A10K2.u2870 = KTree.node A10K2.t2878 (nat_lit 47120654) (nat_lit 11121130426) (nat_lit 0) A10K2.t2879 from rfl, allE_node, rows2878, irow2870, rows2879]
  all_goals rfl

theorem atot2870 : totK PA10K2 A10K2.u2870 = [0, 556621861187, 2046133042122, 2896917818460, 2612339372666, 1271637351266, 202894274768, 6239673734, 0, 0] := by
  rw [show A10K2.u2870 = KTree.node A10K2.t2878 (nat_lit 47120654) (nat_lit 11121130426) (nat_lit 0) A10K2.t2879 from rfl, totK_node, tot2878, tot2879]
  decide +kernel

theorem arows2876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2876 = true := by
  rw [show A10K2.u2876 = KTree.node A10K2.t2880 (nat_lit 47129960) (nat_lit 5492958456) (nat_lit 0) A10K2.t2881 from rfl, allE_node, rows2880, irow2876, rows2881]
  all_goals rfl

theorem atot2876 : totK PA10K2 A10K2.u2876 = [0, 758484837103, 2978157542124, 3938158948143, 1928636342261, 301850315213, 7007974415, 0, 0, 0] := by
  rw [show A10K2.u2876 = KTree.node A10K2.t2880 (nat_lit 47129960) (nat_lit 5492958456) (nat_lit 0) A10K2.t2881 from rfl, totK_node, tot2880, tot2881]
  decide +kernel

theorem arows2877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2877 = true := by
  rw [show A10K2.u2877 = KTree.node A10K2.t2882 (nat_lit 47134619) (nat_lit 9633256820) (nat_lit 0) A10K2.t2883 from rfl, allE_node, rows2882, irow2877, rows2883]
  all_goals rfl

theorem atot2877 : totK PA10K2 A10K2.u2877 = [0, 292097226597, 2001299629781, 4073512460501, 2928029795092, 610730984044, 31285368086, 0, 0, 0] := by
  rw [show A10K2.u2877 = KTree.node A10K2.t2882 (nat_lit 47134619) (nat_lit 9633256820) (nat_lit 0) A10K2.t2883 from rfl, totK_node, tot2882, tot2883]
  decide +kernel

theorem arows2879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2879 = true := by
  rw [show A10K2.u2879 = KTree.node A10K2.t2884 (nat_lit 47148274) (nat_lit 14883909207) (nat_lit 0) A10K2.t2885 from rfl, allE_node, rows2884, irow2879, rows2885]
  all_goals rfl

theorem atot2879 : totK PA10K2 A10K2.u2879 = [0, 615112866711, 2805598059013, 4105877258765, 2067971526963, 284443539022, 6281495166, 0, 0, 0] := by
  rw [show A10K2.u2879 = KTree.node A10K2.t2884 (nat_lit 47148274) (nat_lit 14883909207) (nat_lit 0) A10K2.t2885 from rfl, totK_node, tot2884, tot2885]
  decide +kernel

theorem arows2880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2880 = true := by
  rw [show A10K2.u2880 = KTree.node A10K2.t2886 (nat_lit 47152852) (nat_lit 8258749016) (nat_lit 0) A10K2.t2887 from rfl, allE_node, rows2886, irow2880, rows2887]
  all_goals rfl

theorem atot2880 : totK PA10K2 A10K2.u2880 = [480657707117, 1575325675077, 2015252960399, 2519861127939, 2439484852793, 776041928989, 56100664475, 0, 0, 0] := by
  rw [show A10K2.u2880 = KTree.node A10K2.t2886 (nat_lit 47152852) (nat_lit 8258749016) (nat_lit 0) A10K2.t2887 from rfl, totK_node, tot2886, tot2887]
  decide +kernel

theorem arows2883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2883 = true := by
  rw [show A10K2.u2883 = KTree.node A10K2.t2888 (nat_lit 47714689) (nat_lit 10422756214) (nat_lit 0) A10K2.t2889 from rfl, allE_node, rows2888, irow2883, rows2889]
  all_goals rfl

theorem atot2883 : totK PA10K2 A10K2.u2883 = [297251734964, 2044025470807, 4149490897874, 2789422808754, 558225884336, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2883 = KTree.node A10K2.t2888 (nat_lit 47714689) (nat_lit 10422756214) (nat_lit 0) A10K2.t2889 from rfl, totK_node, tot2888, tot2889]
  decide +kernel

theorem arows2884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2884 = true := by
  rw [show A10K2.u2884 = KTree.node A10K2.t2890 (nat_lit 47735048) (nat_lit 14123762134) (nat_lit 0) A10K2.t2891 from rfl, allE_node, rows2890, irow2884, rows2891]
  all_goals rfl

theorem atot2884 : totK PA10K2 A10K2.u2884 = [915374327186, 3424780715947, 4012801278090, 1446804887878, 129344471736, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2884 = KTree.node A10K2.t2890 (nat_lit 47735048) (nat_lit 14123762134) (nat_lit 0) A10K2.t2891 from rfl, totK_node, tot2890, tot2891]
  decide +kernel

theorem arows2886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2886 = true := by
  rw [show A10K2.u2886 = KTree.node A10K2.t2892 (nat_lit 47739655) (nat_lit 8479983140) (nat_lit 0) A10K2.t2893 from rfl, allE_node, rows2892, irow2886, rows2893]
  all_goals rfl

theorem atot2886 : totK PA10K2 A10K2.u2886 = [177435414779, 1660986656068, 4144020280168, 3499502314972, 748089271612, 19707287507, 0, 0, 0, 0] := by
  rw [show A10K2.u2886 = KTree.node A10K2.t2892 (nat_lit 47739655) (nat_lit 8479983140) (nat_lit 0) A10K2.t2893 from rfl, totK_node, tot2892, tot2893]
  decide +kernel

theorem arows2887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2887 = true := by
  rw [show A10K2.u2887 = KTree.node A10K2.t2894 (nat_lit 47745536) (nat_lit 15366970878) (nat_lit 0) A10K2.t2895 from rfl, allE_node, rows2894, irow2887, rows2895]
  all_goals rfl

theorem atot2887 : totK PA10K2 A10K2.u2887 = [0, 777422358885, 3254366676539, 4068076717207, 1506793385347, 129484023159, 0, 0, 0, 0] := by
  rw [show A10K2.u2887 = KTree.node A10K2.t2894 (nat_lit 47745536) (nat_lit 15366970878) (nat_lit 0) A10K2.t2895 from rfl, totK_node, tot2894, tot2895]
  decide +kernel

theorem arows2891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2891 = true := by
  rw [show A10K2.u2891 = KTree.node A10K2.t2896 (nat_lit 47759428) (nat_lit 11552108224) (nat_lit 0) A10K2.t2897 from rfl, allE_node, rows2896, irow2891, rows2897]
  all_goals rfl

theorem atot2891 : totK PA10K2 A10K2.u2891 = [0, 533777669358, 2284649817156, 3722982427086, 2421507696663, 527801149725, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u2891 = KTree.node A10K2.t2896 (nat_lit 47759428) (nat_lit 11552108224) (nat_lit 0) A10K2.t2897 from rfl, totK_node, tot2896, tot2897]
  decide +kernel

theorem arows2892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2892 = true := by
  rw [show A10K2.u2892 = KTree.node A10K2.t2898 (nat_lit 47771080) (nat_lit 13815362515) (nat_lit 0) A10K2.t2899 from rfl, allE_node, rows2898, irow2892, rows2899]
  all_goals rfl

theorem atot2892 : totK PA10K2 A10K2.u2892 = [312139800791, 1640370476754, 3586136568200, 3437954507640, 1069019706708, 77617841135, 0, 0, 0, 0] := by
  rw [show A10K2.u2892 = KTree.node A10K2.t2898 (nat_lit 47771080) (nat_lit 13815362515) (nat_lit 0) A10K2.t2899 from rfl, totK_node, tot2898, tot2899]
  decide +kernel

theorem arows2894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2894 = true := by
  rw [show A10K2.u2894 = KTree.node A10K2.t2900 (nat_lit 47787961) (nat_lit 6446859460) (nat_lit 0) A10K2.t2901 from rfl, allE_node, rows2900, irow2894, rows2901]
  all_goals rfl

theorem atot2894 : totK PA10K2 A10K2.u2894 = [510881146888, 2440778505891, 3951093929932, 2384085888192, 459165344366, 25734533292, 0, 0, 0, 0] := by
  rw [show A10K2.u2894 = KTree.node A10K2.t2900 (nat_lit 47787961) (nat_lit 6446859460) (nat_lit 0) A10K2.t2901 from rfl, totK_node, tot2900, tot2901]
  decide +kernel

theorem arows2895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2895 = true := by
  rw [show A10K2.u2895 = KTree.node A10K2.t2902 (nat_lit 47794104) (nat_lit 10353479194) (nat_lit 0) A10K2.t2903 from rfl, allE_node, rows2902, irow2895, rows2903]
  all_goals rfl

theorem atot2895 : totK PA10K2 A10K2.u2895 = [481051651601, 2531591275930, 4192087196581, 2270678891958, 317211387410, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u2895 = KTree.node A10K2.t2902 (nat_lit 47794104) (nat_lit 10353479194) (nat_lit 0) A10K2.t2903 from rfl, totK_node, tot2902, tot2903]
  decide +kernel

theorem arows2898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2898 = true := by
  rw [show A10K2.u2898 = KTree.node A10K2.t2904 (nat_lit 47802221) (nat_lit 5394304696) (nat_lit 0) A10K2.t2905 from rfl, allE_node, rows2904, irow2898, rows2905]
  all_goals rfl

theorem atot2898 : totK PA10K2 A10K2.u2898 = [829662196464, 3267964050203, 4095096333266, 1746480707339, 239133223315, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2898 = KTree.node A10K2.t2904 (nat_lit 47802221) (nat_lit 5394304696) (nat_lit 0) A10K2.t2905 from rfl, totK_node, tot2904, tot2905]
  decide +kernel

theorem arows2899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2899 = true := by
  rw [show A10K2.u2899 = KTree.node A10K2.t2906 (nat_lit 47807962) (nat_lit 13986726338) (nat_lit 0) A10K2.t2907 from rfl, allE_node, rows2906, irow2899, rows2907]
  all_goals rfl

theorem atot2899 : totK PA10K2 A10K2.u2899 = [0, 925358531024, 3557785005793, 4077883815276, 1300257504168, 89457584680, 0, 0, 0, 0] := by
  rw [show A10K2.u2899 = KTree.node A10K2.t2906 (nat_lit 47807962) (nat_lit 13986726338) (nat_lit 0) A10K2.t2907 from rfl, totK_node, tot2906, tot2907]
  decide +kernel

theorem arows2901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2901 = true := by
  rw [show A10K2.u2901 = KTree.node A10K2.t2908 (nat_lit 47820756) (nat_lit 6303659676) (nat_lit 0) A10K2.t2909 from rfl, allE_node, rows2908, irow2901, rows2909]
  all_goals rfl

theorem atot2901 : totK PA10K2 A10K2.u2901 = [0, 510058576851, 2384331989613, 3888129689680, 2330868958504, 448645164100, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u2901 = KTree.node A10K2.t2908 (nat_lit 47820756) (nat_lit 6303659676) (nat_lit 0) A10K2.t2909 from rfl, totK_node, tot2908, tot2909]
  decide +kernel

theorem arows2902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2902 = true := by
  rw [show A10K2.u2902 = KTree.node A10K2.t2910 (nat_lit 47827171) (nat_lit 10340699668) (nat_lit 0) A10K2.t2911 from rfl, allE_node, rows2910, irow2902, rows2911]
  all_goals rfl

theorem atot2902 : totK PA10K2 A10K2.u2902 = [0, 565160121363, 2634954079544, 4018625740123, 2108649365606, 335620988584, 11638555097, 0, 0, 0] := by
  rw [show A10K2.u2902 = KTree.node A10K2.t2910 (nat_lit 47827171) (nat_lit 10340699668) (nat_lit 0) A10K2.t2911 from rfl, totK_node, tot2910, tot2911]
  decide +kernel

theorem arows2907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2907 = true := by
  rw [show A10K2.u2907 = KTree.node A10K2.t2912 (nat_lit 47836225) (nat_lit 10035684367) (nat_lit 0) A10K2.t2913 from rfl, allE_node, rows2912, irow2907, rows2913]
  all_goals rfl

theorem atot2907 : totK PA10K2 A10K2.u2907 = [289498769530, 1558963235742, 3508298659568, 3473035891566, 1143584363444, 83063383024, 0, 0, 0, 0] := by
  rw [show A10K2.u2907 = KTree.node A10K2.t2912 (nat_lit 47836225) (nat_lit 10035684367) (nat_lit 0) A10K2.t2913 from rfl, totK_node, tot2912, tot2913]
  decide +kernel

theorem arows2908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2908 = true := by
  rw [show A10K2.u2908 = KTree.node A10K2.t2914 (nat_lit 47910640) (nat_lit 10975876506) (nat_lit 0) A10K2.t2915 from rfl, allE_node, rows2914, irow2908, rows2915]
  all_goals rfl

theorem atot2908 : totK PA10K2 A10K2.u2908 = [436450538801, 2272985628674, 3894446323940, 2380706266402, 459689443276, 24601572423, 0, 0, 0, 0] := by
  rw [show A10K2.u2908 = KTree.node A10K2.t2914 (nat_lit 47910640) (nat_lit 10975876506) (nat_lit 0) A10K2.t2915 from rfl, totK_node, tot2914, tot2915]
  decide +kernel

theorem arows2910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2910 = true := by
  rw [show A10K2.u2910 = KTree.node A10K2.t2916 (nat_lit 47917247) (nat_lit 13433872580) (nat_lit 0) A10K2.t2917 from rfl, allE_node, rows2916, irow2910, rows2917]
  all_goals rfl

theorem atot2910 : totK PA10K2 A10K2.u2910 = [769730181679, 3209830194725, 4195768742310, 1708219895322, 159538433148, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u2910 = KTree.node A10K2.t2916 (nat_lit 47917247) (nat_lit 13433872580) (nat_lit 0) A10K2.t2917 from rfl, totK_node, tot2916, tot2917]
  decide +kernel

theorem arows2911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2911 = true := by
  rw [show A10K2.u2911 = KTree.node A10K2.t2918 (nat_lit 47922422) (nat_lit 16319387176) (nat_lit 0) A10K2.t2919 from rfl, allE_node, rows2918, irow2911, rows2919]
  all_goals rfl

theorem atot2911 : totK PA10K2 A10K2.u2911 = [561117401612, 2390139817457, 3779845459773, 2475876290582, 533858224621, 31450896759, 0, 0, 0, 0] := by
  rw [show A10K2.u2911 = KTree.node A10K2.t2918 (nat_lit 47922422) (nat_lit 16319387176) (nat_lit 0) A10K2.t2919 from rfl, totK_node, tot2918, tot2919]
  decide +kernel

theorem arows2914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2914 = true := by
  rw [show A10K2.u2914 = KTree.node A10K2.t2920 (nat_lit 47935493) (nat_lit 5957406640) (nat_lit 0) A10K2.t2921 from rfl, allE_node, rows2920, irow2914, rows2921]
  all_goals rfl

theorem atot2914 : totK PA10K2 A10K2.u2914 = [332208314330, 2092792527613, 4180975101639, 2855911695734, 514300487691, 13816090359, 0, 0, 0, 0] := by
  rw [show A10K2.u2914 = KTree.node A10K2.t2920 (nat_lit 47935493) (nat_lit 5957406640) (nat_lit 0) A10K2.t2921 from rfl, totK_node, tot2920, tot2921]
  decide +kernel

theorem arows2915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2915 = true := by
  rw [show A10K2.u2915 = KTree.node A10K2.t2922 (nat_lit 47940026) (nat_lit 12028605723) (nat_lit 0) A10K2.t2923 from rfl, allE_node, rows2922, irow2915, rows2923]
  all_goals rfl

theorem atot2915 : totK PA10K2 A10K2.u2915 = [0, 1055615555590, 3706774100647, 3848747599563, 1125870940432, 73908064551, 0, 0, 0, 0] := by
  rw [show A10K2.u2915 = KTree.node A10K2.t2922 (nat_lit 47940026) (nat_lit 12028605723) (nat_lit 0) A10K2.t2923 from rfl, totK_node, tot2922, tot2923]
  decide +kernel

theorem arows2917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2917 = true := by
  rw [show A10K2.u2917 = KTree.node A10K2.t2924 (nat_lit 47946821) (nat_lit 5442952294) (nat_lit 0) A10K2.t2925 from rfl, allE_node, rows2924, irow2917, rows2925]
  all_goals rfl

theorem atot2917 : totK PA10K2 A10K2.u2917 = [0, 423629393039, 2293695941603, 4141021022435, 2406303123340, 353541385587, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u2917 = KTree.node A10K2.t2924 (nat_lit 47946821) (nat_lit 5442952294) (nat_lit 0) A10K2.t2925 from rfl, totK_node, tot2924, tot2925]
  decide +kernel

theorem arows2918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2918 = true := by
  rw [show A10K2.u2918 = KTree.node A10K2.t2926 (nat_lit 47953185) (nat_lit 2343761364) (nat_lit 0) A10K2.t2927 from rfl, allE_node, rows2926, irow2918, rows2927]
  all_goals rfl

theorem atot2918 : totK PA10K2 A10K2.u2918 = [0, 508759922918, 2568822210058, 4158827461374, 2352862181244, 339531092379, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u2918 = KTree.node A10K2.t2926 (nat_lit 47953185) (nat_lit 2343761364) (nat_lit 0) A10K2.t2927 from rfl, totK_node, tot2926, tot2927]
  decide +kernel

theorem arows2922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2922 = true := by
  rw [show A10K2.u2922 = KTree.node A10K2.t2928 (nat_lit 47967289) (nat_lit 7244271112) (nat_lit 0) A10K2.t2929 from rfl, allE_node, rows2928, irow2922, rows2929]
  all_goals rfl

theorem atot2922 : totK PA10K2 A10K2.u2922 = [0, 728367492097, 3173120812722, 4220740924128, 1706476246652, 137037874025, 0, 0, 0, 0] := by
  rw [show A10K2.u2922 = KTree.node A10K2.t2928 (nat_lit 47967289) (nat_lit 7244271112) (nat_lit 0) A10K2.t2929 from rfl, totK_node, tot2928, tot2929]
  decide +kernel

theorem arows2923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2923 = true := by
  rw [show A10K2.u2923 = KTree.node A10K2.t2930 (nat_lit 47971838) (nat_lit 15941591276) (nat_lit 0) A10K2.t2931 from rfl, allE_node, rows2930, irow2923, rows2931]
  all_goals rfl

theorem atot2923 : totK PA10K2 A10K2.u2923 = [0, 345924611889, 1782638221539, 3579701140694, 3096623422607, 881432404386, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u2923 = KTree.node A10K2.t2930 (nat_lit 47971838) (nat_lit 15941591276) (nat_lit 0) A10K2.t2931 from rfl, totK_node, tot2930, tot2931]
  decide +kernel

theorem arows2925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2925 = true := by
  rw [show A10K2.u2925 = KTree.node A10K2.t2932 (nat_lit 47976507) (nat_lit 4085779790) (nat_lit 0) A10K2.t2933 from rfl, allE_node, rows2932, irow2925, rows2933]
  all_goals rfl

theorem atot2925 : totK PA10K2 A10K2.u2925 = [0, 417526276724, 2281142722301, 3975860817767, 2545358178320, 536536805445, 30780440178, 0, 0, 0] := by
  rw [show A10K2.u2925 = KTree.node A10K2.t2932 (nat_lit 47976507) (nat_lit 4085779790) (nat_lit 0) A10K2.t2933 from rfl, totK_node, tot2932, tot2933]
  decide +kernel

theorem arows2926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2926 = true := by
  rw [show A10K2.u2926 = KTree.node A10K2.t2934 (nat_lit 47993287) (nat_lit 11310647596) (nat_lit 0) A10K2.t2935 from rfl, allE_node, rows2934, irow2926, rows2935]
  all_goals rfl

theorem atot2926 : totK PA10K2 A10K2.u2926 = [0, 770396326733, 3226711636797, 4158995638095, 1622094846418, 140547690058, 0, 0, 0, 0] := by
  rw [show A10K2.u2926 = KTree.node A10K2.t2934 (nat_lit 47993287) (nat_lit 11310647596) (nat_lit 0) A10K2.t2935 from rfl, totK_node, tot2934, tot2935]
  decide +kernel

theorem arows2929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2929 = true := by
  rw [show A10K2.u2929 = KTree.node A10K2.t2936 (nat_lit 48001498) (nat_lit 12306243294) (nat_lit 0) A10K2.t2937 from rfl, allE_node, rows2936, irow2929, rows2937]
  all_goals rfl

theorem atot2929 : totK PA10K2 A10K2.u2929 = [0, 320910162593, 2004670195249, 4216461999078, 3121791896871, 559848131553, 13229391832, 0, 0, 0] := by
  rw [show A10K2.u2929 = KTree.node A10K2.t2936 (nat_lit 48001498) (nat_lit 12306243294) (nat_lit 0) A10K2.t2937 from rfl, totK_node, tot2936, tot2937]
  decide +kernel

theorem arows2930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2930 = true := by
  rw [show A10K2.u2930 = KTree.node A10K2.t2938 (nat_lit 48007224) (nat_lit 14769319574) (nat_lit 0) A10K2.t2939 from rfl, allE_node, rows2938, irow2930, rows2939]
  all_goals rfl

theorem atot2930 : totK PA10K2 A10K2.u2930 = [0, 0, 776274244863, 3246328348989, 4128505968059, 1548871644263, 129685739508, 0, 0, 0] := by
  rw [show A10K2.u2930 = KTree.node A10K2.t2938 (nat_lit 48007224) (nat_lit 14769319574) (nat_lit 0) A10K2.t2939 from rfl, totK_node, tot2938, tot2939]
  decide +kernel

theorem arows2932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2932 = true := by
  rw [show A10K2.u2932 = KTree.node A10K2.t2940 (nat_lit 48021767) (nat_lit 9758942045) (nat_lit 0) A10K2.t2941 from rfl, allE_node, rows2940, irow2932, rows2941]
  all_goals rfl

theorem atot2932 : totK PA10K2 A10K2.u2932 = [0, 0, 685140889684, 2924084781097, 3961029779512, 1814969739997, 265116419838, 7007974415, 0, 0] := by
  rw [show A10K2.u2932 = KTree.node A10K2.t2940 (nat_lit 48021767) (nat_lit 9758942045) (nat_lit 0) A10K2.t2941 from rfl, totK_node, tot2940, tot2941]
  decide +kernel

theorem arows2933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2933 = true := by
  rw [show A10K2.u2933 = KTree.node A10K2.t2942 (nat_lit 48047281) (nat_lit 4659210060) (nat_lit 0) A10K2.t2943 from rfl, allE_node, rows2942, irow2933, rows2943]
  all_goals rfl

theorem atot2933 : totK PA10K2 A10K2.u2933 = [0, 525241347744, 2321422563549, 3640939850607, 2589615862124, 763142752281, 56820615133, 0, 0, 0] := by
  rw [show A10K2.u2933 = KTree.node A10K2.t2942 (nat_lit 48047281) (nat_lit 4659210060) (nat_lit 0) A10K2.t2943 from rfl, totK_node, tot2942, tot2943]
  decide +kernel

theorem arows2940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2940 = true := by
  rw [show A10K2.u2940 = KTree.node A10K2.t2944 (nat_lit 48051862) (nat_lit 14366830446) (nat_lit 0) A10K2.t2945 from rfl, allE_node, rows2944, irow2940, rows2945]
  all_goals rfl

theorem atot2940 : totK PA10K2 A10K2.u2940 = [0, 297281370121, 1917001946811, 4009983121921, 3002938990239, 628855385497, 31306924438, 0, 0, 0] := by
  rw [show A10K2.u2940 = KTree.node A10K2.t2944 (nat_lit 48051862) (nat_lit 14366830446) (nat_lit 0) A10K2.t2945 from rfl, totK_node, tot2944, tot2945]
  decide +kernel

theorem arows2941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2941 = true := by
  rw [show A10K2.u2941 = KTree.node A10K2.t2946 (nat_lit 48059569) (nat_lit 1898609198) (nat_lit 0) A10K2.t2947 from rfl, allE_node, rows2946, irow2941, rows2947]
  all_goals rfl

theorem atot2941 : totK PA10K2 A10K2.u2941 = [0, 679656139867, 2992121395440, 4080850372364, 1812292351711, 229069956136, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u2941 = KTree.node A10K2.t2946 (nat_lit 48059569) (nat_lit 1898609198) (nat_lit 0) A10K2.t2947 from rfl, totK_node, tot2946, tot2947]
  decide +kernel

theorem arows2943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2943 = true := by
  rw [show A10K2.u2943 = KTree.node A10K2.t2948 (nat_lit 48066097) (nat_lit 9515586386) (nat_lit 0) A10K2.t2949 from rfl, allE_node, rows2948, irow2943, rows2949]
  all_goals rfl

theorem atot2943 : totK PA10K2 A10K2.u2943 = [0, 613762948205, 2794140985576, 4177821307617, 2242836459926, 311077015807, 6279851884, 0, 0, 0] := by
  rw [show A10K2.u2943 = KTree.node A10K2.t2948 (nat_lit 48066097) (nat_lit 9515586386) (nat_lit 0) A10K2.t2949 from rfl, totK_node, tot2948, tot2949]
  decide +kernel

theorem arows2944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2944 = true := by
  rw [show A10K2.u2944 = KTree.node A10K2.t2950 (nat_lit 48080096) (nat_lit 5621889274) (nat_lit 0) A10K2.t2951 from rfl, allE_node, rows2950, irow2944, rows2951]
  all_goals rfl

theorem atot2944 : totK PA10K2 A10K2.u2944 = [0, 0, 914519772549, 3545779247177, 4009864214341, 1277674040225, 87826231206, 0, 0, 0] := by
  rw [show A10K2.u2944 = KTree.node A10K2.t2950 (nat_lit 48080096) (nat_lit 5621889274) (nat_lit 0) A10K2.t2951 from rfl, totK_node, tot2950, tot2951]
  decide +kernel

theorem arows2947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2947 = true := by
  rw [show A10K2.u2947 = KTree.node A10K2.t2952 (nat_lit 48084727) (nat_lit 9773258358) (nat_lit 0) A10K2.t2953 from rfl, allE_node, rows2952, irow2947, rows2953]
  all_goals rfl

theorem atot2947 : totK PA10K2 A10K2.u2947 = [0, 0, 607610986392, 2723439181915, 4082629824091, 2111131298263, 303927538966, 7151180950, 0, 0] := by
  rw [show A10K2.u2947 = KTree.node A10K2.t2952 (nat_lit 48084727) (nat_lit 9773258358) (nat_lit 0) A10K2.t2953 from rfl, totK_node, tot2952, tot2953]
  decide +kernel

theorem arows2948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2948 = true := by
  rw [show A10K2.u2948 = KTree.node A10K2.t2954 (nat_lit 48096930) (nat_lit 14432924140) (nat_lit 0) A10K2.t2955 from rfl, allE_node, rows2954, irow2948, rows2955]
  all_goals rfl

theorem atot2948 : totK PA10K2 A10K2.u2948 = [0, 113839911969, 1155085438018, 3588948940433, 3891941208188, 1218800167147, 75189232056, 0, 0, 0] := by
  rw [show A10K2.u2948 = KTree.node A10K2.t2954 (nat_lit 48096930) (nat_lit 14432924140) (nat_lit 0) A10K2.t2955 from rfl, totK_node, tot2954, tot2955]
  decide +kernel

theorem arows2950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2950 = true := by
  rw [show A10K2.u2950 = KTree.node A10K2.t2956 (nat_lit 48172466) (nat_lit 13770425449) (nat_lit 0) A10K2.t2957 from rfl, allE_node, rows2956, irow2950, rows2957]
  all_goals rfl

theorem atot2950 : totK PA10K2 A10K2.u2950 = [0, 611608007617, 2743757324975, 3850770062262, 1996157642504, 357697665518, 11991740650, 0, 0, 0] := by
  rw [show A10K2.u2950 = KTree.node A10K2.t2956 (nat_lit 48172466) (nat_lit 13770425449) (nat_lit 0) A10K2.t2957 from rfl, totK_node, tot2956, tot2957]
  decide +kernel

theorem arows2951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2951 = true := by
  rw [show A10K2.u2951 = KTree.node A10K2.t2958 (nat_lit 48178917) (nat_lit 6315755663) (nat_lit 0) A10K2.t2959 from rfl, allE_node, rows2958, irow2951, rows2959]
  all_goals rfl

theorem atot2951 : totK PA10K2 A10K2.u2951 = [0, 769230125203, 3163806137042, 4098769829648, 1698018769466, 156410302712, 0, 0, 0, 0] := by
  rw [show A10K2.u2951 = KTree.node A10K2.t2958 (nat_lit 48178917) (nat_lit 6315755663) (nat_lit 0) A10K2.t2959 from rfl, totK_node, tot2958, tot2959]
  decide +kernel

theorem arows2955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2955 = true := by
  rw [show A10K2.u2955 = KTree.node A10K2.t2960 (nat_lit 48184374) (nat_lit 16500716823) (nat_lit 0) A10K2.t2961 from rfl, allE_node, rows2960, irow2955, rows2961]
  all_goals rfl

theorem atot2955 : totK PA10K2 A10K2.u2955 = [0, 424089518694, 2164607309089, 4004938724987, 2717831606007, 479688849424, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u2955 = KTree.node A10K2.t2960 (nat_lit 48184374) (nat_lit 16500716823) (nat_lit 0) A10K2.t2961 from rfl, totK_node, tot2960, tot2961]
  decide +kernel

theorem arows2956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2956 = true := by
  rw [show A10K2.u2956 = KTree.node A10K2.t2962 (nat_lit 48197505) (nat_lit 9801645940) (nat_lit 0) A10K2.t2963 from rfl, allE_node, rows2962, irow2956, rows2963]
  all_goals rfl

theorem atot2956 : totK PA10K2 A10K2.u2956 = [0, 467252897767, 2480971100820, 4230760175776, 2494410767622, 357306661266, 6772895877, 0, 0, 0] := by
  rw [show A10K2.u2956 = KTree.node A10K2.t2962 (nat_lit 48197505) (nat_lit 9801645940) (nat_lit 0) A10K2.t2963 from rfl, totK_node, tot2962, tot2963]
  decide +kernel

theorem arows2958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2958 = true := by
  rw [show A10K2.u2958 = KTree.node A10K2.t2964 (nat_lit 48201993) (nat_lit 9792185400) (nat_lit 0) A10K2.t2965 from rfl, allE_node, rows2964, irow2958, rows2965]
  all_goals rfl

theorem atot2958 : totK PA10K2 A10K2.u2958 = [0, 0, 1051193734874, 3701280981912, 3883355447010, 1120410977859, 68058142506, 0, 0, 0] := by
  rw [show A10K2.u2958 = KTree.node A10K2.t2964 (nat_lit 48201993) (nat_lit 9792185400) (nat_lit 0) A10K2.t2965 from rfl, totK_node, tot2964, tot2965]
  decide +kernel

theorem arows2959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2959 = true := by
  rw [show A10K2.u2959 = KTree.node A10K2.t2966 (nat_lit 48208955) (nat_lit 5737680239) (nat_lit 0) A10K2.t2967 from rfl, allE_node, rows2966, irow2959, rows2967]
  all_goals rfl

theorem atot2959 : totK PA10K2 A10K2.u2959 = [0, 0, 446335997791, 2404787243320, 4258623331208, 2313016860367, 284871461903, 6318667960, 0, 0] := by
  rw [show A10K2.u2959 = KTree.node A10K2.t2966 (nat_lit 48208955) (nat_lit 5737680239) (nat_lit 0) A10K2.t2967 from rfl, totK_node, tot2966, tot2967]
  decide +kernel

theorem arows2962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2962 = true := by
  rw [show A10K2.u2962 = KTree.node A10K2.t2968 (nat_lit 48215478) (nat_lit 16601064730) (nat_lit 0) A10K2.t2969 from rfl, allE_node, rows2968, irow2962, rows2969]
  all_goals rfl

theorem atot2962 : totK PA10K2 A10K2.u2962 = [0, 0, 595027250046, 2846615782658, 4130457423302, 2128559993555, 277152403198, 6439430839, 0, 0] := by
  rw [show A10K2.u2962 = KTree.node A10K2.t2968 (nat_lit 48215478) (nat_lit 16601064730) (nat_lit 0) A10K2.t2969 from rfl, totK_node, tot2968, tot2969]
  decide +kernel

theorem arows2963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2963 = true := by
  rw [show A10K2.u2963 = KTree.node A10K2.t2970 (nat_lit 48229767) (nat_lit 14707663872) (nat_lit 0) A10K2.t2971 from rfl, allE_node, rows2970, irow2963, rows2971]
  all_goals rfl

theorem atot2963 : totK PA10K2 A10K2.u2963 = [0, 0, 608838009475, 2795499443379, 4094022652033, 1992461368403, 263027130122, 6021244195, 0, 0] := by
  rw [show A10K2.u2963 = KTree.node A10K2.t2970 (nat_lit 48229767) (nat_lit 14707663872) (nat_lit 0) A10K2.t2971 from rfl, totK_node, tot2970, tot2971]
  decide +kernel

theorem arows2965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2965 = true := by
  rw [show A10K2.u2965 = KTree.node A10K2.t2972 (nat_lit 48234231) (nat_lit 14496204204) (nat_lit 0) A10K2.t2973 from rfl, allE_node, rows2972, irow2965, rows2973]
  all_goals rfl

theorem atot2965 : totK PA10K2 A10K2.u2965 = [0, 552620952940, 1685270906194, 2042630793669, 2440606534774, 2265316144143, 720270842047, 54997142734, 0, 0] := by
  rw [show A10K2.u2965 = KTree.node A10K2.t2972 (nat_lit 48234231) (nat_lit 14496204204) (nat_lit 0) A10K2.t2973 from rfl, totK_node, tot2972, tot2973]
  decide +kernel

theorem arows2966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2966 = true := by
  rw [show A10K2.u2966 = KTree.node A10K2.t2974 (nat_lit 48238849) (nat_lit 10404522250) (nat_lit 0) A10K2.t2975 from rfl, allE_node, rows2974, irow2966, rows2975]
  all_goals rfl

theorem atot2966 : totK PA10K2 A10K2.u2966 = [0, 292098887399, 2062237884133, 4009220561451, 2631447298802, 550978578769, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2966 = KTree.node A10K2.t2974 (nat_lit 48238849) (nat_lit 10404522250) (nat_lit 0) A10K2.t2975 from rfl, totK_node, tot2974, tot2975]
  decide +kernel

theorem arows2971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2971 = true := by
  rw [show A10K2.u2971 = KTree.node A10K2.t2976 (nat_lit 48253101) (nat_lit 6561767260) (nat_lit 0) A10K2.t2977 from rfl, allE_node, rows2976, irow2971, rows2977]
  all_goals rfl

theorem atot2971 : totK PA10K2 A10K2.u2971 = [0, 560480332012, 2775599106561, 4253725495370, 1907166633229, 170827765275, 0, 0, 0, 0] := by
  rw [show A10K2.u2971 = KTree.node A10K2.t2976 (nat_lit 48253101) (nat_lit 6561767260) (nat_lit 0) A10K2.t2977 from rfl, totK_node, tot2976, tot2977]
  decide +kernel

theorem arows2972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2972 = true := by
  rw [show A10K2.u2972 = KTree.node A10K2.t2978 (nat_lit 48260798) (nat_lit 15400017336) (nat_lit 0) A10K2.t2979 from rfl, allE_node, rows2978, irow2972, rows2979]
  all_goals rfl

theorem atot2972 : totK PA10K2 A10K2.u2972 = [0, 800656750727, 3150254998882, 3991506078956, 1769391985326, 223779370171, 5976421810, 0, 0, 0] := by
  rw [show A10K2.u2972 = KTree.node A10K2.t2978 (nat_lit 48260798) (nat_lit 15400017336) (nat_lit 0) A10K2.t2979 from rfl, totK_node, tot2978, tot2979]
  decide +kernel

theorem arows2974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2974 = true := by
  rw [show A10K2.u2974 = KTree.node A10K2.t2980 (nat_lit 48266718) (nat_lit 15093312645) (nat_lit 0) A10K2.t2981 from rfl, allE_node, rows2980, irow2974, rows2981]
  all_goals rfl

theorem atot2974 : totK PA10K2 A10K2.u2974 = [0, 0, 919490107007, 3593058814371, 4148934766519, 1303199962355, 88310840913, 0, 0, 0] := by
  rw [show A10K2.u2974 = KTree.node A10K2.t2980 (nat_lit 48266718) (nat_lit 15093312645) (nat_lit 0) A10K2.t2981 from rfl, totK_node, tot2980, tot2981]
  decide +kernel

theorem arows2975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2975 = true := by
  rw [show A10K2.u2975 = KTree.node A10K2.t2982 (nat_lit 48271305) (nat_lit 5872982487) (nat_lit 0) A10K2.t2983 from rfl, allE_node, rows2982, irow2975, rows2983]
  all_goals rfl

theorem atot2975 : totK PA10K2 A10K2.u2975 = [0, 0, 485111030086, 2442350824242, 3854855186494, 2197738022209, 430137260517, 25239774317, 0, 0] := by
  rw [show A10K2.u2975 = KTree.node A10K2.t2982 (nat_lit 48271305) (nat_lit 5872982487) (nat_lit 0) A10K2.t2983 from rfl, totK_node, tot2982, tot2983]
  decide +kernel

theorem arows2978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2978 = true := by
  rw [show A10K2.u2978 = KTree.node A10K2.t2984 (nat_lit 48285745) (nat_lit 9713883039) (nat_lit 0) A10K2.t2985 from rfl, allE_node, rows2984, irow2978, rows2985]
  all_goals rfl

theorem atot2978 : totK PA10K2 A10K2.u2978 = [0, 0, 558424267006, 2860842822833, 4112014809621, 1716849510287, 214370929350, 5410721913, 0, 0] := by
  rw [show A10K2.u2978 = KTree.node A10K2.t2984 (nat_lit 48285745) (nat_lit 9713883039) (nat_lit 0) A10K2.t2985 from rfl, totK_node, tot2984, tot2985]
  decide +kernel

theorem arows2979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2979 = true := by
  rw [show A10K2.u2979 = KTree.node A10K2.t2986 (nat_lit 48293375) (nat_lit 13977239216) (nat_lit 0) A10K2.t2987 from rfl, allE_node, rows2986, irow2979, rows2987]
  all_goals rfl

theorem atot2979 : totK PA10K2 A10K2.u2979 = [0, 193918436879, 1215160158389, 3138731068640, 3601734210521, 1561283053103, 205049373882, 5546304973, 0, 0] := by
  rw [show A10K2.u2979 = KTree.node A10K2.t2986 (nat_lit 48293375) (nat_lit 13977239216) (nat_lit 0) A10K2.t2987 from rfl, totK_node, tot2986, tot2987]
  decide +kernel

theorem arows2981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2981 = true := by
  rw [show A10K2.u2981 = KTree.node A10K2.t2988 (nat_lit 48434582) (nat_lit 15994318953) (nat_lit 0) A10K2.t2989 from rfl, allE_node, rows2988, irow2981, rows2989]
  all_goals rfl

theorem atot2981 : totK PA10K2 A10K2.u2981 = [0, 590022855646, 2750915689908, 3990638732848, 2055300757860, 395067161560, 25351274858, 0, 0, 0] := by
  rw [show A10K2.u2981 = KTree.node A10K2.t2988 (nat_lit 48434582) (nat_lit 15994318953) (nat_lit 0) A10K2.t2989 from rfl, totK_node, tot2988, tot2989]
  decide +kernel

theorem arows2982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2982 = true := by
  rw [show A10K2.u2982 = KTree.node A10K2.t2990 (nat_lit 48440979) (nat_lit 10993800162) (nat_lit 0) A10K2.t2991 from rfl, allE_node, rows2990, irow2982, rows2991]
  all_goals rfl

theorem atot2982 : totK PA10K2 A10K2.u2982 = [0, 594570731468, 2777710364243, 4231638251356, 2183594982342, 292368026514, 5459593153, 0, 0, 0] := by
  rw [show A10K2.u2982 = KTree.node A10K2.t2990 (nat_lit 48440979) (nat_lit 10993800162) (nat_lit 0) A10K2.t2991 from rfl, totK_node, tot2990, tot2991]
  decide +kernel

theorem arows2986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2986 = true := by
  rw [show A10K2.u2986 = KTree.node A10K2.t2992 (nat_lit 48456090) (nat_lit 13385991784) (nat_lit 0) A10K2.t2993 from rfl, allE_node, rows2992, irow2986, rows2993]
  all_goals rfl

theorem atot2986 : totK PA10K2 A10K2.u2986 = [0, 701005875330, 2832254000728, 3942813124076, 2124106519277, 379061035497, 12681556880, 0, 0, 0] := by
  rw [show A10K2.u2986 = KTree.node A10K2.t2992 (nat_lit 48456090) (nat_lit 13385991784) (nat_lit 0) A10K2.t2993 from rfl, totK_node, tot2992, tot2993]
  decide +kernel

theorem arows2987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2987 = true := by
  rw [show A10K2.u2987 = KTree.node A10K2.t2994 (nat_lit 48460549) (nat_lit 5852490966) (nat_lit 0) A10K2.t2995 from rfl, allE_node, rows2994, irow2987, rows2995]
  all_goals rfl

theorem atot2987 : totK PA10K2 A10K2.u2987 = [0, 165731654200, 1693621595326, 4206498492994, 3317833474064, 659716378150, 19708922258, 0, 0, 0] := by
  rw [show A10K2.u2987 = KTree.node A10K2.t2994 (nat_lit 48460549) (nat_lit 5852490966) (nat_lit 0) A10K2.t2995 from rfl, totK_node, tot2994, tot2995]
  decide +kernel

theorem arows2989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2989 = true := by
  rw [show A10K2.u2989 = KTree.node A10K2.t2996 (nat_lit 48466184) (nat_lit 13716224831) (nat_lit 0) A10K2.t2997 from rfl, allE_node, rows2996, irow2989, rows2997]
  all_goals rfl

theorem atot2989 : totK PA10K2 A10K2.u2989 = [0, 0, 783794500080, 3222844799271, 4087927799616, 1624215896560, 145174496293, 0, 0, 0] := by
  rw [show A10K2.u2989 = KTree.node A10K2.t2996 (nat_lit 48466184) (nat_lit 13716224831) (nat_lit 0) A10K2.t2997 from rfl, totK_node, tot2996, tot2997]
  decide +kernel

theorem arows2990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2990 = true := by
  rw [show A10K2.u2990 = KTree.node A10K2.t2998 (nat_lit 48473307) (nat_lit 9773256128) (nat_lit 0) A10K2.t2999 from rfl, allE_node, rows2998, irow2990, rows2999]
  all_goals rfl

theorem atot2990 : totK PA10K2 A10K2.u2990 = [0, 0, 593535314503, 2706606495455, 4196969428364, 2171476430899, 290798274090, 6904928264, 0, 0] := by
  rw [show A10K2.u2990 = KTree.node A10K2.t2998 (nat_lit 48473307) (nat_lit 9773256128) (nat_lit 0) A10K2.t2999 from rfl, totK_node, tot2998, tot2999]
  decide +kernel

theorem arows2993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2993 = true := by
  rw [show A10K2.u2993 = KTree.node A10K2.t3000 (nat_lit 48488502) (nat_lit 16097883093) (nat_lit 0) A10K2.t3001 from rfl, allE_node, rows3000, irow2993, rows3001]
  all_goals rfl

theorem atot2993 : totK PA10K2 A10K2.u2993 = [0, 0, 538702996020, 2665728707500, 4188434085043, 2250529102557, 291019008573, 6766355402, 0, 0] := by
  rw [show A10K2.u2993 = KTree.node A10K2.t3000 (nat_lit 48488502) (nat_lit 16097883093) (nat_lit 0) A10K2.t3001 from rfl, totK_node, tot3000, tot3001]
  decide +kernel

theorem arows2994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2994 = true := by
  rw [show A10K2.u2994 = KTree.node A10K2.t3002 (nat_lit 48493041) (nat_lit 8671897886) (nat_lit 0) A10K2.t3003 from rfl, allE_node, rows3002, irow2994, rows3003]
  all_goals rfl

theorem atot2994 : totK PA10K2 A10K2.u2994 = [0, 0, 327234200007, 2057195932205, 4141345119480, 2886280651268, 472310371782, 12224107035, 0, 0] := by
  rw [show A10K2.u2994 = KTree.node A10K2.t3002 (nat_lit 48493041) (nat_lit 8671897886) (nat_lit 0) A10K2.t3003 from rfl, totK_node, tot3002, tot3003]
  decide +kernel

theorem arows2996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2996 = true := by
  rw [show A10K2.u2996 = KTree.node A10K2.t3004 (nat_lit 48497591) (nat_lit 14902078619) (nat_lit 0) A10K2.t3005 from rfl, allE_node, rows3004, irow2996, rows3005]
  all_goals rfl

theorem atot2996 : totK PA10K2 A10K2.u2996 = [0, 0, 844719840339, 3035653372653, 3497706498786, 1792744508594, 533351460869, 48886019071, 0, 0] := by
  rw [show A10K2.u2996 = KTree.node A10K2.t3004 (nat_lit 48497591) (nat_lit 14902078619) (nat_lit 0) A10K2.t3005 from rfl, totK_node, tot3004, tot3005]
  decide +kernel

theorem arows2997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2997 = true := by
  rw [show A10K2.u2997 = KTree.node A10K2.t3006 (nat_lit 48503303) (nat_lit 10794192655) (nat_lit 0) A10K2.t3007 from rfl, allE_node, rows3006, irow2997, rows3007]
  all_goals rfl

theorem atot2997 : totK PA10K2 A10K2.u2997 = [0, 0, 291919316456, 1862811252013, 3902127756764, 2837525127448, 596395951494, 30831673886, 0, 0] := by
  rw [show A10K2.u2997 = KTree.node A10K2.t3006 (nat_lit 48503303) (nat_lit 10794192655) (nat_lit 0) A10K2.t3007 from rfl, totK_node, tot3006, tot3007]
  decide +kernel

theorem arows3003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3003 = true := by
  rw [show A10K2.u3003 = KTree.node A10K2.t3008 (nat_lit 48519314) (nat_lit 13970282471) (nat_lit 0) A10K2.t3009 from rfl, allE_node, rows3008, irow3003, rows3009]
  all_goals rfl

theorem atot3003 : totK PA10K2 A10K2.u3003 = [0, 0, 645038917417, 2794903353968, 4014627583625, 1825104446117, 224777357882, 5705019915, 0, 0] := by
  rw [show A10K2.u3003 = KTree.node A10K2.t3008 (nat_lit 48519314) (nat_lit 13970282471) (nat_lit 0) A10K2.t3009 from rfl, totK_node, tot3008, tot3009]
  decide +kernel

theorem arows3004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3004 = true := by
  rw [show A10K2.u3004 = KTree.node A10K2.t3010 (nat_lit 48525316) (nat_lit 11396332684) (nat_lit 0) A10K2.t3011 from rfl, allE_node, rows3010, irow3004, rows3011]
  all_goals rfl

theorem atot3004 : totK PA10K2 A10K2.u3004 = [0, 0, 424178848866, 2515295121535, 4323550771806, 2489844782126, 354569380808, 6853348008, 0, 0] := by
  rw [show A10K2.u3004 = KTree.node A10K2.t3010 (nat_lit 48525316) (nat_lit 11396332684) (nat_lit 0) A10K2.t3011 from rfl, totK_node, tot3010, tot3011]
  decide +kernel

theorem arows3006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3006 = true := by
  rw [show A10K2.u3006 = KTree.node A10K2.t3012 (nat_lit 48531469) (nat_lit 5811818217) (nat_lit 0) A10K2.t3013 from rfl, allE_node, rows3012, irow3006, rows3013]
  all_goals rfl

theorem atot3006 : totK PA10K2 A10K2.u3006 = [0, 0, 0, 850124517596, 3501467745710, 3965834209932, 1231273537959, 88038342352, 0, 0] := by
  rw [show A10K2.u3006 = KTree.node A10K2.t3012 (nat_lit 48531469) (nat_lit 5811818217) (nat_lit 0) A10K2.t3013 from rfl, totK_node, tot3012, tot3013]
  decide +kernel

theorem arows3007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3007 = true := by
  rw [show A10K2.u3007 = KTree.node A10K2.t3014 (nat_lit 48537044) (nat_lit 341183547) (nat_lit 0) A10K2.t3015 from rfl, allE_node, rows3014, irow3007, rows3015]
  all_goals rfl

theorem atot3007 : totK PA10K2 A10K2.u3007 = [0, 0, 0, 553529002408, 2697703606605, 3961437277038, 1884550288893, 286873715814, 7237400819, 0] := by
  rw [show A10K2.u3007 = KTree.node A10K2.t3014 (nat_lit 48537044) (nat_lit 341183547) (nat_lit 0) A10K2.t3015 from rfl, totK_node, tot3014, tot3015]
  decide +kernel

theorem arows3010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3010 = true := by
  rw [show A10K2.u3010 = KTree.node A10K2.t3016 (nat_lit 48557445) (nat_lit 4084932589) (nat_lit 0) A10K2.t3017 from rfl, allE_node, rows3016, irow3010, rows3017]
  all_goals rfl

theorem atot3010 : totK PA10K2 A10K2.u3010 = [0, 0, 303693864090, 1903268537840, 3858741674748, 3062216113856, 757552262120, 47303685681, 0, 0] := by
  rw [show A10K2.u3010 = KTree.node A10K2.t3016 (nat_lit 48557445) (nat_lit 4084932589) (nat_lit 0) A10K2.t3017 from rfl, totK_node, tot3016, tot3017]
  decide +kernel

theorem arows3011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3011 = true := by
  rw [show A10K2.u3011 = KTree.node A10K2.t3018 (nat_lit 48697348) (nat_lit 11952560992) (nat_lit 0) A10K2.t3019 from rfl, allE_node, rows3018, irow3011, rows3019]
  all_goals rfl

theorem atot3011 : totK PA10K2 A10K2.u3011 = [0, 0, 480247428435, 2490275593935, 4104795041721, 2342792373651, 388896250441, 12473006693, 0, 0] := by
  rw [show A10K2.u3011 = KTree.node A10K2.t3018 (nat_lit 48697348) (nat_lit 11952560992) (nat_lit 0) A10K2.t3019 from rfl, totK_node, tot3018, tot3019]
  decide +kernel

theorem arows3013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3013 = true := by
  rw [show A10K2.u3013 = KTree.node A10K2.t3020 (nat_lit 48705037) (nat_lit 2942653931) (nat_lit 0) A10K2.t3021 from rfl, allE_node, rows3020, irow3013, rows3021]
  all_goals rfl

theorem atot3013 : totK PA10K2 A10K2.u3013 = [0, 0, 594293228886, 2770646838998, 4186194340053, 2270535150953, 293505236272, 6860445330, 0, 0] := by
  rw [show A10K2.u3013 = KTree.node A10K2.t3020 (nat_lit 48705037) (nat_lit 2942653931) (nat_lit 0) A10K2.t3021 from rfl, totK_node, tot3020, tot3021]
  decide +kernel

theorem arows3014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3014 = true := by
  rw [show A10K2.u3014 = KTree.node A10K2.t3022 (nat_lit 48719539) (nat_lit 10276812094) (nat_lit 0) A10K2.t3023 from rfl, allE_node, rows3022, irow3014, rows3023]
  all_goals rfl

theorem atot3014 : totK PA10K2 A10K2.u3014 = [0, 0, 866737529530, 3337209333054, 4043906131932, 1551979090686, 136886545499, 0, 0, 0] := by
  rw [show A10K2.u3014 = KTree.node A10K2.t3022 (nat_lit 48719539) (nat_lit 10276812094) (nat_lit 0) A10K2.t3023 from rfl, totK_node, tot3022, tot3023]
  decide +kernel

theorem arows3018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3018 = true := by
  rw [show A10K2.u3018 = KTree.node A10K2.t3024 (nat_lit 48725164) (nat_lit 3764429051) (nat_lit 0) A10K2.t3025 from rfl, allE_node, rows3024, irow3018, rows3025]
  all_goals rfl

theorem atot3018 : totK PA10K2 A10K2.u3018 = [0, 320479959089, 972451722066, 1532051309740, 3027768521216, 3163825558972, 936268093573, 62368562949, 0, 0] := by
  rw [show A10K2.u3018 = KTree.node A10K2.t3024 (nat_lit 48725164) (nat_lit 3764429051) (nat_lit 0) A10K2.t3025 from rfl, totK_node, tot3024, tot3025]
  decide +kernel

theorem arows3019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3019 = true := by
  rw [show A10K2.u3019 = KTree.node A10K2.t3026 (nat_lit 48836096) (nat_lit 11736345994) (nat_lit 0) A10K2.t3027 from rfl, allE_node, rows3026, irow3019, rows3027]
  all_goals rfl

theorem atot3019 : totK PA10K2 A10K2.u3019 = [0, 541416715838, 2587568406079, 3966831142661, 2187324034514, 421706860988, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u3019 = KTree.node A10K2.t3026 (nat_lit 48836096) (nat_lit 11736345994) (nat_lit 0) A10K2.t3027 from rfl, totK_node, tot3026, tot3027]
  decide +kernel

theorem arows3021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3021 = true := by
  rw [show A10K2.u3021 = KTree.node A10K2.t3028 (nat_lit 48841948) (nat_lit 11129437821) (nat_lit 0) A10K2.t3029 from rfl, allE_node, rows3028, irow3021, rows3029]
  all_goals rfl

theorem atot3021 : totK PA10K2 A10K2.u3021 = [0, 643544332899, 2800978424181, 3954798463705, 1939720160293, 266179753999, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u3021 = KTree.node A10K2.t3028 (nat_lit 48841948) (nat_lit 11129437821) (nat_lit 0) A10K2.t3029 from rfl, totK_node, tot3028, tot3029]
  decide +kernel

theorem arows3022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3022 = true := by
  rw [show A10K2.u3022 = KTree.node A10K2.t3030 (nat_lit 48849284) (nat_lit 4919956017) (nat_lit 0) A10K2.t3031 from rfl, allE_node, rows3030, irow3022, rows3031]
  all_goals rfl

theorem atot3022 : totK PA10K2 A10K2.u3022 = [0, 663979261139, 2787964248196, 4063706890982, 2002302800397, 240065064856, 5982052406, 0, 0, 0] := by
  rw [show A10K2.u3022 = KTree.node A10K2.t3030 (nat_lit 48849284) (nat_lit 4919956017) (nat_lit 0) A10K2.t3031 from rfl, totK_node, tot3030, tot3031]
  decide +kernel

theorem arows3025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3025 = true := by
  rw [show A10K2.u3025 = KTree.node A10K2.t3032 (nat_lit 48854252) (nat_lit 11100827000) (nat_lit 0) A10K2.t3033 from rfl, allE_node, rows3032, irow3025, rows3033]
  all_goals rfl

theorem atot3025 : totK PA10K2 A10K2.u3025 = [0, 119627100822, 1596382895918, 4111504554288, 3488131368135, 790077616633, 25359001435, 0, 0, 0] := by
  rw [show A10K2.u3025 = KTree.node A10K2.t3032 (nat_lit 48854252) (nat_lit 11100827000) (nat_lit 0) A10K2.t3033 from rfl, totK_node, tot3032, tot3033]
  decide +kernel

theorem arows3026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3026 = true := by
  rw [show A10K2.u3026 = KTree.node A10K2.t3034 (nat_lit 48867669) (nat_lit 6960785344) (nat_lit 0) A10K2.t3035 from rfl, allE_node, rows3034, irow3026, rows3035]
  all_goals rfl

theorem atot3026 : totK PA10K2 A10K2.u3026 = [0, 0, 860163598482, 3355847540241, 3965535734123, 1447915233751, 125632015561, 0, 0, 0] := by
  rw [show A10K2.u3026 = KTree.node A10K2.t3034 (nat_lit 48867669) (nat_lit 6960785344) (nat_lit 0) A10K2.t3035 from rfl, totK_node, tot3034, tot3035]
  decide +kernel

theorem arows3028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3028 = true := by
  rw [show A10K2.u3028 = KTree.node A10K2.t3036 (nat_lit 48872625) (nat_lit 5343170184) (nat_lit 0) A10K2.t3037 from rfl, allE_node, rows3036, irow3028, rows3037]
  all_goals rfl

theorem atot3028 : totK PA10K2 A10K2.u3028 = [0, 0, 435104128367, 2111821298424, 3795572857827, 2530673211652, 546059511866, 31082886609, 0, 0] := by
  rw [show A10K2.u3028 = KTree.node A10K2.t3036 (nat_lit 48872625) (nat_lit 5343170184) (nat_lit 0) A10K2.t3037 from rfl, totK_node, tot3036, tot3037]
  decide +kernel

theorem arows3029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3029 = true := by
  rw [show A10K2.u3029 = KTree.node A10K2.t3038 (nat_lit 48879826) (nat_lit 14935241105) (nat_lit 0) A10K2.t3039 from rfl, allE_node, rows3038, irow3029, rows3039]
  all_goals rfl

theorem atot3029 : totK PA10K2 A10K2.u3029 = [0, 0, 692610448318, 2966530698225, 3981993007029, 1706771500541, 207666718636, 5885702948, 0, 0] := by
  rw [show A10K2.u3029 = KTree.node A10K2.t3038 (nat_lit 48879826) (nat_lit 14935241105) (nat_lit 0) A10K2.t3039 from rfl, totK_node, tot3038, tot3039]
  decide +kernel

theorem arows3034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3034 = true := by
  rw [show A10K2.u3034 = KTree.node A10K2.t3040 (nat_lit 48899228) (nat_lit 11653260701) (nat_lit 0) A10K2.t3041 from rfl, allE_node, rows3040, irow3034, rows3041]
  all_goals rfl

theorem atot3034 : totK PA10K2 A10K2.u3034 = [0, 575843650046, 2316018331321, 3412837253884, 2627268575349, 917027443315, 76351749596, 0, 0, 0] := by
  rw [show A10K2.u3034 = KTree.node A10K2.t3040 (nat_lit 48899228) (nat_lit 11653260701) (nat_lit 0) A10K2.t3041 from rfl, totK_node, tot3040, tot3041]
  decide +kernel

theorem arows3035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3035 = true := by
  rw [show A10K2.u3035 = KTree.node A10K2.t3042 (nat_lit 48903904) (nat_lit 5857453627) (nat_lit 0) A10K2.t3043 from rfl, allE_node, rows3042, irow3035, rows3043]
  all_goals rfl

theorem atot3035 : totK PA10K2 A10K2.u3035 = [0, 323228085410, 1915061833916, 4048823420434, 2999503245460, 601748639491, 31543789865, 0, 0, 0] := by
  rw [show A10K2.u3035 = KTree.node A10K2.t3042 (nat_lit 48903904) (nat_lit 5857453627) (nat_lit 0) A10K2.t3043 from rfl, totK_node, tot3042, tot3043]
  decide +kernel

theorem arows3037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3037 = true := by
  rw [show A10K2.u3037 = KTree.node A10K2.t3044 (nat_lit 48908460) (nat_lit 13164463702) (nat_lit 0) A10K2.t3045 from rfl, allE_node, rows3044, irow3037, rows3045]
  all_goals rfl

theorem atot3037 : totK PA10K2 A10K2.u3037 = [0, 639500710750, 3009581286862, 4112190157664, 1639090170838, 138244987727, 0, 0, 0, 0] := by
  rw [show A10K2.u3037 = KTree.node A10K2.t3044 (nat_lit 48908460) (nat_lit 13164463702) (nat_lit 0) A10K2.t3045 from rfl, totK_node, tot3044, tot3045]
  decide +kernel

theorem arows3038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3038 = true := by
  rw [show A10K2.u3038 = KTree.node A10K2.t3046 (nat_lit 48932717) (nat_lit 5526792442) (nat_lit 0) A10K2.t3047 from rfl, allE_node, rows3046, irow3038, rows3047]
  all_goals rfl

theorem atot3038 : totK PA10K2 A10K2.u3038 = [0, 0, 1078754128845, 3861023415757, 3820702037455, 959025932855, 45698759736, 0, 0, 0] := by
  rw [show A10K2.u3038 = KTree.node A10K2.t3046 (nat_lit 48932717) (nat_lit 5526792442) (nat_lit 0) A10K2.t3047 from rfl, totK_node, tot3046, tot3047]
  decide +kernel

theorem arows3041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3041 = true := by
  rw [show A10K2.u3041 = KTree.node A10K2.t3048 (nat_lit 48941242) (nat_lit 13555926055) (nat_lit 0) A10K2.t3049 from rfl, allE_node, rows3048, irow3041, rows3049]
  all_goals rfl

theorem atot3041 : totK PA10K2 A10K2.u3041 = [0, 0, 663618996947, 3156685388310, 4156626800111, 1309513677153, 80882596222, 0, 0, 0] := by
  rw [show A10K2.u3041 = KTree.node A10K2.t3048 (nat_lit 48941242) (nat_lit 13555926055) (nat_lit 0) A10K2.t3049 from rfl, totK_node, tot3048, tot3049]
  decide +kernel

theorem arows3042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3042 = true := by
  rw [show A10K2.u3042 = KTree.node A10K2.t3050 (nat_lit 48958641) (nat_lit 6872407935) (nat_lit 0) A10K2.t3051 from rfl, allE_node, rows3050, irow3042, rows3051]
  all_goals rfl

theorem atot3042 : totK PA10K2 A10K2.u3042 = [0, 556621861187, 2300511639272, 3369509103549, 2321482930673, 976019032629, 177130544212, 6354482628, 0, 0] := by
  rw [show A10K2.u3042 = KTree.node A10K2.t3050 (nat_lit 48958641) (nat_lit 6872407935) (nat_lit 0) A10K2.t3051 from rfl, totK_node, tot3050, tot3051]
  decide +kernel

theorem arows3044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3044 = true := by
  rw [show A10K2.u3044 = KTree.node A10K2.t3052 (nat_lit 48965804) (nat_lit 12918673961) (nat_lit 0) A10K2.t3053 from rfl, allE_node, rows3052, irow3044, rows3053]
  all_goals rfl

theorem atot3044 : totK PA10K2 A10K2.u3044 = [0, 804252991483, 3300126275192, 4146497661929, 1646550534903, 159984704953, 0, 0, 0, 0] := by
  rw [show A10K2.u3044 = KTree.node A10K2.t3052 (nat_lit 48965804) (nat_lit 12918673961) (nat_lit 0) A10K2.t3053 from rfl, totK_node, tot3052, tot3053]
  decide +kernel

theorem arows3045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3045 = true := by
  rw [show A10K2.u3045 = KTree.node A10K2.t3054 (nat_lit 48970865) (nat_lit 7688012592) (nat_lit 0) A10K2.t3055 from rfl, allE_node, rows3054, irow3045, rows3055]
  all_goals rfl

theorem atot3045 : totK PA10K2 A10K2.u3045 = [0, 490038649257, 2245612676713, 3798647853761, 2621862057900, 577475115931, 31522233512, 0, 0, 0] := by
  rw [show A10K2.u3045 = KTree.node A10K2.t3054 (nat_lit 48970865) (nat_lit 7688012592) (nat_lit 0) A10K2.t3055 from rfl, totK_node, tot3054, tot3055]
  decide +kernel

theorem arows3049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3049 = true := by
  rw [show A10K2.u3049 = KTree.node A10K2.t3056 (nat_lit 48984008) (nat_lit 12751923964) (nat_lit 0) A10K2.t3057 from rfl, allE_node, rows3056, irow3049, rows3057]
  all_goals rfl

theorem atot3049 : totK PA10K2 A10K2.u3049 = [0, 359360087617, 2213058867660, 4180781882666, 2718171565186, 499587130880, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u3049 = KTree.node A10K2.t3056 (nat_lit 48984008) (nat_lit 12751923964) (nat_lit 0) A10K2.t3057 from rfl, totK_node, tot3056, tot3057]
  decide +kernel

theorem arows3050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3050 = true := by
  rw [show A10K2.u3050 = KTree.node A10K2.t3058 (nat_lit 48988634) (nat_lit 10986726780) (nat_lit 0) A10K2.t3059 from rfl, allE_node, rows3058, irow3050, rows3059]
  all_goals rfl

theorem atot3050 : totK PA10K2 A10K2.u3050 = [0, 0, 882102330457, 3423554794365, 4089000607282, 1499017666558, 121303278978, 0, 0, 0] := by
  rw [show A10K2.u3050 = KTree.node A10K2.t3058 (nat_lit 48988634) (nat_lit 10986726780) (nat_lit 0) A10K2.t3059 from rfl, totK_node, tot3058, tot3059]
  decide +kernel

theorem arows3052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3052 = true := by
  rw [show A10K2.u3052 = KTree.node A10K2.t3060 (nat_lit 48997846) (nat_lit 15557456960) (nat_lit 0) A10K2.t3061 from rfl, allE_node, rows3060, irow3052, rows3061]
  all_goals rfl

theorem atot3052 : totK PA10K2 A10K2.u3052 = [0, 0, 804109052366, 3088624539993, 3908196849652, 1839686572184, 248235381104, 6632180018, 0, 0] := by
  rw [show A10K2.u3052 = KTree.node A10K2.t3060 (nat_lit 48997846) (nat_lit 15557456960) (nat_lit 0) A10K2.t3061 from rfl, totK_node, tot3060, tot3061]
  decide +kernel

theorem arows3053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3053 = true := by
  rw [show A10K2.u3053 = KTree.node A10K2.t3062 (nat_lit 49002838) (nat_lit 9448495918) (nat_lit 0) A10K2.t3063 from rfl, allE_node, rows3062, irow3053, rows3063]
  all_goals rfl

theorem atot3053 : totK PA10K2 A10K2.u3053 = [0, 0, 395707756605, 2345877130524, 4249084825045, 2484168141813, 345224472405, 7047025452, 0, 0] := by
  rw [show A10K2.u3053 = KTree.node A10K2.t3062 (nat_lit 49002838) (nat_lit 9448495918) (nat_lit 0) A10K2.t3063 from rfl, totK_node, tot3062, tot3063]
  decide +kernel

theorem arows3056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3056 = true := by
  rw [show A10K2.u3056 = KTree.node A10K2.t3064 (nat_lit 49016711) (nat_lit 14658428996) (nat_lit 0) A10K2.t3065 from rfl, allE_node, rows3064, irow3056, rows3065]
  all_goals rfl

theorem atot3056 : totK PA10K2 A10K2.u3056 = [0, 0, 466005079570, 2448638492801, 4092363267265, 2485684121737, 402904429948, 12224107035, 0, 0] := by
  rw [show A10K2.u3056 = KTree.node A10K2.t3064 (nat_lit 49016711) (nat_lit 14658428996) (nat_lit 0) A10K2.t3065 from rfl, totK_node, tot3064, tot3065]
  decide +kernel

theorem arows3057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3057 = true := by
  rw [show A10K2.u3057 = KTree.node A10K2.t3066 (nat_lit 49096037) (nat_lit 7215580020) (nat_lit 0) A10K2.t3067 from rfl, allE_node, rows3066, irow3057, rows3067]
  all_goals rfl

theorem atot3057 : totK PA10K2 A10K2.u3057 = [0, 0, 702439704561, 2667637163431, 3545350053448, 2151734779700, 608943561740, 48886019071, 0, 0] := by
  rw [show A10K2.u3057 = KTree.node A10K2.t3066 (nat_lit 49096037) (nat_lit 7215580020) (nat_lit 0) A10K2.t3067 from rfl, totK_node, tot3066, tot3067]
  decide +kernel

theorem arows3059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3059 = true := by
  rw [show A10K2.u3059 = KTree.node A10K2.t3068 (nat_lit 49100548) (nat_lit 11262964285) (nat_lit 0) A10K2.t3069 from rfl, allE_node, rows3068, irow3059, rows3069]
  all_goals rfl

theorem atot3059 : totK PA10K2 A10K2.u3059 = [0, 0, 232019765432, 1823977943239, 4025089464444, 3003992801356, 605845418817, 31543789865, 0, 0] := by
  rw [show A10K2.u3059 = KTree.node A10K2.t3068 (nat_lit 49100548) (nat_lit 11262964285) (nat_lit 0) A10K2.t3069 from rfl, totK_node, tot3068, tot3069]
  decide +kernel

theorem arows3060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3060 = true := by
  rw [show A10K2.u3060 = KTree.node A10K2.t3070 (nat_lit 49105595) (nat_lit 6474281311) (nat_lit 0) A10K2.t3071 from rfl, allE_node, rows3070, irow3060, rows3071]
  all_goals rfl

theorem atot3060 : totK PA10K2 A10K2.u3060 = [0, 0, 573275469022, 2701882168722, 4039885254694, 1885909456672, 228970814135, 5982052406, 0, 0] := by
  rw [show A10K2.u3060 = KTree.node A10K2.t3070 (nat_lit 49105595) (nat_lit 6474281311) (nat_lit 0) A10K2.t3071 from rfl, totK_node, tot3070, tot3071]
  decide +kernel

theorem arows3070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3070 = true := by
  rw [show A10K2.u3070 = KTree.node A10K2.t3072 (nat_lit 49114185) (nat_lit 8305260632) (nat_lit 0) A10K2.t3073 from rfl, allE_node, rows3072, irow3070, rows3073]
  all_goals rfl

theorem atot3070 : totK PA10K2 A10K2.u3070 = [0, 0, 776975258324, 3219907475482, 4204993680300, 1801389744735, 189536503065, 0, 0, 0] := by
  rw [show A10K2.u3070 = KTree.node A10K2.t3072 (nat_lit 49114185) (nat_lit 8305260632) (nat_lit 0) A10K2.t3073 from rfl, totK_node, tot3072, tot3073]
  decide +kernel

theorem arows3071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3071 = true := by
  rw [show A10K2.u3071 = KTree.node A10K2.t3074 (nat_lit 49119134) (nat_lit 15472625972) (nat_lit 0) A10K2.t3075 from rfl, allE_node, rows3074, irow3071, rows3075]
  all_goals rfl

theorem atot3071 : totK PA10K2 A10K2.u3071 = [0, 0, 0, 1052777614608, 3749258133617, 3805231448277, 1079607609511, 67324059887, 0, 0] := by
  rw [show A10K2.u3071 = KTree.node A10K2.t3074 (nat_lit 49119134) (nat_lit 15472625972) (nat_lit 0) A10K2.t3075 from rfl, totK_node, tot3074, tot3075]
  decide +kernel

theorem arows3073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3073 = true := by
  rw [show A10K2.u3073 = KTree.node A10K2.t3076 (nat_lit 49132954) (nat_lit 15023698103) (nat_lit 0) A10K2.t3077 from rfl, allE_node, rows3076, irow3073, rows3077]
  all_goals rfl

theorem atot3073 : totK PA10K2 A10K2.u3073 = [0, 0, 0, 484267249085, 2578657646281, 4122326362715, 2108904076126, 310347174173, 7380853412, 0] := by
  rw [show A10K2.u3073 = KTree.node A10K2.t3076 (nat_lit 49132954) (nat_lit 15023698103) (nat_lit 0) A10K2.t3077 from rfl, totK_node, tot3076, tot3077]
  decide +kernel

theorem arows3074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3074 = true := by
  rw [show A10K2.u3074 = KTree.node A10K2.t3078 (nat_lit 49144262) (nat_lit 15521492747) (nat_lit 0) A10K2.t3079 from rfl, allE_node, rows3078, irow3074, rows3079]
  all_goals rfl

theorem atot3074 : totK PA10K2 A10K2.u3074 = [0, 0, 0, 1231522811494, 4155388720203, 3667270145175, 736240627798, 24346292730, 0, 0] := by
  rw [show A10K2.u3074 = KTree.node A10K2.t3078 (nat_lit 49144262) (nat_lit 15521492747) (nat_lit 0) A10K2.t3079 from rfl, totK_node, tot3078, tot3079]
  decide +kernel

theorem arows3077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3077 = true := by
  rw [show A10K2.u3077 = KTree.node A10K2.t3080 (nat_lit 49162483) (nat_lit 10106281549) (nat_lit 0) A10K2.t3081 from rfl, allE_node, rows3080, irow3077, rows3081]
  all_goals rfl

theorem atot3077 : totK PA10K2 A10K2.u3077 = [0, 0, 968799304382, 3427393454494, 3669036621692, 1456169595525, 341860417709, 31276155898, 0, 0] := by
  rw [show A10K2.u3077 = KTree.node A10K2.t3080 (nat_lit 49162483) (nat_lit 10106281549) (nat_lit 0) A10K2.t3081 from rfl, totK_node, tot3080, tot3081]
  decide +kernel

theorem arows3078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3078 = true := by
  rw [show A10K2.u3078 = KTree.node A10K2.t3082 (nat_lit 49170772) (nat_lit 13140071320) (nat_lit 0) A10K2.t3083 from rfl, allE_node, rows3082, irow3078, rows3083]
  all_goals rfl

theorem atot3078 : totK PA10K2 A10K2.u3078 = [0, 0, 569306206854, 2905616201997, 4231625069017, 1602508235849, 118244226082, 0, 0, 0] := by
  rw [show A10K2.u3078 = KTree.node A10K2.t3082 (nat_lit 49170772) (nat_lit 13140071320) (nat_lit 0) A10K2.t3083 from rfl, totK_node, tot3082, tot3083]
  decide +kernel

theorem arows3080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3080 = true := by
  rw [show A10K2.u3080 = KTree.node A10K2.t3084 (nat_lit 49221065) (nat_lit 6782221256) (nat_lit 0) A10K2.t3085 from rfl, allE_node, rows3084, irow3080, rows3085]
  all_goals rfl

theorem atot3080 : totK PA10K2 A10K2.u3080 = [0, 0, 556621861187, 2480480780935, 3968899638230, 2419060669882, 398465373951, 13079907231, 0, 0] := by
  rw [show A10K2.u3080 = KTree.node A10K2.t3084 (nat_lit 49221065) (nat_lit 6782221256) (nat_lit 0) A10K2.t3085 from rfl, totK_node, tot3084, tot3085]
  decide +kernel

theorem arows3081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3081 = true := by
  rw [show A10K2.u3081 = KTree.node A10K2.t3086 (nat_lit 49228448) (nat_lit 4515861476) (nat_lit 0) A10K2.t3087 from rfl, allE_node, rows3086, irow3081, rows3087]
  all_goals rfl

theorem atot3081 : totK PA10K2 A10K2.u3081 = [0, 0, 800495458520, 3238144610205, 4088437431076, 1652396216345, 148276566899, 0, 0, 0] := by
  rw [show A10K2.u3081 = KTree.node A10K2.t3086 (nat_lit 49228448) (nat_lit 4515861476) (nat_lit 0) A10K2.t3087 from rfl, totK_node, tot3086, tot3087]
  decide +kernel

theorem arows3085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3085 = true := by
  rw [show A10K2.u3085 = KTree.node A10K2.t3088 (nat_lit 49233402) (nat_lit 13252596604) (nat_lit 0) A10K2.t3089 from rfl, allE_node, rows3088, irow3085, rows3089]
  all_goals rfl

theorem atot3085 : totK PA10K2 A10K2.u3085 = [0, 0, 533568215722, 2438438714007, 3965319499610, 2476260374418, 438440051295, 12692412833, 0, 0] := by
  rw [show A10K2.u3085 = KTree.node A10K2.t3088 (nat_lit 49233402) (nat_lit 13252596604) (nat_lit 0) A10K2.t3089 from rfl, totK_node, tot3088, tot3089]
  decide +kernel

theorem arows3086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3086 = true := by
  rw [show A10K2.u3086 = KTree.node A10K2.t3090 (nat_lit 49246654) (nat_lit 16287430150) (nat_lit 0) A10K2.t3091 from rfl, allE_node, rows3090, irow3086, rows3091]
  all_goals rfl

theorem atot3086 : totK PA10K2 A10K2.u3086 = [0, 0, 327251851251, 2086276311817, 4152280603977, 2894597758585, 494615219065, 13244237517, 0, 0] := by
  rw [show A10K2.u3086 = KTree.node A10K2.t3090 (nat_lit 49246654) (nat_lit 16287430150) (nat_lit 0) A10K2.t3091 from rfl, totK_node, tot3090, tot3091]
  decide +kernel

theorem arows3088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3088 = true := by
  rw [show A10K2.u3088 = KTree.node A10K2.t3092 (nat_lit 49808198) (nat_lit 10802019512) (nat_lit 0) A10K2.t3093 from rfl, allE_node, rows3092, irow3088, rows3093]
  all_goals rfl

theorem atot3088 : totK PA10K2 A10K2.u3088 = [0, 777909442081, 2844522486456, 3145960311020, 1514373822395, 1105843507109, 506914864948, 49137922124, 0, 0] := by
  rw [show A10K2.u3088 = KTree.node A10K2.t3092 (nat_lit 49808198) (nat_lit 10802019512) (nat_lit 0) A10K2.t3093 from rfl, totK_node, tot3092, tot3093]
  decide +kernel

theorem arows3089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3089 = true := by
  rw [show A10K2.u3089 = KTree.node A10K2.t3094 (nat_lit 49814532) (nat_lit 10385418866) (nat_lit 0) A10K2.t3095 from rfl, allE_node, rows3094, irow3089, rows3095]
  all_goals rfl

theorem atot3089 : totK PA10K2 A10K2.u3089 = [0, 265289717592, 1889683342463, 3981707821261, 2866200970634, 603797250999, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u3089 = KTree.node A10K2.t3094 (nat_lit 49814532) (nat_lit 10385418866) (nat_lit 0) A10K2.t3095 from rfl, totK_node, tot3094, tot3095]
  decide +kernel

theorem arows3092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3092 = true := by
  rw [show A10K2.u3092 = KTree.node A10K2.t3096 (nat_lit 49833636) (nat_lit 8321939921) (nat_lit 0) A10K2.t3097 from rfl, allE_node, rows3096, irow3092, rows3097]
  all_goals rfl

theorem atot3092 : totK PA10K2 A10K2.u3092 = [0, 827520024373, 3333195221907, 4186818342789, 1587997054559, 126154468033, 0, 0, 0, 0] := by
  rw [show A10K2.u3092 = KTree.node A10K2.t3096 (nat_lit 49833636) (nat_lit 8321939921) (nat_lit 0) A10K2.t3097 from rfl, totK_node, tot3096, tot3097]
  decide +kernel

theorem arows3093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3093 = true := by
  rw [show A10K2.u3093 = KTree.node A10K2.t3098 (nat_lit 49839496) (nat_lit 13778730677) (nat_lit 0) A10K2.t3099 from rfl, allE_node, rows3098, irow3093, rows3099]
  all_goals rfl

theorem atot3093 : totK PA10K2 A10K2.u3093 = [0, 0, 955757143141, 3623847701170, 4084937724672, 1245441737103, 83255389061, 0, 0, 0] := by
  rw [show A10K2.u3093 = KTree.node A10K2.t3098 (nat_lit 49839496) (nat_lit 13778730677) (nat_lit 0) A10K2.t3099 from rfl, totK_node, tot3098, tot3099]
  decide +kernel

theorem arows3095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3095 = true := by
  rw [show A10K2.u3095 = KTree.node A10K2.t3100 (nat_lit 49844217) (nat_lit 5927093538) (nat_lit 0) A10K2.t3101 from rfl, allE_node, rows3100, irow3095, rows3101]
  all_goals rfl

theorem atot3095 : totK PA10K2 A10K2.u3095 = [0, 0, 473027519034, 2416681827018, 4028343299042, 2343336405634, 408764446211, 12477124820, 0, 0] := by
  rw [show A10K2.u3095 = KTree.node A10K2.t3100 (nat_lit 49844217) (nat_lit 5927093538) (nat_lit 0) A10K2.t3101 from rfl, totK_node, tot3100, tot3101]
  decide +kernel

theorem arows3096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3096 = true := by
  rw [show A10K2.u3096 = KTree.node A10K2.t3102 (nat_lit 49864716) (nat_lit 10934062318) (nat_lit 0) A10K2.t3103 from rfl, allE_node, rows3102, irow3096, rows3103]
  all_goals rfl

theorem atot3096 : totK PA10K2 A10K2.u3096 = [0, 0, 875237470523, 3439149123853, 4087238617682, 1397427097349, 106211606522, 0, 0, 0] := by
  rw [show A10K2.u3096 = KTree.node A10K2.t3102 (nat_lit 49864716) (nat_lit 10934062318) (nat_lit 0) A10K2.t3103 from rfl, totK_node, tot3102, tot3103]
  decide +kernel

theorem arows3101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3101 = true := by
  rw [show A10K2.u3101 = KTree.node A10K2.t3104 (nat_lit 49882785) (nat_lit 3995678162) (nat_lit 0) A10K2.t3105 from rfl, allE_node, rows3104, irow3101, rows3105]
  all_goals rfl

theorem atot3101 : totK PA10K2 A10K2.u3101 = [0, 823020947679, 2935398081143, 3528311377972, 1984688345344, 589628598390, 50548650670, 0, 0, 0] := by
  rw [show A10K2.u3101 = KTree.node A10K2.t3104 (nat_lit 49882785) (nat_lit 3995678162) (nat_lit 0) A10K2.t3105 from rfl, totK_node, tot3104, tot3105]
  decide +kernel

theorem arows3102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3102 = true := by
  rw [show A10K2.u3102 = KTree.node A10K2.t3106 (nat_lit 49887410) (nat_lit 15045764662) (nat_lit 0) A10K2.t3107 from rfl, allE_node, rows3106, irow3102, rows3107]
  all_goals rfl

theorem atot3102 : totK PA10K2 A10K2.u3102 = [0, 280788281866, 1896713359366, 4021907425979, 2952987788350, 619808809729, 31543789865, 0, 0, 0] := by
  rw [show A10K2.u3102 = KTree.node A10K2.t3106 (nat_lit 49887410) (nat_lit 15045764662) (nat_lit 0) A10K2.t3107 from rfl, totK_node, tot3106, tot3107]
  decide +kernel

theorem arows3104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3104 = true := by
  rw [show A10K2.u3104 = KTree.node A10K2.t3108 (nat_lit 49895649) (nat_lit 4662147130) (nat_lit 0) A10K2.t3109 from rfl, allE_node, rows3108, irow3104, rows3109]
  all_goals rfl

theorem atot3104 : totK PA10K2 A10K2.u3104 = [0, 707873938277, 3156667620766, 4236690152785, 1638856694623, 128838697286, 0, 0, 0, 0] := by
  rw [show A10K2.u3104 = KTree.node A10K2.t3108 (nat_lit 49895649) (nat_lit 4662147130) (nat_lit 0) A10K2.t3109 from rfl, totK_node, tot3108, tot3109]
  decide +kernel

theorem arows3105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3105 = true := by
  rw [show A10K2.u3105 = KTree.node A10K2.t3110 (nat_lit 49902017) (nat_lit 10157531786) (nat_lit 0) A10K2.t3111 from rfl, allE_node, rows3110, irow3105, rows3111]
  all_goals rfl

theorem atot3105 : totK PA10K2 A10K2.u3105 = [0, 322051627922, 2118904562505, 4257714157222, 2937010162712, 539759884941, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u3105 = KTree.node A10K2.t3110 (nat_lit 49902017) (nat_lit 10157531786) (nat_lit 0) A10K2.t3111 from rfl, totK_node, tot3110, tot3111]
  decide +kernel

theorem arows3108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3108 = true := by
  rw [show A10K2.u3108 = KTree.node A10K2.t3112 (nat_lit 49915748) (nat_lit 13209665022) (nat_lit 0) A10K2.t3113 from rfl, allE_node, rows3112, irow3108, rows3113]
  all_goals rfl

theorem atot3108 : totK PA10K2 A10K2.u3108 = [0, 0, 867602113832, 3481511739360, 4071379877464, 1326827117769, 88107887360, 0, 0, 0] := by
  rw [show A10K2.u3108 = KTree.node A10K2.t3112 (nat_lit 49915748) (nat_lit 13209665022) (nat_lit 0) A10K2.t3113 from rfl, totK_node, tot3112, tot3113]
  decide +kernel

theorem arows3109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3109 = true := by
  rw [show A10K2.u3109 = KTree.node A10K2.t3114 (nat_lit 49920702) (nat_lit 10615099457) (nat_lit 0) A10K2.t3115 from rfl, allE_node, rows3114, irow3109, rows3115]
  all_goals rfl

theorem atot3109 : totK PA10K2 A10K2.u3109 = [0, 0, 382064625605, 2122091936880, 3995430381026, 2619835167789, 459404848744, 12696458652, 0, 0] := by
  rw [show A10K2.u3109 = KTree.node A10K2.t3114 (nat_lit 49920702) (nat_lit 10615099457) (nat_lit 0) A10K2.t3115 from rfl, totK_node, tot3114, tot3115]
  decide +kernel

theorem arows3111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3111 = true := by
  rw [show A10K2.u3111 = KTree.node A10K2.t3116 (nat_lit 49930747) (nat_lit 6050126607) (nat_lit 0) A10K2.t3117 from rfl, allE_node, rows3116, irow3111, rows3117]
  all_goals rfl

theorem atot3111 : totK PA10K2 A10K2.u3111 = [0, 0, 857800415261, 3415802073027, 4125044348723, 1384255626359, 76797726327, 0, 0, 0] := by
  rw [show A10K2.u3111 = KTree.node A10K2.t3116 (nat_lit 49930747) (nat_lit 6050126607) (nat_lit 0) A10K2.t3117 from rfl, totK_node, tot3116, tot3117]
  decide +kernel

theorem arows3112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3112 = true := by
  rw [show A10K2.u3112 = KTree.node A10K2.t3118 (nat_lit 50004845) (nat_lit 4610732687) (nat_lit 0) A10K2.t3119 from rfl, allE_node, rows3118, irow3112, rows3119]
  all_goals rfl

theorem atot3112 : totK PA10K2 A10K2.u3112 = [0, 725949308331, 2785248020319, 3605787458699, 2097551431114, 609633002838, 50555834002, 0, 0, 0] := by
  rw [show A10K2.u3112 = KTree.node A10K2.t3118 (nat_lit 50004845) (nat_lit 4610732687) (nat_lit 0) A10K2.t3119 from rfl, totK_node, tot3118, tot3119]
  decide +kernel

theorem arows3116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3116 = true := by
  rw [show A10K2.u3116 = KTree.node A10K2.t3120 (nat_lit 50011521) (nat_lit 10144077097) (nat_lit 0) A10K2.t3121 from rfl, allE_node, rows3120, irow3116, rows3121]
  all_goals rfl

theorem atot3116 : totK PA10K2 A10K2.u3116 = [0, 460689358819, 2322875644921, 3855122275828, 2382168030730, 468485665114, 17500500512, 0, 0, 0] := by
  rw [show A10K2.u3116 = KTree.node A10K2.t3120 (nat_lit 50011521) (nat_lit 10144077097) (nat_lit 0) A10K2.t3121 from rfl, totK_node, tot3120, tot3121]
  decide +kernel

theorem arows3117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3117 = true := by
  rw [show A10K2.u3117 = KTree.node A10K2.t3122 (nat_lit 50017742) (nat_lit 13785541233) (nat_lit 0) A10K2.t3123 from rfl, allE_node, rows3122, irow3117, rows3123]
  all_goals rfl

theorem atot3117 : totK PA10K2 A10K2.u3117 = [0, 418274782927, 2115869041308, 4029976603795, 2828513999172, 543720233470, 17754888877, 0, 0, 0] := by
  rw [show A10K2.u3117 = KTree.node A10K2.t3122 (nat_lit 50017742) (nat_lit 13785541233) (nat_lit 0) A10K2.t3123 from rfl, totK_node, tot3122, tot3123]
  decide +kernel

theorem arows3119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3119 = true := by
  rw [show A10K2.u3119 = KTree.node A10K2.t3124 (nat_lit 50030444) (nat_lit 7388017957) (nat_lit 0) A10K2.t3125 from rfl, allE_node, rows3124, irow3119, rows3125]
  all_goals rfl

theorem atot3119 : totK PA10K2 A10K2.u3119 = [0, 784091755875, 3316313624387, 4144727922746, 1508877311977, 114268311079, 0, 0, 0, 0] := by
  rw [show A10K2.u3119 = KTree.node A10K2.t3124 (nat_lit 50030444) (nat_lit 7388017957) (nat_lit 0) A10K2.t3125 from rfl, totK_node, tot3124, tot3125]
  decide +kernel

theorem arows3120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3120 = true := by
  rw [show A10K2.u3120 = KTree.node A10K2.t3126 (nat_lit 50035925) (nat_lit 5021260213) (nat_lit 0) A10K2.t3127 from rfl, allE_node, rows3126, irow3120, rows3127]
  all_goals rfl

theorem atot3120 : totK PA10K2 A10K2.u3120 = [0, 0, 962301684914, 3666718083973, 4047670747871, 1217443835244, 80537954553, 0, 0, 0] := by
  rw [show A10K2.u3120 = KTree.node A10K2.t3126 (nat_lit 50035925) (nat_lit 5021260213) (nat_lit 0) A10K2.t3127 from rfl, totK_node, tot3126, tot3127]
  decide +kernel

theorem arows3123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3123 = true := by
  rw [show A10K2.u3123 = KTree.node A10K2.t3128 (nat_lit 50040794) (nat_lit 12769350418) (nat_lit 0) A10K2.t3129 from rfl, allE_node, rows3128, irow3123, rows3129]
  all_goals rfl

theorem atot3123 : totK PA10K2 A10K2.u3123 = [0, 0, 435690288822, 2456985306671, 4215659274277, 2218910373879, 269798423550, 6904928264, 0, 0] := by
  rw [show A10K2.u3123 = KTree.node A10K2.t3128 (nat_lit 50040794) (nat_lit 12769350418) (nat_lit 0) A10K2.t3129 from rfl, totK_node, tot3128, tot3129]
  decide +kernel

theorem arows3124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3124 = true := by
  rw [show A10K2.u3124 = KTree.node A10K2.t3130 (nat_lit 50048070) (nat_lit 15144811040) (nat_lit 0) A10K2.t3131 from rfl, allE_node, rows3130, irow3124, rows3131]
  all_goals rfl

theorem atot3124 : totK PA10K2 A10K2.u3124 = [0, 0, 768720349653, 3115178817332, 4014676668041, 1777124603526, 165257711417, 0, 0, 0] := by
  rw [show A10K2.u3124 = KTree.node A10K2.t3130 (nat_lit 50048070) (nat_lit 15144811040) (nat_lit 0) A10K2.t3131 from rfl, totK_node, tot3130, tot3131]
  decide +kernel

theorem arows3126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3126 = true := by
  rw [show A10K2.u3126 = KTree.node A10K2.t3132 (nat_lit 50061923) (nat_lit 837591433) (nat_lit 0) A10K2.t3133 from rfl, allE_node, rows3132, irow3126, rows3133]
  all_goals rfl

theorem atot3126 : totK PA10K2 A10K2.u3126 = [0, 0, 892036458401, 3302115009242, 3865864197839, 1612923538188, 206644296846, 7047025452, 0, 0] := by
  rw [show A10K2.u3126 = KTree.node A10K2.t3132 (nat_lit 50061923) (nat_lit 837591433) (nat_lit 0) A10K2.t3133 from rfl, totK_node, tot3132, tot3133]
  decide +kernel

theorem arows3127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3127 = true := by
  rw [show A10K2.u3127 = KTree.node A10K2.t3134 (nat_lit 50066654) (nat_lit 11389925001) (nat_lit 0) A10K2.t3135 from rfl, allE_node, rows3134, irow3127, rows3135]
  all_goals rfl

theorem atot3127 : totK PA10K2 A10K2.u3127 = [0, 0, 0, 1313738216264, 4159649959531, 3614559667968, 760908709182, 23799715721, 0, 0] := by
  rw [show A10K2.u3127 = KTree.node A10K2.t3134 (nat_lit 50066654) (nat_lit 11389925001) (nat_lit 0) A10K2.t3135 from rfl, totK_node, tot3134, tot3135]
  decide +kernel

theorem arows3133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3133 = true := by
  rw [show A10K2.u3133 = KTree.node A10K2.t3136 (nat_lit 50072352) (nat_lit 12740398072) (nat_lit 0) A10K2.t3137 from rfl, allE_node, rows3136, irow3133, rows3137]
  all_goals rfl

theorem atot3133 : totK PA10K2 A10K2.u3133 = [0, 0, 777410068509, 3146029076783, 3897777696544, 1626547672995, 323023873531, 37310410385, 0, 0] := by
  rw [show A10K2.u3133 = KTree.node A10K2.t3136 (nat_lit 50072352) (nat_lit 12740398072) (nat_lit 0) A10K2.t3137 from rfl, totK_node, tot3136, tot3137]
  decide +kernel

theorem arows3134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3134 = true := by
  rw [show A10K2.u3134 = KTree.node A10K2.t3138 (nat_lit 50085992) (nat_lit 12163624977) (nat_lit 0) A10K2.t3139 from rfl, allE_node, rows3138, irow3134, rows3139]
  all_goals rfl

theorem atot3134 : totK PA10K2 A10K2.u3134 = [0, 0, 551840218655, 2394221865086, 3829395152335, 2459576975155, 445650750709, 12477124820, 0, 0] := by
  rw [show A10K2.u3134 = KTree.node A10K2.t3138 (nat_lit 50085992) (nat_lit 12163624977) (nat_lit 0) A10K2.t3139 from rfl, totK_node, tot3138, tot3139]
  decide +kernel

theorem arows3136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3136 = true := by
  rw [show A10K2.u3136 = KTree.node A10K2.t3140 (nat_lit 50097605) (nat_lit 4015748516) (nat_lit 0) A10K2.t3141 from rfl, allE_node, rows3140, irow3136, rows3141]
  all_goals rfl

theorem atot3136 : totK PA10K2 A10K2.u3136 = [0, 0, 537680587155, 2719542960840, 4298758449789, 2227453019468, 302600839887, 6853348008, 0, 0] := by
  rw [show A10K2.u3136 = KTree.node A10K2.t3140 (nat_lit 50097605) (nat_lit 4015748516) (nat_lit 0) A10K2.t3141 from rfl, totK_node, tot3140, tot3141]
  decide +kernel

theorem arows3137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3137 = true := by
  rw [show A10K2.u3137 = KTree.node A10K2.t3142 (nat_lit 50102271) (nat_lit 13968960306) (nat_lit 0) A10K2.t3143 from rfl, allE_node, rows3142, irow3137, rows3143]
  all_goals rfl

theorem atot3137 : totK PA10K2 A10K2.u3137 = [0, 0, 0, 1021120635998, 3714763185443, 3995900589262, 1131204140387, 67995113947, 0, 0] := by
  rw [show A10K2.u3137 = KTree.node A10K2.t3142 (nat_lit 50102271) (nat_lit 13968960306) (nat_lit 0) A10K2.t3143 from rfl, totK_node, tot3142, tot3143]
  decide +kernel

theorem arows3140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3140 = true := by
  rw [show A10K2.u3140 = KTree.node A10K2.t3144 (nat_lit 50107320) (nat_lit 13422721784) (nat_lit 0) A10K2.t3145 from rfl, allE_node, rows3144, irow3140, rows3145]
  all_goals rfl

theorem atot3140 : totK PA10K2 A10K2.u3140 = [0, 0, 0, 601007676173, 2900806838873, 4161904934265, 1845655687214, 230980798152, 6725424603, 0] := by
  rw [show A10K2.u3140 = KTree.node A10K2.t3144 (nat_lit 50107320) (nat_lit 13422721784) (nat_lit 0) A10K2.t3145 from rfl, totK_node, tot3144, tot3145]
  decide +kernel

theorem arows3141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3141 = true := by
  rw [show A10K2.u3141 = KTree.node A10K2.t3146 (nat_lit 50130305) (nat_lit 9982413561) (nat_lit 0) A10K2.t3147 from rfl, allE_node, rows3146, irow3141, rows3147]
  all_goals rfl

theorem atot3141 : totK PA10K2 A10K2.u3141 = [0, 0, 310599358184, 1700530151401, 3582601580465, 3349267442162, 1003433771500, 68492179993, 0, 0] := by
  rw [show A10K2.u3141 = KTree.node A10K2.t3146 (nat_lit 50130305) (nat_lit 9982413561) (nat_lit 0) A10K2.t3147 from rfl, totK_node, tot3146, tot3147]
  decide +kernel

theorem arows3143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3143 = true := by
  rw [show A10K2.u3143 = KTree.node A10K2.t3148 (nat_lit 50147209) (nat_lit 7150663023) (nat_lit 0) A10K2.t3149 from rfl, allE_node, rows3148, irow3143, rows3149]
  all_goals rfl

theorem atot3143 : totK PA10K2 A10K2.u3143 = [0, 0, 510380714468, 2475639811902, 4000254890602, 2379699218844, 411391231303, 12696458652, 0, 0] := by
  rw [show A10K2.u3143 = KTree.node A10K2.t3148 (nat_lit 50147209) (nat_lit 7150663023) (nat_lit 0) A10K2.t3149 from rfl, totK_node, tot3148, tot3149]
  decide +kernel

theorem arows3144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3144 = true := by
  rw [show A10K2.u3144 = KTree.node A10K2.t3150 (nat_lit 50153651) (nat_lit 10071710841) (nat_lit 0) A10K2.t3151 from rfl, allE_node, rows3150, irow3144, rows3151]
  all_goals rfl

theorem atot3144 : totK PA10K2 A10K2.u3144 = [0, 0, 695451510932, 3068491835025, 4142077255676, 1831879209345, 165133810429, 0, 0, 0] := by
  rw [show A10K2.u3144 = KTree.node A10K2.t3150 (nat_lit 50153651) (nat_lit 10071710841) (nat_lit 0) A10K2.t3151 from rfl, totK_node, tot3150, tot3151]
  decide +kernel

theorem arows3148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3148 = true := by
  rw [show A10K2.u3148 = KTree.node A10K2.t3152 (nat_lit 50163250) (nat_lit 11585204989) (nat_lit 0) A10K2.t3153 from rfl, allE_node, rows3152, irow3148, rows3153]
  all_goals rfl

theorem atot3148 : totK PA10K2 A10K2.u3148 = [0, 0, 612143352615, 2797365120795, 4178480781943, 2212026508217, 293526728295, 6279851884, 0, 0] := by
  rw [show A10K2.u3148 = KTree.node A10K2.t3152 (nat_lit 50163250) (nat_lit 11585204989) (nat_lit 0) A10K2.t3153 from rfl, totK_node, tot3152, tot3153]
  decide +kernel

theorem arows3149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3149 = true := by
  rw [show A10K2.u3149 = KTree.node A10K2.t3154 (nat_lit 50177252) (nat_lit 12336417934) (nat_lit 0) A10K2.t3155 from rfl, allE_node, rows3154, irow3149, rows3155]
  all_goals rfl

theorem atot3149 : totK PA10K2 A10K2.u3149 = [0, 0, 0, 1017368237404, 3712795559260, 3972081341641, 1149992932933, 68803341712, 0, 0] := by
  rw [show A10K2.u3149 = KTree.node A10K2.t3154 (nat_lit 50177252) (nat_lit 12336417934) (nat_lit 0) A10K2.t3155 from rfl, totK_node, tot3154, tot3155]
  decide +kernel

theorem arows3151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3151 = true := by
  rw [show A10K2.u3151 = KTree.node A10K2.t3156 (nat_lit 50182306) (nat_lit 14142712800) (nat_lit 0) A10K2.t3157 from rfl, allE_node, rows3156, irow3151, rows3157]
  all_goals rfl

theorem atot3151 : totK PA10K2 A10K2.u3151 = [0, 0, 0, 807395128762, 3000792464785, 3908293479006, 1849310903481, 241951880202, 6860445330, 0] := by
  rw [show A10K2.u3151 = KTree.node A10K2.t3156 (nat_lit 50182306) (nat_lit 14142712800) (nat_lit 0) A10K2.t3157 from rfl, totK_node, tot3156, tot3157]
  decide +kernel

theorem arows3152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3152 = true := by
  rw [show A10K2.u3152 = KTree.node A10K2.t3158 (nat_lit 50195840) (nat_lit 14565408706) (nat_lit 0) A10K2.t3159 from rfl, allE_node, rows3158, irow3152, rows3159]
  all_goals rfl

theorem atot3152 : totK PA10K2 A10K2.u3152 = [0, 0, 289498769530, 1552170229373, 3483492441661, 3408535772577, 1043917672499, 68647199231, 0, 0] := by
  rw [show A10K2.u3152 = KTree.node A10K2.t3158 (nat_lit 50195840) (nat_lit 14565408706) (nat_lit 0) A10K2.t3159 from rfl, totK_node, tot3158, tot3159]
  decide +kernel

theorem arows3155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3155 = true := by
  rw [show A10K2.u3155 = KTree.node A10K2.t3160 (nat_lit 50270244) (nat_lit 11838618323) (nat_lit 0) A10K2.t3161 from rfl, allE_node, rows3160, irow3155, rows3161]
  all_goals rfl

theorem atot3155 : totK PA10K2 A10K2.u3155 = [0, 0, 435949150056, 2402597192012, 4085791706357, 2390061635610, 352651476847, 11694325420, 0, 0] := by
  rw [show A10K2.u3155 = KTree.node A10K2.t3160 (nat_lit 50270244) (nat_lit 11838618323) (nat_lit 0) A10K2.t3161 from rfl, totK_node, tot3160, tot3161]
  decide +kernel

theorem arows3156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3156 = true := by
  rw [show A10K2.u3156 = KTree.node A10K2.t3162 (nat_lit 50277440) (nat_lit 14966789945) (nat_lit 0) A10K2.t3163 from rfl, allE_node, rows3162, irow3156, rows3163]
  all_goals rfl

theorem atot3156 : totK PA10K2 A10K2.u3156 = [0, 0, 764272469103, 3095372048261, 4030200323785, 1795440791543, 173347058177, 0, 0, 0] := by
  rw [show A10K2.u3156 = KTree.node A10K2.t3162 (nat_lit 50277440) (nat_lit 14966789945) (nat_lit 0) A10K2.t3163 from rfl, totK_node, tot3162, tot3163]
  decide +kernel

theorem arows3158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3158 = true := by
  rw [show A10K2.u3158 = KTree.node A10K2.t3164 (nat_lit 50291123) (nat_lit 8236344417) (nat_lit 0) A10K2.t3165 from rfl, allE_node, rows3164, irow3158, rows3165]
  all_goals rfl

theorem atot3158 : totK PA10K2 A10K2.u3158 = [0, 0, 662078289728, 2785345862432, 3893683955620, 2088048917060, 319197949257, 11918539728, 0, 0] := by
  rw [show A10K2.u3158 = KTree.node A10K2.t3164 (nat_lit 50291123) (nat_lit 8236344417) (nat_lit 0) A10K2.t3165 from rfl, totK_node, tot3164, tot3165]
  decide +kernel

theorem arows3159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3159 = true := by
  rw [show A10K2.u3159 = KTree.node A10K2.t3166 (nat_lit 50295374) (nat_lit 10059891680) (nat_lit 0) A10K2.t3167 from rfl, allE_node, rows3166, irow3159, rows3167]
  all_goals rfl

theorem atot3159 : totK PA10K2 A10K2.u3159 = [0, 0, 211927423510, 1826375691751, 4227846109346, 3177668199952, 553970656803, 13653259670, 0, 0] := by
  rw [show A10K2.u3159 = KTree.node A10K2.t3166 (nat_lit 50295374) (nat_lit 10059891680) (nat_lit 0) A10K2.t3167 from rfl, totK_node, tot3166, tot3167]
  decide +kernel

theorem arows3164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3164 = true := by
  rw [show A10K2.u3164 = KTree.node A10K2.t3168 (nat_lit 50301036) (nat_lit 8745832774) (nat_lit 0) A10K2.t3169 from rfl, allE_node, rows3168, irow3164, rows3169]
  all_goals rfl

theorem atot3164 : totK PA10K2 A10K2.u3164 = [0, 0, 0, 720197533683, 3108425234289, 4155908497519, 1548081718458, 123036785356, 0, 0] := by
  rw [show A10K2.u3164 = KTree.node A10K2.t3168 (nat_lit 50301036) (nat_lit 8745832774) (nat_lit 0) A10K2.t3169 from rfl, totK_node, tot3168, tot3169]
  decide +kernel

theorem arows3165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3165 = true := by
  rw [show A10K2.u3165 = KTree.node A10K2.t3170 (nat_lit 50308571) (nat_lit 6870203376) (nat_lit 0) A10K2.t3171 from rfl, allE_node, rows3170, irow3165, rows3171]
  all_goals rfl

theorem atot3165 : totK PA10K2 A10K2.u3165 = [0, 0, 0, 758403210404, 3014114360961, 4004088840038, 1782712909440, 233361412699, 6318667960, 0] := by
  rw [show A10K2.u3165 = KTree.node A10K2.t3170 (nat_lit 50308571) (nat_lit 6870203376) (nat_lit 0) A10K2.t3171 from rfl, totK_node, tot3170, tot3171]
  decide +kernel

theorem arows3167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3167 = true := by
  rw [show A10K2.u3167 = KTree.node A10K2.t3172 (nat_lit 50314693) (nat_lit 1507353488) (nat_lit 0) A10K2.t3173 from rfl, allE_node, rows3172, irow3167, rows3173]
  all_goals rfl

theorem atot3167 : totK PA10K2 A10K2.u3167 = [0, 0, 0, 548781731263, 2696528487826, 4059140984297, 2100959960840, 284933150203, 6439430839, 0] := by
  rw [show A10K2.u3167 = KTree.node A10K2.t3172 (nat_lit 50314693) (nat_lit 1507353488) (nat_lit 0) A10K2.t3173 from rfl, totK_node, tot3172, tot3173]
  decide +kernel

theorem arows3168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3168 = true := by
  rw [show A10K2.u3168 = KTree.node A10K2.t3174 (nat_lit 50327821) (nat_lit 2889412139) (nat_lit 0) A10K2.t3175 from rfl, allE_node, rows3174, irow3168, rows3175]
  all_goals rfl

theorem atot3168 : totK PA10K2 A10K2.u3168 = [0, 0, 0, 328627686157, 2114700578152, 4156493931710, 2691840470652, 449475605636, 12132367858, 0] := by
  rw [show A10K2.u3168 = KTree.node A10K2.t3174 (nat_lit 50327821) (nat_lit 2889412139) (nat_lit 0) A10K2.t3175 from rfl, totK_node, tot3174, tot3175]
  decide +kernel

theorem arows3171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3171 = true := by
  rw [show A10K2.u3171 = KTree.node A10K2.t3176 (nat_lit 55125760) (nat_lit 7179241454) (nat_lit 0) A10K2.t3177 from rfl, allE_node, rows3176, irow3171, rows3177]
  all_goals rfl

theorem atot3171 : totK PA10K2 A10K2.u3171 = [0, 876250713213, 2931714180431, 2747554674863, 794523112780, 753226069485, 1160230896244, 511713723036, 48886019071, 0] := by
  rw [show A10K2.u3171 = KTree.node A10K2.t3176 (nat_lit 55125760) (nat_lit 7179241454) (nat_lit 0) A10K2.t3177 from rfl, totK_node, tot3176, tot3177]
  decide +kernel

theorem arows3172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3172 = true := by
  rw [show A10K2.u3172 = KTree.node A10K2.t3178 (nat_lit 55130260) (nat_lit 12714679208) (nat_lit 0) A10K2.t3179 from rfl, allE_node, rows3178, irow3172, rows3179]
  all_goals rfl

theorem atot3172 : totK PA10K2 A10K2.u3172 = [0, 146952719065, 1598517481238, 4016651212034, 3168246098214, 648173302228, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3172 = KTree.node A10K2.t3178 (nat_lit 55130260) (nat_lit 12714679208) (nat_lit 0) A10K2.t3179 from rfl, totK_node, tot3178, tot3179]
  decide +kernel

theorem arows3174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3174 = true := by
  rw [show A10K2.u3174 = KTree.node A10K2.t3180 (nat_lit 55134560) (nat_lit 12213653678) (nat_lit 0) A10K2.t3181 from rfl, allE_node, rows3180, irow3174, rows3181]
  all_goals rfl

theorem atot3174 : totK PA10K2 A10K2.u3174 = [0, 576047241256, 2874050152099, 4151542545931, 1681318226897, 126604034924, 0, 0, 0, 0] := by
  rw [show A10K2.u3174 = KTree.node A10K2.t3180 (nat_lit 55134560) (nat_lit 12213653678) (nat_lit 0) A10K2.t3181 from rfl, totK_node, tot3180, tot3181]
  decide +kernel

theorem arows3175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3175 = true := by
  rw [show A10K2.u3175 = KTree.node A10K2.t3182 (nat_lit 55142107) (nat_lit 9723505766) (nat_lit 0) A10K2.t3183 from rfl, allE_node, rows3182, irow3175, rows3183]
  all_goals rfl

theorem atot3175 : totK PA10K2 A10K2.u3175 = [0, 785223503628, 3065051215461, 4052592503933, 1840692896648, 255292221047, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3175 = KTree.node A10K2.t3182 (nat_lit 55142107) (nat_lit 9723505766) (nat_lit 0) A10K2.t3183 from rfl, totK_node, tot3182, tot3183]
  decide +kernel

theorem arows3179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3179 = true := by
  rw [show A10K2.u3179 = KTree.node A10K2.t3184 (nat_lit 55147972) (nat_lit 4926030519) (nat_lit 0) A10K2.t3185 from rfl, allE_node, rows3184, irow3179, rows3185]
  all_goals rfl

theorem atot3179 : totK PA10K2 A10K2.u3179 = [0, 0, 930078964227, 3620826570857, 4070938430281, 1268672437559, 80496002899, 0, 0, 0] := by
  rw [show A10K2.u3179 = KTree.node A10K2.t3184 (nat_lit 55147972) (nat_lit 4926030519) (nat_lit 0) A10K2.t3185 from rfl, totK_node, tot3184, tot3185]
  decide +kernel

theorem arows3180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3180 = true := by
  rw [show A10K2.u3180 = KTree.node A10K2.t3186 (nat_lit 55160549) (nat_lit 6044051378) (nat_lit 0) A10K2.t3187 from rfl, allE_node, rows3186, irow3180, rows3187]
  all_goals rfl

theorem atot3180 : totK PA10K2 A10K2.u3180 = [0, 0, 552523461095, 2636410732668, 3935646541271, 2077595723602, 404331712694, 25565504801, 0, 0] := by
  rw [show A10K2.u3180 = KTree.node A10K2.t3186 (nat_lit 55160549) (nat_lit 6044051378) (nat_lit 0) A10K2.t3187 from rfl, totK_node, tot3186, tot3187]
  decide +kernel

theorem arows3182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3182 = true := by
  rw [show A10K2.u3182 = KTree.node A10K2.t3188 (nat_lit 55166245) (nat_lit 7408626806) (nat_lit 0) A10K2.t3189 from rfl, allE_node, rows3188, irow3182, rows3189]
  all_goals rfl

theorem atot3182 : totK PA10K2 A10K2.u3182 = [0, 0, 722374899439, 2963607531902, 3815432462136, 1639338755180, 211873521882, 5517381808, 0, 0] := by
  rw [show A10K2.u3182 = KTree.node A10K2.t3188 (nat_lit 55166245) (nat_lit 7408626806) (nat_lit 0) A10K2.t3189 from rfl, totK_node, tot3188, tot3189]
  decide +kernel

theorem arows3183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3183 = true := by
  rw [show A10K2.u3183 = KTree.node A10K2.t3190 (nat_lit 55173175) (nat_lit 14628563125) (nat_lit 0) A10K2.t3191 from rfl, allE_node, rows3190, irow3183, rows3191]
  all_goals rfl

theorem atot3183 : totK PA10K2 A10K2.u3183 = [0, 0, 597384360804, 2679736658399, 4063611968228, 1968713580123, 238838251310, 6121173289, 0, 0] := by
  rw [show A10K2.u3183 = KTree.node A10K2.t3190 (nat_lit 55173175) (nat_lit 14628563125) (nat_lit 0) A10K2.t3191 from rfl, totK_node, tot3190, tot3191]
  decide +kernel

theorem arows3186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3186 = true := by
  rw [show A10K2.u3186 = KTree.node A10K2.t3192 (nat_lit 55183509) (nat_lit 6830174778) (nat_lit 0) A10K2.t3193 from rfl, allE_node, rows3192, irow3186, rows3193]
  all_goals rfl

theorem atot3186 : totK PA10K2 A10K2.u3186 = [0, 424355675811, 2135785502930, 3591623318826, 2410486207261, 707313569848, 53670550828, 0, 0, 0] := by
  rw [show A10K2.u3186 = KTree.node A10K2.t3192 (nat_lit 55183509) (nat_lit 6830174778) (nat_lit 0) A10K2.t3193 from rfl, totK_node, tot3192, tot3193]
  decide +kernel

theorem arows3187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3187 = true := by
  rw [show A10K2.u3187 = KTree.node A10K2.t3194 (nat_lit 55191778) (nat_lit 14075434324) (nat_lit 0) A10K2.t3195 from rfl, allE_node, rows3194, irow3187, rows3195]
  all_goals rfl

theorem atot3187 : totK PA10K2 A10K2.u3187 = [0, 803828201493, 3155785635418, 3920980569632, 1718272626023, 226307102841, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u3187 = KTree.node A10K2.t3194 (nat_lit 55191778) (nat_lit 14075434324) (nat_lit 0) A10K2.t3195 from rfl, totK_node, tot3194, tot3195]
  decide +kernel

theorem arows3189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3189 = true := by
  rw [show A10K2.u3189 = KTree.node A10K2.t3196 (nat_lit 55196863) (nat_lit 14008065033) (nat_lit 0) A10K2.t3197 from rfl, allE_node, rows3196, irow3189, rows3197]
  all_goals rfl

theorem atot3189 : totK PA10K2 A10K2.u3189 = [0, 476246592928, 2115665756815, 3591089205389, 2627206091322, 588319400774, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3189 = KTree.node A10K2.t3196 (nat_lit 55196863) (nat_lit 14008065033) (nat_lit 0) A10K2.t3197 from rfl, totK_node, tot3196, tot3197]
  decide +kernel

theorem arows3190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3190 = true := by
  rw [show A10K2.u3190 = KTree.node A10K2.t3198 (nat_lit 55202156) (nat_lit 12674247042) (nat_lit 0) A10K2.t3199 from rfl, allE_node, rows3198, irow3190, rows3199]
  all_goals rfl

theorem atot3190 : totK PA10K2 A10K2.u3190 = [0, 298263154340, 2165047112164, 4168338291439, 2296840232062, 307543065072, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3190 = KTree.node A10K2.t3198 (nat_lit 55202156) (nat_lit 12674247042) (nat_lit 0) A10K2.t3199 from rfl, totK_node, tot3198, tot3199]
  decide +kernel

theorem arows3197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3197 = true := by
  rw [show A10K2.u3197 = KTree.node A10K2.t3200 (nat_lit 55223743) (nat_lit 14018446412) (nat_lit 0) A10K2.t3201 from rfl, allE_node, rows3200, irow3197, rows3201]
  all_goals rfl

theorem atot3197 : totK PA10K2 A10K2.u3197 = [0, 0, 1036179188663, 3728741743291, 3748462516144, 938920815126, 44211540368, 0, 0, 0] := by
  rw [show A10K2.u3197 = KTree.node A10K2.t3200 (nat_lit 55223743) (nat_lit 14018446412) (nat_lit 0) A10K2.t3201 from rfl, totK_node, tot3200, tot3201]
  decide +kernel

theorem arows3198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3198 = true := by
  rw [show A10K2.u3198 = KTree.node A10K2.t3202 (nat_lit 55231964) (nat_lit 5601451034) (nat_lit 0) A10K2.t3203 from rfl, allE_node, rows3202, irow3198, rows3203]
  all_goals rfl

theorem atot3198 : totK PA10K2 A10K2.u3198 = [0, 0, 814633695578, 3416086271431, 3925273006990, 1065384169316, 54930991058, 0, 0, 0] := by
  rw [show A10K2.u3198 = KTree.node A10K2.t3202 (nat_lit 55231964) (nat_lit 5601451034) (nat_lit 0) A10K2.t3203 from rfl, totK_node, tot3202, tot3203]
  decide +kernel

theorem arows3200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3200 = true := by
  rw [show A10K2.u3200 = KTree.node A10K2.t3204 (nat_lit 55247295) (nat_lit 14166159072) (nat_lit 0) A10K2.t3205 from rfl, allE_node, rows3204, irow3200, rows3205]
  all_goals rfl

theorem atot3200 : totK PA10K2 A10K2.u3200 = [0, 476537513919, 1944603884521, 3037047977326, 2769197116619, 1334578986097, 218133052917, 6354482628, 0, 0] := by
  rw [show A10K2.u3200 = KTree.node A10K2.t3204 (nat_lit 55247295) (nat_lit 14166159072) (nat_lit 0) A10K2.t3205 from rfl, totK_node, tot3204, tot3205]
  decide +kernel

theorem arows3201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3201 = true := by
  rw [show A10K2.u3201 = KTree.node A10K2.t3206 (nat_lit 55256915) (nat_lit 10374073118) (nat_lit 0) A10K2.t3207 from rfl, allE_node, rows3206, irow3201, rows3207]
  all_goals rfl

theorem atot3201 : totK PA10K2 A10K2.u3201 = [0, 817218475588, 3182854071669, 4025081416512, 1797151059746, 244938247213, 7903172220, 0, 0, 0] := by
  rw [show A10K2.u3201 = KTree.node A10K2.t3206 (nat_lit 55256915) (nat_lit 10374073118) (nat_lit 0) A10K2.t3207 from rfl, totK_node, tot3206, tot3207]
  decide +kernel

theorem arows3204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3204 = true := by
  rw [show A10K2.u3204 = KTree.node A10K2.t3208 (nat_lit 55261874) (nat_lit 14946481621) (nat_lit 0) A10K2.t3209 from rfl, allE_node, rows3208, irow3204, rows3209]
  all_goals rfl

theorem atot3204 : totK PA10K2 A10K2.u3204 = [0, 334869779639, 1994839681928, 3974713901317, 2884326424627, 620299192952, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u3204 = KTree.node A10K2.t3208 (nat_lit 55261874) (nat_lit 14946481621) (nat_lit 0) A10K2.t3209 from rfl, totK_node, tot3208, tot3209]
  decide +kernel

theorem arows3205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3205 = true := by
  rw [show A10K2.u3205 = KTree.node A10K2.t3210 (nat_lit 55275218) (nat_lit 15272314365) (nat_lit 0) A10K2.t3211 from rfl, allE_node, rows3210, irow3205, rows3211]
  all_goals rfl

theorem atot3205 : totK PA10K2 A10K2.u3205 = [0, 502001897941, 2509659940604, 4152742887494, 2464149364524, 395347869502, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u3205 = KTree.node A10K2.t3210 (nat_lit 55275218) (nat_lit 15272314365) (nat_lit 0) A10K2.t3211 from rfl, totK_node, tot3210, tot3211]
  decide +kernel

theorem arows3207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3207 = true := by
  rw [show A10K2.u3207 = KTree.node A10K2.t3212 (nat_lit 55280113) (nat_lit 8771603586) (nat_lit 0) A10K2.t3213 from rfl, allE_node, rows3212, irow3207, rows3213]
  all_goals rfl

theorem atot3207 : totK PA10K2 A10K2.u3207 = [0, 0, 798026428868, 3290855213397, 4231790532903, 1702796457212, 145836318460, 0, 0, 0] := by
  rw [show A10K2.u3207 = KTree.node A10K2.t3212 (nat_lit 55280113) (nat_lit 8771603586) (nat_lit 0) A10K2.t3213 from rfl, totK_node, tot3212, tot3213]
  decide +kernel

theorem arows3208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3208 = true := by
  rw [show A10K2.u3208 = KTree.node A10K2.t3214 (nat_lit 55289779) (nat_lit 9868432826) (nat_lit 0) A10K2.t3215 from rfl, allE_node, rows3214, irow3208, rows3215]
  all_goals rfl

theorem atot3208 : totK PA10K2 A10K2.u3208 = [0, 0, 817074536471, 3280501206971, 4111663717566, 1645628592220, 134159251219, 0, 0, 0] := by
  rw [show A10K2.u3208 = KTree.node A10K2.t3214 (nat_lit 55289779) (nat_lit 9868432826) (nat_lit 0) A10K2.t3215 from rfl, totK_node, tot3214, tot3215]
  decide +kernel

theorem arows3212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3212 = true := by
  rw [show A10K2.u3212 = KTree.node A10K2.t3216 (nat_lit 55295408) (nat_lit 13538069344) (nat_lit 0) A10K2.t3217 from rfl, allE_node, rows3216, irow3212, rows3217]
  all_goals rfl

theorem atot3212 : totK PA10K2 A10K2.u3212 = [0, 0, 512905690969, 2580465433237, 4104986550214, 2338305783537, 338540018629, 7047025452, 0, 0] := by
  rw [show A10K2.u3212 = KTree.node A10K2.t3216 (nat_lit 55295408) (nat_lit 13538069344) (nat_lit 0) A10K2.t3217 from rfl, totK_node, tot3216, tot3217]
  decide +kernel

theorem arows3213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3213 = true := by
  rw [show A10K2.u3213 = KTree.node A10K2.t3218 (nat_lit 55308735) (nat_lit 14252228148) (nat_lit 0) A10K2.t3219 from rfl, allE_node, rows3218, irow3213, rows3219]
  all_goals rfl

theorem atot3213 : totK PA10K2 A10K2.u3213 = [0, 0, 323255249417, 2125797694702, 4255852726198, 2774970898277, 419588893607, 6157148557, 0, 0] := by
  rw [show A10K2.u3213 = KTree.node A10K2.t3218 (nat_lit 55308735) (nat_lit 14252228148) (nat_lit 0) A10K2.t3219 from rfl, totK_node, tot3218, tot3219]
  decide +kernel

theorem arows3215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3215 = true := by
  rw [show A10K2.u3215 = KTree.node A10K2.t3220 (nat_lit 55388053) (nat_lit 5171259390) (nat_lit 0) A10K2.t3221 from rfl, allE_node, rows3220, irow3215, rows3221]
  all_goals rfl

theorem atot3215 : totK PA10K2 A10K2.u3215 = [0, 0, 873756522823, 3084436673657, 3505237821517, 1787180774893, 529276259564, 41354396063, 0, 0] := by
  rw [show A10K2.u3215 = KTree.node A10K2.t3220 (nat_lit 55388053) (nat_lit 5171259390) (nat_lit 0) A10K2.t3221 from rfl, totK_node, tot3220, tot3221]
  decide +kernel

theorem arows3216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3216 = true := by
  rw [show A10K2.u3216 = KTree.node A10K2.t3222 (nat_lit 55392530) (nat_lit 14632383213) (nat_lit 0) A10K2.t3223 from rfl, allE_node, rows3222, irow3216, rows3223]
  all_goals rfl

theorem atot3216 : totK PA10K2 A10K2.u3216 = [0, 0, 261126451520, 1743097106346, 3857873668328, 2980456102219, 626108618196, 31768748853, 0, 0] := by
  rw [show A10K2.u3216 = KTree.node A10K2.t3222 (nat_lit 55392530) (nat_lit 14632383213) (nat_lit 0) A10K2.t3223 from rfl, totK_node, tot3222, tot3223]
  decide +kernel

theorem arows3219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3219 = true := by
  rw [show A10K2.u3219 = KTree.node A10K2.t3224 (nat_lit 55397154) (nat_lit 12862676312) (nat_lit 0) A10K2.t3225 from rfl, allE_node, rows3224, irow3219, rows3225]
  all_goals rfl

theorem atot3219 : totK PA10K2 A10K2.u3219 = [0, 0, 461208852344, 2581146884132, 4182955856056, 1894032890282, 163923980379, 0, 0, 0] := by
  rw [show A10K2.u3219 = KTree.node A10K2.t3224 (nat_lit 55397154) (nat_lit 12862676312) (nat_lit 0) A10K2.t3225 from rfl, totK_node, tot3224, tot3225]
  decide +kernel

theorem arows3220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3220 = true := by
  rw [show A10K2.u3220 = KTree.node A10K2.t3226 (nat_lit 55405617) (nat_lit 8956751894) (nat_lit 0) A10K2.t3227 from rfl, allE_node, rows3226, irow3220, rows3227]
  all_goals rfl

theorem atot3220 : totK PA10K2 A10K2.u3220 = [0, 0, 784301050123, 3175101238956, 4132955192488, 1836903084398, 230553682457, 6239673734, 0, 0] := by
  rw [show A10K2.u3220 = KTree.node A10K2.t3226 (nat_lit 55405617) (nat_lit 8956751894) (nat_lit 0) A10K2.t3227 from rfl, totK_node, tot3226, tot3227]
  decide +kernel

theorem arows3222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3222 = true := by
  rw [show A10K2.u3222 = KTree.node A10K2.t3228 (nat_lit 55410582) (nat_lit 15989820252) (nat_lit 0) A10K2.t3229 from rfl, allE_node, rows3228, irow3222, rows3229]
  all_goals rfl

theorem atot3222 : totK PA10K2 A10K2.u3222 = [0, 0, 0, 1069683561023, 3735792972995, 3823580864968, 1095395368219, 67541609336, 0, 0] := by
  rw [show A10K2.u3222 = KTree.node A10K2.t3228 (nat_lit 55410582) (nat_lit 15989820252) (nat_lit 0) A10K2.t3229 from rfl, totK_node, tot3228, tot3229]
  decide +kernel

theorem arows3223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3223 = true := by
  rw [show A10K2.u3223 = KTree.node A10K2.t3230 (nat_lit 55424342) (nat_lit 11512749655) (nat_lit 0) A10K2.t3231 from rfl, allE_node, rows3230, irow3223, rows3231]
  all_goals rfl

theorem atot3223 : totK PA10K2 A10K2.u3223 = [0, 0, 0, 286168622330, 2086618131646, 3983679342099, 2520063923082, 538143242785, 31018567651, 0] := by
  rw [show A10K2.u3223 = KTree.node A10K2.t3230 (nat_lit 55424342) (nat_lit 11512749655) (nat_lit 0) A10K2.t3231 from rfl, totK_node, tot3230, tot3231]
  decide +kernel

theorem arows3228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3228 = true := by
  rw [show A10K2.u3228 = KTree.node A10K2.t3232 (nat_lit 55429015) (nat_lit 13475229992) (nat_lit 0) A10K2.t3233 from rfl, allE_node, rows3232, irow3228, rows3233]
  all_goals rfl

theorem atot3228 : totK PA10K2 A10K2.u3228 = [0, 0, 0, 715817143954, 3129203159681, 3961015346234, 1315683273723, 94165340858, 0, 0] := by
  rw [show A10K2.u3228 = KTree.node A10K2.t3232 (nat_lit 55429015) (nat_lit 13475229992) (nat_lit 0) A10K2.t3233 from rfl, totK_node, tot3232, tot3233]
  decide +kernel

theorem arows3229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3229 = true := by
  rw [show A10K2.u3229 = KTree.node A10K2.t3234 (nat_lit 55436792) (nat_lit 12005796913) (nat_lit 0) A10K2.t3235 from rfl, allE_node, rows3234, irow3229, rows3235]
  all_goals rfl

theorem atot3229 : totK PA10K2 A10K2.u3229 = [0, 0, 166940909255, 1179644334999, 3032516777824, 3543376240486, 1564545476924, 212236174594, 5685526223, 0] := by
  rw [show A10K2.u3229 = KTree.node A10K2.t3234 (nat_lit 55436792) (nat_lit 12005796913) (nat_lit 0) A10K2.t3235 from rfl, totK_node, tot3234, tot3235]
  decide +kernel

theorem arows3231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3231 = true := by
  rw [show A10K2.u3231 = KTree.node A10K2.t3236 (nat_lit 55449824) (nat_lit 8763854771) (nat_lit 0) A10K2.t3237 from rfl, allE_node, rows3236, irow3231, rows3237]
  all_goals rfl

theorem atot3231 : totK PA10K2 A10K2.u3231 = [0, 0, 629910093284, 2814662026325, 3938666816004, 1673817281947, 165955694596, 5460492893, 0, 0] := by
  rw [show A10K2.u3231 = KTree.node A10K2.t3236 (nat_lit 55449824) (nat_lit 8763854771) (nat_lit 0) A10K2.t3237 from rfl, totK_node, tot3236, tot3237]
  decide +kernel

theorem arows3232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3232 = true := by
  rw [show A10K2.u3232 = KTree.node A10K2.t3238 (nat_lit 55456979) (nat_lit 10878723544) (nat_lit 0) A10K2.t3239 from rfl, allE_node, rows3238, irow3232, rows3239]
  all_goals rfl

theorem atot3232 : totK PA10K2 A10K2.u3232 = [0, 0, 431332874765, 2256636900095, 4003922682183, 2558541324961, 478980834453, 25734533292, 0, 0] := by
  rw [show A10K2.u3232 = KTree.node A10K2.t3238 (nat_lit 55456979) (nat_lit 10878723544) (nat_lit 0) A10K2.t3239 from rfl, totK_node, tot3238, tot3239]
  decide +kernel

theorem arows3235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3235 = true := by
  rw [show A10K2.u3235 = KTree.node A10K2.t3240 (nat_lit 55461311) (nat_lit 12743579776) (nat_lit 0) A10K2.t3241 from rfl, allE_node, rows3240, irow3235, rows3241]
  all_goals rfl

theorem atot3235 : totK PA10K2 A10K2.u3235 = [0, 0, 774509747268, 3135973432020, 3770263479136, 1412491193646, 181220770303, 6034215561, 0, 0] := by
  rw [show A10K2.u3235 = KTree.node A10K2.t3240 (nat_lit 55461311) (nat_lit 12743579776) (nat_lit 0) A10K2.t3241 from rfl, totK_node, tot3240, tot3241]
  decide +kernel

theorem arows3236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3236 = true := by
  rw [show A10K2.u3236 = KTree.node A10K2.t3242 (nat_lit 55476269) (nat_lit 6297487042) (nat_lit 0) A10K2.t3243 from rfl, allE_node, rows3242, irow3236, rows3243]
  all_goals rfl

theorem atot3236 : totK PA10K2 A10K2.u3236 = [0, 0, 0, 1292249978837, 4113651383268, 3206111766608, 502993922150, 17863269420, 0, 0] := by
  rw [show A10K2.u3236 = KTree.node A10K2.t3242 (nat_lit 55476269) (nat_lit 6297487042) (nat_lit 0) A10K2.t3243 from rfl, totK_node, tot3242, tot3243]
  decide +kernel

theorem arows3238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3238 = true := by
  rw [show A10K2.u3238 = KTree.node A10K2.t3244 (nat_lit 55487716) (nat_lit 11866023538) (nat_lit 0) A10K2.t3245 from rfl, allE_node, rows3244, irow3238, rows3245]
  all_goals rfl

theorem atot3238 : totK PA10K2 A10K2.u3238 = [0, 0, 0, 1061923853011, 3784397430849, 3761095816901, 873899700728, 44649496490, 0, 0] := by
  rw [show A10K2.u3238 = KTree.node A10K2.t3244 (nat_lit 55487716) (nat_lit 11866023538) (nat_lit 0) A10K2.t3245 from rfl, totK_node, tot3244, tot3245]
  decide +kernel

theorem arows3239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3239 = true := by
  rw [show A10K2.u3239 = KTree.node A10K2.t3246 (nat_lit 55497045) (nat_lit 6867476576) (nat_lit 0) A10K2.t3247 from rfl, allE_node, rows3246, irow3239, rows3247]
  all_goals rfl

theorem atot3239 : totK PA10K2 A10K2.u3239 = [0, 0, 187384252814, 758059399979, 2357336456736, 3809455657045, 1775276869924, 240182798325, 6239673734, 0] := by
  rw [show A10K2.u3239 = KTree.node A10K2.t3246 (nat_lit 55497045) (nat_lit 6867476576) (nat_lit 0) A10K2.t3247 from rfl, totK_node, tot3246, tot3247]
  decide +kernel

theorem arows3243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3243 = true := by
  rw [show A10K2.u3243 = KTree.node A10K2.t3248 (nat_lit 55513988) (nat_lit 5159823457) (nat_lit 0) A10K2.t3249 from rfl, allE_node, rows3248, irow3243, rows3249]
  all_goals rfl

theorem atot3243 : totK PA10K2 A10K2.u3243 = [0, 0, 640940993575, 2975296282258, 4379604108339, 2027179352177, 193923052815, 0, 0, 0] := by
  rw [show A10K2.u3243 = KTree.node A10K2.t3248 (nat_lit 55513988) (nat_lit 5159823457) (nat_lit 0) A10K2.t3249 from rfl, totK_node, tot3248, tot3249]
  decide +kernel

theorem arows3244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3244 = true := by
  rw [show A10K2.u3244 = KTree.node A10K2.t3250 (nat_lit 55521273) (nat_lit 6033803245) (nat_lit 0) A10K2.t3251 from rfl, allE_node, rows3250, irow3244, rows3251]
  all_goals rfl

theorem atot3244 : totK PA10K2 A10K2.u3244 = [0, 0, 455869960580, 2318562855185, 3919639836561, 2554487869996, 550318348309, 31285368086, 0, 0] := by
  rw [show A10K2.u3244 = KTree.node A10K2.t3250 (nat_lit 55521273) (nat_lit 6033803245) (nat_lit 0) A10K2.t3251 from rfl, totK_node, tot3250, tot3251]
  decide +kernel

theorem arows3246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3246 = true := by
  rw [show A10K2.u3246 = KTree.node A10K2.t3252 (nat_lit 55535031) (nat_lit 15077211702) (nat_lit 0) A10K2.t3253 from rfl, allE_node, rows3252, irow3246, rows3253]
  all_goals rfl

theorem atot3246 : totK PA10K2 A10K2.u3246 = [0, 0, 835948860983, 3343687492386, 4149033236837, 1547377473140, 115965018089, 0, 0, 0] := by
  rw [show A10K2.u3246 = KTree.node A10K2.t3252 (nat_lit 55535031) (nat_lit 15077211702) (nat_lit 0) A10K2.t3253 from rfl, totK_node, tot3252, tot3253]
  decide +kernel

theorem arows3247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3247 = true := by
  rw [show A10K2.u3247 = KTree.node A10K2.t3254 (nat_lit 55540776) (nat_lit 10004893959) (nat_lit 0) A10K2.t3255 from rfl, allE_node, rows3254, irow3247, rows3255]
  all_goals rfl

theorem atot3247 : totK PA10K2 A10K2.u3247 = [0, 292640272425, 817924421101, 1366619788838, 3173132684782, 3359088150847, 947218048660, 48472019145, 0, 0] := by
  rw [show A10K2.u3247 = KTree.node A10K2.t3254 (nat_lit 55540776) (nat_lit 10004893959) (nat_lit 0) A10K2.t3255 from rfl, totK_node, tot3254, tot3255]
  decide +kernel

theorem arows3250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3250 = true := by
  rw [show A10K2.u3250 = KTree.node A10K2.t3256 (nat_lit 55579017) (nat_lit 9617707213) (nat_lit 0) A10K2.t3257 from rfl, allE_node, rows3256, irow3250, rows3257]
  all_goals rfl

theorem atot3250 : totK PA10K2 A10K2.u3250 = [0, 510087213982, 2619913457224, 4102906562896, 1931827328811, 240593340700, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u3250 = KTree.node A10K2.t3256 (nat_lit 55579017) (nat_lit 9617707213) (nat_lit 0) A10K2.t3257 from rfl, totK_node, tot3256, tot3257]
  decide +kernel

theorem arows3251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3251 = true := by
  rw [show A10K2.u3251 = KTree.node A10K2.t3258 (nat_lit 55593773) (nat_lit 6630724235) (nat_lit 0) A10K2.t3259 from rfl, allE_node, rows3258, irow3251, rows3259]
  all_goals rfl

theorem atot3251 : totK PA10K2 A10K2.u3251 = [0, 497071727381, 2575714487853, 4182959762349, 2013357494705, 202831075397, 0, 0, 0, 0] := by
  rw [show A10K2.u3251 = KTree.node A10K2.t3258 (nat_lit 55593773) (nat_lit 6630724235) (nat_lit 0) A10K2.t3259 from rfl, totK_node, tot3258, tot3259]
  decide +kernel

theorem arows3253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3253 = true := by
  rw [show A10K2.u3253 = KTree.node A10K2.t3260 (nat_lit 55609912) (nat_lit 13787993803) (nat_lit 0) A10K2.t3261 from rfl, allE_node, rows3260, irow3253, rows3261]
  all_goals rfl

theorem atot3253 : totK PA10K2 A10K2.u3253 = [0, 0, 1004215840978, 3674850280557, 3799781735930, 978213840401, 63287484054, 0, 0, 0] := by
  rw [show A10K2.u3253 = KTree.node A10K2.t3260 (nat_lit 55609912) (nat_lit 13787993803) (nat_lit 0) A10K2.t3261 from rfl, totK_node, tot3260, tot3261]
  decide +kernel

theorem arows3254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3254 = true := by
  rw [show A10K2.u3254 = KTree.node A10K2.t3262 (nat_lit 55629831) (nat_lit 10345315748) (nat_lit 0) A10K2.t3263 from rfl, allE_node, rows3262, irow3254, rows3263]
  all_goals rfl

theorem atot3254 : totK PA10K2 A10K2.u3254 = [0, 316846731414, 1312838714182, 2704621531923, 3354016125202, 1522658225438, 198207399149, 5546304973, 0, 0] := by
  rw [show A10K2.u3254 = KTree.node A10K2.t3262 (nat_lit 55629831) (nat_lit 10345315748) (nat_lit 0) A10K2.t3263 from rfl, totK_node, tot3262, tot3263]
  decide +kernel

theorem arows3260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3260 = true := by
  rw [show A10K2.u3260 = KTree.node A10K2.t3264 (nat_lit 55652010) (nat_lit 12668747883) (nat_lit 0) A10K2.t3265 from rfl, allE_node, rows3264, irow3260, rows3265]
  all_goals rfl

theorem atot3260 : totK PA10K2 A10K2.u3260 = [0, 527310909255, 2549358395109, 3984866309929, 2214876046186, 425723223748, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u3260 = KTree.node A10K2.t3264 (nat_lit 55652010) (nat_lit 12668747883) (nat_lit 0) A10K2.t3265 from rfl, totK_node, tot3264, tot3265]
  decide +kernel

theorem arows3261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3261 = true := by
  rw [show A10K2.u3261 = KTree.node A10K2.t3266 (nat_lit 55657298) (nat_lit 12866758809) (nat_lit 0) A10K2.t3267 from rfl, allE_node, rows3266, irow3261, rows3267]
  all_goals rfl

theorem atot3261 : totK PA10K2 A10K2.u3261 = [0, 760368498474, 2898962466201, 3692893648432, 1845388324228, 265164019365, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u3261 = KTree.node A10K2.t3266 (nat_lit 55657298) (nat_lit 12866758809) (nat_lit 0) A10K2.t3267 from rfl, totK_node, tot3266, tot3267]
  decide +kernel

theorem arows3263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3263 = true := by
  rw [show A10K2.u3263 = KTree.node A10K2.t3268 (nat_lit 55662935) (nat_lit 4563600352) (nat_lit 0) A10K2.t3269 from rfl, allE_node, rows3268, irow3263, rows3269]
  all_goals rfl

theorem atot3263 : totK PA10K2 A10K2.u3263 = [0, 474944754325, 2508779912974, 4183641885379, 2186160206298, 301874974759, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3263 = KTree.node A10K2.t3268 (nat_lit 55662935) (nat_lit 4563600352) (nat_lit 0) A10K2.t3269 from rfl, totK_node, tot3268, tot3269]
  decide +kernel

theorem arows3264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3264 = true := by
  rw [show A10K2.u3264 = KTree.node A10K2.t3270 (nat_lit 55671815) (nat_lit 14175392568) (nat_lit 0) A10K2.t3271 from rfl, allE_node, rows3270, irow3264, rows3271]
  all_goals rfl

theorem atot3264 : totK PA10K2 A10K2.u3264 = [0, 117338935714, 1545613530425, 4121134287603, 3447403084464, 865323915394, 48349237427, 0, 0, 0] := by
  rw [show A10K2.u3264 = KTree.node A10K2.t3270 (nat_lit 55671815) (nat_lit 14175392568) (nat_lit 0) A10K2.t3271 from rfl, totK_node, tot3270, tot3271]
  decide +kernel

theorem arows3267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3267 = true := by
  rw [show A10K2.u3267 = KTree.node A10K2.t3272 (nat_lit 55684564) (nat_lit 8162892843) (nat_lit 0) A10K2.t3273 from rfl, allE_node, rows3272, irow3267, rows3273]
  all_goals rfl

theorem atot3267 : totK PA10K2 A10K2.u3267 = [0, 0, 525699093747, 2541453774618, 3952246883425, 2123057011476, 409339687510, 25565504801, 0, 0] := by
  rw [show A10K2.u3267 = KTree.node A10K2.t3272 (nat_lit 55684564) (nat_lit 8162892843) (nat_lit 0) A10K2.t3273 from rfl, totK_node, tot3272, tot3273]
  decide +kernel

theorem arows3268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3268 = true := by
  rw [show A10K2.u3268 = KTree.node A10K2.t3274 (nat_lit 55690066) (nat_lit 12664477791) (nat_lit 0) A10K2.t3275 from rfl, allE_node, rows3274, irow3268, rows3275]
  all_goals rfl

theorem atot3268 : totK PA10K2 A10K2.u3268 = [0, 0, 760220352298, 2969779228435, 3781983896707, 1716343792758, 226966334845, 5517381808, 0, 0] := by
  rw [show A10K2.u3268 = KTree.node A10K2.t3274 (nat_lit 55690066) (nat_lit 12664477791) (nat_lit 0) A10K2.t3275 from rfl, totK_node, tot3274, tot3275]
  decide +kernel

theorem arows3270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3270 = true := by
  rw [show A10K2.u3270 = KTree.node A10K2.t3276 (nat_lit 55695877) (nat_lit 6480272069) (nat_lit 0) A10K2.t3277 from rfl, allE_node, rows3276, irow3270, rows3277]
  all_goals rfl

theorem atot3270 : totK PA10K2 A10K2.u3270 = [0, 0, 505556307028, 2579566568136, 4166379285135, 2022145063967, 245216352043, 6121173289, 0, 0] := by
  rw [show A10K2.u3270 = KTree.node A10K2.t3276 (nat_lit 55695877) (nat_lit 6480272069) (nat_lit 0) A10K2.t3277 from rfl, totK_node, tot3276, tot3277]
  decide +kernel

theorem arows3271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3271 = true := by
  rw [show A10K2.u3271 = KTree.node A10K2.t3278 (nat_lit 55707713) (nat_lit 10335345372) (nat_lit 0) A10K2.t3279 from rfl, allE_node, rows3278, irow3271, rows3279]
  all_goals rfl

theorem atot3271 : totK PA10K2 A10K2.u3271 = [0, 582799510374, 2418582772102, 3500291542123, 2241106277620, 719232562187, 62678265349, 0, 0, 0] := by
  rw [show A10K2.u3271 = KTree.node A10K2.t3278 (nat_lit 55707713) (nat_lit 10335345372) (nat_lit 0) A10K2.t3279 from rfl, totK_node, tot3278, tot3279]
  decide +kernel

theorem arows3275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3275 = true := by
  rw [show A10K2.u3275 = KTree.node A10K2.t3280 (nat_lit 55715327) (nat_lit 13400349110) (nat_lit 0) A10K2.t3281 from rfl, allE_node, rows3280, irow3275, rows3281]
  all_goals rfl

theorem atot3275 : totK PA10K2 A10K2.u3275 = [0, 769220453689, 2935795803313, 3745919335410, 1796770683557, 286941395633, 10760911071, 0, 0, 0] := by
  rw [show A10K2.u3275 = KTree.node A10K2.t3280 (nat_lit 55715327) (nat_lit 13400349110) (nat_lit 0) A10K2.t3281 from rfl, totK_node, tot3280, tot3281]
  decide +kernel

theorem arows3276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3276 = true := by
  rw [show A10K2.u3276 = KTree.node A10K2.t3282 (nat_lit 55720168) (nat_lit 6717044629) (nat_lit 0) A10K2.t3283 from rfl, allE_node, rows3282, irow3276, rows3283]
  all_goals rfl

theorem atot3276 : totK PA10K2 A10K2.u3276 = [0, 238785603865, 1752861793098, 3866742897153, 2961666363102, 635748773415, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3276 = KTree.node A10K2.t3282 (nat_lit 55720168) (nat_lit 6717044629) (nat_lit 0) A10K2.t3283 from rfl, totK_node, tot3282, tot3283]
  decide +kernel

theorem arows3278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3278 = true := by
  rw [show A10K2.u3278 = KTree.node A10K2.t3284 (nat_lit 55724394) (nat_lit 9839619679) (nat_lit 0) A10K2.t3285 from rfl, allE_node, rows3284, irow3278, rows3285]
  all_goals rfl

theorem atot3278 : totK PA10K2 A10K2.u3278 = [0, 583317622402, 2890569802525, 4175136820639, 1656964430748, 125584219509, 0, 0, 0, 0] := by
  rw [show A10K2.u3278 = KTree.node A10K2.t3284 (nat_lit 55724394) (nat_lit 9839619679) (nat_lit 0) A10K2.t3285 from rfl, totK_node, tot3284, tot3285]
  decide +kernel

theorem arows3279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3279 = true := by
  rw [show A10K2.u3279 = KTree.node A10K2.t3286 (nat_lit 55740534) (nat_lit 4933530356) (nat_lit 0) A10K2.t3287 from rfl, allE_node, rows3286, irow3279, rows3287]
  all_goals rfl

theorem atot3279 : totK PA10K2 A10K2.u3279 = [0, 0, 991661922816, 3685987554221, 3691575568397, 945567438928, 58931901996, 0, 0, 0] := by
  rw [show A10K2.u3279 = KTree.node A10K2.t3286 (nat_lit 55740534) (nat_lit 4933530356) (nat_lit 0) A10K2.t3287 from rfl, totK_node, tot3286, tot3287]
  decide +kernel

theorem arows3282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3282 = true := by
  rw [show A10K2.u3282 = KTree.node A10K2.t3288 (nat_lit 55750558) (nat_lit 15257075862) (nat_lit 0) A10K2.t3289 from rfl, allE_node, rows3288, irow3282, rows3289]
  all_goals rfl

theorem atot3282 : totK PA10K2 A10K2.u3282 = [0, 0, 979941970775, 3580863560519, 3794889770515, 1030231307084, 63118289004, 0, 0, 0] := by
  rw [show A10K2.u3282 = KTree.node A10K2.t3288 (nat_lit 55750558) (nat_lit 15257075862) (nat_lit 0) A10K2.t3289 from rfl, totK_node, tot3288, tot3289]
  decide +kernel

theorem arows3283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3283 = true := by
  rw [show A10K2.u3283 = KTree.node A10K2.t3290 (nat_lit 55760057) (nat_lit 731654889) (nat_lit 0) A10K2.t3291 from rfl, allE_node, rows3290, irow3283, rows3291]
  all_goals rfl

theorem atot3283 : totK PA10K2 A10K2.u3283 = [0, 0, 572421784704, 2644870667286, 3962635077263, 1841062417932, 271677105452, 6354482628, 0, 0] := by
  rw [show A10K2.u3283 = KTree.node A10K2.t3290 (nat_lit 55760057) (nat_lit 731654889) (nat_lit 0) A10K2.t3291 from rfl, totK_node, tot3290, tot3291]
  decide +kernel

theorem arows3285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3285 = true := by
  rw [show A10K2.u3285 = KTree.node A10K2.t3292 (nat_lit 55841060) (nat_lit 13697790674) (nat_lit 0) A10K2.t3293 from rfl, allE_node, rows3292, irow3285, rows3293]
  all_goals rfl

theorem atot3285 : totK PA10K2 A10K2.u3285 = [0, 0, 536184975795, 2700852864259, 4089107418360, 1874184294177, 240410964148, 5447185874, 0, 0] := by
  rw [show A10K2.u3285 = KTree.node A10K2.t3292 (nat_lit 55841060) (nat_lit 13697790674) (nat_lit 0) A10K2.t3293 from rfl, totK_node, tot3292, tot3293]
  decide +kernel

theorem arows3286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3286 = true := by
  rw [show A10K2.u3286 = KTree.node A10K2.t3294 (nat_lit 55855872) (nat_lit 14038219998) (nat_lit 0) A10K2.t3295 from rfl, allE_node, rows3294, irow3286, rows3295]
  all_goals rfl

theorem atot3286 : totK PA10K2 A10K2.u3286 = [0, 0, 495048406196, 2658411888767, 4218202981631, 1834057804615, 172294063882, 0, 0, 0] := by
  rw [show A10K2.u3286 = KTree.node A10K2.t3294 (nat_lit 55855872) (nat_lit 14038219998) (nat_lit 0) A10K2.t3295 from rfl, totK_node, tot3294, tot3295]
  decide +kernel

theorem arows3291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3291 = true := by
  rw [show A10K2.u3291 = KTree.node A10K2.t3296 (nat_lit 55912727) (nat_lit 8942793278) (nat_lit 0) A10K2.t3297 from rfl, allE_node, rows3296, irow3291, rows3297]
  all_goals rfl

theorem atot3291 : totK PA10K2 A10K2.u3291 = [0, 0, 844157640669, 3238558130525, 3837528442105, 1572906137596, 216432279732, 6354482628, 0, 0] := by
  rw [show A10K2.u3291 = KTree.node A10K2.t3296 (nat_lit 55912727) (nat_lit 8942793278) (nat_lit 0) A10K2.t3297 from rfl, totK_node, tot3296, tot3297]
  decide +kernel

theorem arows3292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3292 = true := by
  rw [show A10K2.u3292 = KTree.node A10K2.t3298 (nat_lit 55917686) (nat_lit 15880443759) (nat_lit 0) A10K2.t3299 from rfl, allE_node, rows3298, irow3292, rows3299]
  all_goals rfl

theorem atot3292 : totK PA10K2 A10K2.u3292 = [0, 0, 466842231207, 2167822990310, 3710226616107, 2548321796935, 545676386221, 31452573850, 0, 0] := by
  rw [show A10K2.u3292 = KTree.node A10K2.t3298 (nat_lit 55917686) (nat_lit 15880443759) (nat_lit 0) A10K2.t3299 from rfl, totK_node, tot3298, tot3299]
  decide +kernel

theorem arows3294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3294 = true := by
  rw [show A10K2.u3294 = KTree.node A10K2.t3300 (nat_lit 55923872) (nat_lit 7515942373) (nat_lit 0) A10K2.t3301 from rfl, allE_node, rows3300, irow3294, rows3301]
  all_goals rfl

theorem atot3294 : totK PA10K2 A10K2.u3294 = [0, 0, 482499997145, 2475563942815, 4074140737475, 2111322688084, 264759506410, 6354482628, 0, 0] := by
  rw [show A10K2.u3294 = KTree.node A10K2.t3300 (nat_lit 55923872) (nat_lit 7515942373) (nat_lit 0) A10K2.t3301 from rfl, totK_node, tot3300, tot3301]
  decide +kernel

theorem arows3295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3295 = true := by
  rw [show A10K2.u3295 = KTree.node A10K2.t3302 (nat_lit 55930830) (nat_lit 14588966310) (nat_lit 0) A10K2.t3303 from rfl, allE_node, rows3302, irow3295, rows3303]
  all_goals rfl

theorem atot3295 : totK PA10K2 A10K2.u3295 = [0, 0, 507898111864, 2577313896549, 4280571695061, 2413156472030, 332634132573, 6962742351, 0, 0] := by
  rw [show A10K2.u3295 = KTree.node A10K2.t3302 (nat_lit 55930830) (nat_lit 14588966310) (nat_lit 0) A10K2.t3303 from rfl, totK_node, tot3302, tot3303]
  decide +kernel

theorem arows3298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3298 = true := by
  rw [show A10K2.u3298 = KTree.node A10K2.t3304 (nat_lit 55971336) (nat_lit 14393746616) (nat_lit 0) A10K2.t3305 from rfl, allE_node, rows3304, irow3298, rows3305]
  all_goals rfl

theorem atot3298 : totK PA10K2 A10K2.u3298 = [0, 0, 613248963072, 2732608803705, 3983287336193, 1747861116678, 213386271159, 5460492893, 0, 0] := by
  rw [show A10K2.u3298 = KTree.node A10K2.t3304 (nat_lit 55971336) (nat_lit 14393746616) (nat_lit 0) A10K2.t3305 from rfl, totK_node, tot3304, tot3305]
  decide +kernel

theorem arows3299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3299 = true := by
  rw [show A10K2.u3299 = KTree.node A10K2.t3306 (nat_lit 55978851) (nat_lit 8665999144) (nat_lit 0) A10K2.t3307 from rfl, allE_node, rows3306, irow3299, rows3307]
  all_goals rfl

theorem atot3299 : totK PA10K2 A10K2.u3299 = [0, 0, 633184153174, 2840281976832, 3934111626558, 1876075155620, 323837843266, 24969229125, 0, 0] := by
  rw [show A10K2.u3299 = KTree.node A10K2.t3306 (nat_lit 55978851) (nat_lit 8665999144) (nat_lit 0) A10K2.t3307 from rfl, totK_node, tot3306, tot3307]
  decide +kernel

theorem arows3301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3301 = true := by
  rw [show A10K2.u3301 = KTree.node A10K2.t3308 (nat_lit 55984680) (nat_lit 12594929656) (nat_lit 0) A10K2.t3309 from rfl, allE_node, rows3308, irow3301, rows3309]
  all_goals rfl

theorem atot3301 : totK PA10K2 A10K2.u3301 = [0, 0, 707365779400, 2745474155216, 3749539600176, 1831251366943, 248954455845, 6034215561, 0, 0] := by
  rw [show A10K2.u3301 = KTree.node A10K2.t3308 (nat_lit 55984680) (nat_lit 12594929656) (nat_lit 0) A10K2.t3309 from rfl, totK_node, tot3308, tot3309]
  decide +kernel

theorem arows3302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3302 = true := by
  rw [show A10K2.u3302 = KTree.node A10K2.t3310 (nat_lit 55990341) (nat_lit 6202701764) (nat_lit 0) A10K2.t3311 from rfl, allE_node, rows3310, irow3302, rows3311]
  all_goals rfl

theorem atot3302 : totK PA10K2 A10K2.u3302 = [0, 0, 113126642960, 1772566014765, 4247931625456, 2649887985374, 429304556881, 11740475125, 0, 0] := by
  rw [show A10K2.u3302 = KTree.node A10K2.t3310 (nat_lit 55990341) (nat_lit 6202701764) (nat_lit 0) A10K2.t3311 from rfl, totK_node, tot3310, tot3311]
  decide +kernel

theorem arows3306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3306 = true := by
  rw [show A10K2.u3306 = KTree.node A10K2.t3312 (nat_lit 56010525) (nat_lit 6289469235) (nat_lit 0) A10K2.t3313 from rfl, allE_node, rows3312, irow3306, rows3313]
  all_goals rfl

theorem atot3306 : totK PA10K2 A10K2.u3306 = [0, 0, 0, 1205286304008, 3936050730548, 3449961486122, 738786562975, 38045387652, 0, 0] := by
  rw [show A10K2.u3306 = KTree.node A10K2.t3312 (nat_lit 56010525) (nat_lit 6289469235) (nat_lit 0) A10K2.t3313 from rfl, totK_node, tot3312, tot3313]
  decide +kernel

theorem arows3307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3307 = true := by
  rw [show A10K2.u3307 = KTree.node A10K2.t3314 (nat_lit 56019156) (nat_lit 11800462688) (nat_lit 0) A10K2.t3315 from rfl, allE_node, rows3314, irow3307, rows3315]
  all_goals rfl

theorem atot3307 : totK PA10K2 A10K2.u3307 = [0, 0, 0, 608567617877, 3122927159351, 4001110552636, 1223898870486, 80723002698, 0, 0] := by
  rw [show A10K2.u3307 = KTree.node A10K2.t3314 (nat_lit 56019156) (nat_lit 11800462688) (nat_lit 0) A10K2.t3315 from rfl, totK_node, tot3314, tot3315]
  decide +kernel

theorem arows3309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3309 = true := by
  rw [show A10K2.u3309 = KTree.node A10K2.t3316 (nat_lit 56101945) (nat_lit 7281133814) (nat_lit 0) A10K2.t3317 from rfl, allE_node, rows3316, irow3309, rows3317]
  all_goals rfl

theorem atot3309 : totK PA10K2 A10K2.u3309 = [0, 592100586184, 2467366238710, 3303846072505, 1683640710326, 940328678724, 735894025269, 168882025844, 6354482628, 0] := by
  rw [show A10K2.u3309 = KTree.node A10K2.t3316 (nat_lit 56101945) (nat_lit 7281133814) (nat_lit 0) A10K2.t3317 from rfl, totK_node, tot3316, tot3317]
  decide +kernel

theorem arows3310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3310 = true := by
  rw [show A10K2.u3310 = KTree.node A10K2.t3318 (nat_lit 56124645) (nat_lit 5611527531) (nat_lit 0) A10K2.t3319 from rfl, allE_node, rows3318, irow3310, rows3319]
  all_goals rfl

theorem atot3310 : totK PA10K2 A10K2.u3310 = [0, 794133235012, 3218822547776, 4264682085078, 1854854337165, 168894554937, 0, 0, 0, 0] := by
  rw [show A10K2.u3310 = KTree.node A10K2.t3318 (nat_lit 56124645) (nat_lit 5611527531) (nat_lit 0) A10K2.t3319 from rfl, totK_node, tot3318, tot3319]
  decide +kernel

theorem arows3313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3313 = true := by
  rw [show A10K2.u3313 = KTree.node A10K2.t3320 (nat_lit 56130714) (nat_lit 14809575548) (nat_lit 0) A10K2.t3321 from rfl, allE_node, rows3320, irow3313, rows3321]
  all_goals rfl

theorem atot3313 : totK PA10K2 A10K2.u3313 = [0, 0, 1088862261172, 3805381825327, 4018443673560, 1192594225209, 83255389061, 0, 0, 0] := by
  rw [show A10K2.u3313 = KTree.node A10K2.t3320 (nat_lit 56130714) (nat_lit 14809575548) (nat_lit 0) A10K2.t3321 from rfl, totK_node, tot3320, tot3321]
  decide +kernel

theorem arows3314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3314 = true := by
  rw [show A10K2.u3314 = KTree.node A10K2.t3322 (nat_lit 56136186) (nat_lit 5307457272) (nat_lit 0) A10K2.t3323 from rfl, allE_node, rows3322, irow3314, rows3323]
  all_goals rfl

theorem atot3314 : totK PA10K2 A10K2.u3314 = [0, 0, 656157723194, 2923198753792, 4210212610456, 2000419568542, 288503888454, 7903172220, 0, 0] := by
  rw [show A10K2.u3314 = KTree.node A10K2.t3322 (nat_lit 56136186) (nat_lit 5307457272) (nat_lit 0) A10K2.t3323 from rfl, totK_node, tot3322, tot3323]
  decide +kernel

theorem arows3316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3316 = true := by
  rw [show A10K2.u3316 = KTree.node A10K2.t3324 (nat_lit 56160218) (nat_lit 12808418316) (nat_lit 0) A10K2.t3325 from rfl, allE_node, rows3324, irow3316, rows3325]
  all_goals rfl

theorem atot3316 : totK PA10K2 A10K2.u3316 = [0, 550461195332, 2308567550852, 3593494090472, 2699912262684, 809738354371, 57551169768, 0, 0, 0] := by
  rw [show A10K2.u3316 = KTree.node A10K2.t3324 (nat_lit 56160218) (nat_lit 12808418316) (nat_lit 0) A10K2.t3325 from rfl, totK_node, tot3324, tot3325]
  decide +kernel

theorem arows3317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3317 = true := by
  rw [show A10K2.u3317 = KTree.node A10K2.t3326 (nat_lit 56178054) (nat_lit 14832189078) (nat_lit 0) A10K2.t3327 from rfl, allE_node, rows3326, irow3317, rows3327]
  all_goals rfl

theorem atot3317 : totK PA10K2 A10K2.u3317 = [0, 296440474885, 1946306473992, 4056739924653, 2877189482714, 596558805575, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3317 = KTree.node A10K2.t3326 (nat_lit 56178054) (nat_lit 14832189078) (nat_lit 0) A10K2.t3327 from rfl, totK_node, tot3326, tot3327]
  decide +kernel

theorem arows3325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3325 = true := by
  rw [show A10K2.u3325 = KTree.node A10K2.t3328 (nat_lit 56183073) (nat_lit 9428846082) (nat_lit 0) A10K2.t3329 from rfl, allE_node, rows3328, irow3325, rows3329]
  all_goals rfl

theorem atot3325 : totK PA10K2 A10K2.u3325 = [0, 556706159517, 2698942871287, 4168409486778, 1990208708790, 193309037206, 0, 0, 0, 0] := by
  rw [show A10K2.u3325 = KTree.node A10K2.t3328 (nat_lit 56183073) (nat_lit 9428846082) (nat_lit 0) A10K2.t3329 from rfl, totK_node, tot3328, tot3329]
  decide +kernel

theorem arows3326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3326 = true := by
  rw [show A10K2.u3326 = KTree.node A10K2.t3330 (nat_lit 56190862) (nat_lit 14757792515) (nat_lit 0) A10K2.t3331 from rfl, allE_node, rows3330, irow3326, rows3331]
  all_goals rfl

theorem atot3326 : totK PA10K2 A10K2.u3326 = [0, 815136327260, 3199081684325, 4051320881178, 1811943375515, 254262830628, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3326 = KTree.node A10K2.t3330 (nat_lit 56190862) (nat_lit 14757792515) (nat_lit 0) A10K2.t3331 from rfl, totK_node, tot3330, tot3331]
  decide +kernel

theorem arows3328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3328 = true := by
  rw [show A10K2.u3328 = KTree.node A10K2.t3332 (nat_lit 56196615) (nat_lit 14124766815) (nat_lit 0) A10K2.t3333 from rfl, allE_node, rows3332, irow3328, rows3333]
  all_goals rfl

theorem atot3328 : totK PA10K2 A10K2.u3328 = [0, 0, 960526180481, 3595976113822, 4014933921655, 1294363638659, 89457584680, 0, 0, 0] := by
  rw [show A10K2.u3328 = KTree.node A10K2.t3332 (nat_lit 56196615) (nat_lit 14124766815) (nat_lit 0) A10K2.t3333 from rfl, totK_node, tot3332, tot3333]
  decide +kernel

theorem arows3329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3329 = true := by
  rw [show A10K2.u3329 = KTree.node A10K2.t3334 (nat_lit 56209365) (nat_lit 2562187344) (nat_lit 0) A10K2.t3335 from rfl, allE_node, rows3334, irow3329, rows3335]
  all_goals rfl

theorem atot3329 : totK PA10K2 A10K2.u3329 = [0, 0, 498879068420, 2399433301697, 3925566616116, 2314220140837, 444388998392, 25565504801, 0, 0] := by
  rw [show A10K2.u3329 = KTree.node A10K2.t3334 (nat_lit 56209365) (nat_lit 2562187344) (nat_lit 0) A10K2.t3335 from rfl, totK_node, tot3334, tot3335]
  decide +kernel

theorem arows3332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3332 = true := by
  rw [show A10K2.u3332 = KTree.node A10K2.t3336 (nat_lit 56215594) (nat_lit 9044374027) (nat_lit 0) A10K2.t3337 from rfl, allE_node, rows3336, irow3332, rows3337]
  all_goals rfl

theorem atot3332 : totK PA10K2 A10K2.u3332 = [0, 0, 555913410347, 2828220081637, 4104529538029, 1815053893942, 225600441307, 5517381808, 0, 0] := by
  rw [show A10K2.u3332 = KTree.node A10K2.t3336 (nat_lit 56215594) (nat_lit 9044374027) (nat_lit 0) A10K2.t3337 from rfl, totK_node, tot3336, tot3337]
  decide +kernel

theorem arows3333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3333 = true := by
  rw [show A10K2.u3333 = KTree.node A10K2.t3338 (nat_lit 56223400) (nat_lit 3114659590) (nat_lit 0) A10K2.t3339 from rfl, allE_node, rows3338, irow3333, rows3339]
  all_goals rfl

theorem atot3333 : totK PA10K2 A10K2.u3333 = [0, 106966390865, 1034529086474, 3119162380352, 3791631023193, 1673767139463, 214935749329, 6121173289, 0, 0] := by
  rw [show A10K2.u3333 = KTree.node A10K2.t3338 (nat_lit 56223400) (nat_lit 3114659590) (nat_lit 0) A10K2.t3339 from rfl, totK_node, tot3338, tot3339]
  decide +kernel

theorem arows3335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3335 = true := by
  rw [show A10K2.u3335 = KTree.node A10K2.t3340 (nat_lit 56299195) (nat_lit 7017141324) (nat_lit 0) A10K2.t3341 from rfl, allE_node, rows3340, irow3335, rows3341]
  all_goals rfl

theorem atot3335 : totK PA10K2 A10K2.u3335 = [0, 518770102172, 2677923346507, 4277239050768, 2256134807691, 347400506726, 13360781053, 0, 0, 0] := by
  rw [show A10K2.u3335 = KTree.node A10K2.t3340 (nat_lit 56299195) (nat_lit 7017141324) (nat_lit 0) A10K2.t3341 from rfl, totK_node, tot3340, tot3341]
  decide +kernel

theorem arows3336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3336 = true := by
  rw [show A10K2.u3336 = KTree.node A10K2.t3342 (nat_lit 56306476) (nat_lit 13168437998) (nat_lit 0) A10K2.t3343 from rfl, allE_node, rows3342, irow3336, rows3343]
  all_goals rfl

theorem atot3336 : totK PA10K2 A10K2.u3336 = [0, 785174949095, 3202882101307, 4139502852634, 1704181374836, 150005286338, 0, 0, 0, 0] := by
  rw [show A10K2.u3336 = KTree.node A10K2.t3342 (nat_lit 56306476) (nat_lit 13168437998) (nat_lit 0) A10K2.t3343 from rfl, totK_node, tot3342, tot3343]
  decide +kernel

theorem arows3340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3340 = true := by
  rw [show A10K2.u3340 = KTree.node A10K2.t3344 (nat_lit 56320042) (nat_lit 935047555) (nat_lit 0) A10K2.t3345 from rfl, allE_node, rows3344, irow3340, rows3345]
  all_goals rfl

theorem atot3340 : totK PA10K2 A10K2.u3340 = [0, 542937375368, 2362990542873, 3746143993426, 2490971606988, 559910022015, 31677228370, 0, 0, 0] := by
  rw [show A10K2.u3340 = KTree.node A10K2.t3344 (nat_lit 56320042) (nat_lit 935047555) (nat_lit 0) A10K2.t3345 from rfl, totK_node, tot3344, tot3345]
  decide +kernel

theorem arows3341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3341 = true := by
  rw [show A10K2.u3341 = KTree.node A10K2.t3346 (nat_lit 56324534) (nat_lit 16849478543) (nat_lit 0) A10K2.t3347 from rfl, allE_node, rows3346, irow3341, rows3347]
  all_goals rfl

theorem atot3341 : totK PA10K2 A10K2.u3341 = [0, 330865856800, 2064326344539, 4146552742681, 2915378064635, 537031561323, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u3341 = KTree.node A10K2.t3346 (nat_lit 56324534) (nat_lit 16849478543) (nat_lit 0) A10K2.t3347 from rfl, totK_node, tot3346, tot3347]
  decide +kernel

theorem arows3343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3343 = true := by
  rw [show A10K2.u3343 = KTree.node A10K2.t3348 (nat_lit 56330252) (nat_lit 9163984974) (nat_lit 0) A10K2.t3349 from rfl, allE_node, rows3348, irow3343, rows3349]
  all_goals rfl

theorem atot3343 : totK PA10K2 A10K2.u3343 = [0, 0, 746528199751, 3231562870136, 4295447315511, 1682128474185, 133389362230, 0, 0, 0] := by
  rw [show A10K2.u3343 = KTree.node A10K2.t3348 (nat_lit 56330252) (nat_lit 9163984974) (nat_lit 0) A10K2.t3349 from rfl, totK_node, tot3348, tot3349]
  decide +kernel

theorem arows3344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3344 = true := by
  rw [show A10K2.u3344 = KTree.node A10K2.t3350 (nat_lit 56338130) (nat_lit 15385045096) (nat_lit 0) A10K2.t3351 from rfl, allE_node, rows3350, irow3344, rows3351]
  all_goals rfl

theorem atot3344 : totK PA10K2 A10K2.u3344 = [0, 0, 784165117069, 3113438154625, 3971945099101, 1799256653890, 248825124143, 6904928264, 0, 0] := by
  rw [show A10K2.u3344 = KTree.node A10K2.t3350 (nat_lit 56338130) (nat_lit 15385045096) (nat_lit 0) A10K2.t3351 from rfl, totK_node, tot3350, tot3351]
  decide +kernel

theorem arows3347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3347 = true := by
  rw [show A10K2.u3347 = KTree.node A10K2.t3352 (nat_lit 56343730) (nat_lit 15078393574) (nat_lit 0) A10K2.t3353 from rfl, allE_node, rows3352, irow3347, rows3353]
  all_goals rfl

theorem atot3347 : totK PA10K2 A10K2.u3347 = [0, 0, 542492176839, 2556242579041, 4059859523931, 2338220875405, 339682217265, 7047025452, 0, 0] := by
  rw [show A10K2.u3347 = KTree.node A10K2.t3352 (nat_lit 56343730) (nat_lit 15078393574) (nat_lit 0) A10K2.t3353 from rfl, totK_node, tot3352, tot3353]
  decide +kernel

theorem arows3348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3348 = true := by
  rw [show A10K2.u3348 = KTree.node A10K2.t3354 (nat_lit 56356862) (nat_lit 15844512021) (nat_lit 0) A10K2.t3355 from rfl, allE_node, rows3354, irow3348, rows3355]
  all_goals rfl

theorem atot3348 : totK PA10K2 A10K2.u3348 = [0, 0, 330021797788, 2149080298272, 4186816196057, 2740162515553, 458647460984, 12224107035, 0, 0] := by
  rw [show A10K2.u3348 = KTree.node A10K2.t3354 (nat_lit 56356862) (nat_lit 15844512021) (nat_lit 0) A10K2.t3355 from rfl, totK_node, tot3354, tot3355]
  decide +kernel

theorem arows3350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3350 = true := by
  rw [show A10K2.u3350 = KTree.node A10K2.t3356 (nat_lit 56361473) (nat_lit 10582213929) (nat_lit 0) A10K2.t3357 from rfl, allE_node, rows3356, irow3350, rows3357]
  all_goals rfl

theorem atot3350 : totK PA10K2 A10K2.u3350 = [0, 0, 591601212612, 2628431151388, 3908592092796, 2296394395861, 594106049899, 48886019071, 0, 0] := by
  rw [show A10K2.u3350 = KTree.node A10K2.t3356 (nat_lit 56361473) (nat_lit 10582213929) (nat_lit 0) A10K2.t3357 from rfl, totK_node, tot3356, tot3357]
  decide +kernel

theorem arows3351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3351 = true := by
  rw [show A10K2.u3351 = KTree.node A10K2.t3358 (nat_lit 56386118) (nat_lit 13415364663) (nat_lit 0) A10K2.t3359 from rfl, allE_node, rows3358, irow3351, rows3359]
  all_goals rfl

theorem atot3351 : totK PA10K2 A10K2.u3351 = [0, 0, 792629982373, 3143154264116, 4092556115369, 1963847946883, 285527634158, 7903172220, 0, 0] := by
  rw [show A10K2.u3351 = KTree.node A10K2.t3358 (nat_lit 56386118) (nat_lit 13415364663) (nat_lit 0) A10K2.t3359 from rfl, totK_node, tot3358, tot3359]
  decide +kernel

theorem arows3356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3356 = true := by
  rw [show A10K2.u3356 = KTree.node A10K2.t3360 (nat_lit 56391411) (nat_lit 8037392376) (nat_lit 0) A10K2.t3361 from rfl, allE_node, rows3360, irow3356, rows3361]
  all_goals rfl

theorem atot3356 : totK PA10K2 A10K2.u3356 = [0, 0, 0, 1262415010001, 4035280826379, 3819352855737, 1007374471064, 62351816811, 0, 0] := by
  rw [show A10K2.u3356 = KTree.node A10K2.t3360 (nat_lit 56391411) (nat_lit 8037392376) (nat_lit 0) A10K2.t3361 from rfl, totK_node, tot3360, tot3361]
  decide +kernel

theorem arows3357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3357 = true := by
  rw [show A10K2.u3357 = KTree.node A10K2.t3362 (nat_lit 56419249) (nat_lit 9081975783) (nat_lit 0) A10K2.t3363 from rfl, allE_node, rows3362, irow3357, rows3363]
  all_goals rfl

theorem atot3357 : totK PA10K2 A10K2.u3357 = [0, 0, 0, 1086107851489, 4064465378620, 4180705159711, 988110401853, 34726567813, 0, 0] := by
  rw [show A10K2.u3357 = KTree.node A10K2.t3362 (nat_lit 56419249) (nat_lit 9081975783) (nat_lit 0) A10K2.t3363 from rfl, totK_node, tot3362, tot3363]
  decide +kernel

theorem arows3359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3359 = true := by
  rw [show A10K2.u3359 = KTree.node A10K2.t3364 (nat_lit 56437281) (nat_lit 7410956052) (nat_lit 0) A10K2.t3365 from rfl, allE_node, rows3364, irow3359, rows3365]
  all_goals rfl

theorem atot3359 : totK PA10K2 A10K2.u3359 = [0, 0, 846901670217, 3312692881518, 3857769746884, 1491086355484, 313013404649, 37674914273, 0, 0] := by
  rw [show A10K2.u3359 = KTree.node A10K2.t3364 (nat_lit 56437281) (nat_lit 7410956052) (nat_lit 0) A10K2.t3365 from rfl, totK_node, tot3364, tot3365]
  decide +kernel

theorem arows3360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3360 = true := by
  rw [show A10K2.u3360 = KTree.node A10K2.t3366 (nat_lit 56442034) (nat_lit 15078393574) (nat_lit 0) A10K2.t3367 from rfl, allE_node, rows3366, irow3360, rows3367]
  all_goals rfl

theorem atot3360 : totK PA10K2 A10K2.u3360 = [0, 0, 476659998554, 2137610531072, 3761613979485, 2679923193197, 576964461796, 31306924438, 0, 0] := by
  rw [show A10K2.u3360 = KTree.node A10K2.t3366 (nat_lit 56442034) (nat_lit 15078393574) (nat_lit 0) A10K2.t3367 from rfl, totK_node, tot3366, tot3367]
  decide +kernel

theorem arows3363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3363 = true := by
  rw [show A10K2.u3363 = KTree.node A10K2.t3368 (nat_lit 56449718) (nat_lit 11385878517) (nat_lit 0) A10K2.t3369 from rfl, allE_node, rows3368, irow3363, rows3369]
  all_goals rfl

theorem atot3363 : totK PA10K2 A10K2.u3363 = [0, 0, 575817692310, 2783493401129, 4141725493095, 1890908496198, 236721838107, 6239673734, 0, 0] := by
  rw [show A10K2.u3363 = KTree.node A10K2.t3368 (nat_lit 56449718) (nat_lit 11385878517) (nat_lit 0) A10K2.t3369 from rfl, totK_node, tot3368, tot3369]
  decide +kernel

theorem arows3364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3364 = true := by
  rw [show A10K2.u3364 = KTree.node A10K2.t3370 (nat_lit 56455713) (nat_lit 6646730762) (nat_lit 0) A10K2.t3371 from rfl, allE_node, rows3370, irow3364, rows3371]
  all_goals rfl

theorem atot3364 : totK PA10K2 A10K2.u3364 = [0, 0, 319364795913, 2100086222909, 4284401611434, 3043597870983, 510126058816, 6962742351, 0, 0] := by
  rw [show A10K2.u3364 = KTree.node A10K2.t3370 (nat_lit 56455713) (nat_lit 6646730762) (nat_lit 0) A10K2.t3371 from rfl, totK_node, tot3370, tot3371]
  decide +kernel

theorem arows3366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3366 = true := by
  rw [show A10K2.u3366 = KTree.node A10K2.t3372 (nat_lit 56469665) (nat_lit 6028055669) (nat_lit 0) A10K2.t3373 from rfl, allE_node, rows3372, irow3366, rows3373]
  all_goals rfl

theorem atot3366 : totK PA10K2 A10K2.u3366 = [0, 0, 0, 842044503153, 3335981113670, 4075873608284, 1475201207935, 95115636766, 0, 0] := by
  rw [show A10K2.u3366 = KTree.node A10K2.t3372 (nat_lit 56469665) (nat_lit 6028055669) (nat_lit 0) A10K2.t3373 from rfl, totK_node, tot3372, tot3373]
  decide +kernel

theorem arows3367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3367 = true := by
  rw [show A10K2.u3367 = KTree.node A10K2.t3374 (nat_lit 56475091) (nat_lit 10199451034) (nat_lit 0) A10K2.t3375 from rfl, allE_node, rows3374, irow3367, rows3375]
  all_goals rfl

theorem atot3367 : totK PA10K2 A10K2.u3367 = [0, 0, 0, 755048217192, 2954502428208, 3785481762928, 1806012488242, 275624836782, 7151180950, 0] := by
  rw [show A10K2.u3367 = KTree.node A10K2.t3374 (nat_lit 56475091) (nat_lit 10199451034) (nat_lit 0) A10K2.t3375 from rfl, totK_node, tot3374, tot3375]
  decide +kernel

theorem arows3371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3371 = true := by
  rw [show A10K2.u3371 = KTree.node A10K2.t3376 (nat_lit 56487308) (nat_lit 5582115243) (nat_lit 0) A10K2.t3377 from rfl, allE_node, rows3376, irow3371, rows3377]
  all_goals rfl

theorem atot3371 : totK PA10K2 A10K2.u3371 = [0, 0, 321728677231, 1728381171173, 3620782200178, 3394311182700, 1023790403173, 54848387600, 0, 0] := by
  rw [show A10K2.u3371 = KTree.node A10K2.t3376 (nat_lit 56487308) (nat_lit 5582115243) (nat_lit 0) A10K2.t3377 from rfl, totK_node, tot3376, tot3377]
  decide +kernel

theorem arows3372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3372 = true := by
  rw [show A10K2.u3372 = KTree.node A10K2.t3378 (nat_lit 56562211) (nat_lit 13652359) (nat_lit 0) A10K2.t3379 from rfl, allE_node, rows3378, irow3372, rows3379]
  all_goals rfl

theorem atot3372 : totK PA10K2 A10K2.u3372 = [0, 0, 605979537915, 2731028310437, 4186848167074, 2286307935834, 304518792474, 7685602490, 0, 0] := by
  rw [show A10K2.u3372 = KTree.node A10K2.t3378 (nat_lit 56562211) (nat_lit 13652359) (nat_lit 0) A10K2.t3379 from rfl, totK_node, tot3378, tot3379]
  decide +kernel

theorem arows3374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3374 = true := by
  rw [show A10K2.u3374 = KTree.node A10K2.t3380 (nat_lit 56569585) (nat_lit 5544975795) (nat_lit 0) A10K2.t3381 from rfl, allE_node, rows3380, irow3374, rows3381]
  all_goals rfl

theorem atot3374 : totK PA10K2 A10K2.u3374 = [0, 0, 482701838241, 2434743344533, 4060145955996, 2462135959991, 419183349851, 12219140272, 0, 0] := by
  rw [show A10K2.u3374 = KTree.node A10K2.t3380 (nat_lit 56569585) (nat_lit 5544975795) (nat_lit 0) A10K2.t3381 from rfl, totK_node, tot3380, tot3381]
  decide +kernel

theorem arows3375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3375 = true := by
  rw [show A10K2.u3375 = KTree.node A10K2.t3382 (nat_lit 56583410) (nat_lit 15042214456) (nat_lit 0) A10K2.t3383 from rfl, allE_node, rows3382, irow3375, rows3383]
  all_goals rfl

theorem atot3375 : totK PA10K2 A10K2.u3375 = [0, 0, 872810143373, 3391449565057, 4066400741569, 1536255165684, 118516280401, 0, 0, 0] := by
  rw [show A10K2.u3375 = KTree.node A10K2.t3382 (nat_lit 56583410) (nat_lit 15042214456) (nat_lit 0) A10K2.t3383 from rfl, totK_node, tot3382, tot3383]
  decide +kernel

theorem arows3378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3378 = true := by
  rw [show A10K2.u3378 = KTree.node A10K2.t3384 (nat_lit 56587953) (nat_lit 5138457624) (nat_lit 0) A10K2.t3385 from rfl, allE_node, rows3384, irow3378, rows3385]
  all_goals rfl

theorem atot3378 : totK PA10K2 A10K2.u3378 = [0, 0, 0, 1173931479993, 3916419699628, 3807147144995, 1009295666775, 62833682686, 0, 0] := by
  rw [show A10K2.u3378 = KTree.node A10K2.t3384 (nat_lit 56587953) (nat_lit 5138457624) (nat_lit 0) A10K2.t3385 from rfl, totK_node, tot3384, tot3385]
  decide +kernel

theorem arows3379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3379 = true := by
  rw [show A10K2.u3379 = KTree.node A10K2.t3386 (nat_lit 56594439) (nat_lit 13664898875) (nat_lit 0) A10K2.t3387 from rfl, allE_node, rows3386, irow3379, rows3387]
  all_goals rfl

theorem atot3379 : totK PA10K2 A10K2.u3379 = [0, 0, 0, 741875860127, 3363340808560, 4264034725974, 1620067330710, 130163390217, 0, 0] := by
  rw [show A10K2.u3379 = KTree.node A10K2.t3386 (nat_lit 56594439) (nat_lit 13664898875) (nat_lit 0) A10K2.t3387 from rfl, totK_node, tot3386, tot3387]
  decide +kernel

theorem arows3381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3381 = true := by
  rw [show A10K2.u3381 = KTree.node A10K2.t3388 (nat_lit 56603796) (nat_lit 11596874819) (nat_lit 0) A10K2.t3389 from rfl, allE_node, rows3388, irow3381, rows3389]
  all_goals rfl

theorem atot3381 : totK PA10K2 A10K2.u3381 = [0, 0, 0, 583937536180, 2770927038084, 4177704648640, 2163621371909, 261567554369, 6439430839, 0] := by
  rw [show A10K2.u3381 = KTree.node A10K2.t3388 (nat_lit 56603796) (nat_lit 11596874819) (nat_lit 0) A10K2.t3389 from rfl, totK_node, tot3388, tot3389]
  decide +kernel

theorem arows3382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3382 = true := by
  rw [show A10K2.u3382 = KTree.node A10K2.t3390 (nat_lit 56618042) (nat_lit 11821546759) (nat_lit 0) A10K2.t3391 from rfl, allE_node, rows3390, irow3382, rows3391]
  all_goals rfl

theorem atot3382 : totK PA10K2 A10K2.u3382 = [0, 0, 0, 761744941117, 3196044506357, 4163574659371, 1679804643378, 136276997300, 0, 0] := by
  rw [show A10K2.u3382 = KTree.node A10K2.t3390 (nat_lit 56618042) (nat_lit 11821546759) (nat_lit 0) A10K2.t3391 from rfl, totK_node, tot3390, tot3391]
  decide +kernel

theorem arows3388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3388 = true := by
  rw [show A10K2.u3388 = KTree.node A10K2.t3392 (nat_lit 56622811) (nat_lit 5822300001) (nat_lit 0) A10K2.t3393 from rfl, allE_node, rows3392, irow3388, rows3393]
  all_goals rfl

theorem atot3388 : totK PA10K2 A10K2.u3388 = [0, 0, 504401514522, 1612971754281, 2153910904043, 2542168150791, 2272778345991, 683054882366, 41875219570, 0] := by
  rw [show A10K2.u3388 = KTree.node A10K2.t3392 (nat_lit 56622811) (nat_lit 5822300001) (nat_lit 0) A10K2.t3393 from rfl, totK_node, tot3392, tot3393]
  decide +kernel

theorem arows3389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3389 = true := by
  rw [show A10K2.u3389 = KTree.node A10K2.t3394 (nat_lit 57226423) (nat_lit 14401140337) (nat_lit 0) A10K2.t3395 from rfl, allE_node, rows3394, irow3389, rows3395]
  all_goals rfl

theorem atot3389 : totK PA10K2 A10K2.u3389 = [0, 0, 368688490232, 2159173325046, 3995875495830, 2599764514886, 495744713585, 25734533292, 0, 0] := by
  rw [show A10K2.u3389 = KTree.node A10K2.t3394 (nat_lit 57226423) (nat_lit 14401140337) (nat_lit 0) A10K2.t3395 from rfl, totK_node, tot3394, tot3395]
  decide +kernel

theorem arows3391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3391 = true := by
  rw [show A10K2.u3391 = KTree.node A10K2.t3396 (nat_lit 57230805) (nat_lit 5287672699) (nat_lit 0) A10K2.t3397 from rfl, allE_node, rows3396, irow3391, rows3397]
  all_goals rfl

theorem atot3391 : totK PA10K2 A10K2.u3391 = [0, 0, 720231317471, 3048950504598, 3847721880601, 1530632545316, 192487056577, 6034215561, 0, 0] := by
  rw [show A10K2.u3391 = KTree.node A10K2.t3396 (nat_lit 57230805) (nat_lit 5287672699) (nat_lit 0) A10K2.t3397 from rfl, totK_node, tot3396, tot3397]
  decide +kernel

theorem arows3392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3392 = true := by
  rw [show A10K2.u3392 = KTree.node A10K2.t3398 (nat_lit 57237958) (nat_lit 15671917983) (nat_lit 0) A10K2.t3399 from rfl, allE_node, rows3398, irow3392, rows3399]
  all_goals rfl

theorem atot3392 : totK PA10K2 A10K2.u3392 = [0, 0, 733183447167, 2868348510789, 3949232966625, 1907530633761, 249756988416, 6354482628, 0, 0] := by
  rw [show A10K2.u3392 = KTree.node A10K2.t3398 (nat_lit 57237958) (nat_lit 15671917983) (nat_lit 0) A10K2.t3399 from rfl, totK_node, tot3398, tot3399]
  decide +kernel

theorem arows3395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3395 = true := by
  rw [show A10K2.u3395 = KTree.node A10K2.t3400 (nat_lit 57243092) (nat_lit 8574041929) (nat_lit 0) A10K2.t3401 from rfl, allE_node, rows3400, irow3395, rows3401]
  all_goals rfl

theorem atot3395 : totK PA10K2 A10K2.u3395 = [0, 0, 45770322325, 1419123371418, 4081578786651, 3553024970289, 884068762134, 47540011751, 0, 0] := by
  rw [show A10K2.u3395 = KTree.node A10K2.t3400 (nat_lit 57243092) (nat_lit 8574041929) (nat_lit 0) A10K2.t3401 from rfl, totK_node, tot3400, tot3401]
  decide +kernel

theorem arows3396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3396 = true := by
  rw [show A10K2.u3396 = KTree.node A10K2.t3402 (nat_lit 57256737) (nat_lit 8615151961) (nat_lit 0) A10K2.t3403 from rfl, allE_node, rows3402, irow3396, rows3403]
  all_goals rfl

theorem atot3396 : totK PA10K2 A10K2.u3396 = [0, 0, 0, 751804841142, 3248537393886, 4158596611495, 1457384667811, 101146013670, 0, 0] := by
  rw [show A10K2.u3396 = KTree.node A10K2.t3402 (nat_lit 57256737) (nat_lit 8615151961) (nat_lit 0) A10K2.t3403 from rfl, totK_node, tot3402, tot3403]
  decide +kernel

theorem arows3398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3398 = true := by
  rw [show A10K2.u3398 = KTree.node A10K2.t3404 (nat_lit 57261526) (nat_lit 15637030661) (nat_lit 0) A10K2.t3405 from rfl, allE_node, rows3404, irow3398, rows3405]
  all_goals rfl

theorem atot3398 : totK PA10K2 A10K2.u3398 = [0, 0, 0, 509026996888, 2278466462832, 3594455496383, 2334773260643, 535182075992, 31082886609, 0] := by
  rw [show A10K2.u3398 = KTree.node A10K2.t3404 (nat_lit 57261526) (nat_lit 15637030661) (nat_lit 0) A10K2.t3405 from rfl, totK_node, tot3404, tot3405]
  decide +kernel

theorem arows3399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3399 = true := by
  rw [show A10K2.u3399 = KTree.node A10K2.t3406 (nat_lit 57268273) (nat_lit 4043222812) (nat_lit 0) A10K2.t3407 from rfl, allE_node, rows3406, irow3399, rows3407]
  all_goals rfl

theorem atot3399 : totK PA10K2 A10K2.u3399 = [0, 0, 0, 681521680852, 2858842840934, 3860723198559, 1699499451547, 219342352943, 6121173289, 0] := by
  rw [show A10K2.u3399 = KTree.node A10K2.t3406 (nat_lit 57268273) (nat_lit 4043222812) (nat_lit 0) A10K2.t3407 from rfl, totK_node, tot3406, tot3407]
  decide +kernel

theorem arows3403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3403 = true := by
  rw [show A10K2.u3403 = KTree.node A10K2.t3408 (nat_lit 57274363) (nat_lit 6018884933) (nat_lit 0) A10K2.t3409 from rfl, allE_node, rows3408, irow3403, rows3409]
  all_goals rfl

theorem atot3403 : totK PA10K2 A10K2.u3403 = [0, 0, 424355675811, 2045585941291, 3435893795671, 2637907146409, 861192859629, 67630175297, 0, 0] := by
  rw [show A10K2.u3403 = KTree.node A10K2.t3408 (nat_lit 57274363) (nat_lit 6018884933) (nat_lit 0) A10K2.t3409 from rfl, totK_node, tot3408, tot3409]
  decide +kernel

theorem arows3404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3404 = true := by
  rw [show A10K2.u3404 = KTree.node A10K2.t3410 (nat_lit 57288595) (nat_lit 10671537095) (nat_lit 0) A10K2.t3411 from rfl, allE_node, rows3410, irow3404, rows3411]
  all_goals rfl

theorem atot3404 : totK PA10K2 A10K2.u3404 = [0, 0, 800683903397, 3132902514868, 3971389364343, 1612357044791, 159752263137, 5460492893, 0, 0] := by
  rw [show A10K2.u3404 = KTree.node A10K2.t3410 (nat_lit 57288595) (nat_lit 10671537095) (nat_lit 0) A10K2.t3411 from rfl, totK_node, tot3410, tot3411]
  decide +kernel

theorem arows3406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3406 = true := by
  rw [show A10K2.u3406 = KTree.node A10K2.t3412 (nat_lit 57293460) (nat_lit 12298234913) (nat_lit 0) A10K2.t3413 from rfl, allE_node, rows3412, irow3406, rows3413]
  all_goals rfl

theorem atot3406 : totK PA10K2 A10K2.u3406 = [0, 0, 359027376508, 1846658396594, 3702937732971, 2830523118971, 623605861083, 31768748853, 0, 0] := by
  rw [show A10K2.u3406 = KTree.node A10K2.t3412 (nat_lit 57293460) (nat_lit 12298234913) (nat_lit 0) A10K2.t3413 from rfl, totK_node, tot3412, tot3413]
  decide +kernel

theorem arows3407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3407 = true := by
  rw [show A10K2.u3407 = KTree.node A10K2.t3414 (nat_lit 57298950) (nat_lit 5297320161) (nat_lit 0) A10K2.t3415 from rfl, allE_node, rows3414, irow3407, rows3415]
  all_goals rfl

theorem atot3407 : totK PA10K2 A10K2.u3407 = [0, 0, 404069830576, 2524147535537, 4238196506425, 1993017779305, 169503960004, 0, 0, 0] := by
  rw [show A10K2.u3407 = KTree.node A10K2.t3414 (nat_lit 57298950) (nat_lit 5297320161) (nat_lit 0) A10K2.t3415 from rfl, totK_node, tot3414, tot3415]
  decide +kernel

theorem arows3410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3410 = true := by
  rw [show A10K2.u3410 = KTree.node A10K2.t3416 (nat_lit 57320685) (nat_lit 5884227124) (nat_lit 0) A10K2.t3417 from rfl, allE_node, rows3416, irow3410, rows3417]
  all_goals rfl

theorem atot3410 : totK PA10K2 A10K2.u3410 = [0, 0, 0, 1002612297383, 3672514958545, 3724466552746, 882028113512, 44211413894, 0, 0] := by
  rw [show A10K2.u3410 = KTree.node A10K2.t3416 (nat_lit 57320685) (nat_lit 5884227124) (nat_lit 0) A10K2.t3417 from rfl, totK_node, tot3416, tot3417]
  decide +kernel

theorem arows3411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3411 = true := by
  rw [show A10K2.u3411 = KTree.node A10K2.t3418 (nat_lit 57328926) (nat_lit 10349621055) (nat_lit 0) A10K2.t3419 from rfl, allE_node, rows3418, irow3411, rows3419]
  all_goals rfl

theorem atot3411 : totK PA10K2 A10K2.u3411 = [0, 0, 0, 986973602882, 3648270683989, 3796919864399, 917671405720, 50537752072, 0, 0] := by
  rw [show A10K2.u3411 = KTree.node A10K2.t3418 (nat_lit 57328926) (nat_lit 10349621055) (nat_lit 0) A10K2.t3419 from rfl, totK_node, tot3418, tot3419]
  decide +kernel

theorem arows3413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3413 = true := by
  rw [show A10K2.u3413 = KTree.node A10K2.t3420 (nat_lit 57344058) (nat_lit 7858508227) (nat_lit 8) A10K2.t3421 from rfl, allE_node, rows3420, irow3413, rows3421]
  all_goals rfl

theorem atot3413 : totK PA10K2 A10K2.u3413 = [0, 0, 476533825286, 1850058798162, 2917941770939, 2886951041758, 1366491044421, 208241182707, 6354482628, 0] := by
  rw [show A10K2.u3413 = KTree.node A10K2.t3420 (nat_lit 57344058) (nat_lit 7858508227) (nat_lit 8) A10K2.t3421 from rfl, totK_node, tot3420, tot3421]
  decide +kernel

theorem arows3414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3414 = true := by
  rw [show A10K2.u3414 = KTree.node A10K2.t3422 (nat_lit 57354916) (nat_lit 13430371079) (nat_lit 0) A10K2.t3423 from rfl, allE_node, rows3422, irow3414, rows3423]
  all_goals rfl

theorem atot3414 : totK PA10K2 A10K2.u3414 = [0, 0, 814218265826, 3269144945482, 4136846110608, 1612656187449, 141758241596, 0, 0, 0] := by
  rw [show A10K2.u3414 = KTree.node A10K2.t3422 (nat_lit 57354916) (nat_lit 13430371079) (nat_lit 0) A10K2.t3423 from rfl, totK_node, tot3422, tot3423]
  decide +kernel

theorem arows3419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3419 = true := by
  rw [show A10K2.u3419 = KTree.node A10K2.t3424 (nat_lit 57359771) (nat_lit 9617838488) (nat_lit 0) A10K2.t3425 from rfl, allE_node, rows3424, irow3419, rows3425]
  all_goals rfl

theorem atot3419 : totK PA10K2 A10K2.u3419 = [0, 0, 513159322381, 2338556122401, 3880489970907, 2618738439937, 575029263894, 31747192500, 0, 0] := by
  rw [show A10K2.u3419 = KTree.node A10K2.t3424 (nat_lit 57359771) (nat_lit 9617838488) (nat_lit 0) A10K2.t3425 from rfl, totK_node, tot3424, tot3425]
  decide +kernel

theorem arows3420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3420 = true := by
  rw [show A10K2.u3420 = KTree.node A10K2.t3426 (nat_lit 57373178) (nat_lit 12455262960) (nat_lit 0) A10K2.t3427 from rfl, allE_node, rows3426, irow3420, rows3427]
  all_goals rfl

theorem atot3420 : totK PA10K2 A10K2.u3420 = [0, 0, 321746006324, 2115297007353, 4250945868832, 2895604154439, 472584219962, 6962742351, 0, 0] := by
  rw [show A10K2.u3420 = KTree.node A10K2.t3426 (nat_lit 57373178) (nat_lit 12455262960) (nat_lit 0) A10K2.t3427 from rfl, totK_node, tot3426, tot3427]
  decide +kernel

theorem arows3422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3422 = true := by
  rw [show A10K2.u3422 = KTree.node A10K2.t3428 (nat_lit 57380800) (nat_lit 13244172656) (nat_lit 32) A10K2.t3429 from rfl, allE_node, rows3428, irow3422, rows3429]
  all_goals rfl

theorem atot3422 : totK PA10K2 A10K2.u3422 = [0, 0, 0, 989550916093, 3683746992000, 3962517074363, 1351265394798, 99217723757, 0, 0] := by
  rw [show A10K2.u3422 = KTree.node A10K2.t3428 (nat_lit 57380800) (nat_lit 13244172656) (nat_lit 32) A10K2.t3429 from rfl, totK_node, tot3428, tot3429]
  decide +kernel

theorem arows3423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3423 = true := by
  rw [show A10K2.u3423 = KTree.node A10K2.t3430 (nat_lit 57390556) (nat_lit 5253446310) (nat_lit 0) A10K2.t3431 from rfl, allE_node, rows3430, irow3423, rows3431]
  all_goals rfl

theorem atot3423 : totK PA10K2 A10K2.u3423 = [0, 0, 0, 523358824727, 2605442837606, 4182970809463, 2295242861746, 317926310263, 7047025452, 0] := by
  rw [show A10K2.u3423 = KTree.node A10K2.t3430 (nat_lit 57390556) (nat_lit 5253446310) (nat_lit 0) A10K2.t3431 from rfl, totK_node, tot3430, tot3431]
  decide +kernel

theorem arows3426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3426 = true := by
  rw [show A10K2.u3426 = KTree.node A10K2.t3432 (nat_lit 57404977) (nat_lit 9621325078) (nat_lit 0) A10K2.t3433 from rfl, allE_node, rows3432, irow3426, rows3433]
  all_goals rfl

theorem atot3426 : totK PA10K2 A10K2.u3426 = [0, 0, 0, 610879770813, 2879560681976, 4198914898486, 2025709922198, 259700715627, 6157148557, 0] := by
  rw [show A10K2.u3426 = KTree.node A10K2.t3432 (nat_lit 57404977) (nat_lit 9621325078) (nat_lit 0) A10K2.t3433 from rfl, totK_node, tot3432, tot3433]
  decide +kernel

theorem arows3427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3427 = true := by
  rw [show A10K2.u3427 = KTree.node A10K2.t3434 (nat_lit 57485074) (nat_lit 15163172844) (nat_lit 0) A10K2.t3435 from rfl, allE_node, rows3434, irow3427, rows3435]
  all_goals rfl

theorem atot3427 : totK PA10K2 A10K2.u3427 = [0, 0, 0, 868128639955, 3164522803062, 3673636648304, 1671235188532, 369484681852, 29591534826, 0] := by
  rw [show A10K2.u3427 = KTree.node A10K2.t3434 (nat_lit 57485074) (nat_lit 15163172844) (nat_lit 0) A10K2.t3435 from rfl, totK_node, tot3434, tot3435]
  decide +kernel

theorem arows3429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3429 = true := by
  rw [show A10K2.u3429 = KTree.node A10K2.t3436 (nat_lit 57489591) (nat_lit 12775772262) (nat_lit 0) A10K2.t3437 from rfl, allE_node, rows3436, irow3429, rows3437]
  all_goals rfl

theorem atot3429 : totK PA10K2 A10K2.u3429 = [0, 0, 0, 188424944321, 1680992080379, 3959183038617, 2985801252619, 616885675172, 31768748853, 0] := by
  rw [show A10K2.u3429 = KTree.node A10K2.t3436 (nat_lit 57489591) (nat_lit 12775772262) (nat_lit 0) A10K2.t3437 from rfl, totK_node, tot3436, tot3437]
  decide +kernel

theorem arows3430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3430 = true := by
  rw [show A10K2.u3430 = KTree.node A10K2.t3438 (nat_lit 57494198) (nat_lit 11798772447) (nat_lit 0) A10K2.t3439 from rfl, allE_node, rows3438, irow3430, rows3439]
  all_goals rfl

theorem atot3430 : totK PA10K2 A10K2.u3430 = [0, 0, 0, 522643722622, 2726914222863, 4134882095207, 1717525935269, 137294302232, 0, 0] := by
  rw [show A10K2.u3430 = KTree.node A10K2.t3438 (nat_lit 57494198) (nat_lit 11798772447) (nat_lit 0) A10K2.t3439 from rfl, totK_node, tot3438, tot3439]
  decide +kernel

theorem arows3434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3434 = true := by
  rw [show A10K2.u3434 = KTree.node A10K2.t3440 (nat_lit 57502792) (nat_lit 7931354501) (nat_lit 2) A10K2.t3441 from rfl, allE_node, rows3440, irow3434, rows3441]
  all_goals rfl

theorem atot3434 : totK PA10K2 A10K2.u3434 = [0, 0, 0, 777446694424, 3194213639524, 4095204593719, 1717646681037, 217325546505, 6239673734, 0] := by
  rw [show A10K2.u3434 = KTree.node A10K2.t3440 (nat_lit 57502792) (nat_lit 7931354501) (nat_lit 2) A10K2.t3441 from rfl, totK_node, tot3440, tot3441]
  decide +kernel

theorem arows3435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3435 = true := by
  rw [show A10K2.u3435 = KTree.node A10K2.t3442 (nat_lit 57517357) (nat_lit 6572469376) (nat_lit 0) A10K2.t3443 from rfl, allE_node, rows3442, irow3435, rows3443]
  all_goals rfl

theorem atot3435 : totK PA10K2 A10K2.u3435 = [0, 0, 0, 0, 953520875997, 3637257134861, 3882937377147, 1082556119490, 68110430736, 0] := by
  rw [show A10K2.u3435 = KTree.node A10K2.t3442 (nat_lit 57517357) (nat_lit 6572469376) (nat_lit 0) A10K2.t3443 from rfl, totK_node, tot3442, tot3443]
  decide +kernel

theorem arows3437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3437 = true := by
  rw [show A10K2.u3437 = KTree.node A10K2.t3444 (nat_lit 57521954) (nat_lit 13522820991) (nat_lit 0) A10K2.t3445 from rfl, allE_node, rows3444, irow3437, rows3445]
  all_goals rfl

theorem atot3437 : totK PA10K2 A10K2.u3437 = [0, 0, 0, 0, 340989056161, 2075930573435, 3791241757089, 2566190384270, 553512620276, 31018567651] := by
  rw [show A10K2.u3437 = KTree.node A10K2.t3444 (nat_lit 57521954) (nat_lit 13522820991) (nat_lit 0) A10K2.t3445 from rfl, totK_node, tot3444, tot3445]
  decide +kernel

theorem arows3438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3438 = true := by
  rw [show A10K2.u3438 = KTree.node A10K2.t3446 (nat_lit 57526572) (nat_lit 13552313479) (nat_lit 0) A10K2.t3447 from rfl, allE_node, rows3446, irow3438, rows3447]
  all_goals rfl

theorem atot3438 : totK PA10K2 A10K2.u3438 = [0, 0, 0, 0, 567298132800, 2896077178010, 4055951621870, 1448118558242, 102662061658, 0] := by
  rw [show A10K2.u3438 = KTree.node A10K2.t3446 (nat_lit 57526572) (nat_lit 13552313479) (nat_lit 0) A10K2.t3447 from rfl, totK_node, tot3446, tot3447]
  decide +kernel

theorem arows3441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3441 = true := by
  rw [show A10K2.u3441 = KTree.node A10K2.t3448 (nat_lit 57535698) (nat_lit 15415996847) (nat_lit 0) A10K2.t3449 from rfl, allE_node, rows3448, irow3441, rows3449]
  all_goals rfl

theorem atot3441 : totK PA10K2 A10K2.u3441 = [0, 0, 0, 424355675811, 1893294052734, 3329133337066, 2687106054874, 1019076830084, 165821970724, 5685526223] := by
  rw [show A10K2.u3441 = KTree.node A10K2.t3448 (nat_lit 57535698) (nat_lit 15415996847) (nat_lit 0) A10K2.t3449 from rfl, totK_node, tot3448, tot3449]
  decide +kernel

theorem arows3442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3442 = true := by
  rw [show A10K2.u3442 = KTree.node A10K2.t3450 (nat_lit 57550103) (nat_lit 10267685640) (nat_lit 0) A10K2.t3451 from rfl, allE_node, rows3450, irow3442, rows3451]
  all_goals rfl

theorem atot3442 : totK PA10K2 A10K2.u3442 = [0, 0, 0, 623320586928, 2954737805156, 4035855611467, 1532166684956, 146987192802, 5460492893, 0] := by
  rw [show A10K2.u3442 = KTree.node A10K2.t3450 (nat_lit 57550103) (nat_lit 10267685640) (nat_lit 0) A10K2.t3451 from rfl, totK_node, tot3450, tot3451]
  decide +kernel

theorem arows3444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3444 = true := by
  rw [show A10K2.u3444 = KTree.node A10K2.t3452 (nat_lit 57554843) (nat_lit 9633256820) (nat_lit 0) A10K2.t3453 from rfl, allE_node, rows3452, irow3444, rows3453]
  all_goals rfl

theorem atot3444 : totK PA10K2 A10K2.u3444 = [0, 0, 0, 369656152089, 2039887606591, 3823029945085, 2747628459463, 594568069791, 31768748853, 0] := by
  rw [show A10K2.u3444 = KTree.node A10K2.t3452 (nat_lit 57554843) (nat_lit 9633256820) (nat_lit 0) A10K2.t3453 from rfl, totK_node, tot3452, tot3453]
  decide +kernel

theorem arows3445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3445 = true := by
  rw [show A10K2.u3445 = KTree.node A10K2.t3454 (nat_lit 57559274) (nat_lit 12348202454) (nat_lit 0) A10K2.t3455 from rfl, allE_node, rows3454, irow3445, rows3455]
  all_goals rfl

theorem atot3445 : totK PA10K2 A10K2.u3445 = [0, 0, 0, 577254094124, 2889769704715, 4123506701320, 1503508335034, 100342502452, 0, 0] := by
  rw [show A10K2.u3445 = KTree.node A10K2.t3454 (nat_lit 57559274) (nat_lit 12348202454) (nat_lit 0) A10K2.t3455 from rfl, totK_node, tot3454, tot3455]
  decide +kernel

theorem arows3452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3452 = true := by
  rw [show A10K2.u3452 = KTree.node A10K2.t3456 (nat_lit 57576274) (nat_lit 11986254314) (nat_lit 0) A10K2.t3457 from rfl, allE_node, rows3456, irow3452, rows3457]
  all_goals rfl

theorem atot3452 : totK PA10K2 A10K2.u3452 = [0, 0, 0, 0, 1170082204899, 3959736035890, 3367833380314, 709223408490, 38593611784, 0] := by
  rw [show A10K2.u3452 = KTree.node A10K2.t3456 (nat_lit 57576274) (nat_lit 11986254314) (nat_lit 0) A10K2.t3457 from rfl, totK_node, tot3456, tot3457]
  decide +kernel

theorem arows3453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3453 = true := by
  rw [show A10K2.u3453 = KTree.node A10K2.t3458 (nat_lit 57591031) (nat_lit 11558653060) (nat_lit 0) A10K2.t3459 from rfl, allE_node, rows3458, irow3453, rows3459]
  all_goals rfl

theorem atot3453 : totK PA10K2 A10K2.u3453 = [0, 0, 0, 0, 982922240928, 3699479720294, 3755322858089, 919160336497, 50422943179, 0] := by
  rw [show A10K2.u3453 = KTree.node A10K2.t3458 (nat_lit 57591031) (nat_lit 11558653060) (nat_lit 0) A10K2.t3459 from rfl, totK_node, tot3458, tot3459]
  decide +kernel

theorem arows3455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3455 = true := by
  rw [show A10K2.u3455 = KTree.node A10K2.t3460 (nat_lit 57606593) (nat_lit 8634505745) (nat_lit 32) A10K2.t3461 from rfl, allE_node, rows3460, irow3455, rows3461]
  all_goals rfl

theorem atot3455 : totK PA10K2 A10K2.u3455 = [0, 0, 0, 786792495819, 2410423971292, 2676898415717, 2405970413134, 1158617762562, 187919439061, 5982052406] := by
  rw [show A10K2.u3455 = KTree.node A10K2.t3460 (nat_lit 57606593) (nat_lit 8634505745) (nat_lit 32) A10K2.t3461 from rfl, totK_node, tot3460, tot3461]
  decide +kernel

theorem arows3456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3456 = true := by
  rw [show A10K2.u3456 = KTree.node A10K2.t3462 (nat_lit 57618140) (nat_lit 7607656934) (nat_lit 0) A10K2.t3463 from rfl, allE_node, rows3462, irow3456, rows3463]
  all_goals rfl

theorem atot3456 : totK PA10K2 A10K2.u3456 = [0, 0, 0, 500856004971, 2587955365994, 4226516103591, 2182739768860, 340625540229, 20328650499, 0] := by
  rw [show A10K2.u3456 = KTree.node A10K2.t3462 (nat_lit 57618140) (nat_lit 7607656934) (nat_lit 0) A10K2.t3463 from rfl, totK_node, tot3462, tot3463]
  decide +kernel

theorem arows3459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3459 = true := by
  rw [show A10K2.u3459 = KTree.node A10K2.t3464 (nat_lit 57632499) (nat_lit 8437989451) (nat_lit 0) A10K2.t3465 from rfl, allE_node, rows3464, irow3459, rows3465]
  all_goals rfl

theorem atot3459 : totK PA10K2 A10K2.u3459 = [0, 0, 0, 833980310658, 3489730451827, 4201300420213, 1486376992281, 121652730080, 0, 0] := by
  rw [show A10K2.u3459 = KTree.node A10K2.t3464 (nat_lit 57632499) (nat_lit 8437989451) (nat_lit 0) A10K2.t3465 from rfl, totK_node, tot3464, tot3465]
  decide +kernel

theorem arows3460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3460 = true := by
  rw [show A10K2.u3460 = KTree.node A10K2.t3466 (nat_lit 57638870) (nat_lit 15601130921) (nat_lit 0) A10K2.t3467 from rfl, allE_node, rows3466, irow3460, rows3467]
  all_goals rfl

theorem atot3460 : totK PA10K2 A10K2.u3460 = [0, 0, 559138620308, 1904291344300, 2297760652959, 2464795437169, 2059722754649, 556815850769, 36702257158, 0] := by
  rw [show A10K2.u3460 = KTree.node A10K2.t3466 (nat_lit 57638870) (nat_lit 15601130921) (nat_lit 0) A10K2.t3467 from rfl, totK_node, tot3466, tot3467]
  decide +kernel

theorem arows3462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3462 = true := by
  rw [show A10K2.u3462 = KTree.node A10K2.t3468 (nat_lit 57688137) (nat_lit 9593038955) (nat_lit 0) A10K2.t3469 from rfl, allE_node, rows3468, irow3462, rows3469]
  all_goals rfl

theorem atot3462 : totK PA10K2 A10K2.u3462 = [0, 0, 588437042121, 2627894853886, 4001094895666, 1926204409127, 246411694656, 5460492893, 0, 0] := by
  rw [show A10K2.u3462 = KTree.node A10K2.t3468 (nat_lit 57688137) (nat_lit 9593038955) (nat_lit 0) A10K2.t3469 from rfl, totK_node, tot3468, tot3469]
  decide +kernel

theorem arows3463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3463 = true := by
  rw [show A10K2.u3463 = KTree.node A10K2.t3470 (nat_lit 57694321) (nat_lit 7386188660) (nat_lit 0) A10K2.t3471 from rfl, allE_node, rows3470, irow3463, rows3471]
  all_goals rfl

theorem atot3463 : totK PA10K2 A10K2.u3463 = [0, 0, 136853044638, 1865070255494, 4270426538037, 2724885827728, 439150916688, 11745936641, 0, 0] := by
  rw [show A10K2.u3463 = KTree.node A10K2.t3470 (nat_lit 57694321) (nat_lit 7386188660) (nat_lit 0) A10K2.t3471 from rfl, totK_node, tot3470, tot3471]
  decide +kernel

theorem arows3467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3467 = true := by
  rw [show A10K2.u3467 = KTree.node A10K2.t3472 (nat_lit 57722112) (nat_lit 13377590316) (nat_lit 0) A10K2.t3473 from rfl, allE_node, rows3472, irow3467, rows3473]
  all_goals rfl

theorem atot3467 : totK PA10K2 A10K2.u3467 = [0, 0, 0, 901514478263, 3667556415063, 3906301614804, 846671115887, 28646685318, 0, 0] := by
  rw [show A10K2.u3467 = KTree.node A10K2.t3472 (nat_lit 57722112) (nat_lit 13377590316) (nat_lit 0) A10K2.t3473 from rfl, totK_node, tot3472, tot3473]
  decide +kernel

theorem arows3468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3468 = true := by
  rw [show A10K2.u3468 = KTree.node A10K2.t3474 (nat_lit 57746907) (nat_lit 6870203376) (nat_lit 0) A10K2.t3475 from rfl, allE_node, rows3474, irow3468, rows3475]
  all_goals rfl

theorem atot3468 : totK PA10K2 A10K2.u3468 = [0, 0, 756252033968, 2556357281367, 2975564053882, 2107995237143, 955573634564, 132126606934, 5546304973, 0] := by
  rw [show A10K2.u3468 = KTree.node A10K2.t3474 (nat_lit 57746907) (nat_lit 6870203376) (nat_lit 0) A10K2.t3475 from rfl, totK_node, tot3474, tot3475]
  decide +kernel

theorem arows3470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3470 = true := by
  rw [show A10K2.u3470 = KTree.node A10K2.t3476 (nat_lit 57751473) (nat_lit 5070348083) (nat_lit 0) A10K2.t3477 from rfl, allE_node, rows3476, irow3470, rows3477]
  all_goals rfl

theorem atot3470 : totK PA10K2 A10K2.u3470 = [0, 0, 260440405277, 1812375531868, 3893185629256, 2966834666810, 622109660397, 31768748853, 0, 0] := by
  rw [show A10K2.u3470 = KTree.node A10K2.t3476 (nat_lit 57751473) (nat_lit 5070348083) (nat_lit 0) A10K2.t3477 from rfl, totK_node, tot3476, tot3477]
  decide +kernel

theorem arows3471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3471 = true := by
  rw [show A10K2.u3471 = KTree.node A10K2.t3478 (nat_lit 57755890) (nat_lit 14113540732) (nat_lit 0) A10K2.t3479 from rfl, allE_node, rows3478, irow3471, rows3479]
  all_goals rfl

theorem atot3471 : totK PA10K2 A10K2.u3471 = [0, 0, 583381828075, 2947417237691, 4262293745555, 1596698555973, 100554280525, 0, 0, 0] := by
  rw [show A10K2.u3471 = KTree.node A10K2.t3478 (nat_lit 57755890) (nat_lit 14113540732) (nat_lit 0) A10K2.t3479 from rfl, totK_node, tot3478, tot3479]
  decide +kernel

theorem arows3474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3474 = true := by
  rw [show A10K2.u3474 = KTree.node A10K2.t3480 (nat_lit 57764926) (nat_lit 16101479194) (nat_lit 0) A10K2.t3481 from rfl, allE_node, rows3480, irow3474, rows3481]
  all_goals rfl

theorem atot3474 : totK PA10K2 A10K2.u3474 = [0, 0, 588004983511, 2534305074854, 3958165548608, 2372615331951, 427154428127, 13317224979, 0, 0] := by
  rw [show A10K2.u3474 = KTree.node A10K2.t3480 (nat_lit 57764926) (nat_lit 16101479194) (nat_lit 0) A10K2.t3481 from rfl, totK_node, tot3480, tot3481]
  decide +kernel

theorem arows3475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3475 = true := by
  rw [show A10K2.u3475 = KTree.node A10K2.t3482 (nat_lit 57779877) (nat_lit 6930083950) (nat_lit 0) A10K2.t3483 from rfl, allE_node, rows3482, irow3475, rows3483]
  all_goals rfl

theorem atot3475 : totK PA10K2 A10K2.u3475 = [0, 0, 0, 1126554822484, 3876136515806, 3744217467418, 979681351951, 62263047470, 0, 0] := by
  rw [show A10K2.u3475 = KTree.node A10K2.t3482 (nat_lit 57779877) (nat_lit 6930083950) (nat_lit 0) A10K2.t3483 from rfl, totK_node, tot3482, tot3483]
  decide +kernel

theorem arows3477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3477 = true := by
  rw [show A10K2.u3477 = KTree.node A10K2.t3484 (nat_lit 57784480) (nat_lit 7557987868) (nat_lit 0) A10K2.t3485 from rfl, allE_node, rows3484, irow3477, rows3485]
  all_goals rfl

theorem atot3477 : totK PA10K2 A10K2.u3477 = [0, 0, 0, 219333510258, 1818279455211, 4055156964459, 2763825248430, 572047556973, 31082886609, 0] := by
  rw [show A10K2.u3477 = KTree.node A10K2.t3484 (nat_lit 57784480) (nat_lit 7557987868) (nat_lit 0) A10K2.t3485 from rfl, totK_node, tot3484, tot3485]
  decide +kernel

theorem arows3478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3478 = true := by
  rw [show A10K2.u3478 = KTree.node A10K2.t3486 (nat_lit 57789101) (nat_lit 6513875158) (nat_lit 0) A10K2.t3487 from rfl, allE_node, rows3486, irow3478, rows3487]
  all_goals rfl

theorem atot3478 : totK PA10K2 A10K2.u3478 = [0, 0, 0, 540883153407, 2814951930930, 4219437897728, 1667233761928, 121944926012, 0, 0] := by
  rw [show A10K2.u3478 = KTree.node A10K2.t3486 (nat_lit 57789101) (nat_lit 6513875158) (nat_lit 0) A10K2.t3487 from rfl, totK_node, tot3486, tot3487]
  decide +kernel

theorem arows3483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3483 = true := by
  rw [show A10K2.u3483 = KTree.node A10K2.t3488 (nat_lit 57798101) (nat_lit 3653085808) (nat_lit 0) A10K2.t3489 from rfl, allE_node, rows3488, irow3483, rows3489]
  all_goals rfl

theorem atot3483 : totK PA10K2 A10K2.u3483 = [0, 0, 409534657359, 1904479971345, 3328386385555, 2774365693542, 1105652222012, 180673546715, 6121173289, 0] := by
  rw [show A10K2.u3483 = KTree.node A10K2.t3488 (nat_lit 57798101) (nat_lit 3653085808) (nat_lit 0) A10K2.t3489 from rfl, totK_node, tot3488, tot3489]
  decide +kernel

theorem arows3484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3484 = true := by
  rw [show A10K2.u3484 = KTree.node A10K2.t3490 (nat_lit 57809008) (nat_lit 14427180537) (nat_lit 0) A10K2.t3491 from rfl, allE_node, rows3490, irow3484, rows3491]
  all_goals rfl

theorem atot3484 : totK PA10K2 A10K2.u3484 = [0, 0, 472903397961, 2383107075445, 4003445467894, 2153303285380, 323641708425, 10760911071, 0, 0] := by
  rw [show A10K2.u3484 = KTree.node A10K2.t3490 (nat_lit 57809008) (nat_lit 14427180537) (nat_lit 0) A10K2.t3491 from rfl, totK_node, tot3490, tot3491]
  decide +kernel

theorem arows3486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3486 = true := by
  rw [show A10K2.u3486 = KTree.node A10K2.t3492 (nat_lit 57815039) (nat_lit 12065270725) (nat_lit 2) A10K2.t3493 from rfl, allE_node, rows3492, irow3486, rows3493]
  all_goals rfl

theorem atot3486 : totK PA10K2 A10K2.u3486 = [0, 0, 467365254010, 2371217562509, 3970769126896, 2411440236218, 456653283164, 25734533292, 0, 0] := by
  rw [show A10K2.u3486 = KTree.node A10K2.t3492 (nat_lit 57815039) (nat_lit 12065270725) (nat_lit 2) A10K2.t3493 from rfl, totK_node, tot3492, tot3493]
  decide +kernel

theorem arows3487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3487 = true := by
  rw [show A10K2.u3487 = KTree.node A10K2.t3494 (nat_lit 57820421) (nat_lit 7008081117) (nat_lit 0) A10K2.t3495 from rfl, allE_node, rows3494, irow3487, rows3495]
  all_goals rfl

theorem atot3487 : totK PA10K2 A10K2.u3487 = [0, 0, 822103226267, 3165739623213, 3724658368204, 1490111778073, 207413772960, 6034215561, 0, 0] := by
  rw [show A10K2.u3487 = KTree.node A10K2.t3494 (nat_lit 57820421) (nat_lit 7008081117) (nat_lit 0) A10K2.t3495 from rfl, totK_node, tot3494, tot3495]
  decide +kernel

theorem arows3490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3490 = true := by
  rw [show A10K2.u3490 = KTree.node A10K2.t3496 (nat_lit 57825943) (nat_lit 8220097271) (nat_lit 0) A10K2.t3497 from rfl, allE_node, rows3496, irow3490, rows3497]
  all_goals rfl

theorem atot3490 : totK PA10K2 A10K2.u3490 = [0, 0, 0, 1333176001468, 4165725944308, 3212775893164, 510239472603, 11740475125, 0, 0] := by
  rw [show A10K2.u3490 = KTree.node A10K2.t3496 (nat_lit 57825943) (nat_lit 8220097271) (nat_lit 0) A10K2.t3497 from rfl, totK_node, tot3496, tot3497]
  decide +kernel

theorem arows3491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3491 = true := by
  rw [show A10K2.u3491 = KTree.node A10K2.t3498 (nat_lit 57845971) (nat_lit 10798587928) (nat_lit 0) A10K2.t3499 from rfl, allE_node, rows3498, irow3491, rows3499]
  all_goals rfl

theorem atot3491 : totK PA10K2 A10K2.u3491 = [0, 0, 0, 1068063569998, 3776239365077, 3743294611994, 937035535009, 45698881016, 0, 0] := by
  rw [show A10K2.u3491 = KTree.node A10K2.t3498 (nat_lit 57845971) (nat_lit 10798587928) (nat_lit 0) A10K2.t3499 from rfl, totK_node, tot3498, tot3499]
  decide +kernel

theorem arows3493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3493 = true := by
  rw [show A10K2.u3493 = KTree.node A10K2.t3500 (nat_lit 57854178) (nat_lit 13673862252) (nat_lit 0) A10K2.t3501 from rfl, allE_node, rows3500, irow3493, rows3501]
  all_goals rfl

theorem atot3493 : totK PA10K2 A10K2.u3493 = [0, 0, 0, 578916574311, 2984874493791, 4200124428955, 1367658773485, 91722484059, 0, 0] := by
  rw [show A10K2.u3493 = KTree.node A10K2.t3500 (nat_lit 57854178) (nat_lit 13673862252) (nat_lit 0) A10K2.t3501 from rfl, totK_node, tot3500, tot3501]
  decide +kernel

theorem arows3494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3494 = true := by
  rw [show A10K2.u3494 = KTree.node A10K2.t3502 (nat_lit 57935906) (nat_lit 8147872920) (nat_lit 0) A10K2.t3503 from rfl, allE_node, rows3502, irow3494, rows3503]
  all_goals rfl

theorem atot3494 : totK PA10K2 A10K2.u3494 = [0, 0, 0, 876123720204, 3157054731701, 3716430223259, 1390435152702, 201888880277, 6354482628, 0] := by
  rw [show A10K2.u3494 = KTree.node A10K2.t3502 (nat_lit 57935906) (nat_lit 8147872920) (nat_lit 0) A10K2.t3503 from rfl, totK_node, tot3502, tot3503]
  decide +kernel

theorem arows3498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3498 = true := by
  rw [show A10K2.u3498 = KTree.node A10K2.t3504 (nat_lit 57954372) (nat_lit 11552108224) (nat_lit 0) A10K2.t3505 from rfl, allE_node, rows3504, irow3498, rows3505]
  all_goals rfl

theorem atot3498 : totK PA10K2 A10K2.u3498 = [0, 0, 0, 536866902183, 2678626380812, 4124318033561, 1813721418396, 188246362538, 6354482628, 0] := by
  rw [show A10K2.u3498 = KTree.node A10K2.t3504 (nat_lit 57954372) (nat_lit 11552108224) (nat_lit 0) A10K2.t3505 from rfl, totK_node, tot3504, tot3505]
  decide +kernel

theorem arows3499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3499 = true := by
  rw [show A10K2.u3499 = KTree.node A10K2.t3506 (nat_lit 58010438) (nat_lit 3530110109) (nat_lit 0) A10K2.t3507 from rfl, allE_node, rows3506, irow3499, rows3507]
  all_goals rfl

theorem atot3499 : totK PA10K2 A10K2.u3499 = [0, 0, 0, 722042254931, 3086150533564, 4094315930952, 1643836427373, 142139706818, 0, 0] := by
  rw [show A10K2.u3499 = KTree.node A10K2.t3506 (nat_lit 58010438) (nat_lit 3530110109) (nat_lit 0) A10K2.t3507 from rfl, totK_node, tot3506, tot3507]
  decide +kernel

theorem arows3501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3501 = true := by
  rw [show A10K2.u3501 = KTree.node A10K2.t3508 (nat_lit 58015780) (nat_lit 13324647755) (nat_lit 0) A10K2.t3509 from rfl, allE_node, rows3508, irow3501, rows3509]
  all_goals rfl

theorem atot3501 : totK PA10K2 A10K2.u3501 = [0, 0, 0, 548115172891, 2367649978803, 3674291580124, 2274079795935, 499378824312, 31452573850, 0] := by
  rw [show A10K2.u3501 = KTree.node A10K2.t3508 (nat_lit 58015780) (nat_lit 13324647755) (nat_lit 0) A10K2.t3509 from rfl, totK_node, tot3508, tot3509]
  decide +kernel

theorem arows3502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3502 = true := by
  rw [show A10K2.u3502 = KTree.node A10K2.t3510 (nat_lit 58021900) (nat_lit 11759478708) (nat_lit 0) A10K2.t3511 from rfl, allE_node, rows3510, irow3502, rows3511]
  all_goals rfl

theorem atot3502 : totK PA10K2 A10K2.u3502 = [0, 0, 0, 508841205694, 2608453061193, 4090198999863, 1989981944054, 255707925710, 6354482628, 0] := by
  rw [show A10K2.u3502 = KTree.node A10K2.t3510 (nat_lit 58021900) (nat_lit 11759478708) (nat_lit 0) A10K2.t3511 from rfl, totK_node, tot3510, tot3511]
  decide +kernel

theorem arows3505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3505 = true := by
  rw [show A10K2.u3505 = KTree.node A10K2.t3512 (nat_lit 58029725) (nat_lit 5564485211) (nat_lit 0) A10K2.t3513 from rfl, allE_node, rows3512, irow3505, rows3513]
  all_goals rfl

theorem atot3505 : totK PA10K2 A10K2.u3505 = [0, 0, 0, 627508793854, 2813508900349, 4151436084693, 2006061297110, 289179859400, 6962742351, 0] := by
  rw [show A10K2.u3505 = KTree.node A10K2.t3512 (nat_lit 58029725) (nat_lit 5564485211) (nat_lit 0) A10K2.t3513 from rfl, totK_node, tot3512, tot3513]
  decide +kernel

theorem arows3506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3506 = true := by
  rw [show A10K2.u3506 = KTree.node A10K2.t3514 (nat_lit 58071360) (nat_lit 14287852619) (nat_lit 0) A10K2.t3515 from rfl, allE_node, rows3514, irow3506, rows3515]
  all_goals rfl

theorem atot3506 : totK PA10K2 A10K2.u3506 = [0, 0, 0, 679883209614, 2905047558373, 3951133956206, 1620401940451, 174738379621, 5460492893, 0] := by
  rw [show A10K2.u3506 = KTree.node A10K2.t3514 (nat_lit 58071360) (nat_lit 14287852619) (nat_lit 0) A10K2.t3515 from rfl, totK_node, tot3514, tot3515]
  decide +kernel

theorem arows3508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3508 = true := by
  rw [show A10K2.u3508 = KTree.node A10K2.t3516 (nat_lit 58078564) (nat_lit 13494132798) (nat_lit 0) A10K2.t3517 from rfl, allE_node, rows3516, irow3508, rows3517]
  all_goals rfl

theorem atot3508 : totK PA10K2 A10K2.u3508 = [0, 0, 0, 332818647249, 2152613930040, 4022285226988, 2504837537074, 487529497735, 31003444686, 0] := by
  rw [show A10K2.u3508 = KTree.node A10K2.t3516 (nat_lit 58078564) (nat_lit 13494132798) (nat_lit 0) A10K2.t3517 from rfl, totK_node, tot3516, tot3517]
  decide +kernel

theorem arows3509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3509 = true := by
  rw [show A10K2.u3509 = KTree.node A10K2.t3518 (nat_lit 58083062) (nat_lit 11907752405) (nat_lit 0) A10K2.t3519 from rfl, allE_node, rows3518, irow3509, rows3519]
  all_goals rfl

theorem atot3509 : totK PA10K2 A10K2.u3509 = [0, 0, 0, 820483373723, 3284191173566, 3884031811523, 1204591530631, 67576196240, 0, 0] := by
  rw [show A10K2.u3509 = KTree.node A10K2.t3518 (nat_lit 58083062) (nat_lit 11907752405) (nat_lit 0) A10K2.t3519 from rfl, totK_node, tot3518, tot3519]
  decide +kernel

theorem arows3515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3515 = true := by
  rw [show A10K2.u3515 = KTree.node A10K2.t3520 (nat_lit 58097960) (nat_lit 12390657786) (nat_lit 0) A10K2.t3521 from rfl, allE_node, rows3520, irow3515, rows3521]
  all_goals rfl

theorem atot3515 : totK PA10K2 A10K2.u3515 = [0, 0, 0, 0, 1409352414210, 4285422238305, 3077359188825, 485672443613, 12709086536, 0] := by
  rw [show A10K2.u3515 = KTree.node A10K2.t3520 (nat_lit 58097960) (nat_lit 12390657786) (nat_lit 0) A10K2.t3521 from rfl, totK_node, tot3520, tot3521]
  decide +kernel

theorem arows3516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3516 = true := by
  rw [show A10K2.u3516 = KTree.node A10K2.t3522 (nat_lit 58114147) (nat_lit 4730707309) (nat_lit 0) A10K2.t3523 from rfl, allE_node, rows3522, irow3516, rows3523]
  all_goals rfl

theorem atot3516 : totK PA10K2 A10K2.u3516 = [0, 0, 0, 0, 1131989975893, 3731868620398, 3439847996823, 872019652194, 62564938186, 0] := by
  rw [show A10K2.u3516 = KTree.node A10K2.t3522 (nat_lit 58114147) (nat_lit 4730707309) (nat_lit 0) A10K2.t3523 from rfl, totK_node, tot3522, tot3523]
  decide +kernel

theorem arows3518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3518 = true := by
  rw [show A10K2.u3518 = KTree.node A10K2.t3524 (nat_lit 58120414) (nat_lit 4611247264) (nat_lit 0) A10K2.t3525 from rfl, allE_node, rows3524, irow3518, rows3525]
  all_goals rfl

theorem atot3518 : totK PA10K2 A10K2.u3518 = [0, 0, 433610675281, 1404868445336, 1399669916019, 1779924626515, 2810001051043, 1386641425290, 196686909756, 6354482628] := by
  rw [show A10K2.u3518 = KTree.node A10K2.t3524 (nat_lit 58120414) (nat_lit 4611247264) (nat_lit 0) A10K2.t3525 from rfl, totK_node, tot3524, tot3525]
  decide +kernel

theorem arows3519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3519 = true := by
  rw [show A10K2.u3519 = KTree.node A10K2.t3526 (nat_lit 58221788) (nat_lit 9724015954) (nat_lit 0) A10K2.t3527 from rfl, allE_node, rows3526, irow3519, rows3527]
  all_goals rfl

theorem atot3519 : totK PA10K2 A10K2.u3519 = [0, 0, 951817273229, 3686296155778, 4276257950216, 1380979054478, 94117172906, 0, 0, 0] := by
  rw [show A10K2.u3519 = KTree.node A10K2.t3526 (nat_lit 58221788) (nat_lit 9724015954) (nat_lit 0) A10K2.t3527 from rfl, totK_node, tot3526, tot3527]
  decide +kernel

theorem arows3522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3522 = true := by
  rw [show A10K2.u3522 = KTree.node A10K2.t3528 (nat_lit 58227931) (nat_lit 8513105699) (nat_lit 0) A10K2.t3529 from rfl, allE_node, rows3528, irow3522, rows3529]
  all_goals rfl

theorem atot3522 : totK PA10K2 A10K2.u3522 = [0, 0, 316661823121, 1806587483029, 3739808184203, 3300413397075, 968971450202, 62708521344, 0, 0] := by
  rw [show A10K2.u3522 = KTree.node A10K2.t3528 (nat_lit 58227931) (nat_lit 8513105699) (nat_lit 0) A10K2.t3529 from rfl, totK_node, tot3528, tot3529]
  decide +kernel

theorem arows3523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3523 = true := by
  rw [show A10K2.u3523 = KTree.node A10K2.t3530 (nat_lit 58273434) (nat_lit 15094184054) (nat_lit 0) A10K2.t3531 from rfl, allE_node, rows3530, irow3523, rows3531]
  all_goals rfl

theorem atot3523 : totK PA10K2 A10K2.u3523 = [0, 0, 528367883341, 2532046606129, 3978164813886, 2253974352579, 435710944065, 25734533292, 0, 0] := by
  rw [show A10K2.u3523 = KTree.node A10K2.t3530 (nat_lit 58273434) (nat_lit 15094184054) (nat_lit 0) A10K2.t3531 from rfl, totK_node, tot3530, tot3531]
  decide +kernel

theorem arows3525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3525 = true := by
  rw [show A10K2.u3525 = KTree.node A10K2.t3532 (nat_lit 58279601) (nat_lit 1985783238) (nat_lit 0) A10K2.t3533 from rfl, allE_node, rows3532, irow3525, rows3533]
  all_goals rfl

theorem atot3525 : totK PA10K2 A10K2.u3525 = [0, 0, 554851874388, 2699067292199, 4035219578340, 2023409006533, 259811307343, 6034215561, 0, 0] := by
  rw [show A10K2.u3525 = KTree.node A10K2.t3532 (nat_lit 58279601) (nat_lit 1985783238) (nat_lit 0) A10K2.t3533 from rfl, totK_node, tot3532, tot3533]
  decide +kernel

theorem arows3526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3526 = true := by
  rw [show A10K2.u3526 = KTree.node A10K2.t3534 (nat_lit 58287381) (nat_lit 6531070536) (nat_lit 0) A10K2.t3535 from rfl, allE_node, rows3534, irow3526, rows3535]
  all_goals rfl

theorem atot3526 : totK PA10K2 A10K2.u3526 = [0, 0, 815132638627, 3129127969801, 4003358723382, 1736171404245, 210599999270, 5982052406, 0, 0] := by
  rw [show A10K2.u3526 = KTree.node A10K2.t3534 (nat_lit 58287381) (nat_lit 6531070536) (nat_lit 0) A10K2.t3535 from rfl, totK_node, tot3534, tot3535]
  decide +kernel

theorem arows3530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3530 = true := by
  rw [show A10K2.u3530 = KTree.node A10K2.t3536 (nat_lit 58292145) (nat_lit 7278516468) (nat_lit 0) A10K2.t3537 from rfl, allE_node, rows3536, irow3530, rows3537]
  all_goals rfl

theorem atot3530 : totK PA10K2 A10K2.u3530 = [0, 0, 0, 1249883221610, 4059991362749, 3809372016733, 975799351502, 48461350123, 0, 0] := by
  rw [show A10K2.u3530 = KTree.node A10K2.t3536 (nat_lit 58292145) (nat_lit 7278516468) (nat_lit 0) A10K2.t3537 from rfl, totK_node, tot3536, tot3537]
  decide +kernel

theorem arows3531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3531 = true := by
  rw [show A10K2.u3531 = KTree.node A10K2.t3538 (nat_lit 58305941) (nat_lit 4625428012) (nat_lit 0) A10K2.t3539 from rfl, allE_node, rows3538, irow3531, rows3539]
  all_goals rfl

theorem atot3531 : totK PA10K2 A10K2.u3531 = [0, 0, 0, 527545313304, 2628351712116, 4043897666638, 2047552946018, 387346000688, 25565504801, 0] := by
  rw [show A10K2.u3531 = KTree.node A10K2.t3538 (nat_lit 58305941) (nat_lit 4625428012) (nat_lit 0) A10K2.t3539 from rfl, totK_node, tot3538, tot3539]
  decide +kernel

theorem arows3533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3533 = true := by
  rw [show A10K2.u3533 = KTree.node A10K2.t3540 (nat_lit 58312158) (nat_lit 14335699038) (nat_lit 0) A10K2.t3541 from rfl, allE_node, rows3540, irow3533, rows3541]
  all_goals rfl

theorem atot3533 : totK PA10K2 A10K2.u3533 = [0, 0, 0, 754322923102, 3093974684688, 3841327227049, 1677287252197, 242307564155, 5517381808, 0] := by
  rw [show A10K2.u3533 = KTree.node A10K2.t3540 (nat_lit 58312158) (nat_lit 14335699038) (nat_lit 0) A10K2.t3541 from rfl, totK_node, tot3540, tot3541]
  decide +kernel

theorem arows3534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3534 = true := by
  rw [show A10K2.u3534 = KTree.node A10K2.t3542 (nat_lit 58322395) (nat_lit 6766853699) (nat_lit 0) A10K2.t3543 from rfl, allE_node, rows3542, irow3534, rows3543]
  all_goals rfl

theorem atot3534 : totK PA10K2 A10K2.u3534 = [0, 0, 424471676933, 1962424241450, 3589176885828, 3042517536604, 995458767787, 68516142398, 0, 0] := by
  rw [show A10K2.u3534 = KTree.node A10K2.t3542 (nat_lit 58322395) (nat_lit 6766853699) (nat_lit 0) A10K2.t3543 from rfl, totK_node, tot3542, tot3543]
  decide +kernel

theorem arows3537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3537 = true := by
  rw [show A10K2.u3537 = KTree.node A10K2.t3544 (nat_lit 58398774) (nat_lit 15197038330) (nat_lit 0) A10K2.t3545 from rfl, allE_node, rows3544, irow3537, rows3545]
  all_goals rfl

theorem atot3537 : totK PA10K2 A10K2.u3537 = [0, 0, 544472211505, 2691973552219, 4284052874945, 2267720737500, 313670803232, 7903172220, 0, 0] := by
  rw [show A10K2.u3537 = KTree.node A10K2.t3544 (nat_lit 58398774) (nat_lit 15197038330) (nat_lit 0) A10K2.t3545 from rfl, totK_node, tot3544, tot3545]
  decide +kernel

theorem arows3538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3538 = true := by
  rw [show A10K2.u3538 = KTree.node A10K2.t3546 (nat_lit 58406053) (nat_lit 6624481473) (nat_lit 0) A10K2.t3547 from rfl, allE_node, rows3546, irow3538, rows3547]
  all_goals rfl

theorem atot3538 : totK PA10K2 A10K2.u3538 = [0, 0, 437221486770, 2362168678991, 4094024147301, 2535614092454, 470119743159, 25654631657, 0, 0] := by
  rw [show A10K2.u3538 = KTree.node A10K2.t3546 (nat_lit 58406053) (nat_lit 6624481473) (nat_lit 0) A10K2.t3547 from rfl, totK_node, tot3546, tot3547]
  decide +kernel

theorem arows3540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3540 = true := by
  rw [show A10K2.u3540 = KTree.node A10K2.t3548 (nat_lit 58418678) (nat_lit 16668028827) (nat_lit 0) A10K2.t3549 from rfl, allE_node, rows3548, irow3540, rows3549]
  all_goals rfl

theorem atot3540 : totK PA10K2 A10K2.u3540 = [0, 0, 873795323667, 3364031637407, 4062049191339, 1591007750234, 143601606913, 0, 0, 0] := by
  rw [show A10K2.u3540 = KTree.node A10K2.t3548 (nat_lit 58418678) (nat_lit 16668028827) (nat_lit 0) A10K2.t3549 from rfl, totK_node, tot3548, tot3549]
  decide +kernel

theorem arows3541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3541 = true := by
  rw [show A10K2.u3541 = KTree.node A10K2.t3550 (nat_lit 58424364) (nat_lit 5722707661) (nat_lit 0) A10K2.t3551 from rfl, allE_node, rows3550, irow3541, rows3551]
  all_goals rfl

theorem atot3541 : totK PA10K2 A10K2.u3541 = [0, 0, 0, 1253111198656, 4034868105557, 3747060667801, 1006452788492, 62996513375, 0, 0] := by
  rw [show A10K2.u3541 = KTree.node A10K2.t3550 (nat_lit 58424364) (nat_lit 5722707661) (nat_lit 0) A10K2.t3551 from rfl, totK_node, tot3550, tot3551]
  decide +kernel

theorem arows3546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3546 = true := by
  rw [show A10K2.u3546 = KTree.node A10K2.t3552 (nat_lit 58435292) (nat_lit 10796029706) (nat_lit 0) A10K2.t3553 from rfl, allE_node, rows3552, irow3546, rows3553]
  all_goals rfl

theorem atot3546 : totK PA10K2 A10K2.u3546 = [0, 0, 0, 980133930848, 3656026625547, 3980243498933, 1285241989346, 83259030176, 0, 0] := by
  rw [show A10K2.u3546 = KTree.node A10K2.t3552 (nat_lit 58435292) (nat_lit 10796029706) (nat_lit 0) A10K2.t3553 from rfl, totK_node, tot3552, tot3553]
  decide +kernel

theorem arows3547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3547 = true := by
  rw [show A10K2.u3547 = KTree.node A10K2.t3554 (nat_lit 58440951) (nat_lit 14641121806) (nat_lit 0) A10K2.t3555 from rfl, allE_node, rows3554, irow3547, rows3555]
  all_goals rfl

theorem atot3547 : totK PA10K2 A10K2.u3547 = [0, 0, 0, 539312721908, 2652119690449, 4155586766546, 2300960436912, 330674639328, 7047025452, 0] := by
  rw [show A10K2.u3547 = KTree.node A10K2.t3554 (nat_lit 58440951) (nat_lit 14641121806) (nat_lit 0) A10K2.t3555 from rfl, totK_node, tot3554, tot3555]
  decide +kernel

theorem arows3549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3549 = true := by
  rw [show A10K2.u3549 = KTree.node A10K2.t3556 (nat_lit 58454515) (nat_lit 7799539766) (nat_lit 0) A10K2.t3557 from rfl, allE_node, rows3556, irow3549, rows3557]
  all_goals rfl

theorem atot3549 : totK PA10K2 A10K2.u3549 = [0, 0, 0, 326490833374, 2206609512870, 4271088710612, 2759086746495, 485167634842, 11979448558, 0] := by
  rw [show A10K2.u3549 = KTree.node A10K2.t3556 (nat_lit 58454515) (nat_lit 7799539766) (nat_lit 0) A10K2.t3557 from rfl, totK_node, tot3556, tot3557]
  decide +kernel

theorem arows3550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3550 = true := by
  rw [show A10K2.u3550 = KTree.node A10K2.t3558 (nat_lit 58722596) (nat_lit 14146055856) (nat_lit 0) A10K2.t3559 from rfl, allE_node, rows3558, irow3550, rows3559]
  all_goals rfl

theorem atot3550 : totK PA10K2 A10K2.u3550 = [0, 840727299041, 3245615607153, 3728909968759, 1252397752296, 175978176360, 265134597811, 204698064761, 29941795906, 0] := by
  rw [show A10K2.u3550 = KTree.node A10K2.t3558 (nat_lit 58722596) (nat_lit 14146055856) (nat_lit 0) A10K2.t3559 from rfl, totK_node, tot3558, tot3559]
  decide +kernel

theorem arows3553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3553 = true := by
  rw [show A10K2.u3553 = KTree.node A10K2.t3560 (nat_lit 58727486) (nat_lit 15940319764) (nat_lit 0) A10K2.t3561 from rfl, allE_node, rows3560, irow3553, rows3561]
  all_goals rfl

theorem atot3553 : totK PA10K2 A10K2.u3553 = [0, 460078346494, 2148870068060, 3756774700951, 2593020891183, 552433512826, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u3553 = KTree.node A10K2.t3560 (nat_lit 58727486) (nat_lit 15940319764) (nat_lit 0) A10K2.t3561 from rfl, totK_node, tot3560, tot3561]
  decide +kernel

theorem arows3554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3554 = true := by
  rw [show A10K2.u3554 = KTree.node A10K2.t3562 (nat_lit 58741134) (nat_lit 14534523165) (nat_lit 0) A10K2.t3563 from rfl, allE_node, rows3562, irow3554, rows3563]
  all_goals rfl

theorem atot3554 : totK PA10K2 A10K2.u3554 = [0, 488521415153, 2444307060175, 3978379901973, 2100694700379, 301871496373, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3554 = KTree.node A10K2.t3562 (nat_lit 58741134) (nat_lit 14534523165) (nat_lit 0) A10K2.t3563 from rfl, totK_node, tot3562, tot3563]
  decide +kernel

theorem arows3556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3556 = true := by
  rw [show A10K2.u3556 = KTree.node A10K2.t3564 (nat_lit 58748962) (nat_lit 3634011185) (nat_lit 0) A10K2.t3565 from rfl, allE_node, rows3564, irow3556, rows3565]
  all_goals rfl

theorem atot3556 : totK PA10K2 A10K2.u3556 = [0, 390980993817, 2268059055032, 4240888904184, 2819327806852, 515023778239, 12746179907, 0, 0, 0] := by
  rw [show A10K2.u3556 = KTree.node A10K2.t3564 (nat_lit 58748962) (nat_lit 3634011185) (nat_lit 0) A10K2.t3565 from rfl, totK_node, tot3564, tot3565]
  decide +kernel

theorem arows3557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3557 = true := by
  rw [show A10K2.u3557 = KTree.node A10K2.t3566 (nat_lit 58755424) (nat_lit 12546697981) (nat_lit 0) A10K2.t3567 from rfl, allE_node, rows3566, irow3557, rows3567]
  all_goals rfl

theorem atot3557 : totK PA10K2 A10K2.u3557 = [0, 0, 837474059011, 3344075726416, 4001766058820, 1370919752081, 110006195671, 0, 0, 0] := by
  rw [show A10K2.u3557 = KTree.node A10K2.t3566 (nat_lit 58755424) (nat_lit 12546697981) (nat_lit 0) A10K2.t3567 from rfl, totK_node, tot3566, tot3567]
  decide +kernel

theorem arows3561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3561 = true := by
  rw [show A10K2.u3561 = KTree.node A10K2.t3568 (nat_lit 58760585) (nat_lit 8696006851) (nat_lit 0) A10K2.t3569 from rfl, allE_node, rows3568, irow3561, rows3569]
  all_goals rfl

theorem atot3561 : totK PA10K2 A10K2.u3561 = [0, 0, 458986923692, 2240476819758, 3790638956842, 2357764678997, 520524378838, 30650496230, 0, 0] := by
  rw [show A10K2.u3561 = KTree.node A10K2.t3568 (nat_lit 58760585) (nat_lit 8696006851) (nat_lit 0) A10K2.t3569 from rfl, totK_node, tot3568, tot3569]
  decide +kernel

theorem arows3562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3562 = true := by
  rw [show A10K2.u3562 = KTree.node A10K2.t3570 (nat_lit 58774866) (nat_lit 13477920813) (nat_lit 0) A10K2.t3571 from rfl, allE_node, rows3570, irow3562, rows3571]
  all_goals rfl

theorem atot3562 : totK PA10K2 A10K2.u3562 = [0, 0, 580223966792, 2704755913443, 3989744881960, 1835671408801, 225076579657, 5546304973, 0, 0] := by
  rw [show A10K2.u3562 = KTree.node A10K2.t3570 (nat_lit 58774866) (nat_lit 13477920813) (nat_lit 0) A10K2.t3571 from rfl, totK_node, tot3570, tot3571]
  decide +kernel

theorem arows3564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3564 = true := by
  rw [show A10K2.u3564 = KTree.node A10K2.t3572 (nat_lit 58851832) (nat_lit 13324120295) (nat_lit 0) A10K2.t3573 from rfl, allE_node, rows3572, irow3564, rows3573]
  all_goals rfl

theorem atot3564 : totK PA10K2 A10K2.u3564 = [0, 767063984985, 2875951710662, 3682094219580, 2099112105915, 501320169203, 30829329317, 0, 0, 0] := by
  rw [show A10K2.u3564 = KTree.node A10K2.t3572 (nat_lit 58851832) (nat_lit 13324120295) (nat_lit 0) A10K2.t3573 from rfl, totK_node, tot3572, tot3573]
  decide +kernel

theorem arows3565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3565 = true := by
  rw [show A10K2.u3565 = KTree.node A10K2.t3574 (nat_lit 58857701) (nat_lit 7104187474) (nat_lit 0) A10K2.t3575 from rfl, allE_node, rows3574, irow3565, rows3575]
  all_goals rfl

theorem atot3565 : totK PA10K2 A10K2.u3565 = [0, 279016151902, 1916071037769, 3994757352312, 2866913095253, 588187533014, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u3565 = KTree.node A10K2.t3574 (nat_lit 58857701) (nat_lit 7104187474) (nat_lit 0) A10K2.t3575 from rfl, totK_node, tot3574, tot3575]
  decide +kernel

theorem arows3568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3568 = true := by
  rw [show A10K2.u3568 = KTree.node A10K2.t3576 (nat_lit 58865365) (nat_lit 6132576974) (nat_lit 0) A10K2.t3577 from rfl, allE_node, rows3576, irow3568, rows3577]
  all_goals rfl

theorem atot3568 : totK PA10K2 A10K2.u3568 = [0, 558996927426, 2402061952635, 3733485663544, 2376186060590, 478410547187, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3568 = KTree.node A10K2.t3576 (nat_lit 58865365) (nat_lit 6132576974) (nat_lit 0) A10K2.t3577 from rfl, totK_node, tot3576, tot3577]
  decide +kernel

theorem arows3569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3569 = true := by
  rw [show A10K2.u3569 = KTree.node A10K2.t3578 (nat_lit 58870002) (nat_lit 12750922797) (nat_lit 0) A10K2.t3579 from rfl, allE_node, rows3578, irow3569, rows3579]
  all_goals rfl

theorem atot3569 : totK PA10K2 A10K2.u3569 = [0, 542618031769, 2840322732343, 4218013431800, 1700434654627, 126325285352, 0, 0, 0, 0] := by
  rw [show A10K2.u3569 = KTree.node A10K2.t3578 (nat_lit 58870002) (nat_lit 12750922797) (nat_lit 0) A10K2.t3579 from rfl, totK_node, tot3578, tot3579]
  decide +kernel

theorem arows3571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3571 = true := by
  rw [show A10K2.u3571 = KTree.node A10K2.t3580 (nat_lit 58884928) (nat_lit 14462861641) (nat_lit 0) A10K2.t3581 from rfl, allE_node, rows3580, irow3571, rows3581]
  all_goals rfl

theorem atot3571 : totK PA10K2 A10K2.u3571 = [0, 0, 1034604433579, 3747100202135, 3803879566497, 964987982313, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u3571 = KTree.node A10K2.t3580 (nat_lit 58884928) (nat_lit 14462861641) (nat_lit 0) A10K2.t3581 from rfl, totK_node, tot3580, tot3581]
  decide +kernel

theorem arows3572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3572 = true := by
  rw [show A10K2.u3572 = KTree.node A10K2.t3582 (nat_lit 58895137) (nat_lit 9134451381) (nat_lit 0) A10K2.t3583 from rfl, allE_node, rows3582, irow3572, rows3583]
  all_goals rfl

theorem atot3572 : totK PA10K2 A10K2.u3572 = [0, 0, 1007880409777, 3672930276970, 3765497622846, 982748762584, 71422475040, 0, 0, 0] := by
  rw [show A10K2.u3572 = KTree.node A10K2.t3582 (nat_lit 58895137) (nat_lit 9134451381) (nat_lit 0) A10K2.t3583 from rfl, totK_node, tot3582, tot3583]
  decide +kernel

theorem arows3581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3581 = true := by
  rw [show A10K2.u3581 = KTree.node A10K2.t3584 (nat_lit 58905768) (nat_lit 7536925380) (nat_lit 0) A10K2.t3585 from rfl, allE_node, rows3584, irow3581, rows3585]
  all_goals rfl

theorem atot3581 : totK PA10K2 A10K2.u3581 = [0, 0, 554763177027, 2644525787397, 3970218467954, 1845958183520, 271677105452, 6354482628, 0, 0] := by
  rw [show A10K2.u3581 = KTree.node A10K2.t3584 (nat_lit 58905768) (nat_lit 7536925380) (nat_lit 0) A10K2.t3585 from rfl, totK_node, tot3584, tot3585]
  decide +kernel

theorem arows3582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3582 = true := by
  rw [show A10K2.u3582 = KTree.node A10K2.t3586 (nat_lit 58985587) (nat_lit 5548872433) (nat_lit 0) A10K2.t3587 from rfl, allE_node, rows3586, irow3582, rows3587]
  all_goals rfl

theorem atot3582 : totK PA10K2 A10K2.u3582 = [0, 0, 585451290126, 2756624524130, 4001367162675, 1929273697224, 327371427913, 20070762815, 0, 0] := by
  rw [show A10K2.u3582 = KTree.node A10K2.t3586 (nat_lit 58985587) (nat_lit 5548872433) (nat_lit 0) A10K2.t3587 from rfl, totK_node, tot3586, tot3587]
  decide +kernel

theorem arows3584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3584 = true := by
  rw [show A10K2.u3584 = KTree.node A10K2.t3588 (nat_lit 58999069) (nat_lit 6332833813) (nat_lit 0) A10K2.t3589 from rfl, allE_node, rows3588, irow3584, rows3589]
  all_goals rfl

theorem atot3584 : totK PA10K2 A10K2.u3584 = [0, 0, 699887931742, 2730570996183, 3774671432213, 1916369237321, 307365389939, 10760911071, 0, 0] := by
  rw [show A10K2.u3584 = KTree.node A10K2.t3588 (nat_lit 58999069) (nat_lit 6332833813) (nat_lit 0) A10K2.t3589 from rfl, totK_node, tot3588, tot3589]
  decide +kernel

theorem arows3585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3585 = true := by
  rw [show A10K2.u3585 = KTree.node A10K2.t3590 (nat_lit 59005184) (nat_lit 14017144367) (nat_lit 0) A10K2.t3591 from rfl, allE_node, rows3590, irow3585, rows3591]
  all_goals rfl

theorem atot3585 : totK PA10K2 A10K2.u3585 = [0, 0, 442904053540, 2555174076666, 4203411965610, 2009301812458, 231729266272, 5705019915, 0, 0] := by
  rw [show A10K2.u3585 = KTree.node A10K2.t3590 (nat_lit 59005184) (nat_lit 14017144367) (nat_lit 0) A10K2.t3591 from rfl, totK_node, tot3590, tot3591]
  decide +kernel

theorem arows3588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3588 = true := by
  rw [show A10K2.u3588 = KTree.node A10K2.t3592 (nat_lit 59012023) (nat_lit 15014564704) (nat_lit 0) A10K2.t3593 from rfl, allE_node, rows3592, irow3588, rows3593]
  all_goals rfl

theorem atot3588 : totK PA10K2 A10K2.u3588 = [0, 0, 595886583297, 2713116597819, 4182131498665, 2274281169556, 330490271267, 6853348008, 0, 0] := by
  rw [show A10K2.u3588 = KTree.node A10K2.t3592 (nat_lit 59012023) (nat_lit 15014564704) (nat_lit 0) A10K2.t3593 from rfl, totK_node, tot3592, tot3593]
  decide +kernel

theorem arows3589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3589 = true := by
  rw [show A10K2.u3589 = KTree.node A10K2.t3594 (nat_lit 59117844) (nat_lit 12544859683) (nat_lit 0) A10K2.t3595 from rfl, allE_node, rows3594, irow3589, rows3595]
  all_goals rfl

theorem atot3589 : totK PA10K2 A10K2.u3589 = [0, 0, 360870500530, 2184059879237, 3989437920271, 2450360277939, 457560955589, 30831673886, 0, 0] := by
  rw [show A10K2.u3589 = KTree.node A10K2.t3594 (nat_lit 59117844) (nat_lit 12544859683) (nat_lit 0) A10K2.t3595 from rfl, totK_node, tot3594, tot3595]
  decide +kernel

theorem arows3591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3591 = true := by
  rw [show A10K2.u3591 = KTree.node A10K2.t3596 (nat_lit 59124236) (nat_lit 11701418930) (nat_lit 0) A10K2.t3597 from rfl, allE_node, rows3596, irow3591, rows3597]
  all_goals rfl

theorem atot3591 : totK PA10K2 A10K2.u3591 = [0, 0, 561822984708, 2685865036904, 4117851629164, 1977366061180, 241435584694, 6034215561, 0, 0] := by
  rw [show A10K2.u3591 = KTree.node A10K2.t3596 (nat_lit 59124236) (nat_lit 11701418930) (nat_lit 0) A10K2.t3597 from rfl, totK_node, tot3596, tot3597]
  decide +kernel

theorem arows3592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3592 = true := by
  rw [show A10K2.u3592 = KTree.node A10K2.t3598 (nat_lit 59131678) (nat_lit 9139897259) (nat_lit 0) A10K2.t3599 from rfl, allE_node, rows3598, irow3592, rows3599]
  all_goals rfl

theorem atot3592 : totK PA10K2 A10K2.u3592 = [0, 0, 802219773210, 3317278439377, 3947646378611, 1269645991878, 91476778698, 0, 0, 0] := by
  rw [show A10K2.u3592 = KTree.node A10K2.t3598 (nat_lit 59131678) (nat_lit 9139897259) (nat_lit 0) A10K2.t3599 from rfl, totK_node, tot3598, tot3599]
  decide +kernel

end QECKChecks.A10K2
