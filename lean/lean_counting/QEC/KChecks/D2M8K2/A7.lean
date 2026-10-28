import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A6

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows8396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8396 = true := by
  rw [show D2M8K2.u8396 = KTree.node D2M8K2.t8400 (nat_lit 18181589) (nat_lit 2038000931) (nat_lit 0) D2M8K2.t8401 from rfl, allE_node, rows8400, irow8396, rows8401]
  all_goals rfl

theorem atot8396 : totK PD2M8K2 D2M8K2.u8396 = [0, 155397482314, 719570630598, 773968497585, 129947583190, 3838026431, 0, 0] := by
  rw [show D2M8K2.u8396 = KTree.node D2M8K2.t8400 (nat_lit 18181589) (nat_lit 2038000931) (nat_lit 0) D2M8K2.t8401 from rfl, totK_node, tot8400, tot8401]
  decide +kernel

theorem arows8397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8397 = true := by
  rw [show D2M8K2.u8397 = KTree.node D2M8K2.t8402 (nat_lit 18183462) (nat_lit 3780083652) (nat_lit 0) D2M8K2.t8403 from rfl, allE_node, rows8402, irow8397, rows8403]
  all_goals rfl

theorem atot8397 : totK PD2M8K2 D2M8K2.u8397 = [0, 262119182791, 780167757737, 629536221555, 108522338211, 1268739303, 0, 0] := by
  rw [show D2M8K2.u8397 = KTree.node D2M8K2.t8402 (nat_lit 18183462) (nat_lit 3780083652) (nat_lit 0) D2M8K2.t8403 from rfl, totK_node, tot8402, tot8403]
  decide +kernel

theorem arows8399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8399 = true := by
  rw [show D2M8K2.u8399 = KTree.node D2M8K2.t8404 (nat_lit 18184877) (nat_lit 1487006904) (nat_lit 0) D2M8K2.t8405 from rfl, allE_node, rows8404, irow8399, rows8405]
  all_goals rfl

theorem atot8399 : totK PD2M8K2 D2M8K2.u8399 = [0, 0, 402806734173, 955897971547, 367464901830, 21873045024, 0, 0] := by
  rw [show D2M8K2.u8399 = KTree.node D2M8K2.t8404 (nat_lit 18184877) (nat_lit 1487006904) (nat_lit 0) D2M8K2.t8405 from rfl, totK_node, tot8404, tot8405]
  decide +kernel

theorem arows8400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8400 = true := by
  rw [show D2M8K2.u8400 = KTree.node D2M8K2.t8406 (nat_lit 18186662) (nat_lit 2688920530) (nat_lit 0) D2M8K2.t8407 from rfl, allE_node, rows8406, irow8400, rows8407]
  all_goals rfl

theorem atot8400 : totK PD2M8K2 D2M8K2.u8400 = [0, 0, 327798076727, 899496058458, 476667214370, 39815991286, 0, 0] := by
  rw [show D2M8K2.u8400 = KTree.node D2M8K2.t8406 (nat_lit 18186662) (nat_lit 2688920530) (nat_lit 0) D2M8K2.t8407 from rfl, totK_node, tot8406, tot8407]
  decide +kernel

theorem arows8403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8403 = true := by
  rw [show D2M8K2.u8403 = KTree.node D2M8K2.t8408 (nat_lit 18188461) (nat_lit 1126510899) (nat_lit 0) D2M8K2.t8409 from rfl, allE_node, rows8408, irow8403, rows8409]
  all_goals rfl

theorem atot8403 : totK PD2M8K2 D2M8K2.u8403 = [0, 0, 190466417523, 737012652211, 675210066637, 124669271428, 1369150432, 0] := by
  rw [show D2M8K2.u8403 = KTree.node D2M8K2.t8408 (nat_lit 18188461) (nat_lit 1126510899) (nat_lit 0) D2M8K2.t8409 from rfl, totK_node, tot8408, tot8409]
  decide +kernel

theorem arows8404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8404 = true := by
  rw [show D2M8K2.u8404 = KTree.node D2M8K2.t8410 (nat_lit 18193949) (nat_lit 2298722737) (nat_lit 0) D2M8K2.t8411 from rfl, allE_node, rows8410, irow8404, rows8411]
  all_goals rfl

theorem atot8404 : totK PD2M8K2 D2M8K2.u8404 = [0, 0, 395502869193, 950539929773, 377594043993, 22141929093, 0, 0] := by
  rw [show D2M8K2.u8404 = KTree.node D2M8K2.t8410 (nat_lit 18193949) (nat_lit 2298722737) (nat_lit 0) D2M8K2.t8411 from rfl, totK_node, tot8410, tot8411]
  decide +kernel

theorem arows8406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8406 = true := by
  rw [show D2M8K2.u8406 = KTree.node D2M8K2.t8412 (nat_lit 18197370) (nat_lit 3918445402) (nat_lit 0) D2M8K2.t8413 from rfl, allE_node, rows8412, irow8406, rows8413]
  all_goals rfl

theorem atot8406 : totK PD2M8K2 D2M8K2.u8406 = [0, 0, 403668656616, 951364375934, 371855327840, 22218528345, 0, 0] := by
  rw [show D2M8K2.u8406 = KTree.node D2M8K2.t8412 (nat_lit 18197370) (nat_lit 3918445402) (nat_lit 0) D2M8K2.t8413 from rfl, totK_node, tot8412, tot8413]
  decide +kernel

theorem arows8407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8407 = true := by
  rw [show D2M8K2.u8407 = KTree.node D2M8K2.t8414 (nat_lit 18200517) (nat_lit 1516654908) (nat_lit 0) D2M8K2.t8415 from rfl, allE_node, rows8414, irow8407, rows8415]
  all_goals rfl

theorem atot8407 : totK PD2M8K2 D2M8K2.u8407 = [0, 0, 398560573223, 956978582236, 371724852045, 21852174825, 0, 0] := by
  rw [show D2M8K2.u8407 = KTree.node D2M8K2.t8414 (nat_lit 18200517) (nat_lit 1516654908) (nat_lit 0) D2M8K2.t8415 from rfl, totK_node, tot8414, tot8415]
  decide +kernel

theorem arows8412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8412 = true := by
  rw [show D2M8K2.u8412 = KTree.node D2M8K2.t8416 (nat_lit 18204270) (nat_lit 4037877846) (nat_lit 0) D2M8K2.t8417 from rfl, allE_node, rows8416, irow8412, rows8417]
  all_goals rfl

theorem atot8412 : totK PD2M8K2 D2M8K2.u8412 = [0, 160713320421, 574137494217, 724216211894, 291650871522, 21055313582, 0, 0] := by
  rw [show D2M8K2.u8412 = KTree.node D2M8K2.t8416 (nat_lit 18204270) (nat_lit 4037877846) (nat_lit 0) D2M8K2.t8417 from rfl, totK_node, tot8416, tot8417]
  decide +kernel

theorem arows8413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8413 = true := by
  rw [show D2M8K2.u8413 = KTree.node D2M8K2.t8418 (nat_lit 18249003) (nat_lit 2876077978) (nat_lit 0) D2M8K2.t8419 from rfl, allE_node, rows8418, irow8413, rows8419]
  all_goals rfl

theorem atot8413 : totK PD2M8K2 D2M8K2.u8413 = [0, 254632037833, 815603675336, 598742666257, 87254748787, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8413 = KTree.node D2M8K2.t8418 (nat_lit 18249003) (nat_lit 2876077978) (nat_lit 0) D2M8K2.t8419 from rfl, totK_node, tot8418, tot8419]
  decide +kernel

theorem arows8415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8415 = true := by
  rw [show D2M8K2.u8415 = KTree.node D2M8K2.t8420 (nat_lit 18250939) (nat_lit 1629803646) (nat_lit 0) D2M8K2.t8421 from rfl, allE_node, rows8420, irow8415, rows8421]
  all_goals rfl

theorem atot8415 : totK PD2M8K2 D2M8K2.u8415 = [0, 178066458620, 758183510043, 767771114936, 104682687552, 0, 0, 0] := by
  rw [show D2M8K2.u8415 = KTree.node D2M8K2.t8420 (nat_lit 18250939) (nat_lit 1629803646) (nat_lit 0) D2M8K2.t8421 from rfl, totK_node, tot8420, tot8421]
  decide +kernel

theorem arows8416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8416 = true := by
  rw [show D2M8K2.u8416 = KTree.node D2M8K2.t8422 (nat_lit 18256072) (nat_lit 3841397406) (nat_lit 0) D2M8K2.t8423 from rfl, allE_node, rows8422, irow8416, rows8423]
  all_goals rfl

theorem atot8416 : totK PD2M8K2 D2M8K2.u8416 = [0, 246852620806, 796827286247, 650575103506, 98233753941, 1164319620, 0, 0] := by
  rw [show D2M8K2.u8416 = KTree.node D2M8K2.t8422 (nat_lit 18256072) (nat_lit 3841397406) (nat_lit 0) D2M8K2.t8423 from rfl, totK_node, tot8422, tot8423]
  decide +kernel

theorem arows8419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8419 = true := by
  rw [show D2M8K2.u8419 = KTree.node D2M8K2.t8424 (nat_lit 18257772) (nat_lit 3444609635) (nat_lit 0) D2M8K2.t8425 from rfl, allE_node, rows8424, irow8419, rows8425]
  all_goals rfl

theorem atot8419 : totK PD2M8K2 D2M8K2.u8419 = [0, 153001941291, 634010460948, 753098585853, 220791430374, 11885407614, 0, 0] := by
  rw [show D2M8K2.u8419 = KTree.node D2M8K2.t8424 (nat_lit 18257772) (nat_lit 3444609635) (nat_lit 0) D2M8K2.t8425 from rfl, totK_node, tot8424, tot8425]
  decide +kernel

theorem arows8420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8420 = true := by
  rw [show D2M8K2.u8420 = KTree.node D2M8K2.t8426 (nat_lit 18262678) (nat_lit 2583317283) (nat_lit 0) D2M8K2.t8427 from rfl, allE_node, rows8426, irow8420, rows8427]
  all_goals rfl

theorem atot8420 : totK PD2M8K2 D2M8K2.u8420 = [0, 243947510850, 792498596490, 642937471247, 91394965568, 1096505104, 0, 0] := by
  rw [show D2M8K2.u8420 = KTree.node D2M8K2.t8426 (nat_lit 18262678) (nat_lit 2583317283) (nat_lit 0) D2M8K2.t8427 from rfl, totK_node, tot8426, tot8427]
  decide +kernel

theorem arows8422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8422 = true := by
  rw [show D2M8K2.u8422 = KTree.node D2M8K2.t8428 (nat_lit 18265013) (nat_lit 2374301204) (nat_lit 0) D2M8K2.t8429 from rfl, allE_node, rows8428, irow8422, rows8429]
  all_goals rfl

theorem atot8422 : totK PD2M8K2 D2M8K2.u8422 = [0, 223798655193, 740764338945, 701356813771, 130741757091, 3820764243, 0, 0] := by
  rw [show D2M8K2.u8422 = KTree.node D2M8K2.t8428 (nat_lit 18265013) (nat_lit 2374301204) (nat_lit 0) D2M8K2.t8429 from rfl, totK_node, tot8428, tot8429]
  decide +kernel

theorem arows8423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8423 = true := by
  rw [show D2M8K2.u8423 = KTree.node D2M8K2.t8430 (nat_lit 18266575) (nat_lit 2032180899) (nat_lit 0) D2M8K2.t8431 from rfl, allE_node, rows8430, irow8423, rows8431]
  all_goals rfl

theorem atot8423 : totK PD2M8K2 D2M8K2.u8423 = [0, 178807734416, 758316738571, 741023776233, 126420100730, 1232398321, 0, 0] := by
  rw [show D2M8K2.u8423 = KTree.node D2M8K2.t8430 (nat_lit 18266575) (nat_lit 2032180899) (nat_lit 0) D2M8K2.t8431 from rfl, totK_node, tot8430, tot8431]
  decide +kernel

theorem arows8427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8427 = true := by
  rw [show D2M8K2.u8427 = KTree.node D2M8K2.t8432 (nat_lit 18289174) (nat_lit 3547600099) (nat_lit 0) D2M8K2.t8433 from rfl, allE_node, rows8432, irow8427, rows8433]
  all_goals rfl

theorem atot8427 : totK PD2M8K2 D2M8K2.u8427 = [0, 230725852455, 678291704218, 652206685943, 202846589689, 12451903996, 0, 0] := by
  rw [show D2M8K2.u8427 = KTree.node D2M8K2.t8432 (nat_lit 18289174) (nat_lit 3547600099) (nat_lit 0) D2M8K2.t8433 from rfl, totK_node, tot8432, tot8433]
  decide +kernel

theorem arows8428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8428 = true := by
  rw [show D2M8K2.u8428 = KTree.node D2M8K2.t8434 (nat_lit 18290728) (nat_lit 3715870945) (nat_lit 0) D2M8K2.t8435 from rfl, allE_node, rows8434, irow8428, rows8435]
  all_goals rfl

theorem atot8428 : totK PD2M8K2 D2M8K2.u8428 = [0, 189009670259, 758456984556, 709675637056, 119097656663, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8428 = KTree.node D2M8K2.t8434 (nat_lit 18290728) (nat_lit 3715870945) (nat_lit 0) D2M8K2.t8435 from rfl, totK_node, tot8434, tot8435]
  decide +kernel

theorem arows8430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8430 = true := by
  rw [show D2M8K2.u8430 = KTree.node D2M8K2.t8436 (nat_lit 18293083) (nat_lit 1704771153) (nat_lit 0) D2M8K2.t8437 from rfl, allE_node, rows8436, irow8430, rows8437]
  all_goals rfl

theorem atot8430 : totK PD2M8K2 D2M8K2.u8430 = [0, 261879954844, 832580806666, 675390292267, 76428412120, 0, 0, 0] := by
  rw [show D2M8K2.u8430 = KTree.node D2M8K2.t8436 (nat_lit 18293083) (nat_lit 1704771153) (nat_lit 0) D2M8K2.t8437 from rfl, totK_node, tot8436, tot8437]
  decide +kernel

theorem arows8431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8431 = true := by
  rw [show D2M8K2.u8431 = KTree.node D2M8K2.t8438 (nat_lit 18295273) (nat_lit 1404844726) (nat_lit 0) D2M8K2.t8439 from rfl, allE_node, rows8438, irow8431, rows8439]
  all_goals rfl

theorem atot8431 : totK PD2M8K2 D2M8K2.u8431 = [0, 84636189914, 627275754098, 884770337987, 218528032074, 5348807592, 0, 0] := by
  rw [show D2M8K2.u8431 = KTree.node D2M8K2.t8438 (nat_lit 18295273) (nat_lit 1404844726) (nat_lit 0) D2M8K2.t8439 from rfl, totK_node, tot8438, tot8439]
  decide +kernel

theorem arows8434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8434 = true := by
  rw [show D2M8K2.u8434 = KTree.node D2M8K2.t8440 (nat_lit 18300411) (nat_lit 3755701842) (nat_lit 0) D2M8K2.t8441 from rfl, allE_node, rows8440, irow8434, rows8441]
  all_goals rfl

theorem atot8434 : totK PD2M8K2 D2M8K2.u8434 = [0, 388194643960, 947333910598, 469971119416, 33241914962, 0, 0, 0] := by
  rw [show D2M8K2.u8434 = KTree.node D2M8K2.t8440 (nat_lit 18300411) (nat_lit 3755701842) (nat_lit 0) D2M8K2.t8441 from rfl, totK_node, tot8440, tot8441]
  decide +kernel

theorem arows8435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8435 = true := by
  rw [show D2M8K2.u8435 = KTree.node D2M8K2.t8442 (nat_lit 18301641) (nat_lit 1892123624) (nat_lit 0) D2M8K2.t8443 from rfl, allE_node, rows8442, irow8435, rows8443]
  all_goals rfl

theorem atot8435 : totK PD2M8K2 D2M8K2.u8435 = [0, 52088170802, 526037948860, 915128209445, 275007596505, 11639431793, 0, 0] := by
  rw [show D2M8K2.u8435 = KTree.node D2M8K2.t8442 (nat_lit 18301641) (nat_lit 1892123624) (nat_lit 0) D2M8K2.t8443 from rfl, totK_node, tot8442, tot8443]
  decide +kernel

theorem arows8437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8437 = true := by
  rw [show D2M8K2.u8437 = KTree.node D2M8K2.t8444 (nat_lit 18303448) (nat_lit 3446768173) (nat_lit 0) D2M8K2.t8445 from rfl, allE_node, rows8444, irow8437, rows8445]
  all_goals rfl

theorem atot8437 : totK PD2M8K2 D2M8K2.u8437 = [0, 318458467283, 872414878881, 546577116543, 64186511203, 1531244125, 0, 0] := by
  rw [show D2M8K2.u8437 = KTree.node D2M8K2.t8444 (nat_lit 18303448) (nat_lit 3446768173) (nat_lit 0) D2M8K2.t8445 from rfl, totK_node, tot8444, tot8445]
  decide +kernel

theorem arows8438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8438 = true := by
  rw [show D2M8K2.u8438 = KTree.node D2M8K2.t8446 (nat_lit 18305038) (nat_lit 3551827188) (nat_lit 0) D2M8K2.t8447 from rfl, allE_node, rows8446, irow8438, rows8447]
  all_goals rfl

theorem atot8438 : totK PD2M8K2 D2M8K2.u8438 = [0, 90494398135, 658406424235, 879405551340, 151402915709, 2165917952, 0, 0] := by
  rw [show D2M8K2.u8438 = KTree.node D2M8K2.t8446 (nat_lit 18305038) (nat_lit 3551827188) (nat_lit 0) D2M8K2.t8447 from rfl, totK_node, tot8446, tot8447]
  decide +kernel

theorem arows8446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8446 = true := by
  rw [show D2M8K2.u8446 = KTree.node D2M8K2.t8448 (nat_lit 18307002) (nat_lit 3555237503) (nat_lit 0) D2M8K2.t8449 from rfl, allE_node, rows8448, irow8446, rows8449]
  all_goals rfl

theorem atot8446 : totK PD2M8K2 D2M8K2.u8446 = [0, 372187602005, 896261112030, 484553850932, 65435600424, 2751766863, 0, 0] := by
  rw [show D2M8K2.u8446 = KTree.node D2M8K2.t8448 (nat_lit 18307002) (nat_lit 3555237503) (nat_lit 0) D2M8K2.t8449 from rfl, totK_node, tot8448, tot8449]
  decide +kernel

theorem arows8447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8447 = true := by
  rw [show D2M8K2.u8447 = KTree.node D2M8K2.t8450 (nat_lit 18308568) (nat_lit 2903563889) (nat_lit 0) D2M8K2.t8451 from rfl, allE_node, rows8450, irow8447, rows8451]
  all_goals rfl

theorem atot8447 : totK PD2M8K2 D2M8K2.u8447 = [0, 38279877783, 582751329130, 943033244572, 228313654384, 4957057700, 0, 0] := by
  rw [show D2M8K2.u8447 = KTree.node D2M8K2.t8450 (nat_lit 18308568) (nat_lit 2903563889) (nat_lit 0) D2M8K2.t8451 from rfl, totK_node, tot8450, tot8451]
  decide +kernel

theorem arows8449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8449 = true := by
  rw [show D2M8K2.u8449 = KTree.node D2M8K2.t8452 (nat_lit 18331395) (nat_lit 2900354658) (nat_lit 0) D2M8K2.t8453 from rfl, allE_node, rows8452, irow8449, rows8453]
  all_goals rfl

theorem atot8449 : totK PD2M8K2 D2M8K2.u8449 = [0, 347267947858, 858445277223, 459081911917, 100919595289, 8757608180, 0, 0] := by
  rw [show D2M8K2.u8449 = KTree.node D2M8K2.t8452 (nat_lit 18331395) (nat_lit 2900354658) (nat_lit 0) D2M8K2.t8453 from rfl, totK_node, tot8452, tot8453]
  decide +kernel

theorem arows8450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8450 = true := by
  rw [show D2M8K2.u8450 = KTree.node D2M8K2.t8454 (nat_lit 18332957) (nat_lit 2314132247) (nat_lit 0) D2M8K2.t8455 from rfl, allE_node, rows8454, irow8450, rows8455]
  all_goals rfl

theorem atot8450 : totK PD2M8K2 D2M8K2.u8450 = [0, 95976148077, 647534758280, 871048566783, 154231306797, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8450 = KTree.node D2M8K2.t8454 (nat_lit 18332957) (nat_lit 2314132247) (nat_lit 0) D2M8K2.t8455 from rfl, totK_node, tot8454, tot8455]
  decide +kernel

theorem arows8453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8453 = true := by
  rw [show D2M8K2.u8453 = KTree.node D2M8K2.t8456 (nat_lit 18335034) (nat_lit 3940882266) (nat_lit 0) D2M8K2.t8457 from rfl, allE_node, rows8456, irow8453, rows8457]
  all_goals rfl

theorem atot8453 : totK PD2M8K2 D2M8K2.u8453 = [0, 303063840477, 883029794262, 586855155854, 62216797950, 0, 0, 0] := by
  rw [show D2M8K2.u8453 = KTree.node D2M8K2.t8456 (nat_lit 18335034) (nat_lit 3940882266) (nat_lit 0) D2M8K2.t8457 from rfl, totK_node, tot8456, tot8457]
  decide +kernel

theorem arows8454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8454 = true := by
  rw [show D2M8K2.u8454 = KTree.node D2M8K2.t8458 (nat_lit 18337596) (nat_lit 3251093975) (nat_lit 0) D2M8K2.t8459 from rfl, allE_node, rows8458, irow8454, rows8459]
  all_goals rfl

theorem atot8454 : totK PD2M8K2 D2M8K2.u8454 = [0, 235434782907, 751523032474, 698383511109, 131234913445, 1409560813, 0, 0] := by
  rw [show D2M8K2.u8454 = KTree.node D2M8K2.t8458 (nat_lit 18337596) (nat_lit 3251093975) (nat_lit 0) D2M8K2.t8459 from rfl, totK_node, tot8458, tot8459]
  decide +kernel

theorem arows8456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8456 = true := by
  rw [show D2M8K2.u8456 = KTree.node D2M8K2.t8460 (nat_lit 18339247) (nat_lit 1686441507) (nat_lit 0) D2M8K2.t8461 from rfl, allE_node, rows8460, irow8456, rows8461]
  all_goals rfl

theorem atot8456 : totK PD2M8K2 D2M8K2.u8456 = [0, 144215413515, 698184353847, 768402219302, 146948334038, 2309606161, 0, 0] := by
  rw [show D2M8K2.u8456 = KTree.node D2M8K2.t8460 (nat_lit 18339247) (nat_lit 1686441507) (nat_lit 0) D2M8K2.t8461 from rfl, totK_node, tot8460, tot8461]
  decide +kernel

theorem arows8457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8457 = true := by
  rw [show D2M8K2.u8457 = KTree.node D2M8K2.t8462 (nat_lit 18341146) (nat_lit 3711780228) (nat_lit 0) D2M8K2.t8463 from rfl, allE_node, rows8462, irow8457, rows8463]
  all_goals rfl

theorem atot8457 : totK PD2M8K2 D2M8K2.u8457 = [0, 256393463935, 741855908115, 618347805830, 152123923532, 10673843635, 0, 0] := by
  rw [show D2M8K2.u8457 = KTree.node D2M8K2.t8462 (nat_lit 18341146) (nat_lit 3711780228) (nat_lit 0) D2M8K2.t8463 from rfl, totK_node, tot8462, tot8463]
  decide +kernel

theorem arows8461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8461 = true := by
  rw [show D2M8K2.u8461 = KTree.node D2M8K2.t8464 (nat_lit 18342727) (nat_lit 2376173763) (nat_lit 0) D2M8K2.t8465 from rfl, allE_node, rows8464, irow8461, rows8465]
  all_goals rfl

theorem atot8461 : totK PD2M8K2 D2M8K2.u8461 = [0, 156696092151, 704128412747, 781642037268, 151288116531, 2348440009, 0, 0] := by
  rw [show D2M8K2.u8461 = KTree.node D2M8K2.t8464 (nat_lit 18342727) (nat_lit 2376173763) (nat_lit 0) D2M8K2.t8465 from rfl, totK_node, tot8464, tot8465]
  decide +kernel

theorem arows8462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8462 = true := by
  rw [show D2M8K2.u8462 = KTree.node D2M8K2.t8466 (nat_lit 18344584) (nat_lit 3543620671) (nat_lit 0) D2M8K2.t8467 from rfl, allE_node, rows8466, irow8462, rows8467]
  all_goals rfl

theorem atot8462 : totK PD2M8K2 D2M8K2.u8462 = [0, 255166178469, 740328814328, 623459685700, 154581309057, 10835877391, 0, 0] := by
  rw [show D2M8K2.u8462 = KTree.node D2M8K2.t8466 (nat_lit 18344584) (nat_lit 3543620671) (nat_lit 0) D2M8K2.t8467 from rfl, totK_node, tot8466, tot8467]
  decide +kernel

theorem arows8464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8464 = true := by
  rw [show D2M8K2.u8464 = KTree.node D2M8K2.t8468 (nat_lit 18345773) (nat_lit 2023480268) (nat_lit 0) D2M8K2.t8469 from rfl, allE_node, rows8468, irow8464, rows8469]
  all_goals rfl

theorem atot8464 : totK PD2M8K2 D2M8K2.u8464 = [0, 179781826033, 767321033698, 745095123059, 108323087494, 1096505104, 0, 0] := by
  rw [show D2M8K2.u8464 = KTree.node D2M8K2.t8468 (nat_lit 18345773) (nat_lit 2023480268) (nat_lit 0) D2M8K2.t8469 from rfl, totK_node, tot8468, tot8469]
  decide +kernel

theorem arows8465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8465 = true := by
  rw [show D2M8K2.u8465 = KTree.node D2M8K2.t8470 (nat_lit 18372226) (nat_lit 4124157814) (nat_lit 0) D2M8K2.t8471 from rfl, allE_node, rows8470, irow8465, rows8471]
  all_goals rfl

theorem atot8465 : totK PD2M8K2 D2M8K2.u8465 = [0, 259817421353, 782981186959, 612386076614, 121082944248, 3884009855, 0, 0] := by
  rw [show D2M8K2.u8465 = KTree.node D2M8K2.t8470 (nat_lit 18372226) (nat_lit 4124157814) (nat_lit 0) D2M8K2.t8471 from rfl, totK_node, tot8470, tot8471]
  decide +kernel

theorem arows8468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8468 = true := by
  rw [show D2M8K2.u8468 = KTree.node D2M8K2.t8472 (nat_lit 18373774) (nat_lit 3575949745) (nat_lit 0) D2M8K2.t8473 from rfl, allE_node, rows8472, irow8468, rows8473]
  all_goals rfl

theorem atot8468 : totK PD2M8K2 D2M8K2.u8468 = [0, 158453285720, 725417538186, 770982531929, 126609516238, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8468 = KTree.node D2M8K2.t8472 (nat_lit 18373774) (nat_lit 3575949745) (nat_lit 0) D2M8K2.t8473 from rfl, totK_node, tot8472, tot8473]
  decide +kernel

theorem arows8469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8469 = true := by
  rw [show D2M8K2.u8469 = KTree.node D2M8K2.t8474 (nat_lit 18376116) (nat_lit 1178301025) (nat_lit 0) D2M8K2.t8475 from rfl, allE_node, rows8474, irow8469, rows8475]
  all_goals rfl

theorem atot8469 : totK PD2M8K2 D2M8K2.u8469 = [0, 294681824041, 851558693800, 628630504295, 68824864845, 0, 0, 0] := by
  rw [show D2M8K2.u8469 = KTree.node D2M8K2.t8474 (nat_lit 18376116) (nat_lit 1178301025) (nat_lit 0) D2M8K2.t8475 from rfl, totK_node, tot8474, tot8475]
  decide +kernel

theorem arows8471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8471 = true := by
  rw [show D2M8K2.u8471 = KTree.node D2M8K2.t8476 (nat_lit 18378152) (nat_lit 2546837743) (nat_lit 0) D2M8K2.t8477 from rfl, allE_node, rows8476, irow8471, rows8477]
  all_goals rfl

theorem atot8471 : totK PD2M8K2 D2M8K2.u8471 = [0, 88468426186, 556682247553, 879639157545, 283177545325, 9575627623, 0, 0] := by
  rw [show D2M8K2.u8471 = KTree.node D2M8K2.t8476 (nat_lit 18378152) (nat_lit 2546837743) (nat_lit 0) D2M8K2.t8477 from rfl, totK_node, tot8476, tot8477]
  decide +kernel

theorem arows8472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8472 = true := by
  rw [show D2M8K2.u8472 = KTree.node D2M8K2.t8478 (nat_lit 18379734) (nat_lit 2565490322) (nat_lit 0) D2M8K2.t8479 from rfl, allE_node, rows8478, irow8472, rows8479]
  all_goals rfl

theorem atot8472 : totK PD2M8K2 D2M8K2.u8472 = [0, 330594673880, 905752553294, 520983521007, 41453706707, 0, 0, 0] := by
  rw [show D2M8K2.u8472 = KTree.node D2M8K2.t8478 (nat_lit 18379734) (nat_lit 2565490322) (nat_lit 0) D2M8K2.t8479 from rfl, totK_node, tot8478, tot8479]
  decide +kernel

theorem arows8477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8477 = true := by
  rw [show D2M8K2.u8477 = KTree.node D2M8K2.t8480 (nat_lit 18381518) (nat_lit 2521907480) (nat_lit 0) D2M8K2.t8481 from rfl, allE_node, rows8480, irow8477, rows8481]
  all_goals rfl

theorem atot8477 : totK PD2M8K2 D2M8K2.u8477 = [0, 111581961659, 629520523267, 846702192907, 198876876232, 5138457373, 0, 0] := by
  rw [show D2M8K2.u8477 = KTree.node D2M8K2.t8480 (nat_lit 18381518) (nat_lit 2521907480) (nat_lit 0) D2M8K2.t8481 from rfl, totK_node, tot8480, tot8481]
  decide +kernel

theorem arows8478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8478 = true := by
  rw [show D2M8K2.u8478 = KTree.node D2M8K2.t8482 (nat_lit 18383658) (nat_lit 3837723114) (nat_lit 0) D2M8K2.t8483 from rfl, allE_node, rows8482, irow8478, rows8483]
  all_goals rfl

theorem atot8478 : totK PD2M8K2 D2M8K2.u8478 = [0, 302607883720, 884734125932, 580259452703, 56023469902, 0, 0, 0] := by
  rw [show D2M8K2.u8478 = KTree.node D2M8K2.t8482 (nat_lit 18383658) (nat_lit 3837723114) (nat_lit 0) D2M8K2.t8483 from rfl, totK_node, tot8482, tot8483]
  decide +kernel

theorem arows8480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8480 = true := by
  rw [show D2M8K2.u8480 = KTree.node D2M8K2.t8484 (nat_lit 18385417) (nat_lit 1455194511) (nat_lit 0) D2M8K2.t8485 from rfl, allE_node, rows8484, irow8480, rows8485]
  all_goals rfl

theorem atot8480 : totK PD2M8K2 D2M8K2.u8480 = [0, 152999581501, 653729786588, 805626157266, 198565437092, 5193381917, 0, 0] := by
  rw [show D2M8K2.u8480 = KTree.node D2M8K2.t8484 (nat_lit 18385417) (nat_lit 1455194511) (nat_lit 0) D2M8K2.t8485 from rfl, totK_node, tot8484, tot8485]
  decide +kernel

theorem arows8481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8481 = true := by
  rw [show D2M8K2.u8481 = KTree.node D2M8K2.t8486 (nat_lit 18390349) (nat_lit 1084498368) (nat_lit 0) D2M8K2.t8487 from rfl, allE_node, rows8486, irow8481, rows8487]
  all_goals rfl

theorem atot8481 : totK PD2M8K2 D2M8K2.u8481 = [0, 286292535038, 877972483091, 606778043663, 54060974869, 0, 0, 0] := by
  rw [show D2M8K2.u8481 = KTree.node D2M8K2.t8486 (nat_lit 18390349) (nat_lit 1084498368) (nat_lit 0) D2M8K2.t8487 from rfl, totK_node, tot8486, tot8487]
  decide +kernel

theorem arows8484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8484 = true := by
  rw [show D2M8K2.u8484 = KTree.node D2M8K2.t8488 (nat_lit 18391998) (nat_lit 3959304808) (nat_lit 0) D2M8K2.t8489 from rfl, allE_node, rows8488, irow8484, rows8489]
  all_goals rfl

theorem atot8484 : totK PD2M8K2 D2M8K2.u8484 = [38616506213, 44737627256, 379214032270, 913275003453, 380135937489, 21897291087, 0, 0] := by
  rw [show D2M8K2.u8484 = KTree.node D2M8K2.t8488 (nat_lit 18391998) (nat_lit 3959304808) (nat_lit 0) D2M8K2.t8489 from rfl, totK_node, tot8488, tot8489]
  decide +kernel

theorem arows8485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8485 = true := by
  rw [show D2M8K2.u8485 = KTree.node D2M8K2.t8490 (nat_lit 18459389) (nat_lit 1843564964) (nat_lit 0) D2M8K2.t8491 from rfl, allE_node, rows8490, irow8485, rows8491]
  all_goals rfl

theorem atot8485 : totK PD2M8K2 D2M8K2.u8485 = [362089844258, 930518185460, 508248917286, 41944776838, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8485 = KTree.node D2M8K2.t8490 (nat_lit 18459389) (nat_lit 1843564964) (nat_lit 0) D2M8K2.t8491 from rfl, totK_node, tot8490, tot8491]
  decide +kernel

theorem arows8487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8487 = true := by
  rw [show D2M8K2.u8487 = KTree.node D2M8K2.t8492 (nat_lit 18460827) (nat_lit 3765844345) (nat_lit 0) D2M8K2.t8493 from rfl, allE_node, rows8492, irow8487, rows8493]
  all_goals rfl

theorem atot8487 : totK PD2M8K2 D2M8K2.u8487 = [48724726441, 494180239987, 872431750126, 386520565614, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u8487 = KTree.node D2M8K2.t8492 (nat_lit 18460827) (nat_lit 3765844345) (nat_lit 0) D2M8K2.t8493 from rfl, totK_node, tot8492, tot8493]
  decide +kernel

theorem arows8488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8488 = true := by
  rw [show D2M8K2.u8488 = KTree.node D2M8K2.t8494 (nat_lit 18462198) (nat_lit 2744551324) (nat_lit 0) D2M8K2.t8495 from rfl, allE_node, rows8494, irow8488, rows8495]
  all_goals rfl

theorem atot8488 : totK PD2M8K2 D2M8K2.u8488 = [233036235967, 690635760795, 679802686714, 215575097801, 8214505460, 0, 0, 0] := by
  rw [show D2M8K2.u8488 = KTree.node D2M8K2.t8494 (nat_lit 18462198) (nat_lit 2744551324) (nat_lit 0) D2M8K2.t8495 from rfl, totK_node, tot8494, tot8495]
  decide +kernel

theorem arows8492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8492 = true := by
  rw [show D2M8K2.u8492 = KTree.node D2M8K2.t8496 (nat_lit 18463660) (nat_lit 3832638052) (nat_lit 0) D2M8K2.t8497 from rfl, allE_node, rows8496, irow8492, rows8497]
  all_goals rfl

theorem atot8492 : totK PD2M8K2 D2M8K2.u8492 = [171140408864, 703280107561, 743117715021, 161746101932, 5890129376, 0, 0, 0] := by
  rw [show D2M8K2.u8492 = KTree.node D2M8K2.t8496 (nat_lit 18463660) (nat_lit 3832638052) (nat_lit 0) D2M8K2.t8497 from rfl, totK_node, tot8496, tot8497]
  decide +kernel

theorem arows8493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8493 = true := by
  rw [show D2M8K2.u8493 = KTree.node D2M8K2.t8498 (nat_lit 18465570) (nat_lit 2829872531) (nat_lit 0) D2M8K2.t8499 from rfl, allE_node, rows8498, irow8493, rows8499]
  all_goals rfl

theorem atot8493 : totK PD2M8K2 D2M8K2.u8493 = [250320230748, 758207509586, 650591818227, 142940381823, 5775380855, 0, 0, 0] := by
  rw [show D2M8K2.u8493 = KTree.node D2M8K2.t8498 (nat_lit 18465570) (nat_lit 2829872531) (nat_lit 0) D2M8K2.t8499 from rfl, totK_node, tot8498, tot8499]
  decide +kernel

theorem arows8495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8495 = true := by
  rw [show D2M8K2.u8495 = KTree.node D2M8K2.t8500 (nat_lit 18467066) (nat_lit 3979444259) (nat_lit 0) D2M8K2.t8501 from rfl, allE_node, rows8500, irow8495, rows8501]
  all_goals rfl

theorem atot8495 : totK PD2M8K2 D2M8K2.u8495 = [173317023195, 749057274703, 758259444232, 132131021685, 1190718505, 0, 0, 0] := by
  rw [show D2M8K2.u8495 = KTree.node D2M8K2.t8500 (nat_lit 18467066) (nat_lit 3979444259) (nat_lit 0) D2M8K2.t8501 from rfl, totK_node, tot8500, tot8501]
  decide +kernel

theorem arows8496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8496 = true := by
  rw [show D2M8K2.u8496 = KTree.node D2M8K2.t8502 (nat_lit 18468929) (nat_lit 2218381755) (nat_lit 0) D2M8K2.t8503 from rfl, allE_node, rows8502, irow8496, rows8503]
  all_goals rfl

theorem atot8496 : totK PD2M8K2 D2M8K2.u8496 = [225888613902, 668908537371, 675921304266, 209152358275, 12003981235, 0, 0, 0] := by
  rw [show D2M8K2.u8496 = KTree.node D2M8K2.t8502 (nat_lit 18468929) (nat_lit 2218381755) (nat_lit 0) D2M8K2.t8503 from rfl, totK_node, tot8502, tot8503]
  decide +kernel

theorem arows8499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8499 = true := by
  rw [show D2M8K2.u8499 = KTree.node D2M8K2.t8504 (nat_lit 18470118) (nat_lit 3823146296) (nat_lit 0) D2M8K2.t8505 from rfl, allE_node, rows8504, irow8499, rows8505]
  all_goals rfl

theorem atot8499 : totK PD2M8K2 D2M8K2.u8499 = [191709425606, 787317366467, 704364309038, 106214602299, 1092001298, 0, 0, 0] := by
  rw [show D2M8K2.u8499 = KTree.node D2M8K2.t8504 (nat_lit 18470118) (nat_lit 3823146296) (nat_lit 0) D2M8K2.t8505 from rfl, totK_node, tot8504, tot8505]
  decide +kernel

theorem arows8500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8500 = true := by
  rw [show D2M8K2.u8500 = KTree.node D2M8K2.t8506 (nat_lit 18472458) (nat_lit 3767399519) (nat_lit 0) D2M8K2.t8507 from rfl, allE_node, rows8506, irow8500, rows8507]
  all_goals rfl

theorem atot8500 : totK PD2M8K2 D2M8K2.u8500 = [243110089169, 753547667035, 674633707630, 136040511837, 3867150671, 0, 0, 0] := by
  rw [show D2M8K2.u8500 = KTree.node D2M8K2.t8506 (nat_lit 18472458) (nat_lit 3767399519) (nat_lit 0) D2M8K2.t8507 from rfl, totK_node, tot8506, tot8507]
  decide +kernel

theorem arows8502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8502 = true := by
  rw [show D2M8K2.u8502 = KTree.node D2M8K2.t8508 (nat_lit 18473936) (nat_lit 3028361899) (nat_lit 0) D2M8K2.t8509 from rfl, allE_node, rows8508, irow8502, rows8509]
  all_goals rfl

theorem atot8502 : totK PD2M8K2 D2M8K2.u8502 = [179781219229, 754789284083, 747407584114, 129628738651, 1260002070, 0, 0, 0] := by
  rw [show D2M8K2.u8502 = KTree.node D2M8K2.t8508 (nat_lit 18473936) (nat_lit 3028361899) (nat_lit 0) D2M8K2.t8509 from rfl, totK_node, tot8508, tot8509]
  decide +kernel

theorem arows8503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8503 = true := by
  rw [show D2M8K2.u8503 = KTree.node D2M8K2.t8510 (nat_lit 18475642) (nat_lit 3911639042) (nat_lit 0) D2M8K2.t8511 from rfl, allE_node, rows8510, irow8503, rows8511]
  all_goals rfl

theorem atot8503 : totK PD2M8K2 D2M8K2.u8503 = [0, 368610261228, 914190355654, 476752045299, 42649695216, 0, 0, 0] := by
  rw [show D2M8K2.u8503 = KTree.node D2M8K2.t8510 (nat_lit 18475642) (nat_lit 3911639042) (nat_lit 0) D2M8K2.t8511 from rfl, totK_node, tot8510, tot8511]
  decide +kernel

theorem arows8509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8509 = true := by
  rw [show D2M8K2.u8509 = KTree.node D2M8K2.t8512 (nat_lit 18480532) (nat_lit 3373863816) (nat_lit 0) D2M8K2.t8513 from rfl, allE_node, rows8512, irow8509, rows8513]
  all_goals rfl

theorem atot8509 : totK PD2M8K2 D2M8K2.u8509 = [0, 272958351927, 884552285969, 616671276299, 67002353533, 0, 0, 0] := by
  rw [show D2M8K2.u8509 = KTree.node D2M8K2.t8512 (nat_lit 18480532) (nat_lit 3373863816) (nat_lit 0) D2M8K2.t8513 from rfl, totK_node, tot8512, tot8513]
  decide +kernel

theorem arows8510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8510 = true := by
  rw [show D2M8K2.u8510 = KTree.node D2M8K2.t8514 (nat_lit 18482003) (nat_lit 2570817658) (nat_lit 0) D2M8K2.t8515 from rfl, allE_node, rows8514, irow8510, rows8515]
  all_goals rfl

theorem atot8510 : totK PD2M8K2 D2M8K2.u8510 = [0, 0, 348585651118, 928144749141, 467458252746, 32664942840, 0, 0] := by
  rw [show D2M8K2.u8510 = KTree.node D2M8K2.t8514 (nat_lit 18482003) (nat_lit 2570817658) (nat_lit 0) D2M8K2.t8515 from rfl, totK_node, tot8514, tot8515]
  decide +kernel

theorem arows8512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8512 = true := by
  rw [show D2M8K2.u8512 = KTree.node D2M8K2.t8516 (nat_lit 18483362) (nat_lit 4014791921) (nat_lit 0) D2M8K2.t8517 from rfl, allE_node, rows8516, irow8512, rows8517]
  all_goals rfl

theorem atot8512 : totK PD2M8K2 D2M8K2.u8512 = [0, 386369236379, 918335812329, 440633532494, 51649857813, 4256931014, 0, 0] := by
  rw [show D2M8K2.u8512 = KTree.node D2M8K2.t8516 (nat_lit 18483362) (nat_lit 4014791921) (nat_lit 0) D2M8K2.t8517 from rfl, totK_node, tot8516, tot8517]
  decide +kernel

theorem arows8513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8513 = true := by
  rw [show D2M8K2.u8513 = KTree.node D2M8K2.t8518 (nat_lit 18485168) (nat_lit 3458701465) (nat_lit 0) D2M8K2.t8519 from rfl, allE_node, rows8518, irow8513, rows8519]
  all_goals rfl

theorem atot8513 : totK PD2M8K2 D2M8K2.u8513 = [0, 78782349947, 606947176481, 876986506132, 206953452195, 5159868635, 0, 0] := by
  rw [show D2M8K2.u8513 = KTree.node D2M8K2.t8518 (nat_lit 18485168) (nat_lit 3458701465) (nat_lit 0) D2M8K2.t8519 from rfl, totK_node, tot8518, tot8519]
  decide +kernel

theorem arows8516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8516 = true := by
  rw [show D2M8K2.u8516 = KTree.node D2M8K2.t8520 (nat_lit 18487172) (nat_lit 2833300544) (nat_lit 0) D2M8K2.t8521 from rfl, allE_node, rows8520, irow8516, rows8521]
  all_goals rfl

theorem atot8516 : totK PD2M8K2 D2M8K2.u8516 = [0, 354755596088, 936156768195, 500392900785, 36655753747, 0, 0, 0] := by
  rw [show D2M8K2.u8516 = KTree.node D2M8K2.t8520 (nat_lit 18487172) (nat_lit 2833300544) (nat_lit 0) D2M8K2.t8521 from rfl, totK_node, tot8520, tot8521]
  decide +kernel

theorem arows8517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8517 = true := by
  rw [show D2M8K2.u8517 = KTree.node D2M8K2.t8522 (nat_lit 18489002) (nat_lit 3698227995) (nat_lit 0) D2M8K2.t8523 from rfl, allE_node, rows8522, irow8517, rows8523]
  all_goals rfl

theorem atot8517 : totK PD2M8K2 D2M8K2.u8517 = [0, 64203887364, 598664793396, 880284407697, 215156041644, 5218872685, 0, 0] := by
  rw [show D2M8K2.u8517 = KTree.node D2M8K2.t8522 (nat_lit 18489002) (nat_lit 3698227995) (nat_lit 0) D2M8K2.t8523 from rfl, totK_node, tot8522, tot8523]
  decide +kernel

theorem arows8519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8519 = true := by
  rw [show D2M8K2.u8519 = KTree.node D2M8K2.t8524 (nat_lit 18490429) (nat_lit 982248353) (nat_lit 0) D2M8K2.t8525 from rfl, allE_node, rows8524, irow8519, rows8525]
  all_goals rfl

theorem atot8519 : totK PD2M8K2 D2M8K2.u8519 = [0, 351494178596, 912759264022, 507254690357, 42589657362, 0, 0, 0] := by
  rw [show D2M8K2.u8519 = KTree.node D2M8K2.t8524 (nat_lit 18490429) (nat_lit 982248353) (nat_lit 0) D2M8K2.t8525 from rfl, totK_node, tot8524, tot8525]
  decide +kernel

theorem arows8520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8520 = true := by
  rw [show D2M8K2.u8520 = KTree.node D2M8K2.t8526 (nat_lit 18492493) (nat_lit 1231787675) (nat_lit 0) D2M8K2.t8527 from rfl, allE_node, rows8526, irow8520, rows8527]
  all_goals rfl

theorem atot8520 : totK PD2M8K2 D2M8K2.u8520 = [0, 156768896951, 711435564201, 800153345115, 137590953832, 1415142070, 0, 0] := by
  rw [show D2M8K2.u8520 = KTree.node D2M8K2.t8526 (nat_lit 18492493) (nat_lit 1231787675) (nat_lit 0) D2M8K2.t8527 from rfl, totK_node, tot8526, tot8527]
  decide +kernel

theorem arows8524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8524 = true := by
  rw [show D2M8K2.u8524 = KTree.node D2M8K2.t8528 (nat_lit 18494054) (nat_lit 3977827650) (nat_lit 0) D2M8K2.t8529 from rfl, allE_node, rows8528, irow8524, rows8529]
  all_goals rfl

theorem atot8524 : totK PD2M8K2 D2M8K2.u8524 = [0, 264151759511, 876644876689, 616723656308, 63332357356, 0, 0, 0] := by
  rw [show D2M8K2.u8524 = KTree.node D2M8K2.t8528 (nat_lit 18494054) (nat_lit 3977827650) (nat_lit 0) D2M8K2.t8529 from rfl, totK_node, tot8528, tot8529]
  decide +kernel

theorem arows8525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8525 = true := by
  rw [show D2M8K2.u8525 = KTree.node D2M8K2.t8530 (nat_lit 18496235) (nat_lit 2932832799) (nat_lit 0) D2M8K2.t8531 from rfl, allE_node, rows8530, irow8525, rows8531]
  all_goals rfl

theorem atot8525 : totK PD2M8K2 D2M8K2.u8525 = [93572267332, 241780322324, 459243212292, 734160176841, 256012270016, 9302370699, 0, 0] := by
  rw [show D2M8K2.u8525 = KTree.node D2M8K2.t8530 (nat_lit 18496235) (nat_lit 2932832799) (nat_lit 0) D2M8K2.t8531 from rfl, totK_node, tot8530, tot8531]
  decide +kernel

theorem arows8527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8527 = true := by
  rw [show D2M8K2.u8527 = KTree.node D2M8K2.t8532 (nat_lit 18501164) (nat_lit 3786797412) (nat_lit 0) D2M8K2.t8533 from rfl, allE_node, rows8532, irow8527, rows8533]
  all_goals rfl

theorem atot8527 : totK PD2M8K2 D2M8K2.u8527 = [335950370752, 904934669960, 529600883514, 51945047923, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8527 = KTree.node D2M8K2.t8532 (nat_lit 18501164) (nat_lit 3786797412) (nat_lit 0) D2M8K2.t8533 from rfl, totK_node, tot8532, tot8533]
  decide +kernel

theorem arows8528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8528 = true := by
  rw [show D2M8K2.u8528 = KTree.node D2M8K2.t8534 (nat_lit 18502651) (nat_lit 2235876877) (nat_lit 0) D2M8K2.t8535 from rfl, allE_node, rows8534, irow8528, rows8535]
  all_goals rfl

theorem atot8528 : totK PD2M8K2 D2M8K2.u8528 = [0, 383413515017, 942733600780, 453528144962, 30796745998, 0, 0, 0] := by
  rw [show D2M8K2.u8528 = KTree.node D2M8K2.t8534 (nat_lit 18502651) (nat_lit 2235876877) (nat_lit 0) D2M8K2.t8535 from rfl, totK_node, tot8534, tot8535]
  decide +kernel

theorem arows8531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8531 = true := by
  rw [show D2M8K2.u8531 = KTree.node D2M8K2.t8536 (nat_lit 18503954) (nat_lit 4088148442) (nat_lit 0) D2M8K2.t8537 from rfl, allE_node, rows8536, irow8531, rows8537]
  all_goals rfl

theorem atot8531 : totK PD2M8K2 D2M8K2.u8531 = [339576514919, 847037752851, 508049440181, 119411156334, 6800370819, 0, 0, 0] := by
  rw [show D2M8K2.u8531 = KTree.node D2M8K2.t8536 (nat_lit 18503954) (nat_lit 4088148442) (nat_lit 0) D2M8K2.t8537 from rfl, totK_node, tot8536, tot8537]
  decide +kernel

theorem arows8532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8532 = true := by
  rw [show D2M8K2.u8532 = KTree.node D2M8K2.t8538 (nat_lit 18505496) (nat_lit 3704549570) (nat_lit 0) D2M8K2.t8539 from rfl, allE_node, rows8538, irow8532, rows8539]
  all_goals rfl

theorem atot8532 : totK PD2M8K2 D2M8K2.u8532 = [87121289351, 579551009223, 867151093840, 244581874137, 10568566766, 0, 0, 0] := by
  rw [show D2M8K2.u8532 = KTree.node D2M8K2.t8538 (nat_lit 18505496) (nat_lit 3704549570) (nat_lit 0) D2M8K2.t8539 from rfl, totK_node, tot8538, tot8539]
  decide +kernel

theorem arows8534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8534 = true := by
  rw [show D2M8K2.u8534 = KTree.node D2M8K2.t8540 (nat_lit 18510796) (nat_lit 3836522516) (nat_lit 0) D2M8K2.t8541 from rfl, allE_node, rows8540, irow8534, rows8541]
  all_goals rfl

theorem atot8534 : totK PD2M8K2 D2M8K2.u8534 = [309697957814, 830720791636, 573964642548, 92407979742, 2481160468, 0, 0, 0] := by
  rw [show D2M8K2.u8534 = KTree.node D2M8K2.t8540 (nat_lit 18510796) (nat_lit 3836522516) (nat_lit 0) D2M8K2.t8541 from rfl, totK_node, tot8540, tot8541]
  decide +kernel

theorem arows8535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8535 = true := by
  rw [show D2M8K2.u8535 = KTree.node D2M8K2.t8542 (nat_lit 18512399) (nat_lit 2043520427) (nat_lit 0) D2M8K2.t8543 from rfl, allE_node, rows8542, irow8535, rows8543]
  all_goals rfl

theorem atot8535 : totK PD2M8K2 D2M8K2.u8535 = [90332340817, 672239993656, 859443578808, 164004210112, 2165917952, 0, 0, 0] := by
  rw [show D2M8K2.u8535 = KTree.node D2M8K2.t8542 (nat_lit 18512399) (nat_lit 2043520427) (nat_lit 0) D2M8K2.t8543 from rfl, totK_node, tot8542, tot8543]
  decide +kernel

theorem arows8540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8540 = true := by
  rw [show D2M8K2.u8540 = KTree.node D2M8K2.t8544 (nat_lit 18514362) (nat_lit 3512150182) (nat_lit 0) D2M8K2.t8545 from rfl, allE_node, rows8544, irow8540, rows8545]
  all_goals rfl

theorem atot8540 : totK PD2M8K2 D2M8K2.u8540 = [361508555134, 870900362738, 513476349521, 83325546010, 2814597007, 0, 0, 0] := by
  rw [show D2M8K2.u8540 = KTree.node D2M8K2.t8544 (nat_lit 18514362) (nat_lit 3512150182) (nat_lit 0) D2M8K2.t8545 from rfl, totK_node, tot8544, tot8545]
  decide +kernel

theorem arows8541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8541 = true := by
  rw [show D2M8K2.u8541 = KTree.node D2M8K2.t8546 (nat_lit 18515944) (nat_lit 3765870559) (nat_lit 0) D2M8K2.t8547 from rfl, allE_node, rows8546, irow8541, rows8547]
  all_goals rfl

theorem atot8541 : totK PD2M8K2 D2M8K2.u8541 = [44268419162, 538431997470, 917827725944, 283821879241, 8684927289, 0, 0, 0] := by
  rw [show D2M8K2.u8541 = KTree.node D2M8K2.t8546 (nat_lit 18515944) (nat_lit 3765870559) (nat_lit 0) D2M8K2.t8547 from rfl, totK_node, tot8546, tot8547]
  decide +kernel

theorem arows8543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8543 = true := by
  rw [show D2M8K2.u8543 = KTree.node D2M8K2.t8548 (nat_lit 18521320) (nat_lit 3897142704) (nat_lit 0) D2M8K2.t8549 from rfl, allE_node, rows8548, irow8543, rows8549]
  all_goals rfl

theorem atot8543 : totK PD2M8K2 D2M8K2.u8543 = [0, 362309599418, 912460223184, 505463989105, 46657356066, 0, 0, 0] := by
  rw [show D2M8K2.u8543 = KTree.node D2M8K2.t8548 (nat_lit 18521320) (nat_lit 3897142704) (nat_lit 0) D2M8K2.t8549 from rfl, totK_node, tot8548, tot8549]
  decide +kernel

theorem arows8544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8544 = true := by
  rw [show D2M8K2.u8544 = KTree.node D2M8K2.t8550 (nat_lit 18524354) (nat_lit 3378556279) (nat_lit 0) D2M8K2.t8551 from rfl, allE_node, rows8550, irow8544, rows8551]
  all_goals rfl

theorem atot8544 : totK PD2M8K2 D2M8K2.u8544 = [0, 352491820620, 948455654332, 487266531371, 32639835484, 0, 0, 0] := by
  rw [show D2M8K2.u8544 = KTree.node D2M8K2.t8550 (nat_lit 18524354) (nat_lit 3378556279) (nat_lit 0) D2M8K2.t8551 from rfl, totK_node, tot8550, tot8551]
  decide +kernel

theorem arows8547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8547 = true := by
  rw [show D2M8K2.u8547 = KTree.node D2M8K2.t8552 (nat_lit 18525869) (nat_lit 2149376973) (nat_lit 0) D2M8K2.t8553 from rfl, allE_node, rows8552, irow8547, rows8553]
  all_goals rfl

theorem atot8547 : totK PD2M8K2 D2M8K2.u8547 = [0, 172088500870, 721658571425, 723727261348, 148542594892, 2305904642, 0, 0] := by
  rw [show D2M8K2.u8547 = KTree.node D2M8K2.t8552 (nat_lit 18525869) (nat_lit 2149376973) (nat_lit 0) D2M8K2.t8553 from rfl, totK_node, tot8552, tot8553]
  decide +kernel

theorem arows8548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8548 = true := by
  rw [show D2M8K2.u8548 = KTree.node D2M8K2.t8554 (nat_lit 18531217) (nat_lit 1556893505) (nat_lit 0) D2M8K2.t8555 from rfl, allE_node, rows8554, irow8548, rows8555]
  all_goals rfl

theorem atot8548 : totK PD2M8K2 D2M8K2.u8548 = [0, 241359334918, 752522506780, 604189468934, 148981788856, 10710292732, 0, 0] := by
  rw [show D2M8K2.u8548 = KTree.node D2M8K2.t8554 (nat_lit 18531217) (nat_lit 1556893505) (nat_lit 0) D2M8K2.t8555 from rfl, totK_node, tot8554, tot8555]
  decide +kernel

theorem arows8550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8550 = true := by
  rw [show D2M8K2.u8550 = KTree.node D2M8K2.t8556 (nat_lit 18532853) (nat_lit 2366427889) (nat_lit 0) D2M8K2.t8557 from rfl, allE_node, rows8556, irow8550, rows8557]
  all_goals rfl

theorem atot8550 : totK PD2M8K2 D2M8K2.u8550 = [0, 157772069674, 777435758876, 711607060475, 95057867651, 1021600638, 0, 0] := by
  rw [show D2M8K2.u8550 = KTree.node D2M8K2.t8556 (nat_lit 18532853) (nat_lit 2366427889) (nat_lit 0) D2M8K2.t8557 from rfl, totK_node, tot8556, tot8557]
  decide +kernel

theorem arows8551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8551 = true := by
  rw [show D2M8K2.u8551 = KTree.node D2M8K2.t8558 (nat_lit 18535008) (nat_lit 2670913037) (nat_lit 0) D2M8K2.t8559 from rfl, allE_node, rows8558, irow8551, rows8559]
  all_goals rfl

theorem atot8551 : totK PD2M8K2 D2M8K2.u8551 = [0, 313179289438, 822510759729, 547168189812, 96040939611, 3552795014, 0, 0] := by
  rw [show D2M8K2.u8551 = KTree.node D2M8K2.t8558 (nat_lit 18535008) (nat_lit 2670913037) (nat_lit 0) D2M8K2.t8559 from rfl, totK_node, tot8558, tot8559]
  decide +kernel

theorem arows8555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8555 = true := by
  rw [show D2M8K2.u8555 = KTree.node D2M8K2.t8560 (nat_lit 18538849) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t8561 from rfl, allE_node, rows8560, irow8555, rows8561]
  all_goals rfl

theorem atot8555 : totK PD2M8K2 D2M8K2.u8555 = [290240873679, 788668445668, 557153717686, 169789817229, 13552619715, 0, 0, 0] := by
  rw [show D2M8K2.u8555 = KTree.node D2M8K2.t8560 (nat_lit 18538849) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t8561 from rfl, totK_node, tot8560, tot8561]
  decide +kernel

theorem arows8556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8556 = true := by
  rw [show D2M8K2.u8556 = KTree.node D2M8K2.t8562 (nat_lit 18540678) (nat_lit 3854587458) (nat_lit 0) D2M8K2.t8563 from rfl, allE_node, rows8562, irow8556, rows8563]
  all_goals rfl

theorem atot8556 : totK PD2M8K2 D2M8K2.u8556 = [144987525680, 705039573185, 822926924775, 151783315461, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8556 = KTree.node D2M8K2.t8562 (nat_lit 18540678) (nat_lit 3854587458) (nat_lit 0) D2M8K2.t8563 from rfl, totK_node, tot8562, tot8563]
  decide +kernel

theorem arows8558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8558 = true := by
  rw [show D2M8K2.u8558 = KTree.node D2M8K2.t8564 (nat_lit 18542568) (nat_lit 3250050697) (nat_lit 0) D2M8K2.t8565 from rfl, allE_node, rows8564, irow8558, rows8565]
  all_goals rfl

theorem atot8558 : totK PD2M8K2 D2M8K2.u8558 = [336970107059, 918840395912, 530397280670, 40973074618, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8558 = KTree.node D2M8K2.t8564 (nat_lit 18542568) (nat_lit 3250050697) (nat_lit 0) D2M8K2.t8565 from rfl, totK_node, tot8564, tot8565]
  decide +kernel

theorem arows8559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8559 = true := by
  rw [show D2M8K2.u8559 = KTree.node D2M8K2.t8566 (nat_lit 18544060) (nat_lit 3335411912) (nat_lit 0) D2M8K2.t8567 from rfl, allE_node, rows8566, irow8559, rows8567]
  all_goals rfl

theorem atot8559 : totK PD2M8K2 D2M8K2.u8559 = [0, 387362736987, 937923135865, 454701387378, 30795354140, 0, 0, 0] := by
  rw [show D2M8K2.u8559 = KTree.node D2M8K2.t8566 (nat_lit 18544060) (nat_lit 3335411912) (nat_lit 0) D2M8K2.t8567 from rfl, totK_node, tot8566, tot8567]
  decide +kernel

theorem arows8562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8562 = true := by
  rw [show D2M8K2.u8562 = KTree.node D2M8K2.t8568 (nat_lit 18548782) (nat_lit 4014667683) (nat_lit 0) D2M8K2.t8569 from rfl, allE_node, rows8568, irow8562, rows8569]
  all_goals rfl

theorem atot8562 : totK PD2M8K2 D2M8K2.u8562 = [341932421724, 831968532214, 533201471096, 130119811080, 6799735859, 0, 0, 0] := by
  rw [show D2M8K2.u8562 = KTree.node D2M8K2.t8568 (nat_lit 18548782) (nat_lit 4014667683) (nat_lit 0) D2M8K2.t8569 from rfl, totK_node, tot8568, tot8569]
  decide +kernel

theorem arows8563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8563 = true := by
  rw [show D2M8K2.u8563 = KTree.node D2M8K2.t8570 (nat_lit 18550231) (nat_lit 2207794610) (nat_lit 0) D2M8K2.t8571 from rfl, allE_node, rows8570, irow8563, rows8571]
  all_goals rfl

theorem atot8563 : totK PD2M8K2 D2M8K2.u8563 = [96163275464, 636391350603, 839771317201, 222545425010, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u8563 = KTree.node D2M8K2.t8570 (nat_lit 18550231) (nat_lit 2207794610) (nat_lit 0) D2M8K2.t8571 from rfl, totK_node, tot8570, tot8571]
  decide +kernel

theorem arows8565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8565 = true := by
  rw [show D2M8K2.u8565 = KTree.node D2M8K2.t8572 (nat_lit 18552078) (nat_lit 3686701214) (nat_lit 0) D2M8K2.t8573 from rfl, allE_node, rows8572, irow8565, rows8573]
  all_goals rfl

theorem atot8565 : totK PD2M8K2 D2M8K2.u8565 = [253499157174, 763582511752, 636424139584, 129099483093, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u8565 = KTree.node D2M8K2.t8572 (nat_lit 18552078) (nat_lit 3686701214) (nat_lit 0) D2M8K2.t8573 from rfl, totK_node, tot8572, tot8573]
  decide +kernel

theorem arows8566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8566 = true := by
  rw [show D2M8K2.u8566 = KTree.node D2M8K2.t8574 (nat_lit 18553609) (nat_lit 1506944971) (nat_lit 0) D2M8K2.t8575 from rfl, allE_node, rows8574, irow8566, rows8575]
  all_goals rfl

theorem atot8566 : totK PD2M8K2 D2M8K2.u8566 = [155067254286, 746073507909, 785927500486, 122125356243, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u8566 = KTree.node D2M8K2.t8574 (nat_lit 18553609) (nat_lit 1506944971) (nat_lit 0) D2M8K2.t8575 from rfl, totK_node, tot8574, tot8575]
  decide +kernel

theorem arows8573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8573 = true := by
  rw [show D2M8K2.u8573 = KTree.node D2M8K2.t8576 (nat_lit 18555632) (nat_lit 3483908264) (nat_lit 0) D2M8K2.t8577 from rfl, allE_node, rows8576, irow8573, rows8577]
  all_goals rfl

theorem atot8573 : totK PD2M8K2 D2M8K2.u8573 = [313468985359, 808545800282, 572458980578, 118385589488, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u8573 = KTree.node D2M8K2.t8576 (nat_lit 18555632) (nat_lit 3483908264) (nat_lit 0) D2M8K2.t8577 from rfl, totK_node, tot8576, tot8577]
  decide +kernel

theorem arows8574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8574 = true := by
  rw [show D2M8K2.u8574 = KTree.node D2M8K2.t8578 (nat_lit 18557124) (nat_lit 3299306638) (nat_lit 0) D2M8K2.t8579 from rfl, allE_node, rows8578, irow8574, rows8579]
  all_goals rfl

theorem atot8574 : totK PD2M8K2 D2M8K2.u8574 = [103714856752, 642814638812, 841477412935, 207214472695, 4813189065, 0, 0, 0] := by
  rw [show D2M8K2.u8574 = KTree.node D2M8K2.t8578 (nat_lit 18557124) (nat_lit 3299306638) (nat_lit 0) D2M8K2.t8579 from rfl, totK_node, tot8578, tot8579]
  decide +kernel

theorem arows8576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8576 = true := by
  rw [show D2M8K2.u8576 = KTree.node D2M8K2.t8580 (nat_lit 18558837) (nat_lit 1723900624) (nat_lit 0) D2M8K2.t8581 from rfl, allE_node, rows8580, irow8576, rows8581]
  all_goals rfl

theorem atot8576 : totK PD2M8K2 D2M8K2.u8576 = [0, 374652788561, 950525906911, 433706532210, 26999013339, 0, 0, 0] := by
  rw [show D2M8K2.u8576 = KTree.node D2M8K2.t8580 (nat_lit 18558837) (nat_lit 1723900624) (nat_lit 0) D2M8K2.t8581 from rfl, totK_node, tot8580, tot8581]
  decide +kernel

theorem arows8577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8577 = true := by
  rw [show D2M8K2.u8577 = KTree.node D2M8K2.t8582 (nat_lit 18560697) (nat_lit 1653587371) (nat_lit 0) D2M8K2.t8583 from rfl, allE_node, rows8582, irow8577, rows8583]
  all_goals rfl

theorem atot8577 : totK PD2M8K2 D2M8K2.u8577 = [0, 177365107145, 745299855294, 744392153506, 108586026113, 1239866073, 0, 0] := by
  rw [show D2M8K2.u8577 = KTree.node D2M8K2.t8582 (nat_lit 18560697) (nat_lit 1653587371) (nat_lit 0) D2M8K2.t8583 from rfl, totK_node, tot8582, tot8583]
  decide +kernel

theorem arows8580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8580 = true := by
  rw [show D2M8K2.u8580 = KTree.node D2M8K2.t8584 (nat_lit 18563212) (nat_lit 3260575856) (nat_lit 0) D2M8K2.t8585 from rfl, allE_node, rows8584, irow8580, rows8585]
  all_goals rfl

theorem atot8580 : totK PD2M8K2 D2M8K2.u8580 = [0, 335651543331, 929853289711, 525571664167, 39649255867, 0, 0, 0] := by
  rw [show D2M8K2.u8580 = KTree.node D2M8K2.t8584 (nat_lit 18563212) (nat_lit 3260575856) (nat_lit 0) D2M8K2.t8585 from rfl, totK_node, tot8584, tot8585]
  decide +kernel

theorem arows8581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8581 = true := by
  rw [show D2M8K2.u8581 = KTree.node D2M8K2.t8586 (nat_lit 18569637) (nat_lit 1368772478) (nat_lit 0) D2M8K2.t8587 from rfl, allE_node, rows8586, irow8581, rows8587]
  all_goals rfl

theorem atot8581 : totK PD2M8K2 D2M8K2.u8581 = [0, 351927983768, 930437090694, 494318089147, 39868998144, 0, 0, 0] := by
  rw [show D2M8K2.u8581 = KTree.node D2M8K2.t8586 (nat_lit 18569637) (nat_lit 1368772478) (nat_lit 0) D2M8K2.t8587 from rfl, totK_node, tot8586, tot8587]
  decide +kernel

theorem arows8583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8583 = true := by
  rw [show D2M8K2.u8583 = KTree.node D2M8K2.t8588 (nat_lit 18571177) (nat_lit 1249499815) (nat_lit 0) D2M8K2.t8589 from rfl, allE_node, rows8588, irow8583, rows8589]
  all_goals rfl

theorem atot8583 : totK PD2M8K2 D2M8K2.u8583 = [0, 88232718943, 568786788135, 842435941244, 241500028015, 10615149062, 0, 0] := by
  rw [show D2M8K2.u8583 = KTree.node D2M8K2.t8588 (nat_lit 18571177) (nat_lit 1249499815) (nat_lit 0) D2M8K2.t8589 from rfl, totK_node, tot8588, tot8589]
  decide +kernel

theorem arows8584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8584 = true := by
  rw [show D2M8K2.u8584 = KTree.node D2M8K2.t8590 (nat_lit 18573007) (nat_lit 2235152603) (nat_lit 0) D2M8K2.t8591 from rfl, allE_node, rows8590, irow8584, rows8591]
  all_goals rfl

theorem atot8584 : totK PD2M8K2 D2M8K2.u8584 = [0, 320012379946, 888564761625, 519187524221, 65481128398, 2490301335, 0, 0] := by
  rw [show D2M8K2.u8584 = KTree.node D2M8K2.t8590 (nat_lit 18573007) (nat_lit 2235152603) (nat_lit 0) D2M8K2.t8591 from rfl, totK_node, tot8590, tot8591]
  decide +kernel

theorem arows8588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8588 = true := by
  rw [show D2M8K2.u8588 = KTree.node D2M8K2.t8592 (nat_lit 18574646) (nat_lit 3740343102) (nat_lit 0) D2M8K2.t8593 from rfl, allE_node, rows8592, irow8588, rows8593]
  all_goals rfl

theorem atot8588 : totK PD2M8K2 D2M8K2.u8588 = [0, 108694292139, 649682704086, 807302703055, 160782353138, 4720618446, 0, 0] := by
  rw [show D2M8K2.u8588 = KTree.node D2M8K2.t8592 (nat_lit 18574646) (nat_lit 3740343102) (nat_lit 0) D2M8K2.t8593 from rfl, totK_node, tot8592, tot8593]
  decide +kernel

theorem arows8589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8589 = true := by
  rw [show D2M8K2.u8589 = KTree.node D2M8K2.t8594 (nat_lit 18576622) (nat_lit 3934097988) (nat_lit 0) D2M8K2.t8595 from rfl, allE_node, rows8594, irow8589, rows8595]
  all_goals rfl

theorem atot8589 : totK PD2M8K2 D2M8K2.u8589 = [0, 389897956180, 937147305515, 458572783952, 33086242966, 0, 0, 0] := by
  rw [show D2M8K2.u8589 = KTree.node D2M8K2.t8594 (nat_lit 18576622) (nat_lit 3934097988) (nat_lit 0) D2M8K2.t8595 from rfl, totK_node, tot8594, tot8595]
  decide +kernel

theorem arows8591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8591 = true := by
  rw [show D2M8K2.u8591 = KTree.node D2M8K2.t8596 (nat_lit 18580224) (nat_lit 3422611686) (nat_lit 0) D2M8K2.t8597 from rfl, allE_node, rows8596, irow8591, rows8597]
  all_goals rfl

theorem atot8591 : totK PD2M8K2 D2M8K2.u8591 = [323601998422, 822870351044, 490956465325, 141441628787, 13552632951, 0, 0, 0] := by
  rw [show D2M8K2.u8591 = KTree.node D2M8K2.t8596 (nat_lit 18580224) (nat_lit 3422611686) (nat_lit 0) D2M8K2.t8597 from rfl, totK_node, tot8596, tot8597]
  decide +kernel

theorem arows8592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8592 = true := by
  rw [show D2M8K2.u8592 = KTree.node D2M8K2.t8598 (nat_lit 18582386) (nat_lit 3713559293) (nat_lit 0) D2M8K2.t8599 from rfl, allE_node, rows8598, irow8592, rows8599]
  all_goals rfl

theorem atot8592 : totK PD2M8K2 D2M8K2.u8592 = [179148547845, 703129515249, 786516588497, 143589417766, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8592 = KTree.node D2M8K2.t8598 (nat_lit 18582386) (nat_lit 3713559293) (nat_lit 0) D2M8K2.t8599 from rfl, totK_node, tot8598, tot8599]
  decide +kernel

theorem arows8595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8595 = true := by
  rw [show D2M8K2.u8595 = KTree.node D2M8K2.t8600 (nat_lit 18584237) (nat_lit 2025995828) (nat_lit 0) D2M8K2.t8601 from rfl, allE_node, rows8600, irow8595, rows8601]
  all_goals rfl

theorem atot8595 : totK PD2M8K2 D2M8K2.u8595 = [249420483215, 812499912272, 622045231167, 128774388906, 13135967731, 0, 0, 0] := by
  rw [show D2M8K2.u8595 = KTree.node D2M8K2.t8600 (nat_lit 18584237) (nat_lit 2025995828) (nat_lit 0) D2M8K2.t8601 from rfl, totK_node, tot8600, tot8601]
  decide +kernel

theorem arows8596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8596 = true := by
  rw [show D2M8K2.u8596 = KTree.node D2M8K2.t8602 (nat_lit 18585762) (nat_lit 3211190834) (nat_lit 0) D2M8K2.t8603 from rfl, allE_node, rows8602, irow8596, rows8603]
  all_goals rfl

theorem atot8596 : totK PD2M8K2 D2M8K2.u8596 = [35250516920, 385185716669, 888974140656, 457738675092, 24465740491, 0, 0, 0] := by
  rw [show D2M8K2.u8596 = KTree.node D2M8K2.t8602 (nat_lit 18585762) (nat_lit 3211190834) (nat_lit 0) D2M8K2.t8603 from rfl, totK_node, tot8602, tot8603]
  decide +kernel

theorem arows8598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8598 = true := by
  rw [show D2M8K2.u8598 = KTree.node D2M8K2.t8604 (nat_lit 18587070) (nat_lit 1920597987) (nat_lit 0) D2M8K2.t8605 from rfl, allE_node, rows8604, irow8598, rows8605]
  all_goals rfl

theorem atot8598 : totK PD2M8K2 D2M8K2.u8598 = [348115666941, 920163173103, 504748912381, 38186090222, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8598 = KTree.node D2M8K2.t8604 (nat_lit 18587070) (nat_lit 1920597987) (nat_lit 0) D2M8K2.t8605 from rfl, totK_node, tot8604, tot8605]
  decide +kernel

theorem arows8599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8599 = true := by
  rw [show D2M8K2.u8599 = KTree.node D2M8K2.t8606 (nat_lit 18588873) (nat_lit 1745220646) (nat_lit 0) D2M8K2.t8607 from rfl, allE_node, rows8606, irow8599, rows8607]
  all_goals rfl

theorem atot8599 : totK PD2M8K2 D2M8K2.u8599 = [77829559297, 521329331616, 865590024666, 282377892196, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u8599 = KTree.node D2M8K2.t8606 (nat_lit 18588873) (nat_lit 1745220646) (nat_lit 0) D2M8K2.t8607 from rfl, totK_node, tot8606, tot8607]
  decide +kernel

theorem arows8604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8604 = true := by
  rw [show D2M8K2.u8604 = KTree.node D2M8K2.t8608 (nat_lit 18590861) (nat_lit 1573319109) (nat_lit 0) D2M8K2.t8609 from rfl, allE_node, rows8608, irow8604, rows8609]
  all_goals rfl

theorem atot8604 : totK PD2M8K2 D2M8K2.u8604 = [337806917362, 927562627287, 525160393686, 40892696399, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8604 = KTree.node D2M8K2.t8608 (nat_lit 18590861) (nat_lit 1573319109) (nat_lit 0) D2M8K2.t8609 from rfl, totK_node, tot8608, tot8609]
  decide +kernel

theorem arows8605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8605 = true := by
  rw [show D2M8K2.u8605 = KTree.node D2M8K2.t8610 (nat_lit 18592576) (nat_lit 1264317014) (nat_lit 0) D2M8K2.t8611 from rfl, allE_node, rows8610, irow8605, rows8611]
  all_goals rfl

theorem atot8605 : totK PD2M8K2 D2M8K2.u8605 = [56610377076, 493410168924, 906574736625, 306723356871, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u8605 = KTree.node D2M8K2.t8610 (nat_lit 18592576) (nat_lit 1264317014) (nat_lit 0) D2M8K2.t8611 from rfl, totK_node, tot8610, tot8611]
  decide +kernel

theorem arows8607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8607 = true := by
  rw [show D2M8K2.u8607 = KTree.node D2M8K2.t8612 (nat_lit 18593972) (nat_lit 3673459564) (nat_lit 0) D2M8K2.t8613 from rfl, allE_node, rows8612, irow8607, rows8613]
  all_goals rfl

theorem atot8607 : totK PD2M8K2 D2M8K2.u8607 = [375749609619, 920838851623, 485825890000, 40341077072, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8607 = KTree.node D2M8K2.t8612 (nat_lit 18593972) (nat_lit 3673459564) (nat_lit 0) D2M8K2.t8613 from rfl, totK_node, tot8612, tot8613]
  decide +kernel

theorem arows8608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8608 = true := by
  rw [show D2M8K2.u8608 = KTree.node D2M8K2.t8614 (nat_lit 18595637) (nat_lit 2400409922) (nat_lit 0) D2M8K2.t8615 from rfl, allE_node, rows8614, irow8608, rows8615]
  all_goals rfl

theorem atot8608 : totK PD2M8K2 D2M8K2.u8608 = [0, 594553227426, 976484220935, 216084605863, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u8608 = KTree.node D2M8K2.t8614 (nat_lit 18595637) (nat_lit 2400409922) (nat_lit 0) D2M8K2.t8615 from rfl, totK_node, tot8614, tot8615]
  decide +kernel

theorem arows8611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8611 = true := by
  rw [show D2M8K2.u8611 = KTree.node D2M8K2.t8616 (nat_lit 18601233) (nat_lit 1539344454) (nat_lit 0) D2M8K2.t8617 from rfl, allE_node, rows8616, irow8611, rows8617]
  all_goals rfl

theorem atot8611 : totK PD2M8K2 D2M8K2.u8611 = [0, 269853447354, 830186628930, 562122119087, 75665700775, 1138244013, 0, 0] := by
  rw [show D2M8K2.u8611 = KTree.node D2M8K2.t8616 (nat_lit 18601233) (nat_lit 1539344454) (nat_lit 0) D2M8K2.t8617 from rfl, totK_node, tot8616, tot8617]
  decide +kernel

theorem arows8612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8612 = true := by
  rw [show D2M8K2.u8612 = KTree.node D2M8K2.t8618 (nat_lit 18604130) (nat_lit 4114323956) (nat_lit 0) D2M8K2.t8619 from rfl, allE_node, rows8618, irow8612, rows8619]
  all_goals rfl

theorem atot8612 : totK PD2M8K2 D2M8K2.u8612 = [0, 266259838592, 855748981143, 615394717759, 62032901137, 0, 0, 0] := by
  rw [show D2M8K2.u8612 = KTree.node D2M8K2.t8618 (nat_lit 18604130) (nat_lit 4114323956) (nat_lit 0) D2M8K2.t8619 from rfl, totK_node, tot8618, tot8619]
  decide +kernel

theorem arows8614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8614 = true := by
  rw [show D2M8K2.u8614 = KTree.node D2M8K2.t8620 (nat_lit 18607105) (nat_lit 1573088089) (nat_lit 0) D2M8K2.t8621 from rfl, allE_node, rows8620, irow8614, rows8621]
  all_goals rfl

theorem atot8614 : totK PD2M8K2 D2M8K2.u8614 = [0, 379014187602, 944230265687, 466528006680, 28219268652, 0, 0, 0] := by
  rw [show D2M8K2.u8614 = KTree.node D2M8K2.t8620 (nat_lit 18607105) (nat_lit 1573088089) (nat_lit 0) D2M8K2.t8621 from rfl, totK_node, tot8620, tot8621]
  decide +kernel

theorem arows8615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8615 = true := by
  rw [show D2M8K2.u8615 = KTree.node D2M8K2.t8622 (nat_lit 18608744) (nat_lit 2813891308) (nat_lit 0) D2M8K2.t8623 from rfl, allE_node, rows8622, irow8615, rows8623]
  all_goals rfl

theorem atot8615 : totK PD2M8K2 D2M8K2.u8615 = [0, 345991999789, 946279389233, 472022332680, 25987222819, 0, 0, 0] := by
  rw [show D2M8K2.u8615 = KTree.node D2M8K2.t8622 (nat_lit 18608744) (nat_lit 2813891308) (nat_lit 0) D2M8K2.t8623 from rfl, totK_node, tot8622, tot8623]
  decide +kernel

theorem arows8619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8619 = true := by
  rw [show D2M8K2.u8619 = KTree.node D2M8K2.t8624 (nat_lit 18612044) (nat_lit 3076788710) (nat_lit 0) D2M8K2.t8625 from rfl, allE_node, rows8624, irow8619, rows8625]
  all_goals rfl

theorem atot8619 : totK PD2M8K2 D2M8K2.u8619 = [0, 401586729970, 974227001891, 417216126784, 17507761186, 0, 0, 0] := by
  rw [show D2M8K2.u8619 = KTree.node D2M8K2.t8624 (nat_lit 18612044) (nat_lit 3076788710) (nat_lit 0) D2M8K2.t8625 from rfl, totK_node, tot8624, tot8625]
  decide +kernel

theorem arows8620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8620 = true := by
  rw [show D2M8K2.u8620 = KTree.node D2M8K2.t8626 (nat_lit 18615040) (nat_lit 1669354923) (nat_lit 0) D2M8K2.t8627 from rfl, allE_node, rows8626, irow8620, rows8627]
  all_goals rfl

theorem atot8620 : totK PD2M8K2 D2M8K2.u8620 = [0, 265192368705, 818225346279, 586543422988, 79719546971, 1095107716, 0, 0] := by
  rw [show D2M8K2.u8620 = KTree.node D2M8K2.t8626 (nat_lit 18615040) (nat_lit 1669354923) (nat_lit 0) D2M8K2.t8627 from rfl, totK_node, tot8626, tot8627]
  decide +kernel

theorem arows8622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8622 = true := by
  rw [show D2M8K2.u8622 = KTree.node D2M8K2.t8628 (nat_lit 18617000) (nat_lit 3950786586) (nat_lit 0) D2M8K2.t8629 from rfl, allE_node, rows8628, irow8622, rows8629]
  all_goals rfl

theorem atot8622 : totK PD2M8K2 D2M8K2.u8622 = [154132651746, 379554926295, 506070629695, 582520954712, 142221785926, 3882006667, 0, 0] := by
  rw [show D2M8K2.u8622 = KTree.node D2M8K2.t8628 (nat_lit 18617000) (nat_lit 3950786586) (nat_lit 0) D2M8K2.t8629 from rfl, totK_node, tot8628, tot8629]
  decide +kernel

theorem arows8623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8623 = true := by
  rw [show D2M8K2.u8623 = KTree.node D2M8K2.t8630 (nat_lit 18622656) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t8631 from rfl, allE_node, rows8630, irow8623, rows8631]
  all_goals rfl

theorem atot8623 : totK PD2M8K2 D2M8K2.u8623 = [172720967628, 737955624918, 773335465053, 133255333587, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8623 = KTree.node D2M8K2.t8630 (nat_lit 18622656) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t8631 from rfl, totK_node, tot8630, tot8631]
  decide +kernel

theorem arows8626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8626 = true := by
  rw [show D2M8K2.u8626 = KTree.node D2M8K2.t8632 (nat_lit 18625120) (nat_lit 3260140172) (nat_lit 0) D2M8K2.t8633 from rfl, allE_node, rows8632, irow8626, rows8633]
  all_goals rfl

theorem atot8626 : totK PD2M8K2 D2M8K2.u8626 = [339084245173, 902766335907, 536863797726, 50870444024, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8626 = KTree.node D2M8K2.t8632 (nat_lit 18625120) (nat_lit 3260140172) (nat_lit 0) D2M8K2.t8633 from rfl, totK_node, tot8632, tot8633]
  decide +kernel

theorem arows8627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8627 = true := by
  rw [show D2M8K2.u8627 = KTree.node D2M8K2.t8634 (nat_lit 18626638) (nat_lit 3448064947) (nat_lit 0) D2M8K2.t8635 from rfl, allE_node, rows8634, irow8627, rows8635]
  all_goals rfl

theorem atot8627 : totK PD2M8K2 D2M8K2.u8627 = [90286224711, 506384250622, 823615057656, 364289845204, 29375735501, 0, 0, 0] := by
  rw [show D2M8K2.u8627 = KTree.node D2M8K2.t8634 (nat_lit 18626638) (nat_lit 3448064947) (nat_lit 0) D2M8K2.t8635 from rfl, totK_node, tot8634, tot8635]
  decide +kernel

theorem arows8629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8629 = true := by
  rw [show D2M8K2.u8629 = KTree.node D2M8K2.t8636 (nat_lit 18627930) (nat_lit 3647770955) (nat_lit 0) D2M8K2.t8637 from rfl, allE_node, rows8636, irow8629, rows8637]
  all_goals rfl

theorem atot8629 : totK PD2M8K2 D2M8K2.u8629 = [242664306910, 686327201055, 672497153438, 221202384374, 8213711289, 0, 0, 0] := by
  rw [show D2M8K2.u8629 = KTree.node D2M8K2.t8636 (nat_lit 18627930) (nat_lit 3647770955) (nat_lit 0) D2M8K2.t8637 from rfl, totK_node, tot8636, tot8637]
  decide +kernel

theorem arows8630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8630 = true := by
  rw [show D2M8K2.u8630 = KTree.node D2M8K2.t8638 (nat_lit 18629554) (nat_lit 4169072756) (nat_lit 0) D2M8K2.t8639 from rfl, allE_node, rows8638, irow8630, rows8639]
  all_goals rfl

theorem atot8630 : totK PD2M8K2 D2M8K2.u8630 = [142717529808, 704367824550, 790437219633, 162488324970, 2309606161, 0, 0, 0] := by
  rw [show D2M8K2.u8630 = KTree.node D2M8K2.t8638 (nat_lit 18629554) (nat_lit 4169072756) (nat_lit 0) D2M8K2.t8639 from rfl, totK_node, tot8638, tot8639]
  decide +kernel

theorem arows8636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8636 = true := by
  rw [show D2M8K2.u8636 = KTree.node D2M8K2.t8640 (nat_lit 18631543) (nat_lit 2224741165) (nat_lit 0) D2M8K2.t8641 from rfl, allE_node, rows8640, irow8636, rows8641]
  all_goals rfl

theorem atot8636 : totK PD2M8K2 D2M8K2.u8636 = [258991380898, 774091654975, 636355955430, 143754944633, 8388657623, 0, 0, 0] := by
  rw [show D2M8K2.u8636 = KTree.node D2M8K2.t8640 (nat_lit 18631543) (nat_lit 2224741165) (nat_lit 0) D2M8K2.t8641 from rfl, totK_node, tot8640, tot8641]
  decide +kernel

theorem arows8637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8637 = true := by
  rw [show D2M8K2.u8637 = KTree.node D2M8K2.t8642 (nat_lit 18633044) (nat_lit 2982370907) (nat_lit 0) D2M8K2.t8643 from rfl, allE_node, rows8642, irow8637, rows8643]
  all_goals rfl

theorem atot8637 : totK PD2M8K2 D2M8K2.u8637 = [157971732341, 695607414513, 783949689307, 171883653519, 2348440009, 0, 0, 0] := by
  rw [show D2M8K2.u8637 = KTree.node D2M8K2.t8642 (nat_lit 18633044) (nat_lit 2982370907) (nat_lit 0) D2M8K2.t8643 from rfl, totK_node, tot8642, tot8643]
  decide +kernel

theorem arows8639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8639 = true := by
  rw [show D2M8K2.u8639 = KTree.node D2M8K2.t8644 (nat_lit 18638360) (nat_lit 3038119977) (nat_lit 0) D2M8K2.t8645 from rfl, allE_node, rows8644, irow8639, rows8645]
  all_goals rfl

theorem atot8639 : totK PD2M8K2 D2M8K2.u8639 = [259023157694, 752015370605, 632294461000, 159856271523, 10860462960, 0, 0, 0] := by
  rw [show D2M8K2.u8639 = KTree.node D2M8K2.t8644 (nat_lit 18638360) (nat_lit 3038119977) (nat_lit 0) D2M8K2.t8645 from rfl, totK_node, tot8644, tot8645]
  decide +kernel

theorem arows8640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8640 = true := by
  rw [show D2M8K2.u8640 = KTree.node D2M8K2.t8646 (nat_lit 18639824) (nat_lit 2992604921) (nat_lit 0) D2M8K2.t8647 from rfl, allE_node, rows8646, irow8640, rows8647]
  all_goals rfl

theorem atot8640 : totK PD2M8K2 D2M8K2.u8640 = [181745577975, 761529867780, 742617958087, 134137724472, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u8640 = KTree.node D2M8K2.t8646 (nat_lit 18639824) (nat_lit 2992604921) (nat_lit 0) D2M8K2.t8647 from rfl, totK_node, tot8646, tot8647]
  decide +kernel

theorem arows8643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8643 = true := by
  rw [show D2M8K2.u8643 = KTree.node D2M8K2.t8648 (nat_lit 18641502) (nat_lit 3909765239) (nat_lit 0) D2M8K2.t8649 from rfl, allE_node, rows8648, irow8643, rows8649]
  all_goals rfl

theorem atot8643 : totK PD2M8K2 D2M8K2.u8643 = [0, 365878508007, 950337084005, 428170891166, 23301045897, 0, 0, 0] := by
  rw [show D2M8K2.u8643 = KTree.node D2M8K2.t8648 (nat_lit 18641502) (nat_lit 3909765239) (nat_lit 0) D2M8K2.t8649 from rfl, totK_node, tot8648, tot8649]
  decide +kernel

theorem arows8644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8644 = true := by
  rw [show D2M8K2.u8644 = KTree.node D2M8K2.t8650 (nat_lit 18643373) (nat_lit 2128585718) (nat_lit 0) D2M8K2.t8651 from rfl, allE_node, rows8650, irow8644, rows8651]
  all_goals rfl

theorem atot8644 : totK PD2M8K2 D2M8K2.u8644 = [0, 171799827768, 748104347391, 759943078862, 110325301802, 1310285577, 0, 0] := by
  rw [show D2M8K2.u8644 = KTree.node D2M8K2.t8650 (nat_lit 18643373) (nat_lit 2128585718) (nat_lit 0) D2M8K2.t8651 from rfl, totK_node, tot8650, tot8651]
  decide +kernel

theorem arows8646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8646 = true := by
  rw [show D2M8K2.u8646 = KTree.node D2M8K2.t8652 (nat_lit 18645849) (nat_lit 1024863254) (nat_lit 0) D2M8K2.t8653 from rfl, allE_node, rows8652, irow8646, rows8653]
  all_goals rfl

theorem atot8646 : totK PD2M8K2 D2M8K2.u8646 = [0, 337767463208, 906633317074, 536664463694, 47758989064, 0, 0, 0] := by
  rw [show D2M8K2.u8646 = KTree.node D2M8K2.t8652 (nat_lit 18645849) (nat_lit 1024863254) (nat_lit 0) D2M8K2.t8653 from rfl, totK_node, tot8652, tot8653]
  decide +kernel

theorem arows8647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8647 = true := by
  rw [show D2M8K2.u8647 = KTree.node D2M8K2.t8654 (nat_lit 18648943) (nat_lit 2269894567) (nat_lit 0) D2M8K2.t8655 from rfl, allE_node, rows8654, irow8647, rows8655]
  all_goals rfl

theorem atot8647 : totK PD2M8K2 D2M8K2.u8647 = [0, 368246878465, 899600701624, 509246039948, 44075466444, 0, 0, 0] := by
  rw [show D2M8K2.u8647 = KTree.node D2M8K2.t8654 (nat_lit 18648943) (nat_lit 2269894567) (nat_lit 0) D2M8K2.t8655 from rfl, totK_node, tot8654, tot8655]
  decide +kernel

theorem arows8651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8651 = true := by
  rw [show D2M8K2.u8651 = KTree.node D2M8K2.t8656 (nat_lit 18650618) (nat_lit 4279769769) (nat_lit 0) D2M8K2.t8657 from rfl, allE_node, rows8656, irow8651, rows8657]
  all_goals rfl

theorem atot8651 : totK PD2M8K2 D2M8K2.u8651 = [0, 105960855477, 677661977799, 814583324729, 168011728046, 4879840392, 0, 0] := by
  rw [show D2M8K2.u8651 = KTree.node D2M8K2.t8656 (nat_lit 18650618) (nat_lit 4279769769) (nat_lit 0) D2M8K2.t8657 from rfl, totK_node, tot8656, tot8657]
  decide +kernel

theorem arows8652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8652 = true := by
  rw [show D2M8K2.u8652 = KTree.node D2M8K2.t8658 (nat_lit 18652904) (nat_lit 3321136177) (nat_lit 0) D2M8K2.t8659 from rfl, allE_node, rows8658, irow8652, rows8659]
  all_goals rfl

theorem atot8652 : totK PD2M8K2 D2M8K2.u8652 = [0, 377443049724, 926984351391, 472610793184, 40362979505, 0, 0, 0] := by
  rw [show D2M8K2.u8652 = KTree.node D2M8K2.t8658 (nat_lit 18652904) (nat_lit 3321136177) (nat_lit 0) D2M8K2.t8659 from rfl, totK_node, tot8658, tot8659]
  decide +kernel

theorem arows8654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8654 = true := by
  rw [show D2M8K2.u8654 = KTree.node D2M8K2.t8660 (nat_lit 18654657) (nat_lit 1661814809) (nat_lit 0) D2M8K2.t8661 from rfl, allE_node, rows8660, irow8654, rows8661]
  all_goals rfl

theorem atot8654 : totK PD2M8K2 D2M8K2.u8654 = [0, 105072446121, 649280326467, 827891952188, 181447262020, 4931404646, 0, 0] := by
  rw [show D2M8K2.u8654 = KTree.node D2M8K2.t8660 (nat_lit 18654657) (nat_lit 1661814809) (nat_lit 0) D2M8K2.t8661 from rfl, totK_node, tot8660, tot8661]
  decide +kernel

theorem arows8655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8655 = true := by
  rw [show D2M8K2.u8655 = KTree.node D2M8K2.t8662 (nat_lit 18659658) (nat_lit 3267423339) (nat_lit 0) D2M8K2.t8663 from rfl, allE_node, rows8662, irow8655, rows8663]
  all_goals rfl

theorem atot8655 : totK PD2M8K2 D2M8K2.u8655 = [0, 364970938808, 943508341285, 483979893012, 32498068207, 0, 0, 0] := by
  rw [show D2M8K2.u8655 = KTree.node D2M8K2.t8662 (nat_lit 18659658) (nat_lit 3267423339) (nat_lit 0) D2M8K2.t8663 from rfl, totK_node, tot8662, tot8663]
  decide +kernel

theorem arows8658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8658 = true := by
  rw [show D2M8K2.u8658 = KTree.node D2M8K2.t8664 (nat_lit 18661306) (nat_lit 3969426450) (nat_lit 0) D2M8K2.t8665 from rfl, allE_node, rows8664, irow8658, rows8665]
  all_goals rfl

theorem atot8658 : totK PD2M8K2 D2M8K2.u8658 = [0, 0, 507644132774, 961779337521, 269959218980, 8424427256, 0, 0] := by
  rw [show D2M8K2.u8658 = KTree.node D2M8K2.t8664 (nat_lit 18661306) (nat_lit 3969426450) (nat_lit 0) D2M8K2.t8665 from rfl, totK_node, tot8664, tot8665]
  decide +kernel

theorem arows8659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8659 = true := by
  rw [show D2M8K2.u8659 = KTree.node D2M8K2.t8666 (nat_lit 18708006) (nat_lit 2957820182) (nat_lit 0) D2M8K2.t8667 from rfl, allE_node, rows8666, irow8659, rows8667]
  all_goals rfl

theorem atot8659 : totK PD2M8K2 D2M8K2.u8659 = [0, 340898367980, 803469720643, 524283370148, 149081985517, 13326740810, 0, 0] := by
  rw [show D2M8K2.u8659 = KTree.node D2M8K2.t8666 (nat_lit 18708006) (nat_lit 2957820182) (nat_lit 0) D2M8K2.t8667 from rfl, totK_node, tot8666, tot8667]
  decide +kernel

theorem arows8661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8661 = true := by
  rw [show D2M8K2.u8661 = KTree.node D2M8K2.t8668 (nat_lit 18709471) (nat_lit 2274185443) (nat_lit 0) D2M8K2.t8669 from rfl, allE_node, rows8668, irow8661, rows8669]
  all_goals rfl

theorem atot8661 : totK PD2M8K2 D2M8K2.u8661 = [0, 108532708932, 609528290455, 792518479104, 297389106190, 25373788367, 0, 0] := by
  rw [show D2M8K2.u8661 = KTree.node D2M8K2.t8668 (nat_lit 18709471) (nat_lit 2274185443) (nat_lit 0) D2M8K2.t8669 from rfl, totK_node, tot8668, tot8669]
  decide +kernel

theorem arows8662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8662 = true := by
  rw [show D2M8K2.u8662 = KTree.node D2M8K2.t8670 (nat_lit 18710696) (nat_lit 2409695891) (nat_lit 0) D2M8K2.t8671 from rfl, allE_node, rows8670, irow8662, rows8671]
  all_goals rfl

theorem atot8662 : totK PD2M8K2 D2M8K2.u8662 = [0, 165869185073, 578350332398, 763128348668, 298283313030, 12235609738, 0, 0] := by
  rw [show D2M8K2.u8662 = KTree.node D2M8K2.t8670 (nat_lit 18710696) (nat_lit 2409695891) (nat_lit 0) D2M8K2.t8671 from rfl, totK_node, tot8670, tot8671]
  decide +kernel

theorem arows8667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8667 = true := by
  rw [show D2M8K2.u8667 = KTree.node D2M8K2.t8672 (nat_lit 18712270) (nat_lit 3998384852) (nat_lit 0) D2M8K2.t8673 from rfl, allE_node, rows8672, irow8667, rows8673]
  all_goals rfl

theorem atot8667 : totK PD2M8K2 D2M8K2.u8667 = [0, 235041128104, 816963985730, 652438257515, 85192028705, 0, 0, 0] := by
  rw [show D2M8K2.u8667 = KTree.node D2M8K2.t8672 (nat_lit 18712270) (nat_lit 3998384852) (nat_lit 0) D2M8K2.t8673 from rfl, totK_node, tot8672, tot8673]
  decide +kernel

theorem arows8668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8668 = true := by
  rw [show D2M8K2.u8668 = KTree.node D2M8K2.t8674 (nat_lit 18714020) (nat_lit 2751904223) (nat_lit 0) D2M8K2.t8675 from rfl, allE_node, rows8674, irow8668, rows8675]
  all_goals rfl

theorem atot8668 : totK PD2M8K2 D2M8K2.u8668 = [0, 171089712959, 639454191669, 751072822104, 220121715248, 8706415949, 0, 0] := by
  rw [show D2M8K2.u8668 = KTree.node D2M8K2.t8674 (nat_lit 18714020) (nat_lit 2751904223) (nat_lit 0) D2M8K2.t8675 from rfl, totK_node, tot8674, tot8675]
  decide +kernel

theorem arows8670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8670 = true := by
  rw [show D2M8K2.u8670 = KTree.node D2M8K2.t8676 (nat_lit 18715712) (nat_lit 3161918047) (nat_lit 0) D2M8K2.t8677 from rfl, allE_node, rows8676, irow8670, rows8677]
  all_goals rfl

theorem atot8670 : totK PD2M8K2 D2M8K2.u8670 = [0, 248718604284, 830225404581, 648308217336, 87654160977, 0, 0, 0] := by
  rw [show D2M8K2.u8670 = KTree.node D2M8K2.t8676 (nat_lit 18715712) (nat_lit 3161918047) (nat_lit 0) D2M8K2.t8677 from rfl, totK_node, tot8676, tot8677]
  decide +kernel

theorem arows8671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8671 = true := by
  rw [show D2M8K2.u8671 = KTree.node D2M8K2.t8678 (nat_lit 18717428) (nat_lit 1840757181) (nat_lit 0) D2M8K2.t8679 from rfl, allE_node, rows8678, irow8671, rows8679]
  all_goals rfl

theorem atot8671 : totK PD2M8K2 D2M8K2.u8671 = [0, 155281256290, 631395580875, 755202258072, 231978957591, 8824320960, 0, 0] := by
  rw [show D2M8K2.u8671 = KTree.node D2M8K2.t8678 (nat_lit 18717428) (nat_lit 1840757181) (nat_lit 0) D2M8K2.t8679 from rfl, totK_node, tot8678, tot8679]
  decide +kernel

theorem arows8674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8674 = true := by
  rw [show D2M8K2.u8674 = KTree.node D2M8K2.t8680 (nat_lit 18718808) (nat_lit 3884234293) (nat_lit 0) D2M8K2.t8681 from rfl, allE_node, rows8680, irow8674, rows8681]
  all_goals rfl

theorem atot8674 : totK PD2M8K2 D2M8K2.u8674 = [0, 262316783218, 817346118309, 625124546882, 81876261905, 0, 0, 0] := by
  rw [show D2M8K2.u8674 = KTree.node D2M8K2.t8680 (nat_lit 18718808) (nat_lit 3884234293) (nat_lit 0) D2M8K2.t8681 from rfl, totK_node, tot8680, tot8681]
  decide +kernel

theorem arows8675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8675 = true := by
  rw [show D2M8K2.u8675 = KTree.node D2M8K2.t8682 (nat_lit 18720793) (nat_lit 1290802969) (nat_lit 0) D2M8K2.t8683 from rfl, allE_node, rows8682, irow8675, rows8683]
  all_goals rfl

theorem atot8675 : totK PD2M8K2 D2M8K2.u8675 = [0, 176708812954, 723089496697, 767645743285, 150566651626, 2498823382, 0, 0] := by
  rw [show D2M8K2.u8675 = KTree.node D2M8K2.t8682 (nat_lit 18720793) (nat_lit 1290802969) (nat_lit 0) D2M8K2.t8683 from rfl, totK_node, tot8682, tot8683]
  decide +kernel

theorem arows8677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8677 = true := by
  rw [show D2M8K2.u8677 = KTree.node D2M8K2.t8684 (nat_lit 18722633) (nat_lit 1776661562) (nat_lit 0) D2M8K2.t8685 from rfl, allE_node, rows8684, irow8677, rows8685]
  all_goals rfl

theorem atot8677 : totK PD2M8K2 D2M8K2.u8677 = [0, 246182495444, 807227213592, 660273288896, 94215150513, 0, 0, 0] := by
  rw [show D2M8K2.u8677 = KTree.node D2M8K2.t8684 (nat_lit 18722633) (nat_lit 1776661562) (nat_lit 0) D2M8K2.t8685 from rfl, totK_node, tot8684, tot8685]
  decide +kernel

theorem arows8678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8678 = true := by
  rw [show D2M8K2.u8678 = KTree.node D2M8K2.t8686 (nat_lit 18724352) (nat_lit 3090264992) (nat_lit 0) D2M8K2.t8687 from rfl, allE_node, rows8686, irow8678, rows8687]
  all_goals rfl

theorem atot8678 : totK PD2M8K2 D2M8K2.u8678 = [0, 0, 362123293401, 922728278277, 470728918976, 33216637714, 0, 0] := by
  rw [show D2M8K2.u8678 = KTree.node D2M8K2.t8686 (nat_lit 18724352) (nat_lit 3090264992) (nat_lit 0) D2M8K2.t8687 from rfl, totK_node, tot8686, tot8687]
  decide +kernel

theorem arows8682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8682 = true := by
  rw [show D2M8K2.u8682 = KTree.node D2M8K2.t8688 (nat_lit 18729236) (nat_lit 3198833306) (nat_lit 0) D2M8K2.t8689 from rfl, allE_node, rows8688, irow8682, rows8689]
  all_goals rfl

theorem atot8682 : totK PD2M8K2 D2M8K2.u8682 = [0, 0, 351596309553, 927583268603, 508710321328, 40224240986, 0, 0] := by
  rw [show D2M8K2.u8682 = KTree.node D2M8K2.t8688 (nat_lit 18729236) (nat_lit 3198833306) (nat_lit 0) D2M8K2.t8689 from rfl, totK_node, tot8688, tot8689]
  decide +kernel

theorem arows8683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8683 = true := by
  rw [show D2M8K2.u8683 = KTree.node D2M8K2.t8690 (nat_lit 18730696) (nat_lit 3318619158) (nat_lit 0) D2M8K2.t8691 from rfl, allE_node, rows8690, irow8683, rows8691]
  all_goals rfl

theorem atot8683 : totK PD2M8K2 D2M8K2.u8683 = [0, 0, 0, 385298902092, 936651823974, 429143010118, 30397782892, 0] := by
  rw [show D2M8K2.u8683 = KTree.node D2M8K2.t8690 (nat_lit 18730696) (nat_lit 3318619158) (nat_lit 0) D2M8K2.t8691 from rfl, totK_node, tot8690, tot8691]
  decide +kernel

theorem arows8685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8685 = true := by
  rw [show D2M8K2.u8685 = KTree.node D2M8K2.t8692 (nat_lit 18732069) (nat_lit 1394966818) (nat_lit 0) D2M8K2.t8693 from rfl, allE_node, rows8692, irow8685, rows8693]
  all_goals rfl

theorem atot8685 : totK PD2M8K2 D2M8K2.u8685 = [0, 0, 314618192412, 821251469021, 526340878593, 118297825184, 6524090962, 0] := by
  rw [show D2M8K2.u8685 = KTree.node D2M8K2.t8692 (nat_lit 18732069) (nat_lit 1394966818) (nat_lit 0) D2M8K2.t8693 from rfl, totK_node, tot8692, tot8693]
  decide +kernel

theorem arows8686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8686 = true := by
  rw [show D2M8K2.u8686 = KTree.node D2M8K2.t8694 (nat_lit 18733872) (nat_lit 3439709489) (nat_lit 0) D2M8K2.t8695 from rfl, allE_node, rows8694, irow8686, rows8695]
  all_goals rfl

theorem atot8686 : totK PD2M8K2 D2M8K2.u8686 = [0, 0, 88808799491, 605310370520, 870105561193, 189821098178, 5067863418, 0] := by
  rw [show D2M8K2.u8686 = KTree.node D2M8K2.t8694 (nat_lit 18733872) (nat_lit 3439709489) (nat_lit 0) D2M8K2.t8695 from rfl, totK_node, tot8694, tot8695]
  decide +kernel

theorem arows8689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8689 = true := by
  rw [show D2M8K2.u8689 = KTree.node D2M8K2.t8696 (nat_lit 18735936) (nat_lit 3414857297) (nat_lit 0) D2M8K2.t8697 from rfl, allE_node, rows8696, irow8689, rows8697]
  all_goals rfl

theorem atot8689 : totK PD2M8K2 D2M8K2.u8689 = [0, 0, 402491767219, 937379977794, 440230825484, 31012102688, 0, 0] := by
  rw [show D2M8K2.u8689 = KTree.node D2M8K2.t8696 (nat_lit 18735936) (nat_lit 3414857297) (nat_lit 0) D2M8K2.t8697 from rfl, totK_node, tot8696, tot8697]
  decide +kernel

theorem arows8690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8690 = true := by
  rw [show D2M8K2.u8690 = KTree.node D2M8K2.t8698 (nat_lit 18737784) (nat_lit 3241524418) (nat_lit 0) D2M8K2.t8699 from rfl, allE_node, rows8698, irow8690, rows8699]
  all_goals rfl

theorem atot8690 : totK PD2M8K2 D2M8K2.u8690 = [0, 0, 71578570206, 607067760181, 860904488191, 195078615179, 5126512042, 0] := by
  rw [show D2M8K2.u8690 = KTree.node D2M8K2.t8698 (nat_lit 18737784) (nat_lit 3241524418) (nat_lit 0) D2M8K2.t8699 from rfl, totK_node, tot8698, tot8699]
  decide +kernel

theorem arows8692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8692 = true := by
  rw [show D2M8K2.u8692 = KTree.node D2M8K2.t8700 (nat_lit 18739210) (nat_lit 3696004331) (nat_lit 0) D2M8K2.t8701 from rfl, allE_node, rows8700, irow8692, rows8701]
  all_goals rfl

theorem atot8692 : totK PD2M8K2 D2M8K2.u8692 = [0, 0, 349559698726, 919824999743, 488607218057, 35104984627, 0, 0] := by
  rw [show D2M8K2.u8692 = KTree.node D2M8K2.t8700 (nat_lit 18739210) (nat_lit 3696004331) (nat_lit 0) D2M8K2.t8701 from rfl, totK_node, tot8700, tot8701]
  decide +kernel

theorem arows8693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8693 = true := by
  rw [show D2M8K2.u8693 = KTree.node D2M8K2.t8702 (nat_lit 18741317) (nat_lit 2261370698) (nat_lit 0) D2M8K2.t8703 from rfl, allE_node, rows8702, irow8693, rows8703]
  all_goals rfl

theorem atot8693 : totK PD2M8K2 D2M8K2.u8693 = [0, 0, 155935246015, 727390637001, 790644780232, 123348644996, 1392055030, 0] := by
  rw [show D2M8K2.u8693 = KTree.node D2M8K2.t8702 (nat_lit 18741317) (nat_lit 2261370698) (nat_lit 0) D2M8K2.t8703 from rfl, totK_node, tot8702, tot8703]
  decide +kernel

theorem arows8702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8702 = true := by
  rw [show D2M8K2.u8702 = KTree.node D2M8K2.t8704 (nat_lit 18742903) (nat_lit 2299071308) (nat_lit 0) D2M8K2.t8705 from rfl, allE_node, rows8704, irow8702, rows8705]
  all_goals rfl

theorem atot8702 : totK PD2M8K2 D2M8K2.u8702 = [0, 0, 262005931797, 862074751286, 613925281075, 61654600146, 0, 0] := by
  rw [show D2M8K2.u8702 = KTree.node D2M8K2.t8704 (nat_lit 18742903) (nat_lit 2299071308) (nat_lit 0) D2M8K2.t8705 from rfl, totK_node, tot8704, tot8705]
  decide +kernel

theorem arows8703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8703 = true := by
  rw [show D2M8K2.u8703 = KTree.node D2M8K2.t8706 (nat_lit 18745104) (nat_lit 3075251144) (nat_lit 0) D2M8K2.t8707 from rfl, allE_node, rows8706, irow8703, rows8707]
  all_goals rfl

theorem atot8703 : totK PD2M8K2 D2M8K2.u8703 = [0, 119216023376, 270757075700, 448044082304, 690233952789, 232519039802, 9139067247, 0] := by
  rw [show D2M8K2.u8703 = KTree.node D2M8K2.t8706 (nat_lit 18745104) (nat_lit 3075251144) (nat_lit 0) D2M8K2.t8707 from rfl, totK_node, tot8706, tot8707]
  decide +kernel

theorem arows8705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8705 = true := by
  rw [show D2M8K2.u8705 = KTree.node D2M8K2.t8708 (nat_lit 18750032) (nat_lit 3775691661) (nat_lit 0) D2M8K2.t8709 from rfl, allE_node, rows8708, irow8705, rows8709]
  all_goals rfl

theorem atot8705 : totK PD2M8K2 D2M8K2.u8705 = [0, 306558624776, 908274805389, 549744434864, 51505642556, 0, 0, 0] := by
  rw [show D2M8K2.u8705 = KTree.node D2M8K2.t8708 (nat_lit 18750032) (nat_lit 3775691661) (nat_lit 0) D2M8K2.t8709 from rfl, totK_node, tot8708, tot8709]
  decide +kernel

theorem arows8706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8706 = true := by
  rw [show D2M8K2.u8706 = KTree.node D2M8K2.t8710 (nat_lit 18751519) (nat_lit 2323855179) (nat_lit 0) D2M8K2.t8711 from rfl, allE_node, rows8710, irow8706, rows8711]
  all_goals rfl

theorem atot8706 : totK PD2M8K2 D2M8K2.u8706 = [0, 0, 353751934281, 942431430812, 476044976570, 30730646440, 0, 0] := by
  rw [show D2M8K2.u8706 = KTree.node D2M8K2.t8710 (nat_lit 18751519) (nat_lit 2323855179) (nat_lit 0) D2M8K2.t8711 from rfl, totK_node, tot8710, tot8711]
  decide +kernel

theorem arows8709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8709 = true := by
  rw [show D2M8K2.u8709 = KTree.node D2M8K2.t8712 (nat_lit 18752826) (nat_lit 3385022997) (nat_lit 0) D2M8K2.t8713 from rfl, allE_node, rows8712, irow8709, rows8713]
  all_goals rfl

theorem atot8709 : totK PD2M8K2 D2M8K2.u8709 = [0, 355841458875, 875876765967, 486840829313, 89410719040, 5570701333, 0, 0] := by
  rw [show D2M8K2.u8709 = KTree.node D2M8K2.t8712 (nat_lit 18752826) (nat_lit 3385022997) (nat_lit 0) D2M8K2.t8713 from rfl, totK_node, tot8712, tot8713]
  decide +kernel

theorem arows8710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8710 = true := by
  rw [show D2M8K2.u8710 = KTree.node D2M8K2.t8714 (nat_lit 18754371) (nat_lit 3703877239) (nat_lit 0) D2M8K2.t8715 from rfl, allE_node, rows8714, irow8710, rows8715]
  all_goals rfl

theorem atot8710 : totK PD2M8K2 D2M8K2.u8710 = [0, 70856345395, 551296216872, 887727311498, 262037614593, 10568566766, 0, 0] := by
  rw [show D2M8K2.u8710 = KTree.node D2M8K2.t8714 (nat_lit 18754371) (nat_lit 3703877239) (nat_lit 0) D2M8K2.t8715 from rfl, totK_node, tot8714, tot8715]
  decide +kernel

theorem arows8712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8712 = true := by
  rw [show D2M8K2.u8712 = KTree.node D2M8K2.t8716 (nat_lit 18759660) (nat_lit 1813384719) (nat_lit 0) D2M8K2.t8717 from rfl, allE_node, rows8716, irow8712, rows8717]
  all_goals rfl

theorem atot8712 : totK PD2M8K2 D2M8K2.u8712 = [0, 309697957814, 874689286387, 550218982759, 72977454144, 2481160468, 0, 0] := by
  rw [show D2M8K2.u8712 = KTree.node D2M8K2.t8716 (nat_lit 18759660) (nat_lit 1813384719) (nat_lit 0) D2M8K2.t8717 from rfl, totK_node, tot8716, tot8717]
  decide +kernel

theorem arows8713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8713 = true := by
  rw [show D2M8K2.u8713 = KTree.node D2M8K2.t8718 (nat_lit 18761278) (nat_lit 3125194145) (nat_lit 0) D2M8K2.t8719 from rfl, allE_node, rows8718, irow8713, rows8719]
  all_goals rfl

theorem atot8713 : totK PD2M8K2 D2M8K2.u8713 = [0, 90332340817, 629267150698, 875841272603, 184630219878, 2165917952, 0, 0] := by
  rw [show D2M8K2.u8713 = KTree.node D2M8K2.t8718 (nat_lit 18761278) (nat_lit 3125194145) (nat_lit 0) D2M8K2.t8719 from rfl, totK_node, tot8718, tot8719]
  decide +kernel

theorem arows8717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8717 = true := by
  rw [show D2M8K2.u8717 = KTree.node D2M8K2.t8720 (nat_lit 18763242) (nat_lit 3183111325) (nat_lit 0) D2M8K2.t8721 from rfl, allE_node, rows8720, irow8717, rows8721]
  all_goals rfl

theorem atot8717 : totK PD2M8K2 D2M8K2.u8717 = [0, 393771481173, 922196030309, 457747781593, 52183294663, 2814597007, 0, 0] := by
  rw [show D2M8K2.u8717 = KTree.node D2M8K2.t8720 (nat_lit 18763242) (nat_lit 3183111325) (nat_lit 0) D2M8K2.t8721 from rfl, totK_node, tot8720, tot8721]
  decide +kernel

theorem arows8718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8718 = true := by
  rw [show D2M8K2.u8718 = KTree.node D2M8K2.t8722 (nat_lit 18764968) (nat_lit 3874156875) (nat_lit 0) D2M8K2.t8723 from rfl, allE_node, rows8722, irow8718, rows8723]
  all_goals rfl

theorem atot8718 : totK PD2M8K2 D2M8K2.u8718 = [0, 12005493123, 520763964673, 971998626706, 279393306478, 6222784045, 0, 0] := by
  rw [show D2M8K2.u8718 = KTree.node D2M8K2.t8722 (nat_lit 18764968) (nat_lit 3874156875) (nat_lit 0) D2M8K2.t8723 from rfl, totK_node, tot8722, tot8723]
  decide +kernel

theorem arows8720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8720 = true := by
  rw [show D2M8K2.u8720 = KTree.node D2M8K2.t8724 (nat_lit 18770232) (nat_lit 3265016501) (nat_lit 0) D2M8K2.t8725 from rfl, allE_node, rows8724, irow8720, rows8725]
  all_goals rfl

theorem atot8720 : totK PD2M8K2 D2M8K2.u8720 = [0, 0, 340180139267, 912889459414, 514409378352, 44132098685, 0, 0] := by
  rw [show D2M8K2.u8720 = KTree.node D2M8K2.t8724 (nat_lit 18770232) (nat_lit 3265016501) (nat_lit 0) D2M8K2.t8725 from rfl, totK_node, tot8724, tot8725]
  decide +kernel

theorem arows8721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8721 = true := by
  rw [show D2M8K2.u8721 = KTree.node D2M8K2.t8726 (nat_lit 18773325) (nat_lit 1488703967) (nat_lit 0) D2M8K2.t8727 from rfl, allE_node, rows8726, irow8721, rows8727]
  all_goals rfl

theorem atot8721 : totK PD2M8K2 D2M8K2.u8721 = [0, 0, 355095921310, 909446019131, 499361859283, 36547937001, 0, 0] := by
  rw [show D2M8K2.u8721 = KTree.node D2M8K2.t8726 (nat_lit 18773325) (nat_lit 1488703967) (nat_lit 0) D2M8K2.t8727 from rfl, totK_node, tot8726, tot8727]
  decide +kernel

theorem arows8724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8724 = true := by
  rw [show D2M8K2.u8724 = KTree.node D2M8K2.t8728 (nat_lit 18774789) (nat_lit 1143282094) (nat_lit 0) D2M8K2.t8729 from rfl, allE_node, rows8728, irow8724, rows8729]
  all_goals rfl

theorem atot8724 : totK PD2M8K2 D2M8K2.u8724 = [0, 0, 155065940111, 725794471612, 735965855709, 140103101490, 4140770520, 0] := by
  rw [show D2M8K2.u8724 = KTree.node D2M8K2.t8728 (nat_lit 18774789) (nat_lit 1143282094) (nat_lit 0) D2M8K2.t8729 from rfl, totK_node, tot8728, tot8729]
  decide +kernel

theorem arows8725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8725 = true := by
  rw [show D2M8K2.u8725 = KTree.node D2M8K2.t8730 (nat_lit 18780304) (nat_lit 3396988453) (nat_lit 0) D2M8K2.t8731 from rfl, allE_node, rows8730, irow8725, rows8731]
  all_goals rfl

theorem atot8725 : totK PD2M8K2 D2M8K2.u8725 = [0, 0, 309076256651, 838649987321, 544358923864, 79077392798, 1179991115, 0] := by
  rw [show D2M8K2.u8725 = KTree.node D2M8K2.t8730 (nat_lit 18780304) (nat_lit 3396988453) (nat_lit 0) D2M8K2.t8731 from rfl, totK_node, tot8730, tot8731]
  decide +kernel

theorem arows8727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8727 = true := by
  rw [show D2M8K2.u8727 = KTree.node D2M8K2.t8732 (nat_lit 18782228) (nat_lit 3106372352) (nat_lit 0) D2M8K2.t8733 from rfl, allE_node, rows8732, irow8727, rows8733]
  all_goals rfl

theorem atot8727 : totK PD2M8K2 D2M8K2.u8727 = [0, 0, 157851214561, 760069120908, 723878081179, 96788466255, 1225787871, 0] := by
  rw [show D2M8K2.u8727 = KTree.node D2M8K2.t8732 (nat_lit 18782228) (nat_lit 3106372352) (nat_lit 0) D2M8K2.t8733 from rfl, totK_node, tot8732, tot8733]
  decide +kernel

theorem arows8728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8728 = true := by
  rw [show D2M8K2.u8728 = KTree.node D2M8K2.t8734 (nat_lit 18784144) (nat_lit 3680994124) (nat_lit 0) D2M8K2.t8735 from rfl, allE_node, rows8734, irow8728, rows8735]
  all_goals rfl

theorem atot8728 : totK PD2M8K2 D2M8K2.u8728 = [0, 32530458273, 371643559669, 878997078398, 492400561509, 38062205523, 0, 0] := by
  rw [show D2M8K2.u8728 = KTree.node D2M8K2.t8734 (nat_lit 18784144) (nat_lit 3680994124) (nat_lit 0) D2M8K2.t8735 from rfl, totK_node, tot8734, tot8735]
  decide +kernel

theorem arows8733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8733 = true := by
  rw [show D2M8K2.u8733 = KTree.node D2M8K2.t8736 (nat_lit 18788047) (nat_lit 2421511515) (nat_lit 0) D2M8K2.t8737 from rfl, allE_node, rows8736, irow8733, rows8737]
  all_goals rfl

theorem atot8733 : totK PD2M8K2 D2M8K2.u8733 = [0, 309123321896, 915735439705, 536891119707, 37844628032, 0, 0, 0] := by
  rw [show D2M8K2.u8733 = KTree.node D2M8K2.t8736 (nat_lit 18788047) (nat_lit 2421511515) (nat_lit 0) D2M8K2.t8737 from rfl, totK_node, tot8736, tot8737]
  decide +kernel

theorem arows8734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8734 = true := by
  rw [show D2M8K2.u8734 = KTree.node D2M8K2.t8738 (nat_lit 18790620) (nat_lit 2094823348) (nat_lit 0) D2M8K2.t8739 from rfl, allE_node, rows8738, irow8734, rows8739]
  all_goals rfl

theorem atot8734 : totK PD2M8K2 D2M8K2.u8734 = [0, 219347820496, 743260781162, 739155613950, 121758736177, 1310517177, 0, 0] := by
  rw [show D2M8K2.u8734 = KTree.node D2M8K2.t8738 (nat_lit 18790620) (nat_lit 2094823348) (nat_lit 0) D2M8K2.t8739 from rfl, totK_node, tot8738, tot8739]
  decide +kernel

theorem arows8736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8736 = true := by
  rw [show D2M8K2.u8736 = KTree.node D2M8K2.t8740 (nat_lit 18791798) (nat_lit 3947839103) (nat_lit 0) D2M8K2.t8741 from rfl, allE_node, rows8740, irow8736, rows8741]
  all_goals rfl

theorem atot8736 : totK PD2M8K2 D2M8K2.u8736 = [0, 211196905753, 745055955622, 641520107571, 204153066104, 21393864572, 0, 0] := by
  rw [show D2M8K2.u8736 = KTree.node D2M8K2.t8740 (nat_lit 18791798) (nat_lit 3947839103) (nat_lit 0) D2M8K2.t8741 from rfl, totK_node, tot8740, tot8741]
  decide +kernel

theorem arows8737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8737 = true := by
  rw [show D2M8K2.u8737 = KTree.node D2M8K2.t8742 (nat_lit 18793300) (nat_lit 2618902621) (nat_lit 0) D2M8K2.t8743 from rfl, allE_node, rows8742, irow8737, rows8743]
  all_goals rfl

theorem atot8737 : totK PD2M8K2 D2M8K2.u8737 = [0, 83047329000, 473472643903, 846147639825, 370977587335, 16091834962, 0, 0] := by
  rw [show D2M8K2.u8737 = KTree.node D2M8K2.t8742 (nat_lit 18793300) (nat_lit 2618902621) (nat_lit 0) D2M8K2.t8743 from rfl, totK_node, tot8742, tot8743]
  decide +kernel

theorem arows8740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8740 = true := by
  rw [show D2M8K2.u8740 = KTree.node D2M8K2.t8744 (nat_lit 18798285) (nat_lit 1471437730) (nat_lit 0) D2M8K2.t8745 from rfl, allE_node, rows8744, irow8740, rows8745]
  all_goals rfl

theorem atot8740 : totK PD2M8K2 D2M8K2.u8740 = [0, 358571242428, 933926990187, 512164847844, 40308401831, 0, 0, 0] := by
  rw [show D2M8K2.u8740 = KTree.node D2M8K2.t8744 (nat_lit 18798285) (nat_lit 1471437730) (nat_lit 0) D2M8K2.t8745 from rfl, totK_node, tot8744, tot8745]
  decide +kernel

theorem arows8741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8741 = true := by
  rw [show D2M8K2.u8741 = KTree.node D2M8K2.t8746 (nat_lit 18799918) (nat_lit 3984500757) (nat_lit 0) D2M8K2.t8747 from rfl, allE_node, rows8746, irow8741, rows8747]
  all_goals rfl

theorem atot8741 : totK PD2M8K2 D2M8K2.u8741 = [0, 26941954745, 485536453816, 951610499075, 308782961933, 13196099988, 0, 0] := by
  rw [show D2M8K2.u8741 = KTree.node D2M8K2.t8746 (nat_lit 18799918) (nat_lit 3984500757) (nat_lit 0) D2M8K2.t8747 from rfl, totK_node, tot8746, tot8747]
  decide +kernel

theorem arows8743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8743 = true := by
  rw [show D2M8K2.u8743 = KTree.node D2M8K2.t8748 (nat_lit 18801276) (nat_lit 2332441522) (nat_lit 0) D2M8K2.t8749 from rfl, allE_node, rows8748, irow8743, rows8749]
  all_goals rfl

theorem atot8743 : totK PD2M8K2 D2M8K2.u8743 = [0, 381171751740, 929631978722, 464054062947, 38951489226, 0, 0, 0] := by
  rw [show D2M8K2.u8743 = KTree.node D2M8K2.t8748 (nat_lit 18801276) (nat_lit 2332441522) (nat_lit 0) D2M8K2.t8749 from rfl, totK_node, tot8748, tot8749]
  decide +kernel

theorem arows8744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8744 = true := by
  rw [show D2M8K2.u8744 = KTree.node D2M8K2.t8750 (nat_lit 18803043) (nat_lit 3603782331) (nat_lit 0) D2M8K2.t8751 from rfl, allE_node, rows8750, irow8744, rows8751]
  all_goals rfl

theorem atot8744 : totK PD2M8K2 D2M8K2.u8744 = [0, 78851247754, 614160002956, 878310060762, 201821265802, 4980514959, 0, 0] := by
  rw [show D2M8K2.u8744 = KTree.node D2M8K2.t8750 (nat_lit 18803043) (nat_lit 3603782331) (nat_lit 0) D2M8K2.t8751 from rfl, totK_node, tot8750, tot8751]
  decide +kernel

theorem arows8748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8748 = true := by
  rw [show D2M8K2.u8748 = KTree.node D2M8K2.t8752 (nat_lit 18804868) (nat_lit 4034614820) (nat_lit 0) D2M8K2.t8753 from rfl, allE_node, rows8752, irow8748, rows8753]
  all_goals rfl

theorem atot8748 : totK PD2M8K2 D2M8K2.u8748 = [0, 338332594357, 925739567250, 525381499248, 40696682038, 0, 0, 0] := by
  rw [show D2M8K2.u8748 = KTree.node D2M8K2.t8752 (nat_lit 18804868) (nat_lit 4034614820) (nat_lit 0) D2M8K2.t8753 from rfl, totK_node, tot8752, tot8753]
  decide +kernel

theorem arows8749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8749 = true := by
  rw [show D2M8K2.u8749 = KTree.node D2M8K2.t8754 (nat_lit 18806572) (nat_lit 3835361316) (nat_lit 0) D2M8K2.t8755 from rfl, allE_node, rows8754, irow8749, rows8755]
  all_goals rfl

theorem atot8749 : totK PD2M8K2 D2M8K2.u8749 = [0, 0, 434335952675, 982217399996, 346610494226, 9632472965, 0, 0] := by
  rw [show D2M8K2.u8749 = KTree.node D2M8K2.t8754 (nat_lit 18806572) (nat_lit 3835361316) (nat_lit 0) D2M8K2.t8755 from rfl, totK_node, tot8754, tot8755]
  decide +kernel

theorem arows8751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8751 = true := by
  rw [show D2M8K2.u8751 = KTree.node D2M8K2.t8756 (nat_lit 18808814) (nat_lit 3526892391) (nat_lit 0) D2M8K2.t8757 from rfl, allE_node, rows8756, irow8751, rows8757]
  all_goals rfl

theorem atot8751 : totK PD2M8K2 D2M8K2.u8751 = [0, 0, 450908277936, 941969799242, 380685014603, 32583689350, 0, 0] := by
  rw [show D2M8K2.u8751 = KTree.node D2M8K2.t8756 (nat_lit 18808814) (nat_lit 3526892391) (nat_lit 0) D2M8K2.t8757 from rfl, totK_node, tot8756, tot8757]
  decide +kernel

theorem arows8752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8752 = true := by
  rw [show D2M8K2.u8752 = KTree.node D2M8K2.t8758 (nat_lit 18812239) (nat_lit 2422567357) (nat_lit 0) D2M8K2.t8759 from rfl, allE_node, rows8758, irow8752, rows8759]
  all_goals rfl

theorem atot8752 : totK PD2M8K2 D2M8K2.u8752 = [0, 0, 395168588855, 937248646006, 434634620002, 22643355937, 0, 0] := by
  rw [show D2M8K2.u8752 = KTree.node D2M8K2.t8758 (nat_lit 18812239) (nat_lit 2422567357) (nat_lit 0) D2M8K2.t8759 from rfl, totK_node, tot8758, tot8759]
  decide +kernel

theorem arows8755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8755 = true := by
  rw [show D2M8K2.u8755 = KTree.node D2M8K2.t8760 (nat_lit 18818938) (nat_lit 3730576843) (nat_lit 0) D2M8K2.t8761 from rfl, allE_node, rows8760, irow8755, rows8761]
  all_goals rfl

theorem atot8755 : totK PD2M8K2 D2M8K2.u8755 = [0, 0, 354016613993, 931511177307, 486335555788, 33398713016, 0, 0] := by
  rw [show D2M8K2.u8755 = KTree.node D2M8K2.t8760 (nat_lit 18818938) (nat_lit 3730576843) (nat_lit 0) D2M8K2.t8761 from rfl, totK_node, tot8760, tot8761]
  decide +kernel

theorem arows8756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8756 = true := by
  rw [show D2M8K2.u8756 = KTree.node D2M8K2.t8762 (nat_lit 18820754) (nat_lit 3594030917) (nat_lit 0) D2M8K2.t8763 from rfl, allE_node, rows8762, irow8756, rows8763]
  all_goals rfl

theorem atot8756 : totK PD2M8K2 D2M8K2.u8756 = [0, 0, 76423586190, 601738132587, 858405019656, 197428444848, 5352782441, 0] := by
  rw [show D2M8K2.u8756 = KTree.node D2M8K2.t8762 (nat_lit 18820754) (nat_lit 3594030917) (nat_lit 0) D2M8K2.t8763 from rfl, totK_node, tot8762, tot8763]
  decide +kernel

theorem arows8758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8758 = true := by
  rw [show D2M8K2.u8758 = KTree.node D2M8K2.t8764 (nat_lit 18822279) (nat_lit 3609496891) (nat_lit 0) D2M8K2.t8765 from rfl, allE_node, rows8764, irow8758, rows8765]
  all_goals rfl

theorem atot8758 : totK PD2M8K2 D2M8K2.u8758 = [0, 0, 332053019548, 942762110924, 488629508665, 28491024604, 0, 0] := by
  rw [show D2M8K2.u8758 = KTree.node D2M8K2.t8764 (nat_lit 18822279) (nat_lit 3609496891) (nat_lit 0) D2M8K2.t8765 from rfl, totK_node, tot8764, tot8765]
  decide +kernel

theorem arows8759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8759 = true := by
  rw [show D2M8K2.u8759 = KTree.node D2M8K2.t8766 (nat_lit 18824456) (nat_lit 3614242147) (nat_lit 0) D2M8K2.t8767 from rfl, allE_node, rows8766, irow8759, rows8767]
  all_goals rfl

theorem atot8759 : totK PD2M8K2 D2M8K2.u8759 = [0, 0, 183603346047, 738849243931, 735380579788, 109131314767, 1271866555, 0] := by
  rw [show D2M8K2.u8759 = KTree.node D2M8K2.t8766 (nat_lit 18824456) (nat_lit 3614242147) (nat_lit 0) D2M8K2.t8767 from rfl, totK_node, tot8766, tot8767]
  decide +kernel

theorem arows8765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8765 = true := by
  rw [show D2M8K2.u8765 = KTree.node D2M8K2.t8768 (nat_lit 18826392) (nat_lit 3594215546) (nat_lit 0) D2M8K2.t8769 from rfl, allE_node, rows8768, irow8765, rows8769]
  all_goals rfl

theorem atot8765 : totK PD2M8K2 D2M8K2.u8765 = [0, 152780043054, 570245823904, 726152131744, 327024893684, 19889085672, 0, 0] := by
  rw [show D2M8K2.u8765 = KTree.node D2M8K2.t8768 (nat_lit 18826392) (nat_lit 3594215546) (nat_lit 0) D2M8K2.t8769 from rfl, totK_node, tot8768, tot8769]
  decide +kernel

theorem arows8766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8766 = true := by
  rw [show D2M8K2.u8766 = KTree.node D2M8K2.t8770 (nat_lit 18829682) (nat_lit 3791982332) (nat_lit 0) D2M8K2.t8771 from rfl, allE_node, rows8770, irow8766, rows8771]
  all_goals rfl

theorem atot8766 : totK PD2M8K2 D2M8K2.u8766 = [0, 170821955368, 752470049223, 741876858016, 103474053752, 1209030869, 0, 0] := by
  rw [show D2M8K2.u8766 = KTree.node D2M8K2.t8770 (nat_lit 18829682) (nat_lit 3791982332) (nat_lit 0) D2M8K2.t8771 from rfl, totK_node, tot8770, tot8771]
  decide +kernel

theorem arows8768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8768 = true := by
  rw [show D2M8K2.u8768 = KTree.node D2M8K2.t8772 (nat_lit 18832475) (nat_lit 1486520250) (nat_lit 0) D2M8K2.t8773 from rfl, allE_node, rows8772, irow8768, rows8773]
  all_goals rfl

theorem atot8768 : totK PD2M8K2 D2M8K2.u8768 = [0, 355353961395, 891487890723, 525366842482, 52338680232, 0, 0, 0] := by
  rw [show D2M8K2.u8768 = KTree.node D2M8K2.t8772 (nat_lit 18832475) (nat_lit 1486520250) (nat_lit 0) D2M8K2.t8773 from rfl, totK_node, tot8772, tot8773]
  decide +kernel

theorem arows8769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8769 = true := by
  rw [show D2M8K2.u8769 = KTree.node D2M8K2.t8774 (nat_lit 18833995) (nat_lit 1648238221) (nat_lit 0) D2M8K2.t8775 from rfl, allE_node, rows8774, irow8769, rows8775]
  all_goals rfl

theorem atot8769 : totK PD2M8K2 D2M8K2.u8769 = [0, 73215069665, 513955932469, 820500076531, 362410176056, 29391110695, 0, 0] := by
  rw [show D2M8K2.u8769 = KTree.node D2M8K2.t8774 (nat_lit 18833995) (nat_lit 1648238221) (nat_lit 0) D2M8K2.t8775 from rfl, totK_node, tot8774, tot8775]
  decide +kernel

theorem arows8772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8772 = true := by
  rw [show D2M8K2.u8772 = KTree.node D2M8K2.t8776 (nat_lit 18835279) (nat_lit 2332778236) (nat_lit 0) D2M8K2.t8777 from rfl, allE_node, rows8776, irow8772, rows8777]
  all_goals rfl

theorem atot8772 : totK PD2M8K2 D2M8K2.u8772 = [0, 241241304989, 671707992347, 669018447600, 225729401104, 8100177866, 0, 0] := by
  rw [show D2M8K2.u8772 = KTree.node D2M8K2.t8776 (nat_lit 18835279) (nat_lit 2332778236) (nat_lit 0) D2M8K2.t8777 from rfl, totK_node, tot8776, tot8777]
  decide +kernel

theorem arows8773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8773 = true := by
  rw [show D2M8K2.u8773 = KTree.node D2M8K2.t8778 (nat_lit 18836915) (nat_lit 2962755239) (nat_lit 0) D2M8K2.t8779 from rfl, allE_node, rows8778, irow8773, rows8779]
  all_goals rfl

theorem atot8773 : totK PD2M8K2 D2M8K2.u8773 = [0, 142124878872, 707475201832, 766373479710, 155624477771, 2309606161, 0, 0] := by
  rw [show D2M8K2.u8773 = KTree.node D2M8K2.t8778 (nat_lit 18836915) (nat_lit 2962755239) (nat_lit 0) D2M8K2.t8779 from rfl, totK_node, tot8778, tot8779]
  decide +kernel

theorem arows8775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8775 = true := by
  rw [show D2M8K2.u8775 = KTree.node D2M8K2.t8780 (nat_lit 18838820) (nat_lit 2768977572) (nat_lit 0) D2M8K2.t8781 from rfl, allE_node, rows8780, irow8775, rows8781]
  all_goals rfl

theorem atot8775 : totK PD2M8K2 D2M8K2.u8775 = [0, 258166282649, 738686316861, 625267135282, 160601412334, 10740121073, 0, 0] := by
  rw [show D2M8K2.u8775 = KTree.node D2M8K2.t8780 (nat_lit 18838820) (nat_lit 2768977572) (nat_lit 0) D2M8K2.t8781 from rfl, totK_node, tot8780, tot8781]
  decide +kernel

theorem arows8776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8776 = true := by
  rw [show D2M8K2.u8776 = KTree.node D2M8K2.t8782 (nat_lit 18840378) (nat_lit 3376302956) (nat_lit 0) D2M8K2.t8783 from rfl, allE_node, rows8782, irow8776, rows8783]
  all_goals rfl

theorem atot8776 : totK PD2M8K2 D2M8K2.u8776 = [0, 157470194010, 716804294404, 759154920723, 152490247542, 2348440009, 0, 0] := by
  rw [show D2M8K2.u8776 = KTree.node D2M8K2.t8782 (nat_lit 18840378) (nat_lit 3376302956) (nat_lit 0) D2M8K2.t8783 from rfl, totK_node, tot8782, tot8783]
  decide +kernel

theorem arows8780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8780 = true := by
  rw [show D2M8K2.u8780 = KTree.node D2M8K2.t8784 (nat_lit 18842214) (nat_lit 3757238787) (nat_lit 0) D2M8K2.t8785 from rfl, allE_node, rows8784, irow8780, rows8785]
  all_goals rfl

theorem atot8780 : totK PD2M8K2 D2M8K2.u8780 = [0, 245603261123, 707309852921, 648226248569, 188616641250, 10902245252, 0, 0] := by
  rw [show D2M8K2.u8780 = KTree.node D2M8K2.t8784 (nat_lit 18842214) (nat_lit 3757238787) (nat_lit 0) D2M8K2.t8785 from rfl, totK_node, tot8784, tot8785]
  decide +kernel

theorem arows8781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8781 = true := by
  rw [show D2M8K2.u8781 = KTree.node D2M8K2.t8786 (nat_lit 18843374) (nat_lit 3845875013) (nat_lit 0) D2M8K2.t8787 from rfl, allE_node, rows8786, irow8781, rows8787]
  all_goals rfl

theorem atot8781 : totK PD2M8K2 D2M8K2.u8781 = [0, 186845441936, 785252556392, 709246981101, 107240571356, 1096505104, 0, 0] := by
  rw [show D2M8K2.u8781 = KTree.node D2M8K2.t8786 (nat_lit 18843374) (nat_lit 3845875013) (nat_lit 0) D2M8K2.t8787 from rfl, totK_node, tot8786, tot8787]
  decide +kernel

theorem arows8783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8783 = true := by
  rw [show D2M8K2.u8783 = KTree.node D2M8K2.t8788 (nat_lit 18849118) (nat_lit 3479082717) (nat_lit 0) D2M8K2.t8789 from rfl, allE_node, rows8788, irow8783, rows8789]
  all_goals rfl

theorem atot8783 : totK PD2M8K2 D2M8K2.u8783 = [0, 0, 444717710650, 997290246334, 309067511168, 7592502197, 0, 0] := by
  rw [show D2M8K2.u8783 = KTree.node D2M8K2.t8788 (nat_lit 18849118) (nat_lit 3479082717) (nat_lit 0) D2M8K2.t8789 from rfl, totK_node, tot8788, tot8789]
  decide +kernel

theorem arows8784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8784 = true := by
  rw [show D2M8K2.u8784 = KTree.node D2M8K2.t8790 (nat_lit 18853046) (nat_lit 3945465005) (nat_lit 0) D2M8K2.t8791 from rfl, allE_node, rows8790, irow8784, rows8791]
  all_goals rfl

theorem atot8784 : totK PD2M8K2 D2M8K2.u8784 = [0, 0, 371372194407, 928180081931, 454890278080, 36100701843, 0, 0] := by
  rw [show D2M8K2.u8784 = KTree.node D2M8K2.t8790 (nat_lit 18853046) (nat_lit 3945465005) (nat_lit 0) D2M8K2.t8791 from rfl, totK_node, tot8790, tot8791]
  decide +kernel

theorem arows8787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8787 = true := by
  rw [show D2M8K2.u8787 = KTree.node D2M8K2.t8792 (nat_lit 18856050) (nat_lit 2918447814) (nat_lit 0) D2M8K2.t8793 from rfl, allE_node, rows8792, irow8787, rows8793]
  all_goals rfl

theorem atot8787 : totK PD2M8K2 D2M8K2.u8787 = [0, 0, 384250493043, 954038632618, 439026271190, 21560363492, 0, 0] := by
  rw [show D2M8K2.u8787 = KTree.node D2M8K2.t8792 (nat_lit 18856050) (nat_lit 2918447814) (nat_lit 0) D2M8K2.t8793 from rfl, totK_node, tot8792, tot8793]
  decide +kernel

theorem arows8788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8788 = true := by
  rw [show D2M8K2.u8788 = KTree.node D2M8K2.t8794 (nat_lit 18859477) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t8795 from rfl, allE_node, rows8794, irow8788, rows8795]
  all_goals rfl

theorem atot8788 : totK PD2M8K2 D2M8K2.u8788 = [0, 0, 389351078920, 947234613155, 438366490599, 23582736986, 0, 0] := by
  rw [show D2M8K2.u8788 = KTree.node D2M8K2.t8794 (nat_lit 18859477) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t8795 from rfl, totK_node, tot8794, tot8795]
  decide +kernel

theorem arows8790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8790 = true := by
  rw [show D2M8K2.u8790 = KTree.node D2M8K2.t8796 (nat_lit 18861051) (nat_lit 3368866172) (nat_lit 0) D2M8K2.t8797 from rfl, allE_node, rows8796, irow8790, rows8797]
  all_goals rfl

theorem atot8790 : totK PD2M8K2 D2M8K2.u8790 = [0, 0, 335225922928, 939444315013, 485449639910, 29586388420, 0, 0] := by
  rw [show D2M8K2.u8790 = KTree.node D2M8K2.t8796 (nat_lit 18861051) (nat_lit 3368866172) (nat_lit 0) D2M8K2.t8797 from rfl, totK_node, tot8796, tot8797]
  decide +kernel

theorem arows8791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8791 = true := by
  rw [show D2M8K2.u8791 = KTree.node D2M8K2.t8798 (nat_lit 18864013) (nat_lit 1374615766) (nat_lit 0) D2M8K2.t8799 from rfl, allE_node, rows8798, irow8791, rows8799]
  all_goals rfl

theorem atot8791 : totK PD2M8K2 D2M8K2.u8791 = [0, 0, 261502822072, 866084036545, 576022422947, 50273986611, 0, 0] := by
  rw [show D2M8K2.u8791 = KTree.node D2M8K2.t8798 (nat_lit 18864013) (nat_lit 1374615766) (nat_lit 0) D2M8K2.t8799 from rfl, totK_node, tot8798, tot8799]
  decide +kernel

theorem arows8796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8796 = true := by
  rw [show D2M8K2.u8796 = KTree.node D2M8K2.t8800 (nat_lit 18869863) (nat_lit 2304102004) (nat_lit 0) D2M8K2.t8801 from rfl, allE_node, rows8800, irow8796, rows8801]
  all_goals rfl

theorem atot8796 : totK PD2M8K2 D2M8K2.u8796 = [0, 238065048061, 576313920747, 464306869260, 405977738630, 100601394923, 1429815836, 0] := by
  rw [show D2M8K2.u8796 = KTree.node D2M8K2.t8800 (nat_lit 18869863) (nat_lit 2304102004) (nat_lit 0) D2M8K2.t8801 from rfl, totK_node, tot8800, tot8801]
  decide +kernel

theorem arows8797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8797 = true := by
  rw [show D2M8K2.u8797 = KTree.node D2M8K2.t8802 (nat_lit 18872065) (nat_lit 1561674922) (nat_lit 0) D2M8K2.t8803 from rfl, allE_node, rows8802, irow8797, rows8803]
  all_goals rfl

theorem atot8797 : totK PD2M8K2 D2M8K2.u8797 = [0, 182398590194, 732098737423, 774624269113, 128699063745, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8797 = KTree.node D2M8K2.t8802 (nat_lit 18872065) (nat_lit 1561674922) (nat_lit 0) D2M8K2.t8803 from rfl, totK_node, tot8802, tot8803]
  decide +kernel

theorem arows8799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8799 = true := by
  rw [show D2M8K2.u8799 = KTree.node D2M8K2.t8804 (nat_lit 18874213) (nat_lit 1275479778) (nat_lit 0) D2M8K2.t8805 from rfl, allE_node, rows8804, irow8799, rows8805]
  all_goals rfl

theorem atot8799 : totK PD2M8K2 D2M8K2.u8799 = [0, 335760451003, 913938422442, 529970188501, 42297938573, 0, 0, 0] := by
  rw [show D2M8K2.u8799 = KTree.node D2M8K2.t8804 (nat_lit 18874213) (nat_lit 1275479778) (nat_lit 0) D2M8K2.t8805 from rfl, totK_node, tot8804, tot8805]
  decide +kernel

theorem arows8800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8800 = true := by
  rw [show D2M8K2.u8800 = KTree.node D2M8K2.t8806 (nat_lit 18875698) (nat_lit 3903462409) (nat_lit 0) D2M8K2.t8807 from rfl, allE_node, rows8806, irow8800, rows8807]
  all_goals rfl

theorem atot8800 : totK PD2M8K2 D2M8K2.u8800 = [0, 0, 389957342800, 931903553438, 441165971783, 30675760985, 0, 0] := by
  rw [show D2M8K2.u8800 = KTree.node D2M8K2.t8806 (nat_lit 18875698) (nat_lit 3903462409) (nat_lit 0) D2M8K2.t8807 from rfl, totK_node, tot8806, tot8807]
  decide +kernel

theorem arows8803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8803 = true := by
  rw [show D2M8K2.u8803 = KTree.node D2M8K2.t8808 (nat_lit 18877085) (nat_lit 2276426875) (nat_lit 0) D2M8K2.t8809 from rfl, allE_node, rows8808, irow8803, rows8809]
  all_goals rfl

theorem atot8803 : totK PD2M8K2 D2M8K2.u8803 = [0, 296557138691, 795041831281, 580505358620, 145489995038, 6804944647, 0, 0] := by
  rw [show D2M8K2.u8803 = KTree.node D2M8K2.t8808 (nat_lit 18877085) (nat_lit 2276426875) (nat_lit 0) D2M8K2.t8809 from rfl, totK_node, tot8808, tot8809]
  decide +kernel

theorem arows8804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8804 = true := by
  rw [show D2M8K2.u8804 = KTree.node D2M8K2.t8810 (nat_lit 18878745) (nat_lit 1783197223) (nat_lit 0) D2M8K2.t8811 from rfl, allE_node, rows8810, irow8804, rows8811]
  all_goals rfl

theorem atot8804 : totK PD2M8K2 D2M8K2.u8804 = [0, 88824698027, 586448422143, 859873926016, 243688704498, 9068544132, 0, 0] := by
  rw [show D2M8K2.u8804 = KTree.node D2M8K2.t8810 (nat_lit 18878745) (nat_lit 1783197223) (nat_lit 0) D2M8K2.t8811 from rfl, totK_node, tot8810, tot8811]
  decide +kernel

theorem arows8806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8806 = true := by
  rw [show D2M8K2.u8806 = KTree.node D2M8K2.t8812 (nat_lit 18880639) (nat_lit 2420449048) (nat_lit 0) D2M8K2.t8813 from rfl, allE_node, rows8812, irow8806, rows8813]
  all_goals rfl

theorem atot8806 : totK PD2M8K2 D2M8K2.u8806 = [0, 331276003976, 901631370094, 542105082720, 57664947199, 0, 0, 0] := by
  rw [show D2M8K2.u8806 = KTree.node D2M8K2.t8812 (nat_lit 18880639) (nat_lit 2420449048) (nat_lit 0) D2M8K2.t8813 from rfl, totK_node, tot8812, tot8813]
  decide +kernel

theorem arows8807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8807 = true := by
  rw [show D2M8K2.u8807 = KTree.node D2M8K2.t8814 (nat_lit 18882218) (nat_lit 4126665669) (nat_lit 0) D2M8K2.t8815 from rfl, allE_node, rows8814, irow8807, rows8815]
  all_goals rfl

theorem atot8807 : totK PD2M8K2 D2M8K2.u8807 = [0, 85687109263, 561515088867, 872425287316, 264902086190, 9179787334, 0, 0] := by
  rw [show D2M8K2.u8807 = KTree.node D2M8K2.t8814 (nat_lit 18882218) (nat_lit 4126665669) (nat_lit 0) D2M8K2.t8815 from rfl, totK_node, tot8814, tot8815]
  decide +kernel

theorem arows8811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8811 = true := by
  rw [show D2M8K2.u8811 = KTree.node D2M8K2.t8816 (nat_lit 18887518) (nat_lit 3768840658) (nat_lit 0) D2M8K2.t8817 from rfl, allE_node, rows8816, irow8811, rows8817]
  all_goals rfl

theorem atot8811 : totK PD2M8K2 D2M8K2.u8811 = [0, 346999970823, 897425341744, 528751642118, 57852377115, 0, 0, 0] := by
  rw [show D2M8K2.u8811 = KTree.node D2M8K2.t8816 (nat_lit 18887518) (nat_lit 3768840658) (nat_lit 0) D2M8K2.t8817 from rfl, totK_node, tot8816, tot8817]
  decide +kernel

theorem arows8812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8812 = true := by
  rw [show D2M8K2.u8812 = KTree.node D2M8K2.t8818 (nat_lit 18888960) (nat_lit 3523492961) (nat_lit 0) D2M8K2.t8819 from rfl, allE_node, rows8818, irow8812, rows8819]
  all_goals rfl

theorem atot8812 : totK PD2M8K2 D2M8K2.u8812 = [0, 93768764846, 622925760075, 864104395740, 216104581120, 4909780899, 0, 0] := by
  rw [show D2M8K2.u8812 = KTree.node D2M8K2.t8818 (nat_lit 18888960) (nat_lit 3523492961) (nat_lit 0) D2M8K2.t8819 from rfl, totK_node, tot8818, tot8819]
  decide +kernel

theorem arows8814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8814 = true := by
  rw [show D2M8K2.u8814 = KTree.node D2M8K2.t8820 (nat_lit 18890605) (nat_lit 1134544092) (nat_lit 0) D2M8K2.t8821 from rfl, allE_node, rows8820, irow8814, rows8821]
  all_goals rfl

theorem atot8814 : totK PD2M8K2 D2M8K2.u8814 = [0, 0, 468587336613, 971678933118, 341003976672, 18411378955, 0, 0] := by
  rw [show D2M8K2.u8814 = KTree.node D2M8K2.t8820 (nat_lit 18890605) (nat_lit 1134544092) (nat_lit 0) D2M8K2.t8821 from rfl, totK_node, tot8820, tot8821]
  decide +kernel

theorem arows8815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8815 = true := by
  rw [show D2M8K2.u8815 = KTree.node D2M8K2.t8822 (nat_lit 18894836) (nat_lit 1979434967) (nat_lit 0) D2M8K2.t8823 from rfl, allE_node, rows8822, irow8815, rows8823]
  all_goals rfl

theorem atot8815 : totK PD2M8K2 D2M8K2.u8815 = [0, 0, 382551386440, 922973813746, 470031930855, 33581013520, 0, 0] := by
  rw [show D2M8K2.u8815 = KTree.node D2M8K2.t8822 (nat_lit 18894836) (nat_lit 1979434967) (nat_lit 0) D2M8K2.t8823 from rfl, totK_node, tot8822, tot8823]
  decide +kernel

theorem arows8818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8818 = true := by
  rw [show D2M8K2.u8818 = KTree.node D2M8K2.t8824 (nat_lit 18897919) (nat_lit 2210480481) (nat_lit 0) D2M8K2.t8825 from rfl, allE_node, rows8824, irow8818, rows8825]
  all_goals rfl

theorem atot8818 : totK PD2M8K2 D2M8K2.u8818 = [0, 0, 348346424676, 899722732813, 512292901602, 39825347874, 0, 0] := by
  rw [show D2M8K2.u8818 = KTree.node D2M8K2.t8824 (nat_lit 18897919) (nat_lit 2210480481) (nat_lit 0) D2M8K2.t8825 from rfl, totK_node, tot8824, tot8825]
  decide +kernel

theorem arows8819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8819 = true := by
  rw [show D2M8K2.u8819 = KTree.node D2M8K2.t8826 (nat_lit 18899833) (nat_lit 1458770128) (nat_lit 0) D2M8K2.t8827 from rfl, allE_node, rows8826, irow8819, rows8827]
  all_goals rfl

theorem atot8819 : totK PD2M8K2 D2M8K2.u8819 = [0, 0, 157800601480, 746519083609, 775802807115, 110160168806, 1323630408, 0] := by
  rw [show D2M8K2.u8819 = KTree.node D2M8K2.t8826 (nat_lit 18899833) (nat_lit 1458770128) (nat_lit 0) D2M8K2.t8827 from rfl, totK_node, tot8826, tot8827]
  decide +kernel

theorem arows8821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8821 = true := by
  rw [show D2M8K2.u8821 = KTree.node D2M8K2.t8828 (nat_lit 18902048) (nat_lit 3776799967) (nat_lit 0) D2M8K2.t8829 from rfl, allE_node, rows8828, irow8821, rows8829]
  all_goals rfl

theorem atot8821 : totK PD2M8K2 D2M8K2.u8821 = [0, 0, 306135660307, 889523979854, 562749431227, 45543241993, 0, 0] := by
  rw [show D2M8K2.u8821 = KTree.node D2M8K2.t8828 (nat_lit 18902048) (nat_lit 3776799967) (nat_lit 0) D2M8K2.t8829 from rfl, totK_node, tot8828, tot8829]
  decide +kernel

theorem arows8822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8822 = true := by
  rw [show D2M8K2.u8822 = KTree.node D2M8K2.t8830 (nat_lit 18907787) (nat_lit 2928354468) (nat_lit 0) D2M8K2.t8831 from rfl, allE_node, rows8830, irow8822, rows8831]
  all_goals rfl

theorem atot8822 : totK PD2M8K2 D2M8K2.u8822 = [0, 0, 203987871170, 770862992691, 706237100323, 111706499776, 1332468113, 0] := by
  rw [show D2M8K2.u8822 = KTree.node D2M8K2.t8830 (nat_lit 18907787) (nat_lit 2928354468) (nat_lit 0) D2M8K2.t8831 from rfl, totK_node, tot8830, tot8831]
  decide +kernel

theorem arows8829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8829 = true := by
  rw [show D2M8K2.u8829 = KTree.node D2M8K2.t8832 (nat_lit 18909286) (nat_lit 3849526529) (nat_lit 0) D2M8K2.t8833 from rfl, allE_node, rows8832, irow8829, rows8833]
  all_goals rfl

theorem atot8829 : totK PD2M8K2 D2M8K2.u8829 = [0, 0, 228781165889, 846136113268, 659944581216, 56033926087, 0, 0] := by
  rw [show D2M8K2.u8829 = KTree.node D2M8K2.t8832 (nat_lit 18909286) (nat_lit 3849526529) (nat_lit 0) D2M8K2.t8833 from rfl, totK_node, tot8832, tot8833]
  decide +kernel

theorem arows8830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8830 = true := by
  rw [show D2M8K2.u8830 = KTree.node D2M8K2.t8834 (nat_lit 18911160) (nat_lit 3229931674) (nat_lit 0) D2M8K2.t8835 from rfl, allE_node, rows8834, irow8830, rows8835]
  all_goals rfl

theorem atot8830 : totK PD2M8K2 D2M8K2.u8830 = [173526806713, 428665407054, 186617504486, 201113663300, 532492236155, 219566865795, 9533751846, 0] := by
  rw [show D2M8K2.u8830 = KTree.node D2M8K2.t8834 (nat_lit 18911160) (nat_lit 3229931674) (nat_lit 0) D2M8K2.t8835 from rfl, totK_node, tot8834, tot8835]
  decide +kernel

theorem arows8832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8832 = true := by
  rw [show D2M8K2.u8832 = KTree.node D2M8K2.t8836 (nat_lit 19410358) (nat_lit 3576224356) (nat_lit 0) D2M8K2.t8837 from rfl, allE_node, rows8836, irow8832, rows8837]
  all_goals rfl

theorem atot8832 : totK PD2M8K2 D2M8K2.u8832 = [261972625305, 805634955032, 630700189926, 105073408665, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8832 = KTree.node D2M8K2.t8836 (nat_lit 19410358) (nat_lit 3576224356) (nat_lit 0) D2M8K2.t8837 from rfl, totK_node, tot8836, tot8837]
  decide +kernel

theorem arows8833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8833 = true := by
  rw [show D2M8K2.u8833 = KTree.node D2M8K2.t8838 (nat_lit 19415866) (nat_lit 3899492587) (nat_lit 0) D2M8K2.t8839 from rfl, allE_node, rows8838, irow8833, rows8839]
  all_goals rfl

theorem atot8833 : totK PD2M8K2 D2M8K2.u8833 = [238987653557, 810577666287, 679737776631, 73725666311, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8833 = KTree.node D2M8K2.t8838 (nat_lit 19415866) (nat_lit 3899492587) (nat_lit 0) D2M8K2.t8839 from rfl, totK_node, tot8838, tot8839]
  decide +kernel

theorem arows8836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8836 = true := by
  rw [show D2M8K2.u8836 = KTree.node D2M8K2.t8840 (nat_lit 19417729) (nat_lit 1441321856) (nat_lit 0) D2M8K2.t8841 from rfl, allE_node, rows8840, irow8836, rows8841]
  all_goals rfl

theorem atot8836 : totK PD2M8K2 D2M8K2.u8836 = [82780561812, 575505422262, 823927882296, 244318405677, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u8836 = KTree.node D2M8K2.t8840 (nat_lit 19417729) (nat_lit 1441321856) (nat_lit 0) D2M8K2.t8841 from rfl, totK_node, tot8840, tot8841]
  decide +kernel

theorem arows8837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8837 = true := by
  rw [show D2M8K2.u8837 = KTree.node D2M8K2.t8842 (nat_lit 19419808) (nat_lit 2589062349) (nat_lit 0) D2M8K2.t8843 from rfl, allE_node, rows8842, irow8837, rows8843]
  all_goals rfl

theorem atot8837 : totK PD2M8K2 D2M8K2.u8837 = [338960369015, 912683185894, 519332128497, 51375906634, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8837 = KTree.node D2M8K2.t8842 (nat_lit 19419808) (nat_lit 2589062349) (nat_lit 0) D2M8K2.t8843 from rfl, totK_node, tot8842, tot8843]
  decide +kernel

theorem arows8839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8839 = true := by
  rw [show D2M8K2.u8839 = KTree.node D2M8K2.t8844 (nat_lit 19421325) (nat_lit 1464097571) (nat_lit 0) D2M8K2.t8845 from rfl, allE_node, rows8844, irow8839, rows8845]
  all_goals rfl

theorem atot8839 : totK PD2M8K2 D2M8K2.u8839 = [87346212865, 561111957113, 874322721464, 256443689109, 10680993762, 0, 0, 0] := by
  rw [show D2M8K2.u8839 = KTree.node D2M8K2.t8844 (nat_lit 19421325) (nat_lit 1464097571) (nat_lit 0) D2M8K2.t8845 from rfl, totK_node, tot8844, tot8845]
  decide +kernel

theorem arows8840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8840 = true := by
  rw [show D2M8K2.u8840 = KTree.node D2M8K2.t8846 (nat_lit 19423111) (nat_lit 2347919392) (nat_lit 0) D2M8K2.t8847 from rfl, allE_node, rows8846, irow8840, rows8847]
  all_goals rfl

theorem atot8840 : totK PD2M8K2 D2M8K2.u8840 = [317728275370, 830467829906, 542257055488, 90186942012, 2569691499, 0, 0, 0] := by
  rw [show D2M8K2.u8840 = KTree.node D2M8K2.t8846 (nat_lit 19423111) (nat_lit 2347919392) (nat_lit 0) D2M8K2.t8847 from rfl, totK_node, tot8846, tot8847]
  decide +kernel

theorem arows8844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8844 = true := by
  rw [show D2M8K2.u8844 = KTree.node D2M8K2.t8848 (nat_lit 19424689) (nat_lit 1423666189) (nat_lit 0) D2M8K2.t8849 from rfl, allE_node, rows8848, irow8844, rows8849]
  all_goals rfl

theorem atot8844 : totK PD2M8K2 D2M8K2.u8844 = [90840904916, 701876369695, 858964721707, 139565581078, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u8844 = KTree.node D2M8K2.t8848 (nat_lit 19424689) (nat_lit 1423666189) (nat_lit 0) D2M8K2.t8849 from rfl, totK_node, tot8848, tot8849]
  decide +kernel

theorem arows8845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8845 = true := by
  rw [show D2M8K2.u8845 = KTree.node D2M8K2.t8850 (nat_lit 19426692) (nat_lit 1438821998) (nat_lit 0) D2M8K2.t8851 from rfl, allE_node, rows8850, irow8845, rows8851]
  all_goals rfl

theorem atot8845 : totK PD2M8K2 D2M8K2.u8845 = [321432167778, 821326728876, 537414714936, 108499241430, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u8845 = KTree.node D2M8K2.t8850 (nat_lit 19426692) (nat_lit 1438821998) (nat_lit 0) D2M8K2.t8851 from rfl, totK_node, tot8850, tot8851]
  decide +kernel

theorem arows8847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8847 = true := by
  rw [show D2M8K2.u8847 = KTree.node D2M8K2.t8852 (nat_lit 19428234) (nat_lit 3809218501) (nat_lit 0) D2M8K2.t8853 from rfl, allE_node, rows8852, irow8847, rows8853]
  all_goals rfl

theorem atot8847 : totK PD2M8K2 D2M8K2.u8847 = [92232705550, 556324612395, 856034514058, 268668468227, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u8847 = KTree.node D2M8K2.t8852 (nat_lit 19428234) (nat_lit 3809218501) (nat_lit 0) D2M8K2.t8853 from rfl, totK_node, tot8852, tot8853]
  decide +kernel

theorem arows8848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8848 = true := by
  rw [show D2M8K2.u8848 = KTree.node D2M8K2.t8854 (nat_lit 19429898) (nat_lit 3184525428) (nat_lit 0) D2M8K2.t8855 from rfl, allE_node, rows8854, irow8848, rows8855]
  all_goals rfl

theorem atot8848 : totK PD2M8K2 D2M8K2.u8848 = [0, 370023194653, 924789028861, 442587721147, 31340853708, 0, 0, 0] := by
  rw [show D2M8K2.u8848 = KTree.node D2M8K2.t8854 (nat_lit 19429898) (nat_lit 3184525428) (nat_lit 0) D2M8K2.t8855 from rfl, totK_node, tot8854, tot8855]
  decide +kernel

theorem arows8851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8851 = true := by
  rw [show D2M8K2.u8851 = KTree.node D2M8K2.t8856 (nat_lit 19431413) (nat_lit 2374285811) (nat_lit 0) D2M8K2.t8857 from rfl, allE_node, rows8856, irow8851, rows8857]
  all_goals rfl

theorem atot8851 : totK PD2M8K2 D2M8K2.u8851 = [0, 155510060804, 742832233393, 709977059207, 125156980604, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8851 = KTree.node D2M8K2.t8856 (nat_lit 19431413) (nat_lit 2374285811) (nat_lit 0) D2M8K2.t8857 from rfl, totK_node, tot8856, tot8857]
  decide +kernel

theorem arows8852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8852 = true := by
  rw [show D2M8K2.u8852 = KTree.node D2M8K2.t8858 (nat_lit 19437274) (nat_lit 3752601801) (nat_lit 0) D2M8K2.t8859 from rfl, allE_node, rows8858, irow8852, rows8859]
  all_goals rfl

theorem atot8852 : totK PD2M8K2 D2M8K2.u8852 = [0, 320855252720, 890573624442, 502691240337, 38782382147, 0, 0, 0] := by
  rw [show D2M8K2.u8852 = KTree.node D2M8K2.t8858 (nat_lit 19437274) (nat_lit 3752601801) (nat_lit 0) D2M8K2.t8859 from rfl, totK_node, tot8858, tot8859]
  decide +kernel

theorem arows8854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8854 = true := by
  rw [show D2M8K2.u8854 = KTree.node D2M8K2.t8860 (nat_lit 19440909) (nat_lit 1456575001) (nat_lit 0) D2M8K2.t8861 from rfl, allE_node, rows8860, irow8854, rows8861]
  all_goals rfl

theorem atot8854 : totK PD2M8K2 D2M8K2.u8854 = [0, 387424578883, 953990739369, 435345816275, 22800187125, 0, 0, 0] := by
  rw [show D2M8K2.u8854 = KTree.node D2M8K2.t8860 (nat_lit 19440909) (nat_lit 1456575001) (nat_lit 0) D2M8K2.t8861 from rfl, totK_node, tot8860, tot8861]
  decide +kernel

theorem arows8855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8855 = true := by
  rw [show D2M8K2.u8855 = KTree.node D2M8K2.t8862 (nat_lit 19443916) (nat_lit 3572368837) (nat_lit 0) D2M8K2.t8863 from rfl, allE_node, rows8862, irow8855, rows8863]
  all_goals rfl

theorem atot8855 : totK PD2M8K2 D2M8K2.u8855 = [0, 354877835795, 937995326371, 452117757808, 25901910195, 0, 0, 0] := by
  rw [show D2M8K2.u8855 = KTree.node D2M8K2.t8862 (nat_lit 19443916) (nat_lit 3572368837) (nat_lit 0) D2M8K2.t8863 from rfl, totK_node, tot8862, tot8863]
  decide +kernel

theorem arows8860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8860 = true := by
  rw [show D2M8K2.u8860 = KTree.node D2M8K2.t8864 (nat_lit 19447239) (nat_lit 3633509164) (nat_lit 0) D2M8K2.t8865 from rfl, allE_node, rows8864, irow8860, rows8865]
  all_goals rfl

theorem atot8860 : totK PD2M8K2 D2M8K2.u8860 = [0, 392730920061, 957061523854, 424619469589, 18558628451, 0, 0, 0] := by
  rw [show D2M8K2.u8860 = KTree.node D2M8K2.t8864 (nat_lit 19447239) (nat_lit 3633509164) (nat_lit 0) D2M8K2.t8865 from rfl, totK_node, tot8864, tot8865]
  decide +kernel

theorem arows8861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8861 = true := by
  rw [show D2M8K2.u8861 = KTree.node D2M8K2.t8866 (nat_lit 19454226) (nat_lit 3410736303) (nat_lit 0) D2M8K2.t8867 from rfl, allE_node, rows8866, irow8861, rows8867]
  all_goals rfl

theorem atot8861 : totK PD2M8K2 D2M8K2.u8861 = [248959702445, 671739028021, 651914468887, 252487474928, 17433533548, 0, 0, 0] := by
  rw [show D2M8K2.u8861 = KTree.node D2M8K2.t8866 (nat_lit 19454226) (nat_lit 3410736303) (nat_lit 0) D2M8K2.t8867 from rfl, totK_node, tot8866, tot8867]
  decide +kernel

theorem arows8863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8863 = true := by
  rw [show D2M8K2.u8863 = KTree.node D2M8K2.t8868 (nat_lit 19455403) (nat_lit 1606342289) (nat_lit 0) D2M8K2.t8869 from rfl, allE_node, rows8868, irow8863, rows8869]
  all_goals rfl

theorem atot8863 : totK PD2M8K2 D2M8K2.u8863 = [195143075606, 737195040860, 677251314304, 205914136832, 21400436502, 0, 0, 0] := by
  rw [show D2M8K2.u8863 = KTree.node D2M8K2.t8868 (nat_lit 19455403) (nat_lit 1606342289) (nat_lit 0) D2M8K2.t8869 from rfl, totK_node, tot8868, tot8869]
  decide +kernel

theorem arows8864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8864 = true := by
  rw [show D2M8K2.u8864 = KTree.node D2M8K2.t8870 (nat_lit 19456876) (nat_lit 3785236362) (nat_lit 0) D2M8K2.t8871 from rfl, allE_node, rows8870, irow8864, rows8871]
  all_goals rfl

theorem atot8864 : totK PD2M8K2 D2M8K2.u8864 = [89930224278, 464591859732, 859693589642, 389237317976, 16208961603, 0, 0, 0] := by
  rw [show D2M8K2.u8864 = KTree.node D2M8K2.t8870 (nat_lit 19456876) (nat_lit 3785236362) (nat_lit 0) D2M8K2.t8871 from rfl, totK_node, tot8870, tot8871]
  decide +kernel

theorem arows8867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8867 = true := by
  rw [show D2M8K2.u8867 = KTree.node D2M8K2.t8872 (nat_lit 19458725) (nat_lit 1769389834) (nat_lit 0) D2M8K2.t8873 from rfl, allE_node, rows8872, irow8867, rows8873]
  all_goals rfl

theorem atot8867 : totK PD2M8K2 D2M8K2.u8867 = [238776117534, 829061689763, 680829790471, 86899474126, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8867 = KTree.node D2M8K2.t8872 (nat_lit 19458725) (nat_lit 1769389834) (nat_lit 0) D2M8K2.t8873 from rfl, totK_node, tot8872, tot8873]
  decide +kernel

theorem arows8868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8868 = true := by
  rw [show D2M8K2.u8868 = KTree.node D2M8K2.t8874 (nat_lit 19460867) (nat_lit 2946700023) (nat_lit 0) D2M8K2.t8875 from rfl, allE_node, rows8874, irow8868, rows8875]
  all_goals rfl

theorem atot8868 : totK PD2M8K2 D2M8K2.u8868 = [254119108645, 730211289837, 645267700386, 173016098899, 10536635055, 0, 0, 0] := by
  rw [show D2M8K2.u8868 = KTree.node D2M8K2.t8874 (nat_lit 19460867) (nat_lit 2946700023) (nat_lit 0) D2M8K2.t8875 from rfl, totK_node, tot8874, tot8875]
  decide +kernel

theorem arows8870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8870 = true := by
  rw [show D2M8K2.u8870 = KTree.node D2M8K2.t8876 (nat_lit 19462349) (nat_lit 2012010561) (nat_lit 0) D2M8K2.t8877 from rfl, allE_node, rows8876, irow8870, rows8877]
  all_goals rfl

theorem atot8870 : totK PD2M8K2 D2M8K2.u8870 = [173439528345, 764553671652, 749309039082, 126103980065, 1197396724, 0, 0, 0] := by
  rw [show D2M8K2.u8870 = KTree.node D2M8K2.t8876 (nat_lit 19462349) (nat_lit 2012010561) (nat_lit 0) D2M8K2.t8877 from rfl, totK_node, tot8876, tot8877]
  decide +kernel

theorem arows8871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8871 = true := by
  rw [show D2M8K2.u8871 = KTree.node D2M8K2.t8878 (nat_lit 19464046) (nat_lit 4051426970) (nat_lit 0) D2M8K2.t8879 from rfl, allE_node, rows8878, irow8871, rows8879]
  all_goals rfl

theorem atot8871 : totK PD2M8K2 D2M8K2.u8871 = [193690295225, 643083946598, 722118257401, 221073778969, 12040273252, 0, 0, 0] := by
  rw [show D2M8K2.u8871 = KTree.node D2M8K2.t8878 (nat_lit 19464046) (nat_lit 4051426970) (nat_lit 0) D2M8K2.t8879 from rfl, totK_node, tot8878, tot8879]
  decide +kernel

theorem arows8875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8875 = true := by
  rw [show D2M8K2.u8875 = KTree.node D2M8K2.t8880 (nat_lit 19465424) (nat_lit 3823420766) (nat_lit 0) D2M8K2.t8881 from rfl, allE_node, rows8880, irow8875, rows8881]
  all_goals rfl

theorem atot8875 : totK PD2M8K2 D2M8K2.u8875 = [217921343792, 796345599785, 676017910290, 104331562711, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u8875 = KTree.node D2M8K2.t8880 (nat_lit 19465424) (nat_lit 3823420766) (nat_lit 0) D2M8K2.t8881 from rfl, totK_node, tot8880, tot8881]
  decide +kernel

theorem arows8876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8876 = true := by
  rw [show D2M8K2.u8876 = KTree.node D2M8K2.t8882 (nat_lit 19467771) (nat_lit 3104845869) (nat_lit 0) D2M8K2.t8883 from rfl, allE_node, rows8882, irow8876, rows8883]
  all_goals rfl

theorem atot8876 : totK PD2M8K2 D2M8K2.u8876 = [237367762888, 755744637011, 690646475219, 139055877136, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u8876 = KTree.node D2M8K2.t8882 (nat_lit 19467771) (nat_lit 3104845869) (nat_lit 0) D2M8K2.t8883 from rfl, totK_node, tot8882, tot8883]
  decide +kernel

theorem arows8878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8878 = true := by
  rw [show D2M8K2.u8878 = KTree.node D2M8K2.t8884 (nat_lit 19469265) (nat_lit 1254848025) (nat_lit 0) D2M8K2.t8885 from rfl, allE_node, rows8884, irow8878, rows8885]
  all_goals rfl

theorem atot8878 : totK PD2M8K2 D2M8K2.u8878 = [179724476225, 756196729801, 747019658633, 133479275219, 1267860612, 0, 0, 0] := by
  rw [show D2M8K2.u8878 = KTree.node D2M8K2.t8884 (nat_lit 19469265) (nat_lit 1254848025) (nat_lit 0) D2M8K2.t8885 from rfl, totK_node, tot8884, tot8885]
  decide +kernel

theorem arows8879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8879 = true := by
  rw [show D2M8K2.u8879 = KTree.node D2M8K2.t8886 (nat_lit 19470990) (nat_lit 3661891380) (nat_lit 0) D2M8K2.t8887 from rfl, allE_node, rows8886, irow8879, rows8887]
  all_goals rfl

theorem atot8879 : totK PD2M8K2 D2M8K2.u8879 = [0, 361150427351, 920365071657, 478832376009, 42673056605, 0, 0, 0] := by
  rw [show D2M8K2.u8879 = KTree.node D2M8K2.t8886 (nat_lit 19470990) (nat_lit 3661891380) (nat_lit 0) D2M8K2.t8887 from rfl, totK_node, tot8886, tot8887]
  decide +kernel

theorem arows8882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8882 = true := by
  rw [show D2M8K2.u8882 = KTree.node D2M8K2.t8888 (nat_lit 19475890) (nat_lit 3482505753) (nat_lit 0) D2M8K2.t8889 from rfl, allE_node, rows8888, irow8882, rows8889]
  all_goals rfl

theorem atot8882 : totK PD2M8K2 D2M8K2.u8882 = [0, 264863258612, 850759307968, 617025006627, 93874588136, 10444649207, 0, 0] := by
  rw [show D2M8K2.u8882 = KTree.node D2M8K2.t8888 (nat_lit 19475890) (nat_lit 3482505753) (nat_lit 0) D2M8K2.t8889 from rfl, totK_node, tot8888, tot8889]
  decide +kernel

theorem arows8883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8883 = true := by
  rw [show D2M8K2.u8883 = KTree.node D2M8K2.t8890 (nat_lit 19477395) (nat_lit 2570778197) (nat_lit 0) D2M8K2.t8891 from rfl, allE_node, rows8890, irow8883, rows8891]
  all_goals rfl

theorem atot8883 : totK PD2M8K2 D2M8K2.u8883 = [0, 19809922038, 361503163691, 907483918609, 460875223241, 26477224647, 0, 0] := by
  rw [show D2M8K2.u8883 = KTree.node D2M8K2.t8890 (nat_lit 19477395) (nat_lit 2570778197) (nat_lit 0) D2M8K2.t8891 from rfl, totK_node, tot8890, tot8891]
  decide +kernel

theorem arows8885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8885 = true := by
  rw [show D2M8K2.u8885 = KTree.node D2M8K2.t8892 (nat_lit 19479213) (nat_lit 1500645314) (nat_lit 0) D2M8K2.t8893 from rfl, allE_node, rows8892, irow8885, rows8893]
  all_goals rfl

theorem atot8885 : totK PD2M8K2 D2M8K2.u8885 = [0, 307795553703, 886916658538, 572372558154, 61318465383, 0, 0, 0] := by
  rw [show D2M8K2.u8885 = KTree.node D2M8K2.t8892 (nat_lit 19479213) (nat_lit 1500645314) (nat_lit 0) D2M8K2.t8893 from rfl, totK_node, tot8892, tot8893]
  decide +kernel

theorem arows8886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8886 = true := by
  rw [show D2M8K2.u8886 = KTree.node D2M8K2.t8894 (nat_lit 19481244) (nat_lit 2452971622) (nat_lit 0) D2M8K2.t8895 from rfl, allE_node, rows8894, irow8886, rows8895]
  all_goals rfl

theorem atot8886 : totK PD2M8K2 D2M8K2.u8886 = [0, 160940599401, 672384457782, 780341389715, 186501489925, 5159868635, 0, 0] := by
  rw [show D2M8K2.u8886 = KTree.node D2M8K2.t8894 (nat_lit 19481244) (nat_lit 2452971622) (nat_lit 0) D2M8K2.t8895 from rfl, totK_node, tot8894, tot8895]
  decide +kernel

theorem arows8892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8892 = true := by
  rw [show D2M8K2.u8892 = KTree.node D2M8K2.t8896 (nat_lit 19482924) (nat_lit 3415698460) (nat_lit 0) D2M8K2.t8897 from rfl, allE_node, rows8896, irow8892, rows8897]
  all_goals rfl

theorem atot8892 : totK PD2M8K2 D2M8K2.u8892 = [0, 264989418676, 870637462295, 618214369679, 62756916442, 0, 0, 0] := by
  rw [show D2M8K2.u8892 = KTree.node D2M8K2.t8896 (nat_lit 19482924) (nat_lit 3415698460) (nat_lit 0) D2M8K2.t8897 from rfl, totK_node, tot8896, tot8897]
  decide +kernel

theorem arows8893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8893 = true := by
  rw [show D2M8K2.u8893 = KTree.node D2M8K2.t8898 (nat_lit 19484771) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t8899 from rfl, allE_node, rows8898, irow8893, rows8899]
  all_goals rfl

theorem atot8893 : totK PD2M8K2 D2M8K2.u8893 = [0, 186604081136, 661804562354, 742571643667, 191250928943, 5218872685, 0, 0] := by
  rw [show D2M8K2.u8893 = KTree.node D2M8K2.t8898 (nat_lit 19484771) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t8899 from rfl, totK_node, tot8898, tot8899]
  decide +kernel

theorem arows8895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8895 = true := by
  rw [show D2M8K2.u8895 = KTree.node D2M8K2.t8900 (nat_lit 19486149) (nat_lit 1516654908) (nat_lit 0) D2M8K2.t8901 from rfl, allE_node, rows8900, irow8895, rows8901]
  all_goals rfl

theorem atot8895 : totK PD2M8K2 D2M8K2.u8895 = [0, 224031715498, 839875861217, 668223734298, 64514355512, 0, 0, 0] := by
  rw [show D2M8K2.u8895 = KTree.node D2M8K2.t8900 (nat_lit 19486149) (nat_lit 1516654908) (nat_lit 0) D2M8K2.t8901 from rfl, totK_node, tot8900, tot8901]
  decide +kernel

theorem arows8896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8896 = true := by
  rw [show D2M8K2.u8896 = KTree.node D2M8K2.t8902 (nat_lit 19488610) (nat_lit 3856370209) (nat_lit 0) D2M8K2.t8903 from rfl, allE_node, rows8902, irow8896, rows8903]
  all_goals rfl

theorem atot8896 : totK PD2M8K2 D2M8K2.u8896 = [0, 236763725527, 776605339567, 679759776087, 121797330253, 1415142070, 0, 0] := by
  rw [show D2M8K2.u8896 = KTree.node D2M8K2.t8902 (nat_lit 19488610) (nat_lit 3856370209) (nat_lit 0) D2M8K2.t8903 from rfl, totK_node, tot8902, tot8903]
  decide +kernel

theorem arows8899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8899 = true := by
  rw [show D2M8K2.u8899 = KTree.node D2M8K2.t8904 (nat_lit 19490104) (nat_lit 3369857075) (nat_lit 0) D2M8K2.t8905 from rfl, allE_node, rows8904, irow8899, rows8905]
  all_goals rfl

theorem atot8899 : totK PD2M8K2 D2M8K2.u8899 = [0, 179238291557, 764598857133, 735001173964, 129573351026, 1238673482, 0, 0] := by
  rw [show D2M8K2.u8899 = KTree.node D2M8K2.t8904 (nat_lit 19490104) (nat_lit 3369857075) (nat_lit 0) D2M8K2.t8905 from rfl, totK_node, tot8904, tot8905]
  decide +kernel

theorem arows8900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8900 = true := by
  rw [show D2M8K2.u8900 = KTree.node D2M8K2.t8906 (nat_lit 19533462) (nat_lit 3692991218) (nat_lit 0) D2M8K2.t8907 from rfl, allE_node, rows8906, irow8900, rows8907]
  all_goals rfl

theorem atot8900 : totK PD2M8K2 D2M8K2.u8900 = [245244981206, 605520578649, 392909956350, 359473401774, 161247805254, 8063697217, 0, 0] := by
  rw [show D2M8K2.u8900 = KTree.node D2M8K2.t8906 (nat_lit 19533462) (nat_lit 3692991218) (nat_lit 0) D2M8K2.t8907 from rfl, totK_node, tot8906, tot8907]
  decide +kernel

theorem arows8902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8902 = true := by
  rw [show D2M8K2.u8902 = KTree.node D2M8K2.t8908 (nat_lit 19535041) (nat_lit 1575612183) (nat_lit 0) D2M8K2.t8909 from rfl, allE_node, rows8908, irow8902, rows8909]
  all_goals rfl

theorem atot8902 : totK PD2M8K2 D2M8K2.u8902 = [171580439313, 738642377771, 757542103251, 125964004996, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8902 = KTree.node D2M8K2.t8908 (nat_lit 19535041) (nat_lit 1575612183) (nat_lit 0) D2M8K2.t8909 from rfl, totK_node, tot8908, tot8909]
  decide +kernel

theorem arows8903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8903 = true := by
  rw [show D2M8K2.u8903 = KTree.node D2M8K2.t8910 (nat_lit 19537378) (nat_lit 3977045308) (nat_lit 0) D2M8K2.t8911 from rfl, allE_node, rows8910, irow8903, rows8911]
  all_goals rfl

theorem atot8903 : totK PD2M8K2 D2M8K2.u8903 = [304636939925, 857847214596, 609284997361, 67112172683, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8903 = KTree.node D2M8K2.t8910 (nat_lit 19537378) (nat_lit 3977045308) (nat_lit 0) D2M8K2.t8911 from rfl, totK_node, tot8910, tot8911]
  decide +kernel

theorem arows8907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8907 = true := by
  rw [show D2M8K2.u8907 = KTree.node D2M8K2.t8912 (nat_lit 19538889) (nat_lit 1886076144) (nat_lit 0) D2M8K2.t8913 from rfl, allE_node, rows8912, irow8907, rows8913]
  all_goals rfl

theorem atot8907 : totK PD2M8K2 D2M8K2.u8907 = [117781926523, 619996145087, 773777534265, 290470352342, 25137448963, 0, 0, 0] := by
  rw [show D2M8K2.u8907 = KTree.node D2M8K2.t8912 (nat_lit 19538889) (nat_lit 1886076144) (nat_lit 0) D2M8K2.t8913 from rfl, totK_node, tot8912, tot8913]
  decide +kernel

theorem arows8908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8908 = true := by
  rw [show D2M8K2.u8908 = KTree.node D2M8K2.t8914 (nat_lit 19540154) (nat_lit 3963623578) (nat_lit 0) D2M8K2.t8915 from rfl, allE_node, rows8914, irow8908, rows8915]
  all_goals rfl

theorem atot8908 : totK PD2M8K2 D2M8K2.u8908 = [176600050142, 608796783457, 730547246510, 288115547405, 12206425282, 0, 0, 0] := by
  rw [show D2M8K2.u8908 = KTree.node D2M8K2.t8914 (nat_lit 19540154) (nat_lit 3963623578) (nat_lit 0) D2M8K2.t8915 from rfl, totK_node, tot8914, tot8915]
  decide +kernel

theorem arows8910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8910 = true := by
  rw [show D2M8K2.u8910 = KTree.node D2M8K2.t8916 (nat_lit 19545080) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t8917 from rfl, allE_node, rows8916, irow8910, rows8917]
  all_goals rfl

theorem atot8910 : totK PD2M8K2 D2M8K2.u8910 = [270100032260, 815366656484, 637253794385, 101703259128, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u8910 = KTree.node D2M8K2.t8916 (nat_lit 19545080) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t8917 from rfl, totK_node, tot8916, tot8917]
  decide +kernel

theorem arows8911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8911 = true := by
  rw [show D2M8K2.u8911 = KTree.node D2M8K2.t8918 (nat_lit 19546714) (nat_lit 2477250038) (nat_lit 0) D2M8K2.t8919 from rfl, allE_node, rows8918, irow8911, rows8919]
  all_goals rfl

theorem atot8911 : totK PD2M8K2 D2M8K2.u8911 = [135185197221, 616873699931, 794719898764, 236010053637, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u8911 = KTree.node D2M8K2.t8918 (nat_lit 19546714) (nat_lit 2477250038) (nat_lit 0) D2M8K2.t8919 from rfl, totK_node, tot8918, tot8919]
  decide +kernel

theorem arows8914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8914 = true := by
  rw [show D2M8K2.u8914 = KTree.node D2M8K2.t8920 (nat_lit 19548114) (nat_lit 3474668509) (nat_lit 0) D2M8K2.t8921 from rfl, allE_node, rows8920, irow8914, rows8921]
  all_goals rfl

theorem atot8914 : totK PD2M8K2 D2M8K2.u8914 = [284340712788, 874522861495, 591896472439, 57751394980, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8914 = KTree.node D2M8K2.t8920 (nat_lit 19548114) (nat_lit 3474668509) (nat_lit 0) D2M8K2.t8921 from rfl, totK_node, tot8920, tot8921]
  decide +kernel

theorem arows8915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8915 = true := by
  rw [show D2M8K2.u8915 = KTree.node D2M8K2.t8922 (nat_lit 19550069) (nat_lit 2306720065) (nat_lit 0) D2M8K2.t8923 from rfl, allE_node, rows8922, irow8915, rows8923]
  all_goals rfl

theorem atot8915 : totK PD2M8K2 D2M8K2.u8915 = [165519874942, 664002443772, 780028076404, 187625463647, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u8915 = KTree.node D2M8K2.t8922 (nat_lit 19550069) (nat_lit 2306720065) (nat_lit 0) D2M8K2.t8923 from rfl, totK_node, tot8922, tot8923]
  decide +kernel

theorem arows8917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8917 = true := by
  rw [show D2M8K2.u8917 = KTree.node D2M8K2.t8924 (nat_lit 19551627) (nat_lit 3723494530) (nat_lit 0) D2M8K2.t8925 from rfl, allE_node, rows8924, irow8917, rows8925]
  all_goals rfl

theorem atot8917 : totK PD2M8K2 D2M8K2.u8917 = [258286810839, 839417447993, 643150748041, 87040163418, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u8917 = KTree.node D2M8K2.t8924 (nat_lit 19551627) (nat_lit 3723494530) (nat_lit 0) D2M8K2.t8925 from rfl, totK_node, tot8924, tot8925]
  decide +kernel

theorem arows8918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8918 = true := by
  rw [show D2M8K2.u8918 = KTree.node D2M8K2.t8926 (nat_lit 19553318) (nat_lit 3951364665) (nat_lit 0) D2M8K2.t8927 from rfl, allE_node, rows8926, irow8918, rows8927]
  all_goals rfl

theorem atot8918 : totK PD2M8K2 D2M8K2.u8918 = [0, 427108596482, 962117985690, 372884994523, 20590734181, 0, 0, 0] := by
  rw [show D2M8K2.u8918 = KTree.node D2M8K2.t8926 (nat_lit 19553318) (nat_lit 3951364665) (nat_lit 0) D2M8K2.t8927 from rfl, totK_node, tot8926, tot8927]
  decide +kernel

theorem arows8923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8923 = true := by
  rw [show D2M8K2.u8923 = KTree.node D2M8K2.t8928 (nat_lit 19555201) (nat_lit 1560988708) (nat_lit 0) D2M8K2.t8929 from rfl, allE_node, rows8928, irow8923, rows8929]
  all_goals rfl

theorem atot8923 : totK PD2M8K2 D2M8K2.u8923 = [0, 324593327069, 937933031198, 480252495268, 25136464737, 0, 0, 0] := by
  rw [show D2M8K2.u8923 = KTree.node D2M8K2.t8928 (nat_lit 19555201) (nat_lit 1560988708) (nat_lit 0) D2M8K2.t8929 from rfl, totK_node, tot8928, tot8929]
  decide +kernel

theorem arows8924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8924 = true := by
  rw [show D2M8K2.u8924 = KTree.node D2M8K2.t8930 (nat_lit 19557031) (nat_lit 2357814271) (nat_lit 0) D2M8K2.t8931 from rfl, allE_node, rows8930, irow8924, rows8931]
  all_goals rfl

theorem atot8924 : totK PD2M8K2 D2M8K2.u8924 = [0, 162011809405, 714825846911, 784418691791, 120106476328, 1239866073, 0, 0] := by
  rw [show D2M8K2.u8924 = KTree.node D2M8K2.t8930 (nat_lit 19557031) (nat_lit 2357814271) (nat_lit 0) D2M8K2.t8931 from rfl, totK_node, tot8930, tot8931]
  decide +kernel

theorem arows8926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8926 = true := by
  rw [show D2M8K2.u8926 = KTree.node D2M8K2.t8932 (nat_lit 19558858) (nat_lit 2551946361) (nat_lit 0) D2M8K2.t8933 from rfl, allE_node, rows8932, irow8926, rows8933]
  all_goals rfl

theorem atot8926 : totK PD2M8K2 D2M8K2.u8926 = [0, 349289802178, 950834553724, 479115083051, 28069532360, 0, 0, 0] := by
  rw [show D2M8K2.u8926 = KTree.node D2M8K2.t8932 (nat_lit 19558858) (nat_lit 2551946361) (nat_lit 0) D2M8K2.t8933 from rfl, totK_node, tot8932, tot8933]
  decide +kernel

theorem arows8927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8927 = true := by
  rw [show D2M8K2.u8927 = KTree.node D2M8K2.t8934 (nat_lit 19565526) (nat_lit 3867271593) (nat_lit 0) D2M8K2.t8935 from rfl, allE_node, rows8934, irow8927, rows8935]
  all_goals rfl

theorem atot8927 : totK PD2M8K2 D2M8K2.u8927 = [0, 358226245047, 931262282002, 507613140052, 35793193946, 0, 0, 0] := by
  rw [show D2M8K2.u8927 = KTree.node D2M8K2.t8934 (nat_lit 19565526) (nat_lit 3867271593) (nat_lit 0) D2M8K2.t8935 from rfl, totK_node, tot8934, tot8935]
  decide +kernel

theorem arows8930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8930 = true := by
  rw [show D2M8K2.u8930 = KTree.node D2M8K2.t8936 (nat_lit 19567180) (nat_lit 2156439812) (nat_lit 0) D2M8K2.t8937 from rfl, allE_node, rows8936, irow8930, rows8937]
  all_goals rfl

theorem atot8930 : totK PD2M8K2 D2M8K2.u8930 = [0, 55368390034, 513165122113, 880219135591, 278946142104, 13105450397, 0, 0] := by
  rw [show D2M8K2.u8930 = KTree.node D2M8K2.t8936 (nat_lit 19567180) (nat_lit 2156439812) (nat_lit 0) D2M8K2.t8937 from rfl, totK_node, tot8936, tot8937]
  decide +kernel

theorem arows8931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8931 = true := by
  rw [show D2M8K2.u8931 = KTree.node D2M8K2.t8938 (nat_lit 19568614) (nat_lit 1173607092) (nat_lit 0) D2M8K2.t8939 from rfl, allE_node, rows8938, irow8931, rows8939]
  all_goals rfl

theorem atot8931 : totK PD2M8K2 D2M8K2.u8931 = [0, 358841350788, 957320552124, 457618489403, 24247689074, 0, 0, 0] := by
  rw [show D2M8K2.u8931 = KTree.node D2M8K2.t8938 (nat_lit 19568614) (nat_lit 1173607092) (nat_lit 0) D2M8K2.t8939 from rfl, totK_node, tot8938, tot8939]
  decide +kernel

theorem arows8933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8933 = true := by
  rw [show D2M8K2.u8933 = KTree.node D2M8K2.t8940 (nat_lit 19570560) (nat_lit 3437577497) (nat_lit 0) D2M8K2.t8941 from rfl, allE_node, rows8940, irow8933, rows8941]
  all_goals rfl

theorem atot8933 : totK PD2M8K2 D2M8K2.u8933 = [0, 100253179405, 649872902606, 805037910491, 159974881921, 4720618446, 0, 0] := by
  rw [show D2M8K2.u8933 = KTree.node D2M8K2.t8940 (nat_lit 19570560) (nat_lit 3437577497) (nat_lit 0) D2M8K2.t8941 from rfl, totK_node, tot8940, tot8941]
  decide +kernel

theorem arows8934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8934 = true := by
  rw [show D2M8K2.u8934 = KTree.node D2M8K2.t8942 (nat_lit 19572266) (nat_lit 4059456874) (nat_lit 0) D2M8K2.t8943 from rfl, allE_node, rows8942, irow8934, rows8943]
  all_goals rfl

theorem atot8934 : totK PD2M8K2 D2M8K2.u8934 = [36508988125, 373385692089, 863538862074, 505878259786, 45274145777, 0, 0, 0] := by
  rw [show D2M8K2.u8934 = KTree.node D2M8K2.t8942 (nat_lit 19572266) (nat_lit 4059456874) (nat_lit 0) D2M8K2.t8943 from rfl, totK_node, tot8942, tot8943]
  decide +kernel

theorem arows8938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8938 = true := by
  rw [show D2M8K2.u8938 = KTree.node D2M8K2.t8944 (nat_lit 19575769) (nat_lit 1487208194) (nat_lit 0) D2M8K2.t8945 from rfl, allE_node, rows8944, irow8938, rows8945]
  all_goals rfl

theorem atot8938 : totK PD2M8K2 D2M8K2.u8938 = [366065987538, 937182947341, 446987672991, 23648084212, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8938 = KTree.node D2M8K2.t8944 (nat_lit 19575769) (nat_lit 1487208194) (nat_lit 0) D2M8K2.t8945 from rfl, totK_node, tot8944, tot8945]
  decide +kernel

theorem arows8939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8939 = true := by
  rw [show D2M8K2.u8939 = KTree.node D2M8K2.t8946 (nat_lit 19577484) (nat_lit 3130586911) (nat_lit 0) D2M8K2.t8947 from rfl, allE_node, rows8946, irow8939, rows8947]
  all_goals rfl

theorem atot8939 : totK PD2M8K2 D2M8K2.u8939 = [92925902623, 647802618197, 888087496134, 166235384984, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8939 = KTree.node D2M8K2.t8946 (nat_lit 19577484) (nat_lit 3130586911) (nat_lit 0) D2M8K2.t8947 from rfl, totK_node, tot8946, tot8947]
  decide +kernel

theorem arows8941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8941 = true := by
  rw [show D2M8K2.u8941 = KTree.node D2M8K2.t8948 (nat_lit 19579370) (nat_lit 3989013130) (nat_lit 0) D2M8K2.t8949 from rfl, allE_node, rows8948, irow8941, rows8949]
  all_goals rfl

theorem atot8941 : totK PD2M8K2 D2M8K2.u8941 = [324575920315, 902205563684, 546183947586, 52047595535, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8941 = KTree.node D2M8K2.t8948 (nat_lit 19579370) (nat_lit 3989013130) (nat_lit 0) D2M8K2.t8949 from rfl, totK_node, tot8948, tot8949]
  decide +kernel

theorem arows8942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8942 = true := by
  rw [show D2M8K2.u8942 = KTree.node D2M8K2.t8950 (nat_lit 19580914) (nat_lit 3862193498) (nat_lit 0) D2M8K2.t8951 from rfl, allE_node, rows8950, irow8942, rows8951]
  all_goals rfl

theorem atot8942 : totK PD2M8K2 D2M8K2.u8942 = [0, 378432613580, 943770167759, 455826798629, 30789563262, 0, 0, 0] := by
  rw [show D2M8K2.u8942 = KTree.node D2M8K2.t8950 (nat_lit 19580914) (nat_lit 3862193498) (nat_lit 0) D2M8K2.t8951 from rfl, totK_node, tot8950, tot8951]
  decide +kernel

theorem arows8945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8945 = true := by
  rw [show D2M8K2.u8945 = KTree.node D2M8K2.t8952 (nat_lit 19582225) (nat_lit 1125615256) (nat_lit 0) D2M8K2.t8953 from rfl, allE_node, rows8952, irow8945, rows8953]
  all_goals rfl

theorem atot8945 : totK PD2M8K2 D2M8K2.u8945 = [323533095032, 844550781814, 510437462677, 110362333240, 6627249222, 0, 0, 0] := by
  rw [show D2M8K2.u8945 = KTree.node D2M8K2.t8952 (nat_lit 19582225) (nat_lit 1125615256) (nat_lit 0) D2M8K2.t8953 from rfl, totK_node, tot8952, tot8953]
  decide +kernel

theorem arows8946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8946 = true := by
  rw [show D2M8K2.u8946 = KTree.node D2M8K2.t8954 (nat_lit 19584252) (nat_lit 2693120782) (nat_lit 0) D2M8K2.t8955 from rfl, allE_node, rows8954, irow8946, rows8955]
  all_goals rfl

theorem atot8946 : totK PD2M8K2 D2M8K2.u8946 = [122008031799, 572848846966, 793366542254, 251976654664, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u8946 = KTree.node D2M8K2.t8954 (nat_lit 19584252) (nat_lit 2693120782) (nat_lit 0) D2M8K2.t8955 from rfl, totK_node, tot8954, tot8955]
  decide +kernel

theorem arows8948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8948 = true := by
  rw [show D2M8K2.u8948 = KTree.node D2M8K2.t8956 (nat_lit 19586336) (nat_lit 3817447700) (nat_lit 0) D2M8K2.t8957 from rfl, allE_node, rows8956, irow8948, rows8957]
  all_goals rfl

theorem atot8948 : totK PD2M8K2 D2M8K2.u8948 = [304519371839, 887892165913, 580116966748, 53802910210, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8948 = KTree.node D2M8K2.t8956 (nat_lit 19586336) (nat_lit 3817447700) (nat_lit 0) D2M8K2.t8957 from rfl, totK_node, tot8956, tot8957]
  decide +kernel

theorem arows8949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8949 = true := by
  rw [show D2M8K2.u8949 = KTree.node D2M8K2.t8958 (nat_lit 19588037) (nat_lit 2115416224) (nat_lit 0) D2M8K2.t8959 from rfl, allE_node, rows8958, irow8949, rows8959]
  all_goals rfl

theorem atot8949 : totK PD2M8K2 D2M8K2.u8949 = [85741851239, 523103624810, 861414304262, 294521327317, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u8949 = KTree.node D2M8K2.t8958 (nat_lit 19588037) (nat_lit 2115416224) (nat_lit 0) D2M8K2.t8959 from rfl, totK_node, tot8958, tot8959]
  decide +kernel

theorem arows8957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8957 = true := by
  rw [show D2M8K2.u8957 = KTree.node D2M8K2.t8960 (nat_lit 19589390) (nat_lit 3063623536) (nat_lit 0) D2M8K2.t8961 from rfl, allE_node, rows8960, irow8957, rows8961]
  all_goals rfl

theorem atot8957 : totK PD2M8K2 D2M8K2.u8957 = [352152937815, 935415329072, 499562853641, 39920132328, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8957 = KTree.node D2M8K2.t8960 (nat_lit 19589390) (nat_lit 3063623536) (nat_lit 0) D2M8K2.t8961 from rfl, totK_node, tot8960, tot8961]
  decide +kernel

theorem arows8958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8958 = true := by
  rw [show D2M8K2.u8958 = KTree.node D2M8K2.t8962 (nat_lit 19591216) (nat_lit 2383437388) (nat_lit 0) D2M8K2.t8963 from rfl, allE_node, rows8962, irow8958, rows8963]
  all_goals rfl

theorem atot8958 : totK PD2M8K2 D2M8K2.u8958 = [0, 533669047939, 1014785122224, 248405563172, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u8958 = KTree.node D2M8K2.t8962 (nat_lit 19591216) (nat_lit 2383437388) (nat_lit 0) D2M8K2.t8963 from rfl, totK_node, tot8962, tot8963]
  decide +kernel

theorem arows8960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8960 = true := by
  rw [show D2M8K2.u8960 = KTree.node D2M8K2.t8964 (nat_lit 19596636) (nat_lit 2814470669) (nat_lit 0) D2M8K2.t8965 from rfl, allE_node, rows8964, irow8960, rows8965]
  all_goals rfl

theorem atot8960 : totK PD2M8K2 D2M8K2.u8960 = [0, 315167346587, 919418935769, 476586021974, 29322472901, 0, 0, 0] := by
  rw [show D2M8K2.u8960 = KTree.node D2M8K2.t8964 (nat_lit 19596636) (nat_lit 2814470669) (nat_lit 0) D2M8K2.t8965 from rfl, totK_node, tot8964, tot8965]
  decide +kernel

theorem arows8961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8961 = true := by
  rw [show D2M8K2.u8961 = KTree.node D2M8K2.t8966 (nat_lit 19598760) (nat_lit 3452223136) (nat_lit 0) D2M8K2.t8967 from rfl, allE_node, rows8966, irow8961, rows8967]
  all_goals rfl

theorem atot8961 : totK PD2M8K2 D2M8K2.u8961 = [0, 171160256165, 758835799461, 723424944298, 104969895651, 1138244013, 0, 0] := by
  rw [show D2M8K2.u8961 = KTree.node D2M8K2.t8966 (nat_lit 19598760) (nat_lit 3452223136) (nat_lit 0) D2M8K2.t8967 from rfl, totK_node, tot8966, tot8967]
  decide +kernel

theorem arows8964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8964 = true := by
  rw [show D2M8K2.u8964 = KTree.node D2M8K2.t8968 (nat_lit 19600458) (nat_lit 3810573890) (nat_lit 0) D2M8K2.t8969 from rfl, allE_node, rows8968, irow8964, rows8969]
  all_goals rfl

theorem atot8964 : totK PD2M8K2 D2M8K2.u8964 = [0, 404389973184, 957026852931, 417685268136, 20666119020, 0, 0, 0] := by
  rw [show D2M8K2.u8964 = KTree.node D2M8K2.t8968 (nat_lit 19600458) (nat_lit 3810573890) (nat_lit 0) D2M8K2.t8969 from rfl, totK_node, tot8968, tot8969]
  decide +kernel

theorem arows8965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8965 = true := by
  rw [show D2M8K2.u8965 = KTree.node D2M8K2.t8970 (nat_lit 19603776) (nat_lit 3390458902) (nat_lit 0) D2M8K2.t8971 from rfl, allE_node, rows8970, irow8965, rows8971]
  all_goals rfl

theorem atot8965 : totK PD2M8K2 D2M8K2.u8965 = [0, 335519886163, 929223452325, 500633605167, 33207858576, 0, 0, 0] := by
  rw [show D2M8K2.u8965 = KTree.node D2M8K2.t8970 (nat_lit 19603776) (nat_lit 3390458902) (nat_lit 0) D2M8K2.t8971 from rfl, totK_node, tot8970, tot8971]
  decide +kernel

theorem arows8967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8967 = true := by
  rw [show D2M8K2.u8967 = KTree.node D2M8K2.t8972 (nat_lit 19607335) (nat_lit 2357138084) (nat_lit 0) D2M8K2.t8973 from rfl, allE_node, rows8972, irow8967, rows8973]
  all_goals rfl

theorem atot8967 : totK PD2M8K2 D2M8K2.u8967 = [0, 403555390818, 968498769356, 417064613768, 17529653952, 0, 0, 0] := by
  rw [show D2M8K2.u8967 = KTree.node D2M8K2.t8972 (nat_lit 19607335) (nat_lit 2357138084) (nat_lit 0) D2M8K2.t8973 from rfl, totK_node, tot8972, tot8973]
  decide +kernel

theorem arows8968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8968 = true := by
  rw [show D2M8K2.u8968 = KTree.node D2M8K2.t8974 (nat_lit 19610324) (nat_lit 3673606522) (nat_lit 0) D2M8K2.t8975 from rfl, allE_node, rows8974, irow8968, rows8975]
  all_goals rfl

theorem atot8968 : totK PD2M8K2 D2M8K2.u8968 = [0, 280767387285, 879334227085, 561260940398, 49833812471, 0, 0, 0] := by
  rw [show D2M8K2.u8968 = KTree.node D2M8K2.t8974 (nat_lit 19610324) (nat_lit 3673606522) (nat_lit 0) D2M8K2.t8975 from rfl, totK_node, tot8974, tot8975]
  decide +kernel

theorem arows8972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8972 = true := by
  rw [show D2M8K2.u8972 = KTree.node D2M8K2.t8976 (nat_lit 19612288) (nat_lit 3558570782) (nat_lit 0) D2M8K2.t8977 from rfl, allE_node, rows8976, irow8972, rows8977]
  all_goals rfl

theorem atot8972 : totK PD2M8K2 D2M8K2.u8972 = [166303772541, 345228622885, 444522491739, 624413716078, 172139077818, 4977114383, 0, 0] := by
  rw [show D2M8K2.u8972 = KTree.node D2M8K2.t8976 (nat_lit 19612288) (nat_lit 3558570782) (nat_lit 0) D2M8K2.t8977 from rfl, totK_node, tot8976, tot8977]
  decide +kernel

theorem arows8973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8973 = true := by
  rw [show D2M8K2.u8973 = KTree.node D2M8K2.t8978 (nat_lit 19617648) (nat_lit 3397798539) (nat_lit 0) D2M8K2.t8979 from rfl, allE_node, rows8978, irow8973, rows8979]
  all_goals rfl

theorem atot8973 : totK PD2M8K2 D2M8K2.u8973 = [241349736286, 781208868100, 640659031085, 109202254412, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u8973 = KTree.node D2M8K2.t8978 (nat_lit 19617648) (nat_lit 3397798539) (nat_lit 0) D2M8K2.t8979 from rfl, totK_node, tot8978, tot8979]
  decide +kernel

theorem arows8975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8975 = true := by
  rw [show D2M8K2.u8975 = KTree.node D2M8K2.t8980 (nat_lit 19620041) (nat_lit 1804861965) (nat_lit 0) D2M8K2.t8981 from rfl, allE_node, rows8980, irow8975, rows8981]
  all_goals rfl

theorem atot8975 : totK PD2M8K2 D2M8K2.u8975 = [186375483619, 777013378685, 766550355030, 93287172905, 0, 0, 0, 0] := by
  rw [show D2M8K2.u8975 = KTree.node D2M8K2.t8980 (nat_lit 19620041) (nat_lit 1804861965) (nat_lit 0) D2M8K2.t8981 from rfl, totK_node, tot8980, tot8981]
  decide +kernel

theorem arows8976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8976 = true := by
  rw [show D2M8K2.u8976 = KTree.node D2M8K2.t8982 (nat_lit 19621243) (nat_lit 2220499248) (nat_lit 0) D2M8K2.t8983 from rfl, allE_node, rows8982, irow8976, rows8983]
  all_goals rfl

theorem atot8976 : totK PD2M8K2 D2M8K2.u8976 = [228503521531, 754993059077, 630031580342, 200453503707, 21379892652, 0, 0, 0] := by
  rw [show D2M8K2.u8976 = KTree.node D2M8K2.t8982 (nat_lit 19621243) (nat_lit 2220499248) (nat_lit 0) D2M8K2.t8983 from rfl, totK_node, tot8982, tot8983]
  decide +kernel

theorem arows8979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8979 = true := by
  rw [show D2M8K2.u8979 = KTree.node D2M8K2.t8984 (nat_lit 19622792) (nat_lit 3655407429) (nat_lit 0) D2M8K2.t8985 from rfl, allE_node, rows8984, irow8979, rows8985]
  all_goals rfl

theorem atot8979 : totK PD2M8K2 D2M8K2.u8979 = [88158716638, 487445636344, 840161746737, 365489917780, 16024055978, 0, 0, 0] := by
  rw [show D2M8K2.u8979 = KTree.node D2M8K2.t8984 (nat_lit 19622792) (nat_lit 3655407429) (nat_lit 0) D2M8K2.t8985 from rfl, totK_node, tot8984, tot8985]
  decide +kernel

theorem arows8980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8980 = true := by
  rw [show D2M8K2.u8980 = KTree.node D2M8K2.t8986 (nat_lit 19624652) (nat_lit 2972513790) (nat_lit 0) D2M8K2.t8987 from rfl, allE_node, rows8986, irow8980, rows8987]
  all_goals rfl

theorem atot8980 : totK PD2M8K2 D2M8K2.u8980 = [234714300677, 776985402420, 693078074939, 116209656011, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u8980 = KTree.node D2M8K2.t8986 (nat_lit 19624652) (nat_lit 2972513790) (nat_lit 0) D2M8K2.t8987 from rfl, totK_node, tot8986, tot8987]
  decide +kernel

theorem arows8982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8982 = true := by
  rw [show D2M8K2.u8982 = KTree.node D2M8K2.t8988 (nat_lit 19626778) (nat_lit 3819830307) (nat_lit 0) D2M8K2.t8989 from rfl, allE_node, rows8988, irow8982, rows8989]
  all_goals rfl

theorem atot8982 : totK PD2M8K2 D2M8K2.u8982 = [265649654124, 787232708376, 635887323246, 136588270445, 5912535468, 0, 0, 0] := by
  rw [show D2M8K2.u8982 = KTree.node D2M8K2.t8988 (nat_lit 19626778) (nat_lit 3819830307) (nat_lit 0) D2M8K2.t8989 from rfl, totK_node, tot8988, tot8989]
  decide +kernel

theorem arows8983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8983 = true := by
  rw [show D2M8K2.u8983 = KTree.node D2M8K2.t8990 (nat_lit 19628293) (nat_lit 1081320351) (nat_lit 0) D2M8K2.t8991 from rfl, allE_node, rows8990, irow8983, rows8991]
  all_goals rfl

theorem atot8983 : totK PD2M8K2 D2M8K2.u8983 = [161514634060, 744116472878, 776539995605, 132431827505, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u8983 = KTree.node D2M8K2.t8990 (nat_lit 19628293) (nat_lit 1081320351) (nat_lit 0) D2M8K2.t8991 from rfl, totK_node, tot8990, tot8991]
  decide +kernel

theorem arows8988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8988 = true := by
  rw [show D2M8K2.u8988 = KTree.node D2M8K2.t8992 (nat_lit 19633605) (nat_lit 1326917595) (nat_lit 0) D2M8K2.t8993 from rfl, allE_node, rows8992, irow8988, rows8993]
  all_goals rfl

theorem atot8988 : totK PD2M8K2 D2M8K2.u8988 = [223539817174, 681628675032, 687011912513, 211964126347, 12045711471, 0, 0, 0] := by
  rw [show D2M8K2.u8988 = KTree.node D2M8K2.t8992 (nat_lit 19633605) (nat_lit 1326917595) (nat_lit 0) D2M8K2.t8993 from rfl, totK_node, tot8992, tot8993]
  decide +kernel

theorem arows8989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8989 = true := by
  rw [show D2M8K2.u8989 = KTree.node D2M8K2.t8994 (nat_lit 19635056) (nat_lit 2944872627) (nat_lit 0) D2M8K2.t8995 from rfl, allE_node, rows8994, irow8989, rows8995]
  all_goals rfl

theorem atot8989 : totK PD2M8K2 D2M8K2.u8989 = [218320538648, 785192783932, 693875085218, 117263436494, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u8989 = KTree.node D2M8K2.t8994 (nat_lit 19635056) (nat_lit 2944872627) (nat_lit 0) D2M8K2.t8995 from rfl, totK_node, tot8994, tot8995]
  decide +kernel

theorem arows8991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8991 = true := by
  rw [show D2M8K2.u8991 = KTree.node D2M8K2.t8996 (nat_lit 19636742) (nat_lit 4125681607) (nat_lit 0) D2M8K2.t8997 from rfl, allE_node, rows8996, irow8991, rows8997]
  all_goals rfl

theorem atot8991 : totK PD2M8K2 D2M8K2.u8991 = [0, 397533258022, 961897901344, 403230573816, 22149860293, 0, 0, 0] := by
  rw [show D2M8K2.u8991 = KTree.node D2M8K2.t8996 (nat_lit 19636742) (nat_lit 4125681607) (nat_lit 0) D2M8K2.t8997 from rfl, totK_node, tot8996, tot8997]
  decide +kernel

theorem arows8992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8992 = true := by
  rw [show D2M8K2.u8992 = KTree.node D2M8K2.t8998 (nat_lit 19638296) (nat_lit 3537863206) (nat_lit 0) D2M8K2.t8999 from rfl, allE_node, rows8998, irow8992, rows8999]
  all_goals rfl

theorem atot8992 : totK PD2M8K2 D2M8K2.u8992 = [0, 274354218561, 842396422255, 564365259830, 72543697087, 1310285577, 0, 0] := by
  rw [show D2M8K2.u8992 = KTree.node D2M8K2.t8998 (nat_lit 19638296) (nat_lit 3537863206) (nat_lit 0) D2M8K2.t8999 from rfl, totK_node, tot8998, tot8999]
  decide +kernel

theorem arows8995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8995 = true := by
  rw [show D2M8K2.u8995 = KTree.node D2M8K2.t9000 (nat_lit 19640767) (nat_lit 2341283416) (nat_lit 0) D2M8K2.t9001 from rfl, allE_node, rows9000, irow8995, rows9001]
  all_goals rfl

theorem atot8995 : totK PD2M8K2 D2M8K2.u8995 = [0, 182068933197, 757660134031, 770274122426, 86591553962, 0, 0, 0] := by
  rw [show D2M8K2.u8995 = KTree.node D2M8K2.t9000 (nat_lit 19640767) (nat_lit 2341283416) (nat_lit 0) D2M8K2.t9001 from rfl, totK_node, tot9000, tot9001]
  decide +kernel

theorem arows8996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8996 = true := by
  rw [show D2M8K2.u8996 = KTree.node D2M8K2.t9002 (nat_lit 19641973) (nat_lit 1160401891) (nat_lit 0) D2M8K2.t9003 from rfl, allE_node, rows9002, irow8996, rows9003]
  all_goals rfl

theorem atot8996 : totK PD2M8K2 D2M8K2.u8996 = [0, 400012584464, 969261070855, 435401494918, 22924840025, 0, 0, 0] := by
  rw [show D2M8K2.u8996 = KTree.node D2M8K2.t9002 (nat_lit 19641973) (nat_lit 1160401891) (nat_lit 0) D2M8K2.t9003 from rfl, totK_node, tot9002, tot9003]
  decide +kernel

theorem arows8998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8998 = true := by
  rw [show D2M8K2.u8998 = KTree.node D2M8K2.t9004 (nat_lit 19645539) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t9005 from rfl, allE_node, rows9004, irow8998, rows9005]
  all_goals rfl

theorem atot8998 : totK PD2M8K2 D2M8K2.u8998 = [0, 161358637377, 720665265242, 768911180771, 133189125178, 2125526286, 0, 0] := by
  rw [show D2M8K2.u8998 = KTree.node D2M8K2.t9004 (nat_lit 19645539) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t9005 from rfl, totK_node, tot9004, tot9005]
  decide +kernel

theorem arows8999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8999 = true := by
  rw [show D2M8K2.u8999 = KTree.node D2M8K2.t9006 (nat_lit 19647762) (nat_lit 3403983718) (nat_lit 0) D2M8K2.t9007 from rfl, allE_node, rows9006, irow8999, rows9007]
  all_goals rfl

theorem atot8999 : totK PD2M8K2 D2M8K2.u8999 = [0, 321119775368, 847325775153, 552085477682, 86888548327, 2754314106, 0, 0] := by
  rw [show D2M8K2.u8999 = KTree.node D2M8K2.t9006 (nat_lit 19647762) (nat_lit 3403983718) (nat_lit 0) D2M8K2.t9007 from rfl, totK_node, tot9006, tot9007]
  decide +kernel

theorem arows9003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9003 = true := by
  rw [show D2M8K2.u9003 = KTree.node D2M8K2.t9008 (nat_lit 19649245) (nat_lit 1107157161) (nat_lit 0) D2M8K2.t9009 from rfl, allE_node, rows9008, irow9003, rows9009]
  all_goals rfl

theorem atot9003 : totK PD2M8K2 D2M8K2.u9003 = [0, 100042299809, 676481372749, 811535297847, 165744778091, 4931404646, 0, 0] := by
  rw [show D2M8K2.u9003 = KTree.node D2M8K2.t9008 (nat_lit 19649245) (nat_lit 1107157161) (nat_lit 0) D2M8K2.t9009 from rfl, totK_node, tot9008, tot9009]
  decide +kernel

theorem arows9004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9004 = true := by
  rw [show D2M8K2.u9004 = KTree.node D2M8K2.t9010 (nat_lit 19654768) (nat_lit 3689724850) (nat_lit 0) D2M8K2.t9011 from rfl, allE_node, rows9010, irow9004, rows9011]
  all_goals rfl

theorem atot9004 : totK PD2M8K2 D2M8K2.u9004 = [0, 346713376770, 911063687569, 515964901881, 47099001353, 0, 0, 0] := by
  rw [show D2M8K2.u9004 = KTree.node D2M8K2.t9010 (nat_lit 19654768) (nat_lit 3689724850) (nat_lit 0) D2M8K2.t9011 from rfl, totK_node, tot9010, tot9011]
  decide +kernel

theorem arows9006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9006 = true := by
  rw [show D2M8K2.u9006 = KTree.node D2M8K2.t9012 (nat_lit 19656245) (nat_lit 1117164056) (nat_lit 0) D2M8K2.t9013 from rfl, allE_node, rows9012, irow9006, rows9013]
  all_goals rfl

theorem atot9006 : totK PD2M8K2 D2M8K2.u9006 = [0, 93578448888, 611766151597, 850627630411, 208954489656, 4811815119, 0, 0] := by
  rw [show D2M8K2.u9006 = KTree.node D2M8K2.t9012 (nat_lit 19656245) (nat_lit 1117164056) (nat_lit 0) D2M8K2.t9013 from rfl, totK_node, tot9012, tot9013]
  decide +kernel

theorem arows9007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9007 = true := by
  rw [show D2M8K2.u9007 = KTree.node D2M8K2.t9014 (nat_lit 19657924) (nat_lit 3957779519) (nat_lit 0) D2M8K2.t9015 from rfl, allE_node, rows9014, irow9007, rows9015]
  all_goals rfl

theorem atot9007 : totK PD2M8K2 D2M8K2.u9007 = [0, 261491637303, 733718800070, 573277994191, 193671996484, 15908383818, 0, 0] := by
  rw [show D2M8K2.u9007 = KTree.node D2M8K2.t9014 (nat_lit 19657924) (nat_lit 3957779519) (nat_lit 0) D2M8K2.t9015 from rfl, totK_node, tot9014, tot9015]
  decide +kernel

theorem arows9010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9010 = true := by
  rw [show D2M8K2.u9010 = KTree.node D2M8K2.t9016 (nat_lit 19659446) (nat_lit 3071489214) (nat_lit 0) D2M8K2.t9017 from rfl, allE_node, rows9016, irow9010, rows9017]
  all_goals rfl

theorem atot9010 : totK PD2M8K2 D2M8K2.u9010 = [0, 173729721164, 737280796568, 755769179211, 127207682375, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9010 = KTree.node D2M8K2.t9016 (nat_lit 19659446) (nat_lit 3071489214) (nat_lit 0) D2M8K2.t9017 from rfl, totK_node, tot9016, tot9017]
  decide +kernel

theorem arows9011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9011 = true := by
  rw [show D2M8K2.u9011 = KTree.node D2M8K2.t9018 (nat_lit 19665281) (nat_lit 2224460729) (nat_lit 0) D2M8K2.t9019 from rfl, allE_node, rows9018, irow9011, rows9019]
  all_goals rfl

theorem atot9011 : totK PD2M8K2 D2M8K2.u9011 = [0, 321119577346, 880051646330, 532664038781, 44539983815, 0, 0, 0] := by
  rw [show D2M8K2.u9011 = KTree.node D2M8K2.t9018 (nat_lit 19665281) (nat_lit 2224460729) (nat_lit 0) D2M8K2.t9019 from rfl, totK_node, tot9018, tot9019]
  decide +kernel

theorem arows9013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9013 = true := by
  rw [show D2M8K2.u9013 = KTree.node D2M8K2.t9020 (nat_lit 19667599) (nat_lit 2355725702) (nat_lit 0) D2M8K2.t9021 from rfl, allE_node, rows9020, irow9013, rows9021]
  all_goals rfl

theorem atot9013 : totK PD2M8K2 D2M8K2.u9013 = [0, 160548355868, 746164935720, 764419540660, 113438463257, 1164319620, 0, 0] := by
  rw [show D2M8K2.u9013 = KTree.node D2M8K2.t9020 (nat_lit 19667599) (nat_lit 2355725702) (nat_lit 0) D2M8K2.t9021 from rfl, totK_node, tot9020, tot9021]
  decide +kernel

theorem arows9014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9014 = true := by
  rw [show D2M8K2.u9014 = KTree.node D2M8K2.t9022 (nat_lit 19669398) (nat_lit 3581696511) (nat_lit 0) D2M8K2.t9023 from rfl, allE_node, rows9022, irow9014, rows9023]
  all_goals rfl

theorem atot9014 : totK PD2M8K2 D2M8K2.u9014 = [0, 264884068991, 831432740506, 617451061008, 81293061164, 1198073392, 0, 0] := by
  rw [show D2M8K2.u9014 = KTree.node D2M8K2.t9022 (nat_lit 19669398) (nat_lit 3581696511) (nat_lit 0) D2M8K2.t9023 from rfl, totK_node, tot9022, tot9023]
  decide +kernel

theorem arows9020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9020 = true := by
  rw [show D2M8K2.u9020 = KTree.node D2M8K2.t9024 (nat_lit 19671061) (nat_lit 1243102186) (nat_lit 0) D2M8K2.t9025 from rfl, allE_node, rows9024, irow9020, rows9025]
  all_goals rfl

theorem atot9020 : totK PD2M8K2 D2M8K2.u9020 = [0, 105938297661, 578386785410, 828042882069, 256060307974, 11991925116, 0, 0] := by
  rw [show D2M8K2.u9020 = KTree.node D2M8K2.t9024 (nat_lit 19671061) (nat_lit 1243102186) (nat_lit 0) D2M8K2.t9025 from rfl, totK_node, tot9024, tot9025]
  decide +kernel

theorem arows9021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9021 = true := by
  rw [show D2M8K2.u9021 = KTree.node D2M8K2.t9026 (nat_lit 19672519) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t9027 from rfl, allE_node, rows9026, irow9021, rows9027]
  all_goals rfl

theorem atot9021 : totK PD2M8K2 D2M8K2.u9021 = [0, 301817753957, 870215069568, 546433125033, 45888633841, 0, 0, 0] := by
  rw [show D2M8K2.u9021 = KTree.node D2M8K2.t9026 (nat_lit 19672519) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t9027 from rfl, totK_node, tot9026, tot9027]
  decide +kernel

theorem arows9023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9023 = true := by
  rw [show D2M8K2.u9023 = KTree.node D2M8K2.t9028 (nat_lit 19674496) (nat_lit 3520389001) (nat_lit 0) D2M8K2.t9029 from rfl, allE_node, rows9028, irow9023, rows9029]
  all_goals rfl

theorem atot9023 : totK PD2M8K2 D2M8K2.u9023 = [0, 157129989792, 670087194941, 791831954861, 169680416503, 4917684815, 0, 0] := by
  rw [show D2M8K2.u9023 = KTree.node D2M8K2.t9028 (nat_lit 19674496) (nat_lit 3520389001) (nat_lit 0) D2M8K2.t9029 from rfl, totK_node, tot9028, tot9029]
  decide +kernel

theorem arows9024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9024 = true := by
  rw [show D2M8K2.u9024 = KTree.node D2M8K2.t9030 (nat_lit 19676109) (nat_lit 1454888220) (nat_lit 0) D2M8K2.t9031 from rfl, allE_node, rows9030, irow9024, rows9031]
  all_goals rfl

theorem atot9024 : totK PD2M8K2 D2M8K2.u9024 = [0, 256489885996, 794248170847, 640356326430, 96911245190, 1268739303, 0, 0] := by
  rw [show D2M8K2.u9024 = KTree.node D2M8K2.t9030 (nat_lit 19676109) (nat_lit 1454888220) (nat_lit 0) D2M8K2.t9031 from rfl, totK_node, tot9030, tot9031]
  decide +kernel

theorem arows9027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9027 = true := by
  rw [show D2M8K2.u9027 = KTree.node D2M8K2.t9032 (nat_lit 19678207) (nat_lit 2240165355) (nat_lit 0) D2M8K2.t9033 from rfl, allE_node, rows9032, irow9027, rows9033]
  all_goals rfl

theorem atot9027 : totK PD2M8K2 D2M8K2.u9027 = [0, 0, 460276009462, 977381409882, 331487514329, 13851876900, 0, 0] := by
  rw [show D2M8K2.u9027 = KTree.node D2M8K2.t9032 (nat_lit 19678207) (nat_lit 2240165355) (nat_lit 0) D2M8K2.t9033 from rfl, totK_node, tot9032, tot9033]
  decide +kernel

theorem arows9028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9028 = true := by
  rw [show D2M8K2.u9028 = KTree.node D2M8K2.t9034 (nat_lit 19679721) (nat_lit 1916366651) (nat_lit 0) D2M8K2.t9035 from rfl, allE_node, rows9034, irow9028, rows9035]
  all_goals rfl

theorem atot9028 : totK PD2M8K2 D2M8K2.u9028 = [0, 0, 292498984474, 868246081431, 500091712901, 60493088566, 1310517177, 0] := by
  rw [show D2M8K2.u9028 = KTree.node D2M8K2.t9034 (nat_lit 19679721) (nat_lit 1916366651) (nat_lit 0) D2M8K2.t9035 from rfl, totK_node, tot9034, tot9035]
  decide +kernel

theorem arows9030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9030 = true := by
  rw [show D2M8K2.u9030 = KTree.node D2M8K2.t9036 (nat_lit 19685388) (nat_lit 3603685625) (nat_lit 0) D2M8K2.t9037 from rfl, allE_node, rows9036, irow9030, rows9037]
  all_goals rfl

theorem atot9030 : totK PD2M8K2 D2M8K2.u9030 = [0, 0, 236059694753, 832482490716, 574058688001, 60036580814, 0, 0] := by
  rw [show D2M8K2.u9030 = KTree.node D2M8K2.t9036 (nat_lit 19685388) (nat_lit 3603685625) (nat_lit 0) D2M8K2.t9037 from rfl, totK_node, tot9036, tot9037]
  decide +kernel

theorem arows9031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9031 = true := by
  rw [show D2M8K2.u9031 = KTree.node D2M8K2.t9038 (nat_lit 19689236) (nat_lit 3548614230) (nat_lit 0) D2M8K2.t9039 from rfl, allE_node, rows9038, irow9031, rows9039]
  all_goals rfl

theorem atot9031 : totK PD2M8K2 D2M8K2.u9031 = [0, 0, 417793396366, 959584312758, 375803809918, 15099382554, 0, 0] := by
  rw [show D2M8K2.u9031 = KTree.node D2M8K2.t9038 (nat_lit 19689236) (nat_lit 3548614230) (nat_lit 0) D2M8K2.t9039 from rfl, totK_node, tot9038, tot9039]
  decide +kernel

theorem arows9035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9035 = true := by
  rw [show D2M8K2.u9035 = KTree.node D2M8K2.t9040 (nat_lit 19692506) (nat_lit 3103662483) (nat_lit 0) D2M8K2.t9041 from rfl, allE_node, rows9040, irow9035, rows9041]
  all_goals rfl

theorem atot9035 : totK PD2M8K2 D2M8K2.u9035 = [0, 0, 386688308238, 954897701754, 378468683465, 16205762792, 0, 0] := by
  rw [show D2M8K2.u9035 = KTree.node D2M8K2.t9040 (nat_lit 19692506) (nat_lit 3103662483) (nat_lit 0) D2M8K2.t9041 from rfl, totK_node, tot9040, tot9041]
  decide +kernel

theorem arows9036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9036 = true := by
  rw [show D2M8K2.u9036 = KTree.node D2M8K2.t9042 (nat_lit 19695877) (nat_lit 1376198177) (nat_lit 0) D2M8K2.t9043 from rfl, allE_node, rows9042, irow9036, rows9043]
  all_goals rfl

theorem atot9036 : totK PD2M8K2 D2M8K2.u9036 = [0, 0, 424400474247, 963013956694, 364701257179, 14785186718, 0, 0] := by
  rw [show D2M8K2.u9036 = KTree.node D2M8K2.t9042 (nat_lit 19695877) (nat_lit 1376198177) (nat_lit 0) D2M8K2.t9043 from rfl, totK_node, tot9042, tot9043]
  decide +kernel

theorem arows9038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9038 = true := by
  rw [show D2M8K2.u9038 = KTree.node D2M8K2.t9044 (nat_lit 19703162) (nat_lit 4116241310) (nat_lit 0) D2M8K2.t9045 from rfl, allE_node, rows9044, irow9038, rows9045]
  all_goals rfl

theorem atot9038 : totK PD2M8K2 D2M8K2.u9038 = [0, 267427015878, 743514401920, 635904731514, 188338114216, 11693999300, 0, 0] := by
  rw [show D2M8K2.u9038 = KTree.node D2M8K2.t9044 (nat_lit 19703162) (nat_lit 4116241310) (nat_lit 0) D2M8K2.t9045 from rfl, totK_node, tot9044, tot9045]
  decide +kernel

theorem arows9039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9039 = true := by
  rw [show D2M8K2.u9039 = KTree.node D2M8K2.t9046 (nat_lit 19704361) (nat_lit 1389510728) (nat_lit 0) D2M8K2.t9047 from rfl, allE_node, rows9046, irow9039, rows9047]
  all_goals rfl

theorem atot9039 : totK PD2M8K2 D2M8K2.u9039 = [0, 176425804272, 665882512180, 702631687556, 252365689144, 24216995793, 0, 0] := by
  rw [show D2M8K2.u9039 = KTree.node D2M8K2.t9046 (nat_lit 19704361) (nat_lit 1389510728) (nat_lit 0) D2M8K2.t9047 from rfl, totK_node, tot9046, tot9047]
  decide +kernel

theorem arows9042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9042 = true := by
  rw [show D2M8K2.u9042 = KTree.node D2M8K2.t9048 (nat_lit 19705856) (nat_lit 3241997085) (nat_lit 0) D2M8K2.t9049 from rfl, allE_node, rows9048, irow9042, rows9049]
  all_goals rfl

theorem atot9042 : totK PD2M8K2 D2M8K2.u9042 = [0, 109069041747, 517556619754, 852382092488, 340028987463, 13283011847, 0, 0] := by
  rw [show D2M8K2.u9042 = KTree.node D2M8K2.t9048 (nat_lit 19705856) (nat_lit 3241997085) (nat_lit 0) D2M8K2.t9049 from rfl, totK_node, tot9048, tot9049]
  decide +kernel

theorem arows9043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9043 = true := by
  rw [show D2M8K2.u9043 = KTree.node D2M8K2.t9050 (nat_lit 19707678) (nat_lit 3700650081) (nat_lit 0) D2M8K2.t9051 from rfl, allE_node, rows9050, irow9043, rows9051]
  all_goals rfl

theorem atot9043 : totK PD2M8K2 D2M8K2.u9043 = [0, 219131390316, 781690696335, 668416593852, 134059697418, 4143089693, 0, 0] := by
  rw [show D2M8K2.u9043 = KTree.node D2M8K2.t9050 (nat_lit 19707678) (nat_lit 3700650081) (nat_lit 0) D2M8K2.t9051 from rfl, totK_node, tot9050, tot9051]
  decide +kernel

theorem arows9045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9045 = true := by
  rw [show D2M8K2.u9045 = KTree.node D2M8K2.t9052 (nat_lit 19709909) (nat_lit 2185494005) (nat_lit 0) D2M8K2.t9053 from rfl, allE_node, rows9052, irow9045, rows9053]
  all_goals rfl

theorem atot9045 : totK PD2M8K2 D2M8K2.u9045 = [0, 269310749115, 791819244394, 647116706420, 109942970421, 1227322468, 0, 0] := by
  rw [show D2M8K2.u9045 = KTree.node D2M8K2.t9052 (nat_lit 19709909) (nat_lit 2185494005) (nat_lit 0) D2M8K2.t9053 from rfl, totK_node, tot9052, tot9053]
  decide +kernel

theorem arows9046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9046 = true := by
  rw [show D2M8K2.u9046 = KTree.node D2M8K2.t9054 (nat_lit 19711375) (nat_lit 2431606759) (nat_lit 0) D2M8K2.t9055 from rfl, allE_node, rows9054, irow9046, rows9055]
  all_goals rfl

theorem atot9046 : totK PD2M8K2 D2M8K2.u9046 = [0, 157534451182, 683466554843, 762862125941, 189435264562, 7210114369, 0, 0] := by
  rw [show D2M8K2.u9046 = KTree.node D2M8K2.t9054 (nat_lit 19711375) (nat_lit 2431606759) (nat_lit 0) D2M8K2.t9055 from rfl, totK_node, tot9054, tot9055]
  decide +kernel

theorem arows9051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9051 = true := by
  rw [show D2M8K2.u9051 = KTree.node D2M8K2.t9056 (nat_lit 19713186) (nat_lit 2806703644) (nat_lit 0) D2M8K2.t9057 from rfl, allE_node, rows9056, irow9051, rows9057]
  all_goals rfl

theorem atot9051 : totK PD2M8K2 D2M8K2.u9051 = [0, 233349618704, 745713646015, 659248212324, 149466755726, 5972970333, 0, 0] := by
  rw [show D2M8K2.u9051 = KTree.node D2M8K2.t9056 (nat_lit 19713186) (nat_lit 2806703644) (nat_lit 0) D2M8K2.t9057 from rfl, totK_node, tot9056, tot9057]
  decide +kernel

theorem arows9052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9052 = true := by
  rw [show D2M8K2.u9052 = KTree.node D2M8K2.t9058 (nat_lit 19714428) (nat_lit 2942876196) (nat_lit 0) D2M8K2.t9059 from rfl, allE_node, rows9058, irow9052, rows9059]
  all_goals rfl

theorem atot9052 : totK PD2M8K2 D2M8K2.u9052 = [0, 177550997700, 803405733500, 750083345446, 83490066867, 0, 0, 0] := by
  rw [show D2M8K2.u9052 = KTree.node D2M8K2.t9058 (nat_lit 19714428) (nat_lit 2942876196) (nat_lit 0) D2M8K2.t9059 from rfl, totK_node, tot9058, tot9059]
  decide +kernel

theorem arows9054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9054 = true := by
  rw [show D2M8K2.u9054 = KTree.node D2M8K2.t9060 (nat_lit 19716888) (nat_lit 3009515013) (nat_lit 0) D2M8K2.t9061 from rfl, allE_node, rows9060, irow9054, rows9061]
  all_goals rfl

theorem atot9054 : totK PD2M8K2 D2M8K2.u9054 = [0, 320250744783, 807384371376, 570349623034, 118422486450, 3880716147, 0, 0] := by
  rw [show D2M8K2.u9054 = KTree.node D2M8K2.t9060 (nat_lit 19716888) (nat_lit 3009515013) (nat_lit 0) D2M8K2.t9061 from rfl, totK_node, tot9060, tot9061]
  decide +kernel

theorem arows9055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9055 = true := by
  rw [show D2M8K2.u9055 = KTree.node D2M8K2.t9062 (nat_lit 19718360) (nat_lit 2475269435) (nat_lit 0) D2M8K2.t9063 from rfl, allE_node, rows9062, irow9055, rows9063]
  all_goals rfl

theorem atot9055 : totK PD2M8K2 D2M8K2.u9055 = [0, 92353366773, 652094064309, 855830111424, 194145899975, 2516391818, 0, 0] := by
  rw [show D2M8K2.u9055 = KTree.node D2M8K2.t9062 (nat_lit 19718360) (nat_lit 2475269435) (nat_lit 0) D2M8K2.t9063 from rfl, totK_node, tot9062, tot9063]
  decide +kernel

theorem arows9058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9058 = true := by
  rw [show D2M8K2.u9058 = KTree.node D2M8K2.t9064 (nat_lit 19782276) (nat_lit 3313522220) (nat_lit 0) D2M8K2.t9065 from rfl, allE_node, rows9064, irow9058, rows9065]
  all_goals rfl

theorem atot9058 : totK PD2M8K2 D2M8K2.u9058 = [0, 244727005290, 709307818543, 595649027596, 210576135761, 15310102822, 0, 0] := by
  rw [show D2M8K2.u9058 = KTree.node D2M8K2.t9064 (nat_lit 19782276) (nat_lit 3313522220) (nat_lit 0) D2M8K2.t9065 from rfl, totK_node, tot9064, tot9065]
  decide +kernel

theorem arows9059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9059 = true := by
  rw [show D2M8K2.u9059 = KTree.node D2M8K2.t9066 (nat_lit 19783870) (nat_lit 3907268955) (nat_lit 0) D2M8K2.t9067 from rfl, allE_node, rows9066, irow9059, rows9067]
  all_goals rfl

theorem atot9059 : totK PD2M8K2 D2M8K2.u9059 = [0, 170587549806, 737026377007, 753571324228, 113701816546, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9059 = KTree.node D2M8K2.t9066 (nat_lit 19783870) (nat_lit 3907268955) (nat_lit 0) D2M8K2.t9067 from rfl, totK_node, tot9066, tot9067]
  decide +kernel

theorem arows9061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9061 = true := by
  rw [show D2M8K2.u9061 = KTree.node D2M8K2.t9068 (nat_lit 19786216) (nat_lit 3753250460) (nat_lit 0) D2M8K2.t9069 from rfl, allE_node, rows9068, irow9061, rows9069]
  all_goals rfl

theorem atot9061 : totK PD2M8K2 D2M8K2.u9061 = [0, 315933650692, 863352945782, 601527540651, 61089378742, 0, 0, 0] := by
  rw [show D2M8K2.u9061 = KTree.node D2M8K2.t9068 (nat_lit 19786216) (nat_lit 3753250460) (nat_lit 0) D2M8K2.t9069 from rfl, totK_node, tot9068, tot9069]
  decide +kernel

theorem arows9062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9062 = true := by
  rw [show D2M8K2.u9062 = KTree.node D2M8K2.t9070 (nat_lit 19787730) (nat_lit 3382612007) (nat_lit 0) D2M8K2.t9071 from rfl, allE_node, rows9070, irow9062, rows9071]
  all_goals rfl

theorem atot9062 : totK PD2M8K2 D2M8K2.u9062 = [0, 106703719193, 611116186969, 794309254501, 275748898068, 19572653258, 0, 0] := by
  rw [show D2M8K2.u9062 = KTree.node D2M8K2.t9070 (nat_lit 19787730) (nat_lit 3382612007) (nat_lit 0) D2M8K2.t9071 from rfl, totK_node, tot9070, tot9071]
  decide +kernel

theorem arows9066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9066 = true := by
  rw [show D2M8K2.u9066 = KTree.node D2M8K2.t9072 (nat_lit 19789036) (nat_lit 3714171854) (nat_lit 0) D2M8K2.t9073 from rfl, allE_node, rows9072, irow9066, rows9073]
  all_goals rfl

theorem atot9066 : totK PD2M8K2 D2M8K2.u9066 = [0, 176308135696, 625633507285, 726200088347, 266808015428, 10578519716, 0, 0] := by
  rw [show D2M8K2.u9066 = KTree.node D2M8K2.t9072 (nat_lit 19789036) (nat_lit 3714171854) (nat_lit 0) D2M8K2.t9073 from rfl, totK_node, tot9072, tot9073]
  decide +kernel

theorem arows9067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9067 = true := by
  rw [show D2M8K2.u9067 = KTree.node D2M8K2.t9074 (nat_lit 19793962) (nat_lit 3991944259) (nat_lit 0) D2M8K2.t9075 from rfl, allE_node, rows9074, irow9067, rows9075]
  all_goals rfl

theorem atot9067 : totK PD2M8K2 D2M8K2.u9067 = [0, 269825121554, 810436051725, 629915577002, 104376633351, 1198073392, 0, 0] := by
  rw [show D2M8K2.u9067 = KTree.node D2M8K2.t9074 (nat_lit 19793962) (nat_lit 3991944259) (nat_lit 0) D2M8K2.t9075 from rfl, totK_node, tot9074, tot9075]
  decide +kernel

theorem arows9069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9069 = true := by
  rw [show D2M8K2.u9069 = KTree.node D2M8K2.t9076 (nat_lit 19795586) (nat_lit 2673105108) (nat_lit 0) D2M8K2.t9077 from rfl, allE_node, rows9076, irow9069, rows9077]
  all_goals rfl

theorem atot9069 : totK PD2M8K2 D2M8K2.u9069 = [0, 152310089089, 628192218634, 767527064492, 229089139458, 12052611869, 0, 0] := by
  rw [show D2M8K2.u9069 = KTree.node D2M8K2.t9076 (nat_lit 19795586) (nat_lit 2673105108) (nat_lit 0) D2M8K2.t9077 from rfl, totK_node, tot9076, tot9077]
  decide +kernel

theorem arows9070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9070 = true := by
  rw [show D2M8K2.u9070 = KTree.node D2M8K2.t9078 (nat_lit 19796987) (nat_lit 2255503661) (nat_lit 0) D2M8K2.t9079 from rfl, allE_node, rows9078, irow9070, rows9079]
  all_goals rfl

theorem atot9070 : totK PD2M8K2 D2M8K2.u9070 = [0, 265637726429, 840386103554, 603034727315, 75230246857, 1096505104, 0, 0] := by
  rw [show D2M8K2.u9070 = KTree.node D2M8K2.t9078 (nat_lit 19796987) (nat_lit 2255503661) (nat_lit 0) D2M8K2.t9079 from rfl, totK_node, tot9078, tot9079]
  decide +kernel

theorem arows9073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9073 = true := by
  rw [show D2M8K2.u9073 = KTree.node D2M8K2.t9080 (nat_lit 19798946) (nat_lit 4067590321) (nat_lit 0) D2M8K2.t9081 from rfl, allE_node, rows9080, irow9073, rows9081]
  all_goals rfl

theorem atot9073 : totK PD2M8K2 D2M8K2.u9073 = [0, 173066691409, 706100347874, 773440716868, 153873882655, 3884009855, 0, 0] := by
  rw [show D2M8K2.u9073 = KTree.node D2M8K2.t9080 (nat_lit 19798946) (nat_lit 4067590321) (nat_lit 0) D2M8K2.t9081 from rfl, totK_node, tot9080, tot9081]
  decide +kernel

theorem arows9074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9074 = true := by
  rw [show D2M8K2.u9074 = KTree.node D2M8K2.t9082 (nat_lit 19800535) (nat_lit 2371469307) (nat_lit 0) D2M8K2.t9083 from rfl, allE_node, rows9082, irow9074, rows9083]
  all_goals rfl

theorem atot9074 : totK PD2M8K2 D2M8K2.u9074 = [0, 249952260028, 794483185128, 657540097073, 96052958047, 1268739303, 0, 0] := by
  rw [show D2M8K2.u9074 = KTree.node D2M8K2.t9082 (nat_lit 19800535) (nat_lit 2371469307) (nat_lit 0) D2M8K2.t9083 from rfl, totK_node, tot9082, tot9083]
  decide +kernel

theorem arows9076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9076 = true := by
  rw [show D2M8K2.u9076 = KTree.node D2M8K2.t9084 (nat_lit 19802245) (nat_lit 1047935701) (nat_lit 0) D2M8K2.t9085 from rfl, allE_node, rows9084, irow9076, rows9085]
  all_goals rfl

theorem atot9076 : totK PD2M8K2 D2M8K2.u9076 = [0, 0, 425986382390, 964838993132, 362294112879, 17257559335, 0, 0] := by
  rw [show D2M8K2.u9076 = KTree.node D2M8K2.t9084 (nat_lit 19802245) (nat_lit 1047935701) (nat_lit 0) D2M8K2.t9085 from rfl, totK_node, tot9084, tot9085]
  decide +kernel

theorem arows9077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9077 = true := by
  rw [show D2M8K2.u9077 = KTree.node D2M8K2.t9086 (nat_lit 19804104) (nat_lit 3542775029) (nat_lit 0) D2M8K2.t9087 from rfl, allE_node, rows9086, irow9077, rows9087]
  all_goals rfl

theorem atot9077 : totK PD2M8K2 D2M8K2.u9077 = [0, 0, 320328920604, 911323107499, 464697763863, 32159592774, 0, 0] := by
  rw [show D2M8K2.u9077 = KTree.node D2M8K2.t9086 (nat_lit 19804104) (nat_lit 3542775029) (nat_lit 0) D2M8K2.t9087 from rfl, totK_node, tot9086, tot9087]
  decide +kernel

theorem arows9084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9084 = true := by
  rw [show D2M8K2.u9084 = KTree.node D2M8K2.t9088 (nat_lit 19806171) (nat_lit 3101754295) (nat_lit 0) D2M8K2.t9089 from rfl, allE_node, rows9088, irow9084, rows9089]
  all_goals rfl

theorem atot9084 : totK PD2M8K2 D2M8K2.u9084 = [0, 0, 244877256704, 757455702359, 661728729995, 101591032498, 1217496766, 0] := by
  rw [show D2M8K2.u9084 = KTree.node D2M8K2.t9088 (nat_lit 19806171) (nat_lit 3101754295) (nat_lit 0) D2M8K2.t9089 from rfl, totK_node, tot9088, tot9089]
  decide +kernel

theorem arows9085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9085 = true := by
  rw [show D2M8K2.u9085 = KTree.node D2M8K2.t9090 (nat_lit 19807995) (nat_lit 3437771324) (nat_lit 0) D2M8K2.t9091 from rfl, allE_node, rows9090, irow9085, rows9091]
  all_goals rfl

theorem atot9085 : totK PD2M8K2 D2M8K2.u9085 = [0, 0, 344461754679, 966774321685, 453105994353, 28994636082, 0, 0] := by
  rw [show D2M8K2.u9085 = KTree.node D2M8K2.t9090 (nat_lit 19807995) (nat_lit 3437771324) (nat_lit 0) D2M8K2.t9091 from rfl, totK_node, tot9090, tot9091]
  decide +kernel

theorem arows9087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9087 = true := by
  rw [show D2M8K2.u9087 = KTree.node D2M8K2.t9092 (nat_lit 19814694) (nat_lit 3802709462) (nat_lit 0) D2M8K2.t9093 from rfl, allE_node, rows9092, irow9087, rows9093]
  all_goals rfl

theorem atot9087 : totK PD2M8K2 D2M8K2.u9087 = [0, 0, 266506895720, 814605021664, 606406470992, 94087949886, 1171084559, 0] := by
  rw [show D2M8K2.u9087 = KTree.node D2M8K2.t9092 (nat_lit 19814694) (nat_lit 3802709462) (nat_lit 0) D2M8K2.t9093 from rfl, totK_node, tot9092, tot9093]
  decide +kernel

theorem arows9088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9088 = true := by
  rw [show D2M8K2.u9088 = KTree.node D2M8K2.t9094 (nat_lit 19816373) (nat_lit 1336340198) (nat_lit 0) D2M8K2.t9095 from rfl, allE_node, rows9094, irow9088, rows9095]
  all_goals rfl

theorem atot9088 : totK PD2M8K2 D2M8K2.u9088 = [0, 0, 168708100794, 653742905930, 696661731275, 206030341513, 11934365838, 0] := by
  rw [show D2M8K2.u9088 = KTree.node D2M8K2.t9094 (nat_lit 19816373) (nat_lit 1336340198) (nat_lit 0) D2M8K2.t9095 from rfl, totK_node, tot9094, tot9095]
  decide +kernel

theorem arows9091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9091 = true := by
  rw [show D2M8K2.u9091 = KTree.node D2M8K2.t9096 (nat_lit 19817857) (nat_lit 1555847182) (nat_lit 0) D2M8K2.t9097 from rfl, allE_node, rows9096, irow9091, rows9097]
  all_goals rfl

theorem atot9091 : totK PD2M8K2 D2M8K2.u9091 = [0, 0, 243467969615, 809183241790, 584117078455, 76914386475, 1032241984, 0] := by
  rw [show D2M8K2.u9091 = KTree.node D2M8K2.t9096 (nat_lit 19817857) (nat_lit 1555847182) (nat_lit 0) D2M8K2.t9097 from rfl, totK_node, tot9096, tot9097]
  decide +kernel

theorem arows9092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9092 = true := by
  rw [show D2M8K2.u9092 = KTree.node D2M8K2.t9098 (nat_lit 19820221) (nat_lit 1182422426) (nat_lit 0) D2M8K2.t9099 from rfl, allE_node, rows9098, irow9092, rows9099]
  all_goals rfl

theorem atot9092 : totK PD2M8K2 D2M8K2.u9092 = [0, 0, 236663040960, 767253964010, 609093725800, 105658063272, 3598673838, 0] := by
  rw [show D2M8K2.u9092 = KTree.node D2M8K2.t9098 (nat_lit 19820221) (nat_lit 1182422426) (nat_lit 0) D2M8K2.t9099 from rfl, totK_node, tot9098, tot9099]
  decide +kernel

theorem arows9094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9094 = true := by
  rw [show D2M8K2.u9094 = KTree.node D2M8K2.t9100 (nat_lit 19823634) (nat_lit 3411630878) (nat_lit 0) D2M8K2.t9101 from rfl, allE_node, rows9100, irow9094, rows9101]
  all_goals rfl

theorem atot9094 : totK PD2M8K2 D2M8K2.u9094 = [0, 216700815643, 668174695625, 658900611904, 235361353235, 15086715677, 0, 0] := by
  rw [show D2M8K2.u9094 = KTree.node D2M8K2.t9100 (nat_lit 19823634) (nat_lit 3411630878) (nat_lit 0) D2M8K2.t9101 from rfl, totK_node, tot9100, tot9101]
  decide +kernel

theorem arows9095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9095 = true := by
  rw [show D2M8K2.u9095 = KTree.node D2M8K2.t9102 (nat_lit 19825204) (nat_lit 3454360906) (nat_lit 0) D2M8K2.t9103 from rfl, allE_node, rows9102, irow9095, rows9103]
  all_goals rfl

theorem atot9095 : totK PD2M8K2 D2M8K2.u9095 = [0, 188754091840, 757267563071, 710181508543, 109116117270, 1310517177, 0, 0] := by
  rw [show D2M8K2.u9095 = KTree.node D2M8K2.t9102 (nat_lit 19825204) (nat_lit 3454360906) (nat_lit 0) D2M8K2.t9103 from rfl, totK_node, tot9102, tot9103]
  decide +kernel

theorem arows9099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9099 = true := by
  rw [show D2M8K2.u9099 = KTree.node D2M8K2.t9104 (nat_lit 19827600) (nat_lit 2599347543) (nat_lit 0) D2M8K2.t9105 from rfl, allE_node, rows9104, irow9099, rows9105]
  all_goals rfl

theorem atot9099 : totK PD2M8K2 D2M8K2.u9099 = [0, 258966664351, 832654773184, 655731515022, 71202265504, 0, 0, 0] := by
  rw [show D2M8K2.u9099 = KTree.node D2M8K2.t9104 (nat_lit 19827600) (nat_lit 2599347543) (nat_lit 0) D2M8K2.t9105 from rfl, totK_node, tot9104, tot9105]
  decide +kernel

theorem arows9100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9100 = true := by
  rw [show D2M8K2.u9100 = KTree.node D2M8K2.t9106 (nat_lit 19829160) (nat_lit 2699732406) (nat_lit 0) D2M8K2.t9107 from rfl, allE_node, rows9106, irow9100, rows9107]
  all_goals rfl

theorem atot9100 : totK PD2M8K2 D2M8K2.u9100 = [0, 158470454872, 676937238563, 759745123534, 226423296639, 12531227089, 0, 0] := by
  rw [show D2M8K2.u9100 = KTree.node D2M8K2.t9106 (nat_lit 19829160) (nat_lit 2699732406) (nat_lit 0) D2M8K2.t9107 from rfl, totK_node, tot9106, tot9107]
  decide +kernel

theorem arows9102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9102 = true := by
  rw [show D2M8K2.u9102 = KTree.node D2M8K2.t9108 (nat_lit 19830680) (nat_lit 3491782222) (nat_lit 0) D2M8K2.t9109 from rfl, allE_node, rows9108, irow9102, rows9109]
  all_goals rfl

theorem atot9102 : totK PD2M8K2 D2M8K2.u9102 = [0, 235366303549, 759377142663, 654561589081, 153851682924, 2535105584, 0, 0] := by
  rw [show D2M8K2.u9102 = KTree.node D2M8K2.t9108 (nat_lit 19830680) (nat_lit 3491782222) (nat_lit 0) D2M8K2.t9109 from rfl, totK_node, tot9108, tot9109]
  decide +kernel

theorem arows9103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9103 = true := by
  rw [show D2M8K2.u9103 = KTree.node D2M8K2.t9110 (nat_lit 19832627) (nat_lit 2072425779) (nat_lit 0) D2M8K2.t9111 from rfl, allE_node, rows9110, irow9103, rows9111]
  all_goals rfl

theorem atot9103 : totK PD2M8K2 D2M8K2.u9103 = [0, 171876130308, 651606924794, 766165267756, 163099868795, 4532804645, 0, 0] := by
  rw [show D2M8K2.u9103 = KTree.node D2M8K2.t9110 (nat_lit 19832627) (nat_lit 2072425779) (nat_lit 0) D2M8K2.t9111 from rfl, totK_node, tot9110, tot9111]
  decide +kernel

theorem arows9106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9106 = true := by
  rw [show D2M8K2.u9106 = KTree.node D2M8K2.t9112 (nat_lit 19834985) (nat_lit 856286547) (nat_lit 0) D2M8K2.t9113 from rfl, allE_node, rows9112, irow9106, rows9113]
  all_goals rfl

theorem atot9106 : totK PD2M8K2 D2M8K2.u9106 = [0, 341450236727, 938351872868, 507249705551, 36497638829, 0, 0, 0] := by
  rw [show D2M8K2.u9106 = KTree.node D2M8K2.t9112 (nat_lit 19834985) (nat_lit 856286547) (nat_lit 0) D2M8K2.t9113 from rfl, totK_node, tot9112, tot9113]
  decide +kernel

theorem arows9107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9107 = true := by
  rw [show D2M8K2.u9107 = KTree.node D2M8K2.t9114 (nat_lit 19836685) (nat_lit 1075981492) (nat_lit 0) D2M8K2.t9115 from rfl, allE_node, rows9114, irow9107, rows9115]
  all_goals rfl

theorem atot9107 : totK PD2M8K2 D2M8K2.u9107 = [0, 18530029189, 476209828138, 956161499959, 307070727891, 13250685261, 0, 0] := by
  rw [show D2M8K2.u9107 = KTree.node D2M8K2.t9114 (nat_lit 19836685) (nat_lit 1075981492) (nat_lit 0) D2M8K2.t9115 from rfl, totK_node, tot9114, tot9115]
  decide +kernel

theorem arows9109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9109 = true := by
  rw [show D2M8K2.u9109 = KTree.node D2M8K2.t9116 (nat_lit 19838049) (nat_lit 1826690268) (nat_lit 0) D2M8K2.t9117 from rfl, allE_node, rows9116, irow9109, rows9117]
  all_goals rfl

theorem atot9109 : totK PD2M8K2 D2M8K2.u9109 = [0, 370514266617, 922336981406, 483388469354, 39717359411, 0, 0, 0] := by
  rw [show D2M8K2.u9109 = KTree.node D2M8K2.t9116 (nat_lit 19838049) (nat_lit 1826690268) (nat_lit 0) D2M8K2.t9117 from rfl, totK_node, tot9116, tot9117]
  decide +kernel

theorem arows9110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9110 = true := by
  rw [show D2M8K2.u9110 = KTree.node D2M8K2.t9118 (nat_lit 19839594) (nat_lit 3601533434) (nat_lit 0) D2M8K2.t9119 from rfl, allE_node, rows9118, irow9110, rows9119]
  all_goals rfl

theorem atot9110 : totK PD2M8K2 D2M8K2.u9110 = [0, 44373624882, 618749406486, 925880329472, 203509107916, 4980514959, 0, 0] := by
  rw [show D2M8K2.u9110 = KTree.node D2M8K2.t9118 (nat_lit 19839594) (nat_lit 3601533434) (nat_lit 0) D2M8K2.t9119 from rfl, totK_node, tot9118, tot9119]
  decide +kernel

theorem arows9115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9115 = true := by
  rw [show D2M8K2.u9115 = KTree.node D2M8K2.t9120 (nat_lit 19845330) (nat_lit 3461452213) (nat_lit 0) D2M8K2.t9121 from rfl, allE_node, rows9120, irow9115, rows9121]
  all_goals rfl

theorem atot9115 : totK PD2M8K2 D2M8K2.u9115 = [0, 0, 382382973826, 959017977054, 365303573334, 15946751661, 0, 0] := by
  rw [show D2M8K2.u9115 = KTree.node D2M8K2.t9120 (nat_lit 19845330) (nat_lit 3461452213) (nat_lit 0) D2M8K2.t9121 from rfl, totK_node, tot9120, tot9121]
  decide +kernel

theorem arows9116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9116 = true := by
  rw [show D2M8K2.u9116 = KTree.node D2M8K2.t9122 (nat_lit 19847300) (nat_lit 3151752891) (nat_lit 0) D2M8K2.t9123 from rfl, allE_node, rows9122, irow9116, rows9123]
  all_goals rfl

theorem atot9116 : totK PD2M8K2 D2M8K2.u9116 = [0, 0, 190613287615, 772370468161, 675317165673, 81275883080, 1138244013, 0] := by
  rw [show D2M8K2.u9116 = KTree.node D2M8K2.t9122 (nat_lit 19847300) (nat_lit 3151752891) (nat_lit 0) D2M8K2.t9123 from rfl, totK_node, tot9122, tot9123]
  decide +kernel

theorem arows9118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9118 = true := by
  rw [show D2M8K2.u9118 = KTree.node D2M8K2.t9124 (nat_lit 19849379) (nat_lit 2979220873) (nat_lit 0) D2M8K2.t9125 from rfl, allE_node, rows9124, irow9118, rows9125]
  all_goals rfl

theorem atot9118 : totK PD2M8K2 D2M8K2.u9118 = [0, 0, 453847284767, 973384842707, 337630066693, 9026212817, 0, 0] := by
  rw [show D2M8K2.u9118 = KTree.node D2M8K2.t9124 (nat_lit 19849379) (nat_lit 2979220873) (nat_lit 0) D2M8K2.t9125 from rfl, totK_node, tot9124, tot9125]
  decide +kernel

theorem arows9119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9119 = true := by
  rw [show D2M8K2.u9119 = KTree.node D2M8K2.t9126 (nat_lit 19855086) (nat_lit 4050905317) (nat_lit 0) D2M8K2.t9127 from rfl, allE_node, rows9126, irow9119, rows9127]
  all_goals rfl

theorem atot9119 : totK PD2M8K2 D2M8K2.u9119 = [0, 0, 395831225562, 935325897891, 408374741143, 24767382070, 0, 0] := by
  rw [show D2M8K2.u9119 = KTree.node D2M8K2.t9126 (nat_lit 19855086) (nat_lit 4050905317) (nat_lit 0) D2M8K2.t9127 from rfl, totK_node, tot9126, tot9127]
  decide +kernel

theorem arows9122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9122 = true := by
  rw [show D2M8K2.u9122 = KTree.node D2M8K2.t9128 (nat_lit 19858338) (nat_lit 2676524730) (nat_lit 0) D2M8K2.t9129 from rfl, allE_node, rows9128, irow9122, rows9129]
  all_goals rfl

theorem atot9122 : totK PD2M8K2 D2M8K2.u9122 = [0, 0, 356998300810, 943852136942, 422727655762, 20534589923, 0, 0] := by
  rw [show D2M8K2.u9122 = KTree.node D2M8K2.t9128 (nat_lit 19858338) (nat_lit 2676524730) (nat_lit 0) D2M8K2.t9129 from rfl, totK_node, tot9128, tot9129]
  decide +kernel

theorem arows9123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9123 = true := by
  rw [show D2M8K2.u9123 = KTree.node D2M8K2.t9130 (nat_lit 19859913) (nat_lit 1836876593) (nat_lit 0) D2M8K2.t9131 from rfl, allE_node, rows9130, irow9123, rows9131]
  all_goals rfl

theorem atot9123 : totK PD2M8K2 D2M8K2.u9123 = [0, 0, 178895967708, 773296033191, 665134671302, 91496157965, 1095107716, 0] := by
  rw [show D2M8K2.u9123 = KTree.node D2M8K2.t9130 (nat_lit 19859913) (nat_lit 1836876593) (nat_lit 0) D2M8K2.t9131 from rfl, totK_node, tot9130, tot9131]
  decide +kernel

theorem arows9125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9125 = true := by
  rw [show D2M8K2.u9125 = KTree.node D2M8K2.t9132 (nat_lit 19865714) (nat_lit 3052886939) (nat_lit 0) D2M8K2.t9133 from rfl, allE_node, rows9132, irow9125, rows9133]
  all_goals rfl

theorem atot9125 : totK PD2M8K2 D2M8K2.u9125 = [0, 317967928139, 734187115769, 396211785666, 227596527082, 76590533551, 3819176523, 0] := by
  rw [show D2M8K2.u9125 = KTree.node D2M8K2.t9132 (nat_lit 19865714) (nat_lit 3052886939) (nat_lit 0) D2M8K2.t9133 from rfl, totK_node, tot9132, tot9133]
  decide +kernel

theorem arows9126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9126 = true := by
  rw [show D2M8K2.u9126 = KTree.node D2M8K2.t9134 (nat_lit 19866982) (nat_lit 2788831180) (nat_lit 0) D2M8K2.t9135 from rfl, allE_node, rows9134, irow9126, rows9135]
  all_goals rfl

theorem atot9126 : totK PD2M8K2 D2M8K2.u9126 = [0, 88990076640, 682849535367, 870126905341, 138009738195, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9126 = KTree.node D2M8K2.t9134 (nat_lit 19866982) (nat_lit 2788831180) (nat_lit 0) D2M8K2.t9135 from rfl, totK_node, tot9134, tot9135]
  decide +kernel

theorem arows9130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9130 = true := by
  rw [show D2M8K2.u9130 = KTree.node D2M8K2.t9136 (nat_lit 19869365) (nat_lit 1823572020) (nat_lit 0) D2M8K2.t9137 from rfl, allE_node, rows9136, irow9130, rows9137]
  all_goals rfl

theorem atot9130 : totK PD2M8K2 D2M8K2.u9130 = [0, 366097906756, 921029943344, 510703414402, 45695899909, 0, 0, 0] := by
  rw [show D2M8K2.u9130 = KTree.node D2M8K2.t9136 (nat_lit 19869365) (nat_lit 1823572020) (nat_lit 0) D2M8K2.t9137 from rfl, totK_node, tot9136, tot9137]
  decide +kernel

theorem arows9131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9131 = true := by
  rw [show D2M8K2.u9131 = KTree.node D2M8K2.t9138 (nat_lit 19870876) (nat_lit 3962582701) (nat_lit 0) D2M8K2.t9139 from rfl, allE_node, rows9138, irow9131, rows9139]
  all_goals rfl

theorem atot9131 : totK PD2M8K2 D2M8K2.u9131 = [0, 52618497867, 500273459408, 868851630413, 363791687308, 24726425107, 0, 0] := by
  rw [show D2M8K2.u9131 = KTree.node D2M8K2.t9138 (nat_lit 19870876) (nat_lit 3962582701) (nat_lit 0) D2M8K2.t9139 from rfl, totK_node, tot9138, tot9139]
  decide +kernel

theorem arows9133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9133 = true := by
  rw [show D2M8K2.u9133 = KTree.node D2M8K2.t9140 (nat_lit 19872244) (nat_lit 2721883230) (nat_lit 0) D2M8K2.t9141 from rfl, allE_node, rows9140, irow9133, rows9141]
  all_goals rfl

theorem atot9133 : totK PD2M8K2 D2M8K2.u9133 = [0, 254377863443, 718797554663, 636263200754, 189360273163, 8078182869, 0, 0] := by
  rw [show D2M8K2.u9133 = KTree.node D2M8K2.t9140 (nat_lit 19872244) (nat_lit 2721883230) (nat_lit 0) D2M8K2.t9141 from rfl, totK_node, tot9140, tot9141]
  decide +kernel

theorem arows9134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9134 = true := by
  rw [show D2M8K2.u9134 = KTree.node D2M8K2.t9142 (nat_lit 19874106) (nat_lit 3727115493) (nat_lit 0) D2M8K2.t9143 from rfl, allE_node, rows9142, irow9134, rows9143]
  all_goals rfl

theorem atot9134 : totK PD2M8K2 D2M8K2.u9134 = [0, 156129484947, 647918038941, 797617829250, 189724060854, 5172807878, 0, 0] := by
  rw [show D2M8K2.u9134 = KTree.node D2M8K2.t9142 (nat_lit 19874106) (nat_lit 3727115493) (nat_lit 0) D2M8K2.t9143 from rfl, totK_node, tot9142, tot9143]
  decide +kernel

theorem arows9137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9137 = true := by
  rw [show D2M8K2.u9137 = KTree.node D2M8K2.t9144 (nat_lit 19876459) (nat_lit 1622503264) (nat_lit 0) D2M8K2.t9145 from rfl, allE_node, rows9144, irow9137, rows9145]
  all_goals rfl

theorem atot9137 : totK PD2M8K2 D2M8K2.u9137 = [0, 341567249297, 938182739331, 511770063689, 37438693365, 0, 0, 0] := by
  rw [show D2M8K2.u9137 = KTree.node D2M8K2.t9144 (nat_lit 19876459) (nat_lit 1622503264) (nat_lit 0) D2M8K2.t9145 from rfl, totK_node, tot9144, tot9145]
  decide +kernel

theorem arows9138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9138 = true := by
  rw [show D2M8K2.u9138 = KTree.node D2M8K2.t9146 (nat_lit 19878151) (nat_lit 2394825812) (nat_lit 0) D2M8K2.t9147 from rfl, allE_node, rows9146, irow9138, rows9147]
  all_goals rfl

theorem atot9138 : totK PD2M8K2 D2M8K2.u9138 = [0, 18567060971, 488364022712, 953589718023, 306495233973, 13183098110, 0, 0] := by
  rw [show D2M8K2.u9138 = KTree.node D2M8K2.t9146 (nat_lit 19878151) (nat_lit 2394825812) (nat_lit 0) D2M8K2.t9147 from rfl, totK_node, tot9146, tot9147]
  decide +kernel

theorem arows9140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9140 = true := by
  rw [show D2M8K2.u9140 = KTree.node D2M8K2.t9148 (nat_lit 19882979) (nat_lit 2849658345) (nat_lit 0) D2M8K2.t9149 from rfl, allE_node, rows9148, irow9140, rows9149]
  all_goals rfl

theorem atot9140 : totK PD2M8K2 D2M8K2.u9140 = [0, 376960225047, 931102850904, 481978952878, 37385091459, 0, 0, 0] := by
  rw [show D2M8K2.u9140 = KTree.node D2M8K2.t9148 (nat_lit 19882979) (nat_lit 2849658345) (nat_lit 0) D2M8K2.t9149 from rfl, totK_node, tot9148, tot9149]
  decide +kernel

theorem arows9141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9141 = true := by
  rw [show D2M8K2.u9141 = KTree.node D2M8K2.t9150 (nat_lit 19884485) (nat_lit 1533471496) (nat_lit 0) D2M8K2.t9151 from rfl, allE_node, rows9150, irow9141, rows9151]
  all_goals rfl

theorem atot9141 : totK PD2M8K2 D2M8K2.u9141 = [0, 38298785186, 536396908060, 917014856200, 280239629746, 8644676715, 0, 0] := by
  rw [show D2M8K2.u9141 = KTree.node D2M8K2.t9150 (nat_lit 19884485) (nat_lit 1533471496) (nat_lit 0) D2M8K2.t9151 from rfl, totK_node, tot9150, tot9151]
  decide +kernel

theorem arows9147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9147 = true := by
  rw [show D2M8K2.u9147 = KTree.node D2M8K2.t9152 (nat_lit 19907164) (nat_lit 3903520620) (nat_lit 0) D2M8K2.t9153 from rfl, allE_node, rows9152, irow9147, rows9153]
  all_goals rfl

theorem atot9147 : totK PD2M8K2 D2M8K2.u9147 = [295802624399, 717867786171, 399141411017, 242330754916, 132698247117, 13338039113, 0, 0] := by
  rw [show D2M8K2.u9147 = KTree.node D2M8K2.t9152 (nat_lit 19907164) (nat_lit 3903520620) (nat_lit 0) D2M8K2.t9153 from rfl, totK_node, tot9152, tot9153]
  decide +kernel

theorem arows9148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9148 = true := by
  rw [show D2M8K2.u9148 = KTree.node D2M8K2.t9154 (nat_lit 19908374) (nat_lit 2607356439) (nat_lit 0) D2M8K2.t9155 from rfl, allE_node, rows9154, irow9148, rows9155]
  all_goals rfl

theorem atot9148 : totK PD2M8K2 D2M8K2.u9148 = [137144555594, 712703014231, 803488207362, 135304836385, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u9148 = KTree.node D2M8K2.t9154 (nat_lit 19908374) (nat_lit 2607356439) (nat_lit 0) D2M8K2.t9155 from rfl, totK_node, tot9154, tot9155]
  decide +kernel

theorem arows9150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9150 = true := by
  rw [show D2M8K2.u9150 = KTree.node D2M8K2.t9156 (nat_lit 19913960) (nat_lit 3647177541) (nat_lit 0) D2M8K2.t9157 from rfl, allE_node, rows9156, irow9150, rows9157]
  all_goals rfl

theorem atot9150 : totK PD2M8K2 D2M8K2.u9150 = [314795536797, 890474850567, 537281773444, 48397197097, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9150 = KTree.node D2M8K2.t9156 (nat_lit 19913960) (nat_lit 3647177541) (nat_lit 0) D2M8K2.t9157 from rfl, totK_node, tot9156, tot9157]
  decide +kernel

theorem arows9151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9151 = true := by
  rw [show D2M8K2.u9151 = KTree.node D2M8K2.t9158 (nat_lit 19915598) (nat_lit 3820489973) (nat_lit 0) D2M8K2.t9159 from rfl, allE_node, rows9158, irow9151, rows9159]
  all_goals rfl

theorem atot9151 : totK PD2M8K2 D2M8K2.u9151 = [65009544155, 512119683003, 880634615908, 276749820170, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u9151 = KTree.node D2M8K2.t9158 (nat_lit 19915598) (nat_lit 3820489973) (nat_lit 0) D2M8K2.t9159 from rfl, totK_node, tot9158, tot9159]
  decide +kernel

theorem arows9154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9154 = true := by
  rw [show D2M8K2.u9154 = KTree.node D2M8K2.t9160 (nat_lit 19917796) (nat_lit 2757144916) (nat_lit 0) D2M8K2.t9161 from rfl, allE_node, rows9160, irow9154, rows9161]
  all_goals rfl

theorem atot9154 : totK PD2M8K2 D2M8K2.u9154 = [351725931832, 918073025983, 505671698331, 45059206367, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9154 = KTree.node D2M8K2.t9160 (nat_lit 19917796) (nat_lit 2757144916) (nat_lit 0) D2M8K2.t9161 from rfl, totK_node, tot9160, tot9161]
  decide +kernel

theorem arows9155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9155 = true := by
  rw [show D2M8K2.u9155 = KTree.node D2M8K2.t9162 (nat_lit 19919060) (nat_lit 3637591942) (nat_lit 0) D2M8K2.t9163 from rfl, allE_node, rows9162, irow9155, rows9163]
  all_goals rfl

theorem atot9155 : totK PD2M8K2 D2M8K2.u9155 = [61933783068, 516133942008, 892090635847, 288451452662, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u9155 = KTree.node D2M8K2.t9162 (nat_lit 19919060) (nat_lit 3637591942) (nat_lit 0) D2M8K2.t9163 from rfl, totK_node, tot9162, tot9163]
  decide +kernel

theorem arows9157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9157 = true := by
  rw [show D2M8K2.u9157 = KTree.node D2M8K2.t9164 (nat_lit 19920884) (nat_lit 3241355303) (nat_lit 0) D2M8K2.t9165 from rfl, allE_node, rows9164, irow9157, rows9165]
  all_goals rfl

theorem atot9157 : totK PD2M8K2 D2M8K2.u9157 = [329407758827, 877418619157, 535377868450, 57779363789, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9157 = KTree.node D2M8K2.t9164 (nat_lit 19920884) (nat_lit 3241355303) (nat_lit 0) D2M8K2.t9165 from rfl, totK_node, tot9164, tot9165]
  decide +kernel

theorem arows9158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9158 = true := by
  rw [show D2M8K2.u9158 = KTree.node D2M8K2.t9166 (nat_lit 19922443) (nat_lit 1786879011) (nat_lit 0) D2M8K2.t9167 from rfl, allE_node, rows9166, irow9158, rows9167]
  all_goals rfl

theorem atot9158 : totK PD2M8K2 D2M8K2.u9158 = [91637619653, 676650043251, 871763492129, 149449366939, 2165917952, 0, 0, 0] := by
  rw [show D2M8K2.u9158 = KTree.node D2M8K2.t9166 (nat_lit 19922443) (nat_lit 1786879011) (nat_lit 0) D2M8K2.t9167 from rfl, totK_node, tot9166, tot9167]
  decide +kernel

theorem arows9162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9162 = true := by
  rw [show D2M8K2.u9162 = KTree.node D2M8K2.t9168 (nat_lit 19924716) (nat_lit 3553967284) (nat_lit 0) D2M8K2.t9169 from rfl, allE_node, rows9168, irow9162, rows9169]
  all_goals rfl

theorem atot9162 : totK PD2M8K2 D2M8K2.u9162 = [326462839732, 856317868526, 532866687580, 88724585122, 2814597007, 0, 0, 0] := by
  rw [show D2M8K2.u9162 = KTree.node D2M8K2.t9168 (nat_lit 19924716) (nat_lit 3553967284) (nat_lit 0) D2M8K2.t9169 from rfl, totK_node, tot9168, tot9169]
  decide +kernel

theorem arows9163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9163 = true := by
  rw [show D2M8K2.u9163 = KTree.node D2M8K2.t9170 (nat_lit 19926581) (nat_lit 1100581182) (nat_lit 0) D2M8K2.t9171 from rfl, allE_node, rows9170, irow9163, rows9171]
  all_goals rfl

theorem atot9163 : totK PD2M8K2 D2M8K2.u9163 = [0, 391586164022, 942695739188, 405310146738, 23418599596, 0, 0, 0] := by
  rw [show D2M8K2.u9163 = KTree.node D2M8K2.t9170 (nat_lit 19926581) (nat_lit 1100581182) (nat_lit 0) D2M8K2.t9171 from rfl, totK_node, tot9170, tot9171]
  decide +kernel

theorem arows9165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9165 = true := by
  rw [show D2M8K2.u9165 = KTree.node D2M8K2.t9172 (nat_lit 19928398) (nat_lit 2853319036) (nat_lit 0) D2M8K2.t9173 from rfl, allE_node, rows9172, irow9165, rows9173]
  all_goals rfl

theorem atot9165 : totK PD2M8K2 D2M8K2.u9165 = [0, 339470128289, 923012190172, 447898803380, 26867145498, 0, 0, 0] := by
  rw [show D2M8K2.u9165 = KTree.node D2M8K2.t9172 (nat_lit 19928398) (nat_lit 2853319036) (nat_lit 0) D2M8K2.t9173 from rfl, totK_node, tot9172, tot9173]
  decide +kernel

theorem arows9166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9166 = true := by
  rw [show D2M8K2.u9166 = KTree.node D2M8K2.t9174 (nat_lit 19930202) (nat_lit 3257598614) (nat_lit 0) D2M8K2.t9175 from rfl, allE_node, rows9174, irow9166, rows9175]
  all_goals rfl

theorem atot9166 : totK PD2M8K2 D2M8K2.u9166 = [0, 136056719320, 702619086144, 759085881518, 137618117216, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9166 = KTree.node D2M8K2.t9174 (nat_lit 19930202) (nat_lit 3257598614) (nat_lit 0) D2M8K2.t9175 from rfl, totK_node, tot9174, tot9175]
  decide +kernel

theorem arows9169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9169 = true := by
  rw [show D2M8K2.u9169 = KTree.node D2M8K2.t9176 (nat_lit 19935537) (nat_lit 1590436039) (nat_lit 0) D2M8K2.t9177 from rfl, allE_node, rows9176, irow9169, rows9177]
  all_goals rfl

theorem atot9169 : totK PD2M8K2 D2M8K2.u9169 = [0, 351864378290, 928421448710, 457548128300, 26515492062, 0, 0, 0] := by
  rw [show D2M8K2.u9169 = KTree.node D2M8K2.t9176 (nat_lit 19935537) (nat_lit 1590436039) (nat_lit 0) D2M8K2.t9177 from rfl, totK_node, tot9176, tot9177]
  decide +kernel

theorem arows9170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9170 = true := by
  rw [show D2M8K2.u9170 = KTree.node D2M8K2.t9178 (nat_lit 19938901) (nat_lit 1251107443) (nat_lit 0) D2M8K2.t9179 from rfl, allE_node, rows9178, irow9170, rows9179]
  all_goals rfl

theorem atot9170 : totK PD2M8K2 D2M8K2.u9170 = [0, 387071794428, 942341850905, 437602719649, 25275037740, 0, 0, 0] := by
  rw [show D2M8K2.u9170 = KTree.node D2M8K2.t9178 (nat_lit 19938901) (nat_lit 1251107443) (nat_lit 0) D2M8K2.t9179 from rfl, totK_node, tot9178, tot9179]
  decide +kernel

theorem arows9172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9172 = true := by
  rw [show D2M8K2.u9172 = KTree.node D2M8K2.t9180 (nat_lit 19941984) (nat_lit 3690063848) (nat_lit 0) D2M8K2.t9181 from rfl, allE_node, rows9180, irow9172, rows9181]
  all_goals rfl

theorem atot9172 : totK PD2M8K2 D2M8K2.u9172 = [0, 351572098855, 939058348974, 452188417836, 23530630971, 0, 0, 0] := by
  rw [show D2M8K2.u9172 = KTree.node D2M8K2.t9180 (nat_lit 19941984) (nat_lit 3690063848) (nat_lit 0) D2M8K2.t9181 from rfl, totK_node, tot9180, tot9181]
  decide +kernel

theorem arows9173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9173 = true := by
  rw [show D2M8K2.u9173 = KTree.node D2M8K2.t9182 (nat_lit 19945577) (nat_lit 1450066104) (nat_lit 0) D2M8K2.t9183 from rfl, allE_node, rows9182, irow9173, rows9183]
  all_goals rfl

theorem atot9173 : totK PD2M8K2 D2M8K2.u9173 = [94305354095, 461934163786, 834787836533, 397152417781, 22707977453, 0, 0, 0] := by
  rw [show D2M8K2.u9173 = KTree.node D2M8K2.t9182 (nat_lit 19945577) (nat_lit 1450066104) (nat_lit 0) D2M8K2.t9183 from rfl, totK_node, tot9182, tot9183]
  decide +kernel

theorem arows9178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9178 = true := by
  rw [show D2M8K2.u9178 = KTree.node D2M8K2.t9184 (nat_lit 19952486) (nat_lit 3992174847) (nat_lit 0) D2M8K2.t9185 from rfl, allE_node, rows9184, irow9178, rows9185]
  all_goals rfl

theorem atot9178 : totK PD2M8K2 D2M8K2.u9178 = [347975436439, 923435125049, 520372208014, 42362598623, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9178 = KTree.node D2M8K2.t9184 (nat_lit 19952486) (nat_lit 3992174847) (nat_lit 0) D2M8K2.t9185 from rfl, totK_node, tot9184, tot9185]
  decide +kernel

theorem arows9179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9179 = true := by
  rw [show D2M8K2.u9179 = KTree.node D2M8K2.t9186 (nat_lit 19953934) (nat_lit 3988033701) (nat_lit 0) D2M8K2.t9187 from rfl, allE_node, rows9186, irow9179, rows9187]
  all_goals rfl

theorem atot9179 : totK PD2M8K2 D2M8K2.u9179 = [0, 413880342569, 945900102274, 421209192777, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u9179 = KTree.node D2M8K2.t9186 (nat_lit 19953934) (nat_lit 3988033701) (nat_lit 0) D2M8K2.t9187 from rfl, totK_node, tot9186, tot9187]
  decide +kernel

theorem arows9181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9181 = true := by
  rw [show D2M8K2.u9181 = KTree.node D2M8K2.t9188 (nat_lit 19955337) (nat_lit 1895653084) (nat_lit 0) D2M8K2.t9189 from rfl, allE_node, rows9188, irow9181, rows9189]
  all_goals rfl

theorem atot9181 : totK PD2M8K2 D2M8K2.u9181 = [283644201134, 745944641187, 599071434064, 177090671385, 8214505460, 0, 0, 0] := by
  rw [show D2M8K2.u9181 = KTree.node D2M8K2.t9188 (nat_lit 19955337) (nat_lit 1895653084) (nat_lit 0) D2M8K2.t9189 from rfl, totK_node, tot9188, tot9189]
  decide +kernel

theorem arows9182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9182 = true := by
  rw [show D2M8K2.u9182 = KTree.node D2M8K2.t9190 (nat_lit 19957000) (nat_lit 3822099201) (nat_lit 0) D2M8K2.t9191 from rfl, allE_node, rows9190, irow9182, rows9191]
  all_goals rfl

theorem atot9182 : totK PD2M8K2 D2M8K2.u9182 = [100207512347, 636307550013, 829282677733, 213595417418, 9580924078, 0, 0, 0] := by
  rw [show D2M8K2.u9182 = KTree.node D2M8K2.t9190 (nat_lit 19957000) (nat_lit 3822099201) (nat_lit 0) D2M8K2.t9191 from rfl, totK_node, tot9190, tot9191]
  decide +kernel

theorem arows9185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9185 = true := by
  rw [show D2M8K2.u9185 = KTree.node D2M8K2.t9192 (nat_lit 19958866) (nat_lit 3970467854) (nat_lit 0) D2M8K2.t9193 from rfl, allE_node, rows9192, irow9185, rows9193]
  all_goals rfl

theorem atot9185 : totK PD2M8K2 D2M8K2.u9185 = [335670364964, 836146520186, 553269780776, 103815134318, 3455941720, 0, 0, 0] := by
  rw [show D2M8K2.u9185 = KTree.node D2M8K2.t9192 (nat_lit 19958866) (nat_lit 3970467854) (nat_lit 0) D2M8K2.t9193 from rfl, totK_node, tot9192, tot9193]
  decide +kernel

theorem arows9186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9186 = true := by
  rw [show D2M8K2.u9186 = KTree.node D2M8K2.t9194 (nat_lit 19960403) (nat_lit 2262045103) (nat_lit 0) D2M8K2.t9195 from rfl, allE_node, rows9194, irow9186, rows9195]
  all_goals rfl

theorem atot9186 : totK PD2M8K2 D2M8K2.u9186 = [80722692060, 628247257806, 856915926601, 225345736292, 9661765460, 0, 0, 0] := by
  rw [show D2M8K2.u9186 = KTree.node D2M8K2.t9194 (nat_lit 19960403) (nat_lit 2262045103) (nat_lit 0) D2M8K2.t9195 from rfl, totK_node, tot9194, tot9195]
  decide +kernel

theorem arows9188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9188 = true := by
  rw [show D2M8K2.u9188 = KTree.node D2M8K2.t9196 (nat_lit 19962244) (nat_lit 3786663752) (nat_lit 0) D2M8K2.t9197 from rfl, allE_node, rows9196, irow9188, rows9197]
  all_goals rfl

theorem atot9188 : totK PD2M8K2 D2M8K2.u9188 = [298350264268, 789248456695, 592634948346, 118618234243, 3575904516, 0, 0, 0] := by
  rw [show D2M8K2.u9188 = KTree.node D2M8K2.t9196 (nat_lit 19962244) (nat_lit 3786663752) (nat_lit 0) D2M8K2.t9197 from rfl, totK_node, tot9196, tot9197]
  decide +kernel

theorem arows9189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9189 = true := by
  rw [show D2M8K2.u9189 = KTree.node D2M8K2.t9198 (nat_lit 19963700) (nat_lit 3663048984) (nat_lit 0) D2M8K2.t9199 from rfl, allE_node, rows9198, irow9189, rows9199]
  all_goals rfl

theorem atot9189 : totK PD2M8K2 D2M8K2.u9189 = [124192078066, 733618463567, 820934130117, 125280445829, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u9189 = KTree.node D2M8K2.t9198 (nat_lit 19963700) (nat_lit 3663048984) (nat_lit 0) D2M8K2.t9199 from rfl, totK_node, tot9198, tot9199]
  decide +kernel

theorem arows9193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9193 = true := by
  rw [show D2M8K2.u9193 = KTree.node D2M8K2.t9200 (nat_lit 19965945) (nat_lit 1755333589) (nat_lit 0) D2M8K2.t9201 from rfl, allE_node, rows9200, irow9193, rows9201]
  all_goals rfl

theorem atot9193 : totK PD2M8K2 D2M8K2.u9193 = [328867273877, 804647652025, 578150340770, 125916473248, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u9193 = KTree.node D2M8K2.t9200 (nat_lit 19965945) (nat_lit 1755333589) (nat_lit 0) D2M8K2.t9201 from rfl, totK_node, tot9200, tot9201]
  decide +kernel

theorem arows9194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9194 = true := by
  rw [show D2M8K2.u9194 = KTree.node D2M8K2.t9202 (nat_lit 19967951) (nat_lit 2129976506) (nat_lit 0) D2M8K2.t9203 from rfl, allE_node, rows9202, irow9194, rows9203]
  all_goals rfl

theorem atot9194 : totK PD2M8K2 D2M8K2.u9194 = [4200607152, 498285801300, 953613352362, 336761166520, 19507587197, 0, 0, 0] := by
  rw [show D2M8K2.u9194 = KTree.node D2M8K2.t9202 (nat_lit 19967951) (nat_lit 2129976506) (nat_lit 0) D2M8K2.t9203 from rfl, totK_node, tot9202, tot9203]
  decide +kernel

theorem arows9196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9196 = true := by
  rw [show D2M8K2.u9196 = KTree.node D2M8K2.t9204 (nat_lit 19973171) (nat_lit 2850697850) (nat_lit 0) D2M8K2.t9205 from rfl, allE_node, rows9204, irow9196, rows9205]
  all_goals rfl

theorem atot9196 : totK PD2M8K2 D2M8K2.u9196 = [0, 364807926593, 933035307795, 499131057952, 37474619550, 0, 0, 0] := by
  rw [show D2M8K2.u9196 = KTree.node D2M8K2.t9204 (nat_lit 19973171) (nat_lit 2850697850) (nat_lit 0) D2M8K2.t9205 from rfl, totK_node, tot9204, tot9205]
  decide +kernel

theorem arows9197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9197 = true := by
  rw [show D2M8K2.u9197 = KTree.node D2M8K2.t9206 (nat_lit 19974625) (nat_lit 920322522) (nat_lit 0) D2M8K2.t9207 from rfl, allE_node, rows9206, irow9197, rows9207]
  all_goals rfl

theorem atot9197 : totK PD2M8K2 D2M8K2.u9197 = [0, 16104169343, 466713132505, 910015110275, 378235611305, 29044448997, 0, 0] := by
  rw [show D2M8K2.u9197 = KTree.node D2M8K2.t9206 (nat_lit 19974625) (nat_lit 920322522) (nat_lit 0) D2M8K2.t9207 from rfl, totK_node, tot9206, tot9207]
  decide +kernel

theorem arows9200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9200 = true := by
  rw [show D2M8K2.u9200 = KTree.node D2M8K2.t9208 (nat_lit 19976036) (nat_lit 3339273480) (nat_lit 0) D2M8K2.t9209 from rfl, allE_node, rows9208, irow9200, rows9209]
  all_goals rfl

theorem atot9200 : totK PD2M8K2 D2M8K2.u9200 = [0, 256960248335, 703648723839, 625191128469, 192809690920, 7877424857, 0, 0] := by
  rw [show D2M8K2.u9200 = KTree.node D2M8K2.t9208 (nat_lit 19976036) (nat_lit 3339273480) (nat_lit 0) D2M8K2.t9209 from rfl, totK_node, tot9208, tot9209]
  decide +kernel

theorem arows9201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9201 = true := by
  rw [show D2M8K2.u9201 = KTree.node D2M8K2.t9210 (nat_lit 19977752) (nat_lit 3688409988) (nat_lit 0) D2M8K2.t9211 from rfl, allE_node, rows9210, irow9201, rows9211]
  all_goals rfl

theorem atot9201 : totK PD2M8K2 D2M8K2.u9201 = [0, 122126538995, 673317105638, 823509638351, 168647700274, 4009909289, 0, 0] := by
  rw [show D2M8K2.u9201 = KTree.node D2M8K2.t9210 (nat_lit 19977752) (nat_lit 3688409988) (nat_lit 0) D2M8K2.t9211 from rfl, totK_node, tot9210, tot9211]
  decide +kernel

theorem arows9203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9203 = true := by
  rw [show D2M8K2.u9203 = KTree.node D2M8K2.t9212 (nat_lit 19979649) (nat_lit 1812249422) (nat_lit 0) D2M8K2.t9213 from rfl, allE_node, rows9212, irow9203, rows9213]
  all_goals rfl

theorem atot9203 : totK PD2M8K2 D2M8K2.u9203 = [0, 334739608666, 882786541619, 530908645129, 73988470711, 1149959346, 0, 0] := by
  rw [show D2M8K2.u9203 = KTree.node D2M8K2.t9212 (nat_lit 19979649) (nat_lit 1812249422) (nat_lit 0) D2M8K2.t9213 from rfl, totK_node, tot9212, tot9213]
  decide +kernel

theorem arows9204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9204 = true := by
  rw [show D2M8K2.u9204 = KTree.node D2M8K2.t9214 (nat_lit 19981736) (nat_lit 3399684660) (nat_lit 0) D2M8K2.t9215 from rfl, allE_node, rows9214, irow9204, rows9215]
  all_goals rfl

theorem atot9204 : totK PD2M8K2 D2M8K2.u9204 = [0, 80679071701, 631819431215, 872573989347, 206532061900, 5218872685, 0, 0] := by
  rw [show D2M8K2.u9204 = KTree.node D2M8K2.t9214 (nat_lit 19981736) (nat_lit 3399684660) (nat_lit 0) D2M8K2.t9215 from rfl, totK_node, tot9214, tot9215]
  decide +kernel

theorem arows9214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9214 = true := by
  rw [show D2M8K2.u9214 = KTree.node D2M8K2.t9216 (nat_lit 19983172) (nat_lit 3791607259) (nat_lit 0) D2M8K2.t9217 from rfl, allE_node, rows9216, irow9214, rows9217]
  all_goals rfl

theorem atot9214 : totK PD2M8K2 D2M8K2.u9214 = [0, 346194703708, 884272183082, 512903284220, 51125588495, 0, 0, 0] := by
  rw [show D2M8K2.u9214 = KTree.node D2M8K2.t9216 (nat_lit 19983172) (nat_lit 3791607259) (nat_lit 0) D2M8K2.t9217 from rfl, totK_node, tot9216, tot9217]
  decide +kernel

theorem arows9215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9215 = true := by
  rw [show D2M8K2.u9215 = KTree.node D2M8K2.t9218 (nat_lit 19984942) (nat_lit 3488271693) (nat_lit 0) D2M8K2.t9219 from rfl, allE_node, rows9218, irow9215, rows9219]
  all_goals rfl

theorem atot9215 : totK PD2M8K2 D2M8K2.u9215 = [0, 130632769111, 699674773866, 840872028383, 140622629294, 1415142070, 0, 0] := by
  rw [show D2M8K2.u9215 = KTree.node D2M8K2.t9218 (nat_lit 19984942) (nat_lit 3488271693) (nat_lit 0) D2M8K2.t9219 from rfl, totK_node, tot9218, tot9219]
  decide +kernel

theorem arows9217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9217 = true := by
  rw [show D2M8K2.u9217 = KTree.node D2M8K2.t9220 (nat_lit 19987049) (nat_lit 1422615439) (nat_lit 0) D2M8K2.t9221 from rfl, allE_node, rows9220, irow9217, rows9221]
  all_goals rfl

theorem atot9217 : totK PD2M8K2 D2M8K2.u9217 = [0, 276568045789, 868449072335, 633964070497, 73537613736, 0, 0, 0] := by
  rw [show D2M8K2.u9217 = KTree.node D2M8K2.t9220 (nat_lit 19987049) (nat_lit 1422615439) (nat_lit 0) D2M8K2.t9221 from rfl, totK_node, tot9220, tot9221]
  decide +kernel

theorem arows9218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9218 = true := by
  rw [show D2M8K2.u9218 = KTree.node D2M8K2.t9222 (nat_lit 19989355) (nat_lit 1595486283) (nat_lit 0) D2M8K2.t9223 from rfl, allE_node, rows9222, irow9218, rows9223]
  all_goals rfl

theorem atot9218 : totK PD2M8K2 D2M8K2.u9218 = [176055752117, 391257976396, 371918839123, 596701734738, 237761934406, 9302370699, 0, 0] := by
  rw [show D2M8K2.u9218 = KTree.node D2M8K2.t9222 (nat_lit 19989355) (nat_lit 1595486283) (nat_lit 0) D2M8K2.t9223 from rfl, totK_node, tot9222, tot9223]
  decide +kernel

theorem arows9221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9221 = true := by
  rw [show D2M8K2.u9221 = KTree.node D2M8K2.t9224 (nat_lit 19990948) (nat_lit 3764267211) (nat_lit 0) D2M8K2.t9225 from rfl, allE_node, rows9224, irow9221, rows9225]
  all_goals rfl

theorem atot9221 : totK PD2M8K2 D2M8K2.u9221 = [219374837633, 757344809647, 666418429567, 117459782505, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u9221 = KTree.node D2M8K2.t9224 (nat_lit 19990948) (nat_lit 3764267211) (nat_lit 0) D2M8K2.t9225 from rfl, totK_node, tot9224, tot9225]
  decide +kernel

theorem arows9222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9222 = true := by
  rw [show D2M8K2.u9222 = KTree.node D2M8K2.t9226 (nat_lit 19993368) (nat_lit 2243054951) (nat_lit 0) D2M8K2.t9227 from rfl, allE_node, rows9226, irow9222, rows9227]
  all_goals rfl

theorem atot9222 : totK PD2M8K2 D2M8K2.u9222 = [242263166798, 805455812968, 691879590193, 81905222687, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9222 = KTree.node D2M8K2.t9226 (nat_lit 19993368) (nat_lit 2243054951) (nat_lit 0) D2M8K2.t9227 from rfl, totK_node, tot9226, tot9227]
  decide +kernel

theorem arows9224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9224 = true := by
  rw [show D2M8K2.u9224 = KTree.node D2M8K2.t9228 (nat_lit 19994665) (nat_lit 1240097365) (nat_lit 0) D2M8K2.t9229 from rfl, allE_node, rows9228, irow9224, rows9229]
  all_goals rfl

theorem atot9224 : totK PD2M8K2 D2M8K2.u9224 = [161044031498, 673125318671, 713065259221, 253592954207, 24245300989, 0, 0, 0] := by
  rw [show D2M8K2.u9224 = KTree.node D2M8K2.t9228 (nat_lit 19994665) (nat_lit 1240097365) (nat_lit 0) D2M8K2.t9229 from rfl, totK_node, tot9228, tot9229]
  decide +kernel

theorem arows9225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9225 = true := by
  rw [show D2M8K2.u9225 = KTree.node D2M8K2.t9230 (nat_lit 19996197) (nat_lit 1052903226) (nat_lit 0) D2M8K2.t9231 from rfl, allE_node, rows9230, irow9225, rows9231]
  all_goals rfl

theorem atot9225 : totK PD2M8K2 D2M8K2.u9225 = [172392954269, 585563500965, 719696814000, 314781258115, 13319238344, 0, 0, 0] := by
  rw [show D2M8K2.u9225 = KTree.node D2M8K2.t9230 (nat_lit 19996197) (nat_lit 1052903226) (nat_lit 0) D2M8K2.t9231 from rfl, totK_node, tot9230, tot9231]
  decide +kernel

theorem arows9229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9229 = true := by
  rw [show D2M8K2.u9229 = KTree.node D2M8K2.t9232 (nat_lit 19997673) (nat_lit 1918752217) (nat_lit 0) D2M8K2.t9233 from rfl, allE_node, rows9232, irow9229, rows9233]
  all_goals rfl

theorem atot9229 : totK PD2M8K2 D2M8K2.u9229 = [253393508778, 809272993586, 644267354817, 94296906575, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u9229 = KTree.node D2M8K2.t9232 (nat_lit 19997673) (nat_lit 1918752217) (nat_lit 0) D2M8K2.t9233 from rfl, totK_node, tot9232, tot9233]
  decide +kernel

theorem arows9230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9230 = true := by
  rw [show D2M8K2.u9230 = KTree.node D2M8K2.t9234 (nat_lit 19999386) (nat_lit 2808277385) (nat_lit 0) D2M8K2.t9235 from rfl, allE_node, rows9234, irow9230, rows9235]
  all_goals rfl

theorem atot9230 : totK PD2M8K2 D2M8K2.u9230 = [121752865925, 601072032688, 813122764457, 240892036702, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u9230 = KTree.node D2M8K2.t9234 (nat_lit 19999386) (nat_lit 2808277385) (nat_lit 0) D2M8K2.t9235 from rfl, totK_node, tot9234, tot9235]
  decide +kernel

theorem arows9232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9232 = true := by
  rw [show D2M8K2.u9232 = KTree.node D2M8K2.t9236 (nat_lit 20004231) (nat_lit 3617197119) (nat_lit 0) D2M8K2.t9237 from rfl, allE_node, rows9236, irow9232, rows9237]
  all_goals rfl

theorem atot9232 : totK PD2M8K2 D2M8K2.u9232 = [301534202593, 884672736246, 566806947267, 54872969655, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9232 = KTree.node D2M8K2.t9236 (nat_lit 20004231) (nat_lit 3617197119) (nat_lit 0) D2M8K2.t9237 from rfl, totK_node, tot9236, tot9237]
  decide +kernel

theorem arows9233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9233 = true := by
  rw [show D2M8K2.u9233 = KTree.node D2M8K2.t9238 (nat_lit 20006237) (nat_lit 2269069152) (nat_lit 0) D2M8K2.t9239 from rfl, allE_node, rows9238, irow9233, rows9239]
  all_goals rfl

theorem atot9233 : totK PD2M8K2 D2M8K2.u9233 = [0, 489523493502, 1016746132887, 284885544646, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u9233 = KTree.node D2M8K2.t9238 (nat_lit 20006237) (nat_lit 2269069152) (nat_lit 0) D2M8K2.t9239 from rfl, totK_node, tot9238, tot9239]
  decide +kernel

theorem arows9236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9236 = true := by
  rw [show D2M8K2.u9236 = KTree.node D2M8K2.t9240 (nat_lit 20011566) (nat_lit 2756470891) (nat_lit 0) D2M8K2.t9241 from rfl, allE_node, rows9240, irow9236, rows9241]
  all_goals rfl

theorem atot9236 : totK PD2M8K2 D2M8K2.u9236 = [0, 252353407569, 803695044572, 582350066100, 80606933899, 1206465782, 0, 0] := by
  rw [show D2M8K2.u9236 = KTree.node D2M8K2.t9240 (nat_lit 20011566) (nat_lit 2756470891) (nat_lit 0) D2M8K2.t9241 from rfl, totK_node, tot9240, tot9241]
  decide +kernel

theorem arows9237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9237 = true := by
  rw [show D2M8K2.u9237 = KTree.node D2M8K2.t9242 (nat_lit 20014100) (nat_lit 3676162564) (nat_lit 0) D2M8K2.t9243 from rfl, allE_node, rows9242, irow9237, rows9243]
  all_goals rfl

theorem atot9237 : totK PD2M8K2 D2M8K2.u9237 = [0, 249381387768, 827105396121, 651642756084, 67403041370, 0, 0, 0] := by
  rw [show D2M8K2.u9237 = KTree.node D2M8K2.t9242 (nat_lit 20014100) (nat_lit 3676162564) (nat_lit 0) D2M8K2.t9243 from rfl, totK_node, tot9242, tot9243]
  decide +kernel

theorem arows9239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9239 = true := by
  rw [show D2M8K2.u9239 = KTree.node D2M8K2.t9244 (nat_lit 20015416) (nat_lit 3359797656) (nat_lit 0) D2M8K2.t9245 from rfl, allE_node, rows9244, irow9239, rows9245]
  all_goals rfl

theorem atot9239 : totK PD2M8K2 D2M8K2.u9239 = [0, 345500192714, 933430892378, 491468851018, 33229407172, 0, 0, 0] := by
  rw [show D2M8K2.u9239 = KTree.node D2M8K2.t9244 (nat_lit 20015416) (nat_lit 3359797656) (nat_lit 0) D2M8K2.t9245 from rfl, totK_node, tot9244, tot9245]
  decide +kernel

theorem arows9240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9240 = true := by
  rw [show D2M8K2.u9240 = KTree.node D2M8K2.t9246 (nat_lit 20018630) (nat_lit 4125996321) (nat_lit 0) D2M8K2.t9247 from rfl, allE_node, rows9246, irow9240, rows9247]
  all_goals rfl

theorem atot9240 : totK PD2M8K2 D2M8K2.u9240 = [0, 234497819971, 802221419074, 635198725232, 96997791300, 1162935789, 0, 0] := by
  rw [show D2M8K2.u9240 = KTree.node D2M8K2.t9246 (nat_lit 20018630) (nat_lit 4125996321) (nat_lit 0) D2M8K2.t9247 from rfl, totK_node, tot9246, tot9247]
  decide +kernel

theorem arows9245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9245 = true := by
  rw [show D2M8K2.u9245 = KTree.node D2M8K2.t9248 (nat_lit 20020362) (nat_lit 1826855077) (nat_lit 0) D2M8K2.t9249 from rfl, allE_node, rows9248, irow9245, rows9249]
  all_goals rfl

theorem atot9245 : totK PD2M8K2 D2M8K2.u9245 = [0, 170315919782, 656720332643, 706178099680, 204906555536, 11853261585, 0, 0] := by
  rw [show D2M8K2.u9245 = KTree.node D2M8K2.t9248 (nat_lit 20020362) (nat_lit 1826855077) (nat_lit 0) D2M8K2.t9249 from rfl, totK_node, tot9248, tot9249]
  decide +kernel

theorem arows9246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9246 = true := by
  rw [show D2M8K2.u9246 = KTree.node D2M8K2.t9250 (nat_lit 20025260) (nat_lit 3791391080) (nat_lit 0) D2M8K2.t9251 from rfl, allE_node, rows9250, irow9246, rows9251]
  all_goals rfl

theorem atot9246 : totK PD2M8K2 D2M8K2.u9246 = [0, 250618406545, 830382920034, 599545152135, 72878444262, 1021600638, 0, 0] := by
  rw [show D2M8K2.u9246 = KTree.node D2M8K2.t9250 (nat_lit 20025260) (nat_lit 3791391080) (nat_lit 0) D2M8K2.t9251 from rfl, totK_node, tot9250, tot9251]
  decide +kernel

theorem arows9248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9248 = true := by
  rw [show D2M8K2.u9248 = KTree.node D2M8K2.t9252 (nat_lit 20031074) (nat_lit 2984032672) (nat_lit 0) D2M8K2.t9253 from rfl, allE_node, rows9252, irow9248, rows9253]
  all_goals rfl

theorem atot9248 : totK PD2M8K2 D2M8K2.u9248 = [243074140685, 556490906165, 449803954137, 397924783997, 93166853631, 3552795014, 0, 0] := by
  rw [show D2M8K2.u9248 = KTree.node D2M8K2.t9252 (nat_lit 20031074) (nat_lit 2984032672) (nat_lit 0) D2M8K2.t9253 from rfl, totK_node, tot9252, tot9253]
  decide +kernel

theorem arows9249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9249 = true := by
  rw [show D2M8K2.u9249 = KTree.node D2M8K2.t9254 (nat_lit 20032643) (nat_lit 2886047953) (nat_lit 0) D2M8K2.t9255 from rfl, allE_node, rows9254, irow9249, rows9255]
  all_goals rfl

theorem atot9249 : totK PD2M8K2 D2M8K2.u9249 = [164210109155, 733068040170, 749659110018, 130531694173, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u9249 = KTree.node D2M8K2.t9254 (nat_lit 20032643) (nat_lit 2886047953) (nat_lit 0) D2M8K2.t9255 from rfl, totK_node, tot9254, tot9255]
  decide +kernel

theorem arows9252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9252 = true := by
  rw [show D2M8K2.u9252 = KTree.node D2M8K2.t9256 (nat_lit 20034990) (nat_lit 3833386876) (nat_lit 0) D2M8K2.t9257 from rfl, allE_node, rows9256, irow9252, rows9257]
  all_goals rfl

theorem atot9252 : totK PD2M8K2 D2M8K2.u9252 = [283347685658, 846791462363, 639617606851, 70117588926, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9252 = KTree.node D2M8K2.t9256 (nat_lit 20034990) (nat_lit 3833386876) (nat_lit 0) D2M8K2.t9257 from rfl, totK_node, tot9256, tot9257]
  decide +kernel

theorem arows9253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9253 = true := by
  rw [show D2M8K2.u9253 = KTree.node D2M8K2.t9258 (nat_lit 20036544) (nat_lit 2570912589) (nat_lit 0) D2M8K2.t9259 from rfl, allE_node, rows9258, irow9253, rows9259]
  all_goals rfl

theorem atot9253 : totK PD2M8K2 D2M8K2.u9253 = [135217399024, 626460942460, 747464760980, 286812854205, 25353971821, 0, 0, 0] := by
  rw [show D2M8K2.u9253 = KTree.node D2M8K2.t9258 (nat_lit 20036544) (nat_lit 2570912589) (nat_lit 0) D2M8K2.t9259 from rfl, totK_node, tot9258, tot9259]
  decide +kernel

theorem arows9255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9255 = true := by
  rw [show D2M8K2.u9255 = KTree.node D2M8K2.t9260 (nat_lit 20037822) (nat_lit 3952233191) (nat_lit 0) D2M8K2.t9261 from rfl, allE_node, rows9260, irow9255, rows9261]
  all_goals rfl

theorem atot9255 : totK PD2M8K2 D2M8K2.u9255 = [175298174919, 599649708074, 743344423064, 289774485714, 12058333121, 0, 0, 0] := by
  rw [show D2M8K2.u9255 = KTree.node D2M8K2.t9260 (nat_lit 20037822) (nat_lit 3952233191) (nat_lit 0) D2M8K2.t9261 from rfl, totK_node, tot9260, tot9261]
  decide +kernel

theorem arows9256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9256 = true := by
  rw [show D2M8K2.u9256 = KTree.node D2M8K2.t9262 (nat_lit 20042745) (nat_lit 1902210205) (nat_lit 0) D2M8K2.t9263 from rfl, allE_node, rows9262, irow9256, rows9263]
  all_goals rfl

theorem atot9256 : totK PD2M8K2 D2M8K2.u9256 = [265889318645, 814745468969, 634242220165, 103790459220, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u9256 = KTree.node D2M8K2.t9262 (nat_lit 20042745) (nat_lit 1902210205) (nat_lit 0) D2M8K2.t9263 from rfl, totK_node, tot9262, tot9263]
  decide +kernel

theorem arows9260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9260 = true := by
  rw [show D2M8K2.u9260 = KTree.node D2M8K2.t9264 (nat_lit 20044396) (nat_lit 2717668658) (nat_lit 0) D2M8K2.t9265 from rfl, allE_node, rows9264, irow9260, rows9265]
  all_goals rfl

theorem atot9260 : totK PD2M8K2 D2M8K2.u9260 = [146186006935, 625260563596, 781862428484, 230725938192, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u9260 = KTree.node D2M8K2.t9264 (nat_lit 20044396) (nat_lit 2717668658) (nat_lit 0) D2M8K2.t9265 from rfl, totK_node, tot9264, tot9265]
  decide +kernel

theorem arows9261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9261 = true := by
  rw [show D2M8K2.u9261 = KTree.node D2M8K2.t9266 (nat_lit 20045790) (nat_lit 3955044315) (nat_lit 0) D2M8K2.t9267 from rfl, allE_node, rows9266, irow9261, rows9267]
  all_goals rfl

theorem atot9261 : totK PD2M8K2 D2M8K2.u9261 = [277917421625, 859651480441, 606324468796, 63616800257, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9261 = KTree.node D2M8K2.t9266 (nat_lit 20045790) (nat_lit 3955044315) (nat_lit 0) D2M8K2.t9267 from rfl, totK_node, tot9266, tot9267]
  decide +kernel

theorem arows9263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9263 = true := by
  rw [show D2M8K2.u9263 = KTree.node D2M8K2.t9268 (nat_lit 20047740) (nat_lit 2962021332) (nat_lit 0) D2M8K2.t9269 from rfl, allE_node, rows9268, irow9263, rows9269]
  all_goals rfl

theorem atot9263 : totK PD2M8K2 D2M8K2.u9263 = [167254128862, 680961021140, 780937331032, 180722482301, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u9263 = KTree.node D2M8K2.t9268 (nat_lit 20047740) (nat_lit 2962021332) (nat_lit 0) D2M8K2.t9269 from rfl, totK_node, tot9268, tot9269]
  decide +kernel

theorem arows9264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9264 = true := by
  rw [show D2M8K2.u9264 = KTree.node D2M8K2.t9270 (nat_lit 20049835) (nat_lit 1613191705) (nat_lit 0) D2M8K2.t9271 from rfl, allE_node, rows9270, irow9264, rows9271]
  all_goals rfl

theorem atot9264 : totK PD2M8K2 D2M8K2.u9264 = [178471279803, 742321687547, 772843515703, 137828498610, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u9264 = KTree.node D2M8K2.t9270 (nat_lit 20049835) (nat_lit 1613191705) (nat_lit 0) D2M8K2.t9271 from rfl, totK_node, tot9270, tot9271]
  decide +kernel

theorem arows9267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9267 = true := by
  rw [show D2M8K2.u9267 = KTree.node D2M8K2.t9272 (nat_lit 20051795) (nat_lit 2861354393) (nat_lit 0) D2M8K2.t9273 from rfl, allE_node, rows9272, irow9267, rows9273]
  all_goals rfl

theorem atot9267 : totK PD2M8K2 D2M8K2.u9267 = [0, 383343826755, 960475504033, 411730822953, 20666902032, 0, 0, 0] := by
  rw [show D2M8K2.u9267 = KTree.node D2M8K2.t9272 (nat_lit 20051795) (nat_lit 2861354393) (nat_lit 0) D2M8K2.t9273 from rfl, totK_node, tot9272, tot9273]
  decide +kernel

theorem arows9268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9268 = true := by
  rw [show D2M8K2.u9268 = KTree.node D2M8K2.t9274 (nat_lit 20053420) (nat_lit 3483140896) (nat_lit 0) D2M8K2.t9275 from rfl, allE_node, rows9274, irow9268, rows9275]
  all_goals rfl

theorem atot9268 : totK PD2M8K2 D2M8K2.u9268 = [0, 163374322970, 741333999601, 725654392575, 101713857005, 1239866073, 0, 0] := by
  rw [show D2M8K2.u9268 = KTree.node D2M8K2.t9274 (nat_lit 20053420) (nat_lit 3483140896) (nat_lit 0) D2M8K2.t9275 from rfl, totK_node, tot9274, tot9275]
  decide +kernel

theorem arows9270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9270 = true := by
  rw [show D2M8K2.u9270 = KTree.node D2M8K2.t9276 (nat_lit 20055808) (nat_lit 3768172604) (nat_lit 0) D2M8K2.t9277 from rfl, allE_node, rows9276, irow9270, rows9277]
  all_goals rfl

theorem atot9270 : totK PD2M8K2 D2M8K2.u9270 = [0, 336006232499, 882270112031, 561397699934, 52435579864, 0, 0, 0] := by
  rw [show D2M8K2.u9270 = KTree.node D2M8K2.t9276 (nat_lit 20055808) (nat_lit 3768172604) (nat_lit 0) D2M8K2.t9277 from rfl, totK_node, tot9276, tot9277]
  decide +kernel

theorem arows9271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9271 = true := by
  rw [show D2M8K2.u9271 = KTree.node D2M8K2.t9278 (nat_lit 20062298) (nat_lit 3387887240) (nat_lit 0) D2M8K2.t9279 from rfl, allE_node, rows9278, irow9271, rows9279]
  all_goals rfl

theorem atot9271 : totK PD2M8K2 D2M8K2.u9271 = [0, 348399304329, 948706749936, 493542345127, 35237834161, 0, 0, 0] := by
  rw [show D2M8K2.u9271 = KTree.node D2M8K2.t9278 (nat_lit 20062298) (nat_lit 3387887240) (nat_lit 0) D2M8K2.t9279 from rfl, totK_node, tot9278, tot9279]
  decide +kernel

theorem arows9277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9277 = true := by
  rw [show D2M8K2.u9277 = KTree.node D2M8K2.t9280 (nat_lit 20063784) (nat_lit 3408782362) (nat_lit 0) D2M8K2.t9281 from rfl, allE_node, rows9280, irow9277, rows9281]
  all_goals rfl

theorem atot9277 : totK PD2M8K2 D2M8K2.u9277 = [0, 171545254961, 742263483175, 742148026865, 125925468387, 1171084559, 0, 0] := by
  rw [show D2M8K2.u9277 = KTree.node D2M8K2.t9280 (nat_lit 20063784) (nat_lit 3408782362) (nat_lit 0) D2M8K2.t9281 from rfl, totK_node, tot9280, tot9281]
  decide +kernel

theorem arows9278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9278 = true := by
  rw [show D2M8K2.u9278 = KTree.node D2M8K2.t9282 (nat_lit 20065619) (nat_lit 2578900959) (nat_lit 0) D2M8K2.t9283 from rfl, allE_node, rows9282, irow9278, rows9283]
  all_goals rfl

theorem atot9278 : totK PD2M8K2 D2M8K2.u9278 = [0, 241865305652, 718886082669, 608280559321, 181374413344, 11934365838, 0, 0] := by
  rw [show D2M8K2.u9278 = KTree.node D2M8K2.t9282 (nat_lit 20065619) (nat_lit 2578900959) (nat_lit 0) D2M8K2.t9283 from rfl, totK_node, tot9282, tot9283]
  decide +kernel

theorem arows9280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9280 = true := by
  rw [show D2M8K2.u9280 = KTree.node D2M8K2.t9284 (nat_lit 20066880) (nat_lit 3232904167) (nat_lit 0) D2M8K2.t9285 from rfl, allE_node, rows9284, irow9280, rows9285]
  all_goals rfl

theorem atot9280 : totK PD2M8K2 D2M8K2.u9280 = [0, 179935757967, 788809968821, 693438085273, 86299465605, 1053411165, 0, 0] := by
  rw [show D2M8K2.u9280 = KTree.node D2M8K2.t9284 (nat_lit 20066880) (nat_lit 3232904167) (nat_lit 0) D2M8K2.t9285 from rfl, totK_node, tot9284, tot9285]
  decide +kernel

theorem arows9281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9281 = true := by
  rw [show D2M8K2.u9281 = KTree.node D2M8K2.t9286 (nat_lit 20069260) (nat_lit 3471800324) (nat_lit 0) D2M8K2.t9287 from rfl, allE_node, rows9286, irow9281, rows9287]
  all_goals rfl

theorem atot9281 : totK PD2M8K2 D2M8K2.u9281 = [0, 255275087570, 783673969643, 631945656736, 114776562949, 3667207281, 0, 0] := by
  rw [show D2M8K2.u9281 = KTree.node D2M8K2.t9286 (nat_lit 20069260) (nat_lit 3471800324) (nat_lit 0) D2M8K2.t9287 from rfl, totK_node, tot9286, tot9287]
  decide +kernel

theorem arows9284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9284 = true := by
  rw [show D2M8K2.u9284 = KTree.node D2M8K2.t9288 (nat_lit 20073036) (nat_lit 3573707026) (nat_lit 0) D2M8K2.t9289 from rfl, allE_node, rows9288, irow9284, rows9289]
  all_goals rfl

theorem atot9284 : totK PD2M8K2 D2M8K2.u9284 = [288897746189, 783402164802, 554775642114, 162063167111, 13444587001, 0, 0, 0] := by
  rw [show D2M8K2.u9284 = KTree.node D2M8K2.t9288 (nat_lit 20073036) (nat_lit 3573707026) (nat_lit 0) D2M8K2.t9289 from rfl, totK_node, tot9288, tot9289]
  decide +kernel

theorem arows9285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9285 = true := by
  rw [show D2M8K2.u9285 = KTree.node D2M8K2.t9290 (nat_lit 20074284) (nat_lit 3202353509) (nat_lit 0) D2M8K2.t9291 from rfl, allE_node, rows9290, irow9285, rows9291]
  all_goals rfl

theorem atot9285 : totK PD2M8K2 D2M8K2.u9285 = [123535522706, 697553499196, 805521162423, 139577074808, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u9285 = KTree.node D2M8K2.t9290 (nat_lit 20074284) (nat_lit 3202353509) (nat_lit 0) D2M8K2.t9291 from rfl, totK_node, tot9290, tot9291]
  decide +kernel

theorem arows9287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9287 = true := by
  rw [show D2M8K2.u9287 = KTree.node D2M8K2.t9292 (nat_lit 20076603) (nat_lit 3625946858) (nat_lit 0) D2M8K2.t9293 from rfl, allE_node, rows9292, irow9287, rows9293]
  all_goals rfl

theorem atot9287 : totK PD2M8K2 D2M8K2.u9287 = [354537707310, 874546679810, 536767260586, 54792332552, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9287 = KTree.node D2M8K2.t9292 (nat_lit 20076603) (nat_lit 3625946858) (nat_lit 0) D2M8K2.t9293 from rfl, totK_node, tot9292, tot9293]
  decide +kernel

theorem arows9288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9288 = true := by
  rw [show D2M8K2.u9288 = KTree.node D2M8K2.t9294 (nat_lit 20078133) (nat_lit 1049723481) (nat_lit 0) D2M8K2.t9295 from rfl, allE_node, rows9294, irow9288, rows9295]
  all_goals rfl

theorem atot9288 : totK PD2M8K2 D2M8K2.u9288 = [68188677921, 538416327878, 825860078033, 341450270695, 28232996955, 0, 0, 0] := by
  rw [show D2M8K2.u9288 = KTree.node D2M8K2.t9294 (nat_lit 20078133) (nat_lit 1049723481) (nat_lit 0) D2M8K2.t9295 from rfl, totK_node, tot9294, tot9295]
  decide +kernel

theorem arows9292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9292 = true := by
  rw [show D2M8K2.u9292 = KTree.node D2M8K2.t9296 (nat_lit 20079424) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t9297 from rfl, allE_node, rows9296, irow9292, rows9297]
  all_goals rfl

theorem atot9292 : totK PD2M8K2 D2M8K2.u9292 = [210263972963, 652632402135, 684746004196, 241795854751, 9177971211, 0, 0, 0] := by
  rw [show D2M8K2.u9292 = KTree.node D2M8K2.t9296 (nat_lit 20079424) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t9297 from rfl, totK_node, tot9296, tot9297]
  decide +kernel

theorem arows9293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9293 = true := by
  rw [show D2M8K2.u9293 = KTree.node D2M8K2.t9298 (nat_lit 20080868) (nat_lit 2812030205) (nat_lit 0) D2M8K2.t9299 from rfl, allE_node, rows9298, irow9293, rows9299]
  all_goals rfl

theorem atot9293 : totK PD2M8K2 D2M8K2.u9293 = [186600705548, 761265776641, 712965808124, 115217720677, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u9293 = KTree.node D2M8K2.t9298 (nat_lit 20080868) (nat_lit 2812030205) (nat_lit 0) D2M8K2.t9299 from rfl, totK_node, tot9298, tot9299]
  decide +kernel

theorem arows9295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9295 = true := by
  rw [show D2M8K2.u9295 = KTree.node D2M8K2.t9300 (nat_lit 20082885) (nat_lit 1497389091) (nat_lit 0) D2M8K2.t9301 from rfl, allE_node, rows9300, irow9295, rows9301]
  all_goals rfl

theorem atot9295 : totK PD2M8K2 D2M8K2.u9295 = [213053461267, 664232579630, 684214464957, 205417907824, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u9295 = KTree.node D2M8K2.t9300 (nat_lit 20082885) (nat_lit 1497389091) (nat_lit 0) D2M8K2.t9301 from rfl, totK_node, tot9300, tot9301]
  decide +kernel

theorem arows9296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9296 = true := by
  rw [show D2M8K2.u9296 = KTree.node D2M8K2.t9302 (nat_lit 20084348) (nat_lit 2833123069) (nat_lit 0) D2M8K2.t9303 from rfl, allE_node, rows9302, irow9296, rows9303]
  all_goals rfl

theorem atot9296 : totK PD2M8K2 D2M8K2.u9296 = [204783472139, 785899879933, 698371746869, 112387816354, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u9296 = KTree.node D2M8K2.t9302 (nat_lit 20084348) (nat_lit 2833123069) (nat_lit 0) D2M8K2.t9303 from rfl, totK_node, tot9302, tot9303]
  decide +kernel

theorem arows9299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9299 = true := by
  rw [show D2M8K2.u9299 = KTree.node D2M8K2.t9304 (nat_lit 20086069) (nat_lit 1236444522) (nat_lit 0) D2M8K2.t9305 from rfl, allE_node, rows9304, irow9299, rows9305]
  all_goals rfl

theorem atot9299 : totK PD2M8K2 D2M8K2.u9299 = [175967501358, 651219818480, 741651866432, 228606729106, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u9299 = KTree.node D2M8K2.t9304 (nat_lit 20086069) (nat_lit 1236444522) (nat_lit 0) D2M8K2.t9305 from rfl, totK_node, tot9304, tot9305]
  decide +kernel

theorem arows9300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9300 = true := by
  rw [show D2M8K2.u9300 = KTree.node D2M8K2.t9306 (nat_lit 20087410) (nat_lit 3158360380) (nat_lit 0) D2M8K2.t9307 from rfl, allE_node, rows9306, irow9300, rows9307]
  all_goals rfl

theorem atot9300 : totK PD2M8K2 D2M8K2.u9300 = [268360723582, 816257711590, 624862537011, 95276086456, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u9300 = KTree.node D2M8K2.t9306 (nat_lit 20087410) (nat_lit 3158360380) (nat_lit 0) D2M8K2.t9307 from rfl, totK_node, tot9306, tot9307]
  decide +kernel

theorem arows9302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9302 = true := by
  rw [show D2M8K2.u9302 = KTree.node D2M8K2.t9308 (nat_lit 20089327) (nat_lit 1738551702) (nat_lit 0) D2M8K2.t9309 from rfl, allE_node, rows9308, irow9302, rows9309]
  all_goals rfl

theorem atot9302 : totK PD2M8K2 D2M8K2.u9302 = [0, 486443559530, 999646302018, 304780831615, 11162872812, 0, 0, 0] := by
  rw [show D2M8K2.u9302 = KTree.node D2M8K2.t9308 (nat_lit 20089327) (nat_lit 1738551702) (nat_lit 0) D2M8K2.t9309 from rfl, totK_node, tot9308, tot9309]
  decide +kernel

theorem arows9303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9303 = true := by
  rw [show D2M8K2.u9303 = KTree.node D2M8K2.t9310 (nat_lit 20094631) (nat_lit 2329786395) (nat_lit 0) D2M8K2.t9311 from rfl, allE_node, rows9310, irow9303, rows9311]
  all_goals rfl

theorem atot9303 : totK PD2M8K2 D2M8K2.u9303 = [0, 237583927598, 797197765893, 600400324486, 78913786674, 1138244013, 0, 0] := by
  rw [show D2M8K2.u9303 = KTree.node D2M8K2.t9310 (nat_lit 20094631) (nat_lit 2329786395) (nat_lit 0) D2M8K2.t9311 from rfl, totK_node, tot9310, tot9311]
  decide +kernel

theorem arows9308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9308 = true := by
  rw [show D2M8K2.u9308 = KTree.node D2M8K2.t9312 (nat_lit 20097168) (nat_lit 2599347543) (nat_lit 0) D2M8K2.t9313 from rfl, allE_node, rows9312, irow9308, rows9313]
  all_goals rfl

theorem atot9308 : totK PD2M8K2 D2M8K2.u9308 = [0, 265013085908, 869355155503, 597460406919, 58956217067, 0, 0, 0] := by
  rw [show D2M8K2.u9308 = KTree.node D2M8K2.t9312 (nat_lit 20097168) (nat_lit 2599347543) (nat_lit 0) D2M8K2.t9313 from rfl, totK_node, tot9312, tot9313]
  decide +kernel

theorem arows9309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9309 = true := by
  rw [show D2M8K2.u9309 = KTree.node D2M8K2.t9314 (nat_lit 20100177) (nat_lit 1782170360) (nat_lit 0) D2M8K2.t9315 from rfl, allE_node, rows9314, irow9309, rows9315]
  all_goals rfl

theorem atot9309 : totK PD2M8K2 D2M8K2.u9309 = [0, 400153014355, 953687911450, 428039204322, 22198684068, 0, 0, 0] := by
  rw [show D2M8K2.u9309 = KTree.node D2M8K2.t9314 (nat_lit 20100177) (nat_lit 1782170360) (nat_lit 0) D2M8K2.t9315 from rfl, totK_node, tot9314, tot9315]
  decide +kernel

theorem arows9311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9311 = true := by
  rw [show D2M8K2.u9311 = KTree.node D2M8K2.t9316 (nat_lit 20101715) (nat_lit 2262774853) (nat_lit 0) D2M8K2.t9317 from rfl, allE_node, rows9316, irow9311, rows9317]
  all_goals rfl

theorem atot9311 : totK PD2M8K2 D2M8K2.u9311 = [0, 341486379143, 929309618013, 475353969831, 27192350259, 0, 0, 0] := by
  rw [show D2M8K2.u9311 = KTree.node D2M8K2.t9316 (nat_lit 20101715) (nat_lit 2262774853) (nat_lit 0) D2M8K2.t9317 from rfl, totK_node, tot9316, tot9317]
  decide +kernel

theorem arows9312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9312 = true := by
  rw [show D2M8K2.u9312 = KTree.node D2M8K2.t9318 (nat_lit 20105023) (nat_lit 2318557482) (nat_lit 0) D2M8K2.t9319 from rfl, allE_node, rows9318, irow9312, rows9319]
  all_goals rfl

theorem atot9312 : totK PD2M8K2 D2M8K2.u9312 = [0, 405397095857, 975988105725, 407423490668, 17529653952, 0, 0, 0] := by
  rw [show D2M8K2.u9312 = KTree.node D2M8K2.t9318 (nat_lit 20105023) (nat_lit 2318557482) (nat_lit 0) D2M8K2.t9319 from rfl, totK_node, tot9318, tot9319]
  decide +kernel

theorem arows9315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9315 = true := by
  rw [show D2M8K2.u9315 = KTree.node D2M8K2.t9320 (nat_lit 20108016) (nat_lit 3651817842) (nat_lit 0) D2M8K2.t9321 from rfl, allE_node, rows9320, irow9315, rows9321]
  all_goals rfl

theorem atot9315 : totK PD2M8K2 D2M8K2.u9315 = [0, 267065533544, 851094580851, 578110436881, 70815153426, 1095107716, 0, 0] := by
  rw [show D2M8K2.u9315 = KTree.node D2M8K2.t9320 (nat_lit 20108016) (nat_lit 3651817842) (nat_lit 0) D2M8K2.t9321 from rfl, totK_node, tot9320, tot9321]
  decide +kernel

theorem arows9316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9316 = true := by
  rw [show D2M8K2.u9316 = KTree.node D2M8K2.t9322 (nat_lit 20109971) (nat_lit 1548831139) (nat_lit 0) D2M8K2.t9323 from rfl, allE_node, rows9322, irow9316, rows9323]
  all_goals rfl

theorem atot9316 : totK PD2M8K2 D2M8K2.u9316 = [0, 176358628726, 719551008753, 720513173886, 154025112882, 3882006667, 0, 0] := by
  rw [show D2M8K2.u9316 = KTree.node D2M8K2.t9322 (nat_lit 20109971) (nat_lit 1548831139) (nat_lit 0) D2M8K2.t9323 from rfl, totK_node, tot9322, tot9323]
  decide +kernel

theorem arows9318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9318 = true := by
  rw [show D2M8K2.u9318 = KTree.node D2M8K2.t9324 (nat_lit 20156716) (nat_lit 3611050461) (nat_lit 0) D2M8K2.t9325 from rfl, allE_node, rows9324, irow9318, rows9325]
  all_goals rfl

theorem atot9318 : totK PD2M8K2 D2M8K2.u9318 = [0, 256016219470, 814464795301, 610306308959, 92541152107, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9318 = KTree.node D2M8K2.t9324 (nat_lit 20156716) (nat_lit 3611050461) (nat_lit 0) D2M8K2.t9325 from rfl, totK_node, tot9324, tot9325]
  decide +kernel

theorem arows9319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9319 = true := by
  rw [show D2M8K2.u9319 = KTree.node D2M8K2.t9326 (nat_lit 20158645) (nat_lit 1170635255) (nat_lit 0) D2M8K2.t9327 from rfl, allE_node, rows9326, irow9319, rows9327]
  all_goals rfl

theorem atot9319 : totK PD2M8K2 D2M8K2.u9319 = [0, 194114593336, 774031117445, 741179511132, 91192204845, 0, 0, 0] := by
  rw [show D2M8K2.u9319 = KTree.node D2M8K2.t9326 (nat_lit 20158645) (nat_lit 1170635255) (nat_lit 0) D2M8K2.t9327 from rfl, totK_node, tot9326, tot9327]
  decide +kernel

theorem arows9323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9323 = true := by
  rw [show D2M8K2.u9323 = KTree.node D2M8K2.t9328 (nat_lit 20163893) (nat_lit 1844231283) (nat_lit 0) D2M8K2.t9329 from rfl, allE_node, rows9328, irow9323, rows9329]
  all_goals rfl

theorem atot9323 : totK PD2M8K2 D2M8K2.u9323 = [0, 184969677711, 749471085016, 716567536838, 110592837210, 1164319620, 0, 0] := by
  rw [show D2M8K2.u9323 = KTree.node D2M8K2.t9328 (nat_lit 20163893) (nat_lit 1844231283) (nat_lit 0) D2M8K2.t9329 from rfl, totK_node, tot9328, tot9329]
  decide +kernel

theorem arows9324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9324 = true := by
  rw [show D2M8K2.u9324 = KTree.node D2M8K2.t9330 (nat_lit 20165857) (nat_lit 1503344942) (nat_lit 0) D2M8K2.t9331 from rfl, allE_node, rows9330, irow9324, rows9331]
  all_goals rfl

theorem atot9324 : totK PD2M8K2 D2M8K2.u9324 = [0, 247792638269, 710262368852, 632477698631, 178911375511, 11819130176, 0, 0] := by
  rw [show D2M8K2.u9324 = KTree.node D2M8K2.t9330 (nat_lit 20165857) (nat_lit 1503344942) (nat_lit 0) D2M8K2.t9331 from rfl, totK_node, tot9330, tot9331]
  decide +kernel

theorem arows9326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9326 = true := by
  rw [show D2M8K2.u9326 = KTree.node D2M8K2.t9332 (nat_lit 20167423) (nat_lit 2414965113) (nat_lit 0) D2M8K2.t9333 from rfl, allE_node, rows9332, irow9326, rows9333]
  all_goals rfl

theorem atot9326 : totK PD2M8K2 D2M8K2.u9326 = [0, 164659483850, 737562947812, 766159087441, 121678859442, 1198073392, 0, 0] := by
  rw [show D2M8K2.u9326 = KTree.node D2M8K2.t9332 (nat_lit 20167423) (nat_lit 2414965113) (nat_lit 0) D2M8K2.t9333 from rfl, totK_node, tot9332, tot9333]
  decide +kernel

theorem arows9327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9327 = true := by
  rw [show D2M8K2.u9327 = KTree.node D2M8K2.t9334 (nat_lit 20169300) (nat_lit 3252523553) (nat_lit 0) D2M8K2.t9335 from rfl, allE_node, rows9334, irow9327, rows9335]
  all_goals rfl

theorem atot9327 : totK PD2M8K2 D2M8K2.u9327 = [0, 242162028248, 697343058784, 632668136814, 182104875700, 11986244008, 0, 0] := by
  rw [show D2M8K2.u9327 = KTree.node D2M8K2.t9334 (nat_lit 20169300) (nat_lit 3252523553) (nat_lit 0) D2M8K2.t9335 from rfl, totK_node, tot9334, tot9335]
  decide +kernel

theorem arows9330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9330 = true := by
  rw [show D2M8K2.u9330 = KTree.node D2M8K2.t9336 (nat_lit 20170522) (nat_lit 2679372284) (nat_lit 0) D2M8K2.t9337 from rfl, allE_node, rows9336, irow9330, rows9337]
  all_goals rfl

theorem atot9330 : totK PD2M8K2 D2M8K2.u9330 = [0, 177086745037, 759633747943, 734035776689, 106615072322, 1096505104, 0, 0] := by
  rw [show D2M8K2.u9330 = KTree.node D2M8K2.t9336 (nat_lit 20170522) (nat_lit 2679372284) (nat_lit 0) D2M8K2.t9337 from rfl, totK_node, tot9336, tot9337]
  decide +kernel

theorem arows9331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9331 = true := by
  rw [show D2M8K2.u9331 = KTree.node D2M8K2.t9338 (nat_lit 20172803) (nat_lit 2975440576) (nat_lit 0) D2M8K2.t9339 from rfl, allE_node, rows9338, irow9331, rows9339]
  all_goals rfl

theorem atot9331 : totK PD2M8K2 D2M8K2.u9331 = [0, 238008253914, 787800809485, 633011936357, 119669342320, 3884009855, 0, 0] := by
  rw [show D2M8K2.u9331 = KTree.node D2M8K2.t9338 (nat_lit 20172803) (nat_lit 2975440576) (nat_lit 0) D2M8K2.t9339 from rfl, totK_node, tot9338, tot9339]
  decide +kernel

theorem arows9333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9333 = true := by
  rw [show D2M8K2.u9333 = KTree.node D2M8K2.t9340 (nat_lit 20175029) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t9341 from rfl, allE_node, rows9340, irow9333, rows9341]
  all_goals rfl

theorem atot9333 : totK PD2M8K2 D2M8K2.u9333 = [0, 87591894987, 642984986731, 889019011354, 181207510430, 2638559756, 0, 0] := by
  rw [show D2M8K2.u9333 = KTree.node D2M8K2.t9340 (nat_lit 20175029) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t9341 from rfl, totK_node, tot9340, tot9341]
  decide +kernel

theorem arows9334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9334 = true := by
  rw [show D2M8K2.u9334 = KTree.node D2M8K2.t9342 (nat_lit 20177258) (nat_lit 2517614692) (nat_lit 0) D2M8K2.t9343 from rfl, allE_node, rows9342, irow9334, rows9343]
  all_goals rfl

theorem atot9334 : totK PD2M8K2 D2M8K2.u9334 = [0, 0, 330676661292, 924208482585, 434804707864, 27641507988, 0, 0] := by
  rw [show D2M8K2.u9334 = KTree.node D2M8K2.t9342 (nat_lit 20177258) (nat_lit 2517614692) (nat_lit 0) D2M8K2.t9343 from rfl, totK_node, tot9342, tot9343]
  decide +kernel

theorem arows9341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9341 = true := by
  rw [show D2M8K2.u9341 = KTree.node D2M8K2.t9344 (nat_lit 20179354) (nat_lit 3987642373) (nat_lit 0) D2M8K2.t9345 from rfl, allE_node, rows9344, irow9341, rows9345]
  all_goals rfl

theorem atot9341 : totK PD2M8K2 D2M8K2.u9341 = [0, 0, 226761684884, 810394018407, 589071283771, 81768975580, 1209030869, 0] := by
  rw [show D2M8K2.u9341 = KTree.node D2M8K2.t9344 (nat_lit 20179354) (nat_lit 3987642373) (nat_lit 0) D2M8K2.t9345 from rfl, totK_node, tot9344, tot9345]
  decide +kernel

theorem arows9342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9342 = true := by
  rw [show D2M8K2.u9342 = KTree.node D2M8K2.t9346 (nat_lit 20186621) (nat_lit 1651565824) (nat_lit 0) D2M8K2.t9347 from rfl, allE_node, rows9346, irow9342, rows9347]
  all_goals rfl

theorem atot9342 : totK PD2M8K2 D2M8K2.u9342 = [0, 0, 427212336963, 952098613263, 359251924439, 20863554415, 0, 0] := by
  rw [show D2M8K2.u9342 = KTree.node D2M8K2.t9346 (nat_lit 20186621) (nat_lit 1651565824) (nat_lit 0) D2M8K2.t9347 from rfl, totK_node, tot9346, tot9347]
  decide +kernel

theorem arows9344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9344 = true := by
  rw [show D2M8K2.u9344 = KTree.node D2M8K2.t9348 (nat_lit 20190222) (nat_lit 3315557244) (nat_lit 0) D2M8K2.t9349 from rfl, allE_node, rows9348, irow9344, rows9349]
  all_goals rfl

theorem atot9344 : totK PD2M8K2 D2M8K2.u9344 = [0, 0, 419615676527, 951823537157, 357444654188, 14807884811, 0, 0] := by
  rw [show D2M8K2.u9344 = KTree.node D2M8K2.t9348 (nat_lit 20190222) (nat_lit 3315557244) (nat_lit 0) D2M8K2.t9349 from rfl, totK_node, tot9348, tot9349]
  decide +kernel

theorem arows9345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9345 = true := by
  rw [show D2M8K2.u9345 = KTree.node D2M8K2.t9350 (nat_lit 20193535) (nat_lit 2256255126) (nat_lit 0) D2M8K2.t9351 from rfl, allE_node, rows9350, irow9345, rows9351]
  all_goals rfl

theorem atot9345 : totK PD2M8K2 D2M8K2.u9345 = [0, 41386975132, 507222132969, 921587111531, 304157376988, 13667190079, 0, 0] := by
  rw [show D2M8K2.u9345 = KTree.node D2M8K2.t9350 (nat_lit 20193535) (nat_lit 2256255126) (nat_lit 0) D2M8K2.t9351 from rfl, totK_node, tot9350, tot9351]
  decide +kernel

theorem arows9348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9348 = true := by
  rw [show D2M8K2.u9348 = KTree.node D2M8K2.t9352 (nat_lit 20201227) (nat_lit 1815681041) (nat_lit 0) D2M8K2.t9353 from rfl, allE_node, rows9352, irow9348, rows9353]
  all_goals rfl

theorem atot9348 : totK PD2M8K2 D2M8K2.u9348 = [0, 366072863152, 929852049325, 503032225665, 39491382953, 0, 0, 0] := by
  rw [show D2M8K2.u9348 = KTree.node D2M8K2.t9352 (nat_lit 20201227) (nat_lit 1815681041) (nat_lit 0) D2M8K2.t9353 from rfl, totK_node, tot9352, tot9353]
  decide +kernel

theorem arows9349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9349 = true := by
  rw [show D2M8K2.u9349 = KTree.node D2M8K2.t9354 (nat_lit 20202675) (nat_lit 3681445855) (nat_lit 0) D2M8K2.t9355 from rfl, allE_node, rows9354, irow9349, rows9355]
  all_goals rfl

theorem atot9349 : totK PD2M8K2 D2M8K2.u9349 = [0, 30291347117, 474837134894, 893430481180, 387619057257, 29394892645, 0, 0] := by
  rw [show D2M8K2.u9349 = KTree.node D2M8K2.t9354 (nat_lit 20202675) (nat_lit 3681445855) (nat_lit 0) D2M8K2.t9355 from rfl, totK_node, tot9354, tot9355]
  decide +kernel

theorem arows9351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9351 = true := by
  rw [show D2M8K2.u9351 = KTree.node D2M8K2.t9356 (nat_lit 20204106) (nat_lit 3724245652) (nat_lit 0) D2M8K2.t9357 from rfl, allE_node, rows9356, irow9351, rows9357]
  all_goals rfl

theorem atot9351 : totK PD2M8K2 D2M8K2.u9351 = [0, 234454937067, 694889735080, 663427735608, 204141250737, 8104085798, 0, 0] := by
  rw [show D2M8K2.u9351 = KTree.node D2M8K2.t9356 (nat_lit 20204106) (nat_lit 3724245652) (nat_lit 0) D2M8K2.t9357 from rfl, totK_node, tot9356, tot9357]
  decide +kernel

theorem arows9352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9352 = true := by
  rw [show D2M8K2.u9352 = KTree.node D2M8K2.t9358 (nat_lit 20205819) (nat_lit 3785722185) (nat_lit 0) D2M8K2.t9359 from rfl, allE_node, rows9358, irow9352, rows9359]
  all_goals rfl

theorem atot9352 : totK PD2M8K2 D2M8K2.u9352 = [0, 149029353690, 706285366416, 774007558013, 167703316834, 8417083954, 0, 0] := by
  rw [show D2M8K2.u9352 = KTree.node D2M8K2.t9358 (nat_lit 20205819) (nat_lit 3785722185) (nat_lit 0) D2M8K2.t9359 from rfl, totK_node, tot9358, tot9359]
  decide +kernel

theorem arows9356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9356 = true := by
  rw [show D2M8K2.u9356 = KTree.node D2M8K2.t9360 (nat_lit 20207693) (nat_lit 2113050302) (nat_lit 0) D2M8K2.t9361 from rfl, allE_node, rows9360, irow9356, rows9361]
  all_goals rfl

theorem atot9356 : totK PD2M8K2 D2M8K2.u9356 = [0, 335032528159, 822076632201, 559405983936, 108138702821, 3455941720, 0, 0] := by
  rw [show D2M8K2.u9356 = KTree.node D2M8K2.t9360 (nat_lit 20207693) (nat_lit 2113050302) (nat_lit 0) D2M8K2.t9361 from rfl, totK_node, tot9360, tot9361]
  decide +kernel

theorem arows9357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9357 = true := by
  rw [show D2M8K2.u9357 = KTree.node D2M8K2.t9362 (nat_lit 20209326) (nat_lit 4050905317) (nat_lit 0) D2M8K2.t9363 from rfl, allE_node, rows9362, irow9357, rows9363]
  all_goals rfl

theorem atot9357 : totK PD2M8K2 D2M8K2.u9357 = [0, 80559306243, 644677493519, 855791837124, 207926842336, 9473607896, 0, 0] := by
  rw [show D2M8K2.u9357 = KTree.node D2M8K2.t9362 (nat_lit 20209326) (nat_lit 4050905317) (nat_lit 0) D2M8K2.t9363 from rfl, totK_node, tot9362, tot9363]
  decide +kernel

theorem arows9359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9359 = true := by
  rw [show D2M8K2.u9359 = KTree.node D2M8K2.t9364 (nat_lit 20211164) (nat_lit 3584241870) (nat_lit 0) D2M8K2.t9365 from rfl, allE_node, rows9364, irow9359, rows9365]
  all_goals rfl

theorem atot9359 : totK PD2M8K2 D2M8K2.u9359 = [0, 329818465811, 856003298189, 533965373226, 83541681218, 2566665356, 0, 0] := by
  rw [show D2M8K2.u9359 = KTree.node D2M8K2.t9364 (nat_lit 20211164) (nat_lit 3584241870) (nat_lit 0) D2M8K2.t9365 from rfl, totK_node, tot9364, tot9365]
  decide +kernel

theorem arows9360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9360 = true := by
  rw [show D2M8K2.u9360 = KTree.node D2M8K2.t9366 (nat_lit 20212783) (nat_lit 2417420896) (nat_lit 0) D2M8K2.t9367 from rfl, allE_node, rows9366, irow9360, rows9367]
  all_goals rfl

theorem atot9360 : totK PD2M8K2 D2M8K2.u9360 = [0, 91681601894, 719646177901, 868708062434, 131095619769, 1067382613, 0, 0] := by
  rw [show D2M8K2.u9360 = KTree.node D2M8K2.t9366 (nat_lit 20212783) (nat_lit 2417420896) (nat_lit 0) D2M8K2.t9367 from rfl, totK_node, tot9366, tot9367]
  decide +kernel

theorem arows9363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9363 = true := by
  rw [show D2M8K2.u9363 = KTree.node D2M8K2.t9368 (nat_lit 20214989) (nat_lit 2002711666) (nat_lit 0) D2M8K2.t9369 from rfl, allE_node, rows9368, irow9363, rows9369]
  all_goals rfl

theorem atot9363 : totK PD2M8K2 D2M8K2.u9363 = [0, 332435806547, 870531018777, 561121097759, 87372259152, 2813333534, 0, 0] := by
  rw [show D2M8K2.u9363 = KTree.node D2M8K2.t9368 (nat_lit 20214989) (nat_lit 2002711666) (nat_lit 0) D2M8K2.t9369 from rfl, totK_node, tot9368, tot9369]
  decide +kernel

theorem arows9364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9364 = true := by
  rw [show D2M8K2.u9364 = KTree.node D2M8K2.t9370 (nat_lit 20217010) (nat_lit 4101123793) (nat_lit 0) D2M8K2.t9371 from rfl, allE_node, rows9370, irow9364, rows9371]
  all_goals rfl

theorem atot9364 : totK PD2M8K2 D2M8K2.u9364 = [0, 121847340634, 578282570299, 820512524658, 267453623690, 9730542555, 0, 0] := by
  rw [show D2M8K2.u9364 = KTree.node D2M8K2.t9370 (nat_lit 20217010) (nat_lit 4101123793) (nat_lit 0) D2M8K2.t9371 from rfl, totK_node, tot9370, tot9371]
  decide +kernel

theorem arows9366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9366 = true := by
  rw [show D2M8K2.u9366 = KTree.node D2M8K2.t9372 (nat_lit 20239582) (nat_lit 1825942117) (nat_lit 0) D2M8K2.t9373 from rfl, allE_node, rows9372, irow9366, rows9373]
  all_goals rfl

theorem atot9366 : totK PD2M8K2 D2M8K2.u9366 = [0, 272312776917, 823980069106, 573575643129, 80600461835, 1310166938, 0, 0] := by
  rw [show D2M8K2.u9366 = KTree.node D2M8K2.t9372 (nat_lit 20239582) (nat_lit 1825942117) (nat_lit 0) D2M8K2.t9373 from rfl, totK_node, tot9372, tot9373]
  decide +kernel

theorem arows9367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9367 = true := by
  rw [show D2M8K2.u9367 = KTree.node D2M8K2.t9374 (nat_lit 20242113) (nat_lit 1828015520) (nat_lit 0) D2M8K2.t9375 from rfl, allE_node, rows9374, irow9367, rows9375]
  all_goals rfl

theorem atot9367 : totK PD2M8K2 D2M8K2.u9367 = [0, 180494141897, 755460275963, 776613452095, 97543081918, 0, 0, 0] := by
  rw [show D2M8K2.u9367 = KTree.node D2M8K2.t9374 (nat_lit 20242113) (nat_lit 1828015520) (nat_lit 0) D2M8K2.t9375 from rfl, totK_node, tot9374, tot9375]
  decide +kernel

theorem arows9372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9372 = true := by
  rw [show D2M8K2.u9372 = KTree.node D2M8K2.t9376 (nat_lit 20243325) (nat_lit 931999376) (nat_lit 0) D2M8K2.t9377 from rfl, allE_node, rows9376, irow9372, rows9377]
  all_goals rfl

theorem atot9372 : totK PD2M8K2 D2M8K2.u9372 = [0, 226128852207, 775299423773, 670310132044, 162960087256, 9631076594, 0, 0] := by
  rw [show D2M8K2.u9372 = KTree.node D2M8K2.t9376 (nat_lit 20243325) (nat_lit 931999376) (nat_lit 0) D2M8K2.t9377 from rfl, totK_node, tot9376, tot9377]
  decide +kernel

theorem arows9373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9373 = true := by
  rw [show D2M8K2.u9373 = KTree.node D2M8K2.t9378 (nat_lit 20245080) (nat_lit 2893857451) (nat_lit 0) D2M8K2.t9379 from rfl, allE_node, rows9378, irow9373, rows9379]
  all_goals rfl

theorem atot9373 : totK PD2M8K2 D2M8K2.u9373 = [0, 171915411504, 662380431567, 757564991168, 216763121577, 5382912678, 0, 0] := by
  rw [show D2M8K2.u9373 = KTree.node D2M8K2.t9378 (nat_lit 20245080) (nat_lit 2893857451) (nat_lit 0) D2M8K2.t9379 from rfl, totK_node, tot9378, tot9379]
  decide +kernel

theorem arows9375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9375 = true := by
  rw [show D2M8K2.u9375 = KTree.node D2M8K2.t9380 (nat_lit 20246694) (nat_lit 2557931941) (nat_lit 0) D2M8K2.t9381 from rfl, allE_node, rows9380, irow9375, rows9381]
  all_goals rfl

theorem atot9375 : totK PD2M8K2 D2M8K2.u9375 = [0, 253241544056, 795319711472, 645888355886, 103024488297, 1164319620, 0, 0] := by
  rw [show D2M8K2.u9375 = KTree.node D2M8K2.t9380 (nat_lit 20246694) (nat_lit 2557931941) (nat_lit 0) D2M8K2.t9381 from rfl, totK_node, tot9380, tot9381]
  decide +kernel

theorem arows9376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9376 = true := by
  rw [show D2M8K2.u9376 = KTree.node D2M8K2.t9382 (nat_lit 20248388) (nat_lit 3306750981) (nat_lit 0) D2M8K2.t9383 from rfl, allE_node, rows9382, irow9376, rows9383]
  all_goals rfl

theorem atot9376 : totK PD2M8K2 D2M8K2.u9376 = [0, 170510339919, 640021006271, 738119620855, 218495659773, 11885407614, 0, 0] := by
  rw [show D2M8K2.u9376 = KTree.node D2M8K2.t9382 (nat_lit 20248388) (nat_lit 3306750981) (nat_lit 0) D2M8K2.t9383 from rfl, totK_node, tot9382, tot9383]
  decide +kernel

theorem arows9379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9379 = true := by
  rw [show D2M8K2.u9379 = KTree.node D2M8K2.t9384 (nat_lit 20253250) (nat_lit 2870535401) (nat_lit 0) D2M8K2.t9385 from rfl, allE_node, rows9384, irow9379, rows9385]
  all_goals rfl

theorem atot9379 : totK PD2M8K2 D2M8K2.u9379 = [0, 251244475206, 800043714224, 640246072587, 90899790030, 1096505104, 0, 0] := by
  rw [show D2M8K2.u9379 = KTree.node D2M8K2.t9384 (nat_lit 20253250) (nat_lit 2870535401) (nat_lit 0) D2M8K2.t9385 from rfl, totK_node, tot9384, tot9385]
  decide +kernel

theorem arows9380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9380 = true := by
  rw [show D2M8K2.u9380 = KTree.node D2M8K2.t9386 (nat_lit 20255197) (nat_lit 1069412848) (nat_lit 0) D2M8K2.t9387 from rfl, allE_node, rows9386, irow9380, rows9387]
  all_goals rfl

theorem atot9380 : totK PD2M8K2 D2M8K2.u9380 = [0, 164629600731, 706139974364, 755231366622, 147337443094, 3884009855, 0, 0] := by
  rw [show D2M8K2.u9380 = KTree.node D2M8K2.t9386 (nat_lit 20255197) (nat_lit 1069412848) (nat_lit 0) D2M8K2.t9387 from rfl, totK_node, tot9386, tot9387]
  decide +kernel

theorem arows9382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9382 = true := by
  rw [show D2M8K2.u9382 = KTree.node D2M8K2.t9388 (nat_lit 20281294) (nat_lit 3883117768) (nat_lit 0) D2M8K2.t9389 from rfl, allE_node, rows9388, irow9382, rows9389]
  all_goals rfl

theorem atot9382 : totK PD2M8K2 D2M8K2.u9382 = [0, 241508090589, 793629530745, 643407561298, 98609134665, 1310517177, 0, 0] := by
  rw [show D2M8K2.u9382 = KTree.node D2M8K2.t9388 (nat_lit 20281294) (nat_lit 3883117768) (nat_lit 0) D2M8K2.t9389 from rfl, totK_node, tot9388, tot9389]
  decide +kernel

theorem arows9383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9383 = true := by
  rw [show D2M8K2.u9383 = KTree.node D2M8K2.t9390 (nat_lit 20283685) (nat_lit 986141456) (nat_lit 0) D2M8K2.t9391 from rfl, allE_node, rows9390, irow9383, rows9391]
  all_goals rfl

theorem atot9383 : totK PD2M8K2 D2M8K2.u9383 = [0, 250302857726, 826743685758, 697252048954, 72258630519, 0, 0, 0] := by
  rw [show D2M8K2.u9383 = KTree.node D2M8K2.t9390 (nat_lit 20283685) (nat_lit 986141456) (nat_lit 0) D2M8K2.t9391 from rfl, totK_node, tot9390, tot9391]
  decide +kernel

theorem arows9387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9387 = true := by
  rw [show D2M8K2.u9387 = KTree.node D2M8K2.t9392 (nat_lit 20284938) (nat_lit 3556981693) (nat_lit 0) D2M8K2.t9393 from rfl, allE_node, rows9392, irow9387, rows9393]
  all_goals rfl

theorem atot9387 : totK PD2M8K2 D2M8K2.u9387 = [0, 167799126264, 728974829952, 745952729878, 186204642697, 9654694938, 0, 0] := by
  rw [show D2M8K2.u9387 = KTree.node D2M8K2.t9392 (nat_lit 20284938) (nat_lit 3556981693) (nat_lit 0) D2M8K2.t9393 from rfl, totK_node, tot9392, tot9393]
  decide +kernel

theorem arows9388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9388 = true := by
  rw [show D2M8K2.u9388 = KTree.node D2M8K2.t9394 (nat_lit 20290241) (nat_lit 1920863894) (nat_lit 0) D2M8K2.t9395 from rfl, allE_node, rows9394, irow9388, rows9395]
  all_goals rfl

theorem atot9388 : totK PD2M8K2 D2M8K2.u9388 = [0, 211782397004, 685187628645, 712638568173, 206206658099, 5411637735, 0, 0] := by
  rw [show D2M8K2.u9388 = KTree.node D2M8K2.t9394 (nat_lit 20290241) (nat_lit 1920863894) (nat_lit 0) D2M8K2.t9395 from rfl, totK_node, tot9394, tot9395]
  decide +kernel

theorem arows9390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9390 = true := by
  rw [show D2M8K2.u9390 = KTree.node D2M8K2.t9396 (nat_lit 20291694) (nat_lit 4048482758) (nat_lit 0) D2M8K2.t9397 from rfl, allE_node, rows9396, irow9390, rows9397]
  all_goals rfl

theorem atot9390 : totK PD2M8K2 D2M8K2.u9390 = [0, 225136324433, 795562722248, 686864578913, 107054972436, 1178750802, 0, 0] := by
  rw [show D2M8K2.u9390 = KTree.node D2M8K2.t9396 (nat_lit 20291694) (nat_lit 4048482758) (nat_lit 0) D2M8K2.t9397 from rfl, totK_node, tot9396, tot9397]
  decide +kernel

theorem arows9391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9391 = true := by
  rw [show D2M8K2.u9391 = KTree.node D2M8K2.t9398 (nat_lit 20293374) (nat_lit 3909094427) (nat_lit 0) D2M8K2.t9399 from rfl, allE_node, rows9398, irow9391, rows9399]
  all_goals rfl

theorem atot9391 : totK PD2M8K2 D2M8K2.u9391 = [0, 171650470825, 652222699442, 726956416399, 224272567234, 11991925116, 0, 0] := by
  rw [show D2M8K2.u9391 = KTree.node D2M8K2.t9398 (nat_lit 20293374) (nat_lit 3909094427) (nat_lit 0) D2M8K2.t9399 from rfl, totK_node, tot9398, tot9399]
  decide +kernel

theorem arows9394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9394 = true := by
  rw [show D2M8K2.u9394 = KTree.node D2M8K2.t9400 (nat_lit 20294743) (nat_lit 2373521376) (nat_lit 0) D2M8K2.t9401 from rfl, allE_node, rows9400, irow9394, rows9401]
  all_goals rfl

theorem atot9394 : totK PD2M8K2 D2M8K2.u9394 = [0, 251047734758, 792936560684, 639962110562, 98075827573, 1096505104, 0, 0] := by
  rw [show D2M8K2.u9394 = KTree.node D2M8K2.t9400 (nat_lit 20294743) (nat_lit 2373521376) (nat_lit 0) D2M8K2.t9401 from rfl, totK_node, tot9400, tot9401]
  decide +kernel

theorem arows9395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9395 = true := by
  rw [show D2M8K2.u9395 = KTree.node D2M8K2.t9402 (nat_lit 20296686) (nat_lit 3521303846) (nat_lit 0) D2M8K2.t9403 from rfl, allE_node, rows9402, irow9395, rows9403]
  all_goals rfl

theorem atot9395 : totK PD2M8K2 D2M8K2.u9395 = [0, 166751405801, 720671878680, 779909157603, 148882960887, 3884009855, 0, 0] := by
  rw [show D2M8K2.u9395 = KTree.node D2M8K2.t9402 (nat_lit 20296686) (nat_lit 3521303846) (nat_lit 0) D2M8K2.t9403 from rfl, totK_node, tot9402, tot9403]
  decide +kernel

theorem arows9397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9397 = true := by
  rw [show D2M8K2.u9397 = KTree.node D2M8K2.t9404 (nat_lit 20298797) (nat_lit 2075955808) (nat_lit 0) D2M8K2.t9405 from rfl, allE_node, rows9404, irow9397, rows9405]
  all_goals rfl

theorem atot9397 : totK PD2M8K2 D2M8K2.u9397 = [0, 178217708811, 727000783577, 773117114365, 138797972503, 1210106048, 0, 0] := by
  rw [show D2M8K2.u9397 = KTree.node D2M8K2.t9404 (nat_lit 20298797) (nat_lit 2075955808) (nat_lit 0) D2M8K2.t9405 from rfl, totK_node, tot9404, tot9405]
  decide +kernel

theorem arows9398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9398 = true := by
  rw [show D2M8K2.u9398 = KTree.node D2M8K2.t9406 (nat_lit 20321918) (nat_lit 3640333723) (nat_lit 0) D2M8K2.t9407 from rfl, allE_node, rows9406, irow9398, rows9407]
  all_goals rfl

theorem atot9398 : totK PD2M8K2 D2M8K2.u9398 = [0, 320219971768, 829666320903, 531828348994, 92590651409, 3724448267, 0, 0] := by
  rw [show D2M8K2.u9398 = KTree.node D2M8K2.t9406 (nat_lit 20321918) (nat_lit 3640333723) (nat_lit 0) D2M8K2.t9407 from rfl, totK_node, tot9406, tot9407]
  decide +kernel

theorem arows9404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9404 = true := by
  rw [show D2M8K2.u9404 = KTree.node D2M8K2.t9408 (nat_lit 20323208) (nat_lit 3293610972) (nat_lit 0) D2M8K2.t9409 from rfl, allE_node, rows9408, irow9404, rows9409]
  all_goals rfl

theorem atot9404 : totK PD2M8K2 D2M8K2.u9404 = [0, 89929757808, 687499530760, 836784287429, 126670237870, 1326647619, 0, 0] := by
  rw [show D2M8K2.u9404 = KTree.node D2M8K2.t9408 (nat_lit 20323208) (nat_lit 3293610972) (nat_lit 0) D2M8K2.t9409 from rfl, totK_node, tot9408, tot9409]
  decide +kernel

theorem arows9405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9405 = true := by
  rw [show D2M8K2.u9405 = KTree.node D2M8K2.t9410 (nat_lit 20325520) (nat_lit 3686841180) (nat_lit 0) D2M8K2.t9411 from rfl, allE_node, rows9410, irow9405, rows9411]
  all_goals rfl

theorem atot9405 : totK PD2M8K2 D2M8K2.u9405 = [0, 353780517344, 913856796996, 509943194795, 42904960054, 0, 0, 0] := by
  rw [show D2M8K2.u9405 = KTree.node D2M8K2.t9410 (nat_lit 20325520) (nat_lit 3686841180) (nat_lit 0) D2M8K2.t9411 from rfl, totK_node, tot9410, tot9411]
  decide +kernel

theorem arows9407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9407 = true := by
  rw [show D2M8K2.u9407 = KTree.node D2M8K2.t9412 (nat_lit 20327068) (nat_lit 3962582701) (nat_lit 0) D2M8K2.t9413 from rfl, allE_node, rows9412, irow9407, rows9413]
  all_goals rfl

theorem atot9407 : totK PD2M8K2 D2M8K2.u9407 = [0, 67979873137, 500436818256, 864132889362, 339205106480, 22301562661, 0, 0] := by
  rw [show D2M8K2.u9407 = KTree.node D2M8K2.t9412 (nat_lit 20327068) (nat_lit 3962582701) (nat_lit 0) D2M8K2.t9413 from rfl, totK_node, tot9412, tot9413]
  decide +kernel

theorem arows9408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9408 = true := by
  rw [show D2M8K2.u9408 = KTree.node D2M8K2.t9414 (nat_lit 20328536) (nat_lit 3733415574) (nat_lit 0) D2M8K2.t9415 from rfl, allE_node, rows9414, irow9408, rows9415]
  all_goals rfl

theorem atot9408 : totK PD2M8K2 D2M8K2.u9408 = [0, 277057140738, 783250607447, 614656132425, 118041163337, 1409560813, 0, 0] := by
  rw [show D2M8K2.u9408 = KTree.node D2M8K2.t9414 (nat_lit 20328536) (nat_lit 3733415574) (nat_lit 0) D2M8K2.t9415 from rfl, totK_node, tot9414, tot9415]
  decide +kernel

theorem arows9411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9411 = true := by
  rw [show D2M8K2.u9411 = KTree.node D2M8K2.t9416 (nat_lit 20330080) (nat_lit 2675009113) (nat_lit 0) D2M8K2.t9417 from rfl, allE_node, rows9416, irow9411, rows9417]
  all_goals rfl

theorem atot9411 : totK PD2M8K2 D2M8K2.u9411 = [0, 122444337579, 645978326394, 792753265360, 188449913453, 9447251962, 0, 0] := by
  rw [show D2M8K2.u9411 = KTree.node D2M8K2.t9416 (nat_lit 20330080) (nat_lit 2675009113) (nat_lit 0) D2M8K2.t9417 from rfl, totK_node, tot9416, tot9417]
  decide +kernel

theorem arows9412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9412 = true := by
  rw [show D2M8K2.u9412 = KTree.node D2M8K2.t9418 (nat_lit 20332010) (nat_lit 4129241511) (nat_lit 0) D2M8K2.t9419 from rfl, allE_node, rows9418, irow9412, rows9419]
  all_goals rfl

theorem atot9412 : totK PD2M8K2 D2M8K2.u9412 = [0, 296217113521, 793282549223, 590443069495, 107840712556, 3462014130, 0, 0] := by
  rw [show D2M8K2.u9412 = KTree.node D2M8K2.t9418 (nat_lit 20332010) (nat_lit 4129241511) (nat_lit 0) D2M8K2.t9419 from rfl, totK_node, tot9418, tot9419]
  decide +kernel

theorem arows9414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9414 = true := by
  rw [show D2M8K2.u9414 = KTree.node D2M8K2.t9420 (nat_lit 20333509) (nat_lit 1244491315) (nat_lit 0) D2M8K2.t9421 from rfl, allE_node, rows9420, irow9414, rows9421]
  all_goals rfl

theorem atot9414 : totK PD2M8K2 D2M8K2.u9414 = [0, 123825068022, 656925849434, 795590522240, 191430182624, 9528124131, 0, 0] := by
  rw [show D2M8K2.u9414 = KTree.node D2M8K2.t9420 (nat_lit 20333509) (nat_lit 1244491315) (nat_lit 0) D2M8K2.t9421 from rfl, totK_node, tot9420, tot9421]
  decide +kernel

theorem arows9415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9415 = true := by
  rw [show D2M8K2.u9415 = KTree.node D2M8K2.t9422 (nat_lit 20335418) (nat_lit 4283784232) (nat_lit 0) D2M8K2.t9423 from rfl, allE_node, rows9422, irow9415, rows9423]
  all_goals rfl

theorem atot9415 : totK PD2M8K2 D2M8K2.u9415 = [0, 262726613740, 781658687874, 639391959585, 120476511744, 3581949829, 0, 0] := by
  rw [show D2M8K2.u9415 = KTree.node D2M8K2.t9422 (nat_lit 20335418) (nat_lit 4283784232) (nat_lit 0) D2M8K2.t9423 from rfl, totK_node, tot9422, tot9423]
  decide +kernel

theorem arows9419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9419 = true := by
  rw [show D2M8K2.u9419 = KTree.node D2M8K2.t9424 (nat_lit 20336842) (nat_lit 3552527579) (nat_lit 0) D2M8K2.t9425 from rfl, allE_node, rows9424, irow9419, rows9425]
  all_goals rfl

theorem atot9419 : totK PD2M8K2 D2M8K2.u9419 = [0, 180758428870, 765710026433, 757017867781, 114439411757, 1096505104, 0, 0] := by
  rw [show D2M8K2.u9419 = KTree.node D2M8K2.t9424 (nat_lit 20336842) (nat_lit 3552527579) (nat_lit 0) D2M8K2.t9425 from rfl, totK_node, tot9424, tot9425]
  decide +kernel

theorem arows9420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9420 = true := by
  rw [show D2M8K2.u9420 = KTree.node D2M8K2.t9426 (nat_lit 20342243) (nat_lit 1671144555) (nat_lit 0) D2M8K2.t9427 from rfl, allE_node, rows9426, irow9420, rows9427]
  all_goals rfl

theorem atot9420 : totK PD2M8K2 D2M8K2.u9420 = [0, 0, 405147357847, 947586337720, 366918149179, 21934142517, 0, 0] := by
  rw [show D2M8K2.u9420 = KTree.node D2M8K2.t9426 (nat_lit 20342243) (nat_lit 1671144555) (nat_lit 0) D2M8K2.t9427 from rfl, totK_node, tot9426, tot9427]
  decide +kernel

theorem arows9422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9422 = true := by
  rw [show D2M8K2.u9422 = KTree.node D2M8K2.t9428 (nat_lit 20343877) (nat_lit 1296282855) (nat_lit 0) D2M8K2.t9429 from rfl, allE_node, rows9428, irow9422, rows9429]
  all_goals rfl

theorem atot9422 : totK PD2M8K2 D2M8K2.u9422 = [0, 0, 158607148675, 775547084513, 663340178323, 92364758340, 1138244013, 0] := by
  rw [show D2M8K2.u9422 = KTree.node D2M8K2.t9428 (nat_lit 20343877) (nat_lit 1296282855) (nat_lit 0) D2M8K2.t9429 from rfl, totK_node, tot9428, tot9429]
  decide +kernel

theorem arows9423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9423 = true := by
  rw [show D2M8K2.u9423 = KTree.node D2M8K2.t9430 (nat_lit 20346374) (nat_lit 4150701349) (nat_lit 0) D2M8K2.t9431 from rfl, allE_node, rows9430, irow9423, rows9431]
  all_goals rfl

theorem atot9423 : totK PD2M8K2 D2M8K2.u9423 = [0, 0, 399720627345, 953725632386, 409353901235, 26529010026, 0, 0] := by
  rw [show D2M8K2.u9423 = KTree.node D2M8K2.t9430 (nat_lit 20346374) (nat_lit 4150701349) (nat_lit 0) D2M8K2.t9431 from rfl, totK_node, tot9430, tot9431]
  decide +kernel

theorem arows9426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9426 = true := by
  rw [show D2M8K2.u9426 = KTree.node D2M8K2.t9432 (nat_lit 20349555) (nat_lit 3673020845) (nat_lit 0) D2M8K2.t9433 from rfl, allE_node, rows9432, irow9426, rows9433]
  all_goals rfl

theorem atot9426 : totK PD2M8K2 D2M8K2.u9426 = [0, 0, 390009816201, 944036094011, 394692806186, 23121697893, 0, 0] := by
  rw [show D2M8K2.u9426 = KTree.node D2M8K2.t9432 (nat_lit 20349555) (nat_lit 3673020845) (nat_lit 0) D2M8K2.t9433 from rfl, totK_node, tot9432, tot9433]
  decide +kernel

theorem arows9427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9427 = true := by
  rw [show D2M8K2.u9427 = KTree.node D2M8K2.t9434 (nat_lit 20353322) (nat_lit 4083786242) (nat_lit 0) D2M8K2.t9435 from rfl, allE_node, rows9434, irow9427, rows9435]
  all_goals rfl

theorem atot9427 : totK PD2M8K2 D2M8K2.u9427 = [0, 0, 395240929118, 953121450602, 396594319376, 23208737258, 0, 0] := by
  rw [show D2M8K2.u9427 = KTree.node D2M8K2.t9434 (nat_lit 20353322) (nat_lit 4083786242) (nat_lit 0) D2M8K2.t9435 from rfl, totK_node, tot9434, tot9435]
  decide +kernel

theorem arows9429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9429 = true := by
  rw [show D2M8K2.u9429 = KTree.node D2M8K2.t9436 (nat_lit 20356427) (nat_lit 2395842926) (nat_lit 0) D2M8K2.t9437 from rfl, allE_node, rows9436, irow9429, rows9437]
  all_goals rfl

theorem atot9429 : totK PD2M8K2 D2M8K2.u9429 = [0, 0, 392048547466, 928668144289, 426109040519, 32520285210, 0, 0] := by
  rw [show D2M8K2.u9429 = KTree.node D2M8K2.t9436 (nat_lit 20356427) (nat_lit 2395842926) (nat_lit 0) D2M8K2.t9437 from rfl, totK_node, tot9436, tot9437]
  decide +kernel

theorem arows9430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9430 = true := by
  rw [show D2M8K2.u9430 = KTree.node D2M8K2.t9438 (nat_lit 20357970) (nat_lit 3292813558) (nat_lit 0) D2M8K2.t9439 from rfl, allE_node, rows9438, irow9430, rows9439]
  all_goals rfl

theorem atot9430 : totK PD2M8K2 D2M8K2.u9430 = [18947402031, 14643827706, 55809825723, 613986445221, 834969978470, 191798525922, 4977114383, 0] := by
  rw [show D2M8K2.u9430 = KTree.node D2M8K2.t9438 (nat_lit 20357970) (nat_lit 3292813558) (nat_lit 0) D2M8K2.t9439 from rfl, totK_node, tot9438, tot9439]
  decide +kernel

theorem arows9435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9435 = true := by
  rw [show D2M8K2.u9435 = KTree.node D2M8K2.t9440 (nat_lit 20405162) (nat_lit 3806011842) (nat_lit 0) D2M8K2.t9441 from rfl, allE_node, rows9440, irow9435, rows9441]
  all_goals rfl

theorem atot9435 : totK PD2M8K2 D2M8K2.u9435 = [395112666646, 954106983031, 420172535635, 22386190152, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9435 = KTree.node D2M8K2.t9440 (nat_lit 20405162) (nat_lit 3806011842) (nat_lit 0) D2M8K2.t9441 from rfl, totK_node, tot9440, tot9441]
  decide +kernel

theorem arows9436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9436 = true := by
  rw [show D2M8K2.u9436 = KTree.node D2M8K2.t9442 (nat_lit 20406662) (nat_lit 3545152819) (nat_lit 0) D2M8K2.t9443 from rfl, allE_node, rows9442, irow9436, rows9443]
  all_goals rfl

theorem atot9436 : totK PD2M8K2 D2M8K2.u9436 = [94265873883, 665811250491, 887724401802, 156448824501, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u9436 = KTree.node D2M8K2.t9442 (nat_lit 20406662) (nat_lit 3545152819) (nat_lit 0) D2M8K2.t9443 from rfl, totK_node, tot9442, tot9443]
  decide +kernel

theorem arows9438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9438 = true := by
  rw [show D2M8K2.u9438 = KTree.node D2M8K2.t9444 (nat_lit 20411958) (nat_lit 1750014059) (nat_lit 0) D2M8K2.t9445 from rfl, allE_node, rows9444, irow9438, rows9445]
  all_goals rfl

theorem atot9438 : totK PD2M8K2 D2M8K2.u9438 = [306500640607, 902364474704, 542183447121, 46111752759, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9438 = KTree.node D2M8K2.t9444 (nat_lit 20411958) (nat_lit 1750014059) (nat_lit 0) D2M8K2.t9445 from rfl, totK_node, tot9444, tot9445]
  decide +kernel

theorem arows9439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9439 = true := by
  rw [show D2M8K2.u9439 = KTree.node D2M8K2.t9446 (nat_lit 20414017) (nat_lit 1544698628) (nat_lit 0) D2M8K2.t9447 from rfl, allE_node, rows9446, irow9439, rows9447]
  all_goals rfl

theorem atot9439 : totK PD2M8K2 D2M8K2.u9439 = [87204366028, 539877994620, 839595198986, 274722619141, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u9439 = KTree.node D2M8K2.t9446 (nat_lit 20414017) (nat_lit 1544698628) (nat_lit 0) D2M8K2.t9447 from rfl, totK_node, tot9446, tot9447]
  decide +kernel

theorem arows9442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9442 = true := by
  rw [show D2M8K2.u9442 = KTree.node D2M8K2.t9448 (nat_lit 20415755) (nat_lit 2527422866) (nat_lit 0) D2M8K2.t9449 from rfl, allE_node, rows9448, irow9442, rows9449]
  all_goals rfl

theorem atot9442 : totK PD2M8K2 D2M8K2.u9442 = [327282852593, 898709568795, 546590806820, 47556067181, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9442 = KTree.node D2M8K2.t9448 (nat_lit 20415755) (nat_lit 2527422866) (nat_lit 0) D2M8K2.t9449 from rfl, totK_node, tot9448, tot9449]
  decide +kernel

theorem arows9443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9443 = true := by
  rw [show D2M8K2.u9443 = KTree.node D2M8K2.t9450 (nat_lit 20417445) (nat_lit 1453953423) (nat_lit 0) D2M8K2.t9451 from rfl, allE_node, rows9450, irow9443, rows9451]
  all_goals rfl

theorem atot9443 : totK PD2M8K2 D2M8K2.u9443 = [86474097249, 515071314493, 861015591576, 298773784952, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u9443 = KTree.node D2M8K2.t9450 (nat_lit 20417445) (nat_lit 1453953423) (nat_lit 0) D2M8K2.t9451 from rfl, totK_node, tot9450, tot9451]
  decide +kernel

theorem arows9445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9445 = true := by
  rw [show D2M8K2.u9445 = KTree.node D2M8K2.t9452 (nat_lit 20419200) (nat_lit 3702502139) (nat_lit 0) D2M8K2.t9453 from rfl, allE_node, rows9452, irow9445, rows9453]
  all_goals rfl

theorem atot9445 : totK PD2M8K2 D2M8K2.u9445 = [237099868611, 812197469113, 636011547997, 85449001857, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u9445 = KTree.node D2M8K2.t9452 (nat_lit 20419200) (nat_lit 3702502139) (nat_lit 0) D2M8K2.t9453 from rfl, totK_node, tot9452, tot9453]
  decide +kernel

theorem arows9446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9446 = true := by
  rw [show D2M8K2.u9446 = KTree.node D2M8K2.t9454 (nat_lit 20421638) (nat_lit 3430668410) (nat_lit 0) D2M8K2.t9455 from rfl, allE_node, rows9454, irow9446, rows9455]
  all_goals rfl

theorem atot9446 : totK PD2M8K2 D2M8K2.u9446 = [245907326836, 762821367028, 651737371193, 133816520911, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u9446 = KTree.node D2M8K2.t9454 (nat_lit 20421638) (nat_lit 3430668410) (nat_lit 0) D2M8K2.t9455 from rfl, totK_node, tot9454, tot9455]
  decide +kernel

theorem arows9450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9450 = true := by
  rw [show D2M8K2.u9450 = KTree.node D2M8K2.t9456 (nat_lit 20423146) (nat_lit 3996530250) (nat_lit 0) D2M8K2.t9457 from rfl, allE_node, rows9456, irow9450, rows9457]
  all_goals rfl

theorem atot9450 : totK PD2M8K2 D2M8K2.u9450 = [179867083042, 733535718503, 748582192043, 140279952698, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u9450 = KTree.node D2M8K2.t9456 (nat_lit 20423146) (nat_lit 3996530250) (nat_lit 0) D2M8K2.t9457 from rfl, totK_node, tot9456, tot9457]
  decide +kernel

theorem arows9451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9451 = true := by
  rw [show D2M8K2.u9451 = KTree.node D2M8K2.t9458 (nat_lit 20424824) (nat_lit 2266040828) (nat_lit 0) D2M8K2.t9459 from rfl, allE_node, rows9458, irow9451, rows9459]
  all_goals rfl

theorem atot9451 : totK PD2M8K2 D2M8K2.u9451 = [0, 373706815944, 946724493899, 423563050867, 23302424837, 0, 0, 0] := by
  rw [show D2M8K2.u9451 = KTree.node D2M8K2.t9458 (nat_lit 20424824) (nat_lit 2266040828) (nat_lit 0) D2M8K2.t9459 from rfl, totK_node, tot9458, tot9459]
  decide +kernel

theorem arows9453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9453 = true := by
  rw [show D2M8K2.u9453 = KTree.node D2M8K2.t9460 (nat_lit 20426334) (nat_lit 3968912540) (nat_lit 0) D2M8K2.t9461 from rfl, allE_node, rows9460, irow9453, rows9461]
  all_goals rfl

theorem atot9453 : totK PD2M8K2 D2M8K2.u9453 = [0, 255671739963, 794110189981, 584686785284, 101325087707, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9453 = KTree.node D2M8K2.t9460 (nat_lit 20426334) (nat_lit 3968912540) (nat_lit 0) D2M8K2.t9461 from rfl, totK_node, tot9460, tot9461]
  decide +kernel

theorem arows9454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9454 = true := by
  rw [show D2M8K2.u9454 = KTree.node D2M8K2.t9462 (nat_lit 20431883) (nat_lit 2911071882) (nat_lit 0) D2M8K2.t9463 from rfl, allE_node, rows9462, irow9454, rows9463]
  all_goals rfl

theorem atot9454 : totK PD2M8K2 D2M8K2.u9454 = [0, 230026197459, 844755033433, 619541397364, 64787856383, 0, 0, 0] := by
  rw [show D2M8K2.u9454 = KTree.node D2M8K2.t9462 (nat_lit 20431883) (nat_lit 2911071882) (nat_lit 0) D2M8K2.t9463 from rfl, totK_node, tot9462, tot9463]
  decide +kernel

theorem arows9457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9457 = true := by
  rw [show D2M8K2.u9457 = KTree.node D2M8K2.t9464 (nat_lit 20433586) (nat_lit 4161564152) (nat_lit 0) D2M8K2.t9465 from rfl, allE_node, rows9464, irow9457, rows9465]
  all_goals rfl

theorem atot9457 : totK PD2M8K2 D2M8K2.u9457 = [0, 362657853126, 936407158044, 464939466357, 26547701453, 0, 0, 0] := by
  rw [show D2M8K2.u9457 = KTree.node D2M8K2.t9464 (nat_lit 20433586) (nat_lit 4161564152) (nat_lit 0) D2M8K2.t9465 from rfl, totK_node, tot9464, tot9465]
  decide +kernel

theorem arows9458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9458 = true := by
  rw [show D2M8K2.u9458 = KTree.node D2M8K2.t9466 (nat_lit 20436895) (nat_lit 2338675932) (nat_lit 0) D2M8K2.t9467 from rfl, allE_node, rows9466, irow9458, rows9467]
  all_goals rfl

theorem atot9458 : totK PD2M8K2 D2M8K2.u9458 = [0, 355083274382, 930266912065, 456208916674, 28397367937, 0, 0, 0] := by
  rw [show D2M8K2.u9458 = KTree.node D2M8K2.t9466 (nat_lit 20436895) (nat_lit 2338675932) (nat_lit 0) D2M8K2.t9467 from rfl, totK_node, tot9466, tot9467]
  decide +kernel

theorem arows9460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9460 = true := by
  rw [show D2M8K2.u9460 = KTree.node D2M8K2.t9468 (nat_lit 20442244) (nat_lit 3772546580) (nat_lit 0) D2M8K2.t9469 from rfl, allE_node, rows9468, irow9460, rows9469]
  all_goals rfl

theorem atot9460 : totK PD2M8K2 D2M8K2.u9460 = [0, 383307191471, 940734680871, 437893485221, 23253293539, 0, 0, 0] := by
  rw [show D2M8K2.u9460 = KTree.node D2M8K2.t9468 (nat_lit 20442244) (nat_lit 3772546580) (nat_lit 0) D2M8K2.t9469 from rfl, totK_node, tot9468, tot9469]
  decide +kernel

theorem arows9461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9461 = true := by
  rw [show D2M8K2.u9461 = KTree.node D2M8K2.t9470 (nat_lit 20443802) (nat_lit 4047264089) (nat_lit 0) D2M8K2.t9471 from rfl, allE_node, rows9470, irow9461, rows9471]
  all_goals rfl

theorem atot9461 : totK PD2M8K2 D2M8K2.u9461 = [145481999772, 520429269614, 783229055223, 352139844551, 21338389516, 0, 0, 0] := by
  rw [show D2M8K2.u9461 = KTree.node D2M8K2.t9470 (nat_lit 20443802) (nat_lit 4047264089) (nat_lit 0) D2M8K2.t9471 from rfl, totK_node, tot9470, tot9471]
  decide +kernel

theorem arows9469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9469 = true := by
  rw [show D2M8K2.u9469 = KTree.node D2M8K2.t9472 (nat_lit 20450388) (nat_lit 2725840564) (nat_lit 0) D2M8K2.t9473 from rfl, allE_node, rows9472, irow9469, rows9473]
  all_goals rfl

theorem atot9469 : totK PD2M8K2 D2M8K2.u9469 = [297411429584, 906421375044, 571031255391, 53841356478, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9469 = KTree.node D2M8K2.t9472 (nat_lit 20450388) (nat_lit 2725840564) (nat_lit 0) D2M8K2.t9473 from rfl, totK_node, tot9472, tot9473]
  decide +kernel

theorem arows9470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9470 = true := by
  rw [show D2M8K2.u9470 = KTree.node D2M8K2.t9474 (nat_lit 20451866) (nat_lit 4044067566) (nat_lit 0) D2M8K2.t9475 from rfl, allE_node, rows9474, irow9470, rows9475]
  all_goals rfl

theorem atot9470 : totK PD2M8K2 D2M8K2.u9470 = [0, 359013006829, 951364752040, 467021631987, 30804453458, 0, 0, 0] := by
  rw [show D2M8K2.u9470 = KTree.node D2M8K2.t9474 (nat_lit 20451866) (nat_lit 4044067566) (nat_lit 0) D2M8K2.t9475 from rfl, totK_node, tot9474, tot9475]
  decide +kernel

theorem arows9472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9472 = true := by
  rw [show D2M8K2.u9472 = KTree.node D2M8K2.t9476 (nat_lit 20453212) (nat_lit 3969568137) (nat_lit 0) D2M8K2.t9477 from rfl, allE_node, rows9476, irow9472, rows9477]
  all_goals rfl

theorem atot9472 : totK PD2M8K2 D2M8K2.u9472 = [369756759311, 876330658112, 471371720124, 100571331176, 6804944647, 0, 0, 0] := by
  rw [show D2M8K2.u9472 = KTree.node D2M8K2.t9476 (nat_lit 20453212) (nat_lit 3969568137) (nat_lit 0) D2M8K2.t9477 from rfl, totK_node, tot9476, tot9477]
  decide +kernel

theorem arows9473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9473 = true := by
  rw [show D2M8K2.u9473 = KTree.node D2M8K2.t9478 (nat_lit 20455010) (nat_lit 3997378488) (nat_lit 0) D2M8K2.t9479 from rfl, allE_node, rows9478, irow9473, rows9479]
  all_goals rfl

theorem atot9473 : totK PD2M8K2 D2M8K2.u9473 = [51798441585, 547592326771, 920103234367, 266178896822, 11886135539, 0, 0, 0] := by
  rw [show D2M8K2.u9473 = KTree.node D2M8K2.t9478 (nat_lit 20455010) (nat_lit 3997378488) (nat_lit 0) D2M8K2.t9479 from rfl, totK_node, tot9478, tot9479]
  decide +kernel

theorem arows9476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9476 = true := by
  rw [show D2M8K2.u9476 = KTree.node D2M8K2.t9480 (nat_lit 20457044) (nat_lit 3665217836) (nat_lit 0) D2M8K2.t9481 from rfl, allE_node, rows9480, irow9476, rows9481]
  all_goals rfl

theorem atot9476 : totK PD2M8K2 D2M8K2.u9476 = [381459287408, 946718009565, 476105795683, 35814949642, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9476 = KTree.node D2M8K2.t9480 (nat_lit 20457044) (nat_lit 3665217836) (nat_lit 0) D2M8K2.t9481 from rfl, totK_node, tot9480, tot9481]
  decide +kernel

theorem arows9477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9477 = true := by
  rw [show D2M8K2.u9477 = KTree.node D2M8K2.t9482 (nat_lit 20458755) (nat_lit 3615454077) (nat_lit 0) D2M8K2.t9483 from rfl, allE_node, rows9482, irow9477, rows9483]
  all_goals rfl

theorem atot9477 : totK PD2M8K2 D2M8K2.u9477 = [8186756758, 493025177024, 980624743656, 304354206431, 13204088881, 0, 0, 0] := by
  rw [show D2M8K2.u9477 = KTree.node D2M8K2.t9482 (nat_lit 20458755) (nat_lit 3615454077) (nat_lit 0) D2M8K2.t9483 from rfl, totK_node, tot9482, tot9483]
  decide +kernel

theorem arows9479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9479 = true := by
  rw [show D2M8K2.u9479 = KTree.node D2M8K2.t9484 (nat_lit 20460428) (nat_lit 3724550032) (nat_lit 0) D2M8K2.t9485 from rfl, allE_node, rows9484, irow9479, rows9485]
  all_goals rfl

theorem atot9479 : totK PD2M8K2 D2M8K2.u9479 = [321899280014, 902905488648, 564092078775, 59761653331, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9479 = KTree.node D2M8K2.t9484 (nat_lit 20460428) (nat_lit 3724550032) (nat_lit 0) D2M8K2.t9485 from rfl, totK_node, tot9484, tot9485]
  decide +kernel

theorem arows9480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9480 = true := by
  rw [show D2M8K2.u9480 = KTree.node D2M8K2.t9486 (nat_lit 20462980) (nat_lit 3724415699) (nat_lit 0) D2M8K2.t9487 from rfl, allE_node, rows9486, irow9480, rows9487]
  all_goals rfl

theorem atot9480 : totK PD2M8K2 D2M8K2.u9480 = [196514914588, 737952914610, 754164347082, 149853103106, 3869034280, 0, 0, 0] := by
  rw [show D2M8K2.u9480 = KTree.node D2M8K2.t9486 (nat_lit 20462980) (nat_lit 3724415699) (nat_lit 0) D2M8K2.t9487 from rfl, totK_node, tot9486, tot9487]
  decide +kernel

theorem arows9484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9484 = true := by
  rw [show D2M8K2.u9484 = KTree.node D2M8K2.t9488 (nat_lit 20464475) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t9489 from rfl, allE_node, rows9488, irow9484, rows9489]
  all_goals rfl

theorem atot9484 : totK PD2M8K2 D2M8K2.u9484 = [231056150071, 792873801559, 673056440353, 113048979176, 1267860612, 0, 0, 0] := by
  rw [show D2M8K2.u9484 = KTree.node D2M8K2.t9488 (nat_lit 20464475) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t9489 from rfl, totK_node, tot9488, tot9489]
  decide +kernel

theorem arows9485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9485 = true := by
  rw [show D2M8K2.u9485 = KTree.node D2M8K2.t9490 (nat_lit 20466179) (nat_lit 2904539451) (nat_lit 0) D2M8K2.t9491 from rfl, allE_node, rows9490, irow9485, rows9491]
  all_goals rfl

theorem atot9485 : totK PD2M8K2 D2M8K2.u9485 = [0, 358245529693, 914786547842, 479640121782, 39560655119, 0, 0, 0] := by
  rw [show D2M8K2.u9485 = KTree.node D2M8K2.t9490 (nat_lit 20466179) (nat_lit 2904539451) (nat_lit 0) D2M8K2.t9491 from rfl, totK_node, tot9490, tot9491]
  decide +kernel

theorem arows9487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9487 = true := by
  rw [show D2M8K2.u9487 = KTree.node D2M8K2.t9492 (nat_lit 20471070) (nat_lit 3869046296) (nat_lit 0) D2M8K2.t9493 from rfl, allE_node, rows9492, irow9487, rows9493]
  all_goals rfl

theorem atot9487 : totK PD2M8K2 D2M8K2.u9487 = [0, 347675481477, 927926697698, 516570745154, 39772003131, 0, 0, 0] := by
  rw [show D2M8K2.u9487 = KTree.node D2M8K2.t9492 (nat_lit 20471070) (nat_lit 3869046296) (nat_lit 0) D2M8K2.t9493 from rfl, totK_node, tot9492, tot9493]
  decide +kernel

theorem arows9488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9488 = true := by
  rw [show D2M8K2.u9488 = KTree.node D2M8K2.t9494 (nat_lit 20472552) (nat_lit 3200773567) (nat_lit 0) D2M8K2.t9495 from rfl, allE_node, rows9494, irow9488, rows9495]
  all_goals rfl

theorem atot9488 : totK PD2M8K2 D2M8K2.u9488 = [0, 0, 393883717430, 932648918891, 426468218835, 30397782892, 0, 0] := by
  rw [show D2M8K2.u9488 = KTree.node D2M8K2.t9494 (nat_lit 20472552) (nat_lit 3200773567) (nat_lit 0) D2M8K2.t9495 from rfl, totK_node, tot9494, tot9495]
  decide +kernel

theorem arows9491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9491 = true := by
  rw [show D2M8K2.u9491 = KTree.node D2M8K2.t9496 (nat_lit 20473900) (nat_lit 3833912465) (nat_lit 0) D2M8K2.t9497 from rfl, allE_node, rows9496, irow9491, rows9497]
  all_goals rfl

theorem atot9491 : totK PD2M8K2 D2M8K2.u9491 = [0, 335619510690, 818935889341, 523281987308, 122376651446, 6524090962, 0, 0] := by
  rw [show D2M8K2.u9491 = KTree.node D2M8K2.t9496 (nat_lit 20473900) (nat_lit 3833912465) (nat_lit 0) D2M8K2.t9497 from rfl, totK_node, tot9496, tot9497]
  decide +kernel

theorem arows9492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9492 = true := by
  rw [show D2M8K2.u9492 = KTree.node D2M8K2.t9498 (nat_lit 20475765) (nat_lit 1627280769) (nat_lit 0) D2M8K2.t9499 from rfl, allE_node, rows9498, irow9492, rows9499]
  all_goals rfl

theorem atot9492 : totK PD2M8K2 D2M8K2.u9492 = [0, 116745725324, 636165735515, 843557587821, 200901243081, 5159868635, 0, 0] := by
  rw [show D2M8K2.u9492 = KTree.node D2M8K2.t9498 (nat_lit 20475765) (nat_lit 1627280769) (nat_lit 0) D2M8K2.t9499 from rfl, totK_node, tot9498, tot9499]
  decide +kernel

theorem arows9494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9494 = true := by
  rw [show D2M8K2.u9494 = KTree.node D2M8K2.t9500 (nat_lit 20477818) (nat_lit 3681304543) (nat_lit 0) D2M8K2.t9501 from rfl, allE_node, rows9500, irow9494, rows9501]
  all_goals rfl

theorem atot9494 : totK PD2M8K2 D2M8K2.u9494 = [0, 348589735848, 938989961954, 507157934081, 36671863254, 0, 0, 0] := by
  rw [show D2M8K2.u9494 = KTree.node D2M8K2.t9500 (nat_lit 20477818) (nat_lit 3681304543) (nat_lit 0) D2M8K2.t9501 from rfl, totK_node, tot9500, tot9501]
  decide +kernel

theorem arows9495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9495 = true := by
  rw [show D2M8K2.u9495 = KTree.node D2M8K2.t9502 (nat_lit 20479666) (nat_lit 4008335566) (nat_lit 0) D2M8K2.t9503 from rfl, allE_node, rows9502, irow9495, rows9503]
  all_goals rfl

theorem atot9495 : totK PD2M8K2 D2M8K2.u9495 = [0, 89442567638, 616387059384, 873700123030, 224176733211, 5218872685, 0, 0] := by
  rw [show D2M8K2.u9495 = KTree.node D2M8K2.t9502 (nat_lit 20479666) (nat_lit 4008335566) (nat_lit 0) D2M8K2.t9503 from rfl, totK_node, tot9502, tot9503]
  decide +kernel

theorem arows9500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9500 = true := by
  rw [show D2M8K2.u9500 = KTree.node D2M8K2.t9504 (nat_lit 20481381) (nat_lit 1524177181) (nat_lit 0) D2M8K2.t9505 from rfl, allE_node, rows9504, irow9500, rows9505]
  all_goals rfl

theorem atot9500 : totK PD2M8K2 D2M8K2.u9500 = [0, 239764877979, 844908640658, 678843501093, 70380317201, 0, 0, 0] := by
  rw [show D2M8K2.u9500 = KTree.node D2M8K2.t9504 (nat_lit 20481381) (nat_lit 1524177181) (nat_lit 0) D2M8K2.t9505 from rfl, totK_node, tot9504, tot9505]
  decide +kernel

theorem arows9501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9501 = true := by
  rw [show D2M8K2.u9501 = KTree.node D2M8K2.t9506 (nat_lit 20484032) (nat_lit 3637259543) (nat_lit 0) D2M8K2.t9507 from rfl, allE_node, rows9506, irow9501, rows9507]
  all_goals rfl

theorem atot9501 : totK PD2M8K2 D2M8K2.u9501 = [0, 249854083152, 780583200240, 661685761923, 120357832710, 1415142070, 0, 0] := by
  rw [show D2M8K2.u9501 = KTree.node D2M8K2.t9506 (nat_lit 20484032) (nat_lit 3637259543) (nat_lit 0) D2M8K2.t9507 from rfl, totK_node, tot9506, tot9507]
  decide +kernel

theorem arows9503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9503 = true := by
  rw [show D2M8K2.u9503 = KTree.node D2M8K2.t9508 (nat_lit 20485440) (nat_lit 3736707029) (nat_lit 0) D2M8K2.t9509 from rfl, allE_node, rows9508, irow9503, rows9509]
  all_goals rfl

theorem atot9503 : totK PD2M8K2 D2M8K2.u9503 = [0, 175897128925, 763182491253, 739866208224, 130830304155, 1238673482, 0, 0] := by
  rw [show D2M8K2.u9503 = KTree.node D2M8K2.t9508 (nat_lit 20485440) (nat_lit 3736707029) (nat_lit 0) D2M8K2.t9509 from rfl, totK_node, tot9508, tot9509]
  decide +kernel

theorem arows9504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9504 = true := by
  rw [show D2M8K2.u9504 = KTree.node D2M8K2.t9510 (nat_lit 20487317) (nat_lit 2190013337) (nat_lit 0) D2M8K2.t9511 from rfl, allE_node, rows9510, irow9504, rows9511]
  all_goals rfl

theorem atot9504 : totK PD2M8K2 D2M8K2.u9504 = [242856659182, 600266090467, 390725975943, 361083511025, 161321392144, 8063697217, 0, 0] := by
  rw [show D2M8K2.u9504 = KTree.node D2M8K2.t9510 (nat_lit 20487317) (nat_lit 2190013337) (nat_lit 0) D2M8K2.t9511 from rfl, totK_node, tot9510, tot9511]
  decide +kernel

theorem arows9507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9507 = true := by
  rw [show D2M8K2.u9507 = KTree.node D2M8K2.t9512 (nat_lit 20488960) (nat_lit 3551995409) (nat_lit 0) D2M8K2.t9513 from rfl, allE_node, rows9512, irow9507, rows9513]
  all_goals rfl

theorem atot9507 : totK PD2M8K2 D2M8K2.u9507 = [153381683531, 715490739865, 767342799760, 137004750763, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u9507 = KTree.node D2M8K2.t9512 (nat_lit 20488960) (nat_lit 3551995409) (nat_lit 0) D2M8K2.t9513 from rfl, totK_node, tot9512, tot9513]
  decide +kernel

theorem arows9508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9508 = true := by
  rw [show D2M8K2.u9508 = KTree.node D2M8K2.t9514 (nat_lit 20491297) (nat_lit 1196845342) (nat_lit 0) D2M8K2.t9515 from rfl, allE_node, rows9514, irow9508, rows9515]
  all_goals rfl

theorem atot9508 : totK PD2M8K2 D2M8K2.u9508 = [319657831956, 894274748131, 576804188798, 56899281246, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9508 = KTree.node D2M8K2.t9514 (nat_lit 20491297) (nat_lit 1196845342) (nat_lit 0) D2M8K2.t9515 from rfl, totK_node, tot9514, tot9515]
  decide +kernel

theorem arows9510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9510 = true := by
  rw [show D2M8K2.u9510 = KTree.node D2M8K2.t9516 (nat_lit 20492874) (nat_lit 3677498367) (nat_lit 0) D2M8K2.t9517 from rfl, allE_node, rows9516, irow9510, rows9517]
  all_goals rfl

theorem atot9510 : totK PD2M8K2 D2M8K2.u9510 = [88453318852, 511884759204, 824658631421, 372897697397, 29350937260, 0, 0, 0] := by
  rw [show D2M8K2.u9510 = KTree.node D2M8K2.t9516 (nat_lit 20492874) (nat_lit 3677498367) (nat_lit 0) D2M8K2.t9517 from rfl, totK_node, tot9516, tot9517]
  decide +kernel

theorem arows9511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9511 = true := by
  rw [show D2M8K2.u9511 = KTree.node D2M8K2.t9518 (nat_lit 20494204) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t9519 from rfl, allE_node, rows9518, irow9511, rows9519]
  all_goals rfl

theorem atot9511 : totK PD2M8K2 D2M8K2.u9511 = [261047138280, 705467835352, 641003343125, 205081775697, 8209931632, 0, 0, 0] := by
  rw [show D2M8K2.u9511 = KTree.node D2M8K2.t9518 (nat_lit 20494204) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t9519 from rfl, totK_node, tot9518, tot9519]
  decide +kernel

theorem arows9515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9515 = true := by
  rw [show D2M8K2.u9515 = KTree.node D2M8K2.t9520 (nat_lit 20495715) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t9521 from rfl, allE_node, rows9520, irow9515, rows9521]
  all_goals rfl

theorem atot9515 : totK PD2M8K2 D2M8K2.u9515 = [161062866879, 759178381302, 761164453731, 125643959632, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u9515 = KTree.node D2M8K2.t9520 (nat_lit 20495715) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t9521 from rfl, totK_node, tot9520, tot9521]
  decide +kernel

theorem arows9516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9516 = true := by
  rw [show D2M8K2.u9516 = KTree.node D2M8K2.t9522 (nat_lit 20504468) (nat_lit 3064244376) (nat_lit 0) D2M8K2.t9523 from rfl, allE_node, rows9522, irow9516, rows9523]
  all_goals rfl

theorem atot9516 : totK PD2M8K2 D2M8K2.u9516 = [205159888884, 666271319684, 699040288182, 209827362657, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u9516 = KTree.node D2M8K2.t9522 (nat_lit 20504468) (nat_lit 3064244376) (nat_lit 0) D2M8K2.t9523 from rfl, totK_node, tot9522, tot9523]
  decide +kernel

theorem arows9518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9518 = true := by
  rw [show D2M8K2.u9518 = KTree.node D2M8K2.t9524 (nat_lit 20505971) (nat_lit 2907377834) (nat_lit 0) D2M8K2.t9525 from rfl, allE_node, rows9524, irow9518, rows9525]
  all_goals rfl

theorem atot9518 : totK PD2M8K2 D2M8K2.u9518 = [221967777151, 789912665088, 686609743496, 116157535566, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u9518 = KTree.node D2M8K2.t9524 (nat_lit 20505971) (nat_lit 2907377834) (nat_lit 0) D2M8K2.t9525 from rfl, totK_node, tot9524, tot9525]
  decide +kernel

theorem arows9519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9519 = true := by
  rw [show D2M8K2.u9519 = KTree.node D2M8K2.t9526 (nat_lit 20507672) (nat_lit 2899190801) (nat_lit 0) D2M8K2.t9527 from rfl, allE_node, rows9526, irow9519, rows9527]
  all_goals rfl

theorem atot9519 : totK PD2M8K2 D2M8K2.u9519 = [0, 393795574701, 958473336340, 408129331993, 22144019970, 0, 0, 0] := by
  rw [show D2M8K2.u9519 = KTree.node D2M8K2.t9526 (nat_lit 20507672) (nat_lit 2899190801) (nat_lit 0) D2M8K2.t9527 from rfl, totK_node, tot9526, tot9527]
  decide +kernel

theorem arows9522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9522 = true := by
  rw [show D2M8K2.u9522 = KTree.node D2M8K2.t9528 (nat_lit 20509303) (nat_lit 2105578096) (nat_lit 0) D2M8K2.t9529 from rfl, allE_node, rows9528, irow9522, rows9529]
  all_goals rfl

theorem atot9522 : totK PD2M8K2 D2M8K2.u9522 = [0, 250850323268, 810746190773, 588787390070, 80581658017, 1206465782, 0, 0] := by
  rw [show D2M8K2.u9522 = KTree.node D2M8K2.t9528 (nat_lit 20509303) (nat_lit 2105578096) (nat_lit 0) D2M8K2.t9529 from rfl, totK_node, tot9528, tot9529]
  decide +kernel

theorem arows9523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9523 = true := by
  rw [show D2M8K2.u9523 = KTree.node D2M8K2.t9530 (nat_lit 20511775) (nat_lit 2227677194) (nat_lit 0) D2M8K2.t9531 from rfl, allE_node, rows9530, irow9523, rows9531]
  all_goals rfl

theorem atot9523 : totK PD2M8K2 D2M8K2.u9523 = [0, 250101940900, 845144404342, 644841974351, 65975107104, 0, 0, 0] := by
  rw [show D2M8K2.u9523 = KTree.node D2M8K2.t9530 (nat_lit 20511775) (nat_lit 2227677194) (nat_lit 0) D2M8K2.t9531 from rfl, totK_node, tot9530, tot9531]
  decide +kernel

theorem arows9525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9525 = true := by
  rw [show D2M8K2.u9525 = KTree.node D2M8K2.t9532 (nat_lit 20513082) (nat_lit 3230748523) (nat_lit 0) D2M8K2.t9533 from rfl, allE_node, rows9532, irow9525, rows9533]
  all_goals rfl

theorem atot9525 : totK PD2M8K2 D2M8K2.u9525 = [0, 347112432622, 929130467592, 496390265139, 34470221135, 0, 0, 0] := by
  rw [show D2M8K2.u9525 = KTree.node D2M8K2.t9532 (nat_lit 20513082) (nat_lit 3230748523) (nat_lit 0) D2M8K2.t9533 from rfl, totK_node, tot9532, tot9533]
  decide +kernel

theorem arows9526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9526 = true := by
  rw [show D2M8K2.u9526 = KTree.node D2M8K2.t9534 (nat_lit 20516321) (nat_lit 2213229743) (nat_lit 0) D2M8K2.t9535 from rfl, allE_node, rows9534, irow9526, rows9535]
  all_goals rfl

theorem atot9526 : totK PD2M8K2 D2M8K2.u9526 = [0, 235427832257, 804209288008, 638626869435, 96674486464, 1162935789, 0, 0] := by
  rw [show D2M8K2.u9526 = KTree.node D2M8K2.t9534 (nat_lit 20516321) (nat_lit 2213229743) (nat_lit 0) D2M8K2.t9535 from rfl, totK_node, tot9534, tot9535]
  decide +kernel

theorem arows9532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9532 = true := by
  rw [show D2M8K2.u9532 = KTree.node D2M8K2.t9536 (nat_lit 20518057) (nat_lit 1266429483) (nat_lit 0) D2M8K2.t9537 from rfl, allE_node, rows9536, irow9532, rows9537]
  all_goals rfl

theorem atot9532 : totK PD2M8K2 D2M8K2.u9532 = [0, 172292400984, 664646565640, 711023186910, 206154206587, 11853261585, 0, 0] := by
  rw [show D2M8K2.u9532 = KTree.node D2M8K2.t9536 (nat_lit 20518057) (nat_lit 1266429483) (nat_lit 0) D2M8K2.t9537 from rfl, totK_node, tot9536, tot9537]
  decide +kernel

theorem arows9533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9533 = true := by
  rw [show D2M8K2.u9533 = KTree.node D2M8K2.t9538 (nat_lit 20526669) (nat_lit 1202564446) (nat_lit 0) D2M8K2.t9539 from rfl, allE_node, rows9538, irow9533, rows9539]
  all_goals rfl

theorem atot9533 : totK PD2M8K2 D2M8K2.u9533 = [133497357572, 540391805087, 747194209286, 361196836968, 27899019731, 0, 0, 0] := by
  rw [show D2M8K2.u9533 = KTree.node D2M8K2.t9538 (nat_lit 20526669) (nat_lit 1202564446) (nat_lit 0) D2M8K2.t9539 from rfl, totK_node, tot9538, tot9539]
  decide +kernel

theorem arows9535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9535 = true := by
  rw [show D2M8K2.u9535 = KTree.node D2M8K2.t9540 (nat_lit 20529942) (nat_lit 3562086533) (nat_lit 0) D2M8K2.t9541 from rfl, allE_node, rows9540, irow9535, rows9541]
  all_goals rfl

theorem atot9535 : totK PD2M8K2 D2M8K2.u9535 = [270851846533, 843216114559, 587303602335, 79918971232, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u9535 = KTree.node D2M8K2.t9540 (nat_lit 20529942) (nat_lit 3562086533) (nat_lit 0) D2M8K2.t9541 from rfl, totK_node, tot9540, tot9541]
  decide +kernel

theorem arows9536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9536 = true := by
  rw [show D2M8K2.u9536 = KTree.node D2M8K2.t9542 (nat_lit 20531894) (nat_lit 3627798010) (nat_lit 0) D2M8K2.t9543 from rfl, allE_node, rows9542, irow9536, rows9543]
  all_goals rfl

theorem atot9536 : totK PD2M8K2 D2M8K2.u9536 = [161705976811, 726652940066, 807956685362, 121566075787, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9536 = KTree.node D2M8K2.t9542 (nat_lit 20531894) (nat_lit 3627798010) (nat_lit 0) D2M8K2.t9543 from rfl, totK_node, tot9542, tot9543]
  decide +kernel

theorem arows9539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9539 = true := by
  rw [show D2M8K2.u9539 = KTree.node D2M8K2.t9544 (nat_lit 20533580) (nat_lit 3237081809) (nat_lit 0) D2M8K2.t9545 from rfl, allE_node, rows9544, irow9539, rows9545]
  all_goals rfl

theorem atot9539 : totK PD2M8K2 D2M8K2.u9539 = [257765346470, 770505046597, 599093034160, 188941024857, 21381705809, 0, 0, 0] := by
  rw [show D2M8K2.u9539 = KTree.node D2M8K2.t9544 (nat_lit 20533580) (nat_lit 3237081809) (nat_lit 0) D2M8K2.t9545 from rfl, totK_node, tot9544, tot9545]
  decide +kernel

theorem arows9540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9540 = true := by
  rw [show D2M8K2.u9540 = KTree.node D2M8K2.t9546 (nat_lit 20535070) (nat_lit 3142388145) (nat_lit 0) D2M8K2.t9547 from rfl, allE_node, rows9546, irow9540, rows9547]
  all_goals rfl

theorem atot9540 : totK PD2M8K2 D2M8K2.u9540 = [86101696324, 461780672215, 860938432993, 380147941527, 16027155882, 0, 0, 0] := by
  rw [show D2M8K2.u9540 = KTree.node D2M8K2.t9546 (nat_lit 20535070) (nat_lit 3142388145) (nat_lit 0) D2M8K2.t9547 from rfl, totK_node, tot9546, tot9547]
  decide +kernel

theorem arows9542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9542 = true := by
  rw [show D2M8K2.u9542 = KTree.node D2M8K2.t9548 (nat_lit 20540046) (nat_lit 3953930835) (nat_lit 0) D2M8K2.t9549 from rfl, allE_node, rows9548, irow9542, rows9549]
  all_goals rfl

theorem atot9542 : totK PD2M8K2 D2M8K2.u9542 = [355288289293, 945589504314, 505637334444, 37900592721, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9542 = KTree.node D2M8K2.t9548 (nat_lit 20540046) (nat_lit 3953930835) (nat_lit 0) D2M8K2.t9549 from rfl, totK_node, tot9548, tot9549]
  decide +kernel

theorem arows9543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9543 = true := by
  rw [show D2M8K2.u9543 = KTree.node D2M8K2.t9550 (nat_lit 20541712) (nat_lit 2315120929) (nat_lit 0) D2M8K2.t9551 from rfl, allE_node, rows9550, irow9543, rows9551]
  all_goals rfl

theorem atot9543 : totK PD2M8K2 D2M8K2.u9543 = [10983878938, 473937427660, 980164237164, 312340234248, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u9543 = KTree.node D2M8K2.t9550 (nat_lit 20541712) (nat_lit 2315120929) (nat_lit 0) D2M8K2.t9551 from rfl, totK_node, tot9550, tot9551]
  decide +kernel

theorem arows9547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9547 = true := by
  rw [show D2M8K2.u9547 = KTree.node D2M8K2.t9552 (nat_lit 20543368) (nat_lit 3054795056) (nat_lit 0) D2M8K2.t9553 from rfl, allE_node, rows9552, irow9547, rows9553]
  all_goals rfl

theorem atot9547 : totK PD2M8K2 D2M8K2.u9547 = [328513955175, 920899466282, 530684786095, 44963071616, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9547 = KTree.node D2M8K2.t9552 (nat_lit 20543368) (nat_lit 3054795056) (nat_lit 0) D2M8K2.t9553 from rfl, totK_node, tot9552, tot9553]
  decide +kernel

theorem arows9548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9548 = true := by
  rw [show D2M8K2.u9548 = KTree.node D2M8K2.t9554 (nat_lit 20545452) (nat_lit 3152783054) (nat_lit 0) D2M8K2.t9555 from rfl, allE_node, rows9554, irow9548, rows9555]
  all_goals rfl

theorem atot9548 : totK PD2M8K2 D2M8K2.u9548 = [173880593436, 682879858255, 763182851132, 186746450126, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u9548 = KTree.node D2M8K2.t9554 (nat_lit 20545452) (nat_lit 3152783054) (nat_lit 0) D2M8K2.t9555 from rfl, totK_node, tot9554, tot9555]
  decide +kernel

theorem arows9550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9550 = true := by
  rw [show D2M8K2.u9550 = KTree.node D2M8K2.t9556 (nat_lit 20547033) (nat_lit 1787488327) (nat_lit 0) D2M8K2.t9557 from rfl, allE_node, rows9556, irow9550, rows9557]
  all_goals rfl

theorem atot9550 : totK PD2M8K2 D2M8K2.u9550 = [254208946231, 789296172050, 661104657009, 104121849784, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u9550 = KTree.node D2M8K2.t9556 (nat_lit 20547033) (nat_lit 1787488327) (nat_lit 0) D2M8K2.t9557 from rfl, totK_node, tot9556, tot9557]
  decide +kernel

theorem arows9551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9551 = true := by
  rw [show D2M8K2.u9551 = KTree.node D2M8K2.t9558 (nat_lit 20548687) (nat_lit 1636405389) (nat_lit 0) D2M8K2.t9559 from rfl, allE_node, rows9558, irow9551, rows9559]
  all_goals rfl

theorem atot9551 : totK PD2M8K2 D2M8K2.u9551 = [0, 430774933780, 951316199513, 386213632188, 22143218390, 0, 0, 0] := by
  rw [show D2M8K2.u9551 = KTree.node D2M8K2.t9558 (nat_lit 20548687) (nat_lit 1636405389) (nat_lit 0) D2M8K2.t9559 from rfl, totK_node, tot9558, tot9559]
  decide +kernel

theorem arows9554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9554 = true := by
  rw [show D2M8K2.u9554 = KTree.node D2M8K2.t9560 (nat_lit 20550576) (nat_lit 3506987218) (nat_lit 0) D2M8K2.t9561 from rfl, allE_node, rows9560, irow9554, rows9561]
  all_goals rfl

theorem atot9554 : totK PD2M8K2 D2M8K2.u9554 = [0, 317246979937, 926443374552, 495663247695, 29736745255, 0, 0, 0] := by
  rw [show D2M8K2.u9554 = KTree.node D2M8K2.t9560 (nat_lit 20550576) (nat_lit 3506987218) (nat_lit 0) D2M8K2.t9561 from rfl, totK_node, tot9560, tot9561]
  decide +kernel

theorem arows9555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9555 = true := by
  rw [show D2M8K2.u9555 = KTree.node D2M8K2.t9562 (nat_lit 20552617) (nat_lit 1484400079) (nat_lit 0) D2M8K2.t9563 from rfl, allE_node, rows9562, irow9555, rows9563]
  all_goals rfl

theorem atot9555 : totK PD2M8K2 D2M8K2.u9555 = [0, 161410853672, 724929242143, 774904561109, 116828344717, 1239866073, 0, 0] := by
  rw [show D2M8K2.u9555 = KTree.node D2M8K2.t9562 (nat_lit 20552617) (nat_lit 1484400079) (nat_lit 0) D2M8K2.t9563 from rfl, totK_node, tot9562, tot9563]
  decide +kernel

theorem arows9557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9557 = true := by
  rw [show D2M8K2.u9557 = KTree.node D2M8K2.t9564 (nat_lit 20554312) (nat_lit 3757993128) (nat_lit 0) D2M8K2.t9565 from rfl, allE_node, rows9564, irow9557, rows9565]
  all_goals rfl

theorem atot9557 : totK PD2M8K2 D2M8K2.u9557 = [0, 395764073018, 962903874249, 439333390825, 25355199112, 0, 0, 0] := by
  rw [show D2M8K2.u9557 = KTree.node D2M8K2.t9564 (nat_lit 20554312) (nat_lit 3757993128) (nat_lit 0) D2M8K2.t9565 from rfl, totK_node, tot9564, tot9565]
  decide +kernel

theorem arows9558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9558 = true := by
  rw [show D2M8K2.u9558 = KTree.node D2M8K2.t9566 (nat_lit 20560941) (nat_lit 1500648801) (nat_lit 0) D2M8K2.t9567 from rfl, allE_node, rows9566, irow9558, rows9567]
  all_goals rfl

theorem atot9558 : totK PD2M8K2 D2M8K2.u9558 = [0, 301216939200, 892082518421, 570037888380, 49550874303, 0, 0, 0] := by
  rw [show D2M8K2.u9558 = KTree.node D2M8K2.t9566 (nat_lit 20560941) (nat_lit 1500648801) (nat_lit 0) D2M8K2.t9567 from rfl, totK_node, tot9566, tot9567]
  decide +kernel

theorem arows9563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9563 = true := by
  rw [show D2M8K2.u9563 = KTree.node D2M8K2.t9568 (nat_lit 20562634) (nat_lit 2521446252) (nat_lit 0) D2M8K2.t9569 from rfl, allE_node, rows9568, irow9563, rows9569]
  all_goals rfl

theorem atot9563 : totK PD2M8K2 D2M8K2.u9563 = [0, 80405182910, 543586552576, 833211061701, 267527242881, 13105450397, 0, 0] := by
  rw [show D2M8K2.u9563 = KTree.node D2M8K2.t9568 (nat_lit 20562634) (nat_lit 2521446252) (nat_lit 0) D2M8K2.t9569 from rfl, totK_node, tot9568, tot9569]
  decide +kernel

theorem arows9564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9564 = true := by
  rw [show D2M8K2.u9564 = KTree.node D2M8K2.t9570 (nat_lit 20564339) (nat_lit 2762959666) (nat_lit 0) D2M8K2.t9571 from rfl, allE_node, rows9570, irow9564, rows9571]
  all_goals rfl

theorem atot9564 : totK PD2M8K2 D2M8K2.u9564 = [0, 261540788208, 838733286767, 619653097392, 78041615630, 1053411165, 0, 0] := by
  rw [show D2M8K2.u9564 = KTree.node D2M8K2.t9570 (nat_lit 20564339) (nat_lit 2762959666) (nat_lit 0) D2M8K2.t9571 from rfl, totK_node, tot9570, tot9571]
  decide +kernel

theorem arows9566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9566 = true := by
  rw [show D2M8K2.u9566 = KTree.node D2M8K2.t9572 (nat_lit 20566800) (nat_lit 3737108960) (nat_lit 0) D2M8K2.t9573 from rfl, allE_node, rows9572, irow9566, rows9573]
  all_goals rfl

theorem atot9566 : totK PD2M8K2 D2M8K2.u9566 = [0, 244695151778, 769433850574, 645099019470, 115500662491, 3667207281, 0, 0] := by
  rw [show D2M8K2.u9566 = KTree.node D2M8K2.t9572 (nat_lit 20566800) (nat_lit 3737108960) (nat_lit 0) D2M8K2.t9573 from rfl, totK_node, tot9572, tot9573]
  decide +kernel

theorem arows9567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9567 = true := by
  rw [show D2M8K2.u9567 = KTree.node D2M8K2.t9574 (nat_lit 20568314) (nat_lit 3978375954) (nat_lit 0) D2M8K2.t9575 from rfl, allE_node, rows9574, irow9567, rows9575]
  all_goals rfl

theorem atot9567 : totK PD2M8K2 D2M8K2.u9567 = [174434339562, 608061497387, 689299250433, 308746173652, 24838138465, 0, 0, 0] := by
  rw [show D2M8K2.u9567 = KTree.node D2M8K2.t9574 (nat_lit 20568314) (nat_lit 3978375954) (nat_lit 0) D2M8K2.t9575 from rfl, totK_node, tot9574, tot9575]
  decide +kernel

theorem arows9570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9570 = true := by
  rw [show D2M8K2.u9570 = KTree.node D2M8K2.t9576 (nat_lit 20613081) (nat_lit 1525864204) (nat_lit 0) D2M8K2.t9577 from rfl, allE_node, rows9576, irow9570, rows9577]
  all_goals rfl

theorem atot9570 : totK PD2M8K2 D2M8K2.u9570 = [239596296617, 783649258556, 649754204625, 110769993573, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u9570 = KTree.node D2M8K2.t9576 (nat_lit 20613081) (nat_lit 1525864204) (nat_lit 0) D2M8K2.t9577 from rfl, totK_node, tot9576, tot9577]
  decide +kernel

theorem arows9571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9571 = true := by
  rw [show D2M8K2.u9571 = KTree.node D2M8K2.t9578 (nat_lit 20615429) (nat_lit 2271178211) (nat_lit 0) D2M8K2.t9579 from rfl, allE_node, rows9578, irow9571, rows9579]
  all_goals rfl

theorem atot9571 : totK PD2M8K2 D2M8K2.u9571 = [231312059488, 791747624069, 710540378112, 86566014205, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9571 = KTree.node D2M8K2.t9578 (nat_lit 20615429) (nat_lit 2271178211) (nat_lit 0) D2M8K2.t9579 from rfl, totK_node, tot9578, tot9579]
  decide +kernel

theorem arows9573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9573 = true := by
  rw [show D2M8K2.u9573 = KTree.node D2M8K2.t9580 (nat_lit 20616651) (nat_lit 3740217982) (nat_lit 0) D2M8K2.t9581 from rfl, allE_node, rows9580, irow9573, rows9581]
  all_goals rfl

theorem atot9573 : totK PD2M8K2 D2M8K2.u9573 = [193217774520, 735929938242, 671425066858, 205565026320, 21376388639, 0, 0, 0] := by
  rw [show D2M8K2.u9573 = KTree.node D2M8K2.t9580 (nat_lit 20616651) (nat_lit 3740217982) (nat_lit 0) D2M8K2.t9581 from rfl, totK_node, tot9580, tot9581]
  decide +kernel

theorem arows9574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9574 = true := by
  rw [show D2M8K2.u9574 = KTree.node D2M8K2.t9582 (nat_lit 20618174) (nat_lit 2975174593) (nat_lit 0) D2M8K2.t9583 from rfl, allE_node, rows9582, irow9574, rows9583]
  all_goals rfl

theorem atot9574 : totK PD2M8K2 D2M8K2.u9574 = [110137281250, 494065769666, 807355498526, 360073507055, 15994617723, 0, 0, 0] := by
  rw [show D2M8K2.u9574 = KTree.node D2M8K2.t9582 (nat_lit 20618174) (nat_lit 2975174593) (nat_lit 0) D2M8K2.t9583 from rfl, totK_node, tot9582, tot9583]
  decide +kernel

theorem arows9578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9578 = true := by
  rw [show D2M8K2.u9578 = KTree.node D2M8K2.t9584 (nat_lit 20619664) (nat_lit 3357963893) (nat_lit 0) D2M8K2.t9585 from rfl, allE_node, rows9584, irow9578, rows9585]
  all_goals rfl

theorem atot9578 : totK PD2M8K2 D2M8K2.u9578 = [288659696641, 868024034481, 589304614376, 57640204752, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9578 = KTree.node D2M8K2.t9584 (nat_lit 20619664) (nat_lit 3357963893) (nat_lit 0) D2M8K2.t9585 from rfl, totK_node, tot9584, tot9585]
  decide +kernel

theorem arows9579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9579 = true := by
  rw [show D2M8K2.u9579 = KTree.node D2M8K2.t9586 (nat_lit 20621414) (nat_lit 4093519868) (nat_lit 0) D2M8K2.t9587 from rfl, allE_node, rows9586, irow9579, rows9587]
  all_goals rfl

theorem atot9579 : totK PD2M8K2 D2M8K2.u9579 = [122297332964, 589610319892, 805929337256, 245578923594, 10460523352, 0, 0, 0] := by
  rw [show D2M8K2.u9579 = KTree.node D2M8K2.t9586 (nat_lit 20621414) (nat_lit 4093519868) (nat_lit 0) D2M8K2.t9587 from rfl, totK_node, tot9586, tot9587]
  decide +kernel

theorem arows9581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9581 = true := by
  rw [show D2M8K2.u9581 = KTree.node D2M8K2.t9588 (nat_lit 20623138) (nat_lit 3364839306) (nat_lit 0) D2M8K2.t9589 from rfl, allE_node, rows9588, irow9581, rows9589]
  all_goals rfl

theorem atot9581 : totK PD2M8K2 D2M8K2.u9581 = [296488670608, 878685598974, 593904766896, 58013004283, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9581 = KTree.node D2M8K2.t9588 (nat_lit 20623138) (nat_lit 3364839306) (nat_lit 0) D2M8K2.t9589 from rfl, totK_node, tot9588, tot9589]
  decide +kernel

theorem arows9582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9582 = true := by
  rw [show D2M8K2.u9582 = KTree.node D2M8K2.t9590 (nat_lit 20624840) (nat_lit 3362199937) (nat_lit 0) D2M8K2.t9591 from rfl, allE_node, rows9590, irow9582, rows9591]
  all_goals rfl

theorem atot9582 : totK PD2M8K2 D2M8K2.u9582 = [87123270202, 550150578000, 856582509057, 283278401647, 13216353549, 0, 0, 0] := by
  rw [show D2M8K2.u9582 = KTree.node D2M8K2.t9590 (nat_lit 20624840) (nat_lit 3362199937) (nat_lit 0) D2M8K2.t9591 from rfl, totK_node, tot9590, tot9591]
  decide +kernel

theorem arows9585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9585 = true := by
  rw [show D2M8K2.u9585 = KTree.node D2M8K2.t9592 (nat_lit 20629685) (nat_lit 2300761511) (nat_lit 0) D2M8K2.t9593 from rfl, allE_node, rows9592, irow9585, rows9593]
  all_goals rfl

theorem atot9585 : totK PD2M8K2 D2M8K2.u9585 = [360495417397, 929448447681, 519800714253, 42741889412, 0, 0, 0, 0] := by
  rw [show D2M8K2.u9585 = KTree.node D2M8K2.t9592 (nat_lit 20629685) (nat_lit 2300761511) (nat_lit 0) D2M8K2.t9593 from rfl, totK_node, tot9592, tot9593]
  decide +kernel

theorem arows9586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9586 = true := by
  rw [show D2M8K2.u9586 = KTree.node D2M8K2.t9594 (nat_lit 20631294) (nat_lit 3264598146) (nat_lit 0) D2M8K2.t9595 from rfl, allE_node, rows9594, irow9586, rows9595]
  all_goals rfl

theorem atot9586 : totK PD2M8K2 D2M8K2.u9586 = [0, 463966509473, 991397106728, 327574952338, 9938656398, 0, 0, 0] := by
  rw [show D2M8K2.u9586 = KTree.node D2M8K2.t9594 (nat_lit 20631294) (nat_lit 3264598146) (nat_lit 0) D2M8K2.t9595 from rfl, totK_node, tot9594, tot9595]
  decide +kernel

theorem arows9588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9588 = true := by
  rw [show D2M8K2.u9588 = KTree.node D2M8K2.t9596 (nat_lit 20633092) (nat_lit 4043245342) (nat_lit 0) D2M8K2.t9597 from rfl, allE_node, rows9596, irow9588, rows9597]
  all_goals rfl

theorem atot9588 : totK PD2M8K2 D2M8K2.u9588 = [0, 356111490642, 943535049880, 432804729837, 22544449898, 0, 0, 0] := by
  rw [show D2M8K2.u9588 = KTree.node D2M8K2.t9596 (nat_lit 20633092) (nat_lit 4043245342) (nat_lit 0) D2M8K2.t9597 from rfl, totK_node, tot9596, tot9597]
  decide +kernel

theorem arows9589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9589 = true := by
  rw [show D2M8K2.u9589 = KTree.node D2M8K2.t9598 (nat_lit 20634725) (nat_lit 2323809461) (nat_lit 0) D2M8K2.t9599 from rfl, allE_node, rows9598, irow9589, rows9599]
  all_goals rfl

theorem atot9589 : totK PD2M8K2 D2M8K2.u9589 = [0, 129835094220, 683055339933, 838013971181, 122137824186, 1310285577, 0, 0] := by
  rw [show D2M8K2.u9589 = KTree.node D2M8K2.t9598 (nat_lit 20634725) (nat_lit 2323809461) (nat_lit 0) D2M8K2.t9599 from rfl, totK_node, tot9598, tot9599]
  decide +kernel

end QECKChecks.D2M8K2
