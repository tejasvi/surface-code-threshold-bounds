import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A17

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows10430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10430 = true := by
  rw [show D2M8K2.u10430 = KTree.node D2M8K2.u10428 (nat_lit 22786438) (nat_lit 2494477528) (nat_lit 0) D2M8K2.u10429 from rfl, allE_node, arows10428, irow10430, arows10429]
  all_goals rfl

theorem atot10430 : totK PD2M8K2 D2M8K2.u10430 = [0, 0, 420691460119, 1448363504828, 1399601091750, 307973049602, 8895493171, 0] := by
  rw [show D2M8K2.u10430 = KTree.node D2M8K2.u10428 (nat_lit 22786438) (nat_lit 2494477528) (nat_lit 0) D2M8K2.u10429 from rfl, totK_node, atot10428, atot10429]
  decide +kernel

theorem arows10433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10433 = true := by
  rw [show D2M8K2.u10433 = KTree.node D2M8K2.u10431 (nat_lit 22790128) (nat_lit 3258814643) (nat_lit 0) D2M8K2.u10432 from rfl, allE_node, arows10431, irow10433, arows10432]
  all_goals rfl

theorem atot10433 : totK PD2M8K2 D2M8K2.u10433 = [0, 0, 0, 521648244292, 1679328909484, 1131524963909, 129117039642, 1217496766] := by
  rw [show D2M8K2.u10433 = KTree.node D2M8K2.u10431 (nat_lit 22790128) (nat_lit 3258814643) (nat_lit 0) D2M8K2.u10432 from rfl, totK_node, atot10431, atot10432]
  decide +kernel

theorem arows10437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10437 = true := by
  rw [show D2M8K2.u10437 = KTree.node D2M8K2.u10435 (nat_lit 22799244) (nat_lit 3603715367) (nat_lit 0) D2M8K2.u10436 from rfl, allE_node, arows10435, irow10437, arows10436]
  all_goals rfl

theorem atot10437 : totK PD2M8K2 D2M8K2.u10437 = [0, 0, 0, 801858033172, 1902322336722, 856683337896, 55313854867, 0] := by
  rw [show D2M8K2.u10437 = KTree.node D2M8K2.u10435 (nat_lit 22799244) (nat_lit 3603715367) (nat_lit 0) D2M8K2.u10436 from rfl, totK_node, atot10435, atot10436]
  decide +kernel

theorem arows10440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10440 = true := by
  rw [show D2M8K2.u10440 = KTree.node D2M8K2.u10438 (nat_lit 22802443) (nat_lit 1453313045) (nat_lit 0) D2M8K2.u10439 from rfl, allE_node, arows10438, irow10440, arows10439]
  all_goals rfl

theorem atot10440 : totK PD2M8K2 D2M8K2.u10440 = [0, 0, 0, 410787186638, 1444921028948, 1314873463841, 303981060019, 13105450397] := by
  rw [show D2M8K2.u10440 = KTree.node D2M8K2.u10438 (nat_lit 22802443) (nat_lit 1453313045) (nat_lit 0) D2M8K2.u10439 from rfl, totK_node, atot10438, atot10439]
  decide +kernel

theorem arows10445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10445 = true := by
  rw [show D2M8K2.u10445 = KTree.node D2M8K2.u10443 (nat_lit 22806271) (nat_lit 2324300023) (nat_lit 0) D2M8K2.u10444 from rfl, allE_node, arows10443, irow10445, arows10444]
  all_goals rfl

theorem atot10445 : totK PD2M8K2 D2M8K2.u10445 = [0, 0, 72675911180, 560746519620, 1529305346109, 1139047156586, 176965968599, 4630915822] := by
  rw [show D2M8K2.u10445 = KTree.node D2M8K2.u10443 (nat_lit 22806271) (nat_lit 2324300023) (nat_lit 0) D2M8K2.u10444 from rfl, totK_node, atot10443, atot10444]
  decide +kernel

theorem arows10448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10448 = true := by
  rw [show D2M8K2.u10448 = KTree.node D2M8K2.u10446 (nat_lit 22811336) (nat_lit 3599311364) (nat_lit 0) D2M8K2.u10447 from rfl, allE_node, arows10446, irow10448, arows10447]
  all_goals rfl

theorem atot10448 : totK PD2M8K2 D2M8K2.u10448 = [0, 0, 460418919703, 1603208746830, 1320405818611, 157201255542, 1310517177, 0] := by
  rw [show D2M8K2.u10448 = KTree.node D2M8K2.u10446 (nat_lit 22811336) (nat_lit 3599311364) (nat_lit 0) D2M8K2.u10447 from rfl, totK_node, atot10446, atot10447]
  decide +kernel

theorem arows10452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10452 = true := by
  rw [show D2M8K2.u10452 = KTree.node D2M8K2.u10450 (nat_lit 22815333) (nat_lit 1322123197) (nat_lit 0) D2M8K2.u10451 from rfl, allE_node, arows10450, irow10452, arows10451]
  all_goals rfl

theorem atot10452 : totK PD2M8K2 D2M8K2.u10452 = [0, 0, 446795977108, 1532353893850, 1323109560802, 326817076757, 15066332673, 0] := by
  rw [show D2M8K2.u10452 = KTree.node D2M8K2.u10450 (nat_lit 22815333) (nat_lit 1322123197) (nat_lit 0) D2M8K2.u10451 from rfl, totK_node, atot10450, atot10451]
  decide +kernel

theorem arows10455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10455 = true := by
  rw [show D2M8K2.u10455 = KTree.node D2M8K2.u10453 (nat_lit 22819570) (nat_lit 1778071288) (nat_lit 32) D2M8K2.u10454 from rfl, allE_node, arows10453, irow10455, arows10454]
  all_goals rfl

theorem atot10455 : totK PD2M8K2 D2M8K2.u10455 = [0, 0, 511973273166, 1663785945497, 1225032643394, 156504638528, 4532804645, 0] := by
  rw [show D2M8K2.u10455 = KTree.node D2M8K2.u10453 (nat_lit 22819570) (nat_lit 1778071288) (nat_lit 32) D2M8K2.u10454 from rfl, totK_node, atot10453, atot10454]
  decide +kernel

theorem arows10461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10461 = true := by
  rw [show D2M8K2.u10461 = KTree.node D2M8K2.u10459 (nat_lit 22823090) (nat_lit 3635859514) (nat_lit 0) D2M8K2.u10460 from rfl, allE_node, arows10459, irow10461, arows10460]
  all_goals rfl

theorem atot10461 : totK PD2M8K2 D2M8K2.u10461 = [0, 0, 415807740403, 1411557118391, 1400601339984, 330797228720, 13250685261, 0] := by
  rw [show D2M8K2.u10461 = KTree.node D2M8K2.u10459 (nat_lit 22823090) (nat_lit 3635859514) (nat_lit 0) D2M8K2.u10460 from rfl, totK_node, atot10459, atot10460]
  decide +kernel

theorem arows10464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10464 = true := by
  rw [show D2M8K2.u10464 = KTree.node D2M8K2.u10462 (nat_lit 22826390) (nat_lit 3722288679) (nat_lit 0) D2M8K2.u10463 from rfl, allE_node, arows10462, irow10464, arows10463]
  all_goals rfl

theorem atot10464 : totK PD2M8K2 D2M8K2.u10464 = [0, 0, 92722817510, 1072258934102, 1828000250099, 510553475115, 19729075688, 0] := by
  rw [show D2M8K2.u10464 = KTree.node D2M8K2.u10462 (nat_lit 22826390) (nat_lit 3722288679) (nat_lit 0) D2M8K2.u10463 from rfl, totK_node, atot10462, atot10463]
  decide +kernel

theorem arows10468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10468 = true := by
  rw [show D2M8K2.u10468 = KTree.node D2M8K2.u10466 (nat_lit 22834412) (nat_lit 3619094356) (nat_lit 0) D2M8K2.u10467 from rfl, allE_node, arows10466, irow10468, arows10467]
  all_goals rfl

theorem atot10468 : totK PD2M8K2 D2M8K2.u10468 = [0, 0, 0, 731905313085, 1748243619316, 913743462448, 87082877896, 1138244013] := by
  rw [show D2M8K2.u10468 = KTree.node D2M8K2.u10466 (nat_lit 22834412) (nat_lit 3619094356) (nat_lit 0) D2M8K2.u10467 from rfl, totK_node, atot10466, atot10467]
  decide +kernel

theorem arows10471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10471 = true := by
  rw [show D2M8K2.u10471 = KTree.node D2M8K2.u10469 (nat_lit 22842005) (nat_lit 1614110536) (nat_lit 0) D2M8K2.u10470 from rfl, allE_node, arows10469, irow10471, arows10470]
  all_goals rfl

theorem atot10471 : totK PD2M8K2 D2M8K2.u10471 = [0, 0, 0, 767749258129, 1882578866482, 795247377464, 45304018359, 0] := by
  rw [show D2M8K2.u10471 = KTree.node D2M8K2.u10469 (nat_lit 22842005) (nat_lit 1614110536) (nat_lit 0) D2M8K2.u10470 from rfl, totK_node, atot10469, atot10470]
  decide +kernel

theorem arows10476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10476 = true := by
  rw [show D2M8K2.u10476 = KTree.node D2M8K2.u10474 (nat_lit 22847131) (nat_lit 2115071988) (nat_lit 0) D2M8K2.u10475 from rfl, allE_node, arows10474, irow10476, arows10475]
  all_goals rfl

theorem atot10476 : totK PD2M8K2 D2M8K2.u10476 = [0, 0, 351453791850, 974190816930, 1122481195197, 838950614233, 160397158189, 4914284239] := by
  rw [show D2M8K2.u10476 = KTree.node D2M8K2.u10474 (nat_lit 22847131) (nat_lit 2115071988) (nat_lit 0) D2M8K2.u10475 from rfl, totK_node, atot10474, atot10475]
  decide +kernel

theorem arows10479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10479 = true := by
  rw [show D2M8K2.u10479 = KTree.node D2M8K2.u10477 (nat_lit 22854948) (nat_lit 2711937486) (nat_lit 0) D2M8K2.u10478 from rfl, allE_node, arows10477, irow10479, arows10478]
  all_goals rfl

theorem atot10479 : totK PD2M8K2 D2M8K2.u10479 = [0, 0, 472874985516, 1650655627881, 1360100945129, 167031050140, 1369150432, 0] := by
  rw [show D2M8K2.u10479 = KTree.node D2M8K2.u10477 (nat_lit 22854948) (nat_lit 2711937486) (nat_lit 0) D2M8K2.u10478 from rfl, totK_node, atot10477, atot10478]
  decide +kernel

theorem arows10483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10483 = true := by
  rw [show D2M8K2.u10483 = KTree.node D2M8K2.u10481 (nat_lit 22858200) (nat_lit 3555296004) (nat_lit 0) D2M8K2.u10482 from rfl, allE_node, arows10481, irow10483, arows10482]
  all_goals rfl

theorem atot10483 : totK PD2M8K2 D2M8K2.u10483 = [0, 0, 496973856001, 1515842290157, 1289288979668, 347295860716, 16293883145, 0] := by
  rw [show D2M8K2.u10483 = KTree.node D2M8K2.u10481 (nat_lit 22858200) (nat_lit 3555296004) (nat_lit 0) D2M8K2.u10482 from rfl, totK_node, atot10481, atot10482]
  decide +kernel

theorem arows10486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10486 = true := by
  rw [show D2M8K2.u10486 = KTree.node D2M8K2.u10484 (nat_lit 22863415) (nat_lit 2208766739) (nat_lit 0) D2M8K2.u10485 from rfl, allE_node, arows10484, irow10486, arows10485]
  all_goals rfl

theorem atot10486 : totK PD2M8K2 D2M8K2.u10486 = [0, 0, 428217872279, 1508629378848, 1404644151593, 277758693005, 9664716404, 0] := by
  rw [show D2M8K2.u10486 = KTree.node D2M8K2.u10484 (nat_lit 22863415) (nat_lit 2208766739) (nat_lit 0) D2M8K2.u10485 from rfl, totK_node, atot10484, atot10485]
  decide +kernel

theorem arows10495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10495 = true := by
  rw [show D2M8K2.u10495 = KTree.node D2M8K2.u10493 (nat_lit 22870273) (nat_lit 1457256795) (nat_lit 0) D2M8K2.u10494 from rfl, allE_node, arows10493, irow10495, arows10494]
  all_goals rfl

theorem atot10495 : totK PD2M8K2 D2M8K2.u10495 = [0, 110047735289, 506458960908, 1272080178012, 1381024972750, 344569245690, 14338667495, 0] := by
  rw [show D2M8K2.u10495 = KTree.node D2M8K2.u10493 (nat_lit 22870273) (nat_lit 1457256795) (nat_lit 0) D2M8K2.u10494 from rfl, totK_node, atot10493, atot10494]
  decide +kernel

theorem arows10498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10498 = true := by
  rw [show D2M8K2.u10498 = KTree.node D2M8K2.u10496 (nat_lit 22894350) (nat_lit 3988799751) (nat_lit 0) D2M8K2.u10497 from rfl, allE_node, arows10496, irow10498, arows10497]
  all_goals rfl

theorem atot10498 : totK PD2M8K2 D2M8K2.u10498 = [0, 463289503948, 1611132605160, 1329244114203, 183470033036, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10498 = KTree.node D2M8K2.u10496 (nat_lit 22894350) (nat_lit 3988799751) (nat_lit 0) D2M8K2.u10497 from rfl, totK_node, atot10496, atot10497]
  decide +kernel

theorem arows10502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10502 = true := by
  rw [show D2M8K2.u10502 = KTree.node D2M8K2.u10500 (nat_lit 22901764) (nat_lit 3866437580) (nat_lit 0) D2M8K2.u10501 from rfl, allE_node, arows10500, irow10502, arows10501]
  all_goals rfl

theorem atot10502 : totK PD2M8K2 D2M8K2.u10502 = [0, 413968024902, 1431210496396, 1397095195530, 303020811656, 13049727234, 0, 0] := by
  rw [show D2M8K2.u10502 = KTree.node D2M8K2.u10500 (nat_lit 22901764) (nat_lit 3866437580) (nat_lit 0) D2M8K2.u10501 from rfl, totK_node, atot10500, atot10501]
  decide +kernel

theorem arows10505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10505 = true := by
  rw [show D2M8K2.u10505 = KTree.node D2M8K2.u10503 (nat_lit 22905067) (nat_lit 1592936550) (nat_lit 0) D2M8K2.u10504 from rfl, allE_node, arows10503, irow10505, arows10504]
  all_goals rfl

theorem atot10505 : totK PD2M8K2 D2M8K2.u10505 = [0, 398436610842, 1434336574812, 1404065418033, 336419521099, 13250685261, 0, 0] := by
  rw [show D2M8K2.u10505 = KTree.node D2M8K2.u10503 (nat_lit 22905067) (nat_lit 1592936550) (nat_lit 0) D2M8K2.u10504 from rfl, totK_node, atot10503, atot10504]
  decide +kernel

theorem arows10510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10510 = true := by
  rw [show D2M8K2.u10510 = KTree.node D2M8K2.u10508 (nat_lit 22908444) (nat_lit 2468790715) (nat_lit 0) D2M8K2.u10509 from rfl, allE_node, arows10508, irow10510, arows10509]
  all_goals rfl

theorem atot10510 : totK PD2M8K2 D2M8K2.u10510 = [0, 463735490679, 1551279478350, 1331919476503, 228352231357, 4980514959, 0, 0] := by
  rw [show D2M8K2.u10510 = KTree.node D2M8K2.u10508 (nat_lit 22908444) (nat_lit 2468790715) (nat_lit 0) D2M8K2.u10509 from rfl, totK_node, atot10508, atot10509]
  decide +kernel

theorem arows10513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10513 = true := by
  rw [show D2M8K2.u10513 = KTree.node D2M8K2.u10511 (nat_lit 22913048) (nat_lit 1858004710) (nat_lit 0) D2M8K2.u10512 from rfl, allE_node, arows10511, irow10513, arows10512]
  all_goals rfl

theorem atot10513 : totK PD2M8K2 D2M8K2.u10513 = [0, 124442828397, 1047591039676, 1748413047876, 607446201613, 32018629498, 0, 0] := by
  rw [show D2M8K2.u10513 = KTree.node D2M8K2.u10511 (nat_lit 22913048) (nat_lit 1858004710) (nat_lit 0) D2M8K2.u10512 from rfl, totK_node, atot10511, atot10512]
  decide +kernel

theorem arows10517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10517 = true := by
  rw [show D2M8K2.u10517 = KTree.node D2M8K2.u10515 (nat_lit 22916586) (nat_lit 3321762336) (nat_lit 0) D2M8K2.u10516 from rfl, allE_node, arows10515, irow10517, arows10516]
  all_goals rfl

theorem atot10517 : totK PD2M8K2 D2M8K2.u10517 = [0, 0, 464800131631, 1685896160099, 1179655228247, 141873656670, 1369150432, 0] := by
  rw [show D2M8K2.u10517 = KTree.node D2M8K2.u10515 (nat_lit 22916586) (nat_lit 3321762336) (nat_lit 0) D2M8K2.u10516 from rfl, totK_node, atot10515, atot10516]
  decide +kernel

theorem arows10520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10520 = true := by
  rw [show D2M8K2.u10520 = KTree.node D2M8K2.u10518 (nat_lit 22925224) (nat_lit 3366965196) (nat_lit 0) D2M8K2.u10519 from rfl, allE_node, arows10518, irow10520, arows10519]
  all_goals rfl

theorem atot10520 : totK PD2M8K2 D2M8K2.u10520 = [0, 0, 748673862854, 1886212081678, 872923952642, 46278971598, 0, 0] := by
  rw [show D2M8K2.u10520 = KTree.node D2M8K2.u10518 (nat_lit 22925224) (nat_lit 3366965196) (nat_lit 0) D2M8K2.u10519 from rfl, totK_node, atot10518, atot10519]
  decide +kernel

theorem arows10526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10526 = true := by
  rw [show D2M8K2.u10526 = KTree.node D2M8K2.u10524 (nat_lit 22932171) (nat_lit 3575325794) (nat_lit 0) D2M8K2.u10525 from rfl, allE_node, arows10524, irow10526, arows10525]
  all_goals rfl

theorem atot10526 : totK PD2M8K2 D2M8K2.u10526 = [0, 357337161097, 1257076400017, 1508167611698, 500697375114, 19408876284, 0, 0] := by
  rw [show D2M8K2.u10526 = KTree.node D2M8K2.u10524 (nat_lit 22932171) (nat_lit 3575325794) (nat_lit 0) D2M8K2.u10525 from rfl, totK_node, atot10524, atot10525]
  decide +kernel

theorem arows10529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10529 = true := by
  rw [show D2M8K2.u10529 = KTree.node D2M8K2.u10527 (nat_lit 22940299) (nat_lit 1775272084) (nat_lit 0) D2M8K2.u10528 from rfl, allE_node, arows10527, irow10529, arows10528]
  all_goals rfl

theorem atot10529 : totK PD2M8K2 D2M8K2.u10529 = [0, 298754804022, 1188920384944, 1532136947518, 592951432238, 37609398105, 0, 0] := by
  rw [show D2M8K2.u10529 = KTree.node D2M8K2.u10527 (nat_lit 22940299) (nat_lit 1775272084) (nat_lit 0) D2M8K2.u10528 from rfl, totK_node, atot10527, atot10528]
  decide +kernel

theorem arows10533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10533 = true := by
  rw [show D2M8K2.u10533 = KTree.node D2M8K2.u10531 (nat_lit 22943490) (nat_lit 1236412734) (nat_lit 0) D2M8K2.u10532 from rfl, allE_node, arows10531, irow10533, arows10532]
  all_goals rfl

theorem atot10533 : totK PD2M8K2 D2M8K2.u10533 = [0, 419526112417, 1527858187167, 1396521551157, 279763593200, 11873025674, 0, 0] := by
  rw [show D2M8K2.u10533 = KTree.node D2M8K2.u10531 (nat_lit 22943490) (nat_lit 1236412734) (nat_lit 0) D2M8K2.u10532 from rfl, totK_node, atot10531, atot10532]
  decide +kernel

theorem arows10536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10536 = true := by
  rw [show D2M8K2.u10536 = KTree.node D2M8K2.u10534 (nat_lit 22947217) (nat_lit 1344035502) (nat_lit 0) D2M8K2.u10535 from rfl, allE_node, arows10534, irow10536, arows10535]
  all_goals rfl

theorem atot10536 : totK PD2M8K2 D2M8K2.u10536 = [0, 411401453085, 1432702437171, 1415266233700, 338940422455, 13237669976, 0, 0] := by
  rw [show D2M8K2.u10536 = KTree.node D2M8K2.u10534 (nat_lit 22947217) (nat_lit 1344035502) (nat_lit 0) D2M8K2.u10535 from rfl, totK_node, atot10534, atot10535]
  decide +kernel

theorem arows10541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10541 = true := by
  rw [show D2M8K2.u10541 = KTree.node D2M8K2.u10539 (nat_lit 22950445) (nat_lit 1266600494) (nat_lit 0) D2M8K2.u10540 from rfl, allE_node, arows10539, irow10541, arows10540]
  all_goals rfl

theorem atot10541 : totK PD2M8K2 D2M8K2.u10541 = [0, 422285271093, 1537516814027, 1432216399767, 252763260222, 4976872846, 0, 0] := by
  rw [show D2M8K2.u10541 = KTree.node D2M8K2.u10539 (nat_lit 22950445) (nat_lit 1266600494) (nat_lit 0) D2M8K2.u10540 from rfl, totK_node, atot10539, atot10540]
  decide +kernel

theorem arows10544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10544 = true := by
  rw [show D2M8K2.u10544 = KTree.node D2M8K2.u10542 (nat_lit 22954678) (nat_lit 3514756269) (nat_lit 0) D2M8K2.u10543 from rfl, allE_node, arows10542, irow10544, arows10543]
  all_goals rfl

theorem atot10544 : totK PD2M8K2 D2M8K2.u10544 = [0, 88830982688, 939221953388, 1794185058985, 782548639965, 51998917695, 0, 0] := by
  rw [show D2M8K2.u10544 = KTree.node D2M8K2.u10542 (nat_lit 22954678) (nat_lit 3514756269) (nat_lit 0) D2M8K2.u10543 from rfl, totK_node, atot10542, atot10543]
  decide +kernel

theorem arows10548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10548 = true := by
  rw [show D2M8K2.u10548 = KTree.node D2M8K2.u10546 (nat_lit 22961261) (nat_lit 1968470821) (nat_lit 0) D2M8K2.u10547 from rfl, allE_node, arows10546, irow10548, arows10547]
  all_goals rfl

theorem atot10548 : totK PD2M8K2 D2M8K2.u10548 = [0, 0, 400363800393, 1433608564789, 1405255970669, 369748702957, 15177715065, 0] := by
  rw [show D2M8K2.u10548 = KTree.node D2M8K2.u10546 (nat_lit 22961261) (nat_lit 1968470821) (nat_lit 0) D2M8K2.u10547 from rfl, totK_node, atot10546, atot10547]
  decide +kernel

theorem arows10551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10551 = true := by
  rw [show D2M8K2.u10551 = KTree.node D2M8K2.u10549 (nat_lit 22966329) (nat_lit 1849562495) (nat_lit 0) D2M8K2.u10550 from rfl, allE_node, arows10549, irow10551, arows10550]
  all_goals rfl

theorem atot10551 : totK PD2M8K2 D2M8K2.u10551 = [0, 0, 482620091589, 1620599373432, 1330902570943, 204487393288, 4031931762, 0] := by
  rw [show D2M8K2.u10551 = KTree.node D2M8K2.u10549 (nat_lit 22966329) (nat_lit 1849562495) (nat_lit 0) D2M8K2.u10550 from rfl, totK_node, atot10549, atot10550]
  decide +kernel

theorem arows10558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10558 = true := by
  rw [show D2M8K2.u10558 = KTree.node D2M8K2.u10556 (nat_lit 22969616) (nat_lit 3691383965) (nat_lit 0) D2M8K2.u10557 from rfl, allE_node, arows10556, irow10558, arows10557]
  all_goals rfl

theorem atot10558 : totK PD2M8K2 D2M8K2.u10558 = [0, 0, 421148028188, 1565324994619, 1402671974895, 211006825028, 1186940923, 0] := by
  rw [show D2M8K2.u10558 = KTree.node D2M8K2.u10556 (nat_lit 22969616) (nat_lit 3691383965) (nat_lit 0) D2M8K2.u10557 from rfl, totK_node, atot10556, atot10557]
  decide +kernel

theorem arows10561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10561 = true := by
  rw [show D2M8K2.u10561 = KTree.node D2M8K2.u10559 (nat_lit 22975566) (nat_lit 3928711501) (nat_lit 0) D2M8K2.u10560 from rfl, allE_node, arows10559, irow10561, arows10560]
  all_goals rfl

theorem atot10561 : totK PD2M8K2 D2M8K2.u10561 = [0, 395430589750, 1324301763057, 1322319239359, 532786367583, 48362935054, 1415142070, 0] := by
  rw [show D2M8K2.u10561 = KTree.node D2M8K2.u10559 (nat_lit 22975566) (nat_lit 3928711501) (nat_lit 0) D2M8K2.u10560 from rfl, totK_node, atot10559, atot10560]
  decide +kernel

theorem arows10565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10565 = true := by
  rw [show D2M8K2.u10565 = KTree.node D2M8K2.u10563 (nat_lit 22979552) (nat_lit 3747989932) (nat_lit 0) D2M8K2.u10564 from rfl, allE_node, arows10563, irow10565, arows10564]
  all_goals rfl

theorem atot10565 : totK PD2M8K2 D2M8K2.u10565 = [0, 407154796039, 1541831612115, 1459839705630, 232189645925, 7290489602, 0, 0] := by
  rw [show D2M8K2.u10565 = KTree.node D2M8K2.u10563 (nat_lit 22979552) (nat_lit 3747989932) (nat_lit 0) D2M8K2.u10564 from rfl, totK_node, atot10563, atot10564]
  decide +kernel

theorem arows10568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10568 = true := by
  rw [show D2M8K2.u10568 = KTree.node D2M8K2.u10566 (nat_lit 22982749) (nat_lit 1105433226) (nat_lit 0) D2M8K2.u10567 from rfl, allE_node, arows10566, irow10568, arows10567]
  all_goals rfl

theorem atot10568 : totK PD2M8K2 D2M8K2.u10568 = [0, 425786463047, 1468581587832, 1397041478679, 343148213142, 9396957438, 0, 0] := by
  rw [show D2M8K2.u10568 = KTree.node D2M8K2.u10566 (nat_lit 22982749) (nat_lit 1105433226) (nat_lit 0) D2M8K2.u10567 from rfl, totK_node, atot10566, atot10567]
  decide +kernel

theorem arows10573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10573 = true := by
  rw [show D2M8K2.u10573 = KTree.node D2M8K2.u10571 (nat_lit 22989539) (nat_lit 1483339461) (nat_lit 2048) D2M8K2.u10572 from rfl, allE_node, arows10571, irow10573, arows10572]
  all_goals rfl

theorem atot10573 : totK PD2M8K2 D2M8K2.u10573 = [0, 423287068518, 1454431949893, 1384688759473, 319059674356, 13049727234, 0, 0] := by
  rw [show D2M8K2.u10573 = KTree.node D2M8K2.u10571 (nat_lit 22989539) (nat_lit 1483339461) (nat_lit 2048) D2M8K2.u10572 from rfl, totK_node, atot10571, atot10572]
  decide +kernel

theorem arows10576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10576 = true := by
  rw [show D2M8K2.u10576 = KTree.node D2M8K2.u10574 (nat_lit 22996498) (nat_lit 4073638830) (nat_lit 0) D2M8K2.u10575 from rfl, allE_node, arows10574, irow10576, arows10575]
  all_goals rfl

theorem atot10576 : totK PD2M8K2 D2M8K2.u10576 = [0, 0, 793394160655, 1868505810040, 782233940606, 65112663432, 1206465782, 0] := by
  rw [show D2M8K2.u10576 = KTree.node D2M8K2.u10574 (nat_lit 22996498) (nat_lit 4073638830) (nat_lit 0) D2M8K2.u10575 from rfl, totK_node, atot10574, atot10575]
  decide +kernel

theorem arows10580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10580 = true := by
  rw [show D2M8K2.u10580 = KTree.node D2M8K2.u10578 (nat_lit 23000715) (nat_lit 3736031856) (nat_lit 0) D2M8K2.u10579 from rfl, allE_node, arows10578, irow10580, arows10579]
  all_goals rfl

theorem atot10580 : totK PD2M8K2 D2M8K2.u10580 = [0, 0, 614019717289, 1824871840589, 1094691182263, 78518734004, 0, 0] := by
  rw [show D2M8K2.u10580 = KTree.node D2M8K2.u10578 (nat_lit 23000715) (nat_lit 3736031856) (nat_lit 0) D2M8K2.u10579 from rfl, totK_node, atot10578, atot10579]
  decide +kernel

theorem arows10583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10583 = true := by
  rw [show D2M8K2.u10583 = KTree.node D2M8K2.u10581 (nat_lit 23010529) (nat_lit 1152366984) (nat_lit 0) D2M8K2.u10582 from rfl, allE_node, arows10581, irow10583, arows10582]
  all_goals rfl

theorem atot10583 : totK PD2M8K2 D2M8K2.u10583 = [0, 0, 636294009491, 1781451062021, 1013512367471, 97073745666, 1021600638, 0] := by
  rw [show D2M8K2.u10583 = KTree.node D2M8K2.u10581 (nat_lit 23010529) (nat_lit 1152366984) (nat_lit 0) D2M8K2.u10582 from rfl, totK_node, atot10581, atot10582]
  decide +kernel

theorem arows10589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10589 = true := by
  rw [show D2M8K2.u10589 = KTree.node D2M8K2.u10587 (nat_lit 23017954) (nat_lit 4107749676) (nat_lit 0) D2M8K2.u10588 from rfl, allE_node, arows10587, irow10589, arows10588]
  all_goals rfl

theorem atot10589 : totK PD2M8K2 D2M8K2.u10589 = [0, 407284249840, 1258279388107, 1210034433209, 545289937431, 93315036218, 3552795014, 0] := by
  rw [show D2M8K2.u10589 = KTree.node D2M8K2.u10587 (nat_lit 23017954) (nat_lit 4107749676) (nat_lit 0) D2M8K2.u10588 from rfl, totK_node, atot10587, atot10588]
  decide +kernel

theorem arows10592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10592 = true := by
  rw [show D2M8K2.u10592 = KTree.node D2M8K2.u10590 (nat_lit 23021577) (nat_lit 1846306080) (nat_lit 0) D2M8K2.u10591 from rfl, allE_node, arows10590, irow10592, arows10591]
  all_goals rfl

theorem atot10592 : totK PD2M8K2 D2M8K2.u10592 = [0, 418565084682, 1476757131825, 1391670729397, 356660013048, 25111632603, 0, 0] := by
  rw [show D2M8K2.u10592 = KTree.node D2M8K2.u10590 (nat_lit 23021577) (nat_lit 1846306080) (nat_lit 0) D2M8K2.u10591 from rfl, totK_node, atot10590, atot10591]
  decide +kernel

theorem arows10596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10596 = true := by
  rw [show D2M8K2.u10596 = KTree.node D2M8K2.u10594 (nat_lit 23027842) (nat_lit 3923195380) (nat_lit 0) D2M8K2.u10595 from rfl, allE_node, arows10594, irow10596, arows10595]
  all_goals rfl

theorem atot10596 : totK PD2M8K2 D2M8K2.u10596 = [0, 441187493564, 1420563727064, 1381812342121, 385109490811, 11986353485, 0, 0] := by
  rw [show D2M8K2.u10596 = KTree.node D2M8K2.u10594 (nat_lit 23027842) (nat_lit 3923195380) (nat_lit 0) D2M8K2.u10595 from rfl, totK_node, atot10594, atot10595]
  decide +kernel

theorem arows10599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10599 = true := by
  rw [show D2M8K2.u10599 = KTree.node D2M8K2.u10597 (nat_lit 23031142) (nat_lit 2952637065) (nat_lit 0) D2M8K2.u10598 from rfl, allE_node, arows10597, irow10599, arows10598]
  all_goals rfl

theorem atot10599 : totK PD2M8K2 D2M8K2.u10599 = [0, 424103428560, 1497701135853, 1384173003387, 296468701380, 12052611869, 0, 0] := by
  rw [show D2M8K2.u10599 = KTree.node D2M8K2.u10597 (nat_lit 23031142) (nat_lit 2952637065) (nat_lit 0) D2M8K2.u10598 from rfl, totK_node, atot10597, atot10598]
  decide +kernel

theorem arows10604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10604 = true := by
  rw [show D2M8K2.u10604 = KTree.node D2M8K2.u10602 (nat_lit 23034644) (nat_lit 3547730324) (nat_lit 0) D2M8K2.u10603 from rfl, allE_node, arows10602, irow10604, arows10603]
  all_goals rfl

theorem atot10604 : totK PD2M8K2 D2M8K2.u10604 = [0, 345725408665, 1421227934376, 1542885278314, 320471049157, 6249254262, 0, 0] := by
  rw [show D2M8K2.u10604 = KTree.node D2M8K2.u10602 (nat_lit 23034644) (nat_lit 3547730324) (nat_lit 0) D2M8K2.u10603 from rfl, totK_node, atot10602, atot10603]
  decide +kernel

theorem arows10607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10607 = true := by
  rw [show D2M8K2.u10607 = KTree.node D2M8K2.u10605 (nat_lit 23038714) (nat_lit 3783264946) (nat_lit 0) D2M8K2.u10606 from rfl, allE_node, arows10605, irow10607, arows10606]
  all_goals rfl

theorem atot10607 : totK PD2M8K2 D2M8K2.u10607 = [0, 0, 565451507256, 1716881274126, 1106355253935, 119401763990, 1239866073, 0] := by
  rw [show D2M8K2.u10607 = KTree.node D2M8K2.u10605 (nat_lit 23038714) (nat_lit 3783264946) (nat_lit 0) D2M8K2.u10606 from rfl, totK_node, atot10605, atot10606]
  decide +kernel

theorem arows10611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10611 = true := by
  rw [show D2M8K2.u10611 = KTree.node D2M8K2.u10609 (nat_lit 23042403) (nat_lit 3688078442) (nat_lit 0) D2M8K2.u10610 from rfl, allE_node, arows10609, irow10611, arows10610]
  all_goals rfl

theorem atot10611 : totK PD2M8K2 D2M8K2.u10611 = [0, 0, 684405536828, 1836484743755, 1049871692787, 83561879744, 0, 0] := by
  rw [show D2M8K2.u10611 = KTree.node D2M8K2.u10609 (nat_lit 23042403) (nat_lit 3688078442) (nat_lit 0) D2M8K2.u10610 from rfl, totK_node, atot10609, atot10610]
  decide +kernel

theorem arows10614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10614 = true := by
  rw [show D2M8K2.u10614 = KTree.node D2M8K2.u10612 (nat_lit 23050800) (nat_lit 3596829569) (nat_lit 0) D2M8K2.u10613 from rfl, allE_node, arows10612, irow10614, arows10613]
  all_goals rfl

theorem atot10614 : totK PD2M8K2 D2M8K2.u10614 = [0, 0, 413410560613, 1455086635320, 1356352542831, 306121099027, 13105450397, 0] := by
  rw [show D2M8K2.u10614 = KTree.node D2M8K2.u10612 (nat_lit 23050800) (nat_lit 3596829569) (nat_lit 0) D2M8K2.u10613 from rfl, totK_node, atot10612, atot10613]
  decide +kernel

theorem arows10622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10622 = true := by
  rw [show D2M8K2.u10622 = KTree.node D2M8K2.u10620 (nat_lit 23054151) (nat_lit 2298342129) (nat_lit 0) D2M8K2.u10621 from rfl, allE_node, arows10620, irow10622, arows10621]
  all_goals rfl

theorem atot10622 : totK PD2M8K2 D2M8K2.u10622 = [0, 0, 435210845537, 1577391728586, 1319594995275, 199456437233, 4720618446, 0] := by
  rw [show D2M8K2.u10622 = KTree.node D2M8K2.u10620 (nat_lit 23054151) (nat_lit 2298342129) (nat_lit 0) D2M8K2.u10621 from rfl, totK_node, atot10620, atot10621]
  decide +kernel

theorem arows10625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10625 = true := by
  rw [show D2M8K2.u10625 = KTree.node D2M8K2.u10623 (nat_lit 23059612) (nat_lit 3685887298) (nat_lit 0) D2M8K2.u10624 from rfl, allE_node, arows10623, irow10625, arows10624]
  all_goals rfl

theorem atot10625 : totK PD2M8K2 D2M8K2.u10625 = [0, 412433268895, 1481584353655, 1363577254872, 299971846538, 13081330053, 0, 0] := by
  rw [show D2M8K2.u10625 = KTree.node D2M8K2.u10623 (nat_lit 23059612) (nat_lit 3685887298) (nat_lit 0) D2M8K2.u10624 from rfl, totK_node, atot10623, atot10624]
  decide +kernel

theorem arows10629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10629 = true := by
  rw [show D2M8K2.u10629 = KTree.node D2M8K2.u10627 (nat_lit 23063154) (nat_lit 3431843160) (nat_lit 0) D2M8K2.u10628 from rfl, allE_node, arows10627, irow10629, arows10628]
  all_goals rfl

theorem atot10629 : totK PD2M8K2 D2M8K2.u10629 = [0, 422726385231, 1416375112142, 1364417236832, 397578737023, 28002240837, 0, 0] := by
  rw [show D2M8K2.u10629 = KTree.node D2M8K2.u10627 (nat_lit 23063154) (nat_lit 3431843160) (nat_lit 0) D2M8K2.u10628 from rfl, totK_node, atot10627, atot10628]
  decide +kernel

theorem arows10632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10632 = true := by
  rw [show D2M8K2.u10632 = KTree.node D2M8K2.u10630 (nat_lit 23065977) (nat_lit 1851009018) (nat_lit 0) D2M8K2.u10631 from rfl, allE_node, arows10630, irow10632, arows10631]
  all_goals rfl

theorem atot10632 : totK PD2M8K2 D2M8K2.u10632 = [0, 400947009422, 1423652228664, 1397034956406, 348021910796, 9122066662, 0, 0] := by
  rw [show D2M8K2.u10632 = KTree.node D2M8K2.u10630 (nat_lit 23065977) (nat_lit 1851009018) (nat_lit 0) D2M8K2.u10631 from rfl, totK_node, atot10630, atot10631]
  decide +kernel

theorem arows10637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10637 = true := by
  rw [show D2M8K2.u10637 = KTree.node D2M8K2.u10635 (nat_lit 23069756) (nat_lit 3390292813) (nat_lit 0) D2M8K2.u10636 from rfl, allE_node, arows10635, irow10637, arows10636]
  all_goals rfl

theorem atot10637 : totK PD2M8K2 D2M8K2.u10637 = [0, 421920719648, 1447206789634, 1389170172785, 315663457988, 13083481006, 0, 0] := by
  rw [show D2M8K2.u10637 = KTree.node D2M8K2.u10635 (nat_lit 23069756) (nat_lit 3390292813) (nat_lit 0) D2M8K2.u10636 from rfl, totK_node, atot10635, atot10636]
  decide +kernel

theorem arows10640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10640 = true := by
  rw [show D2M8K2.u10640 = KTree.node D2M8K2.u10638 (nat_lit 23072832) (nat_lit 3689546633) (nat_lit 0) D2M8K2.u10639 from rfl, allE_node, arows10638, irow10640, arows10639]
  all_goals rfl

theorem atot10640 : totK PD2M8K2 D2M8K2.u10640 = [0, 444328224940, 1479006597519, 1368561384820, 316407486103, 13149116973, 0, 0] := by
  rw [show D2M8K2.u10640 = KTree.node D2M8K2.u10638 (nat_lit 23072832) (nat_lit 3689546633) (nat_lit 0) D2M8K2.u10639 from rfl, totK_node, atot10638, atot10639]
  decide +kernel

theorem arows10644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10644 = true := by
  rw [show D2M8K2.u10644 = KTree.node D2M8K2.u10642 (nat_lit 23080018) (nat_lit 2851069905) (nat_lit 0) D2M8K2.u10643 from rfl, allE_node, arows10642, irow10644, arows10643]
  all_goals rfl

theorem atot10644 : totK PD2M8K2 D2M8K2.u10644 = [0, 0, 708544028355, 1800496247871, 903141658191, 91067027500, 1138244013, 0] := by
  rw [show D2M8K2.u10644 = KTree.node D2M8K2.u10642 (nat_lit 23080018) (nat_lit 2851069905) (nat_lit 0) D2M8K2.u10643 from rfl, totK_node, atot10642, atot10643]
  decide +kernel

theorem arows10647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10647 = true := by
  rw [show D2M8K2.u10647 = KTree.node D2M8K2.u10645 (nat_lit 23083780) (nat_lit 3523054482) (nat_lit 0) D2M8K2.u10646 from rfl, allE_node, arows10645, irow10647, arows10646]
  all_goals rfl

theorem atot10647 : totK PD2M8K2 D2M8K2.u10647 = [0, 0, 681527400643, 1845476925567, 986923887251, 75347349020, 0, 0] := by
  rw [show D2M8K2.u10647 = KTree.node D2M8K2.u10645 (nat_lit 23083780) (nat_lit 3523054482) (nat_lit 0) D2M8K2.u10646 from rfl, totK_node, atot10645, atot10646]
  decide +kernel

theorem arows10653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10653 = true := by
  rw [show D2M8K2.u10653 = KTree.node D2M8K2.u10651 (nat_lit 23090485) (nat_lit 1258560926) (nat_lit 0) D2M8K2.u10652 from rfl, allE_node, arows10651, irow10653, arows10652]
  all_goals rfl

theorem atot10653 : totK PD2M8K2 D2M8K2.u10653 = [0, 0, 734301467719, 1897917975227, 899773461346, 52405264034, 0, 0] := by
  rw [show D2M8K2.u10653 = KTree.node D2M8K2.u10651 (nat_lit 23090485) (nat_lit 1258560926) (nat_lit 0) D2M8K2.u10652 from rfl, totK_node, atot10651, atot10652]
  decide +kernel

theorem arows10656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10656 = true := by
  rw [show D2M8K2.u10656 = KTree.node D2M8K2.u10654 (nat_lit 23095046) (nat_lit 3993540571) (nat_lit 0) D2M8K2.u10655 from rfl, allE_node, arows10654, irow10656, arows10655]
  all_goals rfl

theorem atot10656 : totK PD2M8K2 D2M8K2.u10656 = [0, 0, 442801164870, 1568773035397, 1291207364840, 220543926583, 4977114383, 0] := by
  rw [show D2M8K2.u10656 = KTree.node D2M8K2.u10654 (nat_lit 23095046) (nat_lit 3993540571) (nat_lit 0) D2M8K2.u10655 from rfl, totK_node, atot10654, atot10655]
  decide +kernel

theorem arows10660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10660 = true := by
  rw [show D2M8K2.u10660 = KTree.node D2M8K2.u10658 (nat_lit 23143713) (nat_lit 1748707704) (nat_lit 0) D2M8K2.u10659 from rfl, allE_node, arows10658, irow10660, arows10659]
  all_goals rfl

theorem atot10660 : totK PD2M8K2 D2M8K2.u10660 = [0, 0, 483618583884, 1621040050192, 1302919157387, 155762853468, 1369150432, 0] := by
  rw [show D2M8K2.u10660 = KTree.node D2M8K2.u10658 (nat_lit 23143713) (nat_lit 1748707704) (nat_lit 0) D2M8K2.u10659 from rfl, totK_node, atot10658, atot10659]
  decide +kernel

theorem arows10663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10663 = true := by
  rw [show D2M8K2.u10663 = KTree.node D2M8K2.u10661 (nat_lit 23151516) (nat_lit 3155367300) (nat_lit 0) D2M8K2.u10662 from rfl, allE_node, arows10661, irow10663, arows10662]
  all_goals rfl

theorem atot10663 : totK PD2M8K2 D2M8K2.u10663 = [0, 0, 523578951184, 1692396233393, 1230510954143, 114756856858, 1164319620, 0] := by
  rw [show D2M8K2.u10663 = KTree.node D2M8K2.u10661 (nat_lit 23151516) (nat_lit 3155367300) (nat_lit 0) D2M8K2.u10662 from rfl, totK_node, atot10661, atot10662]
  decide +kernel

theorem arows10668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10668 = true := by
  rw [show D2M8K2.u10668 = KTree.node D2M8K2.u10666 (nat_lit 23154991) (nat_lit 2426719847) (nat_lit 0) D2M8K2.u10667 from rfl, allE_node, arows10666, irow10668, arows10667]
  all_goals rfl

theorem atot10668 : totK PD2M8K2 D2M8K2.u10668 = [0, 0, 398043553617, 1417891466823, 1392111398945, 303738540262, 13184317400, 0] := by
  rw [show D2M8K2.u10668 = KTree.node D2M8K2.u10666 (nat_lit 23154991) (nat_lit 2426719847) (nat_lit 0) D2M8K2.u10667 from rfl, totK_node, atot10666, atot10667]
  decide +kernel

theorem arows10671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10671 = true := by
  rw [show D2M8K2.u10671 = KTree.node D2M8K2.u10669 (nat_lit 23158674) (nat_lit 3395057874) (nat_lit 0) D2M8K2.u10670 from rfl, allE_node, arows10669, irow10671, arows10670]
  all_goals rfl

theorem atot10671 : totK PD2M8K2 D2M8K2.u10671 = [0, 0, 380743153613, 1514191589446, 1420524494855, 242238059310, 6249254262, 0] := by
  rw [show D2M8K2.u10671 = KTree.node D2M8K2.u10669 (nat_lit 23158674) (nat_lit 3395057874) (nat_lit 0) D2M8K2.u10670 from rfl, totK_node, atot10669, atot10670]
  decide +kernel

theorem arows10675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10675 = true := by
  rw [show D2M8K2.u10675 = KTree.node D2M8K2.u10673 (nat_lit 23163251) (nat_lit 2380498459) (nat_lit 0) D2M8K2.u10674 from rfl, allE_node, arows10673, irow10675, arows10674]
  all_goals rfl

theorem atot10675 : totK PD2M8K2 D2M8K2.u10675 = [0, 0, 0, 655224029107, 1776681443257, 914384888668, 88096786128, 1209030869] := by
  rw [show D2M8K2.u10675 = KTree.node D2M8K2.u10673 (nat_lit 23163251) (nat_lit 2380498459) (nat_lit 0) D2M8K2.u10674 from rfl, totK_node, atot10673, atot10674]
  decide +kernel

theorem arows10678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10678 = true := by
  rw [show D2M8K2.u10678 = KTree.node D2M8K2.u10676 (nat_lit 23172797) (nat_lit 1308543517) (nat_lit 32) D2M8K2.u10677 from rfl, allE_node, arows10676, irow10678, arows10677]
  all_goals rfl

theorem atot10678 : totK PD2M8K2 D2M8K2.u10678 = [0, 0, 0, 934073501755, 1963109208515, 586196858565, 18589830813, 0] := by
  rw [show D2M8K2.u10678 = KTree.node D2M8K2.u10676 (nat_lit 23172797) (nat_lit 1308543517) (nat_lit 32) D2M8K2.u10677 from rfl, totK_node, atot10676, atot10677]
  decide +kernel

theorem arows10685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10685 = true := by
  rw [show D2M8K2.u10685 = KTree.node D2M8K2.u10683 (nat_lit 23180038) (nat_lit 3748874246) (nat_lit 0) D2M8K2.u10684 from rfl, allE_node, arows10683, irow10685, arows10684]
  all_goals rfl

theorem atot10685 : totK PD2M8K2 D2M8K2.u10685 = [0, 0, 268165479436, 1244535255700, 1630298621781, 428227556941, 16184734748, 0] := by
  rw [show D2M8K2.u10685 = KTree.node D2M8K2.u10683 (nat_lit 23180038) (nat_lit 3748874246) (nat_lit 0) D2M8K2.u10684 from rfl, totK_node, atot10683, atot10684]
  decide +kernel

theorem arows10688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10688 = true := by
  rw [show D2M8K2.u10688 = KTree.node D2M8K2.u10686 (nat_lit 23189120) (nat_lit 3558778235) (nat_lit 0) D2M8K2.u10687 from rfl, allE_node, arows10686, irow10688, arows10687]
  all_goals rfl

theorem atot10688 : totK PD2M8K2 D2M8K2.u10688 = [0, 0, 436406738696, 1463453376857, 1398329529270, 364672833763, 15407717105, 0] := by
  rw [show D2M8K2.u10688 = KTree.node D2M8K2.u10686 (nat_lit 23189120) (nat_lit 3558778235) (nat_lit 0) D2M8K2.u10687 from rfl, totK_node, atot10686, atot10687]
  decide +kernel

theorem arows10692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10692 = true := by
  rw [show D2M8K2.u10692 = KTree.node D2M8K2.u10690 (nat_lit 23194414) (nat_lit 3339294979) (nat_lit 0) D2M8K2.u10691 from rfl, allE_node, arows10690, irow10692, arows10691]
  all_goals rfl

theorem atot10692 : totK PD2M8K2 D2M8K2.u10692 = [0, 0, 534039069306, 1672129886429, 1253367967505, 194915879622, 7316020427, 0] := by
  rw [show D2M8K2.u10692 = KTree.node D2M8K2.u10690 (nat_lit 23194414) (nat_lit 3339294979) (nat_lit 0) D2M8K2.u10691 from rfl, totK_node, atot10690, atot10691]
  decide +kernel

theorem arows10695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10695 = true := by
  rw [show D2M8K2.u10695 = KTree.node D2M8K2.u10693 (nat_lit 23197692) (nat_lit 3045954703) (nat_lit 0) D2M8K2.u10694 from rfl, allE_node, arows10693, irow10695, arows10694]
  all_goals rfl

theorem atot10695 : totK PD2M8K2 D2M8K2.u10695 = [0, 0, 420276993930, 1565441266498, 1413574120706, 212371189828, 2566665356, 0] := by
  rw [show D2M8K2.u10695 = KTree.node D2M8K2.u10693 (nat_lit 23197692) (nat_lit 3045954703) (nat_lit 0) D2M8K2.u10694 from rfl, totK_node, atot10693, atot10694]
  decide +kernel

theorem arows10700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10700 = true := by
  rw [show D2M8K2.u10700 = KTree.node D2M8K2.u10698 (nat_lit 23224516) (nat_lit 3957779519) (nat_lit 0) D2M8K2.u10699 from rfl, allE_node, arows10698, irow10700, arows10699]
  all_goals rfl

theorem atot10700 : totK PD2M8K2 D2M8K2.u10700 = [0, 0, 726032434057, 1853572732149, 960533158702, 92109676739, 2813333534, 0] := by
  rw [show D2M8K2.u10700 = KTree.node D2M8K2.u10698 (nat_lit 23224516) (nat_lit 3957779519) (nat_lit 0) D2M8K2.u10699 from rfl, totK_node, atot10698, atot10699]
  decide +kernel

theorem arows10703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10703 = true := by
  rw [show D2M8K2.u10703 = KTree.node D2M8K2.u10701 (nat_lit 23228667) (nat_lit 3765549472) (nat_lit 0) D2M8K2.u10702 from rfl, allE_node, arows10701, irow10703, arows10702]
  all_goals rfl

theorem atot10703 : totK PD2M8K2 D2M8K2.u10703 = [0, 0, 668152134226, 1752411511737, 1127009599385, 109757791900, 1310166938, 0] := by
  rw [show D2M8K2.u10703 = KTree.node D2M8K2.u10701 (nat_lit 23228667) (nat_lit 3765549472) (nat_lit 0) D2M8K2.u10702 from rfl, totK_node, atot10701, atot10702]
  decide +kernel

theorem arows10707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10707 = true := by
  rw [show D2M8K2.u10707 = KTree.node D2M8K2.u10705 (nat_lit 23234143) (nat_lit 1494253022) (nat_lit 128) D2M8K2.u10706 from rfl, allE_node, arows10705, irow10707, arows10706]
  all_goals rfl

theorem atot10707 : totK PD2M8K2 D2M8K2.u10707 = [0, 0, 450841590067, 1589345567540, 1324245560227, 193681933236, 4626333750, 0] := by
  rw [show D2M8K2.u10707 = KTree.node D2M8K2.u10705 (nat_lit 23234143) (nat_lit 1494253022) (nat_lit 128) D2M8K2.u10706 from rfl, totK_node, atot10705, atot10706]
  decide +kernel

theorem arows10710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10710 = true := by
  rw [show D2M8K2.u10710 = KTree.node D2M8K2.u10708 (nat_lit 23241099) (nat_lit 3578171007) (nat_lit 0) D2M8K2.u10709 from rfl, allE_node, arows10708, irow10710, arows10709]
  all_goals rfl

theorem atot10710 : totK PD2M8K2 D2M8K2.u10710 = [0, 0, 455086947012, 1608678895366, 1271340707795, 187441176798, 4980514959, 0] := by
  rw [show D2M8K2.u10710 = KTree.node D2M8K2.u10708 (nat_lit 23241099) (nat_lit 3578171007) (nat_lit 0) D2M8K2.u10709 from rfl, totK_node, atot10708, atot10709]
  decide +kernel

theorem arows10716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10716 = true := by
  rw [show D2M8K2.u10716 = KTree.node D2M8K2.u10714 (nat_lit 23269635) (nat_lit 3724153277) (nat_lit 0) D2M8K2.u10715 from rfl, allE_node, arows10714, irow10716, arows10715]
  all_goals rfl

theorem atot10716 : totK PD2M8K2 D2M8K2.u10716 = [0, 0, 493535951165, 1632540861380, 1344138475061, 161194756071, 1310517177, 0] := by
  rw [show D2M8K2.u10716 = KTree.node D2M8K2.u10714 (nat_lit 23269635) (nat_lit 3724153277) (nat_lit 0) D2M8K2.u10715 from rfl, totK_node, atot10714, atot10715]
  decide +kernel

theorem arows10719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10719 = true := by
  rw [show D2M8K2.u10719 = KTree.node D2M8K2.u10717 (nat_lit 23276303) (nat_lit 2704808284) (nat_lit 0) D2M8K2.u10718 from rfl, allE_node, arows10717, irow10719, arows10718]
  all_goals rfl

theorem atot10719 : totK PD2M8K2 D2M8K2.u10719 = [0, 0, 439553000454, 1487077771185, 1372738804687, 340940222397, 15066332673, 0] := by
  rw [show D2M8K2.u10719 = KTree.node D2M8K2.u10717 (nat_lit 23276303) (nat_lit 2704808284) (nat_lit 0) D2M8K2.u10718 from rfl, totK_node, atot10717, atot10718]
  decide +kernel

theorem arows10723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10723 = true := by
  rw [show D2M8K2.u10723 = KTree.node D2M8K2.u10721 (nat_lit 23279470) (nat_lit 4051426970) (nat_lit 0) D2M8K2.u10722 from rfl, allE_node, arows10721, irow10723, arows10722]
  all_goals rfl

theorem atot10723 : totK PD2M8K2 D2M8K2.u10723 = [0, 0, 381589446547, 1388670400772, 1453131102343, 333664287774, 13170675918, 0] := by
  rw [show D2M8K2.u10723 = KTree.node D2M8K2.u10721 (nat_lit 23279470) (nat_lit 4051426970) (nat_lit 0) D2M8K2.u10722 from rfl, totK_node, atot10721, atot10722]
  decide +kernel

theorem arows10726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10726 = true := by
  rw [show D2M8K2.u10726 = KTree.node D2M8K2.u10724 (nat_lit 23283146) (nat_lit 3322212002) (nat_lit 0) D2M8K2.u10725 from rfl, allE_node, arows10724, irow10726, arows10725]
  all_goals rfl

theorem atot10726 : totK PD2M8K2 D2M8K2.u10726 = [0, 0, 381050790233, 1523981076844, 1460544943525, 234995513223, 4980514959, 0] := by
  rw [show D2M8K2.u10726 = KTree.node D2M8K2.u10724 (nat_lit 23283146) (nat_lit 3322212002) (nat_lit 0) D2M8K2.u10725 from rfl, totK_node, atot10724, atot10725]
  decide +kernel

theorem arows10731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10731 = true := by
  rw [show D2M8K2.u10731 = KTree.node D2M8K2.u10729 (nat_lit 23308114) (nat_lit 2832035146) (nat_lit 0) D2M8K2.u10730 from rfl, allE_node, arows10729, irow10731, arows10730]
  all_goals rfl

theorem atot10731 : totK PD2M8K2 D2M8K2.u10731 = [0, 0, 408328961613, 1475916654123, 1361438453781, 262564463585, 6261201934, 0] := by
  rw [show D2M8K2.u10731 = KTree.node D2M8K2.u10729 (nat_lit 23308114) (nat_lit 2832035146) (nat_lit 0) D2M8K2.u10730 from rfl, totK_node, atot10729, atot10730]
  decide +kernel

theorem arows10734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10734 = true := by
  rw [show D2M8K2.u10734 = KTree.node D2M8K2.u10732 (nat_lit 23311756) (nat_lit 3241367379) (nat_lit 0) D2M8K2.u10733 from rfl, allE_node, arows10732, irow10734, arows10733]
  all_goals rfl

theorem atot10734 : totK PD2M8K2 D2M8K2.u10734 = [0, 0, 418043516444, 1510924242136, 1420535956230, 267582339277, 12570117775, 0] := by
  rw [show D2M8K2.u10734 = KTree.node D2M8K2.u10732 (nat_lit 23311756) (nat_lit 3241367379) (nat_lit 0) D2M8K2.u10733 from rfl, totK_node, atot10732, atot10733]
  decide +kernel

theorem arows10738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10738 = true := by
  rw [show D2M8K2.u10738 = KTree.node D2M8K2.u10736 (nat_lit 23315017) (nat_lit 1415546622) (nat_lit 0) D2M8K2.u10737 from rfl, allE_node, arows10736, irow10738, arows10737]
  all_goals rfl

theorem atot10738 : totK PD2M8K2 D2M8K2.u10738 = [0, 0, 395769665482, 1475025850771, 1413414807868, 263380793240, 4663960312, 0] := by
  rw [show D2M8K2.u10738 = KTree.node D2M8K2.u10736 (nat_lit 23315017) (nat_lit 1415546622) (nat_lit 0) D2M8K2.u10737 from rfl, totK_node, atot10736, atot10737]
  decide +kernel

theorem arows10741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10741 = true := by
  rw [show D2M8K2.u10741 = KTree.node D2M8K2.u10739 (nat_lit 23318980) (nat_lit 3814314246) (nat_lit 0) D2M8K2.u10740 from rfl, allE_node, arows10739, irow10741, arows10740]
  all_goals rfl

theorem atot10741 : totK PD2M8K2 D2M8K2.u10741 = [0, 0, 417198856696, 1460764438115, 1367765489247, 285194450507, 13021542929, 0] := by
  rw [show D2M8K2.u10741 = KTree.node D2M8K2.u10739 (nat_lit 23318980) (nat_lit 3814314246) (nat_lit 0) D2M8K2.u10740 from rfl, totK_node, atot10739, atot10740]
  decide +kernel

theorem arows10751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10751 = true := by
  rw [show D2M8K2.u10751 = KTree.node D2M8K2.u10749 (nat_lit 23322101) (nat_lit 1141709988) (nat_lit 0) D2M8K2.u10750 from rfl, allE_node, arows10749, irow10751, arows10750]
  all_goals rfl

theorem atot10751 : totK PD2M8K2 D2M8K2.u10751 = [0, 0, 441947594641, 1593555064246, 1384691581166, 200730870644, 3666196603, 0] := by
  rw [show D2M8K2.u10751 = KTree.node D2M8K2.u10749 (nat_lit 23322101) (nat_lit 1141709988) (nat_lit 0) D2M8K2.u10750 from rfl, totK_node, atot10749, atot10750]
  decide +kernel

theorem arows10754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10754 = true := by
  rw [show D2M8K2.u10754 = KTree.node D2M8K2.u10752 (nat_lit 23329370) (nat_lit 3534179579) (nat_lit 0) D2M8K2.u10753 from rfl, allE_node, arows10752, irow10754, arows10753]
  all_goals rfl

theorem atot10754 : totK PD2M8K2 D2M8K2.u10754 = [0, 0, 0, 530719614516, 1745849501555, 1030826200416, 101140930502, 1138244013] := by
  rw [show D2M8K2.u10754 = KTree.node D2M8K2.u10752 (nat_lit 23329370) (nat_lit 3534179579) (nat_lit 0) D2M8K2.u10753 from rfl, totK_node, atot10752, atot10753]
  decide +kernel

theorem arows10758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10758 = true := by
  rw [show D2M8K2.u10758 = KTree.node D2M8K2.u10756 (nat_lit 23335545) (nat_lit 1851009018) (nat_lit 0) D2M8K2.u10757 from rfl, allE_node, arows10756, irow10758, arows10757]
  all_goals rfl

theorem atot10758 : totK PD2M8K2 D2M8K2.u10758 = [0, 0, 0, 965934945620, 1914518341082, 627887800562, 26846841466, 0] := by
  rw [show D2M8K2.u10758 = KTree.node D2M8K2.u10756 (nat_lit 23335545) (nat_lit 1851009018) (nat_lit 0) D2M8K2.u10757 from rfl, totK_node, atot10756, atot10757]
  decide +kernel

theorem arows10761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10761 = true := by
  rw [show D2M8K2.u10761 = KTree.node D2M8K2.u10759 (nat_lit 23342505) (nat_lit 1907412261) (nat_lit 0) D2M8K2.u10760 from rfl, allE_node, arows10759, irow10761, arows10760]
  all_goals rfl

theorem atot10761 : totK PD2M8K2 D2M8K2.u10761 = [0, 0, 0, 589486079508, 1763473041576, 1034399287475, 104436955926, 1095107716] := by
  rw [show D2M8K2.u10761 = KTree.node D2M8K2.u10759 (nat_lit 23342505) (nat_lit 1907412261) (nat_lit 0) D2M8K2.u10760 from rfl, totK_node, atot10759, atot10760]
  decide +kernel

theorem arows10766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10766 = true := by
  rw [show D2M8K2.u10766 = KTree.node D2M8K2.u10764 (nat_lit 23391312) (nat_lit 3388576300) (nat_lit 0) D2M8K2.u10765 from rfl, allE_node, arows10764, irow10766, arows10765]
  all_goals rfl

theorem atot10766 : totK PD2M8K2 D2M8K2.u10766 = [0, 433494320846, 1375575433638, 1039505538742, 305383629576, 320113192939, 93467172928, 3882006667] := by
  rw [show D2M8K2.u10766 = KTree.node D2M8K2.u10764 (nat_lit 23391312) (nat_lit 3388576300) (nat_lit 0) D2M8K2.u10765 from rfl, totK_node, atot10764, atot10765]
  decide +kernel

theorem arows10769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10769 = true := by
  rw [show D2M8K2.u10769 = KTree.node D2M8K2.u10767 (nat_lit 23398438) (nat_lit 1207084470) (nat_lit 0) D2M8K2.u10768 from rfl, allE_node, arows10767, irow10769, arows10768]
  all_goals rfl

theorem atot10769 : totK PD2M8K2 D2M8K2.u10769 = [0, 381332262321, 1469737898894, 1462430344653, 266004858088, 5398830306, 0, 0] := by
  rw [show D2M8K2.u10769 = KTree.node D2M8K2.u10767 (nat_lit 23398438) (nat_lit 1207084470) (nat_lit 0) D2M8K2.u10768 from rfl, totK_node, atot10767, atot10768]
  decide +kernel

theorem arows10773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10773 = true := by
  rw [show D2M8K2.u10773 = KTree.node D2M8K2.u10771 (nat_lit 23402064) (nat_lit 3449098627) (nat_lit 0) D2M8K2.u10772 from rfl, allE_node, arows10771, irow10773, arows10772]
  all_goals rfl

theorem atot10773 : totK PD2M8K2 D2M8K2.u10773 = [0, 414487218621, 1443312292541, 1394611789384, 331444689104, 13250685261, 0, 0] := by
  rw [show D2M8K2.u10773 = KTree.node D2M8K2.u10771 (nat_lit 23402064) (nat_lit 3449098627) (nat_lit 0) D2M8K2.u10772 from rfl, totK_node, atot10771, atot10772]
  decide +kernel

theorem arows10776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10776 = true := by
  rw [show D2M8K2.u10776 = KTree.node D2M8K2.u10774 (nat_lit 23405830) (nat_lit 2974097589) (nat_lit 0) D2M8K2.u10775 from rfl, allE_node, arows10774, irow10776, arows10775]
  all_goals rfl

theorem atot10776 : totK PD2M8K2 D2M8K2.u10776 = [0, 484616115433, 1593189265936, 1276364722462, 220884023167, 4980514959, 0, 0] := by
  rw [show D2M8K2.u10776 = KTree.node D2M8K2.u10774 (nat_lit 23405830) (nat_lit 2974097589) (nat_lit 0) D2M8K2.u10775 from rfl, totK_node, atot10774, atot10775]
  decide +kernel

theorem arows10782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10782 = true := by
  rw [show D2M8K2.u10782 = KTree.node D2M8K2.u10780 (nat_lit 23409532) (nat_lit 3858311637) (nat_lit 0) D2M8K2.u10781 from rfl, allE_node, arows10780, irow10782, arows10781]
  all_goals rfl

theorem atot10782 : totK PD2M8K2 D2M8K2.u10782 = [0, 264732260305, 1212603072239, 1591450728112, 489679728713, 23418599596, 0, 0] := by
  rw [show D2M8K2.u10782 = KTree.node D2M8K2.u10780 (nat_lit 23409532) (nat_lit 3858311637) (nat_lit 0) D2M8K2.u10781 from rfl, totK_node, atot10780, atot10781]
  decide +kernel

theorem arows10785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10785 = true := by
  rw [show D2M8K2.u10785 = KTree.node D2M8K2.u10783 (nat_lit 23412680) (nat_lit 3573890142) (nat_lit 0) D2M8K2.u10784 from rfl, allE_node, arows10783, irow10785, arows10784]
  all_goals rfl

theorem atot10785 : totK PD2M8K2 D2M8K2.u10785 = [0, 0, 481006309873, 1659628039025, 1189979928120, 150366152548, 1369150432, 0] := by
  rw [show D2M8K2.u10785 = KTree.node D2M8K2.u10783 (nat_lit 23412680) (nat_lit 3573890142) (nat_lit 0) D2M8K2.u10784 from rfl, totK_node, atot10783, atot10784]
  decide +kernel

theorem arows10789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10789 = true := by
  rw [show D2M8K2.u10789 = KTree.node D2M8K2.u10787 (nat_lit 23421739) (nat_lit 1594779421) (nat_lit 0) D2M8K2.u10788 from rfl, allE_node, arows10787, irow10789, arows10788]
  all_goals rfl

theorem atot10789 : totK PD2M8K2 D2M8K2.u10789 = [0, 0, 739646709023, 1905381539192, 883319753964, 43625642079, 0, 0] := by
  rw [show D2M8K2.u10789 = KTree.node D2M8K2.u10787 (nat_lit 23421739) (nat_lit 1594779421) (nat_lit 0) D2M8K2.u10788 from rfl, totK_node, atot10787, atot10788]
  decide +kernel

theorem arows10792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10792 = true := by
  rw [show D2M8K2.u10792 = KTree.node D2M8K2.u10790 (nat_lit 23428721) (nat_lit 1317402923) (nat_lit 0) D2M8K2.u10791 from rfl, allE_node, arows10790, irow10792, arows10791]
  all_goals rfl

theorem atot10792 : totK PD2M8K2 D2M8K2.u10792 = [0, 94311201580, 868586700752, 1782292492162, 805464390755, 43284976356, 0, 0] := by
  rw [show D2M8K2.u10792 = KTree.node D2M8K2.u10790 (nat_lit 23428721) (nat_lit 1317402923) (nat_lit 0) D2M8K2.u10791 from rfl, totK_node, atot10790, atot10791]
  decide +kernel

theorem arows10797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10797 = true := by
  rw [show D2M8K2.u10797 = KTree.node D2M8K2.u10795 (nat_lit 23436852) (nat_lit 3032192815) (nat_lit 0) D2M8K2.u10796 from rfl, allE_node, arows10795, irow10797, arows10796]
  all_goals rfl

theorem atot10797 : totK PD2M8K2 D2M8K2.u10797 = [0, 348582227776, 1315753810145, 1460514632139, 484982058893, 30804453458, 0, 0] := by
  rw [show D2M8K2.u10797 = KTree.node D2M8K2.u10795 (nat_lit 23436852) (nat_lit 3032192815) (nat_lit 0) D2M8K2.u10796 from rfl, totK_node, atot10795, atot10796]
  decide +kernel

theorem arows10800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10800 = true := by
  rw [show D2M8K2.u10800 = KTree.node D2M8K2.u10798 (nat_lit 23439989) (nat_lit 2221120622) (nat_lit 0) D2M8K2.u10799 from rfl, allE_node, arows10798, irow10800, arows10799]
  all_goals rfl

theorem atot10800 : totK PD2M8K2 D2M8K2.u10800 = [0, 385641170734, 1393721656325, 1451277319581, 387553128969, 16284769718, 0, 0] := by
  rw [show D2M8K2.u10800 = KTree.node D2M8K2.u10798 (nat_lit 23439989) (nat_lit 2221120622) (nat_lit 0) D2M8K2.u10799 from rfl, totK_node, atot10798, atot10799]
  decide +kernel

theorem arows10804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10804 = true := by
  rw [show D2M8K2.u10804 = KTree.node D2M8K2.u10802 (nat_lit 23443518) (nat_lit 3910760504) (nat_lit 0) D2M8K2.u10803 from rfl, allE_node, arows10802, irow10804, arows10803]
  all_goals rfl

theorem atot10804 : totK PD2M8K2 D2M8K2.u10804 = [0, 417373317570, 1454379976835, 1422199623181, 327776763206, 13204088881, 0, 0] := by
  rw [show D2M8K2.u10804 = KTree.node D2M8K2.u10802 (nat_lit 23443518) (nat_lit 3910760504) (nat_lit 0) D2M8K2.u10803 from rfl, totK_node, atot10802, atot10803]
  decide +kernel

theorem arows10807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10807 = true := by
  rw [show D2M8K2.u10807 = KTree.node D2M8K2.u10805 (nat_lit 23446904) (nat_lit 3930769992) (nat_lit 0) D2M8K2.u10806 from rfl, allE_node, arows10805, irow10807, arows10806]
  all_goals rfl

theorem atot10807 : totK PD2M8K2 D2M8K2.u10807 = [0, 492063843306, 1644164105273, 1367031365333, 210487094388, 2804045914, 0, 0] := by
  rw [show D2M8K2.u10807 = KTree.node D2M8K2.u10805 (nat_lit 23446904) (nat_lit 3930769992) (nat_lit 0) D2M8K2.u10806 from rfl, totK_node, atot10805, atot10806]
  decide +kernel

theorem arows10814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10814 = true := by
  rw [show D2M8K2.u10814 = KTree.node D2M8K2.u10812 (nat_lit 23451029) (nat_lit 2357672697) (nat_lit 0) D2M8K2.u10813 from rfl, allE_node, arows10812, irow10814, arows10813]
  all_goals rfl

theorem atot10814 : totK PD2M8K2 D2M8K2.u10814 = [0, 265593258125, 1220286265080, 1585291937594, 500805105018, 32500486747, 0, 0] := by
  rw [show D2M8K2.u10814 = KTree.node D2M8K2.u10812 (nat_lit 23451029) (nat_lit 2357672697) (nat_lit 0) D2M8K2.u10813 from rfl, totK_node, atot10812, atot10813]
  decide +kernel

theorem arows10817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10817 = true := by
  rw [show D2M8K2.u10817 = KTree.node D2M8K2.u10815 (nat_lit 23457576) (nat_lit 3249684915) (nat_lit 0) D2M8K2.u10816 from rfl, allE_node, arows10815, irow10817, arows10816]
  all_goals rfl

theorem atot10817 : totK PD2M8K2 D2M8K2.u10817 = [0, 0, 347675481477, 1340272118611, 1474163800344, 442422925684, 26567849899, 0] := by
  rw [show D2M8K2.u10817 = KTree.node D2M8K2.u10815 (nat_lit 23457576) (nat_lit 3249684915) (nat_lit 0) D2M8K2.u10816 from rfl, totK_node, atot10815, atot10816]
  decide +kernel

theorem arows10821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10821 = true := by
  rw [show D2M8K2.u10821 = KTree.node D2M8K2.u10819 (nat_lit 23460788) (nat_lit 1295897737) (nat_lit 0) D2M8K2.u10820 from rfl, allE_node, arows10819, irow10821, arows10820]
  all_goals rfl

theorem atot10821 : totK PD2M8K2 D2M8K2.u10821 = [0, 0, 452365236014, 1554701750333, 1358098768541, 258045286461, 8071924064, 0] := by
  rw [show D2M8K2.u10821 = KTree.node D2M8K2.u10819 (nat_lit 23460788) (nat_lit 1295897737) (nat_lit 0) D2M8K2.u10820 from rfl, totK_node, atot10819, atot10820]
  decide +kernel

theorem arows10824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10824 = true := by
  rw [show D2M8K2.u10824 = KTree.node D2M8K2.u10822 (nat_lit 23464516) (nat_lit 2670825932) (nat_lit 0) D2M8K2.u10823 from rfl, allE_node, arows10822, irow10824, arows10823]
  all_goals rfl

theorem atot10824 : totK PD2M8K2 D2M8K2.u10824 = [0, 0, 438032303486, 1536290493773, 1411060168112, 263615132979, 5218872685, 0] := by
  rw [show D2M8K2.u10824 = KTree.node D2M8K2.u10822 (nat_lit 23464516) (nat_lit 2670825932) (nat_lit 0) D2M8K2.u10823 from rfl, totK_node, atot10822, atot10823]
  decide +kernel

theorem arows10829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10829 = true := by
  rw [show D2M8K2.u10829 = KTree.node D2M8K2.u10827 (nat_lit 23469125) (nat_lit 1565018379) (nat_lit 32) D2M8K2.u10828 from rfl, allE_node, arows10827, irow10829, arows10828]
  all_goals rfl

theorem atot10829 : totK PD2M8K2 D2M8K2.u10829 = [0, 0, 568618712159, 1704106732689, 1234022617800, 157315092720, 1415142070, 0] := by
  rw [show D2M8K2.u10829 = KTree.node D2M8K2.u10827 (nat_lit 23469125) (nat_lit 1565018379) (nat_lit 32) D2M8K2.u10828 from rfl, totK_node, atot10827, atot10828]
  decide +kernel

theorem arows10832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10832 = true := by
  rw [show D2M8K2.u10832 = KTree.node D2M8K2.u10830 (nat_lit 23472871) (nat_lit 1836506383) (nat_lit 0) D2M8K2.u10831 from rfl, allE_node, arows10830, irow10832, arows10831]
  all_goals rfl

theorem atot10832 : totK PD2M8K2 D2M8K2.u10832 = [0, 309149030834, 825028539918, 1058891841917, 1078090047417, 288595232983, 9302370699, 0] := by
  rw [show D2M8K2.u10832 = KTree.node D2M8K2.u10830 (nat_lit 23472871) (nat_lit 1836506383) (nat_lit 0) D2M8K2.u10831 from rfl, totK_node, atot10830, atot10831]
  decide +kernel

theorem arows10836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10836 = true := by
  rw [show D2M8K2.u10836 = KTree.node D2M8K2.u10834 (nat_lit 23476925) (nat_lit 2300159181) (nat_lit 0) D2M8K2.u10835 from rfl, allE_node, arows10834, irow10836, arows10835]
  all_goals rfl

theorem atot10836 : totK PD2M8K2 D2M8K2.u10836 = [0, 495200462687, 1613001127716, 1352204614571, 181294454749, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10836 = KTree.node D2M8K2.u10834 (nat_lit 23476925) (nat_lit 2300159181) (nat_lit 0) D2M8K2.u10835 from rfl, totK_node, atot10834, atot10835]
  decide +kernel

theorem arows10839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10839 = true := by
  rw [show D2M8K2.u10839 = KTree.node D2M8K2.u10837 (nat_lit 23479792) (nat_lit 3238611622) (nat_lit 0) D2M8K2.u10838 from rfl, allE_node, arows10837, irow10839, arows10838]
  all_goals rfl

theorem atot10839 : totK PD2M8K2 D2M8K2.u10839 = [0, 300095866282, 1225025595252, 1514487075963, 557322385546, 33580559210, 0, 0] := by
  rw [show D2M8K2.u10839 = KTree.node D2M8K2.u10837 (nat_lit 23479792) (nat_lit 3238611622) (nat_lit 0) D2M8K2.u10838 from rfl, totK_node, atot10837, atot10838]
  decide +kernel

theorem arows10845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10845 = true := by
  rw [show D2M8K2.u10845 = KTree.node D2M8K2.u10843 (nat_lit 23482960) (nat_lit 3328303018) (nat_lit 0) D2M8K2.u10844 from rfl, allE_node, arows10843, irow10845, arows10844]
  all_goals rfl

theorem atot10845 : totK PD2M8K2 D2M8K2.u10845 = [0, 422840269799, 1516697622727, 1410525827413, 275052477922, 9587713104, 0, 0] := by
  rw [show D2M8K2.u10845 = KTree.node D2M8K2.u10843 (nat_lit 23482960) (nat_lit 3328303018) (nat_lit 0) D2M8K2.u10844 from rfl, totK_node, atot10843, atot10844]
  decide +kernel

theorem arows10848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10848 = true := by
  rw [show D2M8K2.u10848 = KTree.node D2M8K2.u10846 (nat_lit 23493037) (nat_lit 1339629267) (nat_lit 0) D2M8K2.u10847 from rfl, allE_node, arows10846, irow10848, arows10847]
  all_goals rfl

theorem atot10848 : totK PD2M8K2 D2M8K2.u10848 = [0, 130424248025, 1041419624935, 1771143712877, 610320934177, 27658950063, 0, 0] := by
  rw [show D2M8K2.u10848 = KTree.node D2M8K2.u10846 (nat_lit 23493037) (nat_lit 1339629267) (nat_lit 0) D2M8K2.u10847 from rfl, totK_node, atot10846, atot10847]
  decide +kernel

theorem arows10852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10852 = true := by
  rw [show D2M8K2.u10852 = KTree.node D2M8K2.u10850 (nat_lit 23497086) (nat_lit 3163101909) (nat_lit 0) D2M8K2.u10851 from rfl, allE_node, arows10850, irow10852, arows10851]
  all_goals rfl

theorem atot10852 : totK PD2M8K2 D2M8K2.u10852 = [0, 0, 509173656485, 1701265073201, 1239639505521, 124208136111, 1206465782, 0] := by
  rw [show D2M8K2.u10852 = KTree.node D2M8K2.u10850 (nat_lit 23497086) (nat_lit 3163101909) (nat_lit 0) D2M8K2.u10851 from rfl, totK_node, atot10850, atot10851]
  decide +kernel

theorem arows10855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10855 = true := by
  rw [show D2M8K2.u10855 = KTree.node D2M8K2.u10853 (nat_lit 23502049) (nat_lit 1487679972) (nat_lit 0) D2M8K2.u10854 from rfl, allE_node, arows10853, irow10855, arows10854]
  all_goals rfl

theorem atot10855 : totK PD2M8K2 D2M8K2.u10855 = [0, 0, 472506244306, 1609654305778, 1278477493093, 202985400697, 5395128787, 0] := by
  rw [show D2M8K2.u10855 = KTree.node D2M8K2.u10853 (nat_lit 23502049) (nat_lit 1487679972) (nat_lit 0) D2M8K2.u10854 from rfl, totK_node, atot10853, atot10854]
  decide +kernel

theorem arows10860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10860 = true := by
  rw [show D2M8K2.u10860 = KTree.node D2M8K2.u10858 (nat_lit 23512617) (nat_lit 1427528045) (nat_lit 0) D2M8K2.u10859 from rfl, allE_node, arows10858, irow10860, arows10859]
  all_goals rfl

theorem atot10860 : totK PD2M8K2 D2M8K2.u10860 = [0, 302668140502, 1129677326392, 1450009057491, 668332886135, 55936084231, 0, 0] := by
  rw [show D2M8K2.u10860 = KTree.node D2M8K2.u10858 (nat_lit 23512617) (nat_lit 1427528045) (nat_lit 0) D2M8K2.u10859 from rfl, totK_node, atot10858, atot10859]
  decide +kernel

theorem arows10863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10863 = true := by
  rw [show D2M8K2.u10863 = KTree.node D2M8K2.u10861 (nat_lit 23517850) (nat_lit 3949216340) (nat_lit 0) D2M8K2.u10862 from rfl, allE_node, arows10861, irow10863, arows10862]
  all_goals rfl

theorem atot10863 : totK PD2M8K2 D2M8K2.u10863 = [0, 450759994184, 1594029227232, 1389662119941, 192191889381, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10863 = KTree.node D2M8K2.u10861 (nat_lit 23517850) (nat_lit 3949216340) (nat_lit 0) D2M8K2.u10862 from rfl, totK_node, atot10861, atot10862]
  decide +kernel

theorem arows10867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10867 = true := by
  rw [show D2M8K2.u10867 = KTree.node D2M8K2.u10865 (nat_lit 23521028) (nat_lit 3302524520) (nat_lit 0) D2M8K2.u10866 from rfl, allE_node, arows10865, irow10867, arows10866]
  all_goals rfl

theorem atot10867 : totK PD2M8K2 D2M8K2.u10867 = [0, 342631798119, 1234474861650, 1471613296902, 577538716532, 36020842901, 0, 0] := by
  rw [show D2M8K2.u10867 = KTree.node D2M8K2.u10865 (nat_lit 23521028) (nat_lit 3302524520) (nat_lit 0) D2M8K2.u10866 from rfl, totK_node, atot10865, atot10866]
  decide +kernel

theorem arows10870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10870 = true := by
  rw [show D2M8K2.u10870 = KTree.node D2M8K2.u10868 (nat_lit 23527668) (nat_lit 3218112320) (nat_lit 0) D2M8K2.u10869 from rfl, allE_node, arows10868, irow10870, arows10869]
  all_goals rfl

theorem atot10870 : totK PD2M8K2 D2M8K2.u10870 = [0, 353036533279, 1405973414664, 1491318479362, 348978104919, 13250685261, 0, 0] := by
  rw [show D2M8K2.u10870 = KTree.node D2M8K2.u10868 (nat_lit 23527668) (nat_lit 3218112320) (nat_lit 0) D2M8K2.u10869 from rfl, totK_node, atot10868, atot10869]
  decide +kernel

theorem arows10878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10878 = true := by
  rw [show D2M8K2.u10878 = KTree.node D2M8K2.u10876 (nat_lit 23531419) (nat_lit 2118184586) (nat_lit 0) D2M8K2.u10877 from rfl, allE_node, arows10876, irow10878, arows10877]
  all_goals rfl

theorem atot10878 : totK PD2M8K2 D2M8K2.u10878 = [0, 494516690551, 1610104634504, 1310721297521, 214389267984, 4980514959, 0, 0] := by
  rw [show D2M8K2.u10878 = KTree.node D2M8K2.u10876 (nat_lit 23531419) (nat_lit 2118184586) (nat_lit 0) D2M8K2.u10877 from rfl, totK_node, atot10876, atot10877]
  decide +kernel

theorem arows10881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10881 = true := by
  rw [show D2M8K2.u10881 = KTree.node D2M8K2.u10879 (nat_lit 23534649) (nat_lit 1135263285) (nat_lit 0) D2M8K2.u10880 from rfl, allE_node, arows10879, irow10881, arows10880]
  all_goals rfl

theorem atot10881 : totK PD2M8K2 D2M8K2.u10881 = [0, 92934196222, 957785918274, 1814024998583, 675118848778, 33125647945, 0, 0] := by
  rw [show D2M8K2.u10881 = KTree.node D2M8K2.u10879 (nat_lit 23534649) (nat_lit 1135263285) (nat_lit 0) D2M8K2.u10880 from rfl, totK_node, atot10879, atot10880]
  decide +kernel

theorem arows10885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10885 = true := by
  rw [show D2M8K2.u10885 = KTree.node D2M8K2.u10883 (nat_lit 23538563) (nat_lit 2875397828) (nat_lit 0) D2M8K2.u10884 from rfl, allE_node, arows10883, irow10885, arows10884]
  all_goals rfl

theorem atot10885 : totK PD2M8K2 D2M8K2.u10885 = [0, 0, 499433546739, 1660195514435, 1271770864187, 147882682201, 1239866073, 0] := by
  rw [show D2M8K2.u10885 = KTree.node D2M8K2.u10883 (nat_lit 23538563) (nat_lit 2875397828) (nat_lit 0) D2M8K2.u10884 from rfl, totK_node, atot10883, atot10884]
  decide +kernel

theorem arows10888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10888 = true := by
  rw [show D2M8K2.u10888 = KTree.node D2M8K2.u10886 (nat_lit 23546915) (nat_lit 2215404135) (nat_lit 0) D2M8K2.u10887 from rfl, allE_node, arows10886, irow10888, arows10887]
  all_goals rfl

theorem atot10888 : totK PD2M8K2 D2M8K2.u10888 = [0, 0, 505712294413, 1581992232257, 1261237586732, 237498158873, 9633262574, 0] := by
  rw [show D2M8K2.u10888 = KTree.node D2M8K2.u10886 (nat_lit 23546915) (nat_lit 2215404135) (nat_lit 0) D2M8K2.u10887 from rfl, totK_node, atot10886, atot10887]
  decide +kernel

theorem arows10893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10893 = true := by
  rw [show D2M8K2.u10893 = KTree.node D2M8K2.u10891 (nat_lit 23550313) (nat_lit 1377460593) (nat_lit 0) D2M8K2.u10892 from rfl, allE_node, arows10891, irow10893, arows10892]
  all_goals rfl

theorem atot10893 : totK PD2M8K2 D2M8K2.u10893 = [0, 0, 426691085335, 1494408890566, 1339451827830, 258501695907, 8192806269, 0] := by
  rw [show D2M8K2.u10893 = KTree.node D2M8K2.u10891 (nat_lit 23550313) (nat_lit 1377460593) (nat_lit 0) D2M8K2.u10892 from rfl, totK_node, atot10891, atot10892]
  decide +kernel

theorem arows10896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10896 = true := by
  rw [show D2M8K2.u10896 = KTree.node D2M8K2.u10894 (nat_lit 23554296) (nat_lit 3415880598) (nat_lit 0) D2M8K2.u10895 from rfl, allE_node, arows10894, irow10896, arows10895]
  all_goals rfl

theorem atot10896 : totK PD2M8K2 D2M8K2.u10896 = [0, 369552279963, 1228960849361, 1359720880057, 592369580199, 46796999697, 0, 0] := by
  rw [show D2M8K2.u10896 = KTree.node D2M8K2.u10894 (nat_lit 23554296) (nat_lit 3415880598) (nat_lit 0) D2M8K2.u10895 from rfl, totK_node, atot10894, atot10895]
  decide +kernel

theorem arows10900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10900 = true := by
  rw [show D2M8K2.u10900 = KTree.node D2M8K2.u10898 (nat_lit 23601415) (nat_lit 2318075366) (nat_lit 0) D2M8K2.u10899 from rfl, allE_node, arows10898, irow10900, arows10899]
  all_goals rfl

theorem atot10900 : totK PD2M8K2 D2M8K2.u10900 = [0, 466186703583, 1603337400715, 1375347700523, 190262227213, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10900 = KTree.node D2M8K2.u10898 (nat_lit 23601415) (nat_lit 2318075366) (nat_lit 0) D2M8K2.u10899 from rfl, totK_node, atot10898, atot10899]
  decide +kernel

theorem arows10903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10903 = true := by
  rw [show D2M8K2.u10903 = KTree.node D2M8K2.u10901 (nat_lit 23604164) (nat_lit 3536208251) (nat_lit 0) D2M8K2.u10902 from rfl, allE_node, arows10901, irow10903, arows10902]
  all_goals rfl

theorem atot10903 : totK PD2M8K2 D2M8K2.u10903 = [0, 277239998783, 1181255445939, 1523068477356, 583599673803, 35968611740, 0, 0] := by
  rw [show D2M8K2.u10903 = KTree.node D2M8K2.u10901 (nat_lit 23604164) (nat_lit 3536208251) (nat_lit 0) D2M8K2.u10902 from rfl, totK_node, atot10901, atot10902]
  decide +kernel

theorem arows10909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10909 = true := by
  rw [show D2M8K2.u10909 = KTree.node D2M8K2.u10907 (nat_lit 23607408) (nat_lit 3449245705) (nat_lit 0) D2M8K2.u10908 from rfl, allE_node, arows10907, irow10909, arows10908]
  all_goals rfl

theorem atot10909 : totK PD2M8K2 D2M8K2.u10909 = [0, 425161961252, 1466887215922, 1405147872958, 295852392902, 8812418916, 0, 0] := by
  rw [show D2M8K2.u10909 = KTree.node D2M8K2.u10907 (nat_lit 23607408) (nat_lit 3449245705) (nat_lit 0) D2M8K2.u10908 from rfl, totK_node, atot10907, atot10908]
  decide +kernel

theorem arows10912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10912 = true := by
  rw [show D2M8K2.u10912 = KTree.node D2M8K2.u10910 (nat_lit 23610838) (nat_lit 2479991301) (nat_lit 0) D2M8K2.u10911 from rfl, allE_node, arows10910, irow10912, arows10911]
  all_goals rfl

theorem atot10912 : totK PD2M8K2 D2M8K2.u10912 = [0, 388472373461, 1435182828558, 1452325294184, 339662768699, 13216353549, 0, 0] := by
  rw [show D2M8K2.u10912 = KTree.node D2M8K2.u10910 (nat_lit 23610838) (nat_lit 2479991301) (nat_lit 0) D2M8K2.u10911 from rfl, totK_node, atot10910, atot10911]
  decide +kernel

theorem arows10916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10916 = true := by
  rw [show D2M8K2.u10916 = KTree.node D2M8K2.u10914 (nat_lit 23617290) (nat_lit 3208515040) (nat_lit 0) D2M8K2.u10915 from rfl, allE_node, arows10914, irow10916, arows10915]
  all_goals rfl

theorem atot10916 : totK PD2M8K2 D2M8K2.u10916 = [0, 182497872290, 1105755740039, 1714748202442, 581998662359, 25695472006, 0, 0] := by
  rw [show D2M8K2.u10916 = KTree.node D2M8K2.u10914 (nat_lit 23617290) (nat_lit 3208515040) (nat_lit 0) D2M8K2.u10915 from rfl, totK_node, atot10914, atot10915]
  decide +kernel

theorem arows10919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10919 = true := by
  rw [show D2M8K2.u10919 = KTree.node D2M8K2.u10917 (nat_lit 23620729) (nat_lit 1493958301) (nat_lit 0) D2M8K2.u10918 from rfl, allE_node, arows10917, irow10919, arows10918]
  all_goals rfl

theorem atot10919 : totK PD2M8K2 D2M8K2.u10919 = [0, 0, 487889323390, 1608392236960, 1303799622382, 154159018354, 1310285577, 0] := by
  rw [show D2M8K2.u10919 = KTree.node D2M8K2.u10917 (nat_lit 23620729) (nat_lit 1493958301) (nat_lit 0) D2M8K2.u10918 from rfl, totK_node, atot10917, atot10918]
  decide +kernel

theorem arows10924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10924 = true := by
  rw [show D2M8K2.u10924 = KTree.node D2M8K2.u10922 (nat_lit 23625762) (nat_lit 1917839299) (nat_lit 0) D2M8K2.u10923 from rfl, allE_node, arows10922, irow10924, arows10923]
  all_goals rfl

theorem atot10924 : totK PD2M8K2 D2M8K2.u10924 = [0, 0, 569634274012, 1737479526011, 1161298193938, 121647551418, 1075657031, 0] := by
  rw [show D2M8K2.u10924 = KTree.node D2M8K2.u10922 (nat_lit 23625762) (nat_lit 1917839299) (nat_lit 0) D2M8K2.u10923 from rfl, totK_node, atot10922, atot10923]
  decide +kernel

theorem arows10927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10927 = true := by
  rw [show D2M8K2.u10927 = KTree.node D2M8K2.u10925 (nat_lit 23629680) (nat_lit 3669537395) (nat_lit 0) D2M8K2.u10926 from rfl, allE_node, arows10925, irow10927, arows10926]
  all_goals rfl

theorem atot10927 : totK PD2M8K2 D2M8K2.u10927 = [0, 0, 420899002102, 1522080640135, 1380432993838, 236010317235, 4911340522, 0] := by
  rw [show D2M8K2.u10927 = KTree.node D2M8K2.u10925 (nat_lit 23629680) (nat_lit 3669537395) (nat_lit 0) D2M8K2.u10926 from rfl, totK_node, atot10925, atot10926]
  decide +kernel

theorem arows10931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10931 = true := by
  rw [show D2M8K2.u10931 = KTree.node D2M8K2.u10929 (nat_lit 23636448) (nat_lit 3691789053) (nat_lit 0) D2M8K2.u10930 from rfl, allE_node, arows10929, irow10931, arows10930]
  all_goals rfl

theorem atot10931 : totK PD2M8K2 D2M8K2.u10931 = [0, 0, 445470339543, 1548762551119, 1354769287422, 248366032864, 5013799328, 0] := by
  rw [show D2M8K2.u10931 = KTree.node D2M8K2.u10929 (nat_lit 23636448) (nat_lit 3691789053) (nat_lit 0) D2M8K2.u10930 from rfl, totK_node, atot10929, atot10930]
  decide +kernel

theorem arows10934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10934 = true := by
  rw [show D2M8K2.u10934 = KTree.node D2M8K2.u10932 (nat_lit 23888742) (nat_lit 3866735348) (nat_lit 0) D2M8K2.u10933 from rfl, allE_node, arows10932, irow10934, arows10933]
  all_goals rfl

theorem atot10934 : totK PD2M8K2 D2M8K2.u10934 = [442400928062, 1270137119403, 844219017458, 292567145230, 475460965020, 240942723549, 19507788969, 0] := by
  rw [show D2M8K2.u10934 = KTree.node D2M8K2.u10932 (nat_lit 23888742) (nat_lit 3866735348) (nat_lit 0) D2M8K2.u10933 from rfl, totK_node, atot10932, atot10933]
  decide +kernel

theorem arows10941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10941 = true := by
  rw [show D2M8K2.u10941 = KTree.node D2M8K2.u10939 (nat_lit 23895485) (nat_lit 2326292714) (nat_lit 0) D2M8K2.u10940 from rfl, allE_node, arows10939, irow10941, arows10940]
  all_goals rfl

theorem atot10941 : totK PD2M8K2 D2M8K2.u10941 = [416609623085, 1567687521504, 1422760096559, 198112051422, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u10941 = KTree.node D2M8K2.u10939 (nat_lit 23895485) (nat_lit 2326292714) (nat_lit 0) D2M8K2.u10940 from rfl, totK_node, atot10939, atot10940]
  decide +kernel

theorem arows10944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10944 = true := by
  rw [show D2M8K2.u10944 = KTree.node D2M8K2.u10942 (nat_lit 23899147) (nat_lit 1817206615) (nat_lit 0) D2M8K2.u10943 from rfl, allE_node, arows10942, irow10944, arows10943]
  all_goals rfl

theorem atot10944 : totK PD2M8K2 D2M8K2.u10944 = [416815572402, 1424947339379, 1378490840905, 324042010549, 13083481006, 0, 0, 0] := by
  rw [show D2M8K2.u10944 = KTree.node D2M8K2.u10942 (nat_lit 23899147) (nat_lit 1817206615) (nat_lit 0) D2M8K2.u10943 from rfl, totK_node, atot10942, atot10943]
  decide +kernel

theorem arows10948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10948 = true := by
  rw [show D2M8K2.u10948 = KTree.node D2M8K2.u10946 (nat_lit 23902221) (nat_lit 1159574512) (nat_lit 0) D2M8K2.u10947 from rfl, allE_node, arows10946, irow10948, arows10947]
  all_goals rfl

theorem atot10948 : totK PD2M8K2 D2M8K2.u10948 = [419025644943, 1443586456092, 1372755940254, 320117694183, 13149116973, 0, 0, 0] := by
  rw [show D2M8K2.u10948 = KTree.node D2M8K2.u10946 (nat_lit 23902221) (nat_lit 1159574512) (nat_lit 0) D2M8K2.u10947 from rfl, totK_node, atot10946, atot10947]
  decide +kernel

theorem arows10951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10951 = true := by
  rw [show D2M8K2.u10951 = KTree.node D2M8K2.u10949 (nat_lit 23905793) (nat_lit 2222962290) (nat_lit 0) D2M8K2.u10950 from rfl, allE_node, arows10949, irow10951, arows10950]
  all_goals rfl

theorem atot10951 : totK PD2M8K2 D2M8K2.u10951 = [402087814747, 1488751254681, 1428407507534, 258322902731, 5152749158, 0, 0, 0] := by
  rw [show D2M8K2.u10951 = KTree.node D2M8K2.u10949 (nat_lit 23905793) (nat_lit 2222962290) (nat_lit 0) D2M8K2.u10950 from rfl, totK_node, atot10949, atot10950]
  decide +kernel

theorem arows10956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10956 = true := by
  rw [show D2M8K2.u10956 = KTree.node D2M8K2.u10954 (nat_lit 23909294) (nat_lit 3356880169) (nat_lit 0) D2M8K2.u10955 from rfl, allE_node, arows10954, irow10956, arows10955]
  all_goals rfl

theorem atot10956 : totK PD2M8K2 D2M8K2.u10956 = [0, 673971983032, 1820884430079, 950313833807, 72421663005, 0, 0, 0] := by
  rw [show D2M8K2.u10956 = KTree.node D2M8K2.u10954 (nat_lit 23909294) (nat_lit 3356880169) (nat_lit 0) D2M8K2.u10955 from rfl, totK_node, atot10954, atot10955]
  decide +kernel

theorem arows10959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10959 = true := by
  rw [show D2M8K2.u10959 = KTree.node D2M8K2.u10957 (nat_lit 23916125) (nat_lit 2332668471) (nat_lit 0) D2M8K2.u10958 from rfl, allE_node, arows10957, irow10959, arows10958]
  all_goals rfl

theorem atot10959 : totK PD2M8K2 D2M8K2.u10959 = [0, 565536747795, 1704804363605, 1118004345153, 140728952064, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10959 = KTree.node D2M8K2.u10957 (nat_lit 23916125) (nat_lit 2332668471) (nat_lit 0) D2M8K2.u10958 from rfl, totK_node, atot10957, atot10958]
  decide +kernel

theorem arows10963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10963 = true := by
  rw [show D2M8K2.u10963 = KTree.node D2M8K2.u10961 (nat_lit 23922655) (nat_lit 2358867197) (nat_lit 0) D2M8K2.u10962 from rfl, allE_node, arows10961, irow10963, arows10962]
  all_goals rfl

theorem atot10963 : totK PD2M8K2 D2M8K2.u10963 = [0, 738266520216, 1878503080723, 886588717731, 48805668711, 0, 0, 0] := by
  rw [show D2M8K2.u10963 = KTree.node D2M8K2.u10961 (nat_lit 23922655) (nat_lit 2358867197) (nat_lit 0) D2M8K2.u10962 from rfl, totK_node, atot10961, atot10962]
  decide +kernel

theorem arows10966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10966 = true := by
  rw [show D2M8K2.u10966 = KTree.node D2M8K2.u10964 (nat_lit 23927562) (nat_lit 3440438767) (nat_lit 0) D2M8K2.u10965 from rfl, allE_node, arows10964, irow10966, arows10965]
  all_goals rfl

theorem atot10966 : totK PD2M8K2 D2M8K2.u10966 = [384126823169, 1261567792460, 1360814788725, 525490252663, 29733020022, 0, 0, 0] := by
  rw [show D2M8K2.u10966 = KTree.node D2M8K2.u10964 (nat_lit 23927562) (nat_lit 3440438767) (nat_lit 0) D2M8K2.u10965 from rfl, totK_node, atot10964, atot10965]
  decide +kernel

theorem arows10972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10972 = true := by
  rw [show D2M8K2.u10972 = KTree.node D2M8K2.u10970 (nat_lit 23974670) (nat_lit 3885436770) (nat_lit 0) D2M8K2.u10971 from rfl, allE_node, arows10970, irow10972, arows10971]
  all_goals rfl

theorem atot10972 : totK PD2M8K2 D2M8K2.u10972 = [365836653275, 1507514862604, 1500715199668, 256584028467, 11808139943, 0, 0, 0] := by
  rw [show D2M8K2.u10972 = KTree.node D2M8K2.u10970 (nat_lit 23974670) (nat_lit 3885436770) (nat_lit 0) D2M8K2.u10971 from rfl, totK_node, atot10970, atot10971]
  decide +kernel

theorem arows10975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10975 = true := by
  rw [show D2M8K2.u10975 = KTree.node D2M8K2.u10973 (nat_lit 23978090) (nat_lit 4000375028) (nat_lit 0) D2M8K2.u10974 from rfl, allE_node, arows10973, irow10975, arows10974]
  all_goals rfl

theorem atot10975 : totK PD2M8K2 D2M8K2.u10975 = [437503876744, 1410892705108, 1331827823597, 422656771362, 21804665281, 0, 0, 0] := by
  rw [show D2M8K2.u10975 = KTree.node D2M8K2.u10973 (nat_lit 23978090) (nat_lit 4000375028) (nat_lit 0) D2M8K2.u10974 from rfl, totK_node, atot10973, atot10974]
  decide +kernel

theorem arows10979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10979 = true := by
  rw [show D2M8K2.u10979 = KTree.node D2M8K2.u10977 (nat_lit 23984791) (nat_lit 2196233502) (nat_lit 0) D2M8K2.u10978 from rfl, allE_node, arows10977, irow10979, arows10978]
  all_goals rfl

theorem atot10979 : totK PD2M8K2 D2M8K2.u10979 = [412164631822, 1439128354516, 1401610235784, 325444852444, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u10979 = KTree.node D2M8K2.u10977 (nat_lit 23984791) (nat_lit 2196233502) (nat_lit 0) D2M8K2.u10978 from rfl, totK_node, atot10977, atot10978]
  decide +kernel

theorem arows10982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10982 = true := by
  rw [show D2M8K2.u10982 = KTree.node D2M8K2.u10980 (nat_lit 23988411) (nat_lit 3787378992) (nat_lit 0) D2M8K2.u10981 from rfl, allE_node, arows10980, irow10982, arows10981]
  all_goals rfl

theorem atot10982 : totK PD2M8K2 D2M8K2.u10982 = [383112678408, 1471224550579, 1475183891428, 269126021630, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u10982 = KTree.node D2M8K2.u10980 (nat_lit 23988411) (nat_lit 3787378992) (nat_lit 0) D2M8K2.u10981 from rfl, totK_node, atot10980, atot10981]
  decide +kernel

theorem arows10987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10987 = true := by
  rw [show D2M8K2.u10987 = KTree.node D2M8K2.u10985 (nat_lit 23991775) (nat_lit 2281162491) (nat_lit 0) D2M8K2.u10986 from rfl, allE_node, arows10985, irow10987, arows10986]
  all_goals rfl

theorem atot10987 : totK PD2M8K2 D2M8K2.u10987 = [0, 713716700104, 1860885376177, 890215268092, 53048597959, 0, 0, 0] := by
  rw [show D2M8K2.u10987 = KTree.node D2M8K2.u10985 (nat_lit 23991775) (nat_lit 2281162491) (nat_lit 0) D2M8K2.u10986 from rfl, totK_node, atot10985, atot10986]
  decide +kernel

theorem arows10990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10990 = true := by
  rw [show D2M8K2.u10990 = KTree.node D2M8K2.u10988 (nat_lit 23995759) (nat_lit 1646453180) (nat_lit 0) D2M8K2.u10989 from rfl, allE_node, arows10988, irow10990, arows10989]
  all_goals rfl

theorem atot10990 : totK PD2M8K2 D2M8K2.u10990 = [0, 536761780062, 1680984173670, 1230358772100, 147470317936, 1206465782, 0, 0] := by
  rw [show D2M8K2.u10990 = KTree.node D2M8K2.u10988 (nat_lit 23995759) (nat_lit 1646453180) (nat_lit 0) D2M8K2.u10989 from rfl, totK_node, atot10988, atot10989]
  decide +kernel

theorem arows10994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10994 = true := by
  rw [show D2M8K2.u10994 = KTree.node D2M8K2.u10992 (nat_lit 24000774) (nat_lit 2335061250) (nat_lit 0) D2M8K2.u10993 from rfl, allE_node, arows10992, irow10994, arows10993]
  all_goals rfl

theorem atot10994 : totK PD2M8K2 D2M8K2.u10994 = [0, 392537568586, 1458318761616, 1354470382532, 301904346836, 13016197374, 0, 0] := by
  rw [show D2M8K2.u10994 = KTree.node D2M8K2.u10992 (nat_lit 24000774) (nat_lit 2335061250) (nat_lit 0) D2M8K2.u10993 from rfl, totK_node, atot10992, atot10993]
  decide +kernel

theorem arows10997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10997 = true := by
  rw [show D2M8K2.u10997 = KTree.node D2M8K2.u10995 (nat_lit 24007708) (nat_lit 3929634213) (nat_lit 0) D2M8K2.u10996 from rfl, allE_node, arows10995, irow10997, arows10996]
  all_goals rfl

theorem atot10997 : totK PD2M8K2 D2M8K2.u10997 = [0, 484882979022, 1592053082044, 1246856128593, 186649652505, 4574395652, 0, 0] := by
  rw [show D2M8K2.u10997 = KTree.node D2M8K2.u10995 (nat_lit 24007708) (nat_lit 3929634213) (nat_lit 0) D2M8K2.u10996 from rfl, totK_node, atot10995, atot10996]
  decide +kernel

theorem arows11006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11006 = true := by
  rw [show D2M8K2.u11006 = KTree.node D2M8K2.u11004 (nat_lit 24013272) (nat_lit 3561687974) (nat_lit 0) D2M8K2.u11005 from rfl, allE_node, arows11004, irow11006, arows11005]
  all_goals rfl

theorem atot11006 : totK PD2M8K2 D2M8K2.u11006 = [419052346373, 1414362712609, 1331782312386, 382877401891, 23690856139, 0, 0, 0] := by
  rw [show D2M8K2.u11006 = KTree.node D2M8K2.u11004 (nat_lit 24013272) (nat_lit 3561687974) (nat_lit 0) D2M8K2.u11005 from rfl, totK_node, atot11004, atot11005]
  decide +kernel

theorem arows11009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11009 = true := by
  rw [show D2M8K2.u11009 = KTree.node D2M8K2.u11007 (nat_lit 24017071) (nat_lit 2064580359) (nat_lit 0) D2M8K2.u11008 from rfl, allE_node, arows11007, irow11009, arows11008]
  all_goals rfl

theorem atot11009 : totK PD2M8K2 D2M8K2.u11009 = [331084880840, 1349603689517, 1520026157404, 432912715915, 26712625787, 0, 0, 0] := by
  rw [show D2M8K2.u11009 = KTree.node D2M8K2.u11007 (nat_lit 24017071) (nat_lit 2064580359) (nat_lit 0) D2M8K2.u11008 from rfl, totK_node, atot11007, atot11008]
  decide +kernel

theorem arows11013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11013 = true := by
  rw [show D2M8K2.u11013 = KTree.node D2M8K2.u11011 (nat_lit 24023913) (nat_lit 1918754987) (nat_lit 0) D2M8K2.u11012 from rfl, allE_node, arows11011, irow11013, arows11012]
  all_goals rfl

theorem atot11013 : totK PD2M8K2 D2M8K2.u11013 = [437683919179, 1463246769400, 1374936512987, 337874266711, 15227376525, 0, 0, 0] := by
  rw [show D2M8K2.u11013 = KTree.node D2M8K2.u11011 (nat_lit 24023913) (nat_lit 1918754987) (nat_lit 0) D2M8K2.u11012 from rfl, totK_node, atot11011, atot11012]
  decide +kernel

theorem arows11016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11016 = true := by
  rw [show D2M8K2.u11016 = KTree.node D2M8K2.u11014 (nat_lit 24027014) (nat_lit 4124106855) (nat_lit 0) D2M8K2.u11015 from rfl, allE_node, arows11014, irow11016, arows11015]
  all_goals rfl

theorem atot11016 : totK PD2M8K2 D2M8K2.u11016 = [412219636167, 1515764397629, 1420327876308, 248683853524, 4678454933, 0, 0, 0] := by
  rw [show D2M8K2.u11016 = KTree.node D2M8K2.u11014 (nat_lit 24027014) (nat_lit 4124106855) (nat_lit 0) D2M8K2.u11015 from rfl, totK_node, atot11014, atot11015]
  decide +kernel

theorem arows11021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11021 = true := by
  rw [show D2M8K2.u11021 = KTree.node D2M8K2.u11019 (nat_lit 24030673) (nat_lit 1368630800) (nat_lit 0) D2M8K2.u11020 from rfl, allE_node, arows11019, irow11021, arows11020]
  all_goals rfl

theorem atot11021 : totK PD2M8K2 D2M8K2.u11021 = [383209705629, 1365333338908, 1431530257180, 383612629878, 12592023492, 0, 0, 0] := by
  rw [show D2M8K2.u11021 = KTree.node D2M8K2.u11019 (nat_lit 24030673) (nat_lit 1368630800) (nat_lit 0) D2M8K2.u11020 from rfl, totK_node, atot11019, atot11020]
  decide +kernel

theorem arows11024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11024 = true := by
  rw [show D2M8K2.u11024 = KTree.node D2M8K2.u11022 (nat_lit 24034269) (nat_lit 1569723249) (nat_lit 0) D2M8K2.u11023 from rfl, allE_node, arows11022, irow11024, arows11023]
  all_goals rfl

theorem atot11024 : totK PD2M8K2 D2M8K2.u11024 = [0, 493137427762, 1666745227281, 1211994695599, 131595904277, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11024 = KTree.node D2M8K2.u11022 (nat_lit 24034269) (nat_lit 1569723249) (nat_lit 0) D2M8K2.u11023 from rfl, totK_node, atot11022, atot11023]
  decide +kernel

theorem arows11028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11028 = true := by
  rw [show D2M8K2.u11028 = KTree.node D2M8K2.u11026 (nat_lit 24043471) (nat_lit 2432819833) (nat_lit 0) D2M8K2.u11027 from rfl, allE_node, arows11026, irow11028, arows11027]
  all_goals rfl

theorem atot11028 : totK PD2M8K2 D2M8K2.u11028 = [0, 746123483165, 1852472331479, 966970091968, 80735945443, 0, 0, 0] := by
  rw [show D2M8K2.u11028 = KTree.node D2M8K2.u11026 (nat_lit 24043471) (nat_lit 2432819833) (nat_lit 0) D2M8K2.u11027 from rfl, totK_node, atot11026, atot11027]
  decide +kernel

theorem arows11031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11031 = true := by
  rw [show D2M8K2.u11031 = KTree.node D2M8K2.u11029 (nat_lit 24046635) (nat_lit 3563570232) (nat_lit 0) D2M8K2.u11030 from rfl, allE_node, arows11029, irow11031, arows11030]
  all_goals rfl

theorem atot11031 : totK PD2M8K2 D2M8K2.u11031 = [0, 395608592811, 1438904266380, 1377292985044, 308162045141, 13105450397, 0, 0] := by
  rw [show D2M8K2.u11031 = KTree.node D2M8K2.u11029 (nat_lit 24046635) (nat_lit 3563570232) (nat_lit 0) D2M8K2.u11030 from rfl, totK_node, atot11029, atot11030]
  decide +kernel

theorem arows11037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11037 = true := by
  rw [show D2M8K2.u11037 = KTree.node D2M8K2.u11035 (nat_lit 24050430) (nat_lit 3853262279) (nat_lit 0) D2M8K2.u11036 from rfl, allE_node, arows11035, irow11037, arows11036]
  all_goals rfl

theorem atot11037 : totK PD2M8K2 D2M8K2.u11037 = [33270956665, 450688473567, 1520921536415, 1318003237079, 205168552170, 4720618446, 0, 0] := by
  rw [show D2M8K2.u11037 = KTree.node D2M8K2.u11035 (nat_lit 24050430) (nat_lit 3853262279) (nat_lit 0) D2M8K2.u11036 from rfl, totK_node, atot11035, atot11036]
  decide +kernel

theorem arows11040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11040 = true := by
  rw [show D2M8K2.u11040 = KTree.node D2M8K2.u11038 (nat_lit 24055337) (nat_lit 1622298826) (nat_lit 0) D2M8K2.u11039 from rfl, allE_node, arows11038, irow11040, arows11039]
  all_goals rfl

theorem atot11040 : totK PD2M8K2 D2M8K2.u11040 = [477911446045, 1623314241949, 1321187861822, 184978686114, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11040 = KTree.node D2M8K2.u11038 (nat_lit 24055337) (nat_lit 1622298826) (nat_lit 0) D2M8K2.u11039 from rfl, totK_node, atot11038, atot11039]
  decide +kernel

theorem arows11044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11044 = true := by
  rw [show D2M8K2.u11044 = KTree.node D2M8K2.u11042 (nat_lit 24059466) (nat_lit 3684653648) (nat_lit 0) D2M8K2.u11043 from rfl, allE_node, arows11042, irow11044, arows11043]
  all_goals rfl

theorem atot11044 : totK PD2M8K2 D2M8K2.u11044 = [390666113089, 1356399829692, 1405065246340, 470188781510, 30668976266, 0, 0, 0] := by
  rw [show D2M8K2.u11044 = KTree.node D2M8K2.u11042 (nat_lit 24059466) (nat_lit 3684653648) (nat_lit 0) D2M8K2.u11043 from rfl, totK_node, atot11042, atot11043]
  decide +kernel

theorem arows11047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11047 = true := by
  rw [show D2M8K2.u11047 = KTree.node D2M8K2.u11045 (nat_lit 24062557) (nat_lit 1164319620) (nat_lit 0) D2M8K2.u11046 from rfl, allE_node, arows11045, irow11047, arows11046]
  all_goals rfl

theorem atot11047 : totK PD2M8K2 D2M8K2.u11047 = [382011959102, 1416983791755, 1430068371389, 331446485102, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11047 = KTree.node D2M8K2.u11045 (nat_lit 24062557) (nat_lit 1164319620) (nat_lit 0) D2M8K2.u11046 from rfl, totK_node, atot11045, atot11046]
  decide +kernel

theorem arows11052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11052 = true := by
  rw [show D2M8K2.u11052 = KTree.node D2M8K2.u11050 (nat_lit 24065979) (nat_lit 2253959612) (nat_lit 0) D2M8K2.u11051 from rfl, allE_node, arows11050, irow11052, arows11051]
  all_goals rfl

theorem atot11052 : totK PD2M8K2 D2M8K2.u11052 = [390232367976, 1414556518146, 1422063433168, 343284819363, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u11052 = KTree.node D2M8K2.u11050 (nat_lit 24065979) (nat_lit 2253959612) (nat_lit 0) D2M8K2.u11051 from rfl, totK_node, atot11050, atot11051]
  decide +kernel

theorem arows11055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11055 = true := by
  rw [show D2M8K2.u11055 = KTree.node D2M8K2.u11053 (nat_lit 24069318) (nat_lit 3735160554) (nat_lit 0) D2M8K2.u11054 from rfl, allE_node, arows11053, irow11055, arows11054]
  all_goals rfl

theorem atot11055 : totK PD2M8K2 D2M8K2.u11055 = [352446817612, 1443926475543, 1531857291333, 306789783476, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u11055 = KTree.node D2M8K2.u11053 (nat_lit 24069318) (nat_lit 3735160554) (nat_lit 0) D2M8K2.u11054 from rfl, totK_node, atot11053, atot11054]
  decide +kernel

theorem arows11059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11059 = true := by
  rw [show D2M8K2.u11059 = KTree.node D2M8K2.u11057 (nat_lit 24076320) (nat_lit 3619169329) (nat_lit 0) D2M8K2.u11058 from rfl, allE_node, arows11057, irow11059, arows11058]
  all_goals rfl

theorem atot11059 : totK PD2M8K2 D2M8K2.u11059 = [0, 502522482228, 1697154899323, 1198220408979, 136359118472, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11059 = KTree.node D2M8K2.u11057 (nat_lit 24076320) (nat_lit 3619169329) (nat_lit 0) D2M8K2.u11058 from rfl, totK_node, atot11057, atot11058]
  decide +kernel

theorem arows11062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11062 = true := by
  rw [show D2M8K2.u11062 = KTree.node D2M8K2.u11060 (nat_lit 24082083) (nat_lit 3642048460) (nat_lit 0) D2M8K2.u11061 from rfl, allE_node, arows11060, irow11062, arows11061]
  all_goals rfl

theorem atot11062 : totK PD2M8K2 D2M8K2.u11062 = [0, 747038845530, 1904776862302, 894603410198, 49449212648, 0, 0, 0] := by
  rw [show D2M8K2.u11062 = KTree.node D2M8K2.u11060 (nat_lit 24082083) (nat_lit 3642048460) (nat_lit 0) D2M8K2.u11061 from rfl, totK_node, atot11060, atot11061]
  decide +kernel

theorem arows11069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11069 = true := by
  rw [show D2M8K2.u11069 = KTree.node D2M8K2.u11067 (nat_lit 24088712) (nat_lit 3911629605) (nat_lit 0) D2M8K2.u11068 from rfl, allE_node, arows11067, irow11069, arows11068]
  all_goals rfl

theorem atot11069 : totK PD2M8K2 D2M8K2.u11069 = [0, 682100227909, 1831030326138, 984612891675, 70262784296, 0, 0, 0] := by
  rw [show D2M8K2.u11069 = KTree.node D2M8K2.u11067 (nat_lit 24088712) (nat_lit 3911629605) (nat_lit 0) D2M8K2.u11068 from rfl, totK_node, atot11067, atot11068]
  decide +kernel

theorem arows11072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11072 = true := by
  rw [show D2M8K2.u11072 = KTree.node D2M8K2.u11070 (nat_lit 24095941) (nat_lit 1354964743) (nat_lit 0) D2M8K2.u11071 from rfl, allE_node, arows11070, irow11072, arows11071]
  all_goals rfl

theorem atot11072 : totK PD2M8K2 D2M8K2.u11072 = [421327836975, 1165140487855, 1070727710233, 720806253213, 171519235798, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11072 = KTree.node D2M8K2.u11070 (nat_lit 24095941) (nat_lit 1354964743) (nat_lit 0) D2M8K2.u11071 from rfl, totK_node, atot11070, atot11071]
  decide +kernel

theorem arows11076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11076 = true := by
  rw [show D2M8K2.u11076 = KTree.node D2M8K2.u11074 (nat_lit 24102762) (nat_lit 2436672091) (nat_lit 0) D2M8K2.u11075 from rfl, allE_node, arows11074, irow11076, arows11075]
  all_goals rfl

theorem atot11076 : totK PD2M8K2 D2M8K2.u11076 = [401301423914, 1544559087323, 1456023902242, 212943988838, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u11076 = KTree.node D2M8K2.u11074 (nat_lit 24102762) (nat_lit 2436672091) (nat_lit 0) D2M8K2.u11075 from rfl, totK_node, atot11074, atot11075]
  decide +kernel

theorem arows11079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11079 = true := by
  rw [show D2M8K2.u11079 = KTree.node D2M8K2.u11077 (nat_lit 24106511) (nat_lit 2135693947) (nat_lit 0) D2M8K2.u11078 from rfl, allE_node, arows11077, irow11079, arows11078]
  all_goals rfl

theorem atot11079 : totK PD2M8K2 D2M8K2.u11079 = [401552586407, 1428673841763, 1410848603123, 334229043024, 13077537112, 0, 0, 0] := by
  rw [show D2M8K2.u11079 = KTree.node D2M8K2.u11077 (nat_lit 24106511) (nat_lit 2135693947) (nat_lit 0) D2M8K2.u11078 from rfl, totK_node, atot11077, atot11078]
  decide +kernel

theorem arows11084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11084 = true := by
  rw [show D2M8K2.u11084 = KTree.node D2M8K2.u11082 (nat_lit 24113127) (nat_lit 3620048808) (nat_lit 0) D2M8K2.u11083 from rfl, allE_node, arows11082, irow11084, arows11083]
  all_goals rfl

theorem atot11084 : totK PD2M8K2 D2M8K2.u11084 = [427832996020, 1448671184979, 1380603864540, 338322262381, 13314450774, 0, 0, 0] := by
  rw [show D2M8K2.u11084 = KTree.node D2M8K2.u11082 (nat_lit 24113127) (nat_lit 3620048808) (nat_lit 0) D2M8K2.u11083 from rfl, totK_node, atot11082, atot11083]
  decide +kernel

theorem arows11087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11087 = true := by
  rw [show D2M8K2.u11087 = KTree.node D2M8K2.u11085 (nat_lit 24116573) (nat_lit 2318335839) (nat_lit 0) D2M8K2.u11086 from rfl, allE_node, arows11085, irow11087, arows11086]
  all_goals rfl

theorem atot11087 : totK PD2M8K2 D2M8K2.u11087 = [0, 703240051929, 1852599391219, 938232152394, 61336483602, 0, 0, 0] := by
  rw [show D2M8K2.u11087 = KTree.node D2M8K2.u11085 (nat_lit 24116573) (nat_lit 2318335839) (nat_lit 0) D2M8K2.u11086 from rfl, totK_node, atot11085, atot11086]
  decide +kernel

theorem arows11091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11091 = true := by
  rw [show D2M8K2.u11091 = KTree.node D2M8K2.u11089 (nat_lit 24123468) (nat_lit 3550206895) (nat_lit 0) D2M8K2.u11090 from rfl, allE_node, arows11089, irow11091, arows11090]
  all_goals rfl

theorem atot11091 : totK PD2M8K2 D2M8K2.u11091 = [0, 399678947550, 1528390251791, 1426901846421, 196559652839, 2385942608, 0, 0] := by
  rw [show D2M8K2.u11091 = KTree.node D2M8K2.u11089 (nat_lit 24123468) (nat_lit 3550206895) (nat_lit 0) D2M8K2.u11090 from rfl, totK_node, atot11089, atot11090]
  decide +kernel

theorem arows11094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11094 = true := by
  rw [show D2M8K2.u11094 = KTree.node D2M8K2.u11092 (nat_lit 24127371) (nat_lit 3719515635) (nat_lit 0) D2M8K2.u11093 from rfl, allE_node, arows11092, irow11094, arows11093]
  all_goals rfl

theorem atot11094 : totK PD2M8K2 D2M8K2.u11094 = [0, 399936289926, 1464907800892, 1400671614120, 270672852827, 5965167776, 0, 0] := by
  rw [show D2M8K2.u11094 = KTree.node D2M8K2.u11092 (nat_lit 24127371) (nat_lit 3719515635) (nat_lit 0) D2M8K2.u11093 from rfl, totK_node, atot11092, atot11093]
  decide +kernel

theorem arows11100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11100 = true := by
  rw [show D2M8K2.u11100 = KTree.node D2M8K2.u11098 (nat_lit 24134197) (nat_lit 1252430826) (nat_lit 0) D2M8K2.u11099 from rfl, allE_node, arows11098, irow11100, arows11099]
  all_goals rfl

theorem atot11100 : totK PD2M8K2 D2M8K2.u11100 = [0, 426020582414, 1511648430234, 1362856478293, 256962940556, 6501696267, 0, 0] := by
  rw [show D2M8K2.u11100 = KTree.node D2M8K2.u11098 (nat_lit 24134197) (nat_lit 1252430826) (nat_lit 0) D2M8K2.u11099 from rfl, totK_node, atot11098, atot11099]
  decide +kernel

theorem arows11103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11103 = true := by
  rw [show D2M8K2.u11103 = KTree.node D2M8K2.u11101 (nat_lit 24137673) (nat_lit 1896608936) (nat_lit 0) D2M8K2.u11102 from rfl, allE_node, arows11101, irow11103, arows11102]
  all_goals rfl

theorem atot11103 : totK PD2M8K2 D2M8K2.u11103 = [0, 441289674660, 1465620128391, 1322064965924, 335699256072, 18308503379, 0, 0] := by
  rw [show D2M8K2.u11103 = KTree.node D2M8K2.u11101 (nat_lit 24137673) (nat_lit 1896608936) (nat_lit 0) D2M8K2.u11102 from rfl, totK_node, atot11101, atot11102]
  decide +kernel

theorem arows11107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11107 = true := by
  rw [show D2M8K2.u11107 = KTree.node D2M8K2.u11105 (nat_lit 24144435) (nat_lit 2534830668) (nat_lit 0) D2M8K2.u11106 from rfl, allE_node, arows11105, irow11107, arows11106]
  all_goals rfl

theorem atot11107 : totK PD2M8K2 D2M8K2.u11107 = [0, 414345694352, 1541489370540, 1416336115787, 204232486182, 2309606161, 0, 0] := by
  rw [show D2M8K2.u11107 = KTree.node D2M8K2.u11105 (nat_lit 24144435) (nat_lit 2534830668) (nat_lit 0) D2M8K2.u11106 from rfl, totK_node, atot11105, atot11106]
  decide +kernel

theorem arows11110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11110 = true := by
  rw [show D2M8K2.u11110 = KTree.node D2M8K2.u11108 (nat_lit 24148109) (nat_lit 969971931) (nat_lit 0) D2M8K2.u11109 from rfl, allE_node, arows11108, irow11110, arows11109]
  all_goals rfl

theorem atot11110 : totK PD2M8K2 D2M8K2.u11110 = [0, 414555051017, 1469975273169, 1382232530633, 263625845852, 11780125240, 0, 0] := by
  rw [show D2M8K2.u11110 = KTree.node D2M8K2.u11108 (nat_lit 24148109) (nat_lit 969971931) (nat_lit 0) D2M8K2.u11109 from rfl, totK_node, atot11108, atot11109]
  decide +kernel

theorem arows11115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11115 = true := by
  rw [show D2M8K2.u11115 = KTree.node D2M8K2.u11113 (nat_lit 24151236) (nat_lit 3140386521) (nat_lit 0) D2M8K2.u11114 from rfl, allE_node, arows11113, irow11115, arows11114]
  all_goals rfl

theorem atot11115 : totK PD2M8K2 D2M8K2.u11115 = [0, 416024550253, 1449323358540, 1374087130483, 279320491755, 12990811517, 0, 0] := by
  rw [show D2M8K2.u11115 = KTree.node D2M8K2.u11113 (nat_lit 24151236) (nat_lit 3140386521) (nat_lit 0) D2M8K2.u11114 from rfl, totK_node, atot11113, atot11114]
  decide +kernel

theorem arows11118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11118 = true := by
  rw [show D2M8K2.u11118 = KTree.node D2M8K2.u11116 (nat_lit 24154853) (nat_lit 1970790573) (nat_lit 0) D2M8K2.u11117 from rfl, allE_node, arows11116, irow11118, arows11117]
  all_goals rfl

theorem atot11118 : totK PD2M8K2 D2M8K2.u11118 = [0, 400053701674, 1434753160865, 1407344283767, 284923584201, 8766581130, 0, 0] := by
  rw [show D2M8K2.u11118 = KTree.node D2M8K2.u11116 (nat_lit 24154853) (nat_lit 1970790573) (nat_lit 0) D2M8K2.u11117 from rfl, totK_node, atot11116, atot11117]
  decide +kernel

theorem arows11122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11122 = true := by
  rw [show D2M8K2.u11122 = KTree.node D2M8K2.u11120 (nat_lit 24158382) (nat_lit 4071740195) (nat_lit 0) D2M8K2.u11121 from rfl, allE_node, arows11120, irow11122, arows11121]
  all_goals rfl

theorem atot11122 : totK PD2M8K2 D2M8K2.u11122 = [0, 0, 606823021014, 1709610222494, 1025300968955, 140281769223, 1369150432, 0] := by
  rw [show D2M8K2.u11122 = KTree.node D2M8K2.u11120 (nat_lit 24158382) (nat_lit 4071740195) (nat_lit 0) D2M8K2.u11121 from rfl, totK_node, atot11120, atot11121]
  decide +kernel

theorem arows11125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11125 = true := by
  rw [show D2M8K2.u11125 = KTree.node D2M8K2.u11123 (nat_lit 24165578) (nat_lit 2616427912) (nat_lit 0) D2M8K2.u11124 from rfl, allE_node, arows11123, irow11125, arows11124]
  all_goals rfl

theorem atot11125 : totK PD2M8K2 D2M8K2.u11125 = [0, 0, 698804204401, 1822725215590, 899439952923, 72971564103, 0, 0] := by
  rw [show D2M8K2.u11125 = KTree.node D2M8K2.u11123 (nat_lit 24165578) (nat_lit 2616427912) (nat_lit 0) D2M8K2.u11124 from rfl, totK_node, atot11123, atot11124]
  decide +kernel

theorem arows11133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11133 = true := by
  rw [show D2M8K2.u11133 = KTree.node D2M8K2.u11131 (nat_lit 24172212) (nat_lit 3223625270) (nat_lit 0) D2M8K2.u11132 from rfl, allE_node, arows11131, irow11133, arows11132]
  all_goals rfl

theorem atot11133 : totK PD2M8K2 D2M8K2.u11133 = [0, 0, 814500666326, 1916823611551, 725857718508, 39520505052, 0, 0] := by
  rw [show D2M8K2.u11133 = KTree.node D2M8K2.u11131 (nat_lit 24172212) (nat_lit 3223625270) (nat_lit 0) D2M8K2.u11132 from rfl, totK_node, atot11131, atot11132]
  decide +kernel

theorem arows11136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11136 = true := by
  rw [show D2M8K2.u11136 = KTree.node D2M8K2.u11134 (nat_lit 24220736) (nat_lit 3547497317) (nat_lit 0) D2M8K2.u11135 from rfl, allE_node, arows11134, irow11136, arows11135]
  all_goals rfl

theorem atot11136 : totK PD2M8K2 D2M8K2.u11136 = [0, 417485306014, 1420337047479, 1344079135317, 340262131230, 18561750241, 0, 0] := by
  rw [show D2M8K2.u11136 = KTree.node D2M8K2.u11134 (nat_lit 24220736) (nat_lit 3547497317) (nat_lit 0) D2M8K2.u11135 from rfl, totK_node, atot11134, atot11135]
  decide +kernel

theorem arows11140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11140 = true := by
  rw [show D2M8K2.u11140 = KTree.node D2M8K2.u11138 (nat_lit 24224562) (nat_lit 2083537414) (nat_lit 0) D2M8K2.u11139 from rfl, allE_node, arows11138, irow11140, arows11139]
  all_goals rfl

theorem atot11140 : totK PD2M8K2 D2M8K2.u11140 = [0, 417264887356, 1492184122343, 1458114466865, 275729112771, 5284349065, 0, 0] := by
  rw [show D2M8K2.u11140 = KTree.node D2M8K2.u11138 (nat_lit 24224562) (nat_lit 2083537414) (nat_lit 0) D2M8K2.u11139 from rfl, totK_node, atot11138, atot11139]
  decide +kernel

theorem arows11143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11143 = true := by
  rw [show D2M8K2.u11143 = KTree.node D2M8K2.u11141 (nat_lit 24228216) (nat_lit 3270708511) (nat_lit 0) D2M8K2.u11142 from rfl, allE_node, arows11141, irow11143, arows11142]
  all_goals rfl

theorem atot11143 : totK PD2M8K2 D2M8K2.u11143 = [0, 372021662940, 1424424546876, 1461426380262, 325088349973, 13049727234, 0, 0] := by
  rw [show D2M8K2.u11143 = KTree.node D2M8K2.u11141 (nat_lit 24228216) (nat_lit 3270708511) (nat_lit 0) D2M8K2.u11142 from rfl, totK_node, atot11141, atot11142]
  decide +kernel

theorem arows11148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11148 = true := by
  rw [show D2M8K2.u11148 = KTree.node D2M8K2.u11146 (nat_lit 24234736) (nat_lit 3425203049) (nat_lit 0) D2M8K2.u11147 from rfl, allE_node, arows11146, irow11148, arows11147]
  all_goals rfl

theorem atot11148 : totK PD2M8K2 D2M8K2.u11148 = [0, 473611416711, 1547712259337, 1338946212176, 220409426405, 4917269347, 0, 0] := by
  rw [show D2M8K2.u11148 = KTree.node D2M8K2.u11146 (nat_lit 24234736) (nat_lit 3425203049) (nat_lit 0) D2M8K2.u11147 from rfl, totK_node, atot11146, atot11147]
  decide +kernel

theorem arows11151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11151 = true := by
  rw [show D2M8K2.u11151 = KTree.node D2M8K2.u11149 (nat_lit 24238726) (nat_lit 3703103347) (nat_lit 0) D2M8K2.u11150 from rfl, allE_node, arows11149, irow11151, arows11150]
  all_goals rfl

theorem atot11151 : totK PD2M8K2 D2M8K2.u11151 = [0, 388980041158, 1432931761384, 1421376635150, 334815905267, 13684302317, 0, 0] := by
  rw [show D2M8K2.u11151 = KTree.node D2M8K2.u11149 (nat_lit 24238726) (nat_lit 3703103347) (nat_lit 0) D2M8K2.u11150 from rfl, totK_node, atot11149, atot11150]
  decide +kernel

theorem arows11155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11155 = true := by
  rw [show D2M8K2.u11155 = KTree.node D2M8K2.u11153 (nat_lit 24262908) (nat_lit 3235948554) (nat_lit 0) D2M8K2.u11154 from rfl, allE_node, arows11153, irow11155, arows11154]
  all_goals rfl

theorem atot11155 : totK PD2M8K2 D2M8K2.u11155 = [0, 461069064049, 1569936007407, 1361637733156, 194325406315, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11155 = KTree.node D2M8K2.u11153 (nat_lit 24262908) (nat_lit 3235948554) (nat_lit 0) D2M8K2.u11154 from rfl, totK_node, atot11153, atot11154]
  decide +kernel

theorem arows11158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11158 = true := by
  rw [show D2M8K2.u11158 = KTree.node D2M8K2.u11156 (nat_lit 24267498) (nat_lit 3805588731) (nat_lit 0) D2M8K2.u11157 from rfl, allE_node, arows11156, irow11158, arows11157]
  all_goals rfl

theorem atot11158 : totK PD2M8K2 D2M8K2.u11158 = [0, 471247776603, 1567668880432, 1348791598464, 256037146496, 5348807592, 0, 0] := by
  rw [show D2M8K2.u11158 = KTree.node D2M8K2.u11156 (nat_lit 24267498) (nat_lit 3805588731) (nat_lit 0) D2M8K2.u11157 from rfl, totK_node, atot11156, atot11157]
  decide +kernel

theorem arows11164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11164 = true := by
  rw [show D2M8K2.u11164 = KTree.node D2M8K2.u11162 (nat_lit 24274307) (nat_lit 2341236285) (nat_lit 0) D2M8K2.u11163 from rfl, allE_node, arows11162, irow11164, arows11163]
  all_goals rfl

theorem atot11164 : totK PD2M8K2 D2M8K2.u11164 = [0, 393999545743, 1420751345536, 1420404603379, 330968349321, 13170675918, 0, 0] := by
  rw [show D2M8K2.u11164 = KTree.node D2M8K2.u11162 (nat_lit 24274307) (nat_lit 2341236285) (nat_lit 0) D2M8K2.u11163 from rfl, totK_node, atot11162, atot11163]
  decide +kernel

theorem arows11167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11167 = true := by
  rw [show D2M8K2.u11167 = KTree.node D2M8K2.u11165 (nat_lit 24277579) (nat_lit 1755175846) (nat_lit 0) D2M8K2.u11166 from rfl, allE_node, arows11165, irow11167, arows11166]
  all_goals rfl

theorem atot11167 : totK PD2M8K2 D2M8K2.u11167 = [0, 471794137392, 1546422099089, 1355400834349, 222096496206, 4917684815, 0, 0] := by
  rw [show D2M8K2.u11167 = KTree.node D2M8K2.u11165 (nat_lit 24277579) (nat_lit 1755175846) (nat_lit 0) D2M8K2.u11166 from rfl, totK_node, atot11165, atot11166]
  decide +kernel

theorem arows11171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11171 = true := by
  rw [show D2M8K2.u11171 = KTree.node D2M8K2.u11169 (nat_lit 24281569) (nat_lit 1550849715) (nat_lit 0) D2M8K2.u11170 from rfl, allE_node, arows11169, irow11171, arows11170]
  all_goals rfl

theorem atot11171 : totK PD2M8K2 D2M8K2.u11171 = [0, 384121553183, 1431584256198, 1406602969437, 329262230959, 13714665880, 0, 0] := by
  rw [show D2M8K2.u11171 = KTree.node D2M8K2.u11169 (nat_lit 24281569) (nat_lit 1550849715) (nat_lit 0) D2M8K2.u11170 from rfl, totK_node, atot11169, atot11170]
  decide +kernel

theorem arows11174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11174 = true := by
  rw [show D2M8K2.u11174 = KTree.node D2M8K2.u11172 (nat_lit 24305761) (nat_lit 1562614071) (nat_lit 0) D2M8K2.u11173 from rfl, allE_node, arows11172, irow11174, arows11173]
  all_goals rfl

theorem atot11174 : totK PD2M8K2 D2M8K2.u11174 = [0, 466588271872, 1581676886243, 1364935713238, 195238735808, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11174 = KTree.node D2M8K2.u11172 (nat_lit 24305761) (nat_lit 1562614071) (nat_lit 0) D2M8K2.u11173 from rfl, totK_node, atot11172, atot11173]
  decide +kernel

theorem arows11179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11179 = true := by
  rw [show D2M8K2.u11179 = KTree.node D2M8K2.u11177 (nat_lit 24309935) (nat_lit 2168106536) (nat_lit 0) D2M8K2.u11178 from rfl, allE_node, arows11177, irow11179, arows11178]
  all_goals rfl

theorem atot11179 : totK PD2M8K2 D2M8K2.u11179 = [0, 411020513723, 1538357317184, 1420988567895, 238649480584, 2573880433, 0, 0] := by
  rw [show D2M8K2.u11179 = KTree.node D2M8K2.u11177 (nat_lit 24309935) (nat_lit 2168106536) (nat_lit 0) D2M8K2.u11178 from rfl, totK_node, atot11177, atot11178]
  decide +kernel

theorem arows11182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11182 = true := by
  rw [show D2M8K2.u11182 = KTree.node D2M8K2.u11180 (nat_lit 24313370) (nat_lit 4006803394) (nat_lit 0) D2M8K2.u11181 from rfl, allE_node, arows11180, irow11182, arows11181]
  all_goals rfl

theorem atot11182 : totK PD2M8K2 D2M8K2.u11182 = [0, 411244085893, 1457956637176, 1393318401747, 295890228167, 13017203568, 0, 0] := by
  rw [show D2M8K2.u11182 = KTree.node D2M8K2.u11180 (nat_lit 24313370) (nat_lit 4006803394) (nat_lit 0) D2M8K2.u11181 from rfl, totK_node, atot11180, atot11181]
  decide +kernel

theorem arows11186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11186 = true := by
  rw [show D2M8K2.u11186 = KTree.node D2M8K2.u11184 (nat_lit 24316797) (nat_lit 1547845720) (nat_lit 0) D2M8K2.u11185 from rfl, allE_node, arows11184, irow11186, arows11185]
  all_goals rfl

theorem atot11186 : totK PD2M8K2 D2M8K2.u11186 = [0, 438434416974, 1513151492301, 1373603750107, 270336343384, 11986244008, 0, 0] := by
  rw [show D2M8K2.u11186 = KTree.node D2M8K2.u11184 (nat_lit 24316797) (nat_lit 1547845720) (nat_lit 0) D2M8K2.u11185 from rfl, totK_node, atot11184, atot11185]
  decide +kernel

theorem arows11189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11189 = true := by
  rw [show D2M8K2.u11189 = KTree.node D2M8K2.u11187 (nat_lit 24344705) (nat_lit 2224188786) (nat_lit 0) D2M8K2.u11188 from rfl, allE_node, arows11187, irow11189, arows11188]
  all_goals rfl

theorem atot11189 : totK PD2M8K2 D2M8K2.u11189 = [0, 419368070224, 1514792862203, 1396639436124, 243710144480, 4980514959, 0, 0] := by
  rw [show D2M8K2.u11189 = KTree.node D2M8K2.u11187 (nat_lit 24344705) (nat_lit 2224188786) (nat_lit 0) D2M8K2.u11188 from rfl, totK_node, atot11187, atot11188]
  decide +kernel

theorem arows11196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11196 = true := by
  rw [show D2M8K2.u11196 = KTree.node D2M8K2.u11194 (nat_lit 24351553) (nat_lit 1556661526) (nat_lit 0) D2M8K2.u11195 from rfl, allE_node, arows11194, irow11196, arows11195]
  all_goals rfl

theorem atot11196 : totK PD2M8K2 D2M8K2.u11196 = [0, 400206165853, 1513403965173, 1446447317957, 237233502674, 2499119547, 0, 0] := by
  rw [show D2M8K2.u11196 = KTree.node D2M8K2.u11194 (nat_lit 24351553) (nat_lit 1556661526) (nat_lit 0) D2M8K2.u11195 from rfl, totK_node, atot11194, atot11195]
  decide +kernel

theorem arows11199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11199 = true := by
  rw [show D2M8K2.u11199 = KTree.node D2M8K2.u11197 (nat_lit 24355419) (nat_lit 3620461571) (nat_lit 0) D2M8K2.u11198 from rfl, allE_node, arows11197, irow11199, arows11198]
  all_goals rfl

theorem atot11199 : totK PD2M8K2 D2M8K2.u11199 = [0, 400459878024, 1497276624955, 1441030973578, 264509935566, 5171003787, 0, 0] := by
  rw [show D2M8K2.u11199 = KTree.node D2M8K2.u11197 (nat_lit 24355419) (nat_lit 3620461571) (nat_lit 0) D2M8K2.u11198 from rfl, totK_node, atot11197, atot11198]
  decide +kernel

theorem arows11203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11203 = true := by
  rw [show D2M8K2.u11203 = KTree.node D2M8K2.u11201 (nat_lit 24362162) (nat_lit 3095952544) (nat_lit 0) D2M8K2.u11202 from rfl, allE_node, arows11201, irow11203, arows11202]
  all_goals rfl

theorem atot11203 : totK PD2M8K2 D2M8K2.u11203 = [0, 427082067050, 1504070835668, 1417359320152, 268699015863, 5280507705, 0, 0] := by
  rw [show D2M8K2.u11203 = KTree.node D2M8K2.u11201 (nat_lit 24362162) (nat_lit 3095952544) (nat_lit 0) D2M8K2.u11202 from rfl, totK_node, atot11201, atot11202]
  decide +kernel

theorem arows11206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11206 = true := by
  rw [show D2M8K2.u11206 = KTree.node D2M8K2.u11204 (nat_lit 24431197) (nat_lit 970426489) (nat_lit 0) D2M8K2.u11205 from rfl, allE_node, arows11204, irow11206, arows11205]
  all_goals rfl

theorem atot11206 : totK PD2M8K2 D2M8K2.u11206 = [449419051412, 1248438025905, 1005144881509, 642890494589, 282953250546, 20647649770, 0, 0] := by
  rw [show D2M8K2.u11206 = KTree.node D2M8K2.u11204 (nat_lit 24431197) (nat_lit 970426489) (nat_lit 0) D2M8K2.u11205 from rfl, totK_node, atot11204, atot11205]
  decide +kernel

theorem arows11211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11211 = true := by
  rw [show D2M8K2.u11211 = KTree.node D2M8K2.u11209 (nat_lit 24433913) (nat_lit 1132176010) (nat_lit 0) D2M8K2.u11210 from rfl, allE_node, arows11209, irow11211, arows11210]
  all_goals rfl

theorem atot11211 : totK PD2M8K2 D2M8K2.u11211 = [386648953929, 1275752799853, 1408887330035, 530042876966, 27164748898, 0, 0, 0] := by
  rw [show D2M8K2.u11211 = KTree.node D2M8K2.u11209 (nat_lit 24433913) (nat_lit 1132176010) (nat_lit 0) D2M8K2.u11210 from rfl, totK_node, atot11209, atot11210]
  decide +kernel

theorem arows11214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11214 = true := by
  rw [show D2M8K2.u11214 = KTree.node D2M8K2.u11212 (nat_lit 24437136) (nat_lit 3434143752) (nat_lit 0) D2M8K2.u11213 from rfl, allE_node, arows11212, irow11214, arows11213]
  all_goals rfl

theorem atot11214 : totK PD2M8K2 D2M8K2.u11214 = [370739358423, 1428190122408, 1453513313326, 331248450765, 12995965463, 0, 0, 0] := by
  rw [show D2M8K2.u11214 = KTree.node D2M8K2.u11212 (nat_lit 24437136) (nat_lit 3434143752) (nat_lit 0) D2M8K2.u11213 from rfl, totK_node, atot11212, atot11213]
  decide +kernel

theorem arows11218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11218 = true := by
  rw [show D2M8K2.u11218 = KTree.node D2M8K2.u11216 (nat_lit 24440500) (nat_lit 3172807867) (nat_lit 0) D2M8K2.u11217 from rfl, allE_node, arows11216, irow11218, arows11217]
  all_goals rfl

theorem atot11218 : totK PD2M8K2 D2M8K2.u11218 = [412949228026, 1423318802455, 1412620347911, 338555738638, 13194699740, 0, 0, 0] := by
  rw [show D2M8K2.u11218 = KTree.node D2M8K2.u11216 (nat_lit 24440500) (nat_lit 3172807867) (nat_lit 0) D2M8K2.u11217 from rfl, totK_node, atot11216, atot11217]
  decide +kernel

theorem arows11221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11221 = true := by
  rw [show D2M8K2.u11221 = KTree.node D2M8K2.u11219 (nat_lit 24443826) (nat_lit 3414786982) (nat_lit 0) D2M8K2.u11220 from rfl, allE_node, arows11219, irow11221, arows11220]
  all_goals rfl

theorem atot11221 : totK PD2M8K2 D2M8K2.u11221 = [422180929977, 1537205396497, 1410210320660, 248043011286, 4959151969, 0, 0, 0] := by
  rw [show D2M8K2.u11221 = KTree.node D2M8K2.u11219 (nat_lit 24443826) (nat_lit 3414786982) (nat_lit 0) D2M8K2.u11220 from rfl, totK_node, atot11219, atot11220]
  decide +kernel

theorem arows11227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11227 = true := by
  rw [show D2M8K2.u11227 = KTree.node D2M8K2.u11225 (nat_lit 24447490) (nat_lit 4097396695) (nat_lit 0) D2M8K2.u11226 from rfl, allE_node, arows11225, irow11227, arows11226]
  all_goals rfl

theorem atot11227 : totK PD2M8K2 D2M8K2.u11227 = [75805549015, 912633605045, 1787627096701, 785832067035, 55419061239, 0, 0, 0] := by
  rw [show D2M8K2.u11227 = KTree.node D2M8K2.u11225 (nat_lit 24447490) (nat_lit 4097396695) (nat_lit 0) D2M8K2.u11226 from rfl, totK_node, atot11225, atot11226]
  decide +kernel

theorem arows11230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11230 = true := by
  rw [show D2M8K2.u11230 = KTree.node D2M8K2.u11228 (nat_lit 24453833) (nat_lit 1619481088) (nat_lit 0) D2M8K2.u11229 from rfl, allE_node, arows11228, irow11230, arows11229]
  all_goals rfl

theorem atot11230 : totK PD2M8K2 D2M8K2.u11230 = [0, 318658460418, 1225405591093, 1484654464706, 557838248014, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11230 = KTree.node D2M8K2.u11228 (nat_lit 24453833) (nat_lit 1619481088) (nat_lit 0) D2M8K2.u11229 from rfl, totK_node, atot11228, atot11229]
  decide +kernel

theorem arows11234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11234 = true := by
  rw [show D2M8K2.u11234 = KTree.node D2M8K2.u11232 (nat_lit 24456799) (nat_lit 1957742869) (nat_lit 0) D2M8K2.u11233 from rfl, allE_node, arows11232, irow11234, arows11233]
  all_goals rfl

theorem atot11234 : totK PD2M8K2 D2M8K2.u11234 = [0, 418320522200, 1519449230619, 1405757364318, 248566650973, 5159868635, 0, 0] := by
  rw [show D2M8K2.u11234 = KTree.node D2M8K2.u11232 (nat_lit 24456799) (nat_lit 1957742869) (nat_lit 0) D2M8K2.u11233 from rfl, totK_node, atot11232, atot11233]
  decide +kernel

theorem arows11237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11237 = true := by
  rw [show D2M8K2.u11237 = KTree.node D2M8K2.u11235 (nat_lit 24460745) (nat_lit 1042640698) (nat_lit 0) D2M8K2.u11236 from rfl, allE_node, arows11235, irow11237, arows11236]
  all_goals rfl

theorem atot11237 : totK PD2M8K2 D2M8K2.u11237 = [0, 453115650396, 1520212670847, 1358481237513, 254731547346, 5218872685, 0, 0] := by
  rw [show D2M8K2.u11237 = KTree.node D2M8K2.u11235 (nat_lit 24460745) (nat_lit 1042640698) (nat_lit 0) D2M8K2.u11236 from rfl, totK_node, atot11235, atot11236]
  decide +kernel

theorem arows11242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11242 = true := by
  rw [show D2M8K2.u11242 = KTree.node D2M8K2.u11240 (nat_lit 24463977) (nat_lit 1906910786) (nat_lit 0) D2M8K2.u11241 from rfl, allE_node, arows11240, irow11242, arows11241]
  all_goals rfl

theorem atot11242 : totK PD2M8K2 D2M8K2.u11242 = [0, 456475217983, 1613111371121, 1363483548269, 185750623554, 1415142070, 0, 0] := by
  rw [show D2M8K2.u11242 = KTree.node D2M8K2.u11240 (nat_lit 24463977) (nat_lit 1906910786) (nat_lit 0) D2M8K2.u11241 from rfl, totK_node, atot11240, atot11241]
  decide +kernel

theorem arows11245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11245 = true := by
  rw [show D2M8K2.u11245 = KTree.node D2M8K2.u11243 (nat_lit 24467733) (nat_lit 1186770658) (nat_lit 0) D2M8K2.u11244 from rfl, allE_node, arows11243, irow11245, arows11244]
  all_goals rfl

theorem atot11245 : totK PD2M8K2 D2M8K2.u11245 = [256161886194, 809855974820, 1130300939659, 1076425438791, 290036593449, 9302370699, 0, 0] := by
  rw [show D2M8K2.u11245 = KTree.node D2M8K2.u11243 (nat_lit 24467733) (nat_lit 1186770658) (nat_lit 0) D2M8K2.u11244 from rfl, totK_node, atot11243, atot11244]
  decide +kernel

theorem arows11249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11249 = true := by
  rw [show D2M8K2.u11249 = KTree.node D2M8K2.u11247 (nat_lit 24472442) (nat_lit 4116241310) (nat_lit 0) D2M8K2.u11248 from rfl, allE_node, arows11247, irow11249, arows11248]
  all_goals rfl

theorem atot11249 : totK PD2M8K2 D2M8K2.u11249 = [497628736689, 1621081083493, 1331523347102, 187416626077, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11249 = KTree.node D2M8K2.u11247 (nat_lit 24472442) (nat_lit 4116241310) (nat_lit 0) D2M8K2.u11248 from rfl, totK_node, atot11247, atot11248]
  decide +kernel

theorem arows11252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11252 = true := by
  rw [show D2M8K2.u11252 = KTree.node D2M8K2.u11250 (nat_lit 24475169) (nat_lit 2108147795) (nat_lit 0) D2M8K2.u11251 from rfl, allE_node, arows11250, irow11252, arows11251]
  all_goals rfl

theorem atot11252 : totK PD2M8K2 D2M8K2.u11252 = [332978533370, 1211767211231, 1470975989787, 585253092804, 37597116817, 0, 0, 0] := by
  rw [show D2M8K2.u11252 = KTree.node D2M8K2.u11250 (nat_lit 24475169) (nat_lit 2108147795) (nat_lit 0) D2M8K2.u11251 from rfl, totK_node, atot11250, atot11251]
  decide +kernel

theorem arows11263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11263 = true := by
  rw [show D2M8K2.u11263 = KTree.node D2M8K2.u11261 (nat_lit 24478316) (nat_lit 3762351485) (nat_lit 0) D2M8K2.u11262 from rfl, allE_node, arows11261, irow11263, arows11262]
  all_goals rfl

theorem atot11263 : totK PD2M8K2 D2M8K2.u11263 = [356408945616, 1408290174783, 1478260817855, 339121023152, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11263 = KTree.node D2M8K2.u11261 (nat_lit 24478316) (nat_lit 3762351485) (nat_lit 0) D2M8K2.u11262 from rfl, totK_node, atot11261, atot11262]
  decide +kernel

theorem arows11266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11266 = true := by
  rw [show D2M8K2.u11266 = KTree.node D2M8K2.u11264 (nat_lit 24485185) (nat_lit 1548237003) (nat_lit 0) D2M8K2.u11265 from rfl, allE_node, arows11264, irow11266, arows11265]
  all_goals rfl

theorem atot11266 : totK PD2M8K2 D2M8K2.u11266 = [455458018068, 1545220642112, 1376795178261, 245733034888, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u11266 = KTree.node D2M8K2.u11264 (nat_lit 24485185) (nat_lit 1548237003) (nat_lit 0) D2M8K2.u11265 from rfl, totK_node, atot11264, atot11265]
  decide +kernel

theorem arows11270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11270 = true := by
  rw [show D2M8K2.u11270 = KTree.node D2M8K2.u11268 (nat_lit 24488940) (nat_lit 3429489651) (nat_lit 0) D2M8K2.u11269 from rfl, allE_node, arows11268, irow11270, arows11269]
  all_goals rfl

theorem atot11270 : totK PD2M8K2 D2M8K2.u11270 = [90490504222, 964762055239, 1790403674652, 678093602016, 34436811965, 0, 0, 0] := by
  rw [show D2M8K2.u11270 = KTree.node D2M8K2.u11268 (nat_lit 24488940) (nat_lit 3429489651) (nat_lit 0) D2M8K2.u11269 from rfl, totK_node, atot11268, atot11269]
  decide +kernel

theorem arows11273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11273 = true := by
  rw [show D2M8K2.u11273 = KTree.node D2M8K2.u11271 (nat_lit 24493297) (nat_lit 1438226065) (nat_lit 0) D2M8K2.u11272 from rfl, allE_node, arows11271, irow11273, arows11272]
  all_goals rfl

theorem atot11273 : totK PD2M8K2 D2M8K2.u11273 = [0, 527990262067, 1657280636320, 1249866321539, 151748265220, 1206465782, 0, 0] := by
  rw [show D2M8K2.u11273 = KTree.node D2M8K2.u11271 (nat_lit 24493297) (nat_lit 1438226065) (nat_lit 0) D2M8K2.u11272 from rfl, totK_node, atot11271, atot11272]
  decide +kernel

theorem arows11278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11278 = true := by
  rw [show D2M8K2.u11278 = KTree.node D2M8K2.u11276 (nat_lit 24497791) (nat_lit 1231015157) (nat_lit 0) D2M8K2.u11277 from rfl, allE_node, arows11276, irow11278, arows11277]
  all_goals rfl

theorem atot11278 : totK PD2M8K2 D2M8K2.u11278 = [0, 404722578072, 1458918904209, 1359479432206, 306775050438, 13016197374, 0, 0] := by
  rw [show D2M8K2.u11278 = KTree.node D2M8K2.u11276 (nat_lit 24497791) (nat_lit 1231015157) (nat_lit 0) D2M8K2.u11277 from rfl, totK_node, atot11276, atot11277]
  decide +kernel

theorem arows11281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11281 = true := by
  rw [show D2M8K2.u11281 = KTree.node D2M8K2.u11279 (nat_lit 24504417) (nat_lit 1845086237) (nat_lit 0) D2M8K2.u11280 from rfl, allE_node, arows11279, irow11281, arows11280]
  all_goals rfl

theorem atot11281 : totK PD2M8K2 D2M8K2.u11281 = [0, 486725075417, 1631870516269, 1235872602930, 176748781267, 4574395652, 0, 0] := by
  rw [show D2M8K2.u11281 = KTree.node D2M8K2.u11279 (nat_lit 24504417) (nat_lit 1845086237) (nat_lit 0) D2M8K2.u11280 from rfl, totK_node, atot11279, atot11280]
  decide +kernel

theorem arows11285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11285 = true := by
  rw [show D2M8K2.u11285 = KTree.node D2M8K2.u11283 (nat_lit 24510177) (nat_lit 1737235550) (nat_lit 0) D2M8K2.u11284 from rfl, allE_node, arows11283, irow11285, arows11284]
  all_goals rfl

theorem atot11285 : totK PD2M8K2 D2M8K2.u11285 = [325011403864, 1242923133696, 1441672859818, 560927239789, 42986499321, 0, 0, 0] := by
  rw [show D2M8K2.u11285 = KTree.node D2M8K2.u11283 (nat_lit 24510177) (nat_lit 1737235550) (nat_lit 0) D2M8K2.u11284 from rfl, totK_node, atot11283, atot11284]
  decide +kernel

theorem arows11288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11288 = true := by
  rw [show D2M8K2.u11288 = KTree.node D2M8K2.u11286 (nat_lit 24514572) (nat_lit 3160988340) (nat_lit 0) D2M8K2.u11287 from rfl, allE_node, arows11286, irow11288, arows11287]
  all_goals rfl

theorem atot11288 : totK PD2M8K2 D2M8K2.u11288 = [428960387537, 1471389172870, 1370817784956, 360668927030, 25364689049, 0, 0, 0] := by
  rw [show D2M8K2.u11288 = KTree.node D2M8K2.u11286 (nat_lit 24514572) (nat_lit 3160988340) (nat_lit 0) D2M8K2.u11287 from rfl, totK_node, atot11286, atot11287]
  decide +kernel

theorem arows11294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11294 = true := by
  rw [show D2M8K2.u11294 = KTree.node D2M8K2.u11292 (nat_lit 24520796) (nat_lit 3572411049) (nat_lit 0) D2M8K2.u11293 from rfl, allE_node, arows11292, irow11294, arows11293]
  all_goals rfl

theorem atot11294 : totK PD2M8K2 D2M8K2.u11294 = [438704021447, 1429351600766, 1361074355805, 373181365704, 13428474342, 0, 0, 0] := by
  rw [show D2M8K2.u11294 = KTree.node D2M8K2.u11292 (nat_lit 24520796) (nat_lit 3572411049) (nat_lit 0) D2M8K2.u11293 from rfl, totK_node, atot11292, atot11293]
  decide +kernel

theorem arows11297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11297 = true := by
  rw [show D2M8K2.u11297 = KTree.node D2M8K2.u11295 (nat_lit 24524107) (nat_lit 1804167824) (nat_lit 0) D2M8K2.u11296 from rfl, allE_node, arows11295, irow11297, arows11296]
  all_goals rfl

theorem atot11297 : totK PD2M8K2 D2M8K2.u11297 = [413788040677, 1463750608977, 1401082417001, 317076387469, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u11297 = KTree.node D2M8K2.u11295 (nat_lit 24524107) (nat_lit 1804167824) (nat_lit 0) D2M8K2.u11296 from rfl, totK_node, atot11295, atot11296]
  decide +kernel

theorem arows11301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11301 = true := by
  rw [show D2M8K2.u11301 = KTree.node D2M8K2.u11299 (nat_lit 24527659) (nat_lit 1594385462) (nat_lit 0) D2M8K2.u11300 from rfl, allE_node, arows11299, irow11301, arows11300]
  all_goals rfl

theorem atot11301 : totK PD2M8K2 D2M8K2.u11301 = [386732656573, 1450373867550, 1481411526444, 306993036495, 6249254262, 0, 0, 0] := by
  rw [show D2M8K2.u11301 = KTree.node D2M8K2.u11299 (nat_lit 24527659) (nat_lit 1594385462) (nat_lit 0) D2M8K2.u11300 from rfl, totK_node, atot11299, atot11300]
  decide +kernel

theorem arows11304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11304 = true := by
  rw [show D2M8K2.u11304 = KTree.node D2M8K2.u11302 (nat_lit 24531635) (nat_lit 2841131890) (nat_lit 0) D2M8K2.u11303 from rfl, allE_node, arows11302, irow11304, arows11303]
  all_goals rfl

theorem atot11304 : totK PD2M8K2 D2M8K2.u11304 = [0, 608267025382, 1725678547612, 1082813028760, 121246264884, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11304 = KTree.node D2M8K2.u11302 (nat_lit 24531635) (nat_lit 2841131890) (nat_lit 0) D2M8K2.u11303 from rfl, totK_node, atot11302, atot11303]
  decide +kernel

theorem arows11309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11309 = true := by
  rw [show D2M8K2.u11309 = KTree.node D2M8K2.u11307 (nat_lit 24535449) (nat_lit 1821894688) (nat_lit 0) D2M8K2.u11308 from rfl, allE_node, arows11307, irow11309, arows11308]
  all_goals rfl

theorem atot11309 : totK PD2M8K2 D2M8K2.u11309 = [0, 691670659326, 1832400474663, 1047950679156, 86710891324, 0, 0, 0] := by
  rw [show D2M8K2.u11309 = KTree.node D2M8K2.u11307 (nat_lit 24535449) (nat_lit 1821894688) (nat_lit 0) D2M8K2.u11308 from rfl, totK_node, atot11307, atot11308]
  decide +kernel

theorem arows11312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11312 = true := by
  rw [show D2M8K2.u11312 = KTree.node D2M8K2.u11310 (nat_lit 24543802) (nat_lit 3445479231) (nat_lit 0) D2M8K2.u11311 from rfl, allE_node, arows11310, irow11312, arows11311]
  all_goals rfl

theorem atot11312 : totK PD2M8K2 D2M8K2.u11312 = [0, 406737083085, 1449185579551, 1356071737528, 307908584908, 13105450397, 0, 0] := by
  rw [show D2M8K2.u11312 = KTree.node D2M8K2.u11310 (nat_lit 24543802) (nat_lit 3445479231) (nat_lit 0) D2M8K2.u11311 from rfl, totK_node, atot11310, atot11311]
  decide +kernel

theorem arows11316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11316 = true := by
  rw [show D2M8K2.u11316 = KTree.node D2M8K2.u11314 (nat_lit 24547209) (nat_lit 1907098634) (nat_lit 0) D2M8K2.u11315 from rfl, allE_node, arows11314, irow11316, arows11315]
  all_goals rfl

theorem atot11316 : totK PD2M8K2 D2M8K2.u11316 = [0, 474462234683, 1590095738931, 1290506538243, 195236113146, 4720618446, 0, 0] := by
  rw [show D2M8K2.u11316 = KTree.node D2M8K2.u11314 (nat_lit 24547209) (nat_lit 1907098634) (nat_lit 0) D2M8K2.u11315 from rfl, totK_node, atot11314, atot11315]
  decide +kernel

theorem arows11319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11319 = true := by
  rw [show D2M8K2.u11319 = KTree.node D2M8K2.u11317 (nat_lit 24552541) (nat_lit 1025544588) (nat_lit 0) D2M8K2.u11318 from rfl, allE_node, arows11317, irow11319, arows11318]
  all_goals rfl

theorem atot11319 : totK PD2M8K2 D2M8K2.u11319 = [433967504439, 1462598727702, 1348068769844, 356362712642, 22155587479, 0, 0, 0] := by
  rw [show D2M8K2.u11319 = KTree.node D2M8K2.u11317 (nat_lit 24552541) (nat_lit 1025544588) (nat_lit 0) D2M8K2.u11318 from rfl, totK_node, atot11317, atot11318]
  decide +kernel

theorem arows11326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11326 = true := by
  rw [show D2M8K2.u11326 = KTree.node D2M8K2.u11324 (nat_lit 24556547) (nat_lit 2852351391) (nat_lit 0) D2M8K2.u11325 from rfl, allE_node, arows11324, irow11326, arows11325]
  all_goals rfl

theorem atot11326 : totK PD2M8K2 D2M8K2.u11326 = [336687528240, 1297674354895, 1478427145086, 497217588946, 30800671508, 0, 0, 0] := by
  rw [show D2M8K2.u11326 = KTree.node D2M8K2.u11324 (nat_lit 24556547) (nat_lit 2852351391) (nat_lit 0) D2M8K2.u11325 from rfl, totK_node, atot11324, atot11325]
  decide +kernel

theorem arows11329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11329 = true := by
  rw [show D2M8K2.u11329 = KTree.node D2M8K2.u11327 (nat_lit 24559550) (nat_lit 3853134236) (nat_lit 0) D2M8K2.u11328 from rfl, allE_node, arows11327, irow11329, arows11328]
  all_goals rfl

theorem atot11329 : totK PD2M8K2 D2M8K2.u11329 = [413820936442, 1432547718830, 1379739880067, 356796435351, 16388749818, 0, 0, 0] := by
  rw [show D2M8K2.u11329 = KTree.node D2M8K2.u11327 (nat_lit 24559550) (nat_lit 3853134236) (nat_lit 0) D2M8K2.u11328 from rfl, totK_node, atot11327, atot11328]
  decide +kernel

theorem arows11333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11333 = true := by
  rw [show D2M8K2.u11333 = KTree.node D2M8K2.u11331 (nat_lit 24562973) (nat_lit 2152366375) (nat_lit 0) D2M8K2.u11332 from rfl, allE_node, arows11331, irow11333, arows11332]
  all_goals rfl

theorem atot11333 : totK PD2M8K2 D2M8K2.u11333 = [414047057995, 1433693565355, 1390075297054, 335079047769, 13130749562, 0, 0, 0] := by
  rw [show D2M8K2.u11333 = KTree.node D2M8K2.u11331 (nat_lit 24562973) (nat_lit 2152366375) (nat_lit 0) D2M8K2.u11332 from rfl, totK_node, atot11331, atot11332]
  decide +kernel

theorem arows11336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11336 = true := by
  rw [show D2M8K2.u11336 = KTree.node D2M8K2.u11334 (nat_lit 24566076) (nat_lit 2756610414) (nat_lit 0) D2M8K2.u11335 from rfl, allE_node, arows11334, irow11336, arows11335]
  all_goals rfl

theorem atot11336 : totK PD2M8K2 D2M8K2.u11336 = [439668458485, 1553010692223, 1395854213318, 241500480022, 4678454933, 0, 0, 0] := by
  rw [show D2M8K2.u11336 = KTree.node D2M8K2.u11334 (nat_lit 24566076) (nat_lit 2756610414) (nat_lit 0) D2M8K2.u11335 from rfl, totK_node, atot11334, atot11335]
  decide +kernel

theorem arows11341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11341 = true := by
  rw [show D2M8K2.u11341 = KTree.node D2M8K2.u11339 (nat_lit 24573316) (nat_lit 3731426758) (nat_lit 0) D2M8K2.u11340 from rfl, allE_node, arows11339, irow11341, arows11340]
  all_goals rfl

theorem atot11341 : totK PD2M8K2 D2M8K2.u11341 = [0, 575461950540, 1726833798915, 1123033153708, 128612889424, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11341 = KTree.node D2M8K2.u11339 (nat_lit 24573316) (nat_lit 3731426758) (nat_lit 0) D2M8K2.u11340 from rfl, totK_node, atot11339, atot11340]
  decide +kernel

theorem arows11344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11344 = true := by
  rw [show D2M8K2.u11344 = KTree.node D2M8K2.u11342 (nat_lit 24579157) (nat_lit 1249793116) (nat_lit 0) D2M8K2.u11343 from rfl, allE_node, arows11342, irow11344, arows11343]
  all_goals rfl

theorem atot11344 : totK PD2M8K2 D2M8K2.u11344 = [0, 749361055340, 1890949533992, 918949022195, 54678147603, 0, 0, 0] := by
  rw [show D2M8K2.u11344 = KTree.node D2M8K2.u11342 (nat_lit 24579157) (nat_lit 1249793116) (nat_lit 0) D2M8K2.u11343 from rfl, totK_node, atot11342, atot11343]
  decide +kernel

theorem arows11348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11348 = true := by
  rw [show D2M8K2.u11348 = KTree.node D2M8K2.u11346 (nat_lit 24584001) (nat_lit 1338457228) (nat_lit 0) D2M8K2.u11347 from rfl, allE_node, arows11346, irow11348, arows11347]
  all_goals rfl

theorem atot11348 : totK PD2M8K2 D2M8K2.u11348 = [0, 759339015821, 1895636558467, 901069835052, 54019578555, 0, 0, 0] := by
  rw [show D2M8K2.u11348 = KTree.node D2M8K2.u11346 (nat_lit 24584001) (nat_lit 1338457228) (nat_lit 0) D2M8K2.u11347 from rfl, totK_node, atot11346, atot11347]
  decide +kernel

theorem arows11351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11351 = true := by
  rw [show D2M8K2.u11351 = KTree.node D2M8K2.u11349 (nat_lit 24588958) (nat_lit 2169005634) (nat_lit 0) D2M8K2.u11350 from rfl, allE_node, arows11349, irow11351, arows11350]
  all_goals rfl

theorem atot11351 : totK PD2M8K2 D2M8K2.u11351 = [340079057287, 901042642576, 1164069280037, 964489591444, 200536680945, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11351 = KTree.node D2M8K2.u11349 (nat_lit 24588958) (nat_lit 2169005634) (nat_lit 0) D2M8K2.u11350 from rfl, totK_node, atot11349, atot11350]
  decide +kernel

theorem arows11357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11357 = true := by
  rw [show D2M8K2.u11357 = KTree.node D2M8K2.u11355 (nat_lit 24599163) (nat_lit 3442311058) (nat_lit 0) D2M8K2.u11356 from rfl, allE_node, arows11355, irow11357, arows11356]
  all_goals rfl

theorem atot11357 : totK PD2M8K2 D2M8K2.u11357 = [301210220741, 1198480750625, 1523136466096, 590881594923, 37589446790, 0, 0, 0] := by
  rw [show D2M8K2.u11357 = KTree.node D2M8K2.u11355 (nat_lit 24599163) (nat_lit 3442311058) (nat_lit 0) D2M8K2.u11356 from rfl, totK_node, atot11355, atot11356]
  decide +kernel

theorem arows11360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11360 = true := by
  rw [show D2M8K2.u11360 = KTree.node D2M8K2.u11358 (nat_lit 24602208) (nat_lit 3227764098) (nat_lit 0) D2M8K2.u11359 from rfl, allE_node, arows11358, irow11360, arows11359]
  all_goals rfl

theorem atot11360 : totK PD2M8K2 D2M8K2.u11360 = [403602272358, 1451730658944, 1419328257833, 327005476093, 13010905804, 0, 0, 0] := by
  rw [show D2M8K2.u11360 = KTree.node D2M8K2.u11358 (nat_lit 24602208) (nat_lit 3227764098) (nat_lit 0) D2M8K2.u11359 from rfl, totK_node, atot11358, atot11359]
  decide +kernel

theorem arows11364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11364 = true := by
  rw [show D2M8K2.u11364 = KTree.node D2M8K2.u11362 (nat_lit 24605958) (nat_lit 3892297328) (nat_lit 0) D2M8K2.u11363 from rfl, allE_node, arows11362, irow11364, arows11363]
  all_goals rfl

theorem atot11364 : totK PD2M8K2 D2M8K2.u11364 = [405531182802, 1449553064927, 1424309420755, 335375634257, 13208902969, 0, 0, 0] := by
  rw [show D2M8K2.u11364 = KTree.node D2M8K2.u11362 (nat_lit 24605958) (nat_lit 3892297328) (nat_lit 0) D2M8K2.u11363 from rfl, totK_node, atot11362, atot11363]
  decide +kernel

theorem arows11367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11367 = true := by
  rw [show D2M8K2.u11367 = KTree.node D2M8K2.u11365 (nat_lit 24612496) (nat_lit 3393936915) (nat_lit 0) D2M8K2.u11366 from rfl, allE_node, arows11365, irow11367, arows11366]
  all_goals rfl

theorem atot11367 : totK PD2M8K2 D2M8K2.u11367 = [212497088019, 1144463890329, 1612029335841, 598552783510, 43975460845, 0, 0, 0] := by
  rw [show D2M8K2.u11367 = KTree.node D2M8K2.u11365 (nat_lit 24612496) (nat_lit 3393936915) (nat_lit 0) D2M8K2.u11366 from rfl, totK_node, atot11365, atot11366]
  decide +kernel

theorem arows11372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11372 = true := by
  rw [show D2M8K2.u11372 = KTree.node D2M8K2.u11370 (nat_lit 24620696) (nat_lit 3174066036) (nat_lit 0) D2M8K2.u11371 from rfl, allE_node, arows11370, irow11372, arows11371]
  all_goals rfl

theorem atot11372 : totK PD2M8K2 D2M8K2.u11372 = [0, 715888686655, 1864159860080, 987299056709, 68376305508, 0, 0, 0] := by
  rw [show D2M8K2.u11372 = KTree.node D2M8K2.u11370 (nat_lit 24620696) (nat_lit 3174066036) (nat_lit 0) D2M8K2.u11371 from rfl, totK_node, atot11370, atot11371]
  decide +kernel

theorem arows11375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11375 = true := by
  rw [show D2M8K2.u11375 = KTree.node D2M8K2.u11373 (nat_lit 24624410) (nat_lit 4119033422) (nat_lit 0) D2M8K2.u11374 from rfl, allE_node, arows11373, irow11375, arows11374]
  all_goals rfl

theorem atot11375 : totK PD2M8K2 D2M8K2.u11375 = [0, 402502038412, 1484407271540, 1403315870882, 258200016758, 5986997553, 0, 0] := by
  rw [show D2M8K2.u11375 = KTree.node D2M8K2.u11373 (nat_lit 24624410) (nat_lit 4119033422) (nat_lit 0) D2M8K2.u11374 from rfl, totK_node, atot11373, atot11374]
  decide +kernel

theorem arows11379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11379 = true := by
  rw [show D2M8K2.u11379 = KTree.node D2M8K2.u11377 (nat_lit 24631496) (nat_lit 2546558907) (nat_lit 0) D2M8K2.u11378 from rfl, allE_node, arows11377, irow11379, arows11378]
  all_goals rfl

theorem atot11379 : totK PD2M8K2 D2M8K2.u11379 = [0, 427660108618, 1557047051587, 1374838714687, 240084654878, 5066386085, 0, 0] := by
  rw [show D2M8K2.u11379 = KTree.node D2M8K2.u11377 (nat_lit 24631496) (nat_lit 2546558907) (nat_lit 0) D2M8K2.u11378 from rfl, totK_node, atot11377, atot11378]
  decide +kernel

theorem arows11382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11382 = true := by
  rw [show D2M8K2.u11382 = KTree.node D2M8K2.u11380 (nat_lit 24679866) (nat_lit 3553682206) (nat_lit 0) D2M8K2.u11381 from rfl, allE_node, arows11380, irow11382, arows11381]
  all_goals rfl

theorem atot11382 : totK PD2M8K2 D2M8K2.u11382 = [0, 449419051412, 1452153119107, 1333885575741, 352635484654, 20509029466, 0, 0] := by
  rw [show D2M8K2.u11382 = KTree.node D2M8K2.u11380 (nat_lit 24679866) (nat_lit 3553682206) (nat_lit 0) D2M8K2.u11381 from rfl, totK_node, atot11380, atot11381]
  decide +kernel

theorem arows11390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11390 = true := by
  rw [show D2M8K2.u11390 = KTree.node D2M8K2.u11388 (nat_lit 24682532) (nat_lit 2677447841) (nat_lit 0) D2M8K2.u11389 from rfl, allE_node, arows11388, irow11390, arows11389]
  all_goals rfl

theorem atot11390 : totK PD2M8K2 D2M8K2.u11390 = [0, 334249120324, 1213710784452, 1468548242625, 580116835310, 37609398105, 0, 0] := by
  rw [show D2M8K2.u11390 = KTree.node D2M8K2.u11388 (nat_lit 24682532) (nat_lit 2677447841) (nat_lit 0) D2M8K2.u11389 from rfl, totK_node, atot11388, atot11389]
  decide +kernel

theorem arows11393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11393 = true := by
  rw [show D2M8K2.u11393 = KTree.node D2M8K2.u11391 (nat_lit 24685782) (nat_lit 2184066533) (nat_lit 0) D2M8K2.u11392 from rfl, allE_node, arows11391, irow11393, arows11392]
  all_goals rfl

theorem atot11393 : totK PD2M8K2 D2M8K2.u11393 = [0, 401531064266, 1444726466572, 1429220962248, 313619670846, 8706415949, 0, 0] := by
  rw [show D2M8K2.u11393 = KTree.node D2M8K2.u11391 (nat_lit 24685782) (nat_lit 2184066533) (nat_lit 0) D2M8K2.u11392 from rfl, totK_node, atot11391, atot11392]
  decide +kernel

theorem arows11397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11397 = true := by
  rw [show D2M8K2.u11397 = KTree.node D2M8K2.u11395 (nat_lit 24689163) (nat_lit 3612560933) (nat_lit 0) D2M8K2.u11396 from rfl, allE_node, arows11395, irow11397, arows11396]
  all_goals rfl

theorem atot11397 : totK PD2M8K2 D2M8K2.u11397 = [0, 382666508461, 1434485199598, 1431943694627, 324167969240, 8824320960, 0, 0] := by
  rw [show D2M8K2.u11397 = KTree.node D2M8K2.u11395 (nat_lit 24689163) (nat_lit 3612560933) (nat_lit 0) D2M8K2.u11396 from rfl, totK_node, atot11395, atot11396]
  decide +kernel

theorem arows11400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11400 = true := by
  rw [show D2M8K2.u11400 = KTree.node D2M8K2.u11398 (nat_lit 24692573) (nat_lit 2269069152) (nat_lit 0) D2M8K2.u11399 from rfl, allE_node, arows11398, irow11400, arows11399]
  all_goals rfl

theorem atot11400 : totK PD2M8K2 D2M8K2.u11400 = [0, 458022023443, 1558002531843, 1367256001309, 229466111551, 2498823382, 0, 0] := by
  rw [show D2M8K2.u11400 = KTree.node D2M8K2.u11398 (nat_lit 24692573) (nat_lit 2269069152) (nat_lit 0) D2M8K2.u11399 from rfl, totK_node, atot11398, atot11399]
  decide +kernel

theorem arows11405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11405 = true := by
  rw [show D2M8K2.u11405 = KTree.node D2M8K2.u11403 (nat_lit 24695884) (nat_lit 2648048978) (nat_lit 0) D2M8K2.u11404 from rfl, allE_node, arows11403, irow11405, arows11404]
  all_goals rfl

theorem atot11405 : totK PD2M8K2 D2M8K2.u11405 = [0, 91855302876, 980660896066, 1773071207190, 716470887376, 44047968441, 0, 0] := by
  rw [show D2M8K2.u11405 = KTree.node D2M8K2.u11403 (nat_lit 24695884) (nat_lit 2648048978) (nat_lit 0) D2M8K2.u11404 from rfl, totK_node, atot11403, atot11404]
  decide +kernel

theorem arows11408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11408 = true := by
  rw [show D2M8K2.u11408 = KTree.node D2M8K2.u11406 (nat_lit 24702533) (nat_lit 2294773382) (nat_lit 0) D2M8K2.u11407 from rfl, allE_node, arows11406, irow11408, arows11407]
  all_goals rfl

theorem atot11408 : totK PD2M8K2 D2M8K2.u11408 = [0, 0, 326226768495, 1220581259846, 1456935161514, 548754193234, 36921873854, 0] := by
  rw [show D2M8K2.u11408 = KTree.node D2M8K2.u11406 (nat_lit 24702533) (nat_lit 2294773382) (nat_lit 0) D2M8K2.u11407 from rfl, totK_node, atot11406, atot11407]
  decide +kernel

theorem arows11412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11412 = true := by
  rw [show D2M8K2.u11412 = KTree.node D2M8K2.u11410 (nat_lit 24705578) (nat_lit 4104917830) (nat_lit 0) D2M8K2.u11411 from rfl, allE_node, arows11410, irow11412, arows11411]
  all_goals rfl

theorem atot11412 : totK PD2M8K2 D2M8K2.u11412 = [0, 0, 415504726964, 1527411948269, 1390278364534, 235183318929, 5067863418, 0] := by
  rw [show D2M8K2.u11412 = KTree.node D2M8K2.u11410 (nat_lit 24705578) (nat_lit 4104917830) (nat_lit 0) D2M8K2.u11411 from rfl, totK_node, atot11410, atot11411]
  decide +kernel

theorem arows11415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11415 = true := by
  rw [show D2M8K2.u11415 = KTree.node D2M8K2.u11413 (nat_lit 24709570) (nat_lit 3979150017) (nat_lit 0) D2M8K2.u11414 from rfl, allE_node, arows11413, irow11415, arows11414]
  all_goals rfl

theorem atot11415 : totK PD2M8K2 D2M8K2.u11415 = [0, 0, 449320231704, 1522259128218, 1345356651830, 231913283631, 5126512042, 0] := by
  rw [show D2M8K2.u11415 = KTree.node D2M8K2.u11413 (nat_lit 24709570) (nat_lit 3979150017) (nat_lit 0) D2M8K2.u11414 from rfl, totK_node, atot11413, atot11414]
  decide +kernel

theorem arows11421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11421 = true := by
  rw [show D2M8K2.u11421 = KTree.node D2M8K2.u11419 (nat_lit 24712996) (nat_lit 1206498170) (nat_lit 0) D2M8K2.u11420 from rfl, allE_node, arows11419, irow11421, arows11420]
  all_goals rfl

theorem atot11421 : totK PD2M8K2 D2M8K2.u11421 = [0, 0, 475198990661, 1621332485295, 1319608731894, 163493964654, 1392055030, 0] := by
  rw [show D2M8K2.u11421 = KTree.node D2M8K2.u11419 (nat_lit 24712996) (nat_lit 1206498170) (nat_lit 0) D2M8K2.u11420 from rfl, totK_node, atot11419, atot11420]
  decide +kernel

theorem arows11424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11424 = true := by
  rw [show D2M8K2.u11424 = KTree.node D2M8K2.u11422 (nat_lit 24716665) (nat_lit 947994723) (nat_lit 0) D2M8K2.u11423 from rfl, allE_node, arows11422, irow11424, arows11423]
  all_goals rfl

theorem atot11424 : totK PD2M8K2 D2M8K2.u11424 = [0, 283783099808, 831501058069, 1097195822722, 1052717907598, 267210981733, 9139067247, 0] := by
  rw [show D2M8K2.u11424 = KTree.node D2M8K2.u11422 (nat_lit 24716665) (nat_lit 947994723) (nat_lit 0) D2M8K2.u11423 from rfl, totK_node, atot11422, atot11423]
  decide +kernel

theorem arows11428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11428 = true := by
  rw [show D2M8K2.u11428 = KTree.node D2M8K2.u11426 (nat_lit 24721342) (nat_lit 3910255212) (nat_lit 0) D2M8K2.u11427 from rfl, allE_node, arows11426, irow11428, arows11427]
  all_goals rfl

theorem atot11428 : totK PD2M8K2 D2M8K2.u11428 = [0, 470007523075, 1619290258413, 1357122359927, 181204454345, 1275377855, 0, 0] := by
  rw [show D2M8K2.u11428 = KTree.node D2M8K2.u11426 (nat_lit 24721342) (nat_lit 3910255212) (nat_lit 0) D2M8K2.u11427 from rfl, totK_node, atot11426, atot11427]
  decide +kernel

theorem arows11431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11431 = true := by
  rw [show D2M8K2.u11431 = KTree.node D2M8K2.u11429 (nat_lit 24724108) (nat_lit 3710769412) (nat_lit 0) D2M8K2.u11430 from rfl, allE_node, arows11429, irow11431, arows11430]
  all_goals rfl

theorem atot11431 : totK PD2M8K2 D2M8K2.u11431 = [0, 351869631213, 1230392190822, 1434859806055, 566909330933, 37487326182, 0, 0] := by
  rw [show D2M8K2.u11431 = KTree.node D2M8K2.u11429 (nat_lit 24724108) (nat_lit 3710769412) (nat_lit 0) D2M8K2.u11430 from rfl, totK_node, atot11429, atot11430]
  decide +kernel

theorem arows11436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11436 = true := by
  rw [show D2M8K2.u11436 = KTree.node D2M8K2.u11434 (nat_lit 24727216) (nat_lit 3419371942) (nat_lit 0) D2M8K2.u11435 from rfl, allE_node, arows11434, irow11436, arows11435]
  all_goals rfl

theorem atot11436 : totK PD2M8K2 D2M8K2.u11436 = [0, 384308786032, 1403698089547, 1451436966775, 338938720954, 13049727234, 0, 0] := by
  rw [show D2M8K2.u11436 = KTree.node D2M8K2.u11434 (nat_lit 24727216) (nat_lit 3419371942) (nat_lit 0) D2M8K2.u11435 from rfl, totK_node, atot11434, atot11435]
  decide +kernel

theorem arows11439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11439 = true := by
  rw [show D2M8K2.u11439 = KTree.node D2M8K2.u11437 (nat_lit 24734090) (nat_lit 3953114743) (nat_lit 0) D2M8K2.u11438 from rfl, allE_node, arows11437, irow11439, arows11438]
  all_goals rfl

theorem atot11439 : totK PD2M8K2 D2M8K2.u11439 = [0, 432934239027, 1549602131008, 1380556526739, 245328088289, 4980514959, 0, 0] := by
  rw [show D2M8K2.u11439 = KTree.node D2M8K2.u11437 (nat_lit 24734090) (nat_lit 3953114743) (nat_lit 0) D2M8K2.u11438 from rfl, totK_node, atot11437, atot11438]
  decide +kernel

theorem arows11443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11443 = true := by
  rw [show D2M8K2.u11443 = KTree.node D2M8K2.u11441 (nat_lit 24737845) (nat_lit 1027314555) (nat_lit 0) D2M8K2.u11442 from rfl, allE_node, arows11441, irow11443, arows11442]
  all_goals rfl

theorem atot11443 : totK PD2M8K2 D2M8K2.u11443 = [0, 62160131298, 980149897629, 1865451917094, 618038626902, 21404549195, 0, 0] := by
  rw [show D2M8K2.u11443 = KTree.node D2M8K2.u11441 (nat_lit 24737845) (nat_lit 1027314555) (nat_lit 0) D2M8K2.u11442 from rfl, totK_node, atot11441, atot11442]
  decide +kernel

theorem arows11446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11446 = true := by
  rw [show D2M8K2.u11446 = KTree.node D2M8K2.u11444 (nat_lit 24743137) (nat_lit 1345102055) (nat_lit 0) D2M8K2.u11445 from rfl, allE_node, arows11444, irow11446, arows11445]
  all_goals rfl

theorem atot11446 : totK PD2M8K2 D2M8K2.u11446 = [0, 0, 701664081230, 1861391589818, 970228333704, 70125402318, 0, 0] := by
  rw [show D2M8K2.u11446 = KTree.node D2M8K2.u11444 (nat_lit 24743137) (nat_lit 1345102055) (nat_lit 0) D2M8K2.u11445 from rfl, totK_node, atot11444, atot11445]
  decide +kernel

theorem arows11453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11453 = true := by
  rw [show D2M8K2.u11453 = KTree.node D2M8K2.u11451 (nat_lit 24748198) (nat_lit 3710476063) (nat_lit 0) D2M8K2.u11452 from rfl, allE_node, arows11451, irow11453, arows11452]
  all_goals rfl

theorem atot11453 : totK PD2M8K2 D2M8K2.u11453 = [0, 0, 478825057575, 1564870819802, 1276335494850, 219402200142, 5320761635, 0] := by
  rw [show D2M8K2.u11453 = KTree.node D2M8K2.u11451 (nat_lit 24748198) (nat_lit 3710476063) (nat_lit 0) D2M8K2.u11452 from rfl, totK_node, atot11451, atot11452]
  decide +kernel

theorem arows11456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11456 = true := by
  rw [show D2M8K2.u11456 = KTree.node D2M8K2.u11454 (nat_lit 24755743) (nat_lit 2227068907) (nat_lit 0) D2M8K2.u11455 from rfl, allE_node, arows11454, irow11456, arows11455]
  all_goals rfl

theorem atot11456 : totK PD2M8K2 D2M8K2.u11456 = [0, 85430600343, 612416452182, 1554984991600, 1158026291632, 133605502451, 1225787871, 0] := by
  rw [show D2M8K2.u11456 = KTree.node D2M8K2.u11454 (nat_lit 24755743) (nat_lit 2227068907) (nat_lit 0) D2M8K2.u11455 from rfl, totK_node, atot11454, atot11455]
  decide +kernel

theorem arows11460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11460 = true := by
  rw [show D2M8K2.u11460 = KTree.node D2M8K2.u11458 (nat_lit 24761665) (nat_lit 1560988708) (nat_lit 0) D2M8K2.u11459 from rfl, allE_node, arows11458, irow11460, arows11459]
  all_goals rfl

theorem atot11460 : totK PD2M8K2 D2M8K2.u11460 = [0, 530399484029, 1646086595479, 1287382344557, 164296062779, 1310517177, 0, 0] := by
  rw [show D2M8K2.u11460 = KTree.node D2M8K2.u11458 (nat_lit 24761665) (nat_lit 1560988708) (nat_lit 0) D2M8K2.u11459 from rfl, totK_node, atot11458, atot11459]
  decide +kernel

theorem arows11463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11463 = true := by
  rw [show D2M8K2.u11463 = KTree.node D2M8K2.u11461 (nat_lit 24764937) (nat_lit 1893885479) (nat_lit 0) D2M8K2.u11462 from rfl, allE_node, arows11461, irow11463, arows11462]
  all_goals rfl

theorem atot11463 : totK PD2M8K2 D2M8K2.u11463 = [0, 309865107400, 1219663233036, 1469747924921, 578665211124, 37485699534, 0, 0] := by
  rw [show D2M8K2.u11463 = KTree.node D2M8K2.u11461 (nat_lit 24764937) (nat_lit 1893885479) (nat_lit 0) D2M8K2.u11462 from rfl, totK_node, atot11461, atot11462]
  decide +kernel

theorem arows11468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11468 = true := by
  rw [show D2M8K2.u11468 = KTree.node D2M8K2.u11466 (nat_lit 24771195) (nat_lit 3786523991) (nat_lit 0) D2M8K2.u11467 from rfl, allE_node, arows11466, irow11468, arows11467]
  all_goals rfl

theorem atot11468 : totK PD2M8K2 D2M8K2.u11468 = [0, 387995454444, 1409052219052, 1436571594579, 336659863579, 13196099988, 0, 0] := by
  rw [show D2M8K2.u11468 = KTree.node D2M8K2.u11466 (nat_lit 24771195) (nat_lit 3786523991) (nat_lit 0) D2M8K2.u11467 from rfl, totK_node, atot11466, atot11467]
  decide +kernel

theorem arows11471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11471 = true := by
  rw [show D2M8K2.u11471 = KTree.node D2M8K2.u11469 (nat_lit 24774490) (nat_lit 2773789977) (nat_lit 0) D2M8K2.u11470 from rfl, allE_node, arows11469, irow11471, arows11470]
  all_goals rfl

theorem atot11471 : totK PD2M8K2 D2M8K2.u11471 = [0, 445830225596, 1548180766600, 1375837940453, 251688606392, 4980514959, 0, 0] := by
  rw [show D2M8K2.u11471 = KTree.node D2M8K2.u11469 (nat_lit 24774490) (nat_lit 2773789977) (nat_lit 0) D2M8K2.u11470 from rfl, totK_node, atot11469, atot11470]
  decide +kernel

theorem arows11475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11475 = true := by
  rw [show D2M8K2.u11475 = KTree.node D2M8K2.u11473 (nat_lit 24778185) (nat_lit 1605768986) (nat_lit 0) D2M8K2.u11474 from rfl, allE_node, arows11473, irow11475, arows11474]
  all_goals rfl

theorem atot11475 : totK PD2M8K2 D2M8K2.u11475 = [0, 233675638286, 1211151752622, 1640351377940, 483113714981, 19205723059, 0, 0] := by
  rw [show D2M8K2.u11475 = KTree.node D2M8K2.u11473 (nat_lit 24778185) (nat_lit 1605768986) (nat_lit 0) D2M8K2.u11474 from rfl, totK_node, atot11473, atot11474]
  decide +kernel

theorem arows11478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11478 = true := by
  rw [show D2M8K2.u11478 = KTree.node D2M8K2.u11476 (nat_lit 24784084) (nat_lit 2557963580) (nat_lit 0) D2M8K2.u11477 from rfl, allE_node, arows11476, irow11478, arows11477]
  all_goals rfl

theorem atot11478 : totK PD2M8K2 D2M8K2.u11478 = [0, 0, 772002877730, 1861455135284, 910442348776, 65508180106, 0, 0] := by
  rw [show D2M8K2.u11478 = KTree.node D2M8K2.u11476 (nat_lit 24784084) (nat_lit 2557963580) (nat_lit 0) D2M8K2.u11477 from rfl, totK_node, atot11476, atot11477]
  decide +kernel

theorem arows11484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11484 = true := by
  rw [show D2M8K2.u11484 = KTree.node D2M8K2.u11482 (nat_lit 24792570) (nat_lit 3943699390) (nat_lit 0) D2M8K2.u11483 from rfl, allE_node, arows11482, irow11484, arows11483]
  all_goals rfl

theorem atot11484 : totK PD2M8K2 D2M8K2.u11484 = [0, 0, 468262707046, 1558367720801, 1298069843370, 220762969667, 5352782441, 0] := by
  rw [show D2M8K2.u11484 = KTree.node D2M8K2.u11482 (nat_lit 24792570) (nat_lit 3943699390) (nat_lit 0) D2M8K2.u11483 from rfl, totK_node, atot11482, atot11483]
  decide +kernel

theorem arows11487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11487 = true := by
  rw [show D2M8K2.u11487 = KTree.node D2M8K2.u11485 (nat_lit 24796264) (nat_lit 2795690231) (nat_lit 0) D2M8K2.u11486 from rfl, allE_node, arows11485, irow11487, arows11486]
  all_goals rfl

theorem atot11487 : totK PD2M8K2 D2M8K2.u11487 = [0, 0, 496058783974, 1687640237884, 1238256428438, 135962295152, 1271866555, 0] := by
  rw [show D2M8K2.u11487 = KTree.node D2M8K2.u11485 (nat_lit 24796264) (nat_lit 2795690231) (nat_lit 0) D2M8K2.u11486 from rfl, totK_node, atot11485, atot11486]
  decide +kernel

theorem arows11491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11491 = true := by
  rw [show D2M8K2.u11491 = KTree.node D2M8K2.u11489 (nat_lit 24801489) (nat_lit 1855832370) (nat_lit 0) D2M8K2.u11490 from rfl, allE_node, arows11489, irow11491, arows11490]
  all_goals rfl

theorem atot11491 : totK PD2M8K2 D2M8K2.u11491 = [0, 444600726760, 1506629880924, 1350559454520, 280637035961, 12967964044, 0, 0] := by
  rw [show D2M8K2.u11491 = KTree.node D2M8K2.u11489 (nat_lit 24801489) (nat_lit 1855832370) (nat_lit 0) D2M8K2.u11490 from rfl, totK_node, atot11489, atot11490]
  decide +kernel

theorem arows11494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11494 = true := by
  rw [show D2M8K2.u11494 = KTree.node D2M8K2.u11492 (nat_lit 24805821) (nat_lit 1441911124) (nat_lit 0) D2M8K2.u11493 from rfl, allE_node, arows11492, irow11494, arows11493]
  all_goals rfl

theorem atot11494 : totK PD2M8K2 D2M8K2.u11494 = [0, 326054305919, 1287233260755, 1478035422712, 510525322291, 30800671508, 0, 0] := by
  rw [show D2M8K2.u11494 = KTree.node D2M8K2.u11492 (nat_lit 24805821) (nat_lit 1441911124) (nat_lit 0) D2M8K2.u11493 from rfl, totK_node, atot11492, atot11493]
  decide +kernel

theorem arows11499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11499 = true := by
  rw [show D2M8K2.u11499 = KTree.node D2M8K2.u11497 (nat_lit 24808545) (nat_lit 1841244827) (nat_lit 0) D2M8K2.u11498 from rfl, allE_node, arows11497, irow11499, arows11498]
  all_goals rfl

theorem atot11499 : totK PD2M8K2 D2M8K2.u11499 = [0, 413820936442, 1398918873229, 1370290493036, 366099216413, 17259183819, 0, 0] := by
  rw [show D2M8K2.u11499 = KTree.node D2M8K2.u11497 (nat_lit 24808545) (nat_lit 1841244827) (nat_lit 0) D2M8K2.u11498 from rfl, totK_node, atot11497, atot11498]
  decide +kernel

theorem arows11502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11502 = true := by
  rw [show D2M8K2.u11502 = KTree.node D2M8K2.u11500 (nat_lit 24811942) (nat_lit 1088912517) (nat_lit 0) D2M8K2.u11501 from rfl, allE_node, arows11500, irow11502, arows11501]
  all_goals rfl

theorem atot11502 : totK PD2M8K2 D2M8K2.u11502 = [0, 414047057995, 1468695187784, 1377823329449, 310233933349, 13162154230, 0, 0] := by
  rw [show D2M8K2.u11502 = KTree.node D2M8K2.u11500 (nat_lit 24811942) (nat_lit 1088912517) (nat_lit 0) D2M8K2.u11501 from rfl, totK_node, atot11500, atot11501]
  decide +kernel

theorem arows11506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11506 = true := by
  rw [show D2M8K2.u11506 = KTree.node D2M8K2.u11504 (nat_lit 24815058) (nat_lit 3474668509) (nat_lit 0) D2M8K2.u11505 from rfl, allE_node, arows11504, irow11506, arows11505]
  all_goals rfl

theorem atot11506 : totK PD2M8K2 D2M8K2.u11506 = [0, 439668458485, 1569579237298, 1393456200633, 224944503269, 3666196603, 0, 0] := by
  rw [show D2M8K2.u11506 = KTree.node D2M8K2.u11504 (nat_lit 24815058) (nat_lit 3474668509) (nat_lit 0) D2M8K2.u11505 from rfl, totK_node, atot11504, atot11505]
  decide +kernel

theorem arows11509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11509 = true := by
  rw [show D2M8K2.u11509 = KTree.node D2M8K2.u11507 (nat_lit 24822346) (nat_lit 2791058013) (nat_lit 0) D2M8K2.u11508 from rfl, allE_node, arows11507, irow11509, arows11508]
  all_goals rfl

theorem atot11509 : totK PD2M8K2 D2M8K2.u11509 = [0, 0, 751162837330, 1934283489039, 831892795334, 44503612959, 0, 0] := by
  rw [show D2M8K2.u11509 = KTree.node D2M8K2.u11507 (nat_lit 24822346) (nat_lit 2791058013) (nat_lit 0) D2M8K2.u11508 from rfl, totK_node, atot11507, atot11508]
  decide +kernel

theorem arows11518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11518 = true := by
  rw [show D2M8K2.u11518 = KTree.node D2M8K2.u11516 (nat_lit 24829137) (nat_lit 1854253853) (nat_lit 0) D2M8K2.u11517 from rfl, allE_node, arows11516, irow11518, arows11517]
  all_goals rfl

theorem atot11518 : totK PD2M8K2 D2M8K2.u11518 = [0, 0, 744217413215, 1880558534732, 907319233104, 51205043486, 0, 0] := by
  rw [show D2M8K2.u11518 = KTree.node D2M8K2.u11516 (nat_lit 24829137) (nat_lit 1854253853) (nat_lit 0) D2M8K2.u11517 from rfl, totK_node, atot11516, atot11517]
  decide +kernel

theorem arows11521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11521 = true := by
  rw [show D2M8K2.u11521 = KTree.node D2M8K2.u11519 (nat_lit 24835529) (nat_lit 1614079112) (nat_lit 0) D2M8K2.u11520 from rfl, allE_node, arows11519, irow11521, arows11520]
  all_goals rfl

theorem atot11521 : totK PD2M8K2 D2M8K2.u11521 = [0, 0, 593981900764, 1791653018793, 1084374854193, 88690997730, 0, 0] := by
  rw [show D2M8K2.u11521 = KTree.node D2M8K2.u11519 (nat_lit 24835529) (nat_lit 1614079112) (nat_lit 0) D2M8K2.u11520 from rfl, totK_node, atot11519, atot11520]
  decide +kernel

theorem arows11525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11525 = true := by
  rw [show D2M8K2.u11525 = KTree.node D2M8K2.u11523 (nat_lit 24846285) (nat_lit 1408522282) (nat_lit 0) D2M8K2.u11524 from rfl, allE_node, arows11523, irow11525, arows11524]
  all_goals rfl

theorem atot11525 : totK PD2M8K2 D2M8K2.u11525 = [0, 430002671482, 1289201320385, 1213254966870, 592256474480, 110214151206, 1429815836, 0] := by
  rw [show D2M8K2.u11525 = KTree.node D2M8K2.u11523 (nat_lit 24846285) (nat_lit 1408522282) (nat_lit 0) D2M8K2.u11524 from rfl, totK_node, atot11523, atot11524]
  decide +kernel

theorem arows11528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11528 = true := by
  rw [show D2M8K2.u11528 = KTree.node D2M8K2.u11526 (nat_lit 24849130) (nat_lit 3919268871) (nat_lit 0) D2M8K2.u11527 from rfl, allE_node, arows11526, irow11528, arows11527]
  all_goals rfl

theorem atot11528 : totK PD2M8K2 D2M8K2.u11528 = [0, 403459321782, 1388402921140, 1416327363120, 403258770381, 13293733873, 0, 0] := by
  rw [show D2M8K2.u11528 = KTree.node D2M8K2.u11526 (nat_lit 24849130) (nat_lit 3919268871) (nat_lit 0) D2M8K2.u11527 from rfl, totK_node, atot11526, atot11527]
  decide +kernel

theorem arows11533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11533 = true := by
  rw [show D2M8K2.u11533 = KTree.node D2M8K2.u11531 (nat_lit 24852620) (nat_lit 3177961328) (nat_lit 0) D2M8K2.u11532 from rfl, allE_node, arows11531, irow11533, arows11532]
  all_goals rfl

theorem atot11533 : totK PD2M8K2 D2M8K2.u11533 = [0, 403717775972, 1456370355158, 1427142031722, 317530784990, 9101090546, 0, 0] := by
  rw [show D2M8K2.u11533 = KTree.node D2M8K2.u11531 (nat_lit 24852620) (nat_lit 3177961328) (nat_lit 0) D2M8K2.u11532 from rfl, totK_node, atot11531, atot11532]
  decide +kernel

theorem arows11536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11536 = true := by
  rw [show D2M8K2.u11536 = KTree.node D2M8K2.u11534 (nat_lit 24859542) (nat_lit 3662052510) (nat_lit 0) D2M8K2.u11535 from rfl, allE_node, arows11534, irow11536, arows11535]
  all_goals rfl

theorem atot11536 : totK PD2M8K2 D2M8K2.u11536 = [0, 429020973273, 1458900233123, 1403469858855, 324469964421, 9266913122, 0, 0] := by
  rw [show D2M8K2.u11536 = KTree.node D2M8K2.u11534 (nat_lit 24859542) (nat_lit 3662052510) (nat_lit 0) D2M8K2.u11535 from rfl, totK_node, atot11534, atot11535]
  decide +kernel

theorem arows11540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11540 = true := by
  rw [show D2M8K2.u11540 = KTree.node D2M8K2.u11538 (nat_lit 24866405) (nat_lit 2363874554) (nat_lit 0) D2M8K2.u11539 from rfl, allE_node, arows11538, irow11540, arows11539]
  all_goals rfl

theorem atot11540 : totK PD2M8K2 D2M8K2.u11540 = [0, 0, 757577730247, 1858974091045, 923086886904, 62684323292, 0, 0] := by
  rw [show D2M8K2.u11540 = KTree.node D2M8K2.u11538 (nat_lit 24866405) (nat_lit 2363874554) (nat_lit 0) D2M8K2.u11539 from rfl, totK_node, atot11538, atot11539]
  decide +kernel

theorem arows11543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11543 = true := by
  rw [show D2M8K2.u11543 = KTree.node D2M8K2.u11541 (nat_lit 24870988) (nat_lit 3839840330) (nat_lit 0) D2M8K2.u11542 from rfl, allE_node, arows11541, irow11543, arows11542]
  all_goals rfl

theorem atot11543 : totK PD2M8K2 D2M8K2.u11543 = [0, 0, 555115795570, 1682131396283, 1215077429920, 141583904992, 1323630408, 0] := by
  rw [show D2M8K2.u11543 = KTree.node D2M8K2.u11541 (nat_lit 24870988) (nat_lit 3839840330) (nat_lit 0) D2M8K2.u11542 from rfl, totK_node, atot11541, atot11542]
  decide +kernel

theorem arows11549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11549 = true := by
  rw [show D2M8K2.u11549 = KTree.node D2M8K2.u11547 (nat_lit 24875462) (nat_lit 3888249873) (nat_lit 0) D2M8K2.u11548 from rfl, allE_node, arows11547, irow11549, arows11548]
  all_goals rfl

theorem atot11549 : totK PD2M8K2 D2M8K2.u11549 = [0, 0, 490505510921, 1649142031583, 1294160996717, 154808720059, 1332468113, 0] := by
  rw [show D2M8K2.u11549 = KTree.node D2M8K2.u11547 (nat_lit 24875462) (nat_lit 3888249873) (nat_lit 0) D2M8K2.u11548 from rfl, totK_node, atot11547, atot11548]
  decide +kernel

theorem arows11552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11552 = true := by
  rw [show D2M8K2.u11552 = KTree.node D2M8K2.u11550 (nat_lit 24882369) (nat_lit 947204864) (nat_lit 0) D2M8K2.u11551 from rfl, allE_node, arows11550, irow11552, arows11551]
  all_goals rfl

theorem atot11552 : totK PD2M8K2 D2M8K2.u11552 = [261533257835, 580991266440, 399192923119, 906568737320, 1135496883647, 273414375964, 9533751846, 0] := by
  rw [show D2M8K2.u11552 = KTree.node D2M8K2.u11550 (nat_lit 24882369) (nat_lit 947204864) (nat_lit 0) D2M8K2.u11551 from rfl, totK_node, atot11550, atot11551]
  decide +kernel

theorem arows11556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11556 = true := by
  rw [show D2M8K2.u11556 = KTree.node D2M8K2.u11554 (nat_lit 24885883) (nat_lit 2240577022) (nat_lit 0) D2M8K2.u11555 from rfl, allE_node, arows11554, irow11556, arows11555]
  all_goals rfl

theorem atot11556 : totK PD2M8K2 D2M8K2.u11556 = [424054126839, 1576482180381, 1400177554427, 197286873924, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11556 = KTree.node D2M8K2.u11554 (nat_lit 24885883) (nat_lit 2240577022) (nat_lit 0) D2M8K2.u11555 from rfl, totK_node, atot11554, atot11555]
  decide +kernel

theorem arows11559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11559 = true := by
  rw [show D2M8K2.u11559 = KTree.node D2M8K2.u11557 (nat_lit 24892618) (nat_lit 3748938820) (nat_lit 0) D2M8K2.u11558 from rfl, allE_node, arows11557, irow11559, arows11558]
  all_goals rfl

theorem atot11559 : totK PD2M8K2 D2M8K2.u11559 = [427394811595, 1444830467639, 1368401590203, 316339703226, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11559 = KTree.node D2M8K2.u11557 (nat_lit 24892618) (nat_lit 3748938820) (nat_lit 0) D2M8K2.u11558 from rfl, totK_node, atot11557, atot11558]
  decide +kernel

theorem arows11564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11564 = true := by
  rw [show D2M8K2.u11564 = KTree.node D2M8K2.u11562 (nat_lit 24896809) (nat_lit 1469870519) (nat_lit 0) D2M8K2.u11563 from rfl, allE_node, arows11562, irow11564, arows11563]
  all_goals rfl

theorem atot11564 : totK PD2M8K2 D2M8K2.u11564 = [424809830965, 1436549957221, 1365903541960, 320430505863, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u11564 = KTree.node D2M8K2.u11562 (nat_lit 24896809) (nat_lit 1469870519) (nat_lit 0) D2M8K2.u11563 from rfl, totK_node, atot11562, atot11563]
  decide +kernel

theorem arows11567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11567 = true := by
  rw [show D2M8K2.u11567 = KTree.node D2M8K2.u11565 (nat_lit 24900530) (nat_lit 3227414224) (nat_lit 0) D2M8K2.u11566 from rfl, allE_node, arows11565, irow11567, arows11566]
  all_goals rfl

theorem atot11567 : totK PD2M8K2 D2M8K2.u11567 = [437984760583, 1534273386962, 1368821355426, 243896948865, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u11567 = KTree.node D2M8K2.u11565 (nat_lit 24900530) (nat_lit 3227414224) (nat_lit 0) D2M8K2.u11566 from rfl, totK_node, atot11565, atot11566]
  decide +kernel

theorem arows11571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11571 = true := by
  rw [show D2M8K2.u11571 = KTree.node D2M8K2.u11569 (nat_lit 24903922) (nat_lit 4171954186) (nat_lit 0) D2M8K2.u11570 from rfl, allE_node, arows11569, irow11571, arows11570]
  all_goals rfl

theorem atot11571 : totK PD2M8K2 D2M8K2.u11571 = [0, 801671031594, 1882153163428, 786350239425, 43865840370, 0, 0, 0] := by
  rw [show D2M8K2.u11571 = KTree.node D2M8K2.u11569 (nat_lit 24903922) (nat_lit 4171954186) (nat_lit 0) D2M8K2.u11570 from rfl, totK_node, atot11569, atot11570]
  decide +kernel

theorem arows11574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11574 = true := by
  rw [show D2M8K2.u11574 = KTree.node D2M8K2.u11572 (nat_lit 24910972) (nat_lit 3854718101) (nat_lit 0) D2M8K2.u11573 from rfl, allE_node, arows11572, irow11574, arows11573]
  all_goals rfl

theorem atot11574 : totK PD2M8K2 D2M8K2.u11574 = [0, 465174381225, 1636081904462, 1240357645620, 164219556191, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11574 = KTree.node D2M8K2.u11572 (nat_lit 24910972) (nat_lit 3854718101) (nat_lit 0) D2M8K2.u11573 from rfl, totK_node, atot11572, atot11573]
  decide +kernel

theorem arows11581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11581 = true := by
  rw [show D2M8K2.u11581 = KTree.node D2M8K2.u11579 (nat_lit 24917870) (nat_lit 3052271493) (nat_lit 0) D2M8K2.u11580 from rfl, allE_node, arows11579, irow11581, arows11580]
  all_goals rfl

theorem atot11581 : totK PD2M8K2 D2M8K2.u11581 = [0, 738588744783, 1881676182731, 885583316656, 50993105736, 0, 0, 0] := by
  rw [show D2M8K2.u11581 = KTree.node D2M8K2.u11579 (nat_lit 24917870) (nat_lit 3052271493) (nat_lit 0) D2M8K2.u11580 from rfl, totK_node, atot11579, atot11580]
  decide +kernel

theorem arows11584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11584 = true := by
  rw [show D2M8K2.u11584 = KTree.node D2M8K2.u11582 (nat_lit 24922884) (nat_lit 2859164730) (nat_lit 0) D2M8K2.u11583 from rfl, allE_node, arows11582, irow11584, arows11583]
  all_goals rfl

theorem atot11584 : totK PD2M8K2 D2M8K2.u11584 = [355056847956, 1278384353107, 1452030104130, 521322983394, 28369299303, 0, 0, 0] := by
  rw [show D2M8K2.u11584 = KTree.node D2M8K2.u11582 (nat_lit 24922884) (nat_lit 2859164730) (nat_lit 0) D2M8K2.u11583 from rfl, totK_node, atot11582, atot11583]
  decide +kernel

theorem arows11588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11588 = true := by
  rw [show D2M8K2.u11588 = KTree.node D2M8K2.u11586 (nat_lit 24931008) (nat_lit 2665809682) (nat_lit 0) D2M8K2.u11587 from rfl, allE_node, arows11586, irow11588, arows11587]
  all_goals rfl

theorem atot11588 : totK PD2M8K2 D2M8K2.u11588 = [315401126895, 1182470305142, 1522334116161, 594758698350, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u11588 = KTree.node D2M8K2.u11586 (nat_lit 24931008) (nat_lit 2665809682) (nat_lit 0) D2M8K2.u11587 from rfl, totK_node, atot11586, atot11587]
  decide +kernel

theorem arows11591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11591 = true := by
  rw [show D2M8K2.u11591 = KTree.node D2M8K2.u11589 (nat_lit 24933934) (nat_lit 3879537574) (nat_lit 0) D2M8K2.u11590 from rfl, allE_node, arows11589, irow11591, arows11590]
  all_goals rfl

theorem atot11591 : totK PD2M8K2 D2M8K2.u11591 = [372177093382, 1427552539871, 1461287355068, 335470199471, 13036865798, 0, 0, 0] := by
  rw [show D2M8K2.u11591 = KTree.node D2M8K2.u11589 (nat_lit 24933934) (nat_lit 3879537574) (nat_lit 0) D2M8K2.u11590 from rfl, totK_node, atot11589, atot11590]
  decide +kernel

theorem arows11596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11596 = true := by
  rw [show D2M8K2.u11596 = KTree.node D2M8K2.u11594 (nat_lit 24938092) (nat_lit 2749677981) (nat_lit 0) D2M8K2.u11595 from rfl, allE_node, arows11594, irow11596, arows11595]
  all_goals rfl

theorem atot11596 : totK PD2M8K2 D2M8K2.u11596 = [476773240288, 1530621044452, 1329356723116, 289211442316, 12000481954, 0, 0, 0] := by
  rw [show D2M8K2.u11596 = KTree.node D2M8K2.u11594 (nat_lit 24938092) (nat_lit 2749677981) (nat_lit 0) D2M8K2.u11595 from rfl, totK_node, atot11594, atot11595]
  decide +kernel

theorem arows11599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11599 = true := by
  rw [show D2M8K2.u11599 = KTree.node D2M8K2.u11597 (nat_lit 24941524) (nat_lit 3264224483) (nat_lit 0) D2M8K2.u11598 from rfl, allE_node, arows11597, irow11599, arows11598]
  all_goals rfl

theorem atot11599 : totK PD2M8K2 D2M8K2.u11599 = [441063229386, 1549745119674, 1401520563421, 249225273344, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u11599 = KTree.node D2M8K2.u11597 (nat_lit 24941524) (nat_lit 3264224483) (nat_lit 0) D2M8K2.u11598 from rfl, totK_node, atot11597, atot11598]
  decide +kernel

theorem arows11603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11603 = true := by
  rw [show D2M8K2.u11603 = KTree.node D2M8K2.u11601 (nat_lit 24945273) (nat_lit 627047512) (nat_lit 0) D2M8K2.u11602 from rfl, allE_node, arows11601, irow11603, arows11602]
  all_goals rfl

theorem atot11603 : totK PD2M8K2 D2M8K2.u11603 = [36951561255, 891670677770, 1842271061537, 799965970163, 55759125209, 0, 0, 0] := by
  rw [show D2M8K2.u11603 = KTree.node D2M8K2.u11601 (nat_lit 24945273) (nat_lit 627047512) (nat_lit 0) D2M8K2.u11602 from rfl, totK_node, atot11601, atot11602]
  decide +kernel

theorem arows11606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11606 = true := by
  rw [show D2M8K2.u11606 = KTree.node D2M8K2.u11604 (nat_lit 24951681) (nat_lit 1666455029) (nat_lit 0) D2M8K2.u11605 from rfl, allE_node, arows11604, irow11606, arows11605]
  all_goals rfl

theorem atot11606 : totK PD2M8K2 D2M8K2.u11606 = [0, 283588752921, 1192391971801, 1530360601404, 565034718334, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11606 = KTree.node D2M8K2.u11604 (nat_lit 24951681) (nat_lit 1666455029) (nat_lit 0) D2M8K2.u11605 from rfl, totK_node, atot11604, atot11605]
  decide +kernel

theorem arows11612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11612 = true := by
  rw [show D2M8K2.u11612 = KTree.node D2M8K2.u11610 (nat_lit 24954729) (nat_lit 1889978399) (nat_lit 0) D2M8K2.u11611 from rfl, allE_node, arows11610, irow11612, arows11611]
  all_goals rfl

theorem atot11612 : totK PD2M8K2 D2M8K2.u11612 = [0, 425762217417, 1519913962902, 1409880137917, 251866057796, 5159868635, 0, 0] := by
  rw [show D2M8K2.u11612 = KTree.node D2M8K2.u11610 (nat_lit 24954729) (nat_lit 1889978399) (nat_lit 0) D2M8K2.u11611 from rfl, totK_node, atot11610, atot11611]
  decide +kernel

theorem arows11615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11615 = true := by
  rw [show D2M8K2.u11615 = KTree.node D2M8K2.u11613 (nat_lit 24959014) (nat_lit 3752604707) (nat_lit 0) D2M8K2.u11614 from rfl, allE_node, arows11613, irow11615, arows11614]
  all_goals rfl

theorem atot11615 : totK PD2M8K2 D2M8K2.u11615 = [0, 482586247790, 1553957289496, 1329348538562, 253115074484, 5218872685, 0, 0] := by
  rw [show D2M8K2.u11615 = KTree.node D2M8K2.u11613 (nat_lit 24959014) (nat_lit 3752604707) (nat_lit 0) D2M8K2.u11614 from rfl, totK_node, atot11613, atot11614]
  decide +kernel

theorem arows11619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11619 = true := by
  rw [show D2M8K2.u11619 = KTree.node D2M8K2.u11617 (nat_lit 24962882) (nat_lit 3202469189) (nat_lit 0) D2M8K2.u11618 from rfl, allE_node, arows11617, irow11619, arows11618]
  all_goals rfl

theorem atot11619 : totK PD2M8K2 D2M8K2.u11619 = [0, 444844462457, 1613146869733, 1391802152765, 190527365143, 1415142070, 0, 0] := by
  rw [show D2M8K2.u11619 = KTree.node D2M8K2.u11617 (nat_lit 24962882) (nat_lit 3202469189) (nat_lit 0) D2M8K2.u11618 from rfl, totK_node, atot11617, atot11618]
  decide +kernel

theorem arows11622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11622 = true := by
  rw [show D2M8K2.u11622 = KTree.node D2M8K2.u11620 (nat_lit 24966413) (nat_lit 1836107993) (nat_lit 0) D2M8K2.u11621 from rfl, allE_node, arows11620, irow11622, arows11621]
  all_goals rfl

theorem atot11622 : totK PD2M8K2 D2M8K2.u11622 = [413201475250, 1107361339787, 960188124334, 803466136910, 263927749761, 9302370699, 0, 0] := by
  rw [show D2M8K2.u11622 = KTree.node D2M8K2.u11620 (nat_lit 24966413) (nat_lit 1836107993) (nat_lit 0) D2M8K2.u11621 from rfl, totK_node, atot11620, atot11621]
  decide +kernel

theorem arows11627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11627 = true := by
  rw [show D2M8K2.u11627 = KTree.node D2M8K2.u11625 (nat_lit 24970276) (nat_lit 3861555415) (nat_lit 0) D2M8K2.u11626 from rfl, allE_node, arows11625, irow11627, arows11626]
  all_goals rfl

theorem atot11627 : totK PD2M8K2 D2M8K2.u11627 = [423617078586, 1538850364850, 1421116804367, 243927663254, 9784801431, 0, 0, 0] := by
  rw [show D2M8K2.u11627 = KTree.node D2M8K2.u11625 (nat_lit 24970276) (nat_lit 3861555415) (nat_lit 0) D2M8K2.u11626 from rfl, totK_node, atot11625, atot11626]
  decide +kernel

theorem arows11630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11630 = true := by
  rw [show D2M8K2.u11630 = KTree.node D2M8K2.u11628 (nat_lit 24973076) (nat_lit 3239739834) (nat_lit 0) D2M8K2.u11629 from rfl, allE_node, arows11628, irow11630, arows11629]
  all_goals rfl

theorem atot11630 : totK PD2M8K2 D2M8K2.u11630 = [394060497076, 1300847874602, 1386674766028, 521919293933, 26950892994, 0, 0, 0] := by
  rw [show D2M8K2.u11630 = KTree.node D2M8K2.u11628 (nat_lit 24973076) (nat_lit 3239739834) (nat_lit 0) D2M8K2.u11629 from rfl, totK_node, atot11628, atot11629]
  decide +kernel

theorem arows11634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11634 = true := by
  rw [show D2M8K2.u11634 = KTree.node D2M8K2.u11632 (nat_lit 24976225) (nat_lit 1547907610) (nat_lit 0) D2M8K2.u11633 from rfl, allE_node, arows11632, irow11634, arows11633]
  all_goals rfl

theorem atot11634 : totK PD2M8K2 D2M8K2.u11634 = [377174122693, 1413795192297, 1470173717518, 338189521521, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11634 = KTree.node D2M8K2.u11632 (nat_lit 24976225) (nat_lit 1547907610) (nat_lit 0) D2M8K2.u11633 from rfl, totK_node, atot11632, atot11633]
  decide +kernel

theorem arows11637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11637 = true := by
  rw [show D2M8K2.u11637 = KTree.node D2M8K2.u11635 (nat_lit 24982997) (nat_lit 2038000931) (nat_lit 0) D2M8K2.u11636 from rfl, allE_node, arows11635, irow11637, arows11636]
  all_goals rfl

theorem atot11637 : totK PD2M8K2 D2M8K2.u11637 = [440650963474, 1529456873254, 1381070671220, 245558432997, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u11637 = KTree.node D2M8K2.u11635 (nat_lit 24982997) (nat_lit 2038000931) (nat_lit 0) D2M8K2.u11636 from rfl, totK_node, atot11635, atot11636]
  decide +kernel

theorem arows11645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11645 = true := by
  rw [show D2M8K2.u11645 = KTree.node D2M8K2.u11643 (nat_lit 24986648) (nat_lit 2899190801) (nat_lit 0) D2M8K2.u11644 from rfl, allE_node, arows11643, irow11645, arows11644]
  all_goals rfl

theorem atot11645 : totK PD2M8K2 D2M8K2.u11645 = [54703274150, 919934123566, 1834279080051, 684353610038, 31373601116, 0, 0, 0] := by
  rw [show D2M8K2.u11645 = KTree.node D2M8K2.u11643 (nat_lit 24986648) (nat_lit 2899190801) (nat_lit 0) D2M8K2.u11644 from rfl, totK_node, atot11643, atot11644]
  decide +kernel

theorem arows11648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11648 = true := by
  rw [show D2M8K2.u11648 = KTree.node D2M8K2.u11646 (nat_lit 24990689) (nat_lit 2203885956) (nat_lit 0) D2M8K2.u11647 from rfl, allE_node, arows11646, irow11648, arows11647]
  all_goals rfl

theorem atot11648 : totK PD2M8K2 D2M8K2.u11648 = [0, 506337161137, 1668111124157, 1239880312670, 144189403189, 1206465782, 0, 0] := by
  rw [show D2M8K2.u11648 = KTree.node D2M8K2.u11646 (nat_lit 24990689) (nat_lit 2203885956) (nat_lit 0) D2M8K2.u11647 from rfl, totK_node, atot11646, atot11647]
  decide +kernel

theorem arows11652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11652 = true := by
  rw [show D2M8K2.u11652 = KTree.node D2M8K2.u11650 (nat_lit 24995116) (nat_lit 3842413354) (nat_lit 0) D2M8K2.u11651 from rfl, allE_node, arows11650, irow11652, arows11651]
  all_goals rfl

theorem atot11652 : totK PD2M8K2 D2M8K2.u11652 = [0, 443619422642, 1560422130428, 1309808963207, 246703530415, 9579374723, 0, 0] := by
  rw [show D2M8K2.u11652 = KTree.node D2M8K2.u11650 (nat_lit 24995116) (nat_lit 3842413354) (nat_lit 0) D2M8K2.u11651 from rfl, totK_node, atot11650, atot11651]
  decide +kernel

theorem arows11655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11655 = true := by
  rw [show D2M8K2.u11655 = KTree.node D2M8K2.u11653 (nat_lit 25001671) (nat_lit 2327454459) (nat_lit 0) D2M8K2.u11654 from rfl, allE_node, arows11653, irow11655, arows11654]
  all_goals rfl

theorem atot11655 : totK PD2M8K2 D2M8K2.u11655 = [0, 417887997553, 1547766369326, 1319520955844, 213008027729, 5449443519, 0, 0] := by
  rw [show D2M8K2.u11655 = KTree.node D2M8K2.u11653 (nat_lit 25001671) (nat_lit 2327454459) (nat_lit 0) D2M8K2.u11654 from rfl, totK_node, atot11653, atot11654]
  decide +kernel

theorem arows11660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11660 = true := by
  rw [show D2M8K2.u11660 = KTree.node D2M8K2.u11658 (nat_lit 25005673) (nat_lit 1458258326) (nat_lit 0) D2M8K2.u11659 from rfl, allE_node, arows11658, irow11660, arows11659]
  all_goals rfl

theorem atot11660 : totK PD2M8K2 D2M8K2.u11660 = [341618104599, 1185392258314, 1362077383774, 612762329597, 75320773508, 2561774784, 0, 0] := by
  rw [show D2M8K2.u11660 = KTree.node D2M8K2.u11658 (nat_lit 25005673) (nat_lit 1458258326) (nat_lit 0) D2M8K2.u11659 from rfl, totK_node, atot11658, atot11659]
  decide +kernel

theorem arows11663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11663 = true := by
  rw [show D2M8K2.u11663 = KTree.node D2M8K2.u11661 (nat_lit 25052399) (nat_lit 2775266535) (nat_lit 0) D2M8K2.u11662 from rfl, allE_node, arows11661, irow11663, arows11662]
  all_goals rfl

theorem atot11663 : totK PD2M8K2 D2M8K2.u11663 = [434038324453, 1580023282183, 1395793128071, 198225262281, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11663 = KTree.node D2M8K2.u11661 (nat_lit 25052399) (nat_lit 2775266535) (nat_lit 0) D2M8K2.u11662 from rfl, totK_node, atot11661, atot11662]
  decide +kernel

theorem arows11667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11667 = true := by
  rw [show D2M8K2.u11667 = KTree.node D2M8K2.u11665 (nat_lit 25055517) (nat_lit 1565751641) (nat_lit 0) D2M8K2.u11666 from rfl, allE_node, arows11665, irow11667, arows11666]
  all_goals rfl

theorem atot11667 : totK PD2M8K2 D2M8K2.u11667 = [315081984131, 1213905777708, 1485592197718, 582420695784, 37416953616, 0, 0, 0] := by
  rw [show D2M8K2.u11667 = KTree.node D2M8K2.u11665 (nat_lit 25055517) (nat_lit 1565751641) (nat_lit 0) D2M8K2.u11666 from rfl, totK_node, atot11665, atot11666]
  decide +kernel

theorem arows11670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11670 = true := by
  rw [show D2M8K2.u11670 = KTree.node D2M8K2.u11668 (nat_lit 25058482) (nat_lit 3657504572) (nat_lit 0) D2M8K2.u11669 from rfl, allE_node, arows11668, irow11670, arows11669]
  all_goals rfl

theorem atot11670 : totK PD2M8K2 D2M8K2.u11670 = [415288423685, 1430079118383, 1413206804399, 332943399535, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11670 = KTree.node D2M8K2.u11668 (nat_lit 25058482) (nat_lit 3657504572) (nat_lit 0) D2M8K2.u11669 from rfl, totK_node, atot11668, atot11669]
  decide +kernel

theorem arows11676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11676 = true := by
  rw [show D2M8K2.u11676 = KTree.node D2M8K2.u11674 (nat_lit 25062421) (nat_lit 1243102186) (nat_lit 0) D2M8K2.u11675 from rfl, allE_node, arows11674, irow11676, arows11675]
  all_goals rfl

theorem atot11676 : totK PD2M8K2 D2M8K2.u11676 = [435082687204, 1473306254485, 1364178299964, 319410189587, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u11676 = KTree.node D2M8K2.u11674 (nat_lit 25062421) (nat_lit 1243102186) (nat_lit 0) D2M8K2.u11675 from rfl, totK_node, atot11674, atot11675]
  decide +kernel

theorem arows11679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11679 = true := by
  rw [show D2M8K2.u11679 = KTree.node D2M8K2.u11677 (nat_lit 25065871) (nat_lit 2426140697) (nat_lit 0) D2M8K2.u11678 from rfl, allE_node, arows11677, irow11679, arows11678]
  all_goals rfl

theorem atot11679 : totK PD2M8K2 D2M8K2.u11679 = [92722701599, 1075328103108, 1829324225214, 561466795715, 24323361067, 0, 0, 0] := by
  rw [show D2M8K2.u11679 = KTree.node D2M8K2.u11677 (nat_lit 25065871) (nat_lit 2426140697) (nat_lit 0) D2M8K2.u11678 from rfl, totK_node, atot11677, atot11678]
  decide +kernel

theorem arows11683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11683 = true := by
  rw [show D2M8K2.u11683 = KTree.node D2M8K2.u11681 (nat_lit 25073758) (nat_lit 3756317184) (nat_lit 0) D2M8K2.u11682 from rfl, allE_node, arows11681, irow11683, arows11682]
  all_goals rfl

theorem atot11683 : totK PD2M8K2 D2M8K2.u11683 = [0, 501101558569, 1692409812405, 1224835799145, 137911159748, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11683 = KTree.node D2M8K2.u11681 (nat_lit 25073758) (nat_lit 3756317184) (nat_lit 0) D2M8K2.u11682 from rfl, totK_node, atot11681, atot11682]
  decide +kernel

theorem arows11686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11686 = true := by
  rw [show D2M8K2.u11686 = KTree.node D2M8K2.u11684 (nat_lit 25078296) (nat_lit 3500587655) (nat_lit 0) D2M8K2.u11685 from rfl, allE_node, arows11684, irow11686, arows11685]
  all_goals rfl

theorem atot11686 : totK PD2M8K2 D2M8K2.u11686 = [0, 747459910175, 1912077856897, 905490485998, 47871368963, 0, 0, 0] := by
  rw [show D2M8K2.u11686 = KTree.node D2M8K2.u11684 (nat_lit 25078296) (nat_lit 3500587655) (nat_lit 0) D2M8K2.u11685 from rfl, totK_node, atot11684, atot11685]
  decide +kernel

theorem arows11691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11691 = true := by
  rw [show D2M8K2.u11691 = KTree.node D2M8K2.u11689 (nat_lit 25084830) (nat_lit 3855791684) (nat_lit 0) D2M8K2.u11690 from rfl, allE_node, arows11689, irow11691, arows11690]
  all_goals rfl

theorem atot11691 : totK PD2M8K2 D2M8K2.u11691 = [11364832707, 441052552318, 1549310086014, 1305498944608, 227578619026, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11691 = KTree.node D2M8K2.u11689 (nat_lit 25084830) (nat_lit 3855791684) (nat_lit 0) D2M8K2.u11690 from rfl, totK_node, atot11689, atot11690]
  decide +kernel

theorem arows11694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11694 = true := by
  rw [show D2M8K2.u11694 = KTree.node D2M8K2.u11692 (nat_lit 25092174) (nat_lit 3261546917) (nat_lit 0) D2M8K2.u11693 from rfl, allE_node, arows11692, irow11694, arows11693]
  all_goals rfl

theorem atot11694 : totK PD2M8K2 D2M8K2.u11694 = [477577125845, 1599954356883, 1318229998088, 190469455487, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11694 = KTree.node D2M8K2.u11692 (nat_lit 25092174) (nat_lit 3261546917) (nat_lit 0) D2M8K2.u11693 from rfl, totK_node, atot11692, atot11693]
  decide +kernel

theorem arows11698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11698 = true := by
  rw [show D2M8K2.u11698 = KTree.node D2M8K2.u11696 (nat_lit 25096126) (nat_lit 3822977933) (nat_lit 0) D2M8K2.u11697 from rfl, allE_node, arows11696, irow11698, arows11697]
  all_goals rfl

theorem atot11698 : totK PD2M8K2 D2M8K2.u11698 = [315597201980, 1255748697456, 1499952180099, 550468794651, 33123195192, 0, 0, 0] := by
  rw [show D2M8K2.u11698 = KTree.node D2M8K2.u11696 (nat_lit 25096126) (nat_lit 3822977933) (nat_lit 0) D2M8K2.u11697 from rfl, totK_node, atot11696, atot11697]
  decide +kernel

theorem arows11701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11701 = true := by
  rw [show D2M8K2.u11701 = KTree.node D2M8K2.u11699 (nat_lit 25098953) (nat_lit 1788386491) (nat_lit 0) D2M8K2.u11700 from rfl, allE_node, arows11699, irow11701, arows11700]
  all_goals rfl

theorem atot11701 : totK PD2M8K2 D2M8K2.u11701 = [425468763121, 1441408874110, 1370574244058, 338359845262, 17475312391, 0, 0, 0] := by
  rw [show D2M8K2.u11701 = KTree.node D2M8K2.u11699 (nat_lit 25098953) (nat_lit 1788386491) (nat_lit 0) D2M8K2.u11700 from rfl, totK_node, atot11699, atot11700]
  decide +kernel

theorem arows11708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11708 = true := by
  rw [show D2M8K2.u11708 = KTree.node D2M8K2.u11706 (nat_lit 25108926) (nat_lit 4061139483) (nat_lit 0) D2M8K2.u11707 from rfl, allE_node, arows11706, irow11708, arows11707]
  all_goals rfl

theorem atot11708 : totK PD2M8K2 D2M8K2.u11708 = [427983732745, 1503684639448, 1417491460967, 285958775610, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u11708 = KTree.node D2M8K2.u11706 (nat_lit 25108926) (nat_lit 4061139483) (nat_lit 0) D2M8K2.u11707 from rfl, totK_node, atot11706, atot11707]
  decide +kernel

theorem arows11711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11711 = true := by
  rw [show D2M8K2.u11711 = KTree.node D2M8K2.u11709 (nat_lit 25112500) (nat_lit 3933403219) (nat_lit 0) D2M8K2.u11710 from rfl, allE_node, arows11709, irow11711, arows11710]
  all_goals rfl

theorem atot11711 : totK PD2M8K2 D2M8K2.u11711 = [0, 487744970960, 1644973645350, 1249245264286, 138315881795, 1310285577, 0, 0] := by
  rw [show D2M8K2.u11711 = KTree.node D2M8K2.u11709 (nat_lit 25112500) (nat_lit 3933403219) (nat_lit 0) D2M8K2.u11710 from rfl, totK_node, atot11709, atot11710]
  decide +kernel

theorem arows11715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11715 = true := by
  rw [show D2M8K2.u11715 = KTree.node D2M8K2.u11713 (nat_lit 25116249) (nat_lit 1441239266) (nat_lit 0) D2M8K2.u11714 from rfl, allE_node, arows11713, irow11715, arows11714]
  all_goals rfl

theorem atot11715 : totK PD2M8K2 D2M8K2.u11715 = [0, 723489908800, 1834119626546, 1012069283444, 87949919569, 0, 0, 0] := by
  rw [show D2M8K2.u11715 = KTree.node D2M8K2.u11713 (nat_lit 25116249) (nat_lit 1441239266) (nat_lit 0) D2M8K2.u11714 from rfl, totK_node, atot11713, atot11714]
  decide +kernel

theorem arows11718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11718 = true := by
  rw [show D2M8K2.u11718 = KTree.node D2M8K2.u11716 (nat_lit 25121388) (nat_lit 3359020248) (nat_lit 0) D2M8K2.u11717 from rfl, allE_node, arows11716, irow11718, arows11717]
  all_goals rfl

theorem atot11718 : totK PD2M8K2 D2M8K2.u11718 = [0, 440396075746, 1568998379150, 1338657945463, 211024154471, 4879840392, 0, 0] := by
  rw [show D2M8K2.u11718 = KTree.node D2M8K2.u11716 (nat_lit 25121388) (nat_lit 3359020248) (nat_lit 0) D2M8K2.u11717 from rfl, totK_node, atot11716, atot11717]
  decide +kernel

theorem arows11723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11723 = true := by
  rw [show D2M8K2.u11723 = KTree.node D2M8K2.u11721 (nat_lit 25131391) (nat_lit 2282836606) (nat_lit 0) D2M8K2.u11722 from rfl, allE_node, arows11721, irow11723, arows11722]
  all_goals rfl

theorem atot11723 : totK PD2M8K2 D2M8K2.u11723 = [0, 362025959042, 1347222383290, 1415748725073, 402306051253, 21751168066, 0, 0] := by
  rw [show D2M8K2.u11723 = KTree.node D2M8K2.u11721 (nat_lit 25131391) (nat_lit 2282836606) (nat_lit 0) D2M8K2.u11722 from rfl, totK_node, atot11721, atot11722]
  decide +kernel

theorem arows11726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11726 = true := by
  rw [show D2M8K2.u11726 = KTree.node D2M8K2.u11724 (nat_lit 25134969) (nat_lit 1855267513) (nat_lit 0) D2M8K2.u11725 from rfl, allE_node, arows11724, irow11726, arows11725]
  all_goals rfl

theorem atot11726 : totK PD2M8K2 D2M8K2.u11726 = [0, 485828148009, 1607747960030, 1321956985924, 180424936986, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11726 = KTree.node D2M8K2.u11724 (nat_lit 25134969) (nat_lit 1855267513) (nat_lit 0) D2M8K2.u11725 from rfl, totK_node, atot11724, atot11725]
  decide +kernel

theorem arows11730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11730 = true := by
  rw [show D2M8K2.u11730 = KTree.node D2M8K2.u11728 (nat_lit 25141888) (nat_lit 3736311988) (nat_lit 0) D2M8K2.u11729 from rfl, allE_node, arows11728, irow11730, arows11729]
  all_goals rfl

theorem atot11730 : totK PD2M8K2 D2M8K2.u11730 = [0, 383655611181, 1440597255034, 1392871220620, 310459218567, 13049727234, 0, 0] := by
  rw [show D2M8K2.u11730 = KTree.node D2M8K2.u11728 (nat_lit 25141888) (nat_lit 3736311988) (nat_lit 0) D2M8K2.u11729 from rfl, totK_node, atot11728, atot11729]
  decide +kernel

theorem arows11733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11733 = true := by
  rw [show D2M8K2.u11733 = KTree.node D2M8K2.u11731 (nat_lit 25146240) (nat_lit 2764356436) (nat_lit 0) D2M8K2.u11732 from rfl, allE_node, arows11731, irow11733, arows11732]
  all_goals rfl

theorem atot11733 : totK PD2M8K2 D2M8K2.u11733 = [0, 443609608340, 1573009260415, 1352967014796, 188295684515, 2294578496, 0, 0] := by
  rw [show D2M8K2.u11733 = KTree.node D2M8K2.u11731 (nat_lit 25146240) (nat_lit 2764356436) (nat_lit 0) D2M8K2.u11732 from rfl, totK_node, atot11731, atot11732]
  decide +kernel

theorem arows11739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11739 = true := by
  rw [show D2M8K2.u11739 = KTree.node D2M8K2.u11737 (nat_lit 25149899) (nat_lit 2902669009) (nat_lit 0) D2M8K2.u11738 from rfl, allE_node, arows11737, irow11739, arows11738]
  all_goals rfl

theorem atot11739 : totK PD2M8K2 D2M8K2.u11739 = [0, 382286559831, 1467628527727, 1464415392258, 265288740197, 5089503546, 0, 0] := by
  rw [show D2M8K2.u11739 = KTree.node D2M8K2.u11737 (nat_lit 25149899) (nat_lit 2902669009) (nat_lit 0) D2M8K2.u11738 from rfl, totK_node, atot11737, atot11738]
  decide +kernel

theorem arows11742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11742 = true := by
  rw [show D2M8K2.u11742 = KTree.node D2M8K2.u11740 (nat_lit 25153639) (nat_lit 2392624099) (nat_lit 0) D2M8K2.u11741 from rfl, allE_node, arows11740, irow11742, arows11741]
  all_goals rfl

theorem atot11742 : totK PD2M8K2 D2M8K2.u11742 = [0, 0, 634503754594, 1751356975137, 971197616854, 108621586746, 1275377855, 0] := by
  rw [show D2M8K2.u11742 = KTree.node D2M8K2.u11740 (nat_lit 25153639) (nat_lit 2392624099) (nat_lit 0) D2M8K2.u11741 from rfl, totK_node, atot11740, atot11741]
  decide +kernel

theorem arows11746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11746 = true := by
  rw [show D2M8K2.u11746 = KTree.node D2M8K2.u11744 (nat_lit 25160883) (nat_lit 3544937770) (nat_lit 0) D2M8K2.u11745 from rfl, allE_node, arows11744, irow11746, arows11745]
  all_goals rfl

theorem atot11746 : totK PD2M8K2 D2M8K2.u11746 = [0, 0, 721020829287, 1865039132999, 849416906481, 48808067272, 0, 0] := by
  rw [show D2M8K2.u11746 = KTree.node D2M8K2.u11744 (nat_lit 25160883) (nat_lit 3544937770) (nat_lit 0) D2M8K2.u11745 from rfl, totK_node, atot11744, atot11745]
  decide +kernel

theorem arows11749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11749 = true := by
  rw [show D2M8K2.u11749 = KTree.node D2M8K2.u11747 (nat_lit 25167897) (nat_lit 1837088617) (nat_lit 0) D2M8K2.u11748 from rfl, allE_node, arows11747, irow11749, arows11748]
  all_goals rfl

theorem atot11749 : totK PD2M8K2 D2M8K2.u11749 = [0, 38616506213, 847481019274, 1909269172185, 713123342742, 30085228570, 0, 0] := by
  rw [show D2M8K2.u11749 = KTree.node D2M8K2.u11747 (nat_lit 25167897) (nat_lit 1837088617) (nat_lit 0) D2M8K2.u11748 from rfl, totK_node, atot11747, atot11748]
  decide +kernel

theorem arows11754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11754 = true := by
  rw [show D2M8K2.u11754 = KTree.node D2M8K2.u11752 (nat_lit 25178464) (nat_lit 3741127726) (nat_lit 0) D2M8K2.u11753 from rfl, allE_node, arows11752, irow11754, arows11753]
  all_goals rfl

theorem atot11754 : totK PD2M8K2 D2M8K2.u11754 = [0, 403552690395, 1421865988043, 1382082406364, 421849544959, 29328793087, 0, 0] := by
  rw [show D2M8K2.u11754 = KTree.node D2M8K2.u11752 (nat_lit 25178464) (nat_lit 3741127726) (nat_lit 0) D2M8K2.u11753 from rfl, totK_node, atot11752, atot11753]
  decide +kernel

theorem arows11757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11757 = true := by
  rw [show D2M8K2.u11757 = KTree.node D2M8K2.u11755 (nat_lit 25181189) (nat_lit 2384514699) (nat_lit 0) D2M8K2.u11756 from rfl, allE_node, arows11755, irow11757, arows11756]
  all_goals rfl

theorem atot11757 : totK PD2M8K2 D2M8K2.u11757 = [0, 424104852695, 1442536544170, 1391991524258, 349334478433, 14169541985, 0, 0] := by
  rw [show D2M8K2.u11757 = KTree.node D2M8K2.u11755 (nat_lit 25181189) (nat_lit 2384514699) (nat_lit 0) D2M8K2.u11756 from rfl, totK_node, atot11755, atot11756]
  decide +kernel

theorem arows11761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11761 = true := by
  rw [show D2M8K2.u11761 = KTree.node D2M8K2.u11759 (nat_lit 25185129) (nat_lit 1918754987) (nat_lit 0) D2M8K2.u11760 from rfl, allE_node, arows11759, irow11761, arows11760]
  all_goals rfl

theorem atot11761 : totK PD2M8K2 D2M8K2.u11761 = [0, 358576824489, 1381115998752, 1521808479004, 361541517445, 11313309155, 0, 0] := by
  rw [show D2M8K2.u11761 = KTree.node D2M8K2.u11759 (nat_lit 25185129) (nat_lit 1918754987) (nat_lit 0) D2M8K2.u11760 from rfl, totK_node, atot11759, atot11760]
  decide +kernel

theorem arows11764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11764 = true := by
  rw [show D2M8K2.u11764 = KTree.node D2M8K2.u11762 (nat_lit 25188597) (nat_lit 1741952189) (nat_lit 0) D2M8K2.u11763 from rfl, allE_node, arows11762, irow11764, arows11763]
  all_goals rfl

theorem atot11764 : totK PD2M8K2 D2M8K2.u11764 = [0, 476407738113, 1624239453975, 1333344818609, 200935464143, 3880716147, 0, 0] := by
  rw [show D2M8K2.u11764 = KTree.node D2M8K2.u11762 (nat_lit 25188597) (nat_lit 1741952189) (nat_lit 0) D2M8K2.u11763 from rfl, totK_node, atot11762, atot11763]
  decide +kernel

theorem arows11774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11774 = true := by
  rw [show D2M8K2.u11774 = KTree.node D2M8K2.u11772 (nat_lit 25192676) (nat_lit 1720757601) (nat_lit 0) D2M8K2.u11773 from rfl, allE_node, arows11772, irow11774, arows11773]
  all_goals rfl

theorem atot11774 : totK PD2M8K2 D2M8K2.u11774 = [0, 386102733767, 1369116632420, 1437009423373, 403517485299, 17791270226, 0, 0] := by
  rw [show D2M8K2.u11774 = KTree.node D2M8K2.u11772 (nat_lit 25192676) (nat_lit 1720757601) (nat_lit 0) D2M8K2.u11773 from rfl, totK_node, atot11772, atot11773]
  decide +kernel

theorem arows11777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11777 = true := by
  rw [show D2M8K2.u11777 = KTree.node D2M8K2.u11775 (nat_lit 25216777) (nat_lit 1519732958) (nat_lit 0) D2M8K2.u11776 from rfl, allE_node, arows11775, irow11777, arows11776]
  all_goals rfl

theorem atot11777 : totK PD2M8K2 D2M8K2.u11777 = [0, 467902830660, 1594103311149, 1338159799301, 169780788235, 1334361349, 0, 0] := by
  rw [show D2M8K2.u11777 = KTree.node D2M8K2.u11775 (nat_lit 25216777) (nat_lit 1519732958) (nat_lit 0) D2M8K2.u11776 from rfl, totK_node, atot11775, atot11776]
  decide +kernel

theorem arows11781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11781 = true := by
  rw [show D2M8K2.u11781 = KTree.node D2M8K2.u11779 (nat_lit 25220638) (nat_lit 3742615457) (nat_lit 0) D2M8K2.u11780 from rfl, allE_node, arows11779, irow11781, arows11780]
  all_goals rfl

theorem atot11781 : totK PD2M8K2 D2M8K2.u11781 = [0, 363083516081, 1318439593026, 1440511643564, 461520791149, 24088924277, 0, 0] := by
  rw [show D2M8K2.u11781 = KTree.node D2M8K2.u11779 (nat_lit 25220638) (nat_lit 3742615457) (nat_lit 0) D2M8K2.u11780 from rfl, totK_node, atot11779, atot11780]
  decide +kernel

theorem arows11784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11784 = true := by
  rw [show D2M8K2.u11784 = KTree.node D2M8K2.u11782 (nat_lit 25223503) (nat_lit 1986930051) (nat_lit 0) D2M8K2.u11783 from rfl, allE_node, arows11782, irow11784, arows11783]
  all_goals rfl

theorem atot11784 : totK PD2M8K2 D2M8K2.u11784 = [0, 358792387986, 1437951172103, 1485920988138, 330235660048, 13049727234, 0, 0] := by
  rw [show D2M8K2.u11784 = KTree.node D2M8K2.u11782 (nat_lit 25223503) (nat_lit 1986930051) (nat_lit 0) D2M8K2.u11783 from rfl, totK_node, atot11782, atot11783]
  decide +kernel

theorem arows11789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11789 = true := by
  rw [show D2M8K2.u11789 = KTree.node D2M8K2.u11787 (nat_lit 25230014) (nat_lit 3843185347) (nat_lit 0) D2M8K2.u11788 from rfl, allE_node, arows11787, irow11789, arows11788]
  all_goals rfl

theorem atot11789 : totK PD2M8K2 D2M8K2.u11789 = [0, 458885705866, 1540297246046, 1361569403820, 224495416333, 4846308403, 0, 0] := by
  rw [show D2M8K2.u11789 = KTree.node D2M8K2.u11787 (nat_lit 25230014) (nat_lit 3843185347) (nat_lit 0) D2M8K2.u11788 from rfl, totK_node, atot11787, atot11788]
  decide +kernel

theorem arows11792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11792 = true := by
  rw [show D2M8K2.u11792 = KTree.node D2M8K2.u11790 (nat_lit 25233891) (nat_lit 3476449182) (nat_lit 0) D2M8K2.u11791 from rfl, allE_node, arows11790, irow11792, arows11791]
  all_goals rfl

theorem atot11792 : totK PD2M8K2 D2M8K2.u11792 = [0, 362987134942, 1397210262796, 1443136309812, 351880191011, 13729587881, 0, 0] := by
  rw [show D2M8K2.u11792 = KTree.node D2M8K2.u11790 (nat_lit 25233891) (nat_lit 3476449182) (nat_lit 0) D2M8K2.u11791 from rfl, totK_node, atot11790, atot11791]
  decide +kernel

theorem arows11796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11796 = true := by
  rw [show D2M8K2.u11796 = KTree.node D2M8K2.u11794 (nat_lit 25237346) (nat_lit 3599158196) (nat_lit 0) D2M8K2.u11795 from rfl, allE_node, arows11794, irow11796, arows11795]
  all_goals rfl

theorem atot11796 : totK PD2M8K2 D2M8K2.u11796 = [0, 0, 506884826604, 1665223853790, 1146158230645, 134706451425, 1206465782, 0] := by
  rw [show D2M8K2.u11796 = KTree.node D2M8K2.u11794 (nat_lit 25237346) (nat_lit 3599158196) (nat_lit 0) D2M8K2.u11795 from rfl, totK_node, atot11794, atot11795]
  decide +kernel

theorem arows11799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11799 = true := by
  rw [show D2M8K2.u11799 = KTree.node D2M8K2.u11797 (nat_lit 25242980) (nat_lit 3339273480) (nat_lit 0) D2M8K2.u11798 from rfl, allE_node, arows11797, irow11799, arows11798]
  all_goals rfl

theorem atot11799 : totK PD2M8K2 D2M8K2.u11799 = [0, 0, 735676688835, 1886723166109, 905413759725, 58709570099, 0, 0] := by
  rw [show D2M8K2.u11799 = KTree.node D2M8K2.u11797 (nat_lit 25242980) (nat_lit 3339273480) (nat_lit 0) D2M8K2.u11798 from rfl, totK_node, atot11797, atot11798]
  decide +kernel

theorem arows11805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11805 = true := by
  rw [show D2M8K2.u11805 = KTree.node D2M8K2.u11803 (nat_lit 25249762) (nat_lit 2184900203) (nat_lit 0) D2M8K2.u11804 from rfl, allE_node, arows11803, irow11805, arows11804]
  all_goals rfl

theorem atot11805 : totK PD2M8K2 D2M8K2.u11805 = [0, 0, 412565204097, 1452455530183, 1282950506059, 296793059480, 13016197374, 0] := by
  rw [show D2M8K2.u11805 = KTree.node D2M8K2.u11803 (nat_lit 25249762) (nat_lit 2184900203) (nat_lit 0) D2M8K2.u11804 from rfl, totK_node, atot11803, atot11804]
  decide +kernel

theorem arows11808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11808 = true := by
  rw [show D2M8K2.u11808 = KTree.node D2M8K2.u11806 (nat_lit 25253465) (nat_lit 1407617254) (nat_lit 0) D2M8K2.u11807 from rfl, allE_node, arows11806, irow11808, arows11807]
  all_goals rfl

theorem atot11808 : totK PD2M8K2 D2M8K2.u11808 = [0, 175422674038, 756127194280, 1394451995994, 991859877430, 164939871720, 4574395652, 0] := by
  rw [show D2M8K2.u11808 = KTree.node D2M8K2.u11806 (nat_lit 25253465) (nat_lit 1407617254) (nat_lit 0) D2M8K2.u11807 from rfl, totK_node, atot11806, atot11807]
  decide +kernel

theorem arows11812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11812 = true := by
  rw [show D2M8K2.u11812 = KTree.node D2M8K2.u11810 (nat_lit 25300257) (nat_lit 1775119257) (nat_lit 0) D2M8K2.u11811 from rfl, allE_node, arows11810, irow11812, arows11811]
  all_goals rfl

theorem atot11812 : totK PD2M8K2 D2M8K2.u11812 = [0, 440447616346, 1574740453457, 1376361809231, 181504214128, 1310166938, 0, 0] := by
  rw [show D2M8K2.u11812 = KTree.node D2M8K2.u11810 (nat_lit 25300257) (nat_lit 1775119257) (nat_lit 0) D2M8K2.u11811 from rfl, totK_node, atot11810, atot11811]
  decide +kernel

theorem arows11815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11815 = true := by
  rw [show D2M8K2.u11815 = KTree.node D2M8K2.u11813 (nat_lit 25303853) (nat_lit 2033983759) (nat_lit 0) D2M8K2.u11814 from rfl, allE_node, arows11813, irow11815, arows11814]
  all_goals rfl

theorem atot11815 : totK PD2M8K2 D2M8K2.u11815 = [0, 380037926091, 1430566702198, 1440842132826, 385110089131, 15013989272, 0, 0] := by
  rw [show D2M8K2.u11815 = KTree.node D2M8K2.u11813 (nat_lit 25303853) (nat_lit 2033983759) (nat_lit 0) D2M8K2.u11814 from rfl, totK_node, atot11813, atot11814]
  decide +kernel

theorem arows11820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11820 = true := by
  rw [show D2M8K2.u11820 = KTree.node D2M8K2.u11818 (nat_lit 25306964) (nat_lit 3652335736) (nat_lit 0) D2M8K2.u11819 from rfl, allE_node, arows11818, irow11820, arows11819]
  all_goals rfl

theorem atot11820 : totK PD2M8K2 D2M8K2.u11820 = [0, 418271016783, 1455118106204, 1388952148507, 315201162491, 13049727234, 0, 0] := by
  rw [show D2M8K2.u11820 = KTree.node D2M8K2.u11818 (nat_lit 25306964) (nat_lit 3652335736) (nat_lit 0) D2M8K2.u11819 from rfl, totK_node, atot11818, atot11819]
  decide +kernel

theorem arows11823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11823 = true := by
  rw [show D2M8K2.u11823 = KTree.node D2M8K2.u11821 (nat_lit 25311202) (nat_lit 3120769441) (nat_lit 0) D2M8K2.u11822 from rfl, allE_node, arows11821, irow11823, arows11822]
  all_goals rfl

theorem atot11823 : totK PD2M8K2 D2M8K2.u11823 = [0, 504026546975, 1582110283327, 1314397121751, 212831818342, 4686148432, 0, 0] := by
  rw [show D2M8K2.u11823 = KTree.node D2M8K2.u11821 (nat_lit 25311202) (nat_lit 3120769441) (nat_lit 0) D2M8K2.u11822 from rfl, totK_node, atot11821, atot11822]
  decide +kernel

theorem arows11827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11827 = true := by
  rw [show D2M8K2.u11827 = KTree.node D2M8K2.u11825 (nat_lit 25314663) (nat_lit 2890000784) (nat_lit 0) D2M8K2.u11826 from rfl, allE_node, arows11825, irow11827, arows11826]
  all_goals rfl

theorem atot11827 : totK PD2M8K2 D2M8K2.u11827 = [0, 111279211669, 1124003819151, 1807196651314, 492005469640, 16895976387, 0, 0] := by
  rw [show D2M8K2.u11827 = KTree.node D2M8K2.u11825 (nat_lit 25314663) (nat_lit 2890000784) (nat_lit 0) D2M8K2.u11826 from rfl, totK_node, atot11825, atot11826]
  decide +kernel

theorem arows11830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11830 = true := by
  rw [show D2M8K2.u11830 = KTree.node D2M8K2.u11828 (nat_lit 25322618) (nat_lit 4064628083) (nat_lit 0) D2M8K2.u11829 from rfl, allE_node, arows11828, irow11830, arows11829]
  all_goals rfl

theorem atot11830 : totK PD2M8K2 D2M8K2.u11830 = [0, 0, 629564492469, 1754004999591, 1015866175735, 90310914083, 1103454931, 0] := by
  rw [show D2M8K2.u11830 = KTree.node D2M8K2.u11828 (nat_lit 25322618) (nat_lit 4064628083) (nat_lit 0) D2M8K2.u11829 from rfl, totK_node, atot11828, atot11829]
  decide +kernel

theorem arows11837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11837 = true := by
  rw [show D2M8K2.u11837 = KTree.node D2M8K2.u11835 (nat_lit 25329338) (nat_lit 4284098850) (nat_lit 0) D2M8K2.u11836 from rfl, allE_node, arows11835, irow11837, arows11836]
  all_goals rfl

theorem atot11837 : totK PD2M8K2 D2M8K2.u11837 = [0, 0, 836549825836, 1899943690719, 758973491618, 41582908021, 0, 0] := by
  rw [show D2M8K2.u11837 = KTree.node D2M8K2.u11835 (nat_lit 25329338) (nat_lit 4284098850) (nat_lit 0) D2M8K2.u11836 from rfl, totK_node, atot11835, atot11836]
  decide +kernel

theorem arows11840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11840 = true := by
  rw [show D2M8K2.u11840 = KTree.node D2M8K2.u11838 (nat_lit 25334906) (nat_lit 3457707916) (nat_lit 0) D2M8K2.u11839 from rfl, allE_node, arows11838, irow11840, arows11839]
  all_goals rfl

theorem atot11840 : totK PD2M8K2 D2M8K2.u11840 = [0, 270182989682, 838889515633, 1243833986043, 927792995806, 162709336989, 4779662215, 0] := by
  rw [show D2M8K2.u11840 = KTree.node D2M8K2.u11838 (nat_lit 25334906) (nat_lit 3457707916) (nat_lit 0) D2M8K2.u11839 from rfl, totK_node, atot11838, atot11839]
  decide +kernel

theorem arows11844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11844 = true := by
  rw [show D2M8K2.u11844 = KTree.node D2M8K2.u11842 (nat_lit 25342613) (nat_lit 2375234260) (nat_lit 0) D2M8K2.u11843 from rfl, allE_node, arows11842, irow11844, arows11843]
  all_goals rfl

theorem atot11844 : totK PD2M8K2 D2M8K2.u11844 = [0, 477903050450, 1616602087501, 1347887882936, 179448257772, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11844 = KTree.node D2M8K2.u11842 (nat_lit 25342613) (nat_lit 2375234260) (nat_lit 0) D2M8K2.u11843 from rfl, totK_node, atot11842, atot11843]
  decide +kernel

theorem arows11847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11847 = true := by
  rw [show D2M8K2.u11847 = KTree.node D2M8K2.u11845 (nat_lit 25345900) (nat_lit 3723648416) (nat_lit 0) D2M8K2.u11846 from rfl, allE_node, arows11845, irow11847, arows11846]
  all_goals rfl

theorem atot11847 : totK PD2M8K2 D2M8K2.u11847 = [0, 318710345236, 1232815304590, 1489196564838, 548837046059, 32762398897, 0, 0] := by
  rw [show D2M8K2.u11847 = KTree.node D2M8K2.u11845 (nat_lit 25345900) (nat_lit 3723648416) (nat_lit 0) D2M8K2.u11846 from rfl, totK_node, atot11845, atot11846]
  decide +kernel

theorem arows11852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11852 = true := by
  rw [show D2M8K2.u11852 = KTree.node D2M8K2.u11850 (nat_lit 25348804) (nat_lit 4016555572) (nat_lit 0) D2M8K2.u11851 from rfl, allE_node, arows11850, irow11852, arows11851]
  all_goals rfl

theorem atot11852 : totK PD2M8K2 D2M8K2.u11852 = [0, 421892762368, 1508250968702, 1403873417483, 274991903051, 9583672031, 0, 0] := by
  rw [show D2M8K2.u11852 = KTree.node D2M8K2.u11850 (nat_lit 25348804) (nat_lit 4016555572) (nat_lit 0) D2M8K2.u11851 from rfl, totK_node, atot11850, atot11851]
  decide +kernel

theorem arows11855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11855 = true := by
  rw [show D2M8K2.u11855 = KTree.node D2M8K2.u11853 (nat_lit 25359148) (nat_lit 3854928651) (nat_lit 0) D2M8K2.u11854 from rfl, allE_node, arows11853, irow11855, arows11854]
  all_goals rfl

theorem atot11855 : totK PD2M8K2 D2M8K2.u11855 = [191552386262, 633182618209, 1069075195039, 1255394231867, 415872945841, 21982452388, 0, 0] := by
  rw [show D2M8K2.u11855 = KTree.node D2M8K2.u11853 (nat_lit 25359148) (nat_lit 3854928651) (nat_lit 0) D2M8K2.u11854 from rfl, totK_node, atot11853, atot11854]
  decide +kernel

theorem arows11859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11859 = true := by
  rw [show D2M8K2.u11859 = KTree.node D2M8K2.u11857 (nat_lit 25383273) (nat_lit 1894535000) (nat_lit 0) D2M8K2.u11858 from rfl, allE_node, arows11857, irow11859, arows11858]
  all_goals rfl

theorem atot11859 : totK PD2M8K2 D2M8K2.u11859 = [490607963111, 1614979026192, 1316358385949, 178837897139, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11859 = KTree.node D2M8K2.u11857 (nat_lit 25383273) (nat_lit 1894535000) (nat_lit 0) D2M8K2.u11858 from rfl, totK_node, atot11857, atot11858]
  decide +kernel

theorem arows11862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11862 = true := by
  rw [show D2M8K2.u11862 = KTree.node D2M8K2.u11860 (nat_lit 25390997) (nat_lit 2386715761) (nat_lit 0) D2M8K2.u11861 from rfl, allE_node, arows11860, irow11862, arows11861]
  all_goals rfl

theorem atot11862 : totK PD2M8K2 D2M8K2.u11862 = [417702394133, 1465029043358, 1364268168770, 307464953776, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11862 = KTree.node D2M8K2.u11860 (nat_lit 25390997) (nat_lit 2386715761) (nat_lit 0) D2M8K2.u11861 from rfl, totK_node, atot11860, atot11861]
  decide +kernel

theorem arows11868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11868 = true := by
  rw [show D2M8K2.u11868 = KTree.node D2M8K2.u11866 (nat_lit 25394336) (nat_lit 3650956687) (nat_lit 0) D2M8K2.u11867 from rfl, allE_node, arows11866, irow11868, arows11867]
  all_goals rfl

theorem atot11868 : totK PD2M8K2 D2M8K2.u11868 = [395099076164, 1405266097450, 1415624714436, 342778884112, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u11868 = KTree.node D2M8K2.u11866 (nat_lit 25394336) (nat_lit 3650956687) (nat_lit 0) D2M8K2.u11867 from rfl, totK_node, atot11866, atot11867]
  decide +kernel

theorem arows11871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11871 = true := by
  rw [show D2M8K2.u11871 = KTree.node D2M8K2.u11869 (nat_lit 25397720) (nat_lit 3614762614) (nat_lit 0) D2M8K2.u11870 from rfl, allE_node, arows11869, irow11871, arows11870]
  all_goals rfl

theorem atot11871 : totK PD2M8K2 D2M8K2.u11871 = [453942169455, 1519771243180, 1364453193541, 247419841386, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u11871 = KTree.node D2M8K2.u11869 (nat_lit 25397720) (nat_lit 3614762614) (nat_lit 0) D2M8K2.u11870 from rfl, totK_node, atot11869, atot11870]
  decide +kernel

theorem arows11875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11875 = true := by
  rw [show D2M8K2.u11875 = KTree.node D2M8K2.u11873 (nat_lit 25401449) (nat_lit 1614263446) (nat_lit 0) D2M8K2.u11874 from rfl, allE_node, arows11873, irow11875, arows11874]
  all_goals rfl

theorem atot11875 : totK PD2M8K2 D2M8K2.u11875 = [19692840307, 864857633985, 1854698246933, 742736428865, 41132877050, 0, 0, 0] := by
  rw [show D2M8K2.u11875 = KTree.node D2M8K2.u11873 (nat_lit 25401449) (nat_lit 1614263446) (nat_lit 0) D2M8K2.u11874 from rfl, totK_node, atot11873, atot11874]
  decide +kernel

theorem arows11878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11878 = true := by
  rw [show D2M8K2.u11878 = KTree.node D2M8K2.u11876 (nat_lit 25404910) (nat_lit 3806643149) (nat_lit 0) D2M8K2.u11877 from rfl, allE_node, arows11876, irow11878, arows11877]
  all_goals rfl

theorem atot11878 : totK PD2M8K2 D2M8K2.u11878 = [0, 496302198181, 1625341033808, 1210152280498, 167822487480, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11878 = KTree.node D2M8K2.u11876 (nat_lit 25404910) (nat_lit 3806643149) (nat_lit 0) D2M8K2.u11877 from rfl, totK_node, atot11876, atot11877]
  decide +kernel

theorem arows11883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11883 = true := by
  rw [show D2M8K2.u11883 = KTree.node D2M8K2.u11881 (nat_lit 25413684) (nat_lit 3099536721) (nat_lit 0) D2M8K2.u11882 from rfl, allE_node, arows11881, irow11883, arows11882]
  all_goals rfl

theorem atot11883 : totK PD2M8K2 D2M8K2.u11883 = [0, 746116806856, 1887156915440, 887595397340, 46278971598, 0, 0, 0] := by
  rw [show D2M8K2.u11883 = KTree.node D2M8K2.u11881 (nat_lit 25413684) (nat_lit 3099536721) (nat_lit 0) D2M8K2.u11882 from rfl, totK_node, atot11881, atot11882]
  decide +kernel

theorem arows11886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11886 = true := by
  rw [show D2M8K2.u11886 = KTree.node D2M8K2.u11884 (nat_lit 25420440) (nat_lit 3594215546) (nat_lit 0) D2M8K2.u11885 from rfl, allE_node, arows11884, irow11886, arows11885]
  all_goals rfl

theorem atot11886 : totK PD2M8K2 D2M8K2.u11886 = [336184739765, 1163728886661, 1497506197445, 598575781910, 32241630928, 0, 0, 0] := by
  rw [show D2M8K2.u11886 = KTree.node D2M8K2.u11884 (nat_lit 25420440) (nat_lit 3594215546) (nat_lit 0) D2M8K2.u11885 from rfl, totK_node, atot11884, atot11885]
  decide +kernel

theorem arows11890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11890 = true := by
  rw [show D2M8K2.u11890 = KTree.node D2M8K2.u11888 (nat_lit 25428510) (nat_lit 3951079944) (nat_lit 0) D2M8K2.u11889 from rfl, allE_node, arows11888, irow11890, arows11889]
  all_goals rfl

theorem atot11890 : totK PD2M8K2 D2M8K2.u11890 = [284259710052, 1189789911136, 1548162742118, 595501310345, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u11890 = KTree.node D2M8K2.u11888 (nat_lit 25428510) (nat_lit 3951079944) (nat_lit 0) D2M8K2.u11889 from rfl, totK_node, atot11888, atot11889]
  decide +kernel

theorem arows11893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11893 = true := by
  rw [show D2M8K2.u11893 = KTree.node D2M8K2.u11891 (nat_lit 25432276) (nat_lit 3474346236) (nat_lit 0) D2M8K2.u11892 from rfl, allE_node, arows11891, irow11893, arows11892]
  all_goals rfl

theorem atot11893 : totK PD2M8K2 D2M8K2.u11893 = [477479830688, 1543787679734, 1334476365000, 278839828853, 11833525664, 0, 0, 0] := by
  rw [show D2M8K2.u11893 = KTree.node D2M8K2.u11891 (nat_lit 25432276) (nat_lit 3474346236) (nat_lit 0) D2M8K2.u11892 from rfl, totK_node, atot11891, atot11892]
  decide +kernel

theorem arows11901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11901 = true := by
  rw [show D2M8K2.u11901 = KTree.node D2M8K2.u11899 (nat_lit 25435646) (nat_lit 3700650532) (nat_lit 0) D2M8K2.u11900 from rfl, allE_node, arows11899, irow11901, arows11900]
  all_goals rfl

theorem atot11901 : totK PD2M8K2 D2M8K2.u11901 = [372530704050, 1412000257648, 1455298441729, 345892151679, 13237669976, 0, 0, 0] := by
  rw [show D2M8K2.u11901 = KTree.node D2M8K2.u11899 (nat_lit 25435646) (nat_lit 3700650532) (nat_lit 0) D2M8K2.u11900 from rfl, totK_node, atot11899, atot11900]
  decide +kernel

theorem arows11904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11904 = true := by
  rw [show D2M8K2.u11904 = KTree.node D2M8K2.u11902 (nat_lit 25439067) (nat_lit 3755858908) (nat_lit 0) D2M8K2.u11903 from rfl, allE_node, arows11902, irow11904, arows11903]
  all_goals rfl

theorem atot11904 : totK PD2M8K2 D2M8K2.u11904 = [439559757251, 1554003198740, 1401275374161, 248108103534, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u11904 = KTree.node D2M8K2.u11902 (nat_lit 25439067) (nat_lit 3755858908) (nat_lit 0) D2M8K2.u11903 from rfl, totK_node, atot11902, atot11903]
  decide +kernel

theorem arows11908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11908 = true := by
  rw [show D2M8K2.u11908 = KTree.node D2M8K2.u11906 (nat_lit 25442819) (nat_lit 2904539451) (nat_lit 0) D2M8K2.u11907 from rfl, allE_node, arows11906, irow11908, arows11907]
  all_goals rfl

theorem atot11908 : totK PD2M8K2 D2M8K2.u11908 = [90526578066, 936213749095, 1768820317244, 773779381232, 55788527767, 0, 0, 0] := by
  rw [show D2M8K2.u11908 = KTree.node D2M8K2.u11906 (nat_lit 25442819) (nat_lit 2904539451) (nat_lit 0) D2M8K2.u11907 from rfl, totK_node, atot11906, atot11907]
  decide +kernel

theorem arows11911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11911 = true := by
  rw [show D2M8K2.u11911 = KTree.node D2M8K2.u11909 (nat_lit 25449195) (nat_lit 3675647139) (nat_lit 0) D2M8K2.u11910 from rfl, allE_node, arows11909, irow11911, arows11910]
  all_goals rfl

theorem atot11911 : totK PD2M8K2 D2M8K2.u11911 = [0, 316429847036, 1202159214104, 1506961726801, 563804291344, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11911 = KTree.node D2M8K2.u11909 (nat_lit 25449195) (nat_lit 3675647139) (nat_lit 0) D2M8K2.u11910 from rfl, totK_node, atot11909, atot11910]
  decide +kernel

theorem arows11916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11916 = true := by
  rw [show D2M8K2.u11916 = KTree.node D2M8K2.u11914 (nat_lit 25452957) (nat_lit 1233322221) (nat_lit 0) D2M8K2.u11915 from rfl, allE_node, arows11914, irow11916, arows11915]
  all_goals rfl

theorem atot11916 : totK PD2M8K2 D2M8K2.u11916 = [0, 478967752738, 1565294172784, 1340183373297, 246338640386, 5159868635, 0, 0] := by
  rw [show D2M8K2.u11916 = KTree.node D2M8K2.u11914 (nat_lit 25452957) (nat_lit 1233322221) (nat_lit 0) D2M8K2.u11915 from rfl, totK_node, atot11914, atot11915]
  decide +kernel

theorem arows11919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11919 = true := by
  rw [show D2M8K2.u11919 = KTree.node D2M8K2.u11917 (nat_lit 25456543) (nat_lit 2376490998) (nat_lit 0) D2M8K2.u11918 from rfl, allE_node, arows11917, irow11919, arows11918]
  all_goals rfl

theorem atot11919 : totK PD2M8K2 D2M8K2.u11919 = [0, 426686208973, 1535101570490, 1371579192888, 251404140946, 5218872685, 0, 0] := by
  rw [show D2M8K2.u11919 = KTree.node D2M8K2.u11917 (nat_lit 25456543) (nat_lit 2376490998) (nat_lit 0) D2M8K2.u11918 from rfl, totK_node, atot11917, atot11918]
  decide +kernel

theorem arows11923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11923 = true := by
  rw [show D2M8K2.u11923 = KTree.node D2M8K2.u11921 (nat_lit 25460358) (nat_lit 3736644362) (nat_lit 0) D2M8K2.u11922 from rfl, allE_node, arows11921, irow11923, arows11922]
  all_goals rfl

theorem atot11923 : totK PD2M8K2 D2M8K2.u11923 = [0, 477120111192, 1625060712917, 1359024053594, 184439028639, 1415142070, 0, 0] := by
  rw [show D2M8K2.u11923 = KTree.node D2M8K2.u11921 (nat_lit 25460358) (nat_lit 3736644362) (nat_lit 0) D2M8K2.u11922 from rfl, totK_node, atot11921, atot11922]
  decide +kernel

theorem arows11926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11926 = true := by
  rw [show D2M8K2.u11926 = KTree.node D2M8K2.u11924 (nat_lit 25505404) (nat_lit 3722728104) (nat_lit 0) D2M8K2.u11925 from rfl, allE_node, arows11924, irow11926, arows11925]
  all_goals rfl

theorem atot11926 : totK PD2M8K2 D2M8K2.u11926 = [413264604107, 1035601927282, 929871483877, 885367733650, 277447180775, 9302370699, 0, 0] := by
  rw [show D2M8K2.u11926 = KTree.node D2M8K2.u11924 (nat_lit 25505404) (nat_lit 3722728104) (nat_lit 0) D2M8K2.u11925 from rfl, totK_node, atot11924, atot11925]
  decide +kernel

theorem arows11932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11932 = true := by
  rw [show D2M8K2.u11932 = KTree.node D2M8K2.u11930 (nat_lit 25509295) (nat_lit 2213124872) (nat_lit 0) D2M8K2.u11931 from rfl, allE_node, arows11930, irow11932, arows11931]
  all_goals rfl

theorem atot11932 : totK PD2M8K2 D2M8K2.u11932 = [423698525221, 1567530786334, 1425182524372, 213876613613, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11932 = KTree.node D2M8K2.u11930 (nat_lit 25509295) (nat_lit 2213124872) (nat_lit 0) D2M8K2.u11931 from rfl, totK_node, atot11930, atot11931]
  decide +kernel

theorem arows11935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11935 = true := by
  rw [show D2M8K2.u11935 = KTree.node D2M8K2.u11933 (nat_lit 25512083) (nat_lit 2764024456) (nat_lit 0) D2M8K2.u11934 from rfl, allE_node, arows11933, irow11935, arows11934]
  all_goals rfl

theorem atot11935 : totK PD2M8K2 D2M8K2.u11935 = [357754573816, 1244828813547, 1437557485864, 562135127024, 37391899322, 0, 0, 0] := by
  rw [show D2M8K2.u11935 = KTree.node D2M8K2.u11933 (nat_lit 25512083) (nat_lit 2764024456) (nat_lit 0) D2M8K2.u11934 from rfl, totK_node, atot11933, atot11934]
  decide +kernel

theorem arows11939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11939 = true := by
  rw [show D2M8K2.u11939 = KTree.node D2M8K2.u11937 (nat_lit 25518630) (nat_lit 3836535373) (nat_lit 0) D2M8K2.u11938 from rfl, allE_node, arows11937, irow11939, arows11938]
  all_goals rfl

theorem atot11939 : totK PD2M8K2 D2M8K2.u11939 = [383558527275, 1393418353640, 1465692450786, 351323218102, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u11939 = KTree.node D2M8K2.u11937 (nat_lit 25518630) (nat_lit 3836535373) (nat_lit 0) D2M8K2.u11938 from rfl, totK_node, atot11937, atot11938]
  decide +kernel

theorem arows11942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11942 = true := by
  rw [show D2M8K2.u11942 = KTree.node D2M8K2.u11940 (nat_lit 25522015) (nat_lit 2310890434) (nat_lit 0) D2M8K2.u11941 from rfl, allE_node, arows11940, irow11942, arows11941]
  all_goals rfl

theorem atot11942 : totK PD2M8K2 D2M8K2.u11942 = [437508174910, 1550906778924, 1378840479177, 239448858717, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u11942 = KTree.node D2M8K2.u11940 (nat_lit 25522015) (nat_lit 2310890434) (nat_lit 0) D2M8K2.u11941 from rfl, totK_node, atot11940, atot11941]
  decide +kernel

theorem arows11947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11947 = true := by
  rw [show D2M8K2.u11947 = KTree.node D2M8K2.u11945 (nat_lit 25525376) (nat_lit 3010551045) (nat_lit 0) D2M8K2.u11946 from rfl, allE_node, arows11945, irow11947, arows11946]
  all_goals rfl

theorem atot11947 : totK PD2M8K2 D2M8K2.u11947 = [91570829045, 973578375259, 1796367093110, 655330272194, 30359209512, 0, 0, 0] := by
  rw [show D2M8K2.u11947 = KTree.node D2M8K2.u11945 (nat_lit 25525376) (nat_lit 3010551045) (nat_lit 0) D2M8K2.u11946 from rfl, totK_node, atot11945, atot11946]
  decide +kernel

theorem arows11950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11950 = true := by
  rw [show D2M8K2.u11950 = KTree.node D2M8K2.u11948 (nat_lit 25529235) (nat_lit 1962793814) (nat_lit 0) D2M8K2.u11949 from rfl, allE_node, arows11948, irow11950, arows11949]
  all_goals rfl

theorem atot11950 : totK PD2M8K2 D2M8K2.u11950 = [0, 476697680089, 1641875412759, 1289837347275, 149537877493, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11950 = KTree.node D2M8K2.u11948 (nat_lit 25529235) (nat_lit 1962793814) (nat_lit 0) D2M8K2.u11949 from rfl, totK_node, atot11948, atot11949]
  decide +kernel

theorem arows11954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11954 = true := by
  rw [show D2M8K2.u11954 = KTree.node D2M8K2.u11952 (nat_lit 25537562) (nat_lit 4210252945) (nat_lit 0) D2M8K2.u11953 from rfl, allE_node, arows11952, irow11954, arows11953]
  all_goals rfl

theorem atot11954 : totK PD2M8K2 D2M8K2.u11954 = [0, 516340344277, 1606539291871, 1244923018406, 221789708436, 7203532459, 0, 0] := by
  rw [show D2M8K2.u11954 = KTree.node D2M8K2.u11952 (nat_lit 25537562) (nat_lit 4210252945) (nat_lit 0) D2M8K2.u11953 from rfl, totK_node, atot11952, atot11953]
  decide +kernel

theorem arows11957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11957 = true := by
  rw [show D2M8K2.u11957 = KTree.node D2M8K2.u11955 (nat_lit 25540704) (nat_lit 3690063848) (nat_lit 0) D2M8K2.u11956 from rfl, allE_node, arows11955, irow11957, arows11956]
  all_goals rfl

theorem atot11957 : totK PD2M8K2 D2M8K2.u11957 = [0, 418229759367, 1557315549593, 1327429573421, 214786047465, 5976723406, 0, 0] := by
  rw [show D2M8K2.u11957 = KTree.node D2M8K2.u11955 (nat_lit 25540704) (nat_lit 3690063848) (nat_lit 0) D2M8K2.u11956 from rfl, totK_node, atot11955, atot11956]
  decide +kernel

theorem arows11964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11964 = true := by
  rw [show D2M8K2.u11964 = KTree.node D2M8K2.u11962 (nat_lit 25544326) (nat_lit 2494477528) (nat_lit 0) D2M8K2.u11963 from rfl, allE_node, arows11962, irow11964, arows11963]
  all_goals rfl

theorem atot11964 : totK PD2M8K2 D2M8K2.u11964 = [254098032854, 1022522892786, 1386110137066, 774718326209, 118869498961, 3667207281, 0, 0] := by
  rw [show D2M8K2.u11964 = KTree.node D2M8K2.u11962 (nat_lit 25544326) (nat_lit 2494477528) (nat_lit 0) D2M8K2.u11963 from rfl, totK_node, atot11962, atot11963]
  decide +kernel

theorem arows11967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11967 = true := by
  rw [show D2M8K2.u11967 = KTree.node D2M8K2.u11965 (nat_lit 25549692) (nat_lit 3155813852) (nat_lit 0) D2M8K2.u11966 from rfl, allE_node, arows11965, irow11967, arows11966]
  all_goals rfl

theorem atot11967 : totK PD2M8K2 D2M8K2.u11967 = [472490766726, 1575725512117, 1359275680986, 196900659547, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11967 = KTree.node D2M8K2.u11965 (nat_lit 25549692) (nat_lit 3155813852) (nat_lit 0) D2M8K2.u11966 from rfl, totK_node, atot11965, atot11966]
  decide +kernel

theorem arows11971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11971 = true := by
  rw [show D2M8K2.u11971 = KTree.node D2M8K2.u11969 (nat_lit 25553018) (nat_lit 4046771069) (nat_lit 0) D2M8K2.u11970 from rfl, allE_node, arows11969, irow11971, arows11970]
  all_goals rfl

theorem atot11971 : totK PD2M8K2 D2M8K2.u11971 = [297452824638, 1218327649781, 1502551586882, 583937268937, 37417015092, 0, 0, 0] := by
  rw [show D2M8K2.u11971 = KTree.node D2M8K2.u11969 (nat_lit 25553018) (nat_lit 4046771069) (nat_lit 0) D2M8K2.u11970 from rfl, totK_node, atot11969, atot11970]
  decide +kernel

theorem arows11974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11974 = true := by
  rw [show D2M8K2.u11974 = KTree.node D2M8K2.u11972 (nat_lit 25556557) (nat_lit 1275342414) (nat_lit 0) D2M8K2.u11973 from rfl, allE_node, arows11972, irow11974, arows11973]
  all_goals rfl

theorem atot11974 : totK PD2M8K2 D2M8K2.u11974 = [449595574301, 1479088770707, 1352940581356, 310184666899, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11974 = KTree.node D2M8K2.u11972 (nat_lit 25556557) (nat_lit 1275342414) (nat_lit 0) D2M8K2.u11973 from rfl, totK_node, atot11972, atot11973]
  decide +kernel

theorem arows11979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11979 = true := by
  rw [show D2M8K2.u11979 = KTree.node D2M8K2.u11977 (nat_lit 25560032) (nat_lit 3817447700) (nat_lit 0) D2M8K2.u11978 from rfl, allE_node, arows11977, irow11979, arows11978]
  all_goals rfl

theorem atot11979 : totK PD2M8K2 D2M8K2.u11979 = [371707918267, 1421159450031, 1445126194146, 345663216323, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u11979 = KTree.node D2M8K2.u11977 (nat_lit 25560032) (nat_lit 3817447700) (nat_lit 0) D2M8K2.u11978 from rfl, totK_node, atot11977, atot11978]
  decide +kernel

theorem arows11982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11982 = true := by
  rw [show D2M8K2.u11982 = KTree.node D2M8K2.u11980 (nat_lit 25563212) (nat_lit 3716784374) (nat_lit 0) D2M8K2.u11981 from rfl, allE_node, arows11980, irow11982, arows11981]
  all_goals rfl

theorem atot11982 : totK PD2M8K2 D2M8K2.u11982 = [181015165609, 1162952956536, 1714180330691, 511046002773, 23242077755, 0, 0, 0] := by
  rw [show D2M8K2.u11982 = KTree.node D2M8K2.u11980 (nat_lit 25563212) (nat_lit 3716784374) (nat_lit 0) D2M8K2.u11981 from rfl, totK_node, atot11980, atot11981]
  decide +kernel

theorem arows11986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11986 = true := by
  rw [show D2M8K2.u11986 = KTree.node D2M8K2.u11984 (nat_lit 25571258) (nat_lit 4294967296) (nat_lit 0) D2M8K2.u11985 from rfl, allE_node, arows11984, irow11986, arows11985]
  all_goals rfl

theorem atot11986 : totK PD2M8K2 D2M8K2.u11986 = [0, 530810485704, 1716292413475, 1184016835195, 132164045305, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11986 = KTree.node D2M8K2.u11984 (nat_lit 25571258) (nat_lit 4294967296) (nat_lit 0) D2M8K2.u11985 from rfl, totK_node, atot11984, atot11985]
  decide +kernel

theorem arows11989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11989 = true := by
  rw [show D2M8K2.u11989 = KTree.node D2M8K2.u11987 (nat_lit 25575728) (nat_lit 3798449546) (nat_lit 0) D2M8K2.u11988 from rfl, allE_node, arows11987, irow11989, arows11988]
  all_goals rfl

theorem atot11989 : totK PD2M8K2 D2M8K2.u11989 = [0, 729660861471, 1896929797158, 935478776427, 53756472262, 0, 0, 0] := by
  rw [show D2M8K2.u11989 = KTree.node D2M8K2.u11987 (nat_lit 25575728) (nat_lit 3798449546) (nat_lit 0) D2M8K2.u11988 from rfl, totK_node, atot11987, atot11988]
  decide +kernel

theorem arows11995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11995 = true := by
  rw [show D2M8K2.u11995 = KTree.node D2M8K2.u11993 (nat_lit 25582285) (nat_lit 1118879760) (nat_lit 0) D2M8K2.u11994 from rfl, allE_node, arows11993, irow11995, arows11994]
  all_goals rfl

theorem atot11995 : totK PD2M8K2 D2M8K2.u11995 = [0, 505082908040, 1678818972465, 1215352543868, 147510452770, 1095107716, 0, 0] := by
  rw [show D2M8K2.u11995 = KTree.node D2M8K2.u11993 (nat_lit 25582285) (nat_lit 1118879760) (nat_lit 0) D2M8K2.u11994 from rfl, totK_node, atot11993, atot11994]
  decide +kernel

theorem arows11998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11998 = true := by
  rw [show D2M8K2.u11998 = KTree.node D2M8K2.u11996 (nat_lit 25589634) (nat_lit 2885158747) (nat_lit 0) D2M8K2.u11997 from rfl, allE_node, arows11996, irow11998, arows11997]
  all_goals rfl

theorem atot11998 : totK PD2M8K2 D2M8K2.u11998 = [434114777975, 1460151819884, 1254692059910, 330168025517, 82415268481, 3882006667, 0, 0] := by
  rw [show D2M8K2.u11998 = KTree.node D2M8K2.u11996 (nat_lit 25589634) (nat_lit 2885158747) (nat_lit 0) D2M8K2.u11997 from rfl, totK_node, atot11996, atot11997]
  decide +kernel

theorem arows12002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12002 = true := by
  rw [show D2M8K2.u12002 = KTree.node D2M8K2.u12000 (nat_lit 25593298) (nat_lit 4069434322) (nat_lit 0) D2M8K2.u12001 from rfl, allE_node, arows12000, irow12002, arows12001]
  all_goals rfl

theorem atot12002 : totK PD2M8K2 D2M8K2.u12002 = [370533709805, 1349601394719, 1437453792039, 483857896412, 30749515097, 0, 0, 0] := by
  rw [show D2M8K2.u12002 = KTree.node D2M8K2.u12000 (nat_lit 25593298) (nat_lit 4069434322) (nat_lit 0) D2M8K2.u12001 from rfl, totK_node, atot12000, atot12001]
  decide +kernel

theorem arows12005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12005 = true := by
  rw [show D2M8K2.u12005 = KTree.node D2M8K2.u12003 (nat_lit 25599827) (nat_lit 2292575977) (nat_lit 0) D2M8K2.u12004 from rfl, allE_node, arows12003, irow12005, arows12004]
  all_goals rfl

theorem atot12005 : totK PD2M8K2 D2M8K2.u12005 = [425646553716, 1437580333530, 1377613610272, 355970231638, 16469661051, 0, 0, 0] := by
  rw [show D2M8K2.u12005 = KTree.node D2M8K2.u12003 (nat_lit 25599827) (nat_lit 2292575977) (nat_lit 0) D2M8K2.u12004 from rfl, totK_node, atot12003, atot12004]
  decide +kernel

theorem arows12010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12010 = true := by
  rw [show D2M8K2.u12010 = KTree.node D2M8K2.u12008 (nat_lit 25606396) (nat_lit 3248944430) (nat_lit 0) D2M8K2.u12009 from rfl, allE_node, arows12008, irow12010, arows12009]
  all_goals rfl

theorem atot12010 : totK PD2M8K2 D2M8K2.u12010 = [428021878965, 1477159288334, 1405465647642, 307872479346, 6925980121, 0, 0, 0] := by
  rw [show D2M8K2.u12010 = KTree.node D2M8K2.u12008 (nat_lit 25606396) (nat_lit 3248944430) (nat_lit 0) D2M8K2.u12009 from rfl, totK_node, atot12008, atot12009]
  decide +kernel

theorem arows12013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12013 = true := by
  rw [show D2M8K2.u12013 = KTree.node D2M8K2.u12011 (nat_lit 25609925) (nat_lit 1664189448) (nat_lit 0) D2M8K2.u12012 from rfl, allE_node, arows12011, irow12013, arows12012]
  all_goals rfl

theorem atot12013 : totK PD2M8K2 D2M8K2.u12013 = [0, 575813062320, 1711406533173, 1123639923092, 121443438938, 1310285577, 0, 0] := by
  rw [show D2M8K2.u12013 = KTree.node D2M8K2.u12011 (nat_lit 25609925) (nat_lit 1664189448) (nat_lit 0) D2M8K2.u12012 from rfl, totK_node, atot12011, atot12012]
  decide +kernel

theorem arows12017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12017 = true := by
  rw [show D2M8K2.u12017 = KTree.node D2M8K2.u12015 (nat_lit 25613647) (nat_lit 2411734162) (nat_lit 0) D2M8K2.u12016 from rfl, allE_node, arows12015, irow12017, arows12016]
  all_goals rfl

theorem atot12017 : totK PD2M8K2 D2M8K2.u12017 = [0, 670629536562, 1796363582695, 1089103159559, 96373173076, 0, 0, 0] := by
  rw [show D2M8K2.u12017 = KTree.node D2M8K2.u12015 (nat_lit 25613647) (nat_lit 2411734162) (nat_lit 0) D2M8K2.u12016 from rfl, totK_node, atot12015, atot12016]
  decide +kernel

theorem arows12020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12020 = true := by
  rw [show D2M8K2.u12020 = KTree.node D2M8K2.u12018 (nat_lit 25622080) (nat_lit 961581278) (nat_lit 0) D2M8K2.u12019 from rfl, allE_node, arows12018, irow12020, arows12019]
  all_goals rfl

theorem atot12020 : totK PD2M8K2 D2M8K2.u12020 = [0, 437510051220, 1556220348614, 1342547824829, 219127162511, 4931404646, 0, 0] := by
  rw [show D2M8K2.u12020 = KTree.node D2M8K2.u12018 (nat_lit 25622080) (nat_lit 961581278) (nat_lit 0) D2M8K2.u12019 from rfl, totK_node, atot12018, atot12019]
  decide +kernel

theorem arows12029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12029 = true := by
  rw [show D2M8K2.u12029 = KTree.node D2M8K2.u12027 (nat_lit 25628844) (nat_lit 3360107791) (nat_lit 0) D2M8K2.u12028 from rfl, allE_node, arows12027, irow12029, arows12028]
  all_goals rfl

theorem atot12029 : totK PD2M8K2 D2M8K2.u12029 = [0, 378163055385, 1369825869484, 1391832520940, 394515695889, 21751168066, 0, 0] := by
  rw [show D2M8K2.u12029 = KTree.node D2M8K2.u12027 (nat_lit 25628844) (nat_lit 3360107791) (nat_lit 0) D2M8K2.u12028 from rfl, totK_node, atot12027, atot12028]
  decide +kernel

theorem arows12032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12032 = true := by
  rw [show D2M8K2.u12032 = KTree.node D2M8K2.u12030 (nat_lit 25632304) (nat_lit 2690351873) (nat_lit 0) D2M8K2.u12031 from rfl, allE_node, arows12030, irow12032, arows12031]
  all_goals rfl

theorem atot12032 : totK PD2M8K2 D2M8K2.u12032 = [0, 455941830491, 1614330600287, 1326794556487, 175079004777, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12032 = KTree.node D2M8K2.u12030 (nat_lit 25632304) (nat_lit 2690351873) (nat_lit 0) D2M8K2.u12031 from rfl, totK_node, atot12030, atot12031]
  decide +kernel

theorem arows12036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12036 = true := by
  rw [show D2M8K2.u12036 = KTree.node D2M8K2.u12034 (nat_lit 25640330) (nat_lit 3259997295) (nat_lit 0) D2M8K2.u12035 from rfl, allE_node, arows12034, irow12036, arows12035]
  all_goals rfl

theorem atot12036 : totK PD2M8K2 D2M8K2.u12036 = [0, 491094076299, 1635727461463, 1295238247447, 158039547844, 1164319620, 0, 0] := by
  rw [show D2M8K2.u12036 = KTree.node D2M8K2.u12034 (nat_lit 25640330) (nat_lit 3259997295) (nat_lit 0) D2M8K2.u12035 from rfl, totK_node, atot12034, atot12035]
  decide +kernel

theorem arows12039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12039 = true := by
  rw [show D2M8K2.u12039 = KTree.node D2M8K2.u12037 (nat_lit 25643644) (nat_lit 3403371377) (nat_lit 0) D2M8K2.u12038 from rfl, allE_node, arows12037, irow12039, arows12038]
  all_goals rfl

theorem atot12039 : totK PD2M8K2 D2M8K2.u12039 = [0, 410861013225, 1436573473008, 1371465417115, 322857277857, 13189998508, 0, 0] := by
  rw [show D2M8K2.u12039 = KTree.node D2M8K2.u12037 (nat_lit 25643644) (nat_lit 3403371377) (nat_lit 0) D2M8K2.u12038 from rfl, totK_node, atot12037, atot12038]
  decide +kernel

theorem arows12044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12044 = true := by
  rw [show D2M8K2.u12044 = KTree.node D2M8K2.u12042 (nat_lit 25647291) (nat_lit 3776555214) (nat_lit 0) D2M8K2.u12043 from rfl, allE_node, arows12042, irow12044, arows12043]
  all_goals rfl

theorem atot12044 : totK PD2M8K2 D2M8K2.u12044 = [0, 382749107306, 1470489319549, 1467765756048, 253608332595, 4917684815, 0, 0] := by
  rw [show D2M8K2.u12044 = KTree.node D2M8K2.u12042 (nat_lit 25647291) (nat_lit 3776555214) (nat_lit 0) D2M8K2.u12043 from rfl, totK_node, atot12042, atot12043]
  decide +kernel

theorem arows12047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12047 = true := by
  rw [show D2M8K2.u12047 = KTree.node D2M8K2.u12045 (nat_lit 25651070) (nat_lit 3332942675) (nat_lit 0) D2M8K2.u12046 from rfl, allE_node, arows12045, irow12047, arows12046]
  all_goals rfl

theorem atot12047 : totK PD2M8K2 D2M8K2.u12047 = [0, 0, 720925272589, 1843526947731, 850602544363, 70547409395, 1310517177, 0] := by
  rw [show D2M8K2.u12047 = KTree.node D2M8K2.u12045 (nat_lit 25651070) (nat_lit 3332942675) (nat_lit 0) D2M8K2.u12046 from rfl, totK_node, atot12045, atot12046]
  decide +kernel

theorem arows12051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12051 = true := by
  rw [show D2M8K2.u12051 = KTree.node D2M8K2.u12049 (nat_lit 25658575) (nat_lit 2277284769) (nat_lit 0) D2M8K2.u12050 from rfl, allE_node, arows12049, irow12051, arows12050]
  all_goals rfl

theorem atot12051 : totK PD2M8K2 D2M8K2.u12051 = [0, 0, 656394206006, 1792029683978, 954459523757, 76601769094, 0, 0] := by
  rw [show D2M8K2.u12051 = KTree.node D2M8K2.u12049 (nat_lit 25658575) (nat_lit 2277284769) (nat_lit 0) D2M8K2.u12050 from rfl, totK_node, atot12049, atot12050]
  decide +kernel

theorem arows12054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12054 = true := by
  rw [show D2M8K2.u12054 = KTree.node D2M8K2.u12052 (nat_lit 25665216) (nat_lit 3512258599) (nat_lit 0) D2M8K2.u12053 from rfl, allE_node, arows12052, irow12054, arows12053]
  all_goals rfl

theorem atot12054 : totK PD2M8K2 D2M8K2.u12054 = [0, 0, 783754931042, 1920021370073, 768283671064, 33821646105, 0, 0] := by
  rw [show D2M8K2.u12054 = KTree.node D2M8K2.u12052 (nat_lit 25665216) (nat_lit 3512258599) (nat_lit 0) D2M8K2.u12053 from rfl, totK_node, atot12052, atot12053]
  decide +kernel

theorem arows12060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12060 = true := by
  rw [show D2M8K2.u12060 = KTree.node D2M8K2.u12058 (nat_lit 25675753) (nat_lit 1335421566) (nat_lit 0) D2M8K2.u12059 from rfl, allE_node, arows12058, irow12060, arows12059]
  all_goals rfl

theorem atot12060 : totK PD2M8K2 D2M8K2.u12060 = [0, 442320717312, 1409599416067, 1331581192578, 434454702985, 34171233335, 0, 0] := by
  rw [show D2M8K2.u12060 = KTree.node D2M8K2.u12058 (nat_lit 25675753) (nat_lit 1335421566) (nat_lit 0) D2M8K2.u12059 from rfl, totK_node, atot12058, atot12059]
  decide +kernel

theorem arows12063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12063 = true := by
  rw [show D2M8K2.u12063 = KTree.node D2M8K2.u12061 (nat_lit 25678706) (nat_lit 4082330911) (nat_lit 0) D2M8K2.u12062 from rfl, allE_node, arows12061, irow12063, arows12062]
  all_goals rfl

theorem atot12063 : totK PD2M8K2 D2M8K2.u12063 = [0, 330677264928, 1318651407518, 1532754883459, 455885454831, 16335166703, 0, 0] := by
  rw [show D2M8K2.u12063 = KTree.node D2M8K2.u12061 (nat_lit 25678706) (nat_lit 4082330911) (nat_lit 0) D2M8K2.u12062 from rfl, totK_node, atot12061, atot12062]
  decide +kernel

theorem arows12067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12067 = true := by
  rw [show D2M8K2.u12067 = KTree.node D2M8K2.u12065 (nat_lit 25682729) (nat_lit 1741772625) (nat_lit 0) D2M8K2.u12066 from rfl, allE_node, arows12065, irow12067, arows12066]
  all_goals rfl

theorem atot12067 : totK PD2M8K2 D2M8K2.u12067 = [0, 424505023947, 1455688866924, 1399868463952, 319493004277, 10869765338, 0, 0] := by
  rw [show D2M8K2.u12067 = KTree.node D2M8K2.u12065 (nat_lit 25682729) (nat_lit 1741772625) (nat_lit 0) D2M8K2.u12066 from rfl, totK_node, atot12065, atot12066]
  decide +kernel

theorem arows12070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12070 = true := by
  rw [show D2M8K2.u12070 = KTree.node D2M8K2.u12068 (nat_lit 25685842) (nat_lit 3387511739) (nat_lit 0) D2M8K2.u12069 from rfl, allE_node, arows12068, irow12070, arows12069]
  all_goals rfl

theorem atot12070 : totK PD2M8K2 D2M8K2.u12070 = [0, 413589449005, 1575347656264, 1422076218367, 213497429521, 3540641832, 0, 0] := by
  rw [show D2M8K2.u12070 = KTree.node D2M8K2.u12068 (nat_lit 25685842) (nat_lit 3387511739) (nat_lit 0) D2M8K2.u12069 from rfl, totK_node, atot12068, atot12069]
  decide +kernel

theorem arows12075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12075 = true := by
  rw [show D2M8K2.u12075 = KTree.node D2M8K2.u12073 (nat_lit 25689572) (nat_lit 3172609800) (nat_lit 0) D2M8K2.u12074 from rfl, allE_node, arows12073, irow12075, arows12074]
  all_goals rfl

theorem atot12075 : totK PD2M8K2 D2M8K2.u12075 = [0, 386929657333, 1382371310817, 1463581959349, 374043793250, 10115954314, 0, 0] := by
  rw [show D2M8K2.u12075 = KTree.node D2M8K2.u12073 (nat_lit 25689572) (nat_lit 3172609800) (nat_lit 0) D2M8K2.u12074 from rfl, totK_node, atot12073, atot12074]
  decide +kernel

theorem arows12078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12078 = true := by
  rw [show D2M8K2.u12078 = KTree.node D2M8K2.u12076 (nat_lit 25755420) (nat_lit 3082743799) (nat_lit 0) D2M8K2.u12077 from rfl, allE_node, arows12076, irow12078, arows12077]
  all_goals rfl

theorem atot12078 : totK PD2M8K2 D2M8K2.u12078 = [0, 411753738684, 1490102782238, 1348133580221, 264691131033, 12960406905, 0, 0] := by
  rw [show D2M8K2.u12078 = KTree.node D2M8K2.u12076 (nat_lit 25755420) (nat_lit 3082743799) (nat_lit 0) D2M8K2.u12077 from rfl, totK_node, atot12076, atot12077]
  decide +kernel

theorem arows12082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12082 = true := by
  rw [show D2M8K2.u12082 = KTree.node D2M8K2.u12080 (nat_lit 25759043) (nat_lit 2900986281) (nat_lit 0) D2M8K2.u12081 from rfl, allE_node, arows12080, irow12082, arows12081]
  all_goals rfl

theorem atot12082 : totK PD2M8K2 D2M8K2.u12082 = [0, 423101282447, 1424526544430, 1371362225070, 393832158496, 23593757536, 0, 0] := by
  rw [show D2M8K2.u12082 = KTree.node D2M8K2.u12080 (nat_lit 25759043) (nat_lit 2900986281) (nat_lit 0) D2M8K2.u12081 from rfl, totK_node, atot12080, atot12081]
  decide +kernel

theorem arows12085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12085 = true := by
  rw [show D2M8K2.u12085 = KTree.node D2M8K2.u12083 (nat_lit 25765508) (nat_lit 2862694654) (nat_lit 0) D2M8K2.u12084 from rfl, allE_node, arows12083, irow12085, arows12084]
  all_goals rfl

theorem atot12085 : totK PD2M8K2 D2M8K2.u12085 = [0, 445489343800, 1479736724050, 1379334313070, 321206292087, 7755488830, 0, 0] := by
  rw [show D2M8K2.u12085 = KTree.node D2M8K2.u12083 (nat_lit 25765508) (nat_lit 2862694654) (nat_lit 0) D2M8K2.u12084 from rfl, totK_node, atot12083, atot12084]
  decide +kernel

theorem arows12092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12092 = true := by
  rw [show D2M8K2.u12092 = KTree.node D2M8K2.u12090 (nat_lit 25768511) (nat_lit 2040911917) (nat_lit 0) D2M8K2.u12091 from rfl, allE_node, arows12090, irow12092, arows12091]
  all_goals rfl

theorem atot12092 : totK PD2M8K2 D2M8K2.u12092 = [0, 418701216955, 1454325837749, 1374753886165, 309861671329, 13149116973, 0, 0] := by
  rw [show D2M8K2.u12092 = KTree.node D2M8K2.u12090 (nat_lit 25768511) (nat_lit 2040911917) (nat_lit 0) D2M8K2.u12091 from rfl, totK_node, atot12090, atot12091]
  decide +kernel

theorem arows12095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12095 = true := by
  rw [show D2M8K2.u12095 = KTree.node D2M8K2.u12093 (nat_lit 25772095) (nat_lit 1807499070) (nat_lit 0) D2M8K2.u12094 from rfl, allE_node, arows12093, irow12095, arows12094]
  all_goals rfl

theorem atot12095 : totK PD2M8K2 D2M8K2.u12095 = [0, 403329178610, 1487864410615, 1424676094250, 257355532776, 5152749158, 0, 0] := by
  rw [show D2M8K2.u12095 = KTree.node D2M8K2.u12093 (nat_lit 25772095) (nat_lit 1807499070) (nat_lit 0) D2M8K2.u12094 from rfl, totK_node, atot12093, atot12094]
  decide +kernel

theorem arows12099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12099 = true := by
  rw [show D2M8K2.u12099 = KTree.node D2M8K2.u12097 (nat_lit 25775795) (nat_lit 2841131890) (nat_lit 0) D2M8K2.u12098 from rfl, allE_node, arows12097, irow12099, arows12098]
  all_goals rfl

theorem atot12099 : totK PD2M8K2 D2M8K2.u12099 = [0, 0, 587566334641, 1741060333851, 1012733830981, 108056589062, 1217496766, 0] := by
  rw [show D2M8K2.u12099 = KTree.node D2M8K2.u12097 (nat_lit 25775795) (nat_lit 2841131890) (nat_lit 0) D2M8K2.u12098 from rfl, totK_node, atot12097, atot12098]
  decide +kernel

theorem arows12102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12102 = true := by
  rw [show D2M8K2.u12102 = KTree.node D2M8K2.u12100 (nat_lit 25779601) (nat_lit 1430533244) (nat_lit 0) D2M8K2.u12101 from rfl, allE_node, arows12100, irow12102, arows12101]
  all_goals rfl

theorem atot12102 : totK PD2M8K2 D2M8K2.u12102 = [0, 0, 684884574049, 1827049276873, 1006979935852, 81984763880, 0, 0] := by
  rw [show D2M8K2.u12102 = KTree.node D2M8K2.u12100 (nat_lit 25779601) (nat_lit 1430533244) (nat_lit 0) D2M8K2.u12101 from rfl, totK_node, atot12100, atot12101]
  decide +kernel

theorem arows12107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12107 = true := by
  rw [show D2M8K2.u12107 = KTree.node D2M8K2.u12105 (nat_lit 25788035) (nat_lit 2334103690) (nat_lit 0) D2M8K2.u12106 from rfl, allE_node, arows12105, irow12107, arows12106]
  all_goals rfl

theorem atot12107 : totK PD2M8K2 D2M8K2.u12107 = [0, 0, 407479743639, 1469497330927, 1300159658664, 298294585322, 13105450397, 0] := by
  rw [show D2M8K2.u12107 = KTree.node D2M8K2.u12105 (nat_lit 25788035) (nat_lit 2334103690) (nat_lit 0) D2M8K2.u12106 from rfl, totK_node, atot12105, atot12106]
  decide +kernel

theorem arows12110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12110 = true := by
  rw [show D2M8K2.u12110 = KTree.node D2M8K2.u12108 (nat_lit 25791561) (nat_lit 1858190061) (nat_lit 0) D2M8K2.u12109 from rfl, allE_node, arows12108, irow12110, arows12109]
  all_goals rfl

theorem atot12110 : totK PD2M8K2 D2M8K2.u12110 = [0, 0, 508159913850, 1598946915548, 1181463884359, 180401287918, 4630915822, 0] := by
  rw [show D2M8K2.u12110 = KTree.node D2M8K2.u12108 (nat_lit 25791561) (nat_lit 1858190061) (nat_lit 0) D2M8K2.u12109 from rfl, totK_node, atot12108, atot12109]
  decide +kernel

theorem arows12114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12114 = true := by
  rw [show D2M8K2.u12114 = KTree.node D2M8K2.u12112 (nat_lit 25796818) (nat_lit 3051341190) (nat_lit 0) D2M8K2.u12113 from rfl, allE_node, arows12112, irow12114, arows12113]
  all_goals rfl

theorem atot12114 : totK PD2M8K2 D2M8K2.u12114 = [0, 406329781361, 1496878716163, 1374467376535, 265655424088, 10353568507, 0, 0] := by
  rw [show D2M8K2.u12114 = KTree.node D2M8K2.u12112 (nat_lit 25796818) (nat_lit 3051341190) (nat_lit 0) D2M8K2.u12113 from rfl, totK_node, atot12112, atot12113]
  decide +kernel

theorem arows12117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12117 = true := by
  rw [show D2M8K2.u12117 = KTree.node D2M8K2.u12115 (nat_lit 25800521) (nat_lit 1745515775) (nat_lit 0) D2M8K2.u12116 from rfl, allE_node, arows12115, irow12117, arows12116]
  all_goals rfl

theorem atot12117 : totK PD2M8K2 D2M8K2.u12117 = [0, 418304900105, 1428836592515, 1418746617838, 381949775548, 15066332673, 0, 0] := by
  rw [show D2M8K2.u12117 = KTree.node D2M8K2.u12115 (nat_lit 25800521) (nat_lit 1745515775) (nat_lit 0) D2M8K2.u12116 from rfl, totK_node, atot12115, atot12116]
  decide +kernel

theorem arows12123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12123 = true := by
  rw [show D2M8K2.u12123 = KTree.node D2M8K2.u12121 (nat_lit 25803893) (nat_lit 2221120622) (nat_lit 0) D2M8K2.u12122 from rfl, allE_node, arows12121, irow12123, arows12122]
  all_goals rfl

theorem atot12123 : totK PD2M8K2 D2M8K2.u12123 = [0, 497799738020, 1588239947355, 1297476087331, 208483261016, 4532804645, 0, 0] := by
  rw [show D2M8K2.u12123 = KTree.node D2M8K2.u12121 (nat_lit 25803893) (nat_lit 2221120622) (nat_lit 0) D2M8K2.u12122 from rfl, totK_node, atot12121, atot12122]
  decide +kernel

theorem arows12126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12126 = true := by
  rw [show D2M8K2.u12126 = KTree.node D2M8K2.u12124 (nat_lit 25807836) (nat_lit 3169885337) (nat_lit 0) D2M8K2.u12125 from rfl, allE_node, arows12124, irow12126, arows12125]
  all_goals rfl

theorem atot12126 : totK PD2M8K2 D2M8K2.u12126 = [0, 363438907355, 1408350221943, 1456585194715, 343290424195, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12126 = KTree.node D2M8K2.u12124 (nat_lit 25807836) (nat_lit 3169885337) (nat_lit 0) D2M8K2.u12125 from rfl, totK_node, atot12124, atot12125]
  decide +kernel

theorem arows12130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12130 = true := by
  rw [show D2M8K2.u12130 = KTree.node D2M8K2.u12128 (nat_lit 25811185) (nat_lit 1506397216) (nat_lit 0) D2M8K2.u12129 from rfl, allE_node, arows12128, irow12130, arows12129]
  all_goals rfl

theorem atot12130 : totK PD2M8K2 D2M8K2.u12130 = [0, 345349101557, 1419846703525, 1538607920621, 314493237754, 6350335412, 0, 0] := by
  rw [show D2M8K2.u12130 = KTree.node D2M8K2.u12128 (nat_lit 25811185) (nat_lit 1506397216) (nat_lit 0) D2M8K2.u12129 from rfl, totK_node, atot12128, atot12129]
  decide +kernel

theorem arows12133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12133 = true := by
  rw [show D2M8K2.u12133 = KTree.node D2M8K2.u12131 (nat_lit 25818266) (nat_lit 1690801675) (nat_lit 0) D2M8K2.u12132 from rfl, allE_node, arows12131, irow12133, arows12132]
  all_goals rfl

theorem atot12133 : totK PD2M8K2 D2M8K2.u12133 = [0, 0, 571164129285, 1726391339729, 1065784460113, 100923651860, 1138244013, 0] := by
  rw [show D2M8K2.u12133 = KTree.node D2M8K2.u12131 (nat_lit 25818266) (nat_lit 1690801675) (nat_lit 0) D2M8K2.u12132 from rfl, totK_node, atot12131, atot12132]
  decide +kernel

theorem arows12138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12138 = true := by
  rw [show D2M8K2.u12138 = KTree.node D2M8K2.u12136 (nat_lit 25824555) (nat_lit 2587003000) (nat_lit 0) D2M8K2.u12137 from rfl, allE_node, arows12136, irow12138, arows12137]
  all_goals rfl

theorem atot12138 : totK PD2M8K2 D2M8K2.u12138 = [0, 0, 849927374505, 1917700577468, 739862259860, 33608327808, 0, 0] := by
  rw [show D2M8K2.u12138 = KTree.node D2M8K2.u12136 (nat_lit 25824555) (nat_lit 2587003000) (nat_lit 0) D2M8K2.u12137 from rfl, totK_node, atot12136, atot12137]
  decide +kernel

theorem arows12141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12141 = true := by
  rw [show D2M8K2.u12141 = KTree.node D2M8K2.u12139 (nat_lit 25831174) (nat_lit 1740510407) (nat_lit 0) D2M8K2.u12140 from rfl, allE_node, arows12139, irow12141, arows12140]
  all_goals rfl

theorem atot12141 : totK PD2M8K2 D2M8K2.u12141 = [0, 0, 486841899443, 1655707950553, 1163057711295, 145917007665, 2162517376, 0] := by
  rw [show D2M8K2.u12141 = KTree.node D2M8K2.u12139 (nat_lit 25831174) (nat_lit 1740510407) (nat_lit 0) D2M8K2.u12140 from rfl, totK_node, atot12139, atot12140]
  decide +kernel

theorem arows12145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12145 = true := by
  rw [show D2M8K2.u12145 = KTree.node D2M8K2.u12143 (nat_lit 25838619) (nat_lit 3486761676) (nat_lit 0) D2M8K2.u12144 from rfl, allE_node, arows12143, irow12145, arows12144]
  all_goals rfl

theorem atot12145 : totK PD2M8K2 D2M8K2.u12145 = [0, 488252126929, 1571171400778, 1239493335318, 225645636552, 40177742413, 2751766863, 0] := by
  rw [show D2M8K2.u12145 = KTree.node D2M8K2.u12143 (nat_lit 25838619) (nat_lit 3486761676) (nat_lit 0) D2M8K2.u12144 from rfl, totK_node, atot12143, atot12144]
  decide +kernel

theorem arows12148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12148 = true := by
  rw [show D2M8K2.u12148 = KTree.node D2M8K2.u12146 (nat_lit 25842581) (nat_lit 2369403982) (nat_lit 0) D2M8K2.u12147 from rfl, allE_node, arows12146, irow12148, arows12147]
  all_goals rfl

theorem atot12148 : totK PD2M8K2 D2M8K2.u12148 = [0, 315358862361, 1285305171816, 1517568424007, 495778024550, 27185641738, 0, 0] := by
  rw [show D2M8K2.u12148 = KTree.node D2M8K2.u12146 (nat_lit 25842581) (nat_lit 2369403982) (nat_lit 0) D2M8K2.u12147 from rfl, totK_node, atot12146, atot12147]
  decide +kernel

theorem arows12156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12156 = true := by
  rw [show D2M8K2.u12156 = KTree.node D2M8K2.u12154 (nat_lit 25848877) (nat_lit 1382895491) (nat_lit 0) D2M8K2.u12155 from rfl, allE_node, arows12154, irow12156, arows12155]
  all_goals rfl

theorem atot12156 : totK PD2M8K2 D2M8K2.u12156 = [0, 424574532437, 1420872717573, 1367797446160, 353851488003, 16278028120, 0, 0] := by
  rw [show D2M8K2.u12156 = KTree.node D2M8K2.u12154 (nat_lit 25848877) (nat_lit 1382895491) (nat_lit 0) D2M8K2.u12155 from rfl, totK_node, atot12154, atot12155]
  decide +kernel

theorem arows12159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12159 = true := by
  rw [show D2M8K2.u12159 = KTree.node D2M8K2.u12157 (nat_lit 25855375) (nat_lit 2349614553) (nat_lit 0) D2M8K2.u12158 from rfl, allE_node, arows12157, irow12159, arows12158]
  all_goals rfl

theorem atot12159 : totK PD2M8K2 D2M8K2.u12159 = [0, 427676776155, 1519726067926, 1386448502651, 283707101780, 7425968930, 0, 0] := by
  rw [show D2M8K2.u12159 = KTree.node D2M8K2.u12157 (nat_lit 25855375) (nat_lit 2349614553) (nat_lit 0) D2M8K2.u12158 from rfl, totK_node, atot12157, atot12158]
  decide +kernel

theorem arows12163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12163 = true := by
  rw [show D2M8K2.u12163 = KTree.node D2M8K2.u12161 (nat_lit 25879570) (nat_lit 3508225910) (nat_lit 0) D2M8K2.u12162 from rfl, allE_node, arows12161, irow12163, arows12162]
  all_goals rfl

theorem atot12163 : totK PD2M8K2 D2M8K2.u12163 = [435294558901, 1361116556745, 1104087250818, 472722057760, 203646746985, 17080783126, 0, 0] := by
  rw [show D2M8K2.u12163 = KTree.node D2M8K2.u12161 (nat_lit 25879570) (nat_lit 3508225910) (nat_lit 0) D2M8K2.u12162 from rfl, totK_node, atot12161, atot12162]
  decide +kernel

theorem arows12166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12166 = true := by
  rw [show D2M8K2.u12166 = KTree.node D2M8K2.u12164 (nat_lit 25886632) (nat_lit 3782286622) (nat_lit 0) D2M8K2.u12165 from rfl, allE_node, arows12164, irow12166, arows12165]
  all_goals rfl

theorem atot12166 : totK PD2M8K2 D2M8K2.u12166 = [410614163193, 1489588615950, 1407225217316, 274063619892, 9587713104, 0, 0, 0] := by
  rw [show D2M8K2.u12166 = KTree.node D2M8K2.u12164 (nat_lit 25886632) (nat_lit 3782286622) (nat_lit 0) D2M8K2.u12165 from rfl, totK_node, atot12164, atot12165]
  decide +kernel

theorem arows12171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12171 = true := by
  rw [show D2M8K2.u12171 = KTree.node D2M8K2.u12169 (nat_lit 25890052) (nat_lit 3379446489) (nat_lit 0) D2M8K2.u12170 from rfl, allE_node, arows12169, irow12171, arows12170]
  all_goals rfl

theorem atot12171 : totK PD2M8K2 D2M8K2.u12171 = [410834643430, 1441409370695, 1395441571166, 319300033778, 10695362932, 0, 0, 0] := by
  rw [show D2M8K2.u12171 = KTree.node D2M8K2.u12169 (nat_lit 25890052) (nat_lit 3379446489) (nat_lit 0) D2M8K2.u12170 from rfl, totK_node, atot12169, atot12170]
  decide +kernel

theorem arows12174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12174 = true := by
  rw [show D2M8K2.u12174 = KTree.node D2M8K2.u12172 (nat_lit 25893136) (nat_lit 3688162118) (nat_lit 0) D2M8K2.u12173 from rfl, allE_node, arows12172, irow12174, arows12173]
  all_goals rfl

theorem atot12174 : totK PD2M8K2 D2M8K2.u12174 = [424122565885, 1518451104883, 1389644488865, 253937836116, 6132408356, 0, 0, 0] := by
  rw [show D2M8K2.u12174 = KTree.node D2M8K2.u12172 (nat_lit 25893136) (nat_lit 3688162118) (nat_lit 0) D2M8K2.u12173 from rfl, totK_node, atot12172, atot12173]
  decide +kernel

theorem arows12178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12178 = true := by
  rw [show D2M8K2.u12178 = KTree.node D2M8K2.u12176 (nat_lit 25896946) (nat_lit 4121195245) (nat_lit 0) D2M8K2.u12177 from rfl, allE_node, arows12176, irow12178, arows12177]
  all_goals rfl

theorem atot12178 : totK PD2M8K2 D2M8K2.u12178 = [323074992700, 1289845222851, 1502868250189, 415053194372, 13822666253, 0, 0, 0] := by
  rw [show D2M8K2.u12178 = KTree.node D2M8K2.u12176 (nat_lit 25896946) (nat_lit 4121195245) (nat_lit 0) D2M8K2.u12177 from rfl, totK_node, atot12176, atot12177]
  decide +kernel

theorem arows12181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12181 = true := by
  rw [show D2M8K2.u12181 = KTree.node D2M8K2.u12179 (nat_lit 25900661) (nat_lit 2190234039) (nat_lit 0) D2M8K2.u12180 from rfl, allE_node, arows12179, irow12181, arows12180]
  all_goals rfl

theorem atot12181 : totK PD2M8K2 D2M8K2.u12181 = [0, 470763706672, 1607869519946, 1236338850902, 176595656553, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12181 = KTree.node D2M8K2.u12179 (nat_lit 25900661) (nat_lit 2190234039) (nat_lit 0) D2M8K2.u12180 from rfl, totK_node, atot12179, atot12180]
  decide +kernel

theorem arows12187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12187 = true := by
  rw [show D2M8K2.u12187 = KTree.node D2M8K2.u12185 (nat_lit 25907793) (nat_lit 1024151386) (nat_lit 0) D2M8K2.u12186 from rfl, allE_node, arows12185, irow12187, arows12186]
  all_goals rfl

theorem atot12187 : totK PD2M8K2 D2M8K2.u12187 = [0, 736676808084, 1894027062173, 889078429198, 44351270735, 0, 0, 0] := by
  rw [show D2M8K2.u12187 = KTree.node D2M8K2.u12185 (nat_lit 25907793) (nat_lit 1024151386) (nat_lit 0) D2M8K2.u12186 from rfl, totK_node, atot12185, atot12186]
  decide +kernel

theorem arows12190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12190 = true := by
  rw [show D2M8K2.u12190 = KTree.node D2M8K2.u12188 (nat_lit 25914171) (nat_lit 2529409284) (nat_lit 0) D2M8K2.u12189 from rfl, allE_node, arows12188, irow12190, arows12189]
  all_goals rfl

theorem atot12190 : totK PD2M8K2 D2M8K2.u12190 = [0, 754306399475, 1899276660977, 862596555180, 41579268788, 0, 0, 0] := by
  rw [show D2M8K2.u12190 = KTree.node D2M8K2.u12188 (nat_lit 25914171) (nat_lit 2529409284) (nat_lit 0) D2M8K2.u12189 from rfl, totK_node, atot12188, atot12189]
  decide +kernel

theorem arows12194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12194 = true := by
  rw [show D2M8K2.u12194 = KTree.node D2M8K2.u12192 (nat_lit 25924665) (nat_lit 1855624242) (nat_lit 0) D2M8K2.u12193 from rfl, allE_node, arows12192, irow12194, arows12193]
  all_goals rfl

theorem atot12194 : totK PD2M8K2 D2M8K2.u12194 = [443872281396, 1414221019812, 1325939361445, 448211921745, 38841936429, 0, 0, 0] := by
  rw [show D2M8K2.u12194 = KTree.node D2M8K2.u12192 (nat_lit 25924665) (nat_lit 1855624242) (nat_lit 0) D2M8K2.u12193 from rfl, totK_node, atot12192, atot12193]
  decide +kernel

theorem arows12197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12197 = true := by
  rw [show D2M8K2.u12197 = KTree.node D2M8K2.u12195 (nat_lit 25927460) (nat_lit 3646755071) (nat_lit 0) D2M8K2.u12196 from rfl, allE_node, arows12195, irow12197, arows12196]
  all_goals rfl

theorem atot12197 : totK PD2M8K2 D2M8K2.u12197 = [413774819927, 1394442501256, 1407404897603, 398455612110, 13399449862, 0, 0, 0] := by
  rw [show D2M8K2.u12197 = KTree.node D2M8K2.u12195 (nat_lit 25927460) (nat_lit 3646755071) (nat_lit 0) D2M8K2.u12196 from rfl, totK_node, atot12195, atot12196]
  decide +kernel

theorem arows12202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12202 = true := by
  rw [show D2M8K2.u12202 = KTree.node D2M8K2.u12200 (nat_lit 25930879) (nat_lit 2420449048) (nat_lit 0) D2M8K2.u12201 from rfl, allE_node, arows12200, irow12202, arows12201]
  all_goals rfl

theorem atot12202 : totK PD2M8K2 D2M8K2.u12202 = [414015629082, 1447002688592, 1408408147799, 327194978329, 13070422398, 0, 0, 0] := by
  rw [show D2M8K2.u12202 = KTree.node D2M8K2.u12200 (nat_lit 25930879) (nat_lit 2420449048) (nat_lit 0) D2M8K2.u12201 from rfl, totK_node, atot12200, atot12201]
  decide +kernel

theorem arows12205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12205 = true := by
  rw [show D2M8K2.u12205 = KTree.node D2M8K2.u12203 (nat_lit 25934285) (nat_lit 2196136473) (nat_lit 0) D2M8K2.u12204 from rfl, allE_node, arows12203, irow12205, arows12204]
  all_goals rfl

theorem atot12205 : totK PD2M8K2 D2M8K2.u12205 = [425223410355, 1469217268783, 1380766428427, 313112800042, 13136429951, 0, 0, 0] := by
  rw [show D2M8K2.u12205 = KTree.node D2M8K2.u12203 (nat_lit 25934285) (nat_lit 2196136473) (nat_lit 0) D2M8K2.u12204 from rfl, totK_node, atot12203, atot12204]
  decide +kernel

theorem arows12209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12209 = true := by
  rw [show D2M8K2.u12209 = KTree.node D2M8K2.u12207 (nat_lit 25937961) (nat_lit 1839165647) (nat_lit 0) D2M8K2.u12208 from rfl, allE_node, arows12207, irow12209, arows12208]
  all_goals rfl

theorem atot12209 : totK PD2M8K2 D2M8K2.u12209 = [330028431640, 1417274811714, 1571483297910, 332648287807, 7561889112, 0, 0, 0] := by
  rw [show D2M8K2.u12209 = KTree.node D2M8K2.u12207 (nat_lit 25937961) (nat_lit 1839165647) (nat_lit 0) D2M8K2.u12208 from rfl, totK_node, atot12207, atot12208]
  decide +kernel

theorem arows12212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12212 = true := by
  rw [show D2M8K2.u12212 = KTree.node D2M8K2.u12210 (nat_lit 25945180) (nat_lit 3072839920) (nat_lit 0) D2M8K2.u12211 from rfl, allE_node, arows12210, irow12212, arows12211]
  all_goals rfl

theorem atot12212 : totK PD2M8K2 D2M8K2.u12212 = [0, 555591898107, 1654669350475, 1174266961876, 245612269084, 21385604922, 0, 0] := by
  rw [show D2M8K2.u12212 = KTree.node D2M8K2.u12210 (nat_lit 25945180) (nat_lit 3072839920) (nat_lit 0) D2M8K2.u12211 from rfl, totK_node, atot12210, atot12211]
  decide +kernel

theorem arows12219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12219 = true := by
  rw [show D2M8K2.u12219 = KTree.node D2M8K2.u12217 (nat_lit 25948016) (nat_lit 3581757215) (nat_lit 0) D2M8K2.u12218 from rfl, allE_node, arows12217, irow12219, arows12218]
  all_goals rfl

theorem atot12219 : totK PD2M8K2 D2M8K2.u12219 = [0, 412797747568, 1380001564818, 1377117710666, 395632981193, 15536268932, 0, 0] := by
  rw [show D2M8K2.u12219 = KTree.node D2M8K2.u12217 (nat_lit 25948016) (nat_lit 3581757215) (nat_lit 0) D2M8K2.u12218 from rfl, totK_node, atot12217, atot12218]
  decide +kernel

theorem arows12222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12222 = true := by
  rw [show D2M8K2.u12222 = KTree.node D2M8K2.u12220 (nat_lit 25951565) (nat_lit 2113050302) (nat_lit 0) D2M8K2.u12221 from rfl, allE_node, arows12220, irow12222, arows12221]
  all_goals rfl

theorem atot12222 : totK PD2M8K2 D2M8K2.u12222 = [0, 413041252425, 1521316753547, 1417816381332, 260875843710, 5159868635, 0, 0] := by
  rw [show D2M8K2.u12222 = KTree.node D2M8K2.u12220 (nat_lit 25951565) (nat_lit 2113050302) (nat_lit 0) D2M8K2.u12221 from rfl, totK_node, atot12220, atot12221]
  decide +kernel

theorem arows12226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12226 = true := by
  rw [show D2M8K2.u12226 = KTree.node D2M8K2.u12224 (nat_lit 25955082) (nat_lit 3812376366) (nat_lit 0) D2M8K2.u12225 from rfl, allE_node, arows12224, irow12226, arows12225]
  all_goals rfl

theorem atot12226 : totK PD2M8K2 D2M8K2.u12226 = [0, 423784826750, 1518201221223, 1404300052914, 250884135288, 5218872685, 0, 0] := by
  rw [show D2M8K2.u12226 = KTree.node D2M8K2.u12224 (nat_lit 25955082) (nat_lit 3812376366) (nat_lit 0) D2M8K2.u12225 from rfl, totK_node, atot12224, atot12225]
  decide +kernel

theorem arows12229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12229 = true := by
  rw [show D2M8K2.u12229 = KTree.node D2M8K2.u12227 (nat_lit 25958907) (nat_lit 3745994988) (nat_lit 0) D2M8K2.u12228 from rfl, allE_node, arows12227, irow12229, arows12228]
  all_goals rfl

theorem atot12229 : totK PD2M8K2 D2M8K2.u12229 = [0, 329032524333, 1391467908160, 1578065619523, 327421906708, 3899220927, 0, 0] := by
  rw [show D2M8K2.u12229 = KTree.node D2M8K2.u12227 (nat_lit 25958907) (nat_lit 3745994988) (nat_lit 0) D2M8K2.u12228 from rfl, totK_node, atot12227, atot12228]
  decide +kernel

theorem arows12234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12234 = true := by
  rw [show D2M8K2.u12234 = KTree.node D2M8K2.u12232 (nat_lit 25962819) (nat_lit 2453325934) (nat_lit 0) D2M8K2.u12233 from rfl, allE_node, arows12232, irow12234, arows12233]
  all_goals rfl

theorem atot12234 : totK PD2M8K2 D2M8K2.u12234 = [422513773303, 1448708401420, 1263945202545, 320545497763, 93520099079, 6818291842, 0, 0] := by
  rw [show D2M8K2.u12234 = KTree.node D2M8K2.u12232 (nat_lit 25962819) (nat_lit 2453325934) (nat_lit 0) D2M8K2.u12233 from rfl, totK_node, atot12232, atot12233]
  decide +kernel

theorem arows12237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12237 = true := by
  rw [show D2M8K2.u12237 = KTree.node D2M8K2.u12235 (nat_lit 25966438) (nat_lit 3836968154) (nat_lit 0) D2M8K2.u12236 from rfl, allE_node, arows12235, irow12237, arows12236]
  all_goals rfl

theorem atot12237 : totK PD2M8K2 D2M8K2.u12237 = [397925443009, 1404234081439, 1389569065947, 434054936787, 29376414733, 0, 0, 0] := by
  rw [show D2M8K2.u12237 = KTree.node D2M8K2.u12235 (nat_lit 25966438) (nat_lit 3836968154) (nat_lit 0) D2M8K2.u12236 from rfl, totK_node, atot12235, atot12236]
  decide +kernel

theorem arows12241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12241 = true := by
  rw [show D2M8K2.u12241 = KTree.node D2M8K2.u12239 (nat_lit 25969206) (nat_lit 2684278123) (nat_lit 0) D2M8K2.u12240 from rfl, allE_node, arows12239, irow12241, arows12240]
  all_goals rfl

theorem atot12241 : totK PD2M8K2 D2M8K2.u12241 = [439736597927, 1470247871997, 1383260447808, 332876713338, 10345997863, 0, 0, 0] := by
  rw [show D2M8K2.u12241 = KTree.node D2M8K2.u12239 (nat_lit 25969206) (nat_lit 2684278123) (nat_lit 0) D2M8K2.u12240 from rfl, totK_node, atot12239, atot12240]
  decide +kernel

theorem arows12244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12244 = true := by
  rw [show D2M8K2.u12244 = KTree.node D2M8K2.u12242 (nat_lit 25975942) (nat_lit 3612130719) (nat_lit 0) D2M8K2.u12243 from rfl, allE_node, arows12242, irow12244, arows12243]
  all_goals rfl

theorem atot12244 : totK PD2M8K2 D2M8K2.u12244 = [424831878583, 1477003131698, 1390372547828, 297396203591, 11836626177, 0, 0, 0] := by
  rw [show D2M8K2.u12244 = KTree.node D2M8K2.u12242 (nat_lit 25975942) (nat_lit 3612130719) (nat_lit 0) D2M8K2.u12243 from rfl, totK_node, atot12242, atot12243]
  decide +kernel

theorem arows12250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12250 = true := by
  rw [show D2M8K2.u12250 = KTree.node D2M8K2.u12248 (nat_lit 25979470) (nat_lit 4022490277) (nat_lit 0) D2M8K2.u12249 from rfl, allE_node, arows12248, irow12250, arows12249]
  all_goals rfl

theorem atot12250 : totK PD2M8K2 D2M8K2.u12250 = [326127760768, 1356303201318, 1546486706153, 363560748476, 8852005872, 0, 0, 0] := by
  rw [show D2M8K2.u12250 = KTree.node D2M8K2.u12248 (nat_lit 25979470) (nat_lit 4022490277) (nat_lit 0) D2M8K2.u12249 from rfl, totK_node, atot12248, atot12249]
  decide +kernel

theorem arows12253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12253 = true := by
  rw [show D2M8K2.u12253 = KTree.node D2M8K2.u12251 (nat_lit 25983699) (nat_lit 3205116024) (nat_lit 0) D2M8K2.u12252 from rfl, allE_node, arows12251, irow12253, arows12252]
  all_goals rfl

theorem atot12253 : totK PD2M8K2 D2M8K2.u12253 = [0, 497194975742, 1656581426500, 1209615794472, 141406452123, 1206465782, 0, 0] := by
  rw [show D2M8K2.u12253 = KTree.node D2M8K2.u12251 (nat_lit 25983699) (nat_lit 3205116024) (nat_lit 0) D2M8K2.u12252 from rfl, totK_node, atot12251, atot12252]
  decide +kernel

theorem arows12257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12257 = true := by
  rw [show D2M8K2.u12257 = KTree.node D2M8K2.u12255 (nat_lit 25989176) (nat_lit 3688266149) (nat_lit 0) D2M8K2.u12256 from rfl, allE_node, arows12255, irow12257, arows12256]
  all_goals rfl

theorem atot12257 : totK PD2M8K2 D2M8K2.u12257 = [0, 732305163492, 1876196859341, 956751800109, 65058445129, 0, 0, 0] := by
  rw [show D2M8K2.u12257 = KTree.node D2M8K2.u12255 (nat_lit 25989176) (nat_lit 3688266149) (nat_lit 0) D2M8K2.u12256 from rfl, totK_node, atot12255, atot12256]
  decide +kernel

theorem arows12260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12260 = true := by
  rw [show D2M8K2.u12260 = KTree.node D2M8K2.u12258 (nat_lit 25992346) (nat_lit 4009346706) (nat_lit 0) D2M8K2.u12259 from rfl, allE_node, arows12258, irow12260, arows12259]
  all_goals rfl

theorem atot12260 : totK PD2M8K2 D2M8K2.u12260 = [0, 396588937704, 1456695572766, 1357648842406, 303189609729, 13016197374, 0, 0] := by
  rw [show D2M8K2.u12260 = KTree.node D2M8K2.u12258 (nat_lit 25992346) (nat_lit 4009346706) (nat_lit 0) D2M8K2.u12259 from rfl, totK_node, atot12258, atot12259]
  decide +kernel

theorem arows12265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12265 = true := by
  rw [show D2M8K2.u12265 = KTree.node D2M8K2.u12263 (nat_lit 25999604) (nat_lit 3398742819) (nat_lit 0) D2M8K2.u12264 from rfl, allE_node, arows12263, irow12265, arows12264]
  all_goals rfl

theorem atot12265 : totK PD2M8K2 D2M8K2.u12265 = [90010399694, 556955791485, 1467657851869, 1215543986981, 190172109468, 4574395652, 0, 0] := by
  rw [show D2M8K2.u12265 = KTree.node D2M8K2.u12263 (nat_lit 25999604) (nat_lit 3398742819) (nat_lit 0) D2M8K2.u12264 from rfl, totK_node, atot12263, atot12264]
  decide +kernel

theorem arows12268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12268 = true := by
  rw [show D2M8K2.u12268 = KTree.node D2M8K2.u12266 (nat_lit 26004752) (nat_lit 3643693262) (nat_lit 0) D2M8K2.u12267 from rfl, allE_node, arows12266, irow12268, arows12267]
  all_goals rfl

theorem atot12268 : totK PD2M8K2 D2M8K2.u12268 = [464432862770, 1578504638615, 1353905560042, 194371574137, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u12268 = KTree.node D2M8K2.u12266 (nat_lit 26004752) (nat_lit 3643693262) (nat_lit 0) D2M8K2.u12267 from rfl, totK_node, atot12266, atot12267]
  decide +kernel

theorem arows12272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12272 = true := by
  rw [show D2M8K2.u12272 = KTree.node D2M8K2.u12270 (nat_lit 26008622) (nat_lit 3861051847) (nat_lit 0) D2M8K2.u12271 from rfl, allE_node, arows12270, irow12272, arows12271]
  all_goals rfl

theorem atot12272 : totK PD2M8K2 D2M8K2.u12272 = [313064697672, 1219054971078, 1484715393950, 574661179181, 37411484789, 0, 0, 0] := by
  rw [show D2M8K2.u12272 = KTree.node D2M8K2.u12270 (nat_lit 26008622) (nat_lit 3861051847) (nat_lit 0) D2M8K2.u12271 from rfl, totK_node, atot12270, atot12271]
  decide +kernel

theorem arows12275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12275 = true := by
  rw [show D2M8K2.u12275 = KTree.node D2M8K2.u12273 (nat_lit 26014838) (nat_lit 3930760718) (nat_lit 0) D2M8K2.u12274 from rfl, allE_node, arows12273, irow12275, arows12274]
  all_goals rfl

theorem atot12275 : totK PD2M8K2 D2M8K2.u12275 = [397037788058, 1460802279429, 1423694045293, 327071413694, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u12275 = KTree.node D2M8K2.u12273 (nat_lit 26014838) (nat_lit 3930760718) (nat_lit 0) D2M8K2.u12274 from rfl, totK_node, atot12273, atot12274]
  decide +kernel

theorem arows12288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12288 = true := by
  rw [show D2M8K2.u12288 = KTree.node D2M8K2.u12286 (nat_lit 26017885) (nat_lit 1023417417) (nat_lit 0) D2M8K2.u12287 from rfl, allE_node, arows12286, irow12288, arows12287]
  all_goals rfl

theorem atot12288 : totK PD2M8K2 D2M8K2.u12288 = [424860175082, 1553257635654, 1420272932575, 225916158063, 2165917952, 0, 0, 0] := by
  rw [show D2M8K2.u12288 = KTree.node D2M8K2.u12286 (nat_lit 26017885) (nat_lit 1023417417) (nat_lit 0) D2M8K2.u12287 from rfl, totK_node, atot12286, atot12287]
  decide +kernel

theorem arows12291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12291 = true := by
  rw [show D2M8K2.u12291 = KTree.node D2M8K2.u12289 (nat_lit 26021974) (nat_lit 3542039026) (nat_lit 0) D2M8K2.u12290 from rfl, allE_node, arows12289, irow12291, arows12290]
  all_goals rfl

theorem atot12291 : totK PD2M8K2 D2M8K2.u12291 = [326274180204, 1277817960633, 1516867373786, 452515420089, 19948107892, 0, 0, 0] := by
  rw [show D2M8K2.u12291 = KTree.node D2M8K2.u12289 (nat_lit 26021974) (nat_lit 3542039026) (nat_lit 0) D2M8K2.u12290 from rfl, totK_node, atot12289, atot12290]
  decide +kernel

theorem arows12295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12295 = true := by
  rw [show D2M8K2.u12295 = KTree.node D2M8K2.u12293 (nat_lit 26025610) (nat_lit 2607638312) (nat_lit 0) D2M8K2.u12294 from rfl, allE_node, arows12293, irow12295, arows12294]
  all_goals rfl

theorem atot12295 : totK PD2M8K2 D2M8K2.u12295 = [0, 485502703210, 1632447391246, 1275548771230, 147968092379, 1239866073, 0, 0] := by
  rw [show D2M8K2.u12295 = KTree.node D2M8K2.u12293 (nat_lit 26025610) (nat_lit 2607638312) (nat_lit 0) D2M8K2.u12294 from rfl, totK_node, atot12293, atot12294]
  decide +kernel

theorem arows12298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12298 = true := by
  rw [show D2M8K2.u12298 = KTree.node D2M8K2.u12296 (nat_lit 26034512) (nat_lit 3701545796) (nat_lit 0) D2M8K2.u12297 from rfl, allE_node, arows12296, irow12298, arows12297]
  all_goals rfl

theorem atot12298 : totK PD2M8K2 D2M8K2.u12298 = [0, 655071628672, 1799556744871, 1043079507862, 102896032767, 1171084559, 0, 0] := by
  rw [show D2M8K2.u12298 = KTree.node D2M8K2.u12296 (nat_lit 26034512) (nat_lit 3701545796) (nat_lit 0) D2M8K2.u12297 from rfl, totK_node, atot12296, atot12297]
  decide +kernel

theorem arows12303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12303 = true := by
  rw [show D2M8K2.u12303 = KTree.node D2M8K2.u12301 (nat_lit 26037849) (nat_lit 1823894387) (nat_lit 0) D2M8K2.u12302 from rfl, allE_node, arows12301, irow12303, arows12302]
  all_goals rfl

theorem atot12303 : totK PD2M8K2 D2M8K2.u12303 = [0, 422543073938, 1500849007540, 1333907643798, 276615419413, 11934365838, 0, 0] := by
  rw [show D2M8K2.u12303 = KTree.node D2M8K2.u12301 (nat_lit 26037849) (nat_lit 1823894387) (nat_lit 0) D2M8K2.u12302 from rfl, totK_node, atot12301, atot12302]
  decide +kernel

theorem arows12306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12306 = true := by
  rw [show D2M8K2.u12306 = KTree.node D2M8K2.u12304 (nat_lit 26041462) (nat_lit 3090713237) (nat_lit 0) D2M8K2.u12305 from rfl, allE_node, arows12304, irow12306, arows12305]
  all_goals rfl

theorem atot12306 : totK PD2M8K2 D2M8K2.u12306 = [182717929658, 776440770408, 1356996201296, 1048844228980, 182117669914, 4720618446, 0, 0] := by
  rw [show D2M8K2.u12306 = KTree.node D2M8K2.u12304 (nat_lit 26041462) (nat_lit 3090713237) (nat_lit 0) D2M8K2.u12305 from rfl, totK_node, atot12304, atot12305]
  decide +kernel

theorem arows12310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12310 = true := by
  rw [show D2M8K2.u12310 = KTree.node D2M8K2.u12308 (nat_lit 26046847) (nat_lit 1346488587) (nat_lit 0) D2M8K2.u12309 from rfl, allE_node, arows12308, irow12310, arows12309]
  all_goals rfl

theorem atot12310 : totK PD2M8K2 D2M8K2.u12310 = [480205767480, 1587223442113, 1352112783230, 194511731715, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u12310 = KTree.node D2M8K2.u12308 (nat_lit 26046847) (nat_lit 1346488587) (nat_lit 0) D2M8K2.u12309 from rfl, totK_node, atot12308, atot12309]
  decide +kernel

theorem arows12313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12313 = true := by
  rw [show D2M8K2.u12313 = KTree.node D2M8K2.u12311 (nat_lit 26050349) (nat_lit 2033983759) (nat_lit 0) D2M8K2.u12312 from rfl, allE_node, arows12311, irow12313, arows12312]
  all_goals rfl

theorem atot12313 : totK PD2M8K2 D2M8K2.u12313 = [302327969294, 1226317821433, 1486089345343, 574205670172, 37364365039, 0, 0, 0] := by
  rw [show D2M8K2.u12313 = KTree.node D2M8K2.u12311 (nat_lit 26050349) (nat_lit 2033983759) (nat_lit 0) D2M8K2.u12312 from rfl, totK_node, atot12311, atot12312]
  decide +kernel

theorem arows12319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12319 = true := by
  rw [show D2M8K2.u12319 = KTree.node D2M8K2.u12317 (nat_lit 26053188) (nat_lit 3236805905) (nat_lit 0) D2M8K2.u12318 from rfl, allE_node, arows12317, irow12319, arows12318]
  all_goals rfl

theorem atot12319 : totK PD2M8K2 D2M8K2.u12319 = [378740173579, 1418956579938, 1440549369740, 332121930812, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u12319 = KTree.node D2M8K2.u12317 (nat_lit 26053188) (nat_lit 3236805905) (nat_lit 0) D2M8K2.u12318 from rfl, totK_node, atot12317, atot12318]
  decide +kernel

theorem arows12322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12322 = true := by
  rw [show D2M8K2.u12322 = KTree.node D2M8K2.u12320 (nat_lit 26056584) (nat_lit 3621588267) (nat_lit 0) D2M8K2.u12321 from rfl, allE_node, arows12320, irow12322, arows12321]
  all_goals rfl

theorem atot12322 : totK PD2M8K2 D2M8K2.u12322 = [423135840574, 1420253556670, 1411165706848, 342691587848, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u12322 = KTree.node D2M8K2.u12320 (nat_lit 26056584) (nat_lit 3621588267) (nat_lit 0) D2M8K2.u12321 from rfl, totK_node, atot12320, atot12321]
  decide +kernel

theorem arows12326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12326 = true := by
  rw [show D2M8K2.u12326 = KTree.node D2M8K2.u12324 (nat_lit 26059556) (nat_lit 3116490976) (nat_lit 0) D2M8K2.u12325 from rfl, allE_node, arows12324, irow12326, arows12325]
  all_goals rfl

theorem atot12326 : totK PD2M8K2 D2M8K2.u12326 = [358558880073, 1519318624097, 1515589048572, 261566171419, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u12326 = KTree.node D2M8K2.u12324 (nat_lit 26059556) (nat_lit 3116490976) (nat_lit 0) D2M8K2.u12325 from rfl, totK_node, atot12324, atot12325]
  decide +kernel

theorem arows12329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12329 = true := by
  rw [show D2M8K2.u12329 = KTree.node D2M8K2.u12327 (nat_lit 26066880) (nat_lit 3766812078) (nat_lit 0) D2M8K2.u12328 from rfl, allE_node, arows12327, irow12329, arows12328]
  all_goals rfl

theorem atot12329 : totK PD2M8K2 D2M8K2.u12329 = [0, 507199430915, 1690545164991, 1189251796264, 133022633509, 1138244013, 0, 0] := by
  rw [show D2M8K2.u12329 = KTree.node D2M8K2.u12327 (nat_lit 26066880) (nat_lit 3766812078) (nat_lit 0) D2M8K2.u12328 from rfl, totK_node, atot12327, atot12328]
  decide +kernel

theorem arows12334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12334 = true := by
  rw [show D2M8K2.u12334 = KTree.node D2M8K2.u12332 (nat_lit 26072384) (nat_lit 3775447650) (nat_lit 0) D2M8K2.u12333 from rfl, allE_node, arows12332, irow12334, arows12333]
  all_goals rfl

theorem atot12334 : totK PD2M8K2 D2M8K2.u12334 = [0, 742308668606, 1902838161174, 904047522597, 51406617085, 0, 0, 0] := by
  rw [show D2M8K2.u12334 = KTree.node D2M8K2.u12332 (nat_lit 26072384) (nat_lit 3775447650) (nat_lit 0) D2M8K2.u12333 from rfl, totK_node, atot12332, atot12333]
  decide +kernel

theorem arows12337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12337 = true := by
  rw [show D2M8K2.u12337 = KTree.node D2M8K2.u12335 (nat_lit 26077186) (nat_lit 3792297284) (nat_lit 0) D2M8K2.u12336 from rfl, allE_node, arows12335, irow12337, arows12336]
  all_goals rfl

theorem atot12337 : totK PD2M8K2 D2M8K2.u12337 = [0, 719112693471, 1874786711288, 943723197804, 59851078227, 0, 0, 0] := by
  rw [show D2M8K2.u12337 = KTree.node D2M8K2.u12335 (nat_lit 26077186) (nat_lit 3792297284) (nat_lit 0) D2M8K2.u12336 from rfl, totK_node, atot12335, atot12336]
  decide +kernel

theorem arows12341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12341 = true := by
  rw [show D2M8K2.u12341 = KTree.node D2M8K2.u12339 (nat_lit 26082112) (nat_lit 2837447030) (nat_lit 0) D2M8K2.u12340 from rfl, allE_node, arows12339, irow12341, arows12340]
  all_goals rfl

theorem atot12341 : totK PD2M8K2 D2M8K2.u12341 = [0, 473592017436, 1596410724555, 1265931638052, 214601338314, 4977114383, 0, 0] := by
  rw [show D2M8K2.u12341 = KTree.node D2M8K2.u12339 (nat_lit 26082112) (nat_lit 2837447030) (nat_lit 0) D2M8K2.u12340 from rfl, totK_node, atot12339, atot12340]
  decide +kernel

theorem arows12344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12344 = true := by
  rw [show D2M8K2.u12344 = KTree.node D2M8K2.u12342 (nat_lit 26134376) (nat_lit 3842096157) (nat_lit 0) D2M8K2.u12343 from rfl, allE_node, arows12342, irow12344, arows12343]
  all_goals rfl

theorem atot12344 : totK PD2M8K2 D2M8K2.u12344 = [0, 445490065599, 1598239891106, 1362667137240, 180157622182, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12344 = KTree.node D2M8K2.u12342 (nat_lit 26134376) (nat_lit 3842096157) (nat_lit 0) D2M8K2.u12343 from rfl, totK_node, atot12342, atot12343]
  decide +kernel

theorem arows12351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12351 = true := by
  rw [show D2M8K2.u12351 = KTree.node D2M8K2.u12349 (nat_lit 26137828) (nat_lit 3392883032) (nat_lit 0) D2M8K2.u12350 from rfl, allE_node, arows12349, irow12351, arows12350]
  all_goals rfl

theorem atot12351 : totK PD2M8K2 D2M8K2.u12351 = [0, 409627050649, 1454215549038, 1387096541056, 292250307942, 12983449796, 0, 0] := by
  rw [show D2M8K2.u12351 = KTree.node D2M8K2.u12349 (nat_lit 26137828) (nat_lit 3392883032) (nat_lit 0) D2M8K2.u12350 from rfl, totK_node, atot12349, atot12350]
  decide +kernel

theorem arows12354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12354 = true := by
  rw [show D2M8K2.u12354 = KTree.node D2M8K2.u12352 (nat_lit 26141274) (nat_lit 3873051234) (nat_lit 0) D2M8K2.u12353 from rfl, allE_node, arows12352, irow12354, arows12353]
  all_goals rfl

theorem atot12354 : totK PD2M8K2 D2M8K2.u12354 = [0, 421945338544, 1426665441470, 1386292953901, 308290990250, 13184317400, 0, 0] := by
  rw [show D2M8K2.u12354 = KTree.node D2M8K2.u12352 (nat_lit 26141274) (nat_lit 3873051234) (nat_lit 0) D2M8K2.u12353 from rfl, totK_node, atot12352, atot12353]
  decide +kernel

theorem arows12358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12358 = true := by
  rw [show D2M8K2.u12358 = KTree.node D2M8K2.u12356 (nat_lit 26144774) (nat_lit 2386998304) (nat_lit 0) D2M8K2.u12357 from rfl, allE_node, arows12356, irow12358, arows12357]
  all_goals rfl

theorem atot12358 : totK PD2M8K2 D2M8K2.u12358 = [0, 321824156341, 1427088995976, 1512294414047, 289591375923, 6249254262, 0, 0] := by
  rw [show D2M8K2.u12358 = KTree.node D2M8K2.u12356 (nat_lit 26144774) (nat_lit 2386998304) (nat_lit 0) D2M8K2.u12357 from rfl, totK_node, atot12356, atot12357]
  decide +kernel

theorem arows12361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12361 = true := by
  rw [show D2M8K2.u12361 = KTree.node D2M8K2.u12359 (nat_lit 26149234) (nat_lit 4089415224) (nat_lit 0) D2M8K2.u12360 from rfl, allE_node, arows12359, irow12361, arows12360]
  all_goals rfl

theorem atot12361 : totK PD2M8K2 D2M8K2.u12361 = [0, 0, 624563108536, 1746862530292, 972884799989, 109523310931, 1209030869, 0] := by
  rw [show D2M8K2.u12361 = KTree.node D2M8K2.u12359 (nat_lit 26149234) (nat_lit 4089415224) (nat_lit 0) D2M8K2.u12360 from rfl, totK_node, atot12359, atot12360]
  decide +kernel

theorem arows12366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12366 = true := by
  rw [show D2M8K2.u12366 = KTree.node D2M8K2.u12364 (nat_lit 26158557) (nat_lit 1565350020) (nat_lit 0) D2M8K2.u12365 from rfl, allE_node, arows12364, irow12366, arows12365]
  all_goals rfl

theorem atot12366 : totK PD2M8K2 D2M8K2.u12366 = [0, 0, 894931680846, 1934234014052, 672046888061, 28539104444, 0, 0] := by
  rw [show D2M8K2.u12366 = KTree.node D2M8K2.u12364 (nat_lit 26158557) (nat_lit 1565350020) (nat_lit 0) D2M8K2.u12365 from rfl, totK_node, atot12364, atot12365]
  decide +kernel

theorem arows12369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12369 = true := by
  rw [show D2M8K2.u12369 = KTree.node D2M8K2.u12367 (nat_lit 26165468) (nat_lit 2918971320) (nat_lit 0) D2M8K2.u12368 from rfl, allE_node, arows12367, irow12369, arows12368]
  all_goals rfl

theorem atot12369 : totK PD2M8K2 D2M8K2.u12369 = [0, 188814269997, 1120209126597, 1706736665248, 534901721274, 23319289582, 0, 0] := by
  rw [show D2M8K2.u12369 = KTree.node D2M8K2.u12367 (nat_lit 26165468) (nat_lit 2918971320) (nat_lit 0) D2M8K2.u12368 from rfl, totK_node, atot12367, atot12368]
  decide +kernel

theorem arows12373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12373 = true := by
  rw [show D2M8K2.u12373 = KTree.node D2M8K2.u12371 (nat_lit 26174618) (nat_lit 4242461733) (nat_lit 0) D2M8K2.u12372 from rfl, allE_node, arows12371, irow12373, arows12372]
  all_goals rfl

theorem atot12373 : totK PD2M8K2 D2M8K2.u12373 = [0, 317628286962, 1226641636140, 1485189326761, 571864758085, 37498978443, 0, 0] := by
  rw [show D2M8K2.u12373 = KTree.node D2M8K2.u12371 (nat_lit 26174618) (nat_lit 4242461733) (nat_lit 0) D2M8K2.u12372 from rfl, totK_node, atot12371, atot12372]
  decide +kernel

theorem arows12376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12376 = true := by
  rw [show D2M8K2.u12376 = KTree.node D2M8K2.u12374 (nat_lit 26177448) (nat_lit 2574439466) (nat_lit 0) D2M8K2.u12375 from rfl, allE_node, arows12374, irow12376, arows12375]
  all_goals rfl

theorem atot12376 : totK PD2M8K2 D2M8K2.u12376 = [0, 413032005514, 1506245567528, 1398609688966, 281492751913, 11873025674, 0, 0] := by
  rw [show D2M8K2.u12376 = KTree.node D2M8K2.u12374 (nat_lit 26177448) (nat_lit 2574439466) (nat_lit 0) D2M8K2.u12375 from rfl, totK_node, atot12374, atot12375]
  decide +kernel

theorem arows12382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12382 = true := by
  rw [show D2M8K2.u12382 = KTree.node D2M8K2.u12380 (nat_lit 26180935) (nat_lit 2376173763) (nat_lit 0) D2M8K2.u12381 from rfl, allE_node, arows12380, irow12382, arows12381]
  all_goals rfl

theorem atot12382 : totK PD2M8K2 D2M8K2.u12382 = [0, 428594347125, 1495294085907, 1388842513881, 291219570745, 12040273252, 0, 0] := by
  rw [show D2M8K2.u12382 = KTree.node D2M8K2.u12380 (nat_lit 26180935) (nat_lit 2376173763) (nat_lit 0) D2M8K2.u12381 from rfl, totK_node, atot12380, atot12381]
  decide +kernel

theorem arows12385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12385 = true := by
  rw [show D2M8K2.u12385 = KTree.node D2M8K2.u12383 (nat_lit 26184402) (nat_lit 3202579114) (nat_lit 0) D2M8K2.u12384 from rfl, allE_node, arows12383, irow12385, arows12384]
  all_goals rfl

theorem atot12385 : totK PD2M8K2 D2M8K2.u12385 = [0, 453260453587, 1579311949463, 1407239521946, 224270700512, 3880716147, 0, 0] := by
  rw [show D2M8K2.u12385 = KTree.node D2M8K2.u12383 (nat_lit 26184402) (nat_lit 3202579114) (nat_lit 0) D2M8K2.u12384 from rfl, totK_node, atot12383, atot12384]
  decide +kernel

theorem arows12389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12389 = true := by
  rw [show D2M8K2.u12389 = KTree.node D2M8K2.u12387 (nat_lit 26188717) (nat_lit 1229749620) (nat_lit 0) D2M8K2.u12388 from rfl, allE_node, arows12387, irow12389, arows12388]
  all_goals rfl

theorem atot12389 : totK PD2M8K2 D2M8K2.u12389 = [0, 458293339288, 1505809780286, 1321048564690, 304412908179, 9730542555, 0, 0] := by
  rw [show D2M8K2.u12389 = KTree.node D2M8K2.u12387 (nat_lit 26188717) (nat_lit 1229749620) (nat_lit 0) D2M8K2.u12388 from rfl, totK_node, atot12387, atot12388]
  decide +kernel

theorem arows12392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12392 = true := by
  rw [show D2M8K2.u12392 = KTree.node D2M8K2.u12390 (nat_lit 26213240) (nat_lit 3785500377) (nat_lit 0) D2M8K2.u12391 from rfl, allE_node, arows12390, irow12392, arows12391]
  all_goals rfl

theorem atot12392 : totK PD2M8K2 D2M8K2.u12392 = [0, 480706716800, 1594558946629, 1348470400232, 176958501579, 1310166938, 0, 0] := by
  rw [show D2M8K2.u12392 = KTree.node D2M8K2.u12390 (nat_lit 26213240) (nat_lit 3785500377) (nat_lit 0) D2M8K2.u12391 from rfl, totK_node, atot12390, atot12391]
  decide +kernel

theorem arows12397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12397 = true := by
  rw [show D2M8K2.u12397 = KTree.node D2M8K2.u12395 (nat_lit 26216699) (nat_lit 2130132824) (nat_lit 0) D2M8K2.u12396 from rfl, allE_node, arows12395, irow12397, arows12396]
  all_goals rfl

theorem atot12397 : totK PD2M8K2 D2M8K2.u12397 = [0, 366089668088, 1409691320569, 1469822466612, 391012833027, 15013989272, 0, 0] := by
  rw [show D2M8K2.u12397 = KTree.node D2M8K2.u12395 (nat_lit 26216699) (nat_lit 2130132824) (nat_lit 0) D2M8K2.u12396 from rfl, totK_node, atot12395, atot12396]
  decide +kernel

theorem arows12400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12400 = true := by
  rw [show D2M8K2.u12400 = KTree.node D2M8K2.u12398 (nat_lit 26219716) (nat_lit 4016555572) (nat_lit 0) D2M8K2.u12399 from rfl, allE_node, arows12398, irow12400, arows12399]
  all_goals rfl

theorem atot12400 : totK PD2M8K2 D2M8K2.u12400 = [0, 416563888833, 1437523844800, 1414765918694, 322097096476, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12400 = KTree.node D2M8K2.u12398 (nat_lit 26219716) (nat_lit 4016555572) (nat_lit 0) D2M8K2.u12399 from rfl, totK_node, atot12398, atot12399]
  decide +kernel

theorem arows12404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12404 = true := by
  rw [show D2M8K2.u12404 = KTree.node D2M8K2.u12402 (nat_lit 26226541) (nat_lit 1111477064) (nat_lit 0) D2M8K2.u12403 from rfl, allE_node, arows12402, irow12404, arows12403]
  all_goals rfl

theorem atot12404 : totK PD2M8K2 D2M8K2.u12404 = [0, 430363960215, 1526000784571, 1390592640195, 241605160775, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12404 = KTree.node D2M8K2.u12402 (nat_lit 26226541) (nat_lit 1111477064) (nat_lit 0) D2M8K2.u12403 from rfl, totK_node, atot12402, atot12403]
  decide +kernel

theorem arows12407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12407 = true := by
  rw [show D2M8K2.u12407 = KTree.node D2M8K2.u12405 (nat_lit 26251851) (nat_lit 2834267261) (nat_lit 0) D2M8K2.u12406 from rfl, allE_node, arows12405, irow12407, arows12406]
  all_goals rfl

theorem atot12407 : totK PD2M8K2 D2M8K2.u12407 = [0, 478232267787, 1567091455598, 1283996150216, 222389897989, 4880895167, 0, 0] := by
  rw [show D2M8K2.u12407 = KTree.node D2M8K2.u12405 (nat_lit 26251851) (nat_lit 2834267261) (nat_lit 0) D2M8K2.u12406 from rfl, totK_node, atot12405, atot12406]
  decide +kernel

theorem arows12415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12415 = true := by
  rw [show D2M8K2.u12415 = KTree.node D2M8K2.u12413 (nat_lit 26255794) (nat_lit 4137157413) (nat_lit 0) D2M8K2.u12414 from rfl, allE_node, arows12413, irow12415, arows12414]
  all_goals rfl

theorem atot12415 : totK PD2M8K2 D2M8K2.u12415 = [0, 417397204449, 1570111996328, 1443844322472, 198924976111, 1310517177, 0, 0] := by
  rw [show D2M8K2.u12415 = KTree.node D2M8K2.u12413 (nat_lit 26255794) (nat_lit 4137157413) (nat_lit 0) D2M8K2.u12414 from rfl, totK_node, atot12413, atot12414]
  decide +kernel

theorem arows12418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12418 = true := by
  rw [show D2M8K2.u12418 = KTree.node D2M8K2.u12416 (nat_lit 26262366) (nat_lit 3987774429) (nat_lit 0) D2M8K2.u12417 from rfl, allE_node, arows12416, irow12418, arows12417]
  all_goals rfl

theorem atot12418 : totK PD2M8K2 D2M8K2.u12418 = [0, 439218075986, 1452811752445, 1380998487639, 367689802903, 15066332673, 0, 0] := by
  rw [show D2M8K2.u12418 = KTree.node D2M8K2.u12416 (nat_lit 26262366) (nat_lit 3987774429) (nat_lit 0) D2M8K2.u12417 from rfl, totK_node, atot12416, atot12417]
  decide +kernel

theorem arows12422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12422 = true := by
  rw [show D2M8K2.u12422 = KTree.node D2M8K2.u12420 (nat_lit 26265657) (nat_lit 1818145054) (nat_lit 0) D2M8K2.u12421 from rfl, allE_node, arows12420, irow12422, arows12421]
  all_goals rfl

theorem atot12422 : totK PD2M8K2 D2M8K2.u12422 = [0, 404159302714, 1403443536156, 1428365330113, 341545298800, 13170675918, 0, 0] := by
  rw [show D2M8K2.u12422 = KTree.node D2M8K2.u12420 (nat_lit 26265657) (nat_lit 1818145054) (nat_lit 0) D2M8K2.u12421 from rfl, totK_node, atot12420, atot12421]
  decide +kernel

theorem arows12425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12425 = true := by
  rw [show D2M8K2.u12425 = KTree.node D2M8K2.u12423 (nat_lit 26269149) (nat_lit 1504789060) (nat_lit 0) D2M8K2.u12424 from rfl, allE_node, arows12423, irow12425, arows12424]
  all_goals rfl

theorem atot12425 : totK PD2M8K2 D2M8K2.u12425 = [0, 344753255210, 1457791161616, 1503403936712, 278613969376, 6190621007, 0, 0] := by
  rw [show D2M8K2.u12425 = KTree.node D2M8K2.u12423 (nat_lit 26269149) (nat_lit 1504789060) (nat_lit 0) D2M8K2.u12424 from rfl, totK_node, atot12423, atot12424]
  decide +kernel

theorem arows12430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12430 = true := by
  rw [show D2M8K2.u12430 = KTree.node D2M8K2.u12428 (nat_lit 26294142) (nat_lit 3918539046) (nat_lit 0) D2M8K2.u12429 from rfl, allE_node, arows12428, irow12430, arows12429]
  all_goals rfl

theorem atot12430 : totK PD2M8K2 D2M8K2.u12430 = [0, 413617917396, 1483371020874, 1378973592794, 261838916943, 5051095886, 0, 0] := by
  rw [show D2M8K2.u12430 = KTree.node D2M8K2.u12428 (nat_lit 26294142) (nat_lit 3918539046) (nat_lit 0) D2M8K2.u12429 from rfl, totK_node, atot12428, atot12429]
  decide +kernel

theorem arows12433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12433 = true := by
  rw [show D2M8K2.u12433 = KTree.node D2M8K2.u12431 (nat_lit 26297730) (nat_lit 3202396569) (nat_lit 0) D2M8K2.u12432 from rfl, allE_node, arows12431, irow12433, arows12432]
  all_goals rfl

theorem atot12433 : totK PD2M8K2 D2M8K2.u12433 = [0, 424469776137, 1485082101123, 1392203137417, 312525316283, 18317572719, 0, 0] := by
  rw [show D2M8K2.u12433 = KTree.node D2M8K2.u12431 (nat_lit 26297730) (nat_lit 3202396569) (nat_lit 0) D2M8K2.u12432 from rfl, totK_node, atot12431, atot12432]
  decide +kernel

theorem arows12437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12437 = true := by
  rw [show D2M8K2.u12437 = KTree.node D2M8K2.u12435 (nat_lit 26300712) (nat_lit 1834517133) (nat_lit 0) D2M8K2.u12436 from rfl, allE_node, arows12435, irow12437, arows12436]
  all_goals rfl

theorem atot12437 : totK PD2M8K2 D2M8K2.u12437 = [0, 419204832774, 1464388695851, 1410255123239, 304008088393, 6522524465, 0, 0] := by
  rw [show D2M8K2.u12437 = KTree.node D2M8K2.u12435 (nat_lit 26300712) (nat_lit 1834517133) (nat_lit 0) D2M8K2.u12436 from rfl, totK_node, atot12435, atot12436]
  decide +kernel

theorem arows12440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12440 = true := by
  rw [show D2M8K2.u12440 = KTree.node D2M8K2.u12438 (nat_lit 26304121) (nat_lit 1206445477) (nat_lit 0) D2M8K2.u12439 from rfl, allE_node, arows12438, irow12440, arows12439]
  all_goals rfl

theorem atot12440 : totK PD2M8K2 D2M8K2.u12440 = [0, 419402241294, 1451166923059, 1386498642491, 298665090261, 12943032596, 0, 0] := by
  rw [show D2M8K2.u12440 = KTree.node D2M8K2.u12438 (nat_lit 26304121) (nat_lit 1206445477) (nat_lit 0) D2M8K2.u12439 from rfl, totK_node, atot12438, atot12439]
  decide +kernel

theorem arows12446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12446 = true := by
  rw [show D2M8K2.u12446 = KTree.node D2M8K2.u12444 (nat_lit 26307503) (nat_lit 1986990880) (nat_lit 0) D2M8K2.u12445 from rfl, allE_node, arows12444, irow12446, arows12445]
  all_goals rfl

theorem atot12446 : totK PD2M8K2 D2M8K2.u12446 = [0, 444116253521, 1516838483604, 1361416754269, 272154527347, 13043838850, 0, 0] := by
  rw [show D2M8K2.u12446 = KTree.node D2M8K2.u12444 (nat_lit 26307503) (nat_lit 1986990880) (nat_lit 0) D2M8K2.u12445 from rfl, totK_node, atot12444, atot12445]
  decide +kernel

theorem arows12449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12449 = true := by
  rw [show D2M8K2.u12449 = KTree.node D2M8K2.u12447 (nat_lit 26314681) (nat_lit 1487024668) (nat_lit 0) D2M8K2.u12448 from rfl, allE_node, arows12447, irow12449, arows12448]
  all_goals rfl

theorem atot12449 : totK PD2M8K2 D2M8K2.u12449 = [0, 0, 761904097631, 1849314922138, 809207499624, 81623518997, 1138244013, 0] := by
  rw [show D2M8K2.u12449 = KTree.node D2M8K2.u12447 (nat_lit 26314681) (nat_lit 1487024668) (nat_lit 0) D2M8K2.u12448 from rfl, totK_node, atot12447, atot12448]
  decide +kernel

theorem arows12453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12453 = true := by
  rw [show D2M8K2.u12453 = KTree.node D2M8K2.u12451 (nat_lit 26318530) (nat_lit 3603237039) (nat_lit 0) D2M8K2.u12452 from rfl, allE_node, arows12451, irow12453, arows12452]
  all_goals rfl

theorem atot12453 : totK PD2M8K2 D2M8K2.u12453 = [0, 0, 678572800336, 1848232351111, 947836648049, 69999173690, 0, 0] := by
  rw [show D2M8K2.u12453 = KTree.node D2M8K2.u12451 (nat_lit 26318530) (nat_lit 3603237039) (nat_lit 0) D2M8K2.u12452 from rfl, totK_node, atot12451, atot12452]
  decide +kernel

theorem arows12456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12456 = true := by
  rw [show D2M8K2.u12456 = KTree.node D2M8K2.u12454 (nat_lit 26325391) (nat_lit 2359552723) (nat_lit 0) D2M8K2.u12455 from rfl, allE_node, arows12454, irow12456, arows12455]
  all_goals rfl

theorem atot12456 : totK PD2M8K2 D2M8K2.u12456 = [0, 0, 824914431863, 1895345835339, 784490703393, 50173541329, 0, 0] := by
  rw [show D2M8K2.u12456 = KTree.node D2M8K2.u12454 (nat_lit 26325391) (nat_lit 2359552723) (nat_lit 0) D2M8K2.u12455 from rfl, totK_node, atot12454, atot12455]
  decide +kernel

theorem arows12461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12461 = true := by
  rw [show D2M8K2.u12461 = KTree.node D2M8K2.u12459 (nat_lit 26330221) (nat_lit 1111477064) (nat_lit 0) D2M8K2.u12460 from rfl, allE_node, arows12459, irow12461, arows12460]
  all_goals rfl

theorem atot12461 : totK PD2M8K2 D2M8K2.u12461 = [0, 267847118239, 799627518633, 1216669626369, 1040146695632, 208501514346, 4977114383, 0] := by
  rw [show D2M8K2.u12461 = KTree.node D2M8K2.u12459 (nat_lit 26330221) (nat_lit 1111477064) (nat_lit 0) D2M8K2.u12460 from rfl, totK_node, atot12459, atot12460]
  decide +kernel

theorem arows12464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12464 = true := by
  rw [show D2M8K2.u12464 = KTree.node D2M8K2.u12462 (nat_lit 26876560) (nat_lit 2435781022) (nat_lit 0) D2M8K2.u12463 from rfl, allE_node, arows12462, irow12464, arows12463]
  all_goals rfl

theorem atot12464 : totK PD2M8K2 D2M8K2.u12464 = [0, 446184136898, 1599142601265, 1387807320956, 192201926738, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12464 = KTree.node D2M8K2.u12462 (nat_lit 26876560) (nat_lit 2435781022) (nat_lit 0) D2M8K2.u12463 from rfl, totK_node, atot12462, atot12463]
  decide +kernel

theorem arows12468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12468 = true := by
  rw [show D2M8K2.u12468 = KTree.node D2M8K2.u12466 (nat_lit 26883341) (nat_lit 1906733758) (nat_lit 0) D2M8K2.u12467 from rfl, allE_node, arows12466, irow12468, arows12467]
  all_goals rfl

theorem atot12468 : totK PD2M8K2 D2M8K2.u12468 = [0, 391632512030, 1416357984937, 1412117649784, 320909339457, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12468 = KTree.node D2M8K2.u12466 (nat_lit 26883341) (nat_lit 1906733758) (nat_lit 0) D2M8K2.u12467 from rfl, totK_node, atot12466, atot12467]
  decide +kernel

theorem arows12471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12471 = true := by
  rw [show D2M8K2.u12471 = KTree.node D2M8K2.u12469 (nat_lit 26886990) (nat_lit 3904687393) (nat_lit 0) D2M8K2.u12470 from rfl, allE_node, arows12469, irow12471, arows12470]
  all_goals rfl

theorem atot12471 : totK PD2M8K2 D2M8K2.u12471 = [0, 411960253430, 1414754403980, 1388236994067, 329920688588, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12471 = KTree.node D2M8K2.u12469 (nat_lit 26886990) (nat_lit 3904687393) (nat_lit 0) D2M8K2.u12470 from rfl, totK_node, atot12469, atot12470]
  decide +kernel

theorem arows12478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12478 = true := by
  rw [show D2M8K2.u12478 = KTree.node D2M8K2.u12476 (nat_lit 26890115) (nat_lit 2877119303) (nat_lit 0) D2M8K2.u12477 from rfl, allE_node, arows12476, irow12478, arows12477]
  all_goals rfl

theorem atot12478 : totK PD2M8K2 D2M8K2.u12478 = [0, 416448493786, 1522779703134, 1398235132392, 236237745626, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12478 = KTree.node D2M8K2.u12476 (nat_lit 26890115) (nat_lit 2877119303) (nat_lit 0) D2M8K2.u12477 from rfl, totK_node, atot12476, atot12477]
  decide +kernel

theorem arows12481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12481 = true := by
  rw [show D2M8K2.u12481 = KTree.node D2M8K2.u12479 (nat_lit 26893706) (nat_lit 3705937484) (nat_lit 0) D2M8K2.u12480 from rfl, allE_node, arows12479, irow12481, arows12480]
  all_goals rfl

theorem atot12481 : totK PD2M8K2 D2M8K2.u12481 = [0, 162867068856, 1056667840368, 1698574398073, 587374322448, 31659692706, 0, 0] := by
  rw [show D2M8K2.u12481 = KTree.node D2M8K2.u12479 (nat_lit 26893706) (nat_lit 3705937484) (nat_lit 0) D2M8K2.u12480 from rfl, totK_node, atot12479, atot12480]
  decide +kernel

theorem arows12485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12485 = true := by
  rw [show D2M8K2.u12485 = KTree.node D2M8K2.u12483 (nat_lit 26897019) (nat_lit 2009190676) (nat_lit 0) D2M8K2.u12484 from rfl, allE_node, arows12483, irow12485, arows12484]
  all_goals rfl

theorem atot12485 : totK PD2M8K2 D2M8K2.u12485 = [0, 0, 474507171532, 1645305370392, 1220928071477, 166351064291, 1369150432, 0] := by
  rw [show D2M8K2.u12485 = KTree.node D2M8K2.u12483 (nat_lit 26897019) (nat_lit 2009190676) (nat_lit 0) D2M8K2.u12484 from rfl, totK_node, atot12483, atot12484]
  decide +kernel

theorem arows12488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12488 = true := by
  rw [show D2M8K2.u12488 = KTree.node D2M8K2.u12486 (nat_lit 26905923) (nat_lit 3545398558) (nat_lit 0) D2M8K2.u12487 from rfl, allE_node, arows12486, irow12488, arows12487]
  all_goals rfl

theorem atot12488 : totK PD2M8K2 D2M8K2.u12488 = [0, 0, 740659042269, 1893214195408, 846919844913, 43053134310, 0, 0] := by
  rw [show D2M8K2.u12488 = KTree.node D2M8K2.u12486 (nat_lit 26905923) (nat_lit 3545398558) (nat_lit 0) D2M8K2.u12487 from rfl, totK_node, atot12486, atot12487]
  decide +kernel

theorem arows12493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12493 = true := by
  rw [show D2M8K2.u12493 = KTree.node D2M8K2.u12491 (nat_lit 26912242) (nat_lit 3957355096) (nat_lit 0) D2M8K2.u12492 from rfl, allE_node, arows12491, irow12493, arows12492]
  all_goals rfl

theorem atot12493 : totK PD2M8K2 D2M8K2.u12493 = [0, 90905995700, 846513754264, 1766315913702, 791078068525, 44869109229, 0, 0] := by
  rw [show D2M8K2.u12493 = KTree.node D2M8K2.u12491 (nat_lit 26912242) (nat_lit 3957355096) (nat_lit 0) D2M8K2.u12492 from rfl, totK_node, atot12491, atot12492]
  decide +kernel

theorem arows12496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12496 = true := by
  rw [show D2M8K2.u12496 = KTree.node D2M8K2.u12494 (nat_lit 26958581) (nat_lit 2376382725) (nat_lit 0) D2M8K2.u12495 from rfl, allE_node, arows12494, irow12496, arows12495]
  all_goals rfl

theorem atot12496 : totK PD2M8K2 D2M8K2.u12496 = [0, 470402144819, 1606436295035, 1348641735086, 183435094625, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12496 = KTree.node D2M8K2.u12494 (nat_lit 26958581) (nat_lit 2376382725) (nat_lit 0) D2M8K2.u12495 from rfl, totK_node, atot12494, atot12495]
  decide +kernel

theorem arows12500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12500 = true := by
  rw [show D2M8K2.u12500 = KTree.node D2M8K2.u12498 (nat_lit 26962773) (nat_lit 1094904733) (nat_lit 0) D2M8K2.u12499 from rfl, allE_node, arows12498, irow12500, arows12499]
  all_goals rfl

theorem atot12500 : totK PD2M8K2 D2M8K2.u12500 = [0, 434321523916, 1406783402093, 1371407053821, 414149451976, 16504275017, 0, 0] := by
  rw [show D2M8K2.u12500 = KTree.node D2M8K2.u12498 (nat_lit 26962773) (nat_lit 1094904733) (nat_lit 0) D2M8K2.u12499 from rfl, totK_node, atot12498, atot12499]
  decide +kernel

theorem arows12503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12503 = true := by
  rw [show D2M8K2.u12503 = KTree.node D2M8K2.u12501 (nat_lit 26966049) (nat_lit 1792849343) (nat_lit 0) D2M8K2.u12502 from rfl, allE_node, arows12501, irow12503, arows12502]
  all_goals rfl

theorem atot12503 : totK PD2M8K2 D2M8K2.u12503 = [0, 356812940153, 1421476487389, 1460008099915, 330243757379, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12503 = KTree.node D2M8K2.u12501 (nat_lit 26966049) (nat_lit 1792849343) (nat_lit 0) D2M8K2.u12502 from rfl, totK_node, atot12501, atot12502]
  decide +kernel

theorem arows12509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12509 = true := by
  rw [show D2M8K2.u12509 = KTree.node D2M8K2.u12507 (nat_lit 26972757) (nat_lit 1716944964) (nat_lit 0) D2M8K2.u12508 from rfl, allE_node, arows12507, irow12509, arows12508]
  all_goals rfl

theorem atot12509 : totK PD2M8K2 D2M8K2.u12509 = [0, 468248499741, 1530842527237, 1357639317745, 244637240215, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12509 = KTree.node D2M8K2.u12507 (nat_lit 26972757) (nat_lit 1716944964) (nat_lit 0) D2M8K2.u12508 from rfl, totK_node, atot12507, atot12508]
  decide +kernel

theorem arows12512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12512 = true := by
  rw [show D2M8K2.u12512 = KTree.node D2M8K2.u12510 (nat_lit 26976522) (nat_lit 3184986197) (nat_lit 0) D2M8K2.u12511 from rfl, allE_node, arows12510, irow12512, arows12511]
  all_goals rfl

theorem atot12512 : totK PD2M8K2 D2M8K2.u12512 = [0, 162053559089, 1125189550092, 1720550144118, 537934453690, 23790446230, 0, 0] := by
  rw [show D2M8K2.u12512 = KTree.node D2M8K2.u12510 (nat_lit 26976522) (nat_lit 3184986197) (nat_lit 0) D2M8K2.u12511 from rfl, totK_node, atot12510, atot12511]
  decide +kernel

theorem arows12516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12516 = true := by
  rw [show D2M8K2.u12516 = KTree.node D2M8K2.u12514 (nat_lit 26980467) (nat_lit 2982970924) (nat_lit 0) D2M8K2.u12515 from rfl, allE_node, arows12514, irow12516, arows12515]
  all_goals rfl

theorem atot12516 : totK PD2M8K2 D2M8K2.u12516 = [0, 0, 498247570094, 1680374408411, 1205039375499, 131772137824, 1206465782, 0] := by
  rw [show D2M8K2.u12516 = KTree.node D2M8K2.u12514 (nat_lit 26980467) (nat_lit 2982970924) (nat_lit 0) D2M8K2.u12515 from rfl, totK_node, atot12514, atot12515]
  decide +kernel

theorem arows12519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12519 = true := by
  rw [show D2M8K2.u12519 = KTree.node D2M8K2.u12517 (nat_lit 26985901) (nat_lit 1371196557) (nat_lit 0) D2M8K2.u12518 from rfl, allE_node, arows12517, irow12519, arows12518]
  all_goals rfl

theorem atot12519 : totK PD2M8K2 D2M8K2.u12519 = [0, 0, 435354056993, 1507864350573, 1276486185117, 277458540159, 13016197374, 0] := by
  rw [show D2M8K2.u12519 = KTree.node D2M8K2.u12517 (nat_lit 26985901) (nat_lit 1371196557) (nat_lit 0) D2M8K2.u12518 from rfl, totK_node, atot12517, atot12518]
  decide +kernel

theorem arows12524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12524 = true := by
  rw [show D2M8K2.u12524 = KTree.node D2M8K2.u12522 (nat_lit 26992554) (nat_lit 3523051679) (nat_lit 0) D2M8K2.u12523 from rfl, allE_node, arows12522, irow12524, arows12523]
  all_goals rfl

theorem atot12524 : totK PD2M8K2 D2M8K2.u12524 = [0, 0, 469111820476, 1589810556230, 1249290811117, 185064647224, 4574395652, 0] := by
  rw [show D2M8K2.u12524 = KTree.node D2M8K2.u12522 (nat_lit 26992554) (nat_lit 3523051679) (nat_lit 0) D2M8K2.u12523 from rfl, totK_node, atot12522, atot12523]
  decide +kernel

theorem arows12527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12527 = true := by
  rw [show D2M8K2.u12527 = KTree.node D2M8K2.u12525 (nat_lit 26998363) (nat_lit 2238932575) (nat_lit 0) D2M8K2.u12526 from rfl, allE_node, arows12525, irow12527, arows12526]
  all_goals rfl

theorem atot12527 : totK PD2M8K2 D2M8K2.u12527 = [0, 419052346373, 1341611543076, 1350221111743, 455422611405, 19884808526, 0, 0] := by
  rw [show D2M8K2.u12527 = KTree.node D2M8K2.u12525 (nat_lit 26998363) (nat_lit 2238932575) (nat_lit 0) D2M8K2.u12526 from rfl, totK_node, atot12525, atot12526]
  decide +kernel

theorem arows12531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12531 = true := by
  rw [show D2M8K2.u12531 = KTree.node D2M8K2.u12529 (nat_lit 27002261) (nat_lit 2158987495) (nat_lit 0) D2M8K2.u12530 from rfl, allE_node, arows12529, irow12531, arows12530]
  all_goals rfl

theorem atot12531 : totK PD2M8K2 D2M8K2.u12531 = [0, 331084880840, 1454848466690, 1540137058731, 320740736271, 11346202446, 0, 0] := by
  rw [show D2M8K2.u12531 = KTree.node D2M8K2.u12529 (nat_lit 27002261) (nat_lit 2158987495) (nat_lit 0) D2M8K2.u12530 from rfl, totK_node, atot12529, atot12530]
  decide +kernel

theorem arows12534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12534 = true := by
  rw [show D2M8K2.u12534 = KTree.node D2M8K2.u12532 (nat_lit 27009208) (nat_lit 2557937237) (nat_lit 0) D2M8K2.u12533 from rfl, allE_node, arows12532, irow12534, arows12533]
  all_goals rfl

theorem atot12534 : totK PD2M8K2 D2M8K2.u12534 = [0, 437683919179, 1431315931141, 1384075192516, 355284352625, 7816175670, 0, 0] := by
  rw [show D2M8K2.u12534 = KTree.node D2M8K2.u12532 (nat_lit 27009208) (nat_lit 2557937237) (nat_lit 0) D2M8K2.u12533 from rfl, totK_node, atot12532, atot12533]
  decide +kernel

theorem arows12543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12543 = true := by
  rw [show D2M8K2.u12543 = KTree.node D2M8K2.u12541 (nat_lit 27012500) (nat_lit 3684646199) (nat_lit 0) D2M8K2.u12542 from rfl, allE_node, arows12541, irow12543, arows12542]
  all_goals rfl

theorem atot12543 : totK PD2M8K2 D2M8K2.u12543 = [0, 412219636167, 1445734783160, 1387809278955, 316105597206, 13149116973, 0, 0] := by
  rw [show D2M8K2.u12543 = KTree.node D2M8K2.u12541 (nat_lit 27012500) (nat_lit 3684646199) (nat_lit 0) D2M8K2.u12542 from rfl, totK_node, atot12541, atot12542]
  decide +kernel

theorem arows12546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12546 = true := by
  rw [show D2M8K2.u12546 = KTree.node D2M8K2.u12544 (nat_lit 27016108) (nat_lit 3310724644) (nat_lit 0) D2M8K2.u12545 from rfl, allE_node, arows12544, irow12546, arows12545]
  all_goals rfl

theorem atot12546 : totK PD2M8K2 D2M8K2.u12546 = [0, 383209705629, 1468003013163, 1468309656820, 288057019575, 5152749158, 0, 0] := by
  rw [show D2M8K2.u12546 = KTree.node D2M8K2.u12544 (nat_lit 27016108) (nat_lit 3310724644) (nat_lit 0) D2M8K2.u12545 from rfl, totK_node, atot12544, atot12545]
  decide +kernel

theorem arows12550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12550 = true := by
  rw [show D2M8K2.u12550 = KTree.node D2M8K2.u12548 (nat_lit 27019952) (nat_lit 3745749002) (nat_lit 0) D2M8K2.u12549 from rfl, allE_node, arows12548, irow12550, arows12549]
  all_goals rfl

theorem atot12550 : totK PD2M8K2 D2M8K2.u12550 = [0, 0, 634282741994, 1764355938059, 1000772891375, 103007799885, 1239866073, 0] := by
  rw [show D2M8K2.u12550 = KTree.node D2M8K2.u12548 (nat_lit 27019952) (nat_lit 3745749002) (nat_lit 0) D2M8K2.u12549 from rfl, totK_node, atot12548, atot12549]
  decide +kernel

theorem arows12553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12553 = true := by
  rw [show D2M8K2.u12553 = KTree.node D2M8K2.u12551 (nat_lit 27023908) (nat_lit 2195438576) (nat_lit 0) D2M8K2.u12552 from rfl, allE_node, arows12551, irow12553, arows12552]
  all_goals rfl

theorem atot12553 : totK PD2M8K2 D2M8K2.u12553 = [0, 0, 671950646894, 1839740928215, 1044133859448, 77365676216, 0, 0] := by
  rw [show D2M8K2.u12553 = KTree.node D2M8K2.u12551 (nat_lit 27023908) (nat_lit 2195438576) (nat_lit 0) D2M8K2.u12552 from rfl, totK_node, atot12551, atot12552]
  decide +kernel

theorem arows12558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12558 = true := by
  rw [show D2M8K2.u12558 = KTree.node D2M8K2.u12556 (nat_lit 27032350) (nat_lit 3063323388) (nat_lit 0) D2M8K2.u12557 from rfl, allE_node, arows12556, irow12558, arows12557]
  all_goals rfl

theorem atot12558 : totK PD2M8K2 D2M8K2.u12558 = [0, 0, 409534056629, 1489318629261, 1306149973670, 282689955973, 13105450397, 0] := by
  rw [show D2M8K2.u12558 = KTree.node D2M8K2.u12556 (nat_lit 27032350) (nat_lit 3063323388) (nat_lit 0) D2M8K2.u12557 from rfl, totK_node, atot12556, atot12557]
  decide +kernel

theorem arows12561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12561 = true := by
  rw [show D2M8K2.u12561 = KTree.node D2M8K2.u12559 (nat_lit 27035889) (nat_lit 1502131574) (nat_lit 0) D2M8K2.u12560 from rfl, allE_node, arows12559, irow12561, arows12560]
  all_goals rfl

theorem atot12561 : totK PD2M8K2 D2M8K2.u12561 = [0, 0, 472263582476, 1616452656319, 1247969116628, 179229952248, 4720618446, 0] := by
  rw [show D2M8K2.u12561 = KTree.node D2M8K2.u12559 (nat_lit 27035889) (nat_lit 1502131574) (nat_lit 0) D2M8K2.u12560 from rfl, totK_node, atot12559, atot12560]
  decide +kernel

theorem arows12565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12565 = true := by
  rw [show D2M8K2.u12565 = KTree.node D2M8K2.u12563 (nat_lit 27041157) (nat_lit 1726111067) (nat_lit 0) D2M8K2.u12564 from rfl, allE_node, arows12563, irow12565, arows12564]
  all_goals rfl

theorem atot12565 : totK PD2M8K2 D2M8K2.u12565 = [0, 470128640742, 1557867222850, 1327189633637, 235115002131, 9292170540, 0, 0] := by
  rw [show D2M8K2.u12565 = KTree.node D2M8K2.u12563 (nat_lit 27041157) (nat_lit 1726111067) (nat_lit 0) D2M8K2.u12564 from rfl, totK_node, atot12563, atot12564]
  decide +kernel

theorem arows12568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12568 = true := by
  rw [show D2M8K2.u12568 = KTree.node D2M8K2.u12566 (nat_lit 27045343) (nat_lit 2002183441) (nat_lit 2) D2M8K2.u12567 from rfl, allE_node, arows12566, irow12568, arows12567]
  all_goals rfl

theorem atot12568 : totK PD2M8K2 D2M8K2.u12568 = [0, 378803729905, 1372574549743, 1398434624289, 446998663639, 24128189171, 0, 0] := by
  rw [show D2M8K2.u12568 = KTree.node D2M8K2.u12566 (nat_lit 27045343) (nat_lit 2002183441) (nat_lit 2) D2M8K2.u12567 from rfl, totK_node, atot12566, atot12567]
  decide +kernel

theorem arows12574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12574 = true := by
  rw [show D2M8K2.u12574 = KTree.node D2M8K2.u12572 (nat_lit 27048474) (nat_lit 3372879031) (nat_lit 0) D2M8K2.u12573 from rfl, allE_node, arows12572, irow12574, arows12573]
  all_goals rfl

theorem atot12574 : totK PD2M8K2 D2M8K2.u12574 = [0, 411884627477, 1415864812955, 1405096679074, 324873337645, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12574 = KTree.node D2M8K2.u12572 (nat_lit 27048474) (nat_lit 3372879031) (nat_lit 0) D2M8K2.u12573 from rfl, totK_node, atot12572, atot12573]
  decide +kernel

theorem arows12577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12577 = true := by
  rw [show D2M8K2.u12577 = KTree.node D2M8K2.u12575 (nat_lit 27051897) (nat_lit 1721021997) (nat_lit 0) D2M8K2.u12576 from rfl, allE_node, arows12575, irow12577, arows12576]
  all_goals rfl

theorem atot12577 : totK PD2M8K2 D2M8K2.u12577 = [0, 413544762226, 1421239745416, 1396130280645, 334998884930, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12577 = KTree.node D2M8K2.u12575 (nat_lit 27051897) (nat_lit 1721021997) (nat_lit 0) D2M8K2.u12576 from rfl, totK_node, atot12575, atot12576]
  decide +kernel

theorem arows12581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12581 = true := by
  rw [show D2M8K2.u12581 = KTree.node D2M8K2.u12579 (nat_lit 27054896) (nat_lit 3813571117) (nat_lit 0) D2M8K2.u12580 from rfl, allE_node, arows12579, irow12581, arows12580]
  all_goals rfl

theorem atot12581 : totK PD2M8K2 D2M8K2.u12581 = [0, 352446817612, 1510414927392, 1512611091045, 259336787813, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12581 = KTree.node D2M8K2.u12579 (nat_lit 27054896) (nat_lit 3813571117) (nat_lit 0) D2M8K2.u12580 from rfl, totK_node, atot12579, atot12580]
  decide +kernel

theorem arows12584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12584 = true := by
  rw [show D2M8K2.u12584 = KTree.node D2M8K2.u12582 (nat_lit 27062217) (nat_lit 1819679931) (nat_lit 0) D2M8K2.u12583 from rfl, allE_node, arows12582, irow12584, arows12583]
  all_goals rfl

theorem atot12584 : totK PD2M8K2 D2M8K2.u12584 = [0, 0, 502522482228, 1717940808826, 1176809254638, 126262649274, 1138244013, 0] := by
  rw [show D2M8K2.u12584 = KTree.node D2M8K2.u12582 (nat_lit 27062217) (nat_lit 1819679931) (nat_lit 0) D2M8K2.u12583 from rfl, totK_node, atot12582, atot12583]
  decide +kernel

theorem arows12589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12589 = true := by
  rw [show D2M8K2.u12589 = KTree.node D2M8K2.u12587 (nat_lit 27067998) (nat_lit 2907846197) (nat_lit 0) D2M8K2.u12588 from rfl, allE_node, arows12587, irow12589, arows12588]
  all_goals rfl

theorem atot12589 : totK PD2M8K2 D2M8K2.u12589 = [0, 0, 747038845530, 1905904699622, 867512775971, 50026961051, 0, 0] := by
  rw [show D2M8K2.u12589 = KTree.node D2M8K2.u12587 (nat_lit 27067998) (nat_lit 2907846197) (nat_lit 0) D2M8K2.u12588 from rfl, totK_node, atot12587, atot12588]
  decide +kernel

theorem arows12592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12592 = true := by
  rw [show D2M8K2.u12592 = KTree.node D2M8K2.u12590 (nat_lit 27074651) (nat_lit 2280037341) (nat_lit 0) D2M8K2.u12591 from rfl, allE_node, arows12590, irow12592, arows12591]
  all_goals rfl

theorem atot12592 : totK PD2M8K2 D2M8K2.u12592 = [0, 0, 682100227909, 1845431262030, 973241027207, 66189810174, 0, 0] := by
  rw [show D2M8K2.u12592 = KTree.node D2M8K2.u12590 (nat_lit 27074651) (nat_lit 2280037341) (nat_lit 0) D2M8K2.u12591 from rfl, totK_node, atot12590, atot12591]
  decide +kernel

theorem arows12596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12596 = true := by
  rw [show D2M8K2.u12596 = KTree.node D2M8K2.u12594 (nat_lit 27081853) (nat_lit 1224524169) (nat_lit 0) D2M8K2.u12595 from rfl, allE_node, arows12594, irow12596, arows12595]
  all_goals rfl

theorem atot12596 : totK PD2M8K2 D2M8K2.u12596 = [0, 421327836975, 1165140487855, 1046485544519, 729639618247, 177535119139, 4977114383, 0] := by
  rw [show D2M8K2.u12596 = KTree.node D2M8K2.u12594 (nat_lit 27081853) (nat_lit 1224524169) (nat_lit 0) D2M8K2.u12595 from rfl, totK_node, atot12594, atot12595]
  decide +kernel

theorem arows12599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12599 = true := by
  rw [show D2M8K2.u12599 = KTree.node D2M8K2.u12597 (nat_lit 27088699) (nat_lit 1081243724) (nat_lit 0) D2M8K2.u12598 from rfl, allE_node, arows12597, irow12599, arows12598]
  all_goals rfl

theorem atot12599 : totK PD2M8K2 D2M8K2.u12599 = [0, 401301423914, 1506563955709, 1454293983494, 240095320420, 2533470052, 0, 0] := by
  rw [show D2M8K2.u12599 = KTree.node D2M8K2.u12597 (nat_lit 27088699) (nat_lit 1081243724) (nat_lit 0) D2M8K2.u12598 from rfl, totK_node, atot12597, atot12598]
  decide +kernel

theorem arows12606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12606 = true := by
  rw [show D2M8K2.u12606 = KTree.node D2M8K2.u12604 (nat_lit 27092557) (nat_lit 1107400397) (nat_lit 0) D2M8K2.u12605 from rfl, allE_node, arows12604, irow12606, arows12605]
  all_goals rfl

theorem atot12606 : totK PD2M8K2 D2M8K2.u12606 = [0, 401552586407, 1497658962104, 1433364452060, 271259260255, 5432584078, 0, 0] := by
  rw [show D2M8K2.u12606 = KTree.node D2M8K2.u12604 (nat_lit 27092557) (nat_lit 1107400397) (nat_lit 0) D2M8K2.u12605 from rfl, totK_node, atot12604, atot12605]
  decide +kernel

theorem arows12609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12609 = true := by
  rw [show D2M8K2.u12609 = KTree.node D2M8K2.u12607 (nat_lit 27099273) (nat_lit 1688692546) (nat_lit 0) D2M8K2.u12608 from rfl, allE_node, arows12607, irow12609, arows12608]
  all_goals rfl

theorem atot12609 : totK PD2M8K2 D2M8K2.u12609 = [0, 427832996020, 1508768631339, 1411307921806, 270028720994, 5526313451, 0, 0] := by
  rw [show D2M8K2.u12609 = KTree.node D2M8K2.u12607 (nat_lit 27099273) (nat_lit 1688692546) (nat_lit 0) D2M8K2.u12608 from rfl, totK_node, atot12607, atot12608]
  decide +kernel

theorem arows12613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12613 = true := by
  rw [show D2M8K2.u12613 = KTree.node D2M8K2.u12611 (nat_lit 27102730) (nat_lit 3911115837) (nat_lit 0) D2M8K2.u12612 from rfl, allE_node, arows12611, irow12613, arows12612]
  all_goals rfl

theorem atot12613 : totK PD2M8K2 D2M8K2.u12613 = [0, 0, 602428197521, 1765704396259, 1027167798134, 111222935661, 1310285577, 0] := by
  rw [show D2M8K2.u12613 = KTree.node D2M8K2.u12611 (nat_lit 27102730) (nat_lit 3911115837) (nat_lit 0) D2M8K2.u12612 from rfl, totK_node, atot12611, atot12612]
  decide +kernel

theorem arows12616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12616 = true := by
  rw [show D2M8K2.u12616 = KTree.node D2M8K2.u12614 (nat_lit 27109692) (nat_lit 2716669210) (nat_lit 0) D2M8K2.u12615 from rfl, allE_node, arows12614, irow12616, arows12615]
  all_goals rfl

theorem atot12616 : totK PD2M8K2 D2M8K2.u12616 = [0, 0, 644690159115, 1818712547180, 1038362084713, 67145917829, 0, 0] := by
  rw [show D2M8K2.u12616 = KTree.node D2M8K2.u12614 (nat_lit 27109692) (nat_lit 2716669210) (nat_lit 0) D2M8K2.u12615 from rfl, totK_node, atot12614, atot12615]
  decide +kernel

theorem arows12621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12621 = true := by
  rw [show D2M8K2.u12621 = KTree.node D2M8K2.u12619 (nat_lit 27119852) (nat_lit 2688987053) (nat_lit 0) D2M8K2.u12620 from rfl, allE_node, arows12619, irow12621, arows12620]
  all_goals rfl

theorem atot12621 : totK PD2M8K2 D2M8K2.u12621 = [0, 0, 741327852205, 1900065926033, 917120485006, 53550723178, 0, 0] := by
  rw [show D2M8K2.u12621 = KTree.node D2M8K2.u12619 (nat_lit 27119852) (nat_lit 2688987053) (nat_lit 0) D2M8K2.u12620 from rfl, totK_node, atot12619, atot12620]
  decide +kernel

theorem arows12624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12624 = true := by
  rw [show D2M8K2.u12624 = KTree.node D2M8K2.u12622 (nat_lit 27124561) (nat_lit 1558578335) (nat_lit 0) D2M8K2.u12623 from rfl, allE_node, arows12622, irow12624, arows12623]
  all_goals rfl

theorem atot12624 : totK PD2M8K2 D2M8K2.u12624 = [0, 0, 457630986030, 1599137176859, 1342546959283, 178531413278, 1369150432, 0] := by
  rw [show D2M8K2.u12624 = KTree.node D2M8K2.u12622 (nat_lit 27124561) (nat_lit 1558578335) (nat_lit 0) D2M8K2.u12623 from rfl, totK_node, atot12622, atot12623]
  decide +kernel

theorem arows12628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12628 = true := by
  rw [show D2M8K2.u12628 = KTree.node D2M8K2.u12626 (nat_lit 27131935) (nat_lit 998729329) (nat_lit 0) D2M8K2.u12627 from rfl, allE_node, arows12626, irow12628, arows12627]
  all_goals rfl

theorem atot12628 : totK PD2M8K2 D2M8K2.u12628 = [0, 0, 446347246371, 1469151323162, 1307797758858, 263231542171, 12891658009, 0] := by
  rw [show D2M8K2.u12628 = KTree.node D2M8K2.u12626 (nat_lit 27131935) (nat_lit 998729329) (nat_lit 0) D2M8K2.u12627 from rfl, totK_node, atot12626, atot12627]
  decide +kernel

theorem arows12631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12631 = true := by
  rw [show D2M8K2.u12631 = KTree.node D2M8K2.u12629 (nat_lit 27135752) (nat_lit 3890540344) (nat_lit 0) D2M8K2.u12630 from rfl, allE_node, arows12629, irow12631, arows12630]
  all_goals rfl

theorem atot12631 : totK PD2M8K2 D2M8K2.u12631 = [0, 0, 410833796104, 1456861623308, 1335614685634, 273780039056, 13092379805, 0] := by
  rw [show D2M8K2.u12631 = KTree.node D2M8K2.u12629 (nat_lit 27135752) (nat_lit 3890540344) (nat_lit 0) D2M8K2.u12630 from rfl, totK_node, atot12629, atot12630]
  decide +kernel

theorem arows12637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12637 = true := by
  rw [show D2M8K2.u12637 = KTree.node D2M8K2.u12635 (nat_lit 27138920) (nat_lit 3906797986) (nat_lit 0) D2M8K2.u12636 from rfl, allE_node, arows12635, irow12637, arows12636]
  all_goals rfl

theorem atot12637 : totK PD2M8K2 D2M8K2.u12637 = [0, 0, 462407231471, 1538445689483, 1311429000951, 203347378358, 4934531535, 0] := by
  rw [show D2M8K2.u12637 = KTree.node D2M8K2.u12635 (nat_lit 27138920) (nat_lit 3906797986) (nat_lit 0) D2M8K2.u12636 from rfl, totK_node, atot12635, atot12636]
  decide +kernel

theorem arows12640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12640 = true := by
  rw [show D2M8K2.u12640 = KTree.node D2M8K2.u12638 (nat_lit 27143275) (nat_lit 1603155513) (nat_lit 0) D2M8K2.u12639 from rfl, allE_node, arows12638, irow12640, arows12639]
  all_goals rfl

theorem atot12640 : totK PD2M8K2 D2M8K2.u12640 = [0, 0, 116791540598, 1154547186244, 1746454170222, 495911207226, 23085800530, 0] := by
  rw [show D2M8K2.u12640 = KTree.node D2M8K2.u12638 (nat_lit 27143275) (nat_lit 1603155513) (nat_lit 0) D2M8K2.u12639 from rfl, totK_node, atot12638, atot12639]
  decide +kernel

theorem arows12644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12644 = true := by
  rw [show D2M8K2.u12644 = KTree.node D2M8K2.u12642 (nat_lit 27150750) (nat_lit 782689075) (nat_lit 2176) D2M8K2.u12643 from rfl, allE_node, arows12642, irow12644, arows12643]
  all_goals rfl

theorem atot12644 : totK PD2M8K2 D2M8K2.u12644 = [0, 0, 0, 661597999663, 1780162183009, 948727006707, 104197440090, 1369150432] := by
  rw [show D2M8K2.u12644 = KTree.node D2M8K2.u12642 (nat_lit 27150750) (nat_lit 782689075) (nat_lit 2176) D2M8K2.u12643 from rfl, totK_node, atot12642, atot12643]
  decide +kernel

theorem arows12647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12647 = true := by
  rw [show D2M8K2.u12647 = KTree.node D2M8K2.u12645 (nat_lit 27158144) (nat_lit 3737620229) (nat_lit 0) D2M8K2.u12646 from rfl, allE_node, arows12645, irow12647, arows12646]
  all_goals rfl

theorem atot12647 : totK PD2M8K2 D2M8K2.u12647 = [0, 0, 0, 935654296974, 1903890860598, 622112395503, 35380421762, 0] := by
  rw [show D2M8K2.u12647 = KTree.node D2M8K2.u12645 (nat_lit 27158144) (nat_lit 3737620229) (nat_lit 0) D2M8K2.u12646 from rfl, totK_node, atot12645, atot12646]
  decide +kernel

theorem arows12652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12652 = true := by
  rw [show D2M8K2.u12652 = KTree.node D2M8K2.u12650 (nat_lit 27207146) (nat_lit 784898000) (nat_lit 2208) D2M8K2.u12651 from rfl, allE_node, arows12650, irow12652, arows12651]
  all_goals rfl

theorem atot12652 : totK PD2M8K2 D2M8K2.u12652 = [0, 0, 501736306450, 1617918971457, 1257646556812, 164238325402, 1369150432, 0] := by
  rw [show D2M8K2.u12652 = KTree.node D2M8K2.u12650 (nat_lit 27207146) (nat_lit 784898000) (nat_lit 2208) D2M8K2.u12651 from rfl, totK_node, atot12650, atot12651]
  decide +kernel

theorem arows12655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12655 = true := by
  rw [show D2M8K2.u12655 = KTree.node D2M8K2.u12653 (nat_lit 27212885) (nat_lit 2388047705) (nat_lit 0) D2M8K2.u12654 from rfl, allE_node, arows12653, irow12655, arows12654]
  all_goals rfl

theorem atot12655 : totK PD2M8K2 D2M8K2.u12655 = [0, 0, 676223914691, 1855088490719, 1033623422454, 70849047734, 0, 0] := by
  rw [show D2M8K2.u12655 = KTree.node D2M8K2.u12653 (nat_lit 27212885) (nat_lit 2388047705) (nat_lit 0) D2M8K2.u12654 from rfl, totK_node, atot12653, atot12654]
  decide +kernel

theorem arows12659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12659 = true := by
  rw [show D2M8K2.u12659 = KTree.node D2M8K2.u12657 (nat_lit 27219698) (nat_lit 3252316073) (nat_lit 0) D2M8K2.u12658 from rfl, allE_node, arows12657, irow12659, arows12658]
  all_goals rfl

theorem atot12659 : totK PD2M8K2 D2M8K2.u12659 = [0, 0, 410132952639, 1470679396073, 1364388090320, 292242605300, 13049727234, 0] := by
  rw [show D2M8K2.u12659 = KTree.node D2M8K2.u12657 (nat_lit 27219698) (nat_lit 3252316073) (nat_lit 0) D2M8K2.u12658 from rfl, totK_node, atot12657, atot12658]
  decide +kernel

theorem arows12662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12662 = true := by
  rw [show D2M8K2.u12662 = KTree.node D2M8K2.u12660 (nat_lit 27223331) (nat_lit 2970155676) (nat_lit 0) D2M8K2.u12661 from rfl, allE_node, arows12660, irow12662, arows12661]
  all_goals rfl

theorem atot12662 : totK PD2M8K2 D2M8K2.u12662 = [0, 0, 538790627106, 1590540573475, 1240229907025, 199631225278, 4917269347, 0] := by
  rw [show D2M8K2.u12662 = KTree.node D2M8K2.u12660 (nat_lit 27223331) (nat_lit 2970155676) (nat_lit 0) D2M8K2.u12661 from rfl, totK_node, atot12660, atot12661]
  decide +kernel

theorem arows12670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12670 = true := by
  rw [show D2M8K2.u12670 = KTree.node D2M8K2.u12668 (nat_lit 27249412) (nat_lit 3817884147) (nat_lit 0) D2M8K2.u12669 from rfl, allE_node, arows12668, irow12670, arows12669]
  all_goals rfl

theorem atot12670 : totK PD2M8K2 D2M8K2.u12670 = [0, 0, 464854120679, 1596822210814, 1337970312958, 173092844631, 1369150432, 0] := by
  rw [show D2M8K2.u12670 = KTree.node D2M8K2.u12668 (nat_lit 27249412) (nat_lit 3817884147) (nat_lit 0) D2M8K2.u12669 from rfl, totK_node, atot12668, atot12669]
  decide +kernel

theorem arows12673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12673 = true := by
  rw [show D2M8K2.u12673 = KTree.node D2M8K2.u12671 (nat_lit 27258512) (nat_lit 3678724111) (nat_lit 0) D2M8K2.u12672 from rfl, allE_node, arows12671, irow12673, arows12672]
  all_goals rfl

theorem atot12673 : totK PD2M8K2 D2M8K2.u12673 = [0, 0, 555490888562, 1719635706007, 1209374413356, 141774950395, 1178750802, 0] := by
  rw [show D2M8K2.u12673 = KTree.node D2M8K2.u12671 (nat_lit 27258512) (nat_lit 3678724111) (nat_lit 0) D2M8K2.u12672 from rfl, totK_node, atot12671, atot12672]
  decide +kernel

theorem arows12677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12677 = true := by
  rw [show D2M8K2.u12677 = KTree.node D2M8K2.u12675 (nat_lit 27261675) (nat_lit 3238937212) (nat_lit 2048) D2M8K2.u12676 from rfl, allE_node, arows12675, irow12677, arows12676]
  all_goals rfl

theorem atot12677 : totK PD2M8K2 D2M8K2.u12677 = [0, 0, 410185915290, 1473649626404, 1371372204737, 279301694647, 13088430220, 0] := by
  rw [show D2M8K2.u12677 = KTree.node D2M8K2.u12675 (nat_lit 27261675) (nat_lit 3238937212) (nat_lit 2048) D2M8K2.u12676 from rfl, totK_node, atot12675, atot12676]
  decide +kernel

theorem arows12680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12680 = true := by
  rw [show D2M8K2.u12680 = KTree.node D2M8K2.u12678 (nat_lit 27265523) (nat_lit 2946963925) (nat_lit 0) D2M8K2.u12679 from rfl, allE_node, arows12678, irow12680, arows12679]
  all_goals rfl

theorem atot12680 : totK PD2M8K2 D2M8K2.u12680 = [0, 0, 671347198286, 1727620547067, 1046806764645, 138230705626, 3821179711, 0] := by
  rw [show D2M8K2.u12680 = KTree.node D2M8K2.u12678 (nat_lit 27265523) (nat_lit 2946963925) (nat_lit 0) D2M8K2.u12679 from rfl, totK_node, atot12678, atot12679]
  decide +kernel

theorem arows12685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12685 = true := by
  rw [show D2M8K2.u12685 = KTree.node D2M8K2.u12683 (nat_lit 27291752) (nat_lit 2695781702) (nat_lit 0) D2M8K2.u12684 from rfl, allE_node, arows12683, irow12685, arows12684]
  all_goals rfl

theorem atot12685 : totK PD2M8K2 D2M8K2.u12685 = [0, 0, 464084909458, 1594688940091, 1327697630715, 167573052606, 1369150432, 0] := by
  rw [show D2M8K2.u12685 = KTree.node D2M8K2.u12683 (nat_lit 27291752) (nat_lit 2695781702) (nat_lit 0) D2M8K2.u12684 from rfl, totK_node, atot12683, atot12684]
  decide +kernel

theorem arows12688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12688 = true := by
  rw [show D2M8K2.u12688 = KTree.node D2M8K2.u12686 (nat_lit 27296016) (nat_lit 2619112551) (nat_lit 0) D2M8K2.u12687 from rfl, allE_node, arows12686, irow12688, arows12687]
  all_goals rfl

theorem atot12688 : totK PD2M8K2 D2M8K2.u12688 = [0, 0, 407593598042, 1539255516688, 1410052850548, 223732649334, 2573880433, 0] := by
  rw [show D2M8K2.u12688 = KTree.node D2M8K2.u12686 (nat_lit 27296016) (nat_lit 2619112551) (nat_lit 0) D2M8K2.u12687 from rfl, totK_node, atot12686, atot12687]
  decide +kernel

theorem arows12692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12692 = true := by
  rw [show D2M8K2.u12692 = KTree.node D2M8K2.u12690 (nat_lit 27299836) (nat_lit 2930172823) (nat_lit 0) D2M8K2.u12691 from rfl, allE_node, arows12690, irow12692, arows12691]
  all_goals rfl

theorem atot12692 : totK PD2M8K2 D2M8K2.u12692 = [0, 0, 407821975529, 1448811512805, 1390960584576, 284416978914, 13017203568, 0] := by
  rw [show D2M8K2.u12692 = KTree.node D2M8K2.u12690 (nat_lit 27299836) (nat_lit 2930172823) (nat_lit 0) D2M8K2.u12691 from rfl, totK_node, atot12690, atot12691]
  decide +kernel

theorem arows12695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12695 = true := by
  rw [show D2M8K2.u12695 = KTree.node D2M8K2.u12693 (nat_lit 27303044) (nat_lit 3378615208) (nat_lit 0) D2M8K2.u12694 from rfl, allE_node, arows12693, irow12695, arows12694]
  all_goals rfl

theorem atot12695 : totK PD2M8K2 D2M8K2.u12695 = [0, 0, 436573213801, 1497472658637, 1349819456327, 276580506362, 13082749112, 0] := by
  rw [show D2M8K2.u12695 = KTree.node D2M8K2.u12693 (nat_lit 27303044) (nat_lit 3378615208) (nat_lit 0) D2M8K2.u12694 from rfl, totK_node, atot12693, atot12694]
  decide +kernel

theorem arows12701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12701 = true := by
  rw [show D2M8K2.u12701 = KTree.node D2M8K2.u12699 (nat_lit 27331021) (nat_lit 1117046934) (nat_lit 0) D2M8K2.u12700 from rfl, allE_node, arows12699, irow12701, arows12700]
  all_goals rfl

theorem atot12701 : totK PD2M8K2 D2M8K2.u12701 = [0, 0, 415337461602, 1511716774814, 1360985437906, 240111133139, 5253160287, 0] := by
  rw [show D2M8K2.u12701 = KTree.node D2M8K2.u12699 (nat_lit 27331021) (nat_lit 1117046934) (nat_lit 0) D2M8K2.u12700 from rfl, totK_node, atot12699, atot12700]
  decide +kernel

theorem arows12704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12704 = true := by
  rw [show D2M8K2.u12704 = KTree.node D2M8K2.u12702 (nat_lit 27338220) (nat_lit 3125310385) (nat_lit 0) D2M8K2.u12703 from rfl, allE_node, arows12702, irow12704, arows12703]
  all_goals rfl

theorem atot12704 : totK PD2M8K2 D2M8K2.u12704 = [0, 0, 710917890947, 1821277857398, 1005468682014, 74890761499, 0, 0] := by
  rw [show D2M8K2.u12704 = KTree.node D2M8K2.u12702 (nat_lit 27338220) (nat_lit 3125310385) (nat_lit 0) D2M8K2.u12703 from rfl, totK_node, atot12702, atot12703]
  decide +kernel

theorem arows12708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12708 = true := by
  rw [show D2M8K2.u12708 = KTree.node D2M8K2.u12706 (nat_lit 27348301) (nat_lit 1084498368) (nat_lit 0) D2M8K2.u12707 from rfl, allE_node, arows12706, irow12708, arows12707]
  all_goals rfl

theorem atot12708 : totK PD2M8K2 D2M8K2.u12708 = [0, 242922008643, 1066842003953, 1623043336029, 707428656072, 45200247724, 0, 0] := by
  rw [show D2M8K2.u12708 = KTree.node D2M8K2.u12706 (nat_lit 27348301) (nat_lit 1084498368) (nat_lit 0) D2M8K2.u12707 from rfl, totK_node, atot12706, atot12707]
  decide +kernel

theorem arows12711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12711 = true := by
  rw [show D2M8K2.u12711 = KTree.node D2M8K2.u12709 (nat_lit 27418849) (nat_lit 1311156805) (nat_lit 0) D2M8K2.u12710 from rfl, allE_node, arows12709, irow12711, arows12710]
  all_goals rfl

theorem atot12711 : totK PD2M8K2 D2M8K2.u12711 = [0, 272303536113, 1205083067650, 1528692635658, 585951705116, 37609398105, 0, 0] := by
  rw [show D2M8K2.u12711 = KTree.node D2M8K2.u12709 (nat_lit 27418849) (nat_lit 1311156805) (nat_lit 0) D2M8K2.u12710 from rfl, totK_node, atot12709, atot12710]
  decide +kernel

theorem arows12716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12716 = true := by
  rw [show D2M8K2.u12716 = KTree.node D2M8K2.u12714 (nat_lit 27421627) (nat_lit 1486489245) (nat_lit 0) D2M8K2.u12715 from rfl, allE_node, arows12714, irow12716, arows12715]
  all_goals rfl

theorem atot12716 : totK PD2M8K2 D2M8K2.u12716 = [0, 420222413888, 1433504641276, 1418970339624, 317753951784, 11837410003, 0, 0] := by
  rw [show D2M8K2.u12716 = KTree.node D2M8K2.u12714 (nat_lit 27421627) (nat_lit 1486489245) (nat_lit 0) D2M8K2.u12715 from rfl, totK_node, atot12714, atot12715]
  decide +kernel

theorem arows12719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12719 = true := by
  rw [show D2M8K2.u12719 = KTree.node D2M8K2.u12717 (nat_lit 27425003) (nat_lit 2880337099) (nat_lit 0) D2M8K2.u12718 from rfl, allE_node, arows12717, irow12719, arows12718]
  all_goals rfl

theorem atot12719 : totK PD2M8K2 D2M8K2.u12719 = [0, 386097028840, 1423017250575, 1451353929696, 329337457595, 12003981235, 0, 0] := by
  rw [show D2M8K2.u12719 = KTree.node D2M8K2.u12717 (nat_lit 27425003) (nat_lit 2880337099) (nat_lit 0) D2M8K2.u12718 from rfl, totK_node, atot12717, atot12718]
  decide +kernel

theorem arows12723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12723 = true := by
  rw [show D2M8K2.u12723 = KTree.node D2M8K2.u12721 (nat_lit 27428066) (nat_lit 4074876605) (nat_lit 0) D2M8K2.u12722 from rfl, allE_node, arows12721, irow12723, arows12722]
  all_goals rfl

theorem atot12723 : totK PD2M8K2 D2M8K2.u12723 = [0, 441572992272, 1562246669120, 1389230603856, 232039945812, 3867150671, 0, 0] := by
  rw [show D2M8K2.u12723 = KTree.node D2M8K2.u12721 (nat_lit 27428066) (nat_lit 4074876605) (nat_lit 0) D2M8K2.u12722 from rfl, totK_node, atot12721, atot12722]
  decide +kernel

theorem arows12726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12726 = true := by
  rw [show D2M8K2.u12726 = KTree.node D2M8K2.u12724 (nat_lit 27431935) (nat_lit 2408648108) (nat_lit 0) D2M8K2.u12725 from rfl, allE_node, arows12724, irow12726, arows12725]
  all_goals rfl

theorem atot12726 : totK PD2M8K2 D2M8K2.u12726 = [0, 354625091026, 1349327251955, 1478122209235, 393167174928, 9478845344, 0, 0] := by
  rw [show D2M8K2.u12726 = KTree.node D2M8K2.u12724 (nat_lit 27431935) (nat_lit 2408648108) (nat_lit 0) D2M8K2.u12725 from rfl, totK_node, atot12724, atot12725]
  decide +kernel

theorem arows12733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12733 = true := by
  rw [show D2M8K2.u12733 = KTree.node D2M8K2.u12731 (nat_lit 27438596) (nat_lit 3609684929) (nat_lit 0) D2M8K2.u12732 from rfl, allE_node, arows12731, irow12733, arows12732]
  all_goals rfl

theorem atot12733 : totK PD2M8K2 D2M8K2.u12733 = [0, 0, 447896856122, 1436295893645, 1349022858999, 401282988249, 29044448997, 0] := by
  rw [show D2M8K2.u12733 = KTree.node D2M8K2.u12731 (nat_lit 27438596) (nat_lit 3609684929) (nat_lit 0) D2M8K2.u12732 from rfl, totK_node, atot12731, atot12732]
  decide +kernel

theorem arows12736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12736 = true := by
  rw [show D2M8K2.u12736 = KTree.node D2M8K2.u12734 (nat_lit 27441361) (nat_lit 1435094248) (nat_lit 0) D2M8K2.u12735 from rfl, allE_node, arows12734, irow12736, arows12735]
  all_goals rfl

theorem atot12736 : totK PD2M8K2 D2M8K2.u12736 = [0, 0, 418223760961, 1467841451134, 1387686125222, 321477080225, 10786841256, 0] := by
  rw [show D2M8K2.u12736 = KTree.node D2M8K2.u12734 (nat_lit 27441361) (nat_lit 1435094248) (nat_lit 0) D2M8K2.u12735 from rfl, totK_node, atot12734, atot12735]
  decide +kernel

theorem arows12740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12740 = true := by
  rw [show D2M8K2.u12740 = KTree.node D2M8K2.u12738 (nat_lit 27445203) (nat_lit 2578489642) (nat_lit 0) D2M8K2.u12739 from rfl, allE_node, arows12738, irow12740, arows12739]
  all_goals rfl

theorem atot12740 : totK PD2M8K2 D2M8K2.u12740 = [0, 0, 418454291232, 1512619595797, 1383908080761, 270082983460, 6282383998, 0] := by
  rw [show D2M8K2.u12740 = KTree.node D2M8K2.u12738 (nat_lit 27445203) (nat_lit 2578489642) (nat_lit 0) D2M8K2.u12739 from rfl, totK_node, atot12738, atot12739]
  decide +kernel

theorem arows12743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12743 = true := by
  rw [show D2M8K2.u12743 = KTree.node D2M8K2.u12741 (nat_lit 27448457) (nat_lit 1624211620) (nat_lit 0) D2M8K2.u12742 from rfl, allE_node, arows12741, irow12743, arows12742]
  all_goals rfl

theorem atot12743 : totK PD2M8K2 D2M8K2.u12743 = [0, 0, 419272503621, 1582087701776, 1415155224252, 193373082839, 1186940923, 0] := by
  rw [show D2M8K2.u12743 = KTree.node D2M8K2.u12741 (nat_lit 27448457) (nat_lit 1624211620) (nat_lit 0) D2M8K2.u12742 from rfl, totK_node, atot12741, atot12742]
  decide +kernel

theorem arows12748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12748 = true := by
  rw [show D2M8K2.u12748 = KTree.node D2M8K2.u12746 (nat_lit 27452452) (nat_lit 3727352161) (nat_lit 0) D2M8K2.u12747 from rfl, allE_node, arows12746, irow12748, arows12747]
  all_goals rfl

theorem atot12748 : totK PD2M8K2 D2M8K2.u12748 = [0, 0, 404663385649, 1467786344125, 1451550674957, 295897605880, 3899220927, 0] := by
  rw [show D2M8K2.u12748 = KTree.node D2M8K2.u12746 (nat_lit 27452452) (nat_lit 3727352161) (nat_lit 0) D2M8K2.u12747 from rfl, totK_node, atot12746, atot12747]
  decide +kernel

theorem arows12751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12751 = true := by
  rw [show D2M8K2.u12751 = KTree.node D2M8K2.u12749 (nat_lit 27456276) (nat_lit 3249269530) (nat_lit 0) D2M8K2.u12750 from rfl, allE_node, arows12749, irow12751, arows12750]
  all_goals rfl

theorem atot12751 : totK PD2M8K2 D2M8K2.u12751 = [0, 507981697955, 1601022066449, 1226980152362, 206359149191, 66256127300, 6818291842, 0] := by
  rw [show D2M8K2.u12751 = KTree.node D2M8K2.u12749 (nat_lit 27456276) (nat_lit 3249269530) (nat_lit 0) D2M8K2.u12750 from rfl, totK_node, atot12749, atot12750]
  decide +kernel

theorem arows12755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12755 = true := by
  rw [show D2M8K2.u12755 = KTree.node D2M8K2.u12753 (nat_lit 27460246) (nat_lit 3376061873) (nat_lit 0) D2M8K2.u12754 from rfl, allE_node, arows12753, irow12755, arows12754]
  all_goals rfl

theorem atot12755 : totK PD2M8K2 D2M8K2.u12755 = [0, 327576588719, 1214058450439, 1450446657417, 577870259767, 37597116817, 0, 0] := by
  rw [show D2M8K2.u12755 = KTree.node D2M8K2.u12753 (nat_lit 27460246) (nat_lit 3376061873) (nat_lit 0) D2M8K2.u12754 from rfl, totK_node, atot12753, atot12754]
  decide +kernel

theorem arows12758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12758 = true := by
  rw [show D2M8K2.u12758 = KTree.node D2M8K2.u12756 (nat_lit 27463011) (nat_lit 3481550644) (nat_lit 0) D2M8K2.u12757 from rfl, allE_node, arows12756, irow12758, arows12757]
  all_goals rfl

theorem atot12758 : totK PD2M8K2 D2M8K2.u12758 = [0, 356748833854, 1416160399811, 1486068533005, 337739229061, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12758 = KTree.node D2M8K2.u12756 (nat_lit 27463011) (nat_lit 3481550644) (nat_lit 0) D2M8K2.u12757 from rfl, totK_node, atot12756, atot12757]
  decide +kernel

theorem arows12764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12764 = true := by
  rw [show D2M8K2.u12764 = KTree.node D2M8K2.u12762 (nat_lit 27469519) (nat_lit 2411177516) (nat_lit 0) D2M8K2.u12763 from rfl, allE_node, arows12762, irow12764, arows12763]
  all_goals rfl

theorem atot12764 : totK PD2M8K2 D2M8K2.u12764 = [0, 463430625107, 1535831745843, 1359467991257, 248649106109, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12764 = KTree.node D2M8K2.u12762 (nat_lit 27469519) (nat_lit 2411177516) (nat_lit 0) D2M8K2.u12763 from rfl, totK_node, atot12762, atot12763]
  decide +kernel

theorem arows12767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12767 = true := by
  rw [show D2M8K2.u12767 = KTree.node D2M8K2.u12765 (nat_lit 27473459) (nat_lit 2978412160) (nat_lit 0) D2M8K2.u12766 from rfl, allE_node, arows12765, irow12767, arows12766]
  all_goals rfl

theorem atot12767 : totK PD2M8K2 D2M8K2.u12767 = [0, 336929329165, 1351793658938, 1491406304238, 412883466933, 18232212537, 0, 0] := by
  rw [show D2M8K2.u12767 = KTree.node D2M8K2.u12765 (nat_lit 27473459) (nat_lit 2978412160) (nat_lit 0) D2M8K2.u12766 from rfl, totK_node, atot12765, atot12766]
  decide +kernel

theorem arows12771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12771 = true := by
  rw [show D2M8K2.u12771 = KTree.node D2M8K2.u12769 (nat_lit 27479161) (nat_lit 696612104) (nat_lit 0) D2M8K2.u12770 from rfl, allE_node, arows12769, irow12771, arows12770]
  all_goals rfl

theorem atot12771 : totK PD2M8K2 D2M8K2.u12771 = [0, 0, 724850786103, 1878336562839, 937866251004, 63567302826, 0, 0] := by
  rw [show D2M8K2.u12771 = KTree.node D2M8K2.u12769 (nat_lit 27479161) (nat_lit 696612104) (nat_lit 0) D2M8K2.u12770 from rfl, totK_node, atot12769, atot12770]
  decide +kernel

theorem arows12774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12774 = true := by
  rw [show D2M8K2.u12774 = KTree.node D2M8K2.u12772 (nat_lit 27483624) (nat_lit 2551978712) (nat_lit 0) D2M8K2.u12773 from rfl, allE_node, arows12772, irow12774, arows12773]
  all_goals rfl

theorem atot12774 : totK PD2M8K2 D2M8K2.u12774 = [0, 0, 418952869753, 1477375864160, 1323233218543, 298969000539, 13016197374, 0] := by
  rw [show D2M8K2.u12774 = KTree.node D2M8K2.u12772 (nat_lit 27483624) (nat_lit 2551978712) (nat_lit 0) D2M8K2.u12773 from rfl, totK_node, atot12772, atot12773]
  decide +kernel

theorem arows12779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12779 = true := by
  rw [show D2M8K2.u12779 = KTree.node D2M8K2.u12777 (nat_lit 27490260) (nat_lit 2930179721) (nat_lit 0) D2M8K2.u12778 from rfl, allE_node, arows12777, irow12779, arows12778]
  all_goals rfl

theorem atot12779 : totK PD2M8K2 D2M8K2.u12779 = [0, 0, 496653062736, 1647302688059, 1215623897015, 179372927203, 4574395652, 0] := by
  rw [show D2M8K2.u12779 = KTree.node D2M8K2.u12777 (nat_lit 27490260) (nat_lit 2930179721) (nat_lit 0) D2M8K2.u12778 from rfl, totK_node, atot12777, atot12778]
  decide +kernel

theorem arows12782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12782 = true := by
  rw [show D2M8K2.u12782 = KTree.node D2M8K2.u12780 (nat_lit 27496059) (nat_lit 2255737520) (nat_lit 0) D2M8K2.u12781 from rfl, allE_node, arows12780, irow12782, arows12781]
  all_goals rfl

theorem atot12782 : totK PD2M8K2 D2M8K2.u12782 = [0, 325011403864, 1247407119773, 1437833422841, 556092818739, 40357939906, 0, 0] := by
  rw [show D2M8K2.u12782 = KTree.node D2M8K2.u12780 (nat_lit 27496059) (nat_lit 2255737520) (nat_lit 0) D2M8K2.u12781 from rfl, totK_node, atot12780, atot12781]
  decide +kernel

theorem arows12786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12786 = true := by
  rw [show D2M8K2.u12786 = KTree.node D2M8K2.u12784 (nat_lit 27500498) (nat_lit 3982509898) (nat_lit 0) D2M8K2.u12785 from rfl, allE_node, arows12784, irow12786, arows12785]
  all_goals rfl

theorem atot12786 : totK PD2M8K2 D2M8K2.u12786 = [0, 428960387537, 1474167124631, 1372662959870, 354139732947, 25364689049, 0, 0] := by
  rw [show D2M8K2.u12786 = KTree.node D2M8K2.u12784 (nat_lit 27500498) (nat_lit 3982509898) (nat_lit 0) D2M8K2.u12785 from rfl, totK_node, atot12784, atot12785]
  decide +kernel

theorem arows12789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12789 = true := by
  rw [show D2M8K2.u12789 = KTree.node D2M8K2.u12787 (nat_lit 27506713) (nat_lit 1243904975) (nat_lit 0) D2M8K2.u12788 from rfl, allE_node, arows12787, irow12789, arows12788]
  all_goals rfl

theorem atot12789 : totK PD2M8K2 D2M8K2.u12789 = [0, 438704021447, 1458328331085, 1361199906589, 354723676269, 12230400950, 0, 0] := by
  rw [show D2M8K2.u12789 = KTree.node D2M8K2.u12787 (nat_lit 27506713) (nat_lit 1243904975) (nat_lit 0) D2M8K2.u12788 from rfl, totK_node, atot12787, atot12788]
  decide +kernel

theorem arows12799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12799 = true := by
  rw [show D2M8K2.u12799 = KTree.node D2M8K2.u12797 (nat_lit 27509985) (nat_lit 1744413445) (nat_lit 0) D2M8K2.u12798 from rfl, allE_node, arows12797, irow12799, arows12798]
  all_goals rfl

theorem atot12799 : totK PD2M8K2 D2M8K2.u12799 = [0, 413788040677, 1436437438086, 1404468476480, 337027762770, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12799 = KTree.node D2M8K2.u12797 (nat_lit 27509985) (nat_lit 1744413445) (nat_lit 0) D2M8K2.u12798 from rfl, totK_node, atot12797, atot12798]
  decide +kernel

theorem arows12802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12802 = true := by
  rw [show D2M8K2.u12802 = KTree.node D2M8K2.u12800 (nat_lit 27513594) (nat_lit 3904249591) (nat_lit 0) D2M8K2.u12801 from rfl, allE_node, arows12800, irow12802, arows12801]
  all_goals rfl

theorem atot12802 : totK PD2M8K2 D2M8K2.u12802 = [0, 386732656573, 1447219726065, 1478396663813, 298194521591, 6249254262, 0, 0] := by
  rw [show D2M8K2.u12802 = KTree.node D2M8K2.u12800 (nat_lit 27513594) (nat_lit 3904249591) (nat_lit 0) D2M8K2.u12801 from rfl, totK_node, atot12800, atot12801]
  decide +kernel

theorem arows12806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12806 = true := by
  rw [show D2M8K2.u12806 = KTree.node D2M8K2.u12804 (nat_lit 27517549) (nat_lit 1386241413) (nat_lit 0) D2M8K2.u12805 from rfl, allE_node, arows12804, irow12806, arows12805]
  all_goals rfl

theorem atot12806 : totK PD2M8K2 D2M8K2.u12806 = [0, 0, 806194014875, 1887586899487, 856639463007, 56601200380, 0, 0] := by
  rw [show D2M8K2.u12806 = KTree.node D2M8K2.u12804 (nat_lit 27517549) (nat_lit 1386241413) (nat_lit 0) D2M8K2.u12805 from rfl, totK_node, atot12804, atot12805]
  decide +kernel

theorem arows12809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12809 = true := by
  rw [show D2M8K2.u12809 = KTree.node D2M8K2.u12807 (nat_lit 27527305) (nat_lit 1486140203) (nat_lit 0) D2M8K2.u12808 from rfl, allE_node, arows12807, irow12809, arows12808]
  all_goals rfl

theorem atot12809 : totK PD2M8K2 D2M8K2.u12809 = [0, 0, 699069125352, 1875617256039, 979020535479, 62846066613, 0, 0] := by
  rw [show D2M8K2.u12809 = KTree.node D2M8K2.u12807 (nat_lit 27527305) (nat_lit 1486140203) (nat_lit 0) D2M8K2.u12808 from rfl, totK_node, atot12807, atot12808]
  decide +kernel

theorem arows12814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12814 = true := by
  rw [show D2M8K2.u12814 = KTree.node D2M8K2.u12812 (nat_lit 27530616) (nat_lit 3519940497) (nat_lit 0) D2M8K2.u12813 from rfl, allE_node, arows12812, irow12814, arows12813]
  all_goals rfl

theorem atot12814 : totK PD2M8K2 D2M8K2.u12814 = [0, 0, 412731075999, 1488824098401, 1328868805381, 303492535628, 13105450397, 0] := by
  rw [show D2M8K2.u12814 = KTree.node D2M8K2.u12812 (nat_lit 27530616) (nat_lit 3519940497) (nat_lit 0) D2M8K2.u12813 from rfl, totK_node, atot12812, atot12813]
  decide +kernel

theorem arows12817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12817 = true := by
  rw [show D2M8K2.u12817 = KTree.node D2M8K2.u12815 (nat_lit 27534418) (nat_lit 3994184913) (nat_lit 0) D2M8K2.u12816 from rfl, allE_node, arows12815, irow12817, arows12816]
  all_goals rfl

theorem atot12817 : totK PD2M8K2 D2M8K2.u12817 = [0, 104114512826, 620840806507, 1447557700495, 1184717793774, 195185069131, 4720618446, 0] := by
  rw [show D2M8K2.u12817 = KTree.node D2M8K2.u12815 (nat_lit 27534418) (nat_lit 3994184913) (nat_lit 0) D2M8K2.u12816 from rfl, totK_node, atot12815, atot12816]
  decide +kernel

theorem arows12821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12821 = true := by
  rw [show D2M8K2.u12821 = KTree.node D2M8K2.u12819 (nat_lit 27539854) (nat_lit 3181925759) (nat_lit 0) D2M8K2.u12820 from rfl, allE_node, arows12819, irow12821, arows12820]
  all_goals rfl

theorem atot12821 : totK PD2M8K2 D2M8K2.u12821 = [0, 504503377626, 1634313060736, 1304888424064, 172466927283, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12821 = KTree.node D2M8K2.u12819 (nat_lit 27539854) (nat_lit 3181925759) (nat_lit 0) D2M8K2.u12820 from rfl, totK_node, atot12819, atot12820]
  decide +kernel

theorem arows12824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12824 = true := by
  rw [show D2M8K2.u12824 = KTree.node D2M8K2.u12822 (nat_lit 27543491) (nat_lit 2759426660) (nat_lit 0) D2M8K2.u12823 from rfl, allE_node, arows12822, irow12824, arows12823]
  all_goals rfl

theorem atot12824 : totK PD2M8K2 D2M8K2.u12824 = [0, 328554724530, 1232494096157, 1456395089795, 582736394592, 37601708222, 0, 0] := by
  rw [show D2M8K2.u12824 = KTree.node D2M8K2.u12822 (nat_lit 27543491) (nat_lit 2759426660) (nat_lit 0) D2M8K2.u12823 from rfl, totK_node, atot12822, atot12823]
  decide +kernel

end QECKChecks.D2M8K2
