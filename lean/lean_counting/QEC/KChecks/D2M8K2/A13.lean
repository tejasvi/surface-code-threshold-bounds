import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A12

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows15592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15592 = true := by
  rw [show D2M8K2.u15592 = KTree.node D2M8K2.t15600 (nat_lit 33952528) (nat_lit 3688860793) (nat_lit 0) D2M8K2.t15601 from rfl, allE_node, rows15600, irow15592, rows15601]
  all_goals rfl

theorem atot15592 : totK PD2M8K2 D2M8K2.u15592 = [0, 0, 357412367761, 951831033181, 485081374314, 30830301070, 0, 0] := by
  rw [show D2M8K2.u15592 = KTree.node D2M8K2.t15600 (nat_lit 33952528) (nat_lit 3688860793) (nat_lit 0) D2M8K2.t15601 from rfl, totK_node, tot15600, tot15601]
  decide +kernel

theorem arows15593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15593 = true := by
  rw [show D2M8K2.u15593 = KTree.node D2M8K2.t15602 (nat_lit 33954208) (nat_lit 3274910114) (nat_lit 0) D2M8K2.t15603 from rfl, allE_node, rows15602, irow15593, rows15603]
  all_goals rfl

theorem atot15593 : totK PD2M8K2 D2M8K2.u15593 = [0, 0, 50247253896, 509901647642, 875414405925, 276226739243, 13016197374, 0] := by
  rw [show D2M8K2.u15593 = KTree.node D2M8K2.t15602 (nat_lit 33954208) (nat_lit 3274910114) (nat_lit 0) D2M8K2.t15603 from rfl, totK_node, tot15602, tot15603]
  decide +kernel

theorem arows15595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15595 = true := by
  rw [show D2M8K2.u15595 = KTree.node D2M8K2.t15604 (nat_lit 33959363) (nat_lit 2470940877) (nat_lit 0) D2M8K2.t15605 from rfl, allE_node, rows15604, irow15595, rows15605]
  all_goals rfl

theorem atot15595 : totK PD2M8K2 D2M8K2.u15595 = [0, 0, 347333348755, 937574258960, 456209569825, 27019206085, 0, 0] := by
  rw [show D2M8K2.u15595 = KTree.node D2M8K2.t15604 (nat_lit 33959363) (nat_lit 2470940877) (nat_lit 0) D2M8K2.t15605 from rfl, totK_node, tot15604, tot15605]
  decide +kernel

theorem arows15596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15596 = true := by
  rw [show D2M8K2.u15596 = KTree.node D2M8K2.t15606 (nat_lit 33961545) (nat_lit 1858190061) (nat_lit 0) D2M8K2.t15607 from rfl, allE_node, rows15606, irow15596, rows15607]
  all_goals rfl

theorem atot15596 : totK PD2M8K2 D2M8K2.u15596 = [0, 0, 139295941726, 660073477603, 743530304251, 150020283298, 4574395652, 0] := by
  rw [show D2M8K2.u15596 = KTree.node D2M8K2.t15606 (nat_lit 33961545) (nat_lit 1858190061) (nat_lit 0) D2M8K2.t15607 from rfl, totK_node, tot15606, tot15607]
  decide +kernel

theorem arows15599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15599 = true := by
  rw [show D2M8K2.u15599 = KTree.node D2M8K2.t15608 (nat_lit 33963067) (nat_lit 2190411876) (nat_lit 0) D2M8K2.t15609 from rfl, allE_node, rows15608, irow15599, rows15609]
  all_goals rfl

theorem atot15599 : totK PD2M8K2 D2M8K2.u15599 = [0, 89263107398, 407392853760, 809831542376, 477766471999, 42903141254, 0, 0] := by
  rw [show D2M8K2.u15599 = KTree.node D2M8K2.t15608 (nat_lit 33963067) (nat_lit 2190411876) (nat_lit 0) D2M8K2.t15609 from rfl, totK_node, tot15608, tot15609]
  decide +kernel

theorem arows15600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15600 = true := by
  rw [show D2M8K2.u15600 = KTree.node D2M8K2.t15610 (nat_lit 34008148) (nat_lit 2709857969) (nat_lit 0) D2M8K2.t15611 from rfl, allE_node, rows15610, irow15600, rows15611]
  all_goals rfl

theorem atot15600 : totK PD2M8K2 D2M8K2.u15600 = [0, 306092916288, 915509223854, 513124871879, 34166620044, 0, 0, 0] := by
  rw [show D2M8K2.u15600 = KTree.node D2M8K2.t15610 (nat_lit 34008148) (nat_lit 2709857969) (nat_lit 0) D2M8K2.t15611 from rfl, totK_node, tot15610, tot15611]
  decide +kernel

theorem arows15602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15602 = true := by
  rw [show D2M8K2.u15602 = KTree.node D2M8K2.t15612 (nat_lit 34010016) (nat_lit 3577290238) (nat_lit 0) D2M8K2.t15613 from rfl, allE_node, rows15612, irow15602, rows15613]
  all_goals rfl

theorem atot15602 : totK PD2M8K2 D2M8K2.u15602 = [0, 162872193368, 685379830811, 823384295862, 140674993687, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15602 = KTree.node D2M8K2.t15612 (nat_lit 34010016) (nat_lit 3577290238) (nat_lit 0) D2M8K2.t15613 from rfl, totK_node, tot15612, tot15613]
  decide +kernel

theorem arows15603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15603 = true := by
  rw [show D2M8K2.u15603 = KTree.node D2M8K2.t15614 (nat_lit 34011826) (nat_lit 3443923863) (nat_lit 0) D2M8K2.t15615 from rfl, allE_node, rows15614, irow15603, rows15615]
  all_goals rfl

theorem atot15603 : totK PD2M8K2 D2M8K2.u15603 = [0, 244164374753, 809894547658, 621725456628, 144727374345, 9935383930, 0, 0] := by
  rw [show D2M8K2.u15603 = KTree.node D2M8K2.t15614 (nat_lit 34011826) (nat_lit 3443923863) (nat_lit 0) D2M8K2.t15615 from rfl, totK_node, tot15614, tot15615]
  decide +kernel

theorem arows15611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15611 = true := by
  rw [show D2M8K2.u15611 = KTree.node D2M8K2.t15616 (nat_lit 34013554) (nat_lit 3395644128) (nat_lit 0) D2M8K2.t15617 from rfl, allE_node, rows15616, irow15611, rows15617]
  all_goals rfl

theorem atot15611 : totK PD2M8K2 D2M8K2.u15611 = [0, 164861873023, 646753943256, 778343213265, 231717615787, 5382912678, 0, 0] := by
  rw [show D2M8K2.u15611 = KTree.node D2M8K2.t15616 (nat_lit 34013554) (nat_lit 3395644128) (nat_lit 0) D2M8K2.t15617 from rfl, totK_node, tot15616, tot15617]
  decide +kernel

theorem arows15612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15612 = true := by
  rw [show D2M8K2.u15612 = KTree.node D2M8K2.t15618 (nat_lit 34015188) (nat_lit 3058629690) (nat_lit 0) D2M8K2.t15619 from rfl, allE_node, rows15618, irow15612, rows15619]
  all_goals rfl

theorem atot15612 : totK PD2M8K2 D2M8K2.u15612 = [0, 256896689510, 837111527732, 623830339820, 82017254533, 1164319620, 0, 0] := by
  rw [show D2M8K2.u15612 = KTree.node D2M8K2.t15618 (nat_lit 34015188) (nat_lit 3058629690) (nat_lit 0) D2M8K2.t15619 from rfl, totK_node, tot15618, tot15619]
  decide +kernel

theorem arows15614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15614 = true := by
  rw [show D2M8K2.u15614 = KTree.node D2M8K2.t15620 (nat_lit 34016901) (nat_lit 1514933268) (nat_lit 0) D2M8K2.t15621 from rfl, allE_node, rows15620, irow15614, rows15621]
  all_goals rfl

theorem atot15614 : totK PD2M8K2 D2M8K2.u15614 = [0, 106423910014, 582786613304, 838578676774, 245911652648, 11885407614, 0, 0] := by
  rw [show D2M8K2.u15614 = KTree.node D2M8K2.t15620 (nat_lit 34016901) (nat_lit 1514933268) (nat_lit 0) D2M8K2.t15621 from rfl, totK_node, tot15620, tot15621]
  decide +kernel

theorem arows15615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15615 = true := by
  rw [show D2M8K2.u15615 = KTree.node D2M8K2.t15622 (nat_lit 34021750) (nat_lit 2513146003) (nat_lit 0) D2M8K2.t15623 from rfl, allE_node, rows15622, irow15615, rows15623]
  all_goals rfl

theorem atot15615 : totK PD2M8K2 D2M8K2.u15615 = [0, 313621154698, 891963448267, 550178549062, 53549756733, 0, 0, 0] := by
  rw [show D2M8K2.u15615 = KTree.node D2M8K2.t15622 (nat_lit 34021750) (nat_lit 2513146003) (nat_lit 0) D2M8K2.t15623 from rfl, totK_node, tot15622, tot15623]
  decide +kernel

theorem arows15618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15618 = true := by
  rw [show D2M8K2.u15618 = KTree.node D2M8K2.t15624 (nat_lit 34023757) (nat_lit 1284558185) (nat_lit 0) D2M8K2.t15625 from rfl, allE_node, rows15624, irow15618, rows15625]
  all_goals rfl

theorem atot15618 : totK PD2M8K2 D2M8K2.u15618 = [0, 0, 500182324405, 1013787784802, 278222800366, 6350335412, 0, 0] := by
  rw [show D2M8K2.u15618 = KTree.node D2M8K2.t15624 (nat_lit 34023757) (nat_lit 1284558185) (nat_lit 0) D2M8K2.t15625 from rfl, totK_node, tot15624, tot15625]
  decide +kernel

theorem arows15619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15619 = true := by
  rw [show D2M8K2.u15619 = KTree.node D2M8K2.t15626 (nat_lit 34029092) (nat_lit 3114047495) (nat_lit 0) D2M8K2.t15627 from rfl, allE_node, rows15626, irow15619, rows15627]
  all_goals rfl

theorem atot15619 : totK PD2M8K2 D2M8K2.u15619 = [0, 0, 253533200149, 842768968839, 552587851819, 62993037141, 1138244013, 0] := by
  rw [show D2M8K2.u15619 = KTree.node D2M8K2.t15626 (nat_lit 34029092) (nat_lit 3114047495) (nat_lit 0) D2M8K2.t15627 from rfl, totK_node, tot15626, tot15627]
  decide +kernel

theorem arows15621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15621 = true := by
  rw [show D2M8K2.u15621 = KTree.node D2M8K2.t15628 (nat_lit 34031722) (nat_lit 3790371784) (nat_lit 0) D2M8K2.t15629 from rfl, allE_node, rows15628, irow15621, rows15629]
  all_goals rfl

theorem atot15621 : totK PD2M8K2 D2M8K2.u15621 = [0, 0, 249420732261, 870154159832, 621527985170, 55249398018, 0, 0] := by
  rw [show D2M8K2.u15621 = KTree.node D2M8K2.t15628 (nat_lit 34031722) (nat_lit 3790371784) (nat_lit 0) D2M8K2.t15629 from rfl, totK_node, tot15628, tot15629]
  decide +kernel

theorem arows15622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15622 = true := by
  rw [show D2M8K2.u15622 = KTree.node D2M8K2.t15630 (nat_lit 34034781) (nat_lit 1551223810) (nat_lit 0) D2M8K2.t15631 from rfl, allE_node, rows15630, irow15622, rows15631]
  all_goals rfl

theorem atot15622 : totK PD2M8K2 D2M8K2.u15622 = [0, 0, 405858467724, 967125668494, 421405911918, 20817991513, 0, 0] := by
  rw [show D2M8K2.u15622 = KTree.node D2M8K2.t15630 (nat_lit 34034781) (nat_lit 1551223810) (nat_lit 0) D2M8K2.t15631 from rfl, totK_node, tot15630, tot15631]
  decide +kernel

theorem arows15626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15626 = true := by
  rw [show D2M8K2.u15626 = KTree.node D2M8K2.t15632 (nat_lit 34036299) (nat_lit 3710125387) (nat_lit 0) D2M8K2.t15633 from rfl, allE_node, rows15632, irow15626, rows15633]
  all_goals rfl

theorem atot15626 : totK PD2M8K2 D2M8K2.u15626 = [0, 0, 340951151347, 943002851378, 467660895017, 27205345563, 0, 0] := by
  rw [show D2M8K2.u15626 = KTree.node D2M8K2.t15632 (nat_lit 34036299) (nat_lit 3710125387) (nat_lit 0) D2M8K2.t15633 from rfl, totK_node, tot15632, tot15633]
  decide +kernel

theorem arows15627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15627 = true := by
  rw [show D2M8K2.u15627 = KTree.node D2M8K2.t15634 (nat_lit 34042800) (nat_lit 3515465258) (nat_lit 0) D2M8K2.t15635 from rfl, allE_node, rows15634, irow15627, rows15635]
  all_goals rfl

theorem atot15627 : totK PD2M8K2 D2M8K2.u15627 = [0, 0, 251497706177, 827814143787, 590992059202, 73824186436, 1095107716, 0] := by
  rw [show D2M8K2.u15627 = KTree.node D2M8K2.t15634 (nat_lit 34042800) (nat_lit 3515465258) (nat_lit 0) D2M8K2.t15635 from rfl, totK_node, tot15634, tot15635]
  decide +kernel

theorem arows15629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15629 = true := by
  rw [show D2M8K2.u15629 = KTree.node D2M8K2.t15636 (nat_lit 34048624) (nat_lit 3313151831) (nat_lit 0) D2M8K2.t15637 from rfl, allE_node, rows15636, irow15629, rows15637]
  all_goals rfl

theorem atot15629 : totK PD2M8K2 D2M8K2.u15629 = [0, 254709363068, 590415592729, 454868060785, 377053237574, 93082756375, 3882006667, 0] := by
  rw [show D2M8K2.u15629 = KTree.node D2M8K2.t15636 (nat_lit 34048624) (nat_lit 3313151831) (nat_lit 0) D2M8K2.t15637 from rfl, totK_node, tot15636, tot15637]
  decide +kernel

theorem arows15630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15630 = true := by
  rw [show D2M8K2.u15630 = KTree.node D2M8K2.t15638 (nat_lit 34050222) (nat_lit 3814015020) (nat_lit 0) D2M8K2.t15639 from rfl, allE_node, rows15638, irow15630, rows15639]
  all_goals rfl

theorem atot15630 : totK PD2M8K2 D2M8K2.u15630 = [0, 153505176087, 720792417318, 774202267552, 128829641057, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15630 = KTree.node D2M8K2.t15638 (nat_lit 34050222) (nat_lit 3814015020) (nat_lit 0) D2M8K2.t15639 from rfl, totK_node, tot15638, tot15639]
  decide +kernel

theorem arows15633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15633 = true := by
  rw [show D2M8K2.u15633 = KTree.node D2M8K2.t15640 (nat_lit 34052549) (nat_lit 2333378917) (nat_lit 0) D2M8K2.t15641 from rfl, allE_node, rows15640, irow15633, rows15641]
  all_goals rfl

theorem atot15633 : totK PD2M8K2 D2M8K2.u15633 = [0, 295252492639, 849175364322, 627051502797, 68090231317, 0, 0, 0] := by
  rw [show D2M8K2.u15633 = KTree.node D2M8K2.t15640 (nat_lit 34052549) (nat_lit 2333378917) (nat_lit 0) D2M8K2.t15641 from rfl, totK_node, tot15640, tot15641]
  decide +kernel

theorem arows15634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15634 = true := by
  rw [show D2M8K2.u15634 = KTree.node D2M8K2.t15642 (nat_lit 34054104) (nat_lit 2877460365) (nat_lit 0) D2M8K2.t15643 from rfl, allE_node, rows15642, irow15634, rows15643]
  all_goals rfl

theorem atot15634 : totK PD2M8K2 D2M8K2.u15634 = [0, 121150445789, 620416059377, 765112928925, 294431137058, 25114608015, 0, 0] := by
  rw [show D2M8K2.u15634 = KTree.node D2M8K2.t15642 (nat_lit 34054104) (nat_lit 2877460365) (nat_lit 0) D2M8K2.t15643 from rfl, totK_node, tot15642, tot15643]
  decide +kernel

theorem arows15636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15636 = true := by
  rw [show D2M8K2.u15636 = KTree.node D2M8K2.t15644 (nat_lit 34055411) (nat_lit 2961873652) (nat_lit 0) D2M8K2.t15645 from rfl, allE_node, rows15644, irow15636, rows15645]
  all_goals rfl

theorem atot15636 : totK PD2M8K2 D2M8K2.u15636 = [0, 173242794671, 606753843997, 746192880108, 283316089243, 10835369861, 0, 0] := by
  rw [show D2M8K2.u15636 = KTree.node D2M8K2.t15644 (nat_lit 34055411) (nat_lit 2961873652) (nat_lit 0) D2M8K2.t15645 from rfl, totK_node, tot15644, tot15645]
  decide +kernel

theorem arows15637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15637 = true := by
  rw [show D2M8K2.u15637 = KTree.node D2M8K2.t15646 (nat_lit 34056912) (nat_lit 3531234453) (nat_lit 0) D2M8K2.t15647 from rfl, allE_node, rows15646, irow15637, rows15647]
  all_goals rfl

theorem atot15637 : totK PD2M8K2 D2M8K2.u15637 = [0, 249344020546, 801052158643, 651366441815, 103366523981, 1164319620, 0, 0] := by
  rw [show D2M8K2.u15637 = KTree.node D2M8K2.t15646 (nat_lit 34056912) (nat_lit 3531234453) (nat_lit 0) D2M8K2.t15647 from rfl, totK_node, tot15646, tot15647]
  decide +kernel

theorem arows15642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15642 = true := by
  rw [show D2M8K2.u15642 = KTree.node D2M8K2.t15648 (nat_lit 34058624) (nat_lit 2969091196) (nat_lit 0) D2M8K2.t15649 from rfl, allE_node, rows15648, irow15642, rows15649]
  all_goals rfl

theorem atot15642 : totK PD2M8K2 D2M8K2.u15642 = [0, 167221847241, 658273544112, 748020498285, 221363091680, 11879463720, 0, 0] := by
  rw [show D2M8K2.u15642 = KTree.node D2M8K2.t15648 (nat_lit 34058624) (nat_lit 2969091196) (nat_lit 0) D2M8K2.t15649 from rfl, totK_node, tot15648, tot15649]
  decide +kernel

theorem arows15643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15643 = true := by
  rw [show D2M8K2.u15643 = KTree.node D2M8K2.t15650 (nat_lit 34060536) (nat_lit 3419766949) (nat_lit 0) D2M8K2.t15651 from rfl, allE_node, rows15650, irow15643, rows15651]
  all_goals rfl

theorem atot15643 : totK PD2M8K2 D2M8K2.u15643 = [0, 178318182190, 746102523171, 780136326495, 127006209271, 1198073392, 0, 0] := by
  rw [show D2M8K2.u15643 = KTree.node D2M8K2.t15650 (nat_lit 34060536) (nat_lit 3419766949) (nat_lit 0) D2M8K2.t15651 from rfl, totK_node, tot15650, tot15651]
  decide +kernel

theorem arows15645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15645 = true := by
  rw [show D2M8K2.u15645 = KTree.node D2M8K2.t15652 (nat_lit 34066128) (nat_lit 2775940435) (nat_lit 0) D2M8K2.t15653 from rfl, allE_node, rows15652, irow15645, rows15653]
  all_goals rfl

theorem atot15645 : totK PD2M8K2 D2M8K2.u15645 = [0, 281790497535, 784300771949, 610220386574, 145457379067, 6692597642, 0, 0] := by
  rw [show D2M8K2.u15645 = KTree.node D2M8K2.t15652 (nat_lit 34066128) (nat_lit 2775940435) (nat_lit 0) D2M8K2.t15653 from rfl, totK_node, tot15652, tot15653]
  decide +kernel

theorem arows15646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15646 = true := by
  rw [show D2M8K2.u15646 = KTree.node D2M8K2.t15654 (nat_lit 34067569) (nat_lit 1511572004) (nat_lit 0) D2M8K2.t15655 from rfl, allE_node, rows15654, irow15646, rows15655]
  all_goals rfl

theorem atot15646 : totK PD2M8K2 D2M8K2.u15646 = [0, 161232167476, 701550154930, 790531321810, 168966040869, 2304167554, 0, 0] := by
  rw [show D2M8K2.u15646 = KTree.node D2M8K2.t15654 (nat_lit 34067569) (nat_lit 1511572004) (nat_lit 0) D2M8K2.t15655 from rfl, totK_node, tot15654, tot15655]
  decide +kernel

theorem arows15649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15649 = true := by
  rw [show D2M8K2.u15649 = KTree.node D2M8K2.t15656 (nat_lit 34069227) (nat_lit 3011337224) (nat_lit 0) D2M8K2.t15657 from rfl, allE_node, rows15656, irow15649, rows15657]
  all_goals rfl

theorem atot15649 : totK PD2M8K2 D2M8K2.u15649 = [0, 0, 370403657513, 951925215613, 435940327127, 25080681604, 0, 0] := by
  rw [show D2M8K2.u15649 = KTree.node D2M8K2.t15656 (nat_lit 34069227) (nat_lit 3011337224) (nat_lit 0) D2M8K2.t15657 from rfl, totK_node, tot15656, tot15657]
  decide +kernel

theorem arows15650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15650 = true := by
  rw [show D2M8K2.u15650 = KTree.node D2M8K2.t15658 (nat_lit 34070838) (nat_lit 3732158378) (nat_lit 0) D2M8K2.t15659 from rfl, allE_node, rows15658, irow15650, rows15659]
  all_goals rfl

theorem atot15650 : totK PD2M8K2 D2M8K2.u15650 = [0, 0, 213634486140, 776571914947, 673317443784, 95059563695, 1310285577, 0] := by
  rw [show D2M8K2.u15650 = KTree.node D2M8K2.t15658 (nat_lit 34070838) (nat_lit 3732158378) (nat_lit 0) D2M8K2.t15659 from rfl, totK_node, tot15658, tot15659]
  decide +kernel

theorem arows15652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15652 = true := by
  rw [show D2M8K2.u15652 = KTree.node D2M8K2.t15660 (nat_lit 34073215) (nat_lit 2404281665) (nat_lit 0) D2M8K2.t15661 from rfl, allE_node, rows15660, irow15652, rows15661]
  all_goals rfl

theorem atot15652 : totK PD2M8K2 D2M8K2.u15652 = [0, 0, 260873280047, 836340116589, 656852222381, 65687430276, 0, 0] := by
  rw [show D2M8K2.u15652 = KTree.node D2M8K2.t15660 (nat_lit 34073215) (nat_lit 2404281665) (nat_lit 0) D2M8K2.t15661 from rfl, totK_node, tot15660, tot15661]
  decide +kernel

theorem arows15653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15653 = true := by
  rw [show D2M8K2.u15653 = KTree.node D2M8K2.t15662 (nat_lit 34076225) (nat_lit 2222245322) (nat_lit 0) D2M8K2.t15663 from rfl, allE_node, rows15662, irow15653, rows15663]
  all_goals rfl

theorem atot15653 : totK PD2M8K2 D2M8K2.u15653 = [0, 0, 378364420130, 933629930728, 481727240373, 35695958101, 0, 0] := by
  rw [show D2M8K2.u15653 = KTree.node D2M8K2.t15662 (nat_lit 34076225) (nat_lit 2222245322) (nat_lit 0) D2M8K2.t15663 from rfl, totK_node, tot15662, tot15663]
  decide +kernel

theorem arows15657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15657 = true := by
  rw [show D2M8K2.u15657 = KTree.node D2M8K2.t15664 (nat_lit 34077736) (nat_lit 3829952091) (nat_lit 0) D2M8K2.t15665 from rfl, allE_node, rows15664, irow15657, rows15665]
  all_goals rfl

theorem atot15657 : totK PD2M8K2 D2M8K2.u15657 = [0, 0, 199734742704, 798322722614, 690266121673, 93495919008, 1075657031, 0] := by
  rw [show D2M8K2.u15657 = KTree.node D2M8K2.t15664 (nat_lit 34077736) (nat_lit 3829952091) (nat_lit 0) D2M8K2.t15665 from rfl, totK_node, tot15664, tot15665]
  decide +kernel

theorem arows15658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15658 = true := by
  rw [show D2M8K2.u15658 = KTree.node D2M8K2.t15666 (nat_lit 34079760) (nat_lit 3736152580) (nat_lit 0) D2M8K2.t15667 from rfl, allE_node, rows15666, irow15658, rows15667]
  all_goals rfl

theorem atot15658 : totK PD2M8K2 D2M8K2.u15658 = [0, 0, 255157910031, 776818844296, 633525730288, 119062975556, 3804183361, 0] := by
  rw [show D2M8K2.u15658 = KTree.node D2M8K2.t15666 (nat_lit 34079760) (nat_lit 3736152580) (nat_lit 0) D2M8K2.t15667 from rfl, totK_node, tot15666, tot15667]
  decide +kernel

theorem arows15660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15660 = true := by
  rw [show D2M8K2.u15660 = KTree.node D2M8K2.t15668 (nat_lit 34081590) (nat_lit 3398370784) (nat_lit 0) D2M8K2.t15669 from rfl, allE_node, rows15668, irow15660, rows15669]
  all_goals rfl

theorem atot15660 : totK PD2M8K2 D2M8K2.u15660 = [0, 0, 118606553215, 657909171940, 834728295323, 177294042040, 4931404646, 0] := by
  rw [show D2M8K2.u15660 = KTree.node D2M8K2.t15668 (nat_lit 34081590) (nat_lit 3398370784) (nat_lit 0) D2M8K2.t15669 from rfl, totK_node, tot15668, tot15669]
  decide +kernel

theorem arows15661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15661 = true := by
  rw [show D2M8K2.u15661 = KTree.node D2M8K2.t15670 (nat_lit 34087149) (nat_lit 1362536998) (nat_lit 0) D2M8K2.t15671 from rfl, allE_node, rows15670, irow15661, rows15671]
  all_goals rfl

theorem atot15661 : totK PD2M8K2 D2M8K2.u15661 = [0, 0, 370781738191, 943075337016, 476116493634, 32628397399, 0, 0] := by
  rw [show D2M8K2.u15661 = KTree.node D2M8K2.t15670 (nat_lit 34087149) (nat_lit 1362536998) (nat_lit 0) D2M8K2.t15671 from rfl, totK_node, tot15670, tot15671]
  decide +kernel

theorem arows15664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15664 = true := by
  rw [show D2M8K2.u15664 = KTree.node D2M8K2.t15672 (nat_lit 34088681) (nat_lit 1507628458) (nat_lit 0) D2M8K2.t15673 from rfl, allE_node, rows15672, irow15664, rows15673]
  all_goals rfl

theorem atot15664 : totK PD2M8K2 D2M8K2.u15664 = [0, 0, 34608413148, 540795850871, 917160762745, 261551129755, 8424427256, 0] := by
  rw [show D2M8K2.u15664 = KTree.node D2M8K2.t15672 (nat_lit 34088681) (nat_lit 1507628458) (nat_lit 0) D2M8K2.t15673 from rfl, totK_node, tot15672, tot15673]
  decide +kernel

theorem arows15665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15665 = true := by
  rw [show D2M8K2.u15665 = KTree.node D2M8K2.t15674 (nat_lit 34090630) (nat_lit 3785078238) (nat_lit 0) D2M8K2.t15675 from rfl, allE_node, rows15674, irow15665, rows15675]
  all_goals rfl

theorem atot15665 : totK PD2M8K2 D2M8K2.u15665 = [0, 0, 325728155863, 806650929666, 490533199199, 135923729037, 13326740810, 0] := by
  rw [show D2M8K2.u15665 = KTree.node D2M8K2.t15674 (nat_lit 34090630) (nat_lit 3785078238) (nat_lit 0) D2M8K2.t15675 from rfl, totK_node, tot15674, tot15675]
  decide +kernel

theorem arows15667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15667 = true := by
  rw [show D2M8K2.u15667 = KTree.node D2M8K2.t15676 (nat_lit 34091845) (nat_lit 1369077893) (nat_lit 0) D2M8K2.t15677 from rfl, allE_node, rows15676, irow15667, rows15677]
  all_goals rfl

theorem atot15667 : totK PD2M8K2 D2M8K2.u15667 = [0, 0, 102957601977, 707955108960, 846509339616, 128153400486, 1369150432, 0] := by
  rw [show D2M8K2.u15667 = KTree.node D2M8K2.t15676 (nat_lit 34091845) (nat_lit 1369077893) (nat_lit 0) D2M8K2.t15677 from rfl, totK_node, tot15676, tot15677]
  decide +kernel

theorem arows15668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15668 = true := by
  rw [show D2M8K2.u15668 = KTree.node D2M8K2.t15678 (nat_lit 34097449) (nat_lit 1203213592) (nat_lit 0) D2M8K2.t15679 from rfl, allE_node, rows15678, irow15668, rows15679]
  all_goals rfl

theorem atot15668 : totK PD2M8K2 D2M8K2.u15668 = [0, 0, 332533294542, 900802350157, 511067911120, 40883716465, 0, 0] := by
  rw [show D2M8K2.u15668 = KTree.node D2M8K2.t15678 (nat_lit 34097449) (nat_lit 1203213592) (nat_lit 0) D2M8K2.t15679 from rfl, totK_node, tot15678, tot15679]
  decide +kernel

theorem arows15674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15674 = true := by
  rw [show D2M8K2.u15674 = KTree.node D2M8K2.t15680 (nat_lit 34098971) (nat_lit 2800672021) (nat_lit 0) D2M8K2.t15681 from rfl, allE_node, rows15680, irow15674, rows15681]
  all_goals rfl

theorem atot15674 : totK PD2M8K2 D2M8K2.u15674 = [0, 0, 87191050473, 606013503600, 888622025282, 201423387326, 5398830306, 0] := by
  rw [show D2M8K2.u15674 = KTree.node D2M8K2.t15680 (nat_lit 34098971) (nat_lit 2800672021) (nat_lit 0) D2M8K2.t15681 from rfl, totK_node, tot15680, tot15681]
  decide +kernel

theorem arows15675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15675 = true := by
  rw [show D2M8K2.u15675 = KTree.node D2M8K2.t15682 (nat_lit 34101509) (nat_lit 2164444776) (nat_lit 0) D2M8K2.t15683 from rfl, allE_node, rows15682, irow15675, rows15683]
  all_goals rfl

theorem atot15675 : totK PD2M8K2 D2M8K2.u15675 = [0, 0, 324303160659, 929482243675, 515339762761, 30486500788, 0, 0] := by
  rw [show D2M8K2.u15675 = KTree.node D2M8K2.t15682 (nat_lit 34101509) (nat_lit 2164444776) (nat_lit 0) D2M8K2.t15683 from rfl, totK_node, tot15682, tot15683]
  decide +kernel

theorem arows15677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15677 = true := by
  rw [show D2M8K2.u15677 = KTree.node D2M8K2.t15684 (nat_lit 34103883) (nat_lit 1692896980) (nat_lit 0) D2M8K2.t15685 from rfl, allE_node, rows15684, irow15677, rows15685]
  all_goals rfl

theorem atot15677 : totK PD2M8K2 D2M8K2.u15677 = [0, 0, 223966816933, 770705668029, 693796603824, 92651518326, 1198073392, 0] := by
  rw [show D2M8K2.u15677 = KTree.node D2M8K2.t15684 (nat_lit 34103883) (nat_lit 1692896980) (nat_lit 0) D2M8K2.t15685 from rfl, totK_node, tot15684, tot15685]
  decide +kernel

theorem arows15678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15678 = true := by
  rw [show D2M8K2.u15678 = KTree.node D2M8K2.t15686 (nat_lit 34105628) (nat_lit 3204296228) (nat_lit 0) D2M8K2.t15687 from rfl, allE_node, rows15686, irow15678, rows15687]
  all_goals rfl

theorem atot15678 : totK PD2M8K2 D2M8K2.u15678 = [0, 0, 151655187399, 751455083399, 750039926310, 88039905894, 1096505104, 0] := by
  rw [show D2M8K2.u15678 = KTree.node D2M8K2.t15686 (nat_lit 34105628) (nat_lit 3204296228) (nat_lit 0) D2M8K2.t15687 from rfl, totK_node, tot15686, tot15687]
  decide +kernel

theorem arows15681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15681 = true := by
  rw [show D2M8K2.u15681 = KTree.node D2M8K2.t15688 (nat_lit 34107881) (nat_lit 1797739736) (nat_lit 0) D2M8K2.t15689 from rfl, allE_node, rows15688, irow15681, rows15689]
  all_goals rfl

theorem atot15681 : totK PD2M8K2 D2M8K2.u15681 = [0, 0, 391315527012, 939132498675, 470396385366, 28712846084, 0, 0] := by
  rw [show D2M8K2.u15681 = KTree.node D2M8K2.t15688 (nat_lit 34107881) (nat_lit 1797739736) (nat_lit 0) D2M8K2.t15689 from rfl, totK_node, tot15688, tot15689]
  decide +kernel

theorem arows15682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15682 = true := by
  rw [show D2M8K2.u15682 = KTree.node D2M8K2.t15690 (nat_lit 34109580) (nat_lit 3444227702) (nat_lit 0) D2M8K2.t15691 from rfl, allE_node, rows15690, irow15682, rows15691]
  all_goals rfl

theorem atot15682 : totK PD2M8K2 D2M8K2.u15682 = [0, 0, 23716108948, 553241947727, 961788262035, 247070815325, 6161573843, 0] := by
  rw [show D2M8K2.u15682 = KTree.node D2M8K2.t15690 (nat_lit 34109580) (nat_lit 3444227702) (nat_lit 0) D2M8K2.t15691 from rfl, totK_node, tot15690, tot15691]
  decide +kernel

theorem arows15684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15684 = true := by
  rw [show D2M8K2.u15684 = KTree.node D2M8K2.t15692 (nat_lit 34111544) (nat_lit 3826090084) (nat_lit 0) D2M8K2.t15693 from rfl, allE_node, rows15692, irow15684, rows15693]
  all_goals rfl

theorem atot15684 : totK PD2M8K2 D2M8K2.u15684 = [0, 0, 0, 404918492456, 969101036510, 352620309219, 15355272192, 0] := by
  rw [show D2M8K2.u15684 = KTree.node D2M8K2.t15692 (nat_lit 34111544) (nat_lit 3826090084) (nat_lit 0) D2M8K2.t15693 from rfl, totK_node, tot15692, tot15693]
  decide +kernel

theorem arows15685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15685 = true := by
  rw [show D2M8K2.u15685 = KTree.node D2M8K2.t15694 (nat_lit 34113387) (nat_lit 1104037181) (nat_lit 512) D2M8K2.t15695 from rfl, allE_node, rows15694, irow15685, rows15695]
  all_goals rfl

theorem atot15685 : totK PD2M8K2 D2M8K2.u15685 = [0, 0, 0, 142740648669, 796595225380, 688312880108, 84224304823, 1275377855] := by
  rw [show D2M8K2.u15685 = KTree.node D2M8K2.t15694 (nat_lit 34113387) (nat_lit 1104037181) (nat_lit 512) D2M8K2.t15695 from rfl, totK_node, tot15694, tot15695]
  decide +kernel

theorem arows15689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15689 = true := by
  rw [show D2M8K2.u15689 = KTree.node D2M8K2.t15696 (nat_lit 34118936) (nat_lit 3608818374) (nat_lit 0) D2M8K2.t15697 from rfl, allE_node, rows15696, irow15689, rows15697]
  all_goals rfl

theorem atot15689 : totK PD2M8K2 D2M8K2.u15689 = [0, 0, 0, 377033229926, 972249488181, 381171356475, 16912216445, 0] := by
  rw [show D2M8K2.u15689 = KTree.node D2M8K2.t15696 (nat_lit 34118936) (nat_lit 3608818374) (nat_lit 0) D2M8K2.t15697 from rfl, totK_node, tot15696, tot15697]
  decide +kernel

theorem arows15690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15690 = true := by
  rw [show D2M8K2.u15690 = KTree.node D2M8K2.t15698 (nat_lit 34124700) (nat_lit 3440667728) (nat_lit 0) D2M8K2.t15699 from rfl, allE_node, rows15698, irow15690, rows15699]
  all_goals rfl

theorem atot15690 : totK PD2M8K2 D2M8K2.u15690 = [0, 0, 0, 573018494154, 982467521466, 206615015581, 2518061560, 0] := by
  rw [show D2M8K2.u15690 = KTree.node D2M8K2.t15698 (nat_lit 34124700) (nat_lit 3440667728) (nat_lit 0) D2M8K2.t15699 from rfl, totK_node, tot15698, tot15699]
  decide +kernel

theorem arows15692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15692 = true := by
  rw [show D2M8K2.u15692 = KTree.node D2M8K2.t15700 (nat_lit 34128614) (nat_lit 4048245895) (nat_lit 0) D2M8K2.t15701 from rfl, allE_node, rows15700, irow15692, rows15701]
  all_goals rfl

theorem atot15692 : totK PD2M8K2 D2M8K2.u15692 = [0, 0, 0, 447335822703, 995405110852, 328826255323, 8619042136, 0] := by
  rw [show D2M8K2.u15692 = KTree.node D2M8K2.t15700 (nat_lit 34128614) (nat_lit 4048245895) (nat_lit 0) D2M8K2.t15701 from rfl, totK_node, tot15700, tot15701]
  decide +kernel

theorem arows15693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15693 = true := by
  rw [show D2M8K2.u15693 = KTree.node D2M8K2.t15702 (nat_lit 34135682) (nat_lit 4054250822) (nat_lit 0) D2M8K2.t15703 from rfl, allE_node, rows15702, irow15693, rows15703]
  all_goals rfl

theorem atot15693 : totK PD2M8K2 D2M8K2.u15693 = [0, 0, 351244263953, 896656715333, 516312650642, 72768510852, 6594335571, 0] := by
  rw [show D2M8K2.u15693 = KTree.node D2M8K2.t15702 (nat_lit 34135682) (nat_lit 4054250822) (nat_lit 0) D2M8K2.t15703 from rfl, totK_node, tot15702, tot15703]
  decide +kernel

theorem arows15696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15696 = true := by
  rw [show D2M8K2.u15696 = KTree.node D2M8K2.t15704 (nat_lit 34137214) (nat_lit 3766012543) (nat_lit 0) D2M8K2.t15705 from rfl, allE_node, rows15704, irow15696, rows15705]
  all_goals rfl

theorem atot15696 : totK PD2M8K2 D2M8K2.u15696 = [0, 0, 88995923185, 626634711813, 854162560996, 270541583762, 12064694307, 0] := by
  rw [show D2M8K2.u15696 = KTree.node D2M8K2.t15704 (nat_lit 34137214) (nat_lit 3766012543) (nat_lit 0) D2M8K2.t15705 from rfl, totK_node, tot15704, tot15705]
  decide +kernel

theorem arows15697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15697 = true := by
  rw [show D2M8K2.u15697 = KTree.node D2M8K2.t15706 (nat_lit 34138848) (nat_lit 2746137001) (nat_lit 0) D2M8K2.t15707 from rfl, allE_node, rows15706, irow15697, rows15707]
  all_goals rfl

theorem atot15697 : totK PD2M8K2 D2M8K2.u15697 = [0, 0, 335565930026, 824113502441, 536513771647, 116540327103, 4246544562, 0] := by
  rw [show D2M8K2.u15697 = KTree.node D2M8K2.t15706 (nat_lit 34138848) (nat_lit 2746137001) (nat_lit 0) D2M8K2.t15707 from rfl, totK_node, tot15706, tot15707]
  decide +kernel

theorem arows15699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15699 = true := by
  rw [show D2M8K2.u15699 = KTree.node D2M8K2.t15708 (nat_lit 34140478) (nat_lit 3740136315) (nat_lit 0) D2M8K2.t15709 from rfl, allE_node, rows15708, irow15699, rows15709]
  all_goals rfl

theorem atot15699 : totK PD2M8K2 D2M8K2.u15699 = [0, 0, 87430897285, 692247519096, 867500323708, 169697596072, 4231263225, 0] := by
  rw [show D2M8K2.u15699 = KTree.node D2M8K2.t15708 (nat_lit 34140478) (nat_lit 3740136315) (nat_lit 0) D2M8K2.t15709 from rfl, totK_node, tot15708, tot15709]
  decide +kernel

theorem arows15700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15700 = true := by
  rw [show D2M8K2.u15700 = KTree.node D2M8K2.t15710 (nat_lit 34142935) (nat_lit 2375701447) (nat_lit 0) D2M8K2.t15711 from rfl, allE_node, rows15710, irow15700, rows15711]
  all_goals rfl

theorem atot15700 : totK PD2M8K2 D2M8K2.u15700 = [0, 0, 437276916060, 947505208425, 445627482246, 42219654824, 0, 0] := by
  rw [show D2M8K2.u15700 = KTree.node D2M8K2.t15710 (nat_lit 34142935) (nat_lit 2375701447) (nat_lit 0) D2M8K2.t15711 from rfl, totK_node, tot15710, tot15711]
  decide +kernel

theorem arows15705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15705 = true := by
  rw [show D2M8K2.u15705 = KTree.node D2M8K2.t15712 (nat_lit 34146270) (nat_lit 3872392788) (nat_lit 0) D2M8K2.t15713 from rfl, allE_node, rows15712, irow15705, rows15713]
  all_goals rfl

theorem atot15705 : totK PD2M8K2 D2M8K2.u15705 = [0, 0, 414299630447, 965444246684, 431651212009, 34627781413, 0, 0] := by
  rw [show D2M8K2.u15705 = KTree.node D2M8K2.t15712 (nat_lit 34146270) (nat_lit 3872392788) (nat_lit 0) D2M8K2.t15713 from rfl, totK_node, tot15712, tot15713]
  decide +kernel

theorem arows15706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15706 = true := by
  rw [show D2M8K2.u15706 = KTree.node D2M8K2.t15714 (nat_lit 34149722) (nat_lit 4038554353) (nat_lit 0) D2M8K2.t15715 from rfl, allE_node, rows15714, irow15706, rows15715]
  all_goals rfl

theorem atot15706 : totK PD2M8K2 D2M8K2.u15706 = [0, 0, 278731346134, 878268860122, 623275714095, 62991157286, 0, 0] := by
  rw [show D2M8K2.u15706 = KTree.node D2M8K2.t15714 (nat_lit 34149722) (nat_lit 4038554353) (nat_lit 0) D2M8K2.t15715 from rfl, totK_node, tot15714, tot15715]
  decide +kernel

theorem arows15708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15708 = true := by
  rw [show D2M8K2.u15708 = KTree.node D2M8K2.t15716 (nat_lit 34151954) (nat_lit 4013705916) (nat_lit 0) D2M8K2.t15717 from rfl, allE_node, rows15716, irow15708, rows15717]
  all_goals rfl

theorem atot15708 : totK PD2M8K2 D2M8K2.u15708 = [0, 0, 156837995044, 646931838617, 773515022164, 231102505939, 12601510150, 0] := by
  rw [show D2M8K2.u15708 = KTree.node D2M8K2.t15716 (nat_lit 34151954) (nat_lit 4013705916) (nat_lit 0) D2M8K2.t15717 from rfl, totK_node, tot15716, tot15717]
  decide +kernel

theorem arows15709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15709 = true := by
  rw [show D2M8K2.u15709 = KTree.node D2M8K2.t15718 (nat_lit 34174282) (nat_lit 3107158388) (nat_lit 0) D2M8K2.t15719 from rfl, allE_node, rows15718, irow15709, rows15719]
  all_goals rfl

theorem atot15709 : totK PD2M8K2 D2M8K2.u15709 = [0, 0, 253301965531, 808229668819, 585004914932, 82750619565, 1334361349, 0] := by
  rw [show D2M8K2.u15709 = KTree.node D2M8K2.t15718 (nat_lit 34174282) (nat_lit 3107158388) (nat_lit 0) D2M8K2.t15719 from rfl, totK_node, tot15718, tot15719]
  decide +kernel

theorem arows15712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15712 = true := by
  rw [show D2M8K2.u15712 = KTree.node D2M8K2.t15720 (nat_lit 34176705) (nat_lit 1828015520) (nat_lit 0) D2M8K2.t15721 from rfl, allE_node, rows15720, irow15712, rows15721]
  all_goals rfl

theorem atot15712 : totK PD2M8K2 D2M8K2.u15712 = [0, 0, 182254765775, 774125915647, 777451436207, 85886358600, 0, 0] := by
  rw [show D2M8K2.u15712 = KTree.node D2M8K2.t15720 (nat_lit 34176705) (nat_lit 1828015520) (nat_lit 0) D2M8K2.t15721 from rfl, totK_node, tot15720, tot15721]
  decide +kernel

theorem arows15713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15713 = true := by
  rw [show D2M8K2.u15713 = KTree.node D2M8K2.t15722 (nat_lit 34177975) (nat_lit 1240050642) (nat_lit 0) D2M8K2.t15723 from rfl, allE_node, rows15722, irow15713, rows15723]
  all_goals rfl

theorem atot15713 : totK PD2M8K2 D2M8K2.u15713 = [0, 0, 237517231656, 764411150115, 657407284427, 162059662053, 10165445843, 0] := by
  rw [show D2M8K2.u15713 = KTree.node D2M8K2.t15722 (nat_lit 34177975) (nat_lit 1240050642) (nat_lit 0) D2M8K2.t15723 from rfl, totK_node, tot15722, tot15723]
  decide +kernel

theorem arows15715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15715 = true := by
  rw [show D2M8K2.u15715 = KTree.node D2M8K2.t15724 (nat_lit 34179888) (nat_lit 3618816864) (nat_lit 0) D2M8K2.t15725 from rfl, allE_node, rows15724, irow15715, rows15725]
  all_goals rfl

theorem atot15715 : totK PD2M8K2 D2M8K2.u15715 = [0, 0, 212464921445, 721802070910, 700822207930, 189068002979, 5675387547, 0] := by
  rw [show D2M8K2.u15715 = KTree.node D2M8K2.t15724 (nat_lit 34179888) (nat_lit 3618816864) (nat_lit 0) D2M8K2.t15725 from rfl, totK_node, tot15724, tot15725]
  decide +kernel

theorem arows15716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15716 = true := by
  rw [show D2M8K2.u15716 = KTree.node D2M8K2.t15726 (nat_lit 34181331) (nat_lit 3634743472) (nat_lit 0) D2M8K2.t15727 from rfl, allE_node, rows15726, irow15716, rows15727]
  all_goals rfl

theorem atot15716 : totK PD2M8K2 D2M8K2.u15716 = [0, 0, 231607206120, 802715994339, 671759016686, 101679595557, 1164319620, 0] := by
  rw [show D2M8K2.u15716 = KTree.node D2M8K2.t15726 (nat_lit 34181331) (nat_lit 3634743472) (nat_lit 0) D2M8K2.t15727 from rfl, totK_node, tot15726, tot15727]
  decide +kernel

theorem arows15720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15720 = true := by
  rw [show D2M8K2.u15720 = KTree.node D2M8K2.t15728 (nat_lit 34183016) (nat_lit 2414105362) (nat_lit 0) D2M8K2.t15729 from rfl, allE_node, rows15728, irow15720, rows15729]
  all_goals rfl

theorem atot15720 : totK PD2M8K2 D2M8K2.u15720 = [0, 0, 166775602658, 647545958854, 735890669927, 218306176046, 11885407614, 0] := by
  rw [show D2M8K2.u15720 = KTree.node D2M8K2.t15728 (nat_lit 34183016) (nat_lit 2414105362) (nat_lit 0) D2M8K2.t15729 from rfl, totK_node, tot15728, tot15729]
  decide +kernel

theorem arows15721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15721 = true := by
  rw [show D2M8K2.u15721 = KTree.node D2M8K2.t15730 (nat_lit 34187947) (nat_lit 1781826841) (nat_lit 0) D2M8K2.t15731 from rfl, allE_node, rows15730, irow15721, rows15731]
  all_goals rfl

theorem atot15721 : totK PD2M8K2 D2M8K2.u15721 = [0, 0, 228323402236, 779967471722, 658582906016, 85758970341, 1062926506, 0] := by
  rw [show D2M8K2.u15721 = KTree.node D2M8K2.t15730 (nat_lit 34187947) (nat_lit 1781826841) (nat_lit 0) D2M8K2.t15731 from rfl, totK_node, tot15730, tot15731]
  decide +kernel

theorem arows15723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15723 = true := by
  rw [show D2M8K2.u15723 = KTree.node D2M8K2.t15732 (nat_lit 34190312) (nat_lit 3635503190) (nat_lit 0) D2M8K2.t15733 from rfl, allE_node, rows15732, irow15723, rows15733]
  all_goals rfl

theorem atot15723 : totK PD2M8K2 D2M8K2.u15723 = [0, 0, 242042716130, 766154701608, 650778299262, 119175091831, 3783381897, 0] := by
  rw [show D2M8K2.u15723 = KTree.node D2M8K2.t15732 (nat_lit 34190312) (nat_lit 3635503190) (nat_lit 0) D2M8K2.t15733 from rfl, totK_node, tot15732, tot15733]
  decide +kernel

theorem arows15724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15724 = true := by
  rw [show D2M8K2.u15724 = KTree.node D2M8K2.t15734 (nat_lit 34191827) (nat_lit 2892753708) (nat_lit 0) D2M8K2.t15735 from rfl, allE_node, rows15734, irow15724, rows15735]
  all_goals rfl

theorem atot15724 : totK PD2M8K2 D2M8K2.u15724 = [0, 0, 179255141055, 756115729877, 745524984648, 120068457724, 1240621948, 0] := by
  rw [show D2M8K2.u15724 = KTree.node D2M8K2.t15734 (nat_lit 34191827) (nat_lit 2892753708) (nat_lit 0) D2M8K2.t15735 from rfl, totK_node, tot15734, tot15735]
  decide +kernel

theorem arows15727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15727 = true := by
  rw [show D2M8K2.u15727 = KTree.node D2M8K2.t15736 (nat_lit 34193664) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t15737 from rfl, allE_node, rows15736, irow15727, rows15737]
  all_goals rfl

theorem atot15727 : totK PD2M8K2 D2M8K2.u15727 = [0, 0, 0, 405148023108, 971291979802, 382922127491, 18104977176, 0] := by
  rw [show D2M8K2.u15727 = KTree.node D2M8K2.t15736 (nat_lit 34193664) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t15737 from rfl, totK_node, tot15736, tot15737]
  decide +kernel

theorem arows15728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15728 = true := by
  rw [show D2M8K2.u15728 = KTree.node D2M8K2.t15738 (nat_lit 34195320) (nat_lit 3402329986) (nat_lit 0) D2M8K2.t15739 from rfl, allE_node, rows15738, irow15728, rows15739]
  all_goals rfl

theorem atot15728 : totK PD2M8K2 D2M8K2.u15728 = [0, 0, 0, 191309187276, 797491746773, 601358985416, 75548993851, 1206465782] := by
  rw [show D2M8K2.u15728 = KTree.node D2M8K2.t15738 (nat_lit 34195320) (nat_lit 3402329986) (nat_lit 0) D2M8K2.t15739 from rfl, totK_node, tot15738, tot15739]
  decide +kernel

theorem arows15730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15730 = true := by
  rw [show D2M8K2.u15730 = KTree.node D2M8K2.t15740 (nat_lit 34197838) (nat_lit 4004602945) (nat_lit 0) D2M8K2.t15741 from rfl, allE_node, rows15740, irow15730, rows15741]
  all_goals rfl

theorem atot15730 : totK PD2M8K2 D2M8K2.u15730 = [0, 0, 0, 431579811959, 939523325017, 428348035171, 27969627404, 0] := by
  rw [show D2M8K2.u15730 = KTree.node D2M8K2.t15740 (nat_lit 34197838) (nat_lit 4004602945) (nat_lit 0) D2M8K2.t15741 from rfl, totK_node, tot15740, tot15741]
  decide +kernel

theorem arows15731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15731 = true := by
  rw [show D2M8K2.u15731 = KTree.node D2M8K2.t15742 (nat_lit 34201212) (nat_lit 3226978531) (nat_lit 0) D2M8K2.t15743 from rfl, allE_node, rows15742, irow15731, rows15743]
  all_goals rfl

theorem atot15731 : totK PD2M8K2 D2M8K2.u15731 = [0, 0, 0, 397294947881, 960674128952, 407786422619, 23753849909, 0] := by
  rw [show D2M8K2.u15731 = KTree.node D2M8K2.t15742 (nat_lit 34201212) (nat_lit 3226978531) (nat_lit 0) D2M8K2.t15743 from rfl, totK_node, tot15742, tot15743]
  decide +kernel

theorem arows15738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15738 = true := by
  rw [show D2M8K2.u15738 = KTree.node D2M8K2.t15744 (nat_lit 34202939) (nat_lit 2775994901) (nat_lit 0) D2M8K2.t15745 from rfl, allE_node, rows15744, irow15738, rows15745]
  all_goals rfl

theorem atot15738 : totK PD2M8K2 D2M8K2.u15738 = [0, 0, 0, 96637508575, 651512394810, 806175024876, 178315425585, 5395128787] := by
  rw [show D2M8K2.u15738 = KTree.node D2M8K2.t15744 (nat_lit 34202939) (nat_lit 2775994901) (nat_lit 0) D2M8K2.t15745 from rfl, totK_node, tot15744, tot15745]
  decide +kernel

theorem arows15739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15739 = true := by
  rw [show D2M8K2.u15739 = KTree.node D2M8K2.t15746 (nat_lit 34208656) (nat_lit 3337058040) (nat_lit 0) D2M8K2.t15747 from rfl, allE_node, rows15746, irow15739, rows15747]
  all_goals rfl

theorem atot15739 : totK PD2M8K2 D2M8K2.u15739 = [0, 0, 0, 448859387834, 953137774449, 326295383803, 12757919886, 0] := by
  rw [show D2M8K2.u15739 = KTree.node D2M8K2.t15746 (nat_lit 34208656) (nat_lit 3337058040) (nat_lit 0) D2M8K2.t15747 from rfl, totK_node, tot15746, tot15747]
  decide +kernel

theorem arows15741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15741 = true := by
  rw [show D2M8K2.u15741 = KTree.node D2M8K2.t15748 (nat_lit 34212415) (nat_lit 2110505063) (nat_lit 0) D2M8K2.t15749 from rfl, allE_node, rows15748, irow15741, rows15749]
  all_goals rfl

theorem atot15741 : totK PD2M8K2 D2M8K2.u15741 = [0, 0, 132970761498, 558429553950, 762615052227, 326912337155, 23452779107, 0] := by
  rw [show D2M8K2.u15741 = KTree.node D2M8K2.t15748 (nat_lit 34212415) (nat_lit 2110505063) (nat_lit 0) D2M8K2.t15749 from rfl, totK_node, tot15748, tot15749]
  decide +kernel

theorem arows15742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15742 = true := by
  rw [show D2M8K2.u15742 = KTree.node D2M8K2.t15750 (nat_lit 34257184) (nat_lit 2351975168) (nat_lit 0) D2M8K2.t15751 from rfl, allE_node, rows15750, irow15742, rows15751]
  all_goals rfl

theorem atot15742 : totK PD2M8K2 D2M8K2.u15742 = [0, 0, 257410602240, 841449189822, 579947528610, 66517718710, 1310166938, 0] := by
  rw [show D2M8K2.u15742 = KTree.node D2M8K2.t15750 (nat_lit 34257184) (nat_lit 2351975168) (nat_lit 0) D2M8K2.t15751 from rfl, totK_node, tot15750, tot15751]
  decide +kernel

theorem arows15745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15745 = true := by
  rw [show D2M8K2.u15745 = KTree.node D2M8K2.t15752 (nat_lit 34259746) (nat_lit 4124201594) (nat_lit 0) D2M8K2.t15753 from rfl, allE_node, rows15752, irow15745, rows15753]
  all_goals rfl

theorem atot15745 : totK PD2M8K2 D2M8K2.u15745 = [0, 0, 270038425602, 837857433190, 661715234738, 59632491143, 0, 0] := by
  rw [show D2M8K2.u15745 = KTree.node D2M8K2.t15752 (nat_lit 34259746) (nat_lit 4124201594) (nat_lit 0) D2M8K2.t15753 from rfl, totK_node, tot15752, tot15753]
  decide +kernel

theorem arows15746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15746 = true := by
  rw [show D2M8K2.u15746 = KTree.node D2M8K2.t15754 (nat_lit 34263104) (nat_lit 3775447650) (nat_lit 0) D2M8K2.t15755 from rfl, allE_node, rows15754, irow15746, rows15755]
  all_goals rfl

theorem atot15746 : totK PD2M8K2 D2M8K2.u15746 = [0, 0, 403706457098, 958611223443, 436771243228, 25193285449, 0, 0] := by
  rw [show D2M8K2.u15746 = KTree.node D2M8K2.t15754 (nat_lit 34263104) (nat_lit 3775447650) (nat_lit 0) D2M8K2.t15755 from rfl, totK_node, tot15754, tot15755]
  decide +kernel

theorem arows15748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15748 = true := by
  rw [show D2M8K2.u15748 = KTree.node D2M8K2.t15756 (nat_lit 34264612) (nat_lit 3726738556) (nat_lit 0) D2M8K2.t15757 from rfl, allE_node, rows15756, irow15748, rows15757]
  all_goals rfl

theorem atot15748 : totK PD2M8K2 D2M8K2.u15748 = [0, 0, 148720334287, 740316951665, 770421580625, 113677236821, 2145173282, 0] := by
  rw [show D2M8K2.u15748 = KTree.node D2M8K2.t15756 (nat_lit 34264612) (nat_lit 3726738556) (nat_lit 0) D2M8K2.t15757 from rfl, totK_node, tot15756, tot15757]
  decide +kernel

theorem arows15749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15749 = true := by
  rw [show D2M8K2.u15749 = KTree.node D2M8K2.t15758 (nat_lit 34270160) (nat_lit 3729112393) (nat_lit 0) D2M8K2.t15759 from rfl, allE_node, rows15758, irow15749, rows15759]
  all_goals rfl

theorem atot15749 : totK PD2M8K2 D2M8K2.u15749 = [0, 0, 328849365938, 874568974021, 509320753094, 70301643325, 2481160468, 0] := by
  rw [show D2M8K2.u15749 = KTree.node D2M8K2.t15758 (nat_lit 34270160) (nat_lit 3729112393) (nat_lit 0) D2M8K2.t15759 from rfl, totK_node, tot15758, tot15759]
  decide +kernel

theorem arows15753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15753 = true := by
  rw [show D2M8K2.u15753 = KTree.node D2M8K2.t15760 (nat_lit 34271753) (nat_lit 1788976002) (nat_lit 0) D2M8K2.t15761 from rfl, allE_node, rows15760, irow15753, rows15761]
  all_goals rfl

theorem atot15753 : totK PD2M8K2 D2M8K2.u15753 = [0, 0, 92237621127, 671206503588, 856649791047, 147966629493, 2165917952, 0] := by
  rw [show D2M8K2.u15753 = KTree.node D2M8K2.t15760 (nat_lit 34271753) (nat_lit 1788976002) (nat_lit 0) D2M8K2.t15761 from rfl, totK_node, tot15760, tot15761]
  decide +kernel

theorem arows15754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15754 = true := by
  rw [show D2M8K2.u15754 = KTree.node D2M8K2.t15762 (nat_lit 34298218) (nat_lit 3898314748) (nat_lit 0) D2M8K2.t15763 from rfl, allE_node, rows15762, irow15754, rows15763]
  all_goals rfl

theorem atot15754 : totK PD2M8K2 D2M8K2.u15754 = [0, 0, 406766259942, 957257653827, 380049946933, 35919602701, 2814597007, 0] := by
  rw [show D2M8K2.u15754 = KTree.node D2M8K2.t15762 (nat_lit 34298218) (nat_lit 3898314748) (nat_lit 0) D2M8K2.t15763 from rfl, totK_node, tot15762, tot15763]
  decide +kernel

theorem arows15756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15756 = true := by
  rw [show D2M8K2.u15756 = KTree.node D2M8K2.t15764 (nat_lit 34300015) (nat_lit 2446349698) (nat_lit 0) D2M8K2.t15765 from rfl, allE_node, rows15764, irow15756, rows15765]
  all_goals rfl

theorem atot15756 : totK PD2M8K2 D2M8K2.u15756 = [0, 0, 92207005028, 669918263673, 898068824109, 144981018664, 1369150432, 0] := by
  rw [show D2M8K2.u15756 = KTree.node D2M8K2.t15764 (nat_lit 34300015) (nat_lit 2446349698) (nat_lit 0) D2M8K2.t15765 from rfl, totK_node, tot15764, tot15765]
  decide +kernel

theorem arows15757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15757 = true := by
  rw [show D2M8K2.u15757 = KTree.node D2M8K2.t15766 (nat_lit 34301928) (nat_lit 3103300094) (nat_lit 0) D2M8K2.t15767 from rfl, allE_node, rows15766, irow15757, rows15767]
  all_goals rfl

theorem atot15757 : totK PD2M8K2 D2M8K2.u15757 = [0, 0, 324010888332, 917298853447, 560238639002, 49111878768, 0, 0] := by
  rw [show D2M8K2.u15757 = KTree.node D2M8K2.t15766 (nat_lit 34301928) (nat_lit 3103300094) (nat_lit 0) D2M8K2.t15767 from rfl, totK_node, tot15766, tot15767]
  decide +kernel

theorem arows15760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15760 = true := by
  rw [show D2M8K2.u15760 = KTree.node D2M8K2.t15768 (nat_lit 34303733) (nat_lit 2367862426) (nat_lit 0) D2M8K2.t15769 from rfl, allE_node, rows15768, irow15760, rows15769]
  all_goals rfl

theorem atot15760 : totK PD2M8K2 D2M8K2.u15760 = [0, 0, 104100811831, 575713851432, 829361598149, 301724815047, 16311238869, 0] := by
  rw [show D2M8K2.u15760 = KTree.node D2M8K2.t15768 (nat_lit 34303733) (nat_lit 2367862426) (nat_lit 0) D2M8K2.t15769 from rfl, totK_node, tot15768, tot15769]
  decide +kernel

theorem arows15761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15761 = true := by
  rw [show D2M8K2.u15761 = KTree.node D2M8K2.t15770 (nat_lit 34305408) (nat_lit 3661299556) (nat_lit 0) D2M8K2.t15771 from rfl, allE_node, rows15770, irow15761, rows15771]
  all_goals rfl

theorem atot15761 : totK PD2M8K2 D2M8K2.u15761 = [0, 0, 318176078109, 888704951903, 549211677743, 52986853986, 0, 0] := by
  rw [show D2M8K2.u15761 = KTree.node D2M8K2.t15770 (nat_lit 34305408) (nat_lit 3661299556) (nat_lit 0) D2M8K2.t15771 from rfl, totK_node, tot15770, tot15771]
  decide +kernel

theorem arows15763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15763 = true := by
  rw [show D2M8K2.u15763 = KTree.node D2M8K2.t15772 (nat_lit 34306826) (nat_lit 3710843661) (nat_lit 0) D2M8K2.t15773 from rfl, allE_node, rows15772, irow15763, rows15773]
  all_goals rfl

theorem atot15763 : totK PD2M8K2 D2M8K2.u15763 = [0, 0, 114819131042, 624961466033, 837148427374, 208615361546, 7832068735, 0] := by
  rw [show D2M8K2.u15763 = KTree.node D2M8K2.t15772 (nat_lit 34306826) (nat_lit 3710843661) (nat_lit 0) D2M8K2.t15773 from rfl, totK_node, tot15772, tot15773]
  decide +kernel

theorem arows15764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15764 = true := by
  rw [show D2M8K2.u15764 = KTree.node D2M8K2.t15774 (nat_lit 34309204) (nat_lit 3921999773) (nat_lit 0) D2M8K2.t15775 from rfl, allE_node, rows15774, irow15764, rows15775]
  all_goals rfl

theorem atot15764 : totK PD2M8K2 D2M8K2.u15764 = [0, 0, 228466748499, 791333543991, 707533505252, 108184815772, 1198073392, 0] := by
  rw [show D2M8K2.u15764 = KTree.node D2M8K2.t15774 (nat_lit 34309204) (nat_lit 3921999773) (nat_lit 0) D2M8K2.t15775 from rfl, totK_node, tot15774, tot15775]
  decide +kernel

theorem arows15769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15769 = true := by
  rw [show D2M8K2.u15769 = KTree.node D2M8K2.t15776 (nat_lit 34314788) (nat_lit 2629442137) (nat_lit 0) D2M8K2.t15777 from rfl, allE_node, rows15776, irow15769, rows15777]
  all_goals rfl

theorem atot15769 : totK PD2M8K2 D2M8K2.u15769 = [0, 0, 263433262802, 788443239404, 643300560194, 125352194526, 4030866388, 0] := by
  rw [show D2M8K2.u15769 = KTree.node D2M8K2.t15776 (nat_lit 34314788) (nat_lit 2629442137) (nat_lit 0) D2M8K2.t15777 from rfl, totK_node, tot15776, tot15777]
  decide +kernel

theorem arows15770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15770 = true := by
  rw [show D2M8K2.u15770 = KTree.node D2M8K2.t15778 (nat_lit 34316269) (nat_lit 1053231265) (nat_lit 0) D2M8K2.t15779 from rfl, allE_node, rows15778, irow15770, rows15779]
  all_goals rfl

theorem atot15770 : totK PD2M8K2 D2M8K2.u15770 = [0, 0, 178308376453, 752802367081, 756902846261, 134262582258, 1268739303, 0] := by
  rw [show D2M8K2.u15770 = KTree.node D2M8K2.t15778 (nat_lit 34316269) (nat_lit 1053231265) (nat_lit 0) D2M8K2.t15779 from rfl, totK_node, tot15778, tot15779]
  decide +kernel

theorem arows15772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15772 = true := by
  rw [show D2M8K2.u15772 = KTree.node D2M8K2.t15780 (nat_lit 34317945) (nat_lit 999305339) (nat_lit 0) D2M8K2.t15781 from rfl, allE_node, rows15780, irow15772, rows15781]
  all_goals rfl

theorem atot15772 : totK PD2M8K2 D2M8K2.u15772 = [0, 173658224399, 390247151006, 337831033751, 569505290344, 285451027267, 20713713085, 0] := by
  rw [show D2M8K2.u15772 = KTree.node D2M8K2.t15780 (nat_lit 34317945) (nat_lit 999305339) (nat_lit 0) D2M8K2.t15781 from rfl, totK_node, tot15780, tot15781]
  decide +kernel

theorem arows15773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15773 = true := by
  rw [show D2M8K2.u15773 = KTree.node D2M8K2.t15782 (nat_lit 34340190) (nat_lit 3968912540) (nat_lit 0) D2M8K2.t15783 from rfl, allE_node, rows15782, irow15773, rows15783]
  all_goals rfl

theorem atot15773 : totK PD2M8K2 D2M8K2.u15773 = [0, 259628247390, 799880020706, 621809366684, 102432536106, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15773 = KTree.node D2M8K2.t15782 (nat_lit 34340190) (nat_lit 3968912540) (nat_lit 0) D2M8K2.t15783 from rfl, totK_node, tot15782, tot15783]
  decide +kernel

theorem arows15776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15776 = true := by
  rw [show D2M8K2.u15776 = KTree.node D2M8K2.t15784 (nat_lit 34342111) (nat_lit 2232449313) (nat_lit 0) D2M8K2.t15785 from rfl, allE_node, rows15784, irow15776, rows15785]
  all_goals rfl

theorem atot15776 : totK PD2M8K2 D2M8K2.u15776 = [0, 205522976420, 812151087904, 717196272057, 78254380137, 0, 0, 0] := by
  rw [show D2M8K2.u15776 = KTree.node D2M8K2.t15784 (nat_lit 34342111) (nat_lit 2232449313) (nat_lit 0) D2M8K2.t15785 from rfl, totK_node, tot15784, tot15785]
  decide +kernel

theorem arows15777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15777 = true := by
  rw [show D2M8K2.u15777 = KTree.node D2M8K2.t15786 (nat_lit 34347592) (nat_lit 3648899999) (nat_lit 0) D2M8K2.t15787 from rfl, allE_node, rows15786, irow15777, rows15787]
  all_goals rfl

theorem atot15777 : totK PD2M8K2 D2M8K2.u15777 = [0, 119573466220, 654410602487, 816530972011, 186335482450, 5398830306, 0, 0] := by
  rw [show D2M8K2.u15777 = KTree.node D2M8K2.t15786 (nat_lit 34347592) (nat_lit 3648899999) (nat_lit 0) D2M8K2.t15787 from rfl, totK_node, tot15786, tot15787]
  decide +kernel

theorem arows15779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15779 = true := by
  rw [show D2M8K2.u15779 = KTree.node D2M8K2.t15788 (nat_lit 34350075) (nat_lit 3723772572) (nat_lit 0) D2M8K2.t15789 from rfl, allE_node, rows15788, irow15779, rows15789]
  all_goals rfl

theorem atot15779 : totK PD2M8K2 D2M8K2.u15779 = [0, 371275942680, 923057710038, 478744624610, 40063567094, 0, 0, 0] := by
  rw [show D2M8K2.u15779 = KTree.node D2M8K2.t15788 (nat_lit 34350075) (nat_lit 3723772572) (nat_lit 0) D2M8K2.t15789 from rfl, totK_node, tot15788, tot15789]
  decide +kernel

theorem arows15780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15780 = true := by
  rw [show D2M8K2.u15780 = KTree.node D2M8K2.t15790 (nat_lit 34351321) (nat_lit 1217640296) (nat_lit 0) D2M8K2.t15791 from rfl, allE_node, rows15790, irow15780, rows15791]
  all_goals rfl

theorem atot15780 : totK PD2M8K2 D2M8K2.u15780 = [0, 52184351020, 516339437962, 897649560911, 287748583021, 13250685261, 0, 0] := by
  rw [show D2M8K2.u15780 = KTree.node D2M8K2.t15790 (nat_lit 34351321) (nat_lit 1217640296) (nat_lit 0) D2M8K2.t15791 from rfl, totK_node, tot15790, tot15791]
  decide +kernel

theorem arows15784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15784 = true := by
  rw [show D2M8K2.u15784 = KTree.node D2M8K2.t15792 (nat_lit 34353184) (nat_lit 2807242870) (nat_lit 0) D2M8K2.t15793 from rfl, allE_node, rows15792, irow15784, rows15793]
  all_goals rfl

theorem atot15784 : totK PD2M8K2 D2M8K2.u15784 = [0, 339173504810, 876750844061, 527376961937, 54399574934, 0, 0, 0] := by
  rw [show D2M8K2.u15784 = KTree.node D2M8K2.t15792 (nat_lit 34353184) (nat_lit 2807242870) (nat_lit 0) D2M8K2.t15793 from rfl, totK_node, tot15792, tot15793]
  decide +kernel

theorem arows15785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15785 = true := by
  rw [show D2M8K2.u15785 = KTree.node D2M8K2.t15794 (nat_lit 34355014) (nat_lit 3174520549) (nat_lit 0) D2M8K2.t15795 from rfl, allE_node, rows15794, irow15785, rows15795]
  all_goals rfl

theorem atot15785 : totK PD2M8K2 D2M8K2.u15785 = [0, 105937677505, 640250316579, 836557088320, 181512375388, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15785 = KTree.node D2M8K2.t15794 (nat_lit 34355014) (nat_lit 3174520549) (nat_lit 0) D2M8K2.t15795 from rfl, totK_node, tot15794, tot15795]
  decide +kernel

theorem arows15787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15787 = true := by
  rw [show D2M8K2.u15787 = KTree.node D2M8K2.t15796 (nat_lit 34356872) (nat_lit 3230085299) (nat_lit 0) D2M8K2.t15797 from rfl, allE_node, rows15796, irow15787, rows15797]
  all_goals rfl

theorem atot15787 : totK PD2M8K2 D2M8K2.u15787 = [0, 347849501403, 925846782816, 514697869505, 39626886728, 0, 0, 0] := by
  rw [show D2M8K2.u15787 = KTree.node D2M8K2.t15796 (nat_lit 34356872) (nat_lit 3230085299) (nat_lit 0) D2M8K2.t15797 from rfl, totK_node, tot15796, tot15797]
  decide +kernel

theorem arows15788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15788 = true := by
  rw [show D2M8K2.u15788 = KTree.node D2M8K2.t15798 (nat_lit 34358543) (nat_lit 2771375578) (nat_lit 0) D2M8K2.t15799 from rfl, allE_node, rows15798, irow15788, rows15799]
  all_goals rfl

theorem atot15788 : totK PD2M8K2 D2M8K2.u15788 = [0, 0, 447853289058, 988281314532, 337401045735, 9938656398, 0, 0] := by
  rw [show D2M8K2.u15788 = KTree.node D2M8K2.t15798 (nat_lit 34358543) (nat_lit 2771375578) (nat_lit 0) D2M8K2.t15799 from rfl, totK_node, tot15798, tot15799]
  decide +kernel

theorem arows15791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15791 = true := by
  rw [show D2M8K2.u15791 = KTree.node D2M8K2.t15800 (nat_lit 34360377) (nat_lit 1849974107) (nat_lit 0) D2M8K2.t15801 from rfl, allE_node, rows15800, irow15791, rows15801]
  all_goals rfl

theorem atot15791 : totK PD2M8K2 D2M8K2.u15791 = [0, 0, 362257667799, 917206870964, 435183788971, 29845082488, 0, 0] := by
  rw [show D2M8K2.u15791 = KTree.node D2M8K2.t15800 (nat_lit 34360377) (nat_lit 1849974107) (nat_lit 0) D2M8K2.t15801 from rfl, totK_node, tot15800, tot15801]
  decide +kernel

theorem arows15792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15792 = true := by
  rw [show D2M8K2.u15792 = KTree.node D2M8K2.t15802 (nat_lit 34361909) (nat_lit 2399141089) (nat_lit 0) D2M8K2.t15803 from rfl, allE_node, rows15802, irow15792, rows15803]
  all_goals rfl

theorem atot15792 : totK PD2M8K2 D2M8K2.u15792 = [0, 0, 120928381984, 702815249828, 776040433568, 132631463899, 1369150432, 0] := by
  rw [show D2M8K2.u15792 = KTree.node D2M8K2.t15802 (nat_lit 34361909) (nat_lit 2399141089) (nat_lit 0) D2M8K2.t15803 from rfl, totK_node, tot15802, tot15803]
  decide +kernel

theorem arows15794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15794 = true := by
  rw [show D2M8K2.u15794 = KTree.node D2M8K2.t15804 (nat_lit 34367808) (nat_lit 3390458902) (nat_lit 0) D2M8K2.t15805 from rfl, allE_node, rows15804, irow15794, rows15805]
  all_goals rfl

theorem atot15794 : totK PD2M8K2 D2M8K2.u15794 = [0, 0, 367604921136, 973217936807, 425064991399, 16866285330, 0, 0] := by
  rw [show D2M8K2.u15794 = KTree.node D2M8K2.t15804 (nat_lit 34367808) (nat_lit 3390458902) (nat_lit 0) D2M8K2.t15805 from rfl, totK_node, tot15804, tot15805]
  decide +kernel

theorem arows15795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15795 = true := by
  rw [show D2M8K2.u15795 = KTree.node D2M8K2.t15806 (nat_lit 34371121) (nat_lit 1439892271) (nat_lit 0) D2M8K2.t15807 from rfl, allE_node, rows15806, irow15795, rows15807]
  all_goals rfl

theorem atot15795 : totK PD2M8K2 D2M8K2.u15795 = [0, 0, 383600356918, 935270292583, 434896382224, 25275037740, 0, 0] := by
  rw [show D2M8K2.u15795 = KTree.node D2M8K2.t15806 (nat_lit 34371121) (nat_lit 1439892271) (nat_lit 0) D2M8K2.t15807 from rfl, totK_node, tot15806, tot15807]
  decide +kernel

theorem arows15801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15801 = true := by
  rw [show D2M8K2.u15801 = KTree.node D2M8K2.t15808 (nat_lit 34374325) (nat_lit 1255139825) (nat_lit 0) D2M8K2.t15809 from rfl, allE_node, rows15808, irow15801, rows15809]
  all_goals rfl

theorem atot15801 : totK PD2M8K2 D2M8K2.u15801 = [0, 0, 382335895110, 964552204135, 397783427148, 16324572484, 0, 0] := by
  rw [show D2M8K2.u15801 = KTree.node D2M8K2.t15808 (nat_lit 34374325) (nat_lit 1255139825) (nat_lit 0) D2M8K2.t15809 from rfl, totK_node, tot15808, tot15809]
  decide +kernel

theorem arows15802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15802 = true := by
  rw [show D2M8K2.u15802 = KTree.node D2M8K2.t15810 (nat_lit 34377614) (nat_lit 2469624565) (nat_lit 0) D2M8K2.t15811 from rfl, allE_node, rows15810, irow15802, rows15811]
  all_goals rfl

theorem atot15802 : totK PD2M8K2 D2M8K2.u15802 = [0, 0, 347433818470, 952995012932, 483465223996, 22620818871, 0, 0] := by
  rw [show D2M8K2.u15802 = KTree.node D2M8K2.t15810 (nat_lit 34377614) (nat_lit 2469624565) (nat_lit 0) D2M8K2.t15811 from rfl, totK_node, tot15810, tot15811]
  decide +kernel

theorem arows15804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15804 = true := by
  rw [show D2M8K2.u15804 = KTree.node D2M8K2.t15812 (nat_lit 34384564) (nat_lit 3816165285) (nat_lit 0) D2M8K2.t15813 from rfl, allE_node, rows15812, irow15804, rows15813]
  all_goals rfl

theorem atot15804 : totK PD2M8K2 D2M8K2.u15804 = [0, 353558437555, 907628222956, 509702571688, 65935678121, 7093008096, 0, 0] := by
  rw [show D2M8K2.u15804 = KTree.node D2M8K2.t15812 (nat_lit 34384564) (nat_lit 3816165285) (nat_lit 0) D2M8K2.t15813 from rfl, totK_node, tot15812, tot15813]
  decide +kernel

theorem arows15805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15805 = true := by
  rw [show D2M8K2.u15805 = KTree.node D2M8K2.t15814 (nat_lit 34386009) (nat_lit 1812084107) (nat_lit 0) D2M8K2.t15815 from rfl, allE_node, rows15814, irow15805, rows15815]
  all_goals rfl

theorem atot15805 : totK PD2M8K2 D2M8K2.u15805 = [0, 89061927447, 508120194011, 822354321391, 372854520846, 29394892645, 0, 0] := by
  rw [show D2M8K2.u15805 = KTree.node D2M8K2.t15814 (nat_lit 34386009) (nat_lit 1812084107) (nat_lit 0) D2M8K2.t15815 from rfl, totK_node, tot15814, tot15815]
  decide +kernel

theorem arows15808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15808 = true := by
  rw [show D2M8K2.u15808 = KTree.node D2M8K2.t15816 (nat_lit 34387563) (nat_lit 3704435322) (nat_lit 0) D2M8K2.t15817 from rfl, allE_node, rows15816, irow15808, rows15817]
  all_goals rfl

theorem atot15808 : totK PD2M8K2 D2M8K2.u15808 = [0, 214545600531, 673245111061, 723782498022, 225470689408, 8214505460, 0, 0] := by
  rw [show D2M8K2.u15808 = KTree.node D2M8K2.t15816 (nat_lit 34387563) (nat_lit 3704435322) (nat_lit 0) D2M8K2.t15817 from rfl, totK_node, tot15816, tot15817]
  decide +kernel

theorem arows15809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15809 = true := by
  rw [show D2M8K2.u15809 = KTree.node D2M8K2.t15818 (nat_lit 34389505) (nat_lit 1517195302) (nat_lit 0) D2M8K2.t15819 from rfl, allE_node, rows15818, irow15809, rows15819]
  all_goals rfl

theorem atot15809 : totK PD2M8K2 D2M8K2.u15809 = [0, 117142903938, 663918853192, 835495716138, 210711243381, 8302875791, 0, 0] := by
  rw [show D2M8K2.u15809 = KTree.node D2M8K2.t15818 (nat_lit 34389505) (nat_lit 1517195302) (nat_lit 0) D2M8K2.t15819 from rfl, totK_node, tot15818, tot15819]
  decide +kernel

theorem arows15811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15811 = true := by
  rw [show D2M8K2.u15811 = KTree.node D2M8K2.t15820 (nat_lit 34391549) (nat_lit 1703529221) (nat_lit 0) D2M8K2.t15821 from rfl, allE_node, rows15820, irow15811, rows15821]
  all_goals rfl

theorem atot15811 : totK PD2M8K2 D2M8K2.u15811 = [0, 372772434495, 922033004002, 488736460189, 43107051414, 0, 0, 0] := by
  rw [show D2M8K2.u15811 = KTree.node D2M8K2.t15820 (nat_lit 34391549) (nat_lit 1703529221) (nat_lit 0) D2M8K2.t15821 from rfl, totK_node, tot15820, tot15821]
  decide +kernel

theorem arows15812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15812 = true := by
  rw [show D2M8K2.u15812 = KTree.node D2M8K2.t15822 (nat_lit 34392803) (nat_lit 2952665745) (nat_lit 0) D2M8K2.t15823 from rfl, allE_node, rows15822, irow15812, rows15823]
  all_goals rfl

theorem atot15812 : totK PD2M8K2 D2M8K2.u15812 = [0, 52337025351, 525883303962, 895979107053, 284392879722, 13237669976, 0, 0] := by
  rw [show D2M8K2.u15812 = KTree.node D2M8K2.t15822 (nat_lit 34392803) (nat_lit 2952665745) (nat_lit 0) D2M8K2.t15823 from rfl, totK_node, tot15822, tot15823]
  decide +kernel

theorem arows15816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15816 = true := by
  rw [show D2M8K2.u15816 = KTree.node D2M8K2.t15824 (nat_lit 34394668) (nat_lit 3596708481) (nat_lit 0) D2M8K2.t15825 from rfl, allE_node, rows15824, irow15816, rows15825]
  all_goals rfl

theorem atot15816 : totK PD2M8K2 D2M8K2.u15816 = [0, 334875673333, 887857317643, 559222571504, 61564621127, 0, 0, 0] := by
  rw [show D2M8K2.u15816 = KTree.node D2M8K2.t15824 (nat_lit 34394668) (nat_lit 3596708481) (nat_lit 0) D2M8K2.t15825 from rfl, totK_node, tot15824, tot15825]
  decide +kernel

theorem arows15817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15817 = true := by
  rw [show D2M8K2.u15817 = KTree.node D2M8K2.t15826 (nat_lit 34396720) (nat_lit 1191031875) (nat_lit 0) D2M8K2.t15827 from rfl, allE_node, rows15826, irow15817, rows15827]
  all_goals rfl

theorem atot15817 : totK PD2M8K2 D2M8K2.u15817 = [0, 112238876758, 714635060234, 827714703014, 152661013267, 3880716147, 0, 0] := by
  rw [show D2M8K2.u15817 = KTree.node D2M8K2.t15826 (nat_lit 34396720) (nat_lit 1191031875) (nat_lit 0) D2M8K2.t15827 from rfl, totK_node, tot15826, tot15827]
  decide +kernel

theorem arows15819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15819 = true := by
  rw [show D2M8K2.u15819 = KTree.node D2M8K2.t15828 (nat_lit 34398437) (nat_lit 1336753993) (nat_lit 0) D2M8K2.t15829 from rfl, allE_node, rows15828, irow15819, rows15829]
  all_goals rfl

theorem atot15819 : totK PD2M8K2 D2M8K2.u15819 = [0, 350791537959, 912494251716, 539515548748, 48117785950, 0, 0, 0] := by
  rw [show D2M8K2.u15819 = KTree.node D2M8K2.t15828 (nat_lit 34398437) (nat_lit 1336753993) (nat_lit 0) D2M8K2.t15829 from rfl, totK_node, tot15828, tot15829]
  decide +kernel

theorem arows15820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15820 = true := by
  rw [show D2M8K2.u15820 = KTree.node D2M8K2.t15830 (nat_lit 34400121) (nat_lit 1175309014) (nat_lit 0) D2M8K2.t15831 from rfl, allE_node, rows15830, irow15820, rows15831]
  all_goals rfl

theorem atot15820 : totK PD2M8K2 D2M8K2.u15820 = [0, 0, 417367440068, 966836898069, 385425129409, 17729668807, 0, 0] := by
  rw [show D2M8K2.u15820 = KTree.node D2M8K2.t15830 (nat_lit 34400121) (nat_lit 1175309014) (nat_lit 0) D2M8K2.t15831 from rfl, totK_node, tot15830, tot15831]
  decide +kernel

theorem arows15823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15823 = true := by
  rw [show D2M8K2.u15823 = KTree.node D2M8K2.t15832 (nat_lit 34405324) (nat_lit 3917049186) (nat_lit 0) D2M8K2.t15833 from rfl, allE_node, rows15832, irow15823, rows15833]
  all_goals rfl

theorem atot15823 : totK PD2M8K2 D2M8K2.u15823 = [0, 0, 381886941661, 932978005706, 495269656596, 39261913522, 0, 0] := by
  rw [show D2M8K2.u15823 = KTree.node D2M8K2.t15832 (nat_lit 34405324) (nat_lit 3917049186) (nat_lit 0) D2M8K2.t15833 from rfl, totK_node, tot15832, tot15833]
  decide +kernel

theorem arows15824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15824 = true := by
  rw [show D2M8K2.u15824 = KTree.node D2M8K2.t15834 (nat_lit 34406783) (nat_lit 2006050495) (nat_lit 0) D2M8K2.t15835 from rfl, allE_node, rows15834, irow15824, rows15835]
  all_goals rfl

theorem atot15824 : totK PD2M8K2 D2M8K2.u15824 = [0, 0, 59649953388, 513840399341, 861667931706, 349814189909, 25214516004, 0] := by
  rw [show D2M8K2.u15824 = KTree.node D2M8K2.t15834 (nat_lit 34406783) (nat_lit 2006050495) (nat_lit 0) D2M8K2.t15835 from rfl, totK_node, tot15834, tot15835]
  decide +kernel

theorem arows15826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15826 = true := by
  rw [show D2M8K2.u15826 = KTree.node D2M8K2.t15836 (nat_lit 34408397) (nat_lit 2206942966) (nat_lit 0) D2M8K2.t15837 from rfl, allE_node, rows15836, irow15826, rows15837]
  all_goals rfl

theorem atot15826 : totK PD2M8K2 D2M8K2.u15826 = [0, 0, 245820692211, 721267039169, 661421749970, 190663606481, 7877424857, 0] := by
  rw [show D2M8K2.u15826 = KTree.node D2M8K2.t15836 (nat_lit 34408397) (nat_lit 2206942966) (nat_lit 0) D2M8K2.t15837 from rfl, totK_node, tot15836, tot15837]
  decide +kernel

theorem arows15827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15827 = true := by
  rw [show D2M8K2.u15827 = KTree.node D2M8K2.t15838 (nat_lit 34410344) (nat_lit 3889969880) (nat_lit 0) D2M8K2.t15839 from rfl, allE_node, rows15838, irow15827, rows15839]
  all_goals rfl

theorem atot15827 : totK PD2M8K2 D2M8K2.u15827 = [0, 0, 155015881884, 743285671138, 791498921603, 130965228153, 1547833102, 0] := by
  rw [show D2M8K2.u15827 = KTree.node D2M8K2.t15838 (nat_lit 34410344) (nat_lit 3889969880) (nat_lit 0) D2M8K2.t15839 from rfl, totK_node, tot15838, tot15839]
  decide +kernel

theorem arows15832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15832 = true := by
  rw [show D2M8K2.u15832 = KTree.node D2M8K2.t15840 (nat_lit 34412512) (nat_lit 1694791453) (nat_lit 0) D2M8K2.t15841 from rfl, allE_node, rows15840, irow15832, rows15841]
  all_goals rfl

theorem atot15832 : totK PD2M8K2 D2M8K2.u15832 = [0, 0, 353473966155, 907717089031, 522387823178, 45646097351, 0, 0] := by
  rw [show D2M8K2.u15832 = KTree.node D2M8K2.t15840 (nat_lit 34412512) (nat_lit 1694791453) (nat_lit 0) D2M8K2.t15841 from rfl, totK_node, tot15840, tot15841]
  decide +kernel

theorem arows15833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15833 = true := by
  rw [show D2M8K2.u15833 = KTree.node D2M8K2.t15842 (nat_lit 34414320) (nat_lit 1640841536) (nat_lit 0) D2M8K2.t15843 from rfl, allE_node, rows15842, irow15833, rows15843]
  all_goals rfl

theorem atot15833 : totK PD2M8K2 D2M8K2.u15833 = [0, 0, 109701948906, 626583743493, 825437193262, 203163515594, 5218872685, 0] := by
  rw [show D2M8K2.u15833 = KTree.node D2M8K2.t15842 (nat_lit 34414320) (nat_lit 1640841536) (nat_lit 0) D2M8K2.t15843 from rfl, totK_node, tot15842, tot15843]
  decide +kernel

theorem arows15835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15835 = true := by
  rw [show D2M8K2.u15835 = KTree.node D2M8K2.t15844 (nat_lit 34415868) (nat_lit 2958388062) (nat_lit 0) D2M8K2.t15845 from rfl, allE_node, rows15844, irow15835, rows15845]
  all_goals rfl

theorem atot15835 : totK PD2M8K2 D2M8K2.u15835 = [0, 0, 271934344662, 882551823964, 612511618503, 59823132619, 0, 0] := by
  rw [show D2M8K2.u15835 = KTree.node D2M8K2.t15844 (nat_lit 34415868) (nat_lit 2958388062) (nat_lit 0) D2M8K2.t15845 from rfl, totK_node, tot15844, tot15845]
  decide +kernel

theorem arows15836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15836 = true := by
  rw [show D2M8K2.u15836 = KTree.node D2M8K2.t15846 (nat_lit 34418376) (nat_lit 3560709459) (nat_lit 0) D2M8K2.t15847 from rfl, allE_node, rows15846, irow15836, rows15847]
  all_goals rfl

theorem atot15836 : totK PD2M8K2 D2M8K2.u15836 = [0, 0, 234816998071, 767713914996, 716398263608, 114642940348, 1415142070, 0] := by
  rw [show D2M8K2.u15836 = KTree.node D2M8K2.t15846 (nat_lit 34418376) (nat_lit 3560709459) (nat_lit 0) D2M8K2.t15847 from rfl, totK_node, tot15846, tot15847]
  decide +kernel

theorem arows15839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15839 = true := by
  rw [show D2M8K2.u15839 = KTree.node D2M8K2.t15848 (nat_lit 34419897) (nat_lit 848064169) (nat_lit 0) D2M8K2.t15849 from rfl, allE_node, rows15848, irow15839, rows15849]
  all_goals rfl

theorem atot15839 : totK PD2M8K2 D2M8K2.u15839 = [0, 0, 179238291557, 794684157255, 725849012723, 112712828313, 1238673482, 0] := by
  rw [show D2M8K2.u15839 = KTree.node D2M8K2.t15848 (nat_lit 34419897) (nat_lit 848064169) (nat_lit 0) D2M8K2.t15849 from rfl, totK_node, tot15848, tot15849]
  decide +kernel

theorem arows15840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15840 = true := by
  rw [show D2M8K2.u15840 = KTree.node D2M8K2.t15850 (nat_lit 34463296) (nat_lit 3435287206) (nat_lit 0) D2M8K2.t15851 from rfl, allE_node, rows15850, irow15840, rows15851]
  all_goals rfl

theorem atot15840 : totK PD2M8K2 D2M8K2.u15840 = [0, 243831636970, 528331026336, 365676454317, 442526754672, 180830202165, 8063697217, 0] := by
  rw [show D2M8K2.u15840 = KTree.node D2M8K2.t15850 (nat_lit 34463296) (nat_lit 3435287206) (nat_lit 0) D2M8K2.t15851 from rfl, totK_node, tot15850, tot15851]
  decide +kernel

theorem arows15842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15842 = true := by
  rw [show D2M8K2.u15842 = KTree.node D2M8K2.t15852 (nat_lit 34464843) (nat_lit 3638071171) (nat_lit 0) D2M8K2.t15853 from rfl, allE_node, rows15852, irow15842, rows15853]
  all_goals rfl

theorem atot15842 : totK PD2M8K2 D2M8K2.u15842 = [0, 169412605754, 743965548566, 739166004621, 121446062994, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15842 = KTree.node D2M8K2.t15852 (nat_lit 34464843) (nat_lit 3638071171) (nat_lit 0) D2M8K2.t15853 from rfl, totK_node, tot15852, tot15853]
  decide +kernel

theorem arows15843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15843 = true := by
  rw [show D2M8K2.u15843 = KTree.node D2M8K2.t15854 (nat_lit 34467192) (nat_lit 2671737071) (nat_lit 0) D2M8K2.t15855 from rfl, allE_node, rows15854, irow15843, rows15855]
  all_goals rfl

theorem atot15843 : totK PD2M8K2 D2M8K2.u15843 = [0, 251058596656, 826603003738, 681512475859, 74807153373, 0, 0, 0] := by
  rw [show D2M8K2.u15843 = KTree.node D2M8K2.t15854 (nat_lit 34467192) (nat_lit 2671737071) (nat_lit 0) D2M8K2.t15855 from rfl, totK_node, tot15854, tot15855]
  decide +kernel

theorem arows15847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15847 = true := by
  rw [show D2M8K2.u15847 = KTree.node D2M8K2.t15856 (nat_lit 34468738) (nat_lit 4046144306) (nat_lit 0) D2M8K2.t15857 from rfl, allE_node, rows15856, irow15847, rows15857]
  all_goals rfl

theorem atot15847 : totK PD2M8K2 D2M8K2.u15847 = [0, 172571630672, 641368189388, 699317853116, 274253981649, 23785759959, 0, 0] := by
  rw [show D2M8K2.u15847 = KTree.node D2M8K2.t15856 (nat_lit 34468738) (nat_lit 4046144306) (nat_lit 0) D2M8K2.t15857 from rfl, totK_node, tot15856, tot15857]
  decide +kernel

theorem arows15848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15848 = true := by
  rw [show D2M8K2.u15848 = KTree.node D2M8K2.t15858 (nat_lit 34469948) (nat_lit 2720339391) (nat_lit 0) D2M8K2.t15859 from rfl, allE_node, rows15858, irow15848, rows15859]
  all_goals rfl

theorem atot15848 : totK PD2M8K2 D2M8K2.u15848 = [0, 176600050142, 607636966025, 725744428883, 287368873298, 12206425282, 0, 0] := by
  rw [show D2M8K2.u15848 = KTree.node D2M8K2.t15858 (nat_lit 34469948) (nat_lit 2720339391) (nat_lit 0) D2M8K2.t15859 from rfl, totK_node, tot15858, tot15859]
  decide +kernel

theorem arows15850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15850 = true := by
  rw [show D2M8K2.u15850 = KTree.node D2M8K2.t15860 (nat_lit 34474866) (nat_lit 3451040612) (nat_lit 0) D2M8K2.t15861 from rfl, allE_node, rows15860, irow15850, rows15861]
  all_goals rfl

theorem atot15850 : totK PD2M8K2 D2M8K2.u15850 = [0, 269411043250, 848589081399, 636732185907, 75010977584, 1198073392, 0, 0] := by
  rw [show D2M8K2.u15850 = KTree.node D2M8K2.t15860 (nat_lit 34474866) (nat_lit 3451040612) (nat_lit 0) D2M8K2.t15861 from rfl, totK_node, tot15860, tot15861]
  decide +kernel

theorem arows15851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15851 = true := by
  rw [show D2M8K2.u15851 = KTree.node D2M8K2.t15862 (nat_lit 34476530) (nat_lit 3840343361) (nat_lit 0) D2M8K2.t15863 from rfl, allE_node, rows15862, irow15851, rows15863]
  all_goals rfl

theorem atot15851 : totK PD2M8K2 D2M8K2.u15851 = [0, 82984366571, 548650058333, 859023442365, 276570364740, 12052611869, 0, 0] := by
  rw [show D2M8K2.u15851 = KTree.node D2M8K2.t15862 (nat_lit 34476530) (nat_lit 3840343361) (nat_lit 0) D2M8K2.t15863 from rfl, totK_node, tot15862, tot15863]
  decide +kernel

theorem arows15854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15854 = true := by
  rw [show D2M8K2.u15854 = KTree.node D2M8K2.t15864 (nat_lit 34478003) (nat_lit 2685299376) (nat_lit 0) D2M8K2.t15865 from rfl, allE_node, rows15864, irow15854, rows15865]
  all_goals rfl

theorem atot15854 : totK PD2M8K2 D2M8K2.u15854 = [0, 317012343258, 891261764985, 541570287777, 46560431468, 0, 0, 0] := by
  rw [show D2M8K2.u15854 = KTree.node D2M8K2.t15864 (nat_lit 34478003) (nat_lit 2685299376) (nat_lit 0) D2M8K2.t15865 from rfl, totK_node, tot15864, tot15865]
  decide +kernel

theorem arows15855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15855 = true := by
  rw [show D2M8K2.u15855 = KTree.node D2M8K2.t15866 (nat_lit 34479984) (nat_lit 3412091755) (nat_lit 0) D2M8K2.t15867 from rfl, allE_node, rows15866, irow15855, rows15867]
  all_goals rfl

theorem atot15855 : totK PD2M8K2 D2M8K2.u15855 = [0, 157581518143, 656087096052, 791712748038, 174428868766, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15855 = KTree.node D2M8K2.t15866 (nat_lit 34479984) (nat_lit 3412091755) (nat_lit 0) D2M8K2.t15867 from rfl, totK_node, tot15866, tot15867]
  decide +kernel

theorem arows15857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15857 = true := by
  rw [show D2M8K2.u15857 = KTree.node D2M8K2.t15868 (nat_lit 34481538) (nat_lit 3300594669) (nat_lit 0) D2M8K2.t15869 from rfl, allE_node, rows15868, irow15857, rows15869]
  all_goals rfl

theorem atot15857 : totK PD2M8K2 D2M8K2.u15857 = [0, 262677949119, 846969010723, 641229017314, 81104682741, 1268739303, 0, 0] := by
  rw [show D2M8K2.u15857 = KTree.node D2M8K2.t15868 (nat_lit 34481538) (nat_lit 3300594669) (nat_lit 0) D2M8K2.t15869 from rfl, totK_node, tot15868, tot15869]
  decide +kernel

theorem arows15858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15858 = true := by
  rw [show D2M8K2.u15858 = KTree.node D2M8K2.t15870 (nat_lit 34483234) (nat_lit 4141497652) (nat_lit 0) D2M8K2.t15871 from rfl, allE_node, rows15870, irow15858, rows15871]
  all_goals rfl

theorem atot15858 : totK PD2M8K2 D2M8K2.u15858 = [0, 0, 427695195793, 962049688658, 374050495405, 20744889127, 0, 0] := by
  rw [show D2M8K2.u15858 = KTree.node D2M8K2.t15870 (nat_lit 34483234) (nat_lit 4141497652) (nat_lit 0) D2M8K2.t15871 from rfl, totK_node, tot15870, tot15871]
  decide +kernel

theorem arows15867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15867 = true := by
  rw [show D2M8K2.u15867 = KTree.node D2M8K2.t15872 (nat_lit 34485106) (nat_lit 4079590039) (nat_lit 0) D2M8K2.t15873 from rfl, allE_node, rows15872, irow15867, rows15873]
  all_goals rfl

theorem atot15867 : totK PD2M8K2 D2M8K2.u15867 = [0, 0, 321072035383, 932675145048, 474078460914, 25136464737, 0, 0] := by
  rw [show D2M8K2.u15867 = KTree.node D2M8K2.t15872 (nat_lit 34485106) (nat_lit 4079590039) (nat_lit 0) D2M8K2.t15873 from rfl, totK_node, tot15872, tot15873]
  decide +kernel

theorem arows15868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15868 = true := by
  rw [show D2M8K2.u15868 = KTree.node D2M8K2.t15874 (nat_lit 34486949) (nat_lit 2232790299) (nat_lit 0) D2M8K2.t15875 from rfl, allE_node, rows15874, irow15868, rows15875]
  all_goals rfl

theorem atot15868 : totK PD2M8K2 D2M8K2.u15868 = [0, 0, 160967727169, 709405433897, 780800839036, 119876903579, 1239866073, 0] := by
  rw [show D2M8K2.u15868 = KTree.node D2M8K2.t15874 (nat_lit 34486949) (nat_lit 2232790299) (nat_lit 0) D2M8K2.t15875 from rfl, totK_node, tot15874, tot15875]
  decide +kernel

theorem arows15870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15870 = true := by
  rw [show D2M8K2.u15870 = KTree.node D2M8K2.t15876 (nat_lit 34488779) (nat_lit 1022197679) (nat_lit 0) D2M8K2.t15877 from rfl, allE_node, rows15876, irow15870, rows15877]
  all_goals rfl

theorem atot15870 : totK PD2M8K2 D2M8K2.u15870 = [0, 0, 347515759258, 949099341350, 474950140037, 26899171416, 0, 0] := by
  rw [show D2M8K2.u15870 = KTree.node D2M8K2.t15876 (nat_lit 34488779) (nat_lit 1022197679) (nat_lit 0) D2M8K2.t15877 from rfl, totK_node, tot15876, tot15877]
  decide +kernel

theorem arows15871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15871 = true := by
  rw [show D2M8K2.u15871 = KTree.node D2M8K2.t15878 (nat_lit 34495447) (nat_lit 2375701447) (nat_lit 0) D2M8K2.t15879 from rfl, allE_node, rows15878, irow15871, rows15879]
  all_goals rfl

theorem atot15871 : totK PD2M8K2 D2M8K2.u15871 = [0, 0, 357537256038, 926371432400, 507398883396, 37075218324, 0, 0] := by
  rw [show D2M8K2.u15871 = KTree.node D2M8K2.t15878 (nat_lit 34495447) (nat_lit 2375701447) (nat_lit 0) D2M8K2.t15879 from rfl, totK_node, tot15878, tot15879]
  decide +kernel

theorem arows15874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15874 = true := by
  rw [show D2M8K2.u15874 = KTree.node D2M8K2.t15880 (nat_lit 34497102) (nat_lit 3891873182) (nat_lit 0) D2M8K2.t15881 from rfl, allE_node, rows15880, irow15874, rows15881]
  all_goals rfl

theorem atot15874 : totK PD2M8K2 D2M8K2.u15874 = [0, 0, 57196784527, 513048471773, 873655572564, 278946142104, 13105450397, 0] := by
  rw [show D2M8K2.u15874 = KTree.node D2M8K2.t15880 (nat_lit 34497102) (nat_lit 3891873182) (nat_lit 0) D2M8K2.t15881 from rfl, totK_node, tot15880, tot15881]
  decide +kernel

theorem arows15875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15875 = true := by
  rw [show D2M8K2.u15875 = KTree.node D2M8K2.t15882 (nat_lit 34498616) (nat_lit 3883369881) (nat_lit 0) D2M8K2.t15883 from rfl, allE_node, rows15882, irow15875, rows15883]
  all_goals rfl

theorem atot15875 : totK PD2M8K2 D2M8K2.u15875 = [0, 0, 337155337295, 944293106788, 468057571312, 27066369916, 0, 0] := by
  rw [show D2M8K2.u15875 = KTree.node D2M8K2.t15882 (nat_lit 34498616) (nat_lit 3883369881) (nat_lit 0) D2M8K2.t15883 from rfl, totK_node, tot15882, tot15883]
  decide +kernel

theorem arows15877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15877 = true := by
  rw [show D2M8K2.u15877 = KTree.node D2M8K2.t15884 (nat_lit 34500692) (nat_lit 3284668582) (nat_lit 0) D2M8K2.t15885 from rfl, allE_node, rows15884, irow15877, rows15885]
  all_goals rfl

theorem atot15877 : totK PD2M8K2 D2M8K2.u15877 = [0, 0, 139392202069, 665304704108, 748914755566, 151269012273, 4720618446, 0] := by
  rw [show D2M8K2.u15877 = KTree.node D2M8K2.t15884 (nat_lit 34500692) (nat_lit 3284668582) (nat_lit 0) D2M8K2.t15885 from rfl, totK_node, tot15884, tot15885]
  decide +kernel

theorem arows15878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15878 = true := by
  rw [show D2M8K2.u15878 = KTree.node D2M8K2.t15886 (nat_lit 34502251) (nat_lit 1620840820) (nat_lit 0) D2M8K2.t15887 from rfl, allE_node, rows15886, irow15878, rows15887]
  all_goals rfl

theorem atot15878 : totK PD2M8K2 D2M8K2.u15878 = [0, 89266124844, 407542324504, 798873590411, 488200795190, 45436444677, 0, 0] := by
  rw [show D2M8K2.u15878 = KTree.node D2M8K2.t15886 (nat_lit 34502251) (nat_lit 1620840820) (nat_lit 0) D2M8K2.t15887 from rfl, totK_node, tot15886, tot15887]
  decide +kernel

theorem arows15882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15882 = true := by
  rw [show D2M8K2.u15882 = KTree.node D2M8K2.t15888 (nat_lit 34505815) (nat_lit 2368522662) (nat_lit 0) D2M8K2.t15889 from rfl, allE_node, rows15888, irow15882, rows15889]
  all_goals rfl

theorem atot15882 : totK PD2M8K2 D2M8K2.u15882 = [0, 306131675729, 914852904109, 514643791301, 34188810838, 0, 0, 0] := by
  rw [show D2M8K2.u15882 = KTree.node D2M8K2.t15888 (nat_lit 34505815) (nat_lit 2368522662) (nat_lit 0) D2M8K2.t15889 from rfl, totK_node, tot15888, tot15889]
  decide +kernel

theorem arows15883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15883 = true := by
  rw [show D2M8K2.u15883 = KTree.node D2M8K2.t15890 (nat_lit 34507681) (nat_lit 1499270450) (nat_lit 0) D2M8K2.t15891 from rfl, allE_node, rows15890, irow15883, rows15891]
  all_goals rfl

theorem atot15883 : totK PD2M8K2 D2M8K2.u15883 = [0, 162074439460, 692682983023, 821097523200, 140707203021, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15883 = KTree.node D2M8K2.t15890 (nat_lit 34507681) (nat_lit 1499270450) (nat_lit 0) D2M8K2.t15891 from rfl, totK_node, tot15890, tot15891]
  decide +kernel

theorem arows15885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15885 = true := by
  rw [show D2M8K2.u15885 = KTree.node D2M8K2.t15892 (nat_lit 34509504) (nat_lit 2554932599) (nat_lit 0) D2M8K2.t15893 from rfl, allE_node, rows15892, irow15885, rows15893]
  all_goals rfl

theorem atot15885 : totK PD2M8K2 D2M8K2.u15885 = [0, 245013891588, 801825937285, 626754323347, 148423769796, 9977052014, 0, 0] := by
  rw [show D2M8K2.u15885 = KTree.node D2M8K2.t15892 (nat_lit 34509504) (nat_lit 2554932599) (nat_lit 0) D2M8K2.t15893 from rfl, totK_node, tot15892, tot15893]
  decide +kernel

theorem arows15886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15886 = true := by
  rw [show D2M8K2.u15886 = KTree.node D2M8K2.t15894 (nat_lit 34511219) (nat_lit 1336098596) (nat_lit 2080) D2M8K2.t15895 from rfl, allE_node, rows15894, irow15886, rows15895]
  all_goals rfl

theorem atot15886 : totK PD2M8K2 D2M8K2.u15886 = [0, 164100342924, 646391591466, 774637881509, 229923528709, 5430665091, 0, 0] := by
  rw [show D2M8K2.u15886 = KTree.node D2M8K2.t15894 (nat_lit 34511219) (nat_lit 1336098596) (nat_lit 2080) D2M8K2.t15895 from rfl, totK_node, tot15894, tot15895]
  decide +kernel

theorem arows15889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15889 = true := by
  rw [show D2M8K2.u15889 = KTree.node D2M8K2.t15896 (nat_lit 34516310) (nat_lit 3911755357) (nat_lit 0) D2M8K2.t15897 from rfl, allE_node, rows15896, irow15889, rows15897]
  all_goals rfl

theorem atot15889 : totK PD2M8K2 D2M8K2.u15889 = [0, 257005346589, 839602262613, 629697989653, 82287662880, 1198073392, 0, 0] := by
  rw [show D2M8K2.u15889 = KTree.node D2M8K2.t15896 (nat_lit 34516310) (nat_lit 3911755357) (nat_lit 0) D2M8K2.t15897 from rfl, totK_node, tot15896, tot15897]
  decide +kernel

theorem arows15890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15890 = true := by
  rw [show D2M8K2.u15890 = KTree.node D2M8K2.t15898 (nat_lit 34518020) (nat_lit 3350851466) (nat_lit 0) D2M8K2.t15899 from rfl, allE_node, rows15898, irow15890, rows15899]
  all_goals rfl

theorem atot15890 : totK PD2M8K2 D2M8K2.u15890 = [0, 103750404885, 574722823335, 834424533056, 257814599125, 12052611869, 0, 0] := by
  rw [show D2M8K2.u15890 = KTree.node D2M8K2.t15898 (nat_lit 34518020) (nat_lit 3350851466) (nat_lit 0) D2M8K2.t15899 from rfl, totK_node, tot15898, tot15899]
  decide +kernel

theorem arows15892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15892 = true := by
  rw [show D2M8K2.u15892 = KTree.node D2M8K2.t15900 (nat_lit 34519437) (nat_lit 1484268833) (nat_lit 0) D2M8K2.t15901 from rfl, allE_node, rows15900, irow15892, rows15901]
  all_goals rfl

theorem atot15892 : totK PD2M8K2 D2M8K2.u15892 = [0, 320437801854, 897290359368, 544075211870, 49885825363, 0, 0, 0] := by
  rw [show D2M8K2.u15892 = KTree.node D2M8K2.t15900 (nat_lit 34519437) (nat_lit 1484268833) (nat_lit 0) D2M8K2.t15901 from rfl, totK_node, tot15900, tot15901]
  decide +kernel

theorem arows15893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15893 = true := by
  rw [show D2M8K2.u15893 = KTree.node D2M8K2.t15902 (nat_lit 34521414) (nat_lit 3686116061) (nat_lit 0) D2M8K2.t15903 from rfl, allE_node, rows15902, irow15893, rows15903]
  all_goals rfl

theorem atot15893 : totK PD2M8K2 D2M8K2.u15893 = [0, 0, 491884106858, 1014537172708, 279906811322, 6350335412, 0, 0] := by
  rw [show D2M8K2.u15893 = KTree.node D2M8K2.t15902 (nat_lit 34521414) (nat_lit 3686116061) (nat_lit 0) D2M8K2.t15903 from rfl, totK_node, tot15902, tot15903]
  decide +kernel

theorem arows15898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15898 = true := by
  rw [show D2M8K2.u15898 = KTree.node D2M8K2.t15904 (nat_lit 34526746) (nat_lit 2792710188) (nat_lit 0) D2M8K2.t15905 from rfl, allE_node, rows15904, irow15898, rows15905]
  all_goals rfl

theorem atot15898 : totK PD2M8K2 D2M8K2.u15898 = [0, 0, 269358905810, 832156596870, 550501157947, 64983536966, 1138244013, 0] := by
  rw [show D2M8K2.u15898 = KTree.node D2M8K2.t15904 (nat_lit 34526746) (nat_lit 2792710188) (nat_lit 0) D2M8K2.t15905 from rfl, totK_node, tot15904, tot15905]
  decide +kernel

theorem arows15899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15899 = true := by
  rw [show D2M8K2.u15899 = KTree.node D2M8K2.t15906 (nat_lit 34529370) (nat_lit 3679100857) (nat_lit 0) D2M8K2.t15907 from rfl, allE_node, rows15906, irow15899, rows15907]
  all_goals rfl

theorem atot15899 : totK PD2M8K2 D2M8K2.u15899 = [0, 0, 249454696959, 876506509207, 627149733589, 54111739659, 0, 0] := by
  rw [show D2M8K2.u15899 = KTree.node D2M8K2.t15906 (nat_lit 34529370) (nat_lit 3679100857) (nat_lit 0) D2M8K2.t15907 from rfl, totK_node, tot15906, tot15907]
  decide +kernel

theorem arows15901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15901 = true := by
  rw [show D2M8K2.u15901 = KTree.node D2M8K2.t15908 (nat_lit 34535882) (nat_lit 3373927643) (nat_lit 0) D2M8K2.t15909 from rfl, allE_node, rows15908, irow15901, rows15909]
  all_goals rfl

theorem atot15901 : totK PD2M8K2 D2M8K2.u15901 = [0, 0, 394716453698, 957699693721, 439508910758, 23342469906, 0, 0] := by
  rw [show D2M8K2.u15901 = KTree.node D2M8K2.t15908 (nat_lit 34535882) (nat_lit 3373927643) (nat_lit 0) D2M8K2.t15909 from rfl, totK_node, tot15908, tot15909]
  decide +kernel

theorem arows15902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15902 = true := by
  rw [show D2M8K2.u15902 = KTree.node D2M8K2.t15910 (nat_lit 34537392) (nat_lit 3651659898) (nat_lit 0) D2M8K2.t15911 from rfl, allE_node, rows15910, irow15902, rows15911]
  all_goals rfl

theorem atot15902 : totK PD2M8K2 D2M8K2.u15902 = [0, 0, 356267793518, 948510150019, 448882643224, 25944990271, 0, 0] := by
  rw [show D2M8K2.u15902 = KTree.node D2M8K2.t15910 (nat_lit 34537392) (nat_lit 3651659898) (nat_lit 0) D2M8K2.t15911 from rfl, totK_node, tot15910, tot15911]
  decide +kernel

theorem arows15905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15905 = true := by
  rw [show D2M8K2.u15905 = KTree.node D2M8K2.t15912 (nat_lit 34540446) (nat_lit 3855791684) (nat_lit 0) D2M8K2.t15913 from rfl, allE_node, rows15912, irow15905, rows15913]
  all_goals rfl

theorem atot15905 : totK PD2M8K2 D2M8K2.u15905 = [0, 0, 251519737924, 828000398982, 602991759023, 75959298478, 1095107716, 0] := by
  rw [show D2M8K2.u15905 = KTree.node D2M8K2.t15912 (nat_lit 34540446) (nat_lit 3855791684) (nat_lit 0) D2M8K2.t15913 from rfl, totK_node, tot15912, tot15913]
  decide +kernel

theorem arows15906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15906 = true := by
  rw [show D2M8K2.u15906 = KTree.node D2M8K2.t15914 (nat_lit 34546255) (nat_lit 2427379393) (nat_lit 0) D2M8K2.t15915 from rfl, allE_node, rows15914, irow15906, rows15915]
  all_goals rfl

theorem atot15906 : totK PD2M8K2 D2M8K2.u15906 = [0, 250622349935, 544404143240, 452200546787, 415398080985, 99737464219, 3882006667, 0] := by
  rw [show D2M8K2.u15906 = KTree.node D2M8K2.t15914 (nat_lit 34546255) (nat_lit 2427379393) (nat_lit 0) D2M8K2.t15915 from rfl, totK_node, tot15914, tot15915]
  decide +kernel

theorem arows15908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15908 = true := by
  rw [show D2M8K2.u15908 = KTree.node D2M8K2.t15916 (nat_lit 34547828) (nat_lit 1711495694) (nat_lit 0) D2M8K2.t15917 from rfl, allE_node, rows15916, irow15908, rows15917]
  all_goals rfl

theorem atot15908 : totK PD2M8K2 D2M8K2.u15908 = [0, 153525330889, 738719989089, 761574891910, 125664071788, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15908 = KTree.node D2M8K2.t15916 (nat_lit 34547828) (nat_lit 1711495694) (nat_lit 0) D2M8K2.t15917 from rfl, totK_node, tot15916, tot15917]
  decide +kernel

theorem arows15909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15909 = true := by
  rw [show D2M8K2.u15909 = KTree.node D2M8K2.t15918 (nat_lit 34550174) (nat_lit 3831962033) (nat_lit 0) D2M8K2.t15919 from rfl, allE_node, rows15918, irow15909, rows15919]
  all_goals rfl

theorem atot15909 : totK PD2M8K2 D2M8K2.u15909 = [0, 265899730547, 840915092294, 654637979940, 73220108476, 0, 0, 0] := by
  rw [show D2M8K2.u15909 = KTree.node D2M8K2.t15918 (nat_lit 34550174) (nat_lit 3831962033) (nat_lit 0) D2M8K2.t15919 from rfl, totK_node, tot15918, tot15919]
  decide +kernel

theorem arows15913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15913 = true := by
  rw [show D2M8K2.u15913 = KTree.node D2M8K2.t15920 (nat_lit 34551732) (nat_lit 2576356806) (nat_lit 0) D2M8K2.t15921 from rfl, allE_node, rows15920, irow15913, rows15921]
  all_goals rfl

theorem atot15913 : totK PD2M8K2 D2M8K2.u15913 = [0, 150052706404, 636654786903, 742311663956, 286352824536, 23760370731, 0, 0] := by
  rw [show D2M8K2.u15913 = KTree.node D2M8K2.t15920 (nat_lit 34551732) (nat_lit 2576356806) (nat_lit 0) D2M8K2.t15921 from rfl, totK_node, tot15920, tot15921]
  decide +kernel

theorem arows15914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15914 = true := by
  rw [show D2M8K2.u15914 = KTree.node D2M8K2.t15922 (nat_lit 34553014) (nat_lit 3390271686) (nat_lit 0) D2M8K2.t15923 from rfl, allE_node, rows15922, irow15914, rows15923]
  all_goals rfl

theorem atot15914 : totK PD2M8K2 D2M8K2.u15914 = [0, 167187563726, 604907519316, 748124770336, 284772363645, 12229515597, 0, 0] := by
  rw [show D2M8K2.u15914 = KTree.node D2M8K2.t15922 (nat_lit 34553014) (nat_lit 3390271686) (nat_lit 0) D2M8K2.t15923 from rfl, totK_node, tot15922, tot15923]
  decide +kernel

theorem arows15916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15916 = true := by
  rw [show D2M8K2.u15916 = KTree.node D2M8K2.t15924 (nat_lit 34554808) (nat_lit 3371795021) (nat_lit 0) D2M8K2.t15925 from rfl, allE_node, rows15924, irow15916, rows15925]
  all_goals rfl

theorem atot15916 : totK PD2M8K2 D2M8K2.u15916 = [0, 178229519835, 716528276145, 778061733908, 151228584317, 2309606161, 0, 0] := by
  rw [show D2M8K2.u15916 = KTree.node D2M8K2.t15924 (nat_lit 34554808) (nat_lit 3371795021) (nat_lit 0) D2M8K2.t15925 from rfl, totK_node, tot15924, tot15925]
  decide +kernel

theorem arows15917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15917 = true := by
  rw [show D2M8K2.u15917 = KTree.node D2M8K2.t15926 (nat_lit 34556930) (nat_lit 4073968270) (nat_lit 0) D2M8K2.t15927 from rfl, allE_node, rows15926, irow15917, rows15927]
  all_goals rfl

theorem atot15917 : totK PD2M8K2 D2M8K2.u15917 = [0, 312065396366, 830958983713, 571090735120, 110161254691, 5511322840, 0, 0] := by
  rw [show D2M8K2.u15917 = KTree.node D2M8K2.t15926 (nat_lit 34556930) (nat_lit 4073968270) (nat_lit 0) D2M8K2.t15927 from rfl, totK_node, tot15926, tot15927]
  decide +kernel

theorem arows15920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15920 = true := by
  rw [show D2M8K2.u15920 = KTree.node D2M8K2.t15928 (nat_lit 34558406) (nat_lit 3287319739) (nat_lit 0) D2M8K2.t15929 from rfl, allE_node, rows15928, irow15920, rows15929]
  all_goals rfl

theorem atot15920 : totK PD2M8K2 D2M8K2.u15920 = [0, 114411566433, 634166036410, 819915793349, 218887942775, 9664716404, 0, 0] := by
  rw [show D2M8K2.u15920 = KTree.node D2M8K2.t15928 (nat_lit 34558406) (nat_lit 3287319739) (nat_lit 0) D2M8K2.t15929 from rfl, totK_node, tot15928, tot15929]
  decide +kernel

theorem arows15921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15921 = true := by
  rw [show D2M8K2.u15921 = KTree.node D2M8K2.t15930 (nat_lit 34563723) (nat_lit 2093087893) (nat_lit 0) D2M8K2.t15931 from rfl, allE_node, rows15930, irow15921, rows15931]
  all_goals rfl

theorem atot15921 : totK PD2M8K2 D2M8K2.u15921 = [0, 260602896158, 793689137999, 639045197198, 124194671671, 3579068459, 0, 0] := by
  rw [show D2M8K2.u15921 = KTree.node D2M8K2.t15930 (nat_lit 34563723) (nat_lit 2093087893) (nat_lit 0) D2M8K2.t15931 from rfl, totK_node, tot15930, tot15931]
  decide +kernel

theorem arows15923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15923 = true := by
  rw [show D2M8K2.u15923 = KTree.node D2M8K2.t15932 (nat_lit 34565172) (nat_lit 3153403728) (nat_lit 0) D2M8K2.t15933 from rfl, allE_node, rows15932, irow15923, rows15933]
  all_goals rfl

theorem atot15923 : totK PD2M8K2 D2M8K2.u15923 = [0, 182433760473, 734787777939, 769238614017, 145462304492, 1268739303, 0, 0] := by
  rw [show D2M8K2.u15923 = KTree.node D2M8K2.t15932 (nat_lit 34565172) (nat_lit 3153403728) (nat_lit 0) D2M8K2.t15933 from rfl, totK_node, tot15932, tot15933]
  decide +kernel

theorem arows15924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15924 = true := by
  rw [show D2M8K2.u15924 = KTree.node D2M8K2.t15934 (nat_lit 34566828) (nat_lit 2803394435) (nat_lit 0) D2M8K2.t15935 from rfl, allE_node, rows15934, irow15924, rows15935]
  all_goals rfl

theorem atot15924 : totK PD2M8K2 D2M8K2.u15924 = [0, 0, 349404341187, 948161952507, 449230821598, 26116109855, 0, 0] := by
  rw [show D2M8K2.u15924 = KTree.node D2M8K2.t15934 (nat_lit 34566828) (nat_lit 2803394435) (nat_lit 0) D2M8K2.t15935 from rfl, totK_node, tot15934, tot15935]
  decide +kernel

theorem arows15930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15930 = true := by
  rw [show D2M8K2.u15930 = KTree.node D2M8K2.t15936 (nat_lit 34568444) (nat_lit 2599075684) (nat_lit 0) D2M8K2.t15937 from rfl, allE_node, rows15936, irow15930, rows15937]
  all_goals rfl

theorem atot15930 : totK PD2M8K2 D2M8K2.u15930 = [0, 0, 238675590803, 789760025537, 638052508742, 92431884783, 1310285577, 0] := by
  rw [show D2M8K2.u15930 = KTree.node D2M8K2.t15936 (nat_lit 34568444) (nat_lit 2599075684) (nat_lit 0) D2M8K2.t15937 from rfl, totK_node, tot15936, tot15937]
  decide +kernel

theorem arows15931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15931 = true := by
  rw [show D2M8K2.u15931 = KTree.node D2M8K2.t15938 (nat_lit 34570843) (nat_lit 1704771153) (nat_lit 0) D2M8K2.t15939 from rfl, allE_node, rows15938, irow15931, rows15939]
  all_goals rfl

theorem atot15931 : totK PD2M8K2 D2M8K2.u15931 = [0, 0, 260894871999, 834877287280, 668393600513, 61407892308, 0, 0] := by
  rw [show D2M8K2.u15931 = KTree.node D2M8K2.t15938 (nat_lit 34570843) (nat_lit 1704771153) (nat_lit 0) D2M8K2.t15939 from rfl, totK_node, tot15938, tot15939]
  decide +kernel

theorem arows15933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15933 = true := by
  rw [show D2M8K2.u15933 = KTree.node D2M8K2.t15940 (nat_lit 34573830) (nat_lit 3421091285) (nat_lit 0) D2M8K2.t15941 from rfl, allE_node, rows15940, irow15933, rows15941]
  all_goals rfl

theorem atot15933 : totK PD2M8K2 D2M8K2.u15933 = [0, 0, 360229983000, 927651999169, 504307931517, 39580106331, 0, 0] := by
  rw [show D2M8K2.u15933 = KTree.node D2M8K2.t15940 (nat_lit 34573830) (nat_lit 3421091285) (nat_lit 0) D2M8K2.t15941 from rfl, totK_node, tot15940, tot15941]
  decide +kernel

theorem arows15934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15934 = true := by
  rw [show D2M8K2.u15934 = KTree.node D2M8K2.t15942 (nat_lit 34575630) (nat_lit 3775842798) (nat_lit 0) D2M8K2.t15943 from rfl, allE_node, rows15942, irow15934, rows15943]
  all_goals rfl

theorem atot15934 : totK PD2M8K2 D2M8K2.u15934 = [0, 0, 141655997326, 688478031488, 788430155467, 159293519909, 4879840392, 0] := by
  rw [show D2M8K2.u15934 = KTree.node D2M8K2.t15942 (nat_lit 34575630) (nat_lit 3775842798) (nat_lit 0) D2M8K2.t15943 from rfl, totK_node, tot15942, tot15943]
  decide +kernel

theorem arows15937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15937 = true := by
  rw [show D2M8K2.u15937 = KTree.node D2M8K2.t15944 (nat_lit 34577798) (nat_lit 3898669161) (nat_lit 0) D2M8K2.t15945 from rfl, allE_node, rows15944, irow15937, rows15945]
  all_goals rfl

theorem atot15937 : totK PD2M8K2 D2M8K2.u15937 = [0, 0, 335056050988, 907329137416, 520050425277, 46447477321, 0, 0] := by
  rw [show D2M8K2.u15937 = KTree.node D2M8K2.t15944 (nat_lit 34577798) (nat_lit 3898669161) (nat_lit 0) D2M8K2.t15945 from rfl, totK_node, tot15944, tot15945]
  decide +kernel

theorem arows15938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15938 = true := by
  rw [show D2M8K2.u15938 = KTree.node D2M8K2.t15946 (nat_lit 34579371) (nat_lit 3692897612) (nat_lit 0) D2M8K2.t15947 from rfl, allE_node, rows15946, irow15938, rows15947]
  all_goals rfl

theorem atot15938 : totK PD2M8K2 D2M8K2.u15938 = [0, 0, 93170539393, 639655439671, 847374647791, 183451711689, 4931404646, 0] := by
  rw [show D2M8K2.u15938 = KTree.node D2M8K2.t15946 (nat_lit 34579371) (nat_lit 3692897612) (nat_lit 0) D2M8K2.t15947 from rfl, totK_node, tot15946, tot15947]
  decide +kernel

theorem arows15940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15940 = true := by
  rw [show D2M8K2.u15940 = KTree.node D2M8K2.t15948 (nat_lit 34584788) (nat_lit 2588206581) (nat_lit 0) D2M8K2.t15949 from rfl, allE_node, rows15948, irow15940, rows15949]
  all_goals rfl

theorem atot15940 : totK PD2M8K2 D2M8K2.u15940 = [0, 0, 377333226139, 947001247307, 470747135414, 32628585273, 0, 0] := by
  rw [show D2M8K2.u15940 = KTree.node D2M8K2.t15948 (nat_lit 34584788) (nat_lit 2588206581) (nat_lit 0) D2M8K2.t15949 from rfl, totK_node, tot15948, tot15949]
  decide +kernel

theorem arows15941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15941 = true := by
  rw [show D2M8K2.u15941 = KTree.node D2M8K2.t15950 (nat_lit 34586306) (nat_lit 4001766896) (nat_lit 0) D2M8K2.t15951 from rfl, allE_node, rows15950, irow15941, rows15951]
  all_goals rfl

theorem atot15941 : totK PD2M8K2 D2M8K2.u15941 = [0, 0, 56604951192, 548096196715, 892027216655, 253589231387, 8424427256, 0] := by
  rw [show D2M8K2.u15941 = KTree.node D2M8K2.t15950 (nat_lit 34586306) (nat_lit 4001766896) (nat_lit 0) D2M8K2.t15951 from rfl, totK_node, tot15950, tot15951]
  decide +kernel

theorem arows15945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15945 = true := by
  rw [show D2M8K2.u15945 = KTree.node D2M8K2.t15952 (nat_lit 34588274) (nat_lit 3551002793) (nat_lit 0) D2M8K2.t15953 from rfl, allE_node, rows15952, irow15945, rows15953]
  all_goals rfl

theorem atot15945 : totK PD2M8K2 D2M8K2.u15945 = [0, 0, 307342489788, 793158865141, 516313136045, 143918113858, 13326740810, 0] := by
  rw [show D2M8K2.u15945 = KTree.node D2M8K2.t15952 (nat_lit 34588274) (nat_lit 3551002793) (nat_lit 0) D2M8K2.t15953 from rfl, totK_node, tot15952, tot15953]
  decide +kernel

theorem arows15946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15946 = true := by
  rw [show D2M8K2.u15946 = KTree.node D2M8K2.t15954 (nat_lit 34589480) (nat_lit 3841917883) (nat_lit 0) D2M8K2.t15955 from rfl, allE_node, rows15954, irow15946, rows15955]
  all_goals rfl

theorem atot15946 : totK PD2M8K2 D2M8K2.u15946 = [0, 0, 124655673597, 710736478418, 818490002811, 126873463410, 1369150432, 0] := by
  rw [show D2M8K2.u15946 = KTree.node D2M8K2.t15954 (nat_lit 34589480) (nat_lit 3841917883) (nat_lit 0) D2M8K2.t15955 from rfl, totK_node, tot15954, tot15955]
  decide +kernel

theorem arows15948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15948 = true := by
  rw [show D2M8K2.u15948 = KTree.node D2M8K2.t15956 (nat_lit 34595308) (nat_lit 3939139242) (nat_lit 0) D2M8K2.t15957 from rfl, allE_node, rows15956, irow15948, rows15957]
  all_goals rfl

theorem atot15948 : totK PD2M8K2 D2M8K2.u15948 = [0, 0, 323808811174, 921800033804, 518687236890, 34097589229, 0, 0] := by
  rw [show D2M8K2.u15948 = KTree.node D2M8K2.t15956 (nat_lit 34595308) (nat_lit 3939139242) (nat_lit 0) D2M8K2.t15957 from rfl, totK_node, tot15956, tot15957]
  decide +kernel

theorem arows15949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15949 = true := by
  rw [show D2M8K2.u15949 = KTree.node D2M8K2.t15958 (nat_lit 34597860) (nat_lit 3236659581) (nat_lit 0) D2M8K2.t15959 from rfl, allE_node, rows15958, irow15949, rows15959]
  all_goals rfl

theorem atot15949 : totK PD2M8K2 D2M8K2.u15949 = [0, 0, 194800701799, 747712409064, 747922062165, 101717591875, 1164319620, 0] := by
  rw [show D2M8K2.u15949 = KTree.node D2M8K2.t15958 (nat_lit 34597860) (nat_lit 3236659581) (nat_lit 0) D2M8K2.t15959 from rfl, totK_node, tot15958, tot15959]
  decide +kernel

theorem arows15952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15952 = true := by
  rw [show D2M8K2.u15952 = KTree.node D2M8K2.t15960 (nat_lit 34599534) (nat_lit 4048482758) (nat_lit 0) D2M8K2.t15961 from rfl, allE_node, rows15960, irow15952, rows15961]
  all_goals rfl

theorem atot15952 : totK PD2M8K2 D2M8K2.u15952 = [0, 0, 225143171968, 783592250540, 672386025042, 104586215327, 1198073392, 0] := by
  rw [show D2M8K2.u15952 = KTree.node D2M8K2.t15960 (nat_lit 34599534) (nat_lit 4048482758) (nat_lit 0) D2M8K2.t15961 from rfl, totK_node, tot15960, tot15961]
  decide +kernel

theorem arows15953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15953 = true := by
  rw [show D2M8K2.u15953 = KTree.node D2M8K2.t15962 (nat_lit 34601524) (nat_lit 3970866394) (nat_lit 0) D2M8K2.t15963 from rfl, allE_node, rows15962, irow15953, rows15963]
  all_goals rfl

theorem atot15953 : totK PD2M8K2 D2M8K2.u15953 = [0, 0, 236709981309, 763367124113, 658963229932, 128016002965, 4257574148, 0] := by
  rw [show D2M8K2.u15953 = KTree.node D2M8K2.t15962 (nat_lit 34601524) (nat_lit 3970866394) (nat_lit 0) D2M8K2.t15963 from rfl, totK_node, tot15962, tot15963]
  decide +kernel

theorem arows15955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15955 = true := by
  rw [show D2M8K2.u15955 = KTree.node D2M8K2.t15964 (nat_lit 34603294) (nat_lit 2989019154) (nat_lit 0) D2M8K2.t15965 from rfl, allE_node, rows15964, irow15955, rows15965]
  all_goals rfl

theorem atot15955 : totK PD2M8K2 D2M8K2.u15955 = [0, 0, 138983479959, 752305042050, 775678780958, 90703205571, 1096505104, 0] := by
  rw [show D2M8K2.u15955 = KTree.node D2M8K2.t15964 (nat_lit 34603294) (nat_lit 2989019154) (nat_lit 0) D2M8K2.t15965 from rfl, totK_node, tot15964, tot15965]
  decide +kernel

theorem arows15956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15956 = true := by
  rw [show D2M8K2.u15956 = KTree.node D2M8K2.t15966 (nat_lit 34605555) (nat_lit 3384304329) (nat_lit 0) D2M8K2.t15967 from rfl, allE_node, rows15966, irow15956, rows15967]
  all_goals rfl

theorem atot15956 : totK PD2M8K2 D2M8K2.u15956 = [0, 0, 395827957418, 939325467379, 455776346379, 29579979427, 0, 0] := by
  rw [show D2M8K2.u15956 = KTree.node D2M8K2.t15966 (nat_lit 34605555) (nat_lit 3384304329) (nat_lit 0) D2M8K2.t15967 from rfl, totK_node, tot15966, tot15967]
  decide +kernel

theorem arows15961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15961 = true := by
  rw [show D2M8K2.u15961 = KTree.node D2M8K2.t15968 (nat_lit 34607254) (nat_lit 3445385284) (nat_lit 0) D2M8K2.t15969 from rfl, allE_node, rows15968, irow15961, rows15969]
  all_goals rfl

theorem atot15961 : totK PD2M8K2 D2M8K2.u15961 = [0, 0, 19692840307, 540506050934, 971501300052, 252723874757, 6186994463, 0] := by
  rw [show D2M8K2.u15961 = KTree.node D2M8K2.t15968 (nat_lit 34607254) (nat_lit 3445385284) (nat_lit 0) D2M8K2.t15969 from rfl, totK_node, tot15968, tot15969]
  decide +kernel

theorem arows15962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15962 = true := by
  rw [show D2M8K2.u15962 = KTree.node D2M8K2.t15970 (nat_lit 34609266) (nat_lit 3443727579) (nat_lit 0) D2M8K2.t15971 from rfl, allE_node, rows15970, irow15962, rows15971]
  all_goals rfl

theorem atot15962 : totK PD2M8K2 D2M8K2.u15962 = [0, 0, 0, 405353251395, 962916519425, 353267643306, 15379538068, 0] := by
  rw [show D2M8K2.u15962 = KTree.node D2M8K2.t15970 (nat_lit 34609266) (nat_lit 3443727579) (nat_lit 0) D2M8K2.t15971 from rfl, totK_node, tot15970, tot15971]
  decide +kernel

theorem arows15964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15964 = true := by
  rw [show D2M8K2.u15964 = KTree.node D2M8K2.t15972 (nat_lit 34611075) (nat_lit 1828880774) (nat_lit 32) D2M8K2.t15973 from rfl, allE_node, rows15972, irow15964, rows15973]
  all_goals rfl

theorem atot15964 : totK PD2M8K2 D2M8K2.u15964 = [0, 0, 0, 137091450180, 790025378468, 691269351485, 87196634919, 1310517177] := by
  rw [show D2M8K2.u15964 = KTree.node D2M8K2.t15972 (nat_lit 34611075) (nat_lit 1828880774) (nat_lit 32) D2M8K2.t15973 from rfl, totK_node, tot15972, tot15973]
  decide +kernel

theorem arows15965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15965 = true := by
  rw [show D2M8K2.u15965 = KTree.node D2M8K2.t15974 (nat_lit 34618891) (nat_lit 1619810307) (nat_lit 0) D2M8K2.t15975 from rfl, allE_node, rows15974, irow15965, rows15975]
  all_goals rfl

theorem atot15965 : totK PD2M8K2 D2M8K2.u15965 = [0, 0, 0, 451388968886, 996224189751, 322526778067, 8302628378, 0] := by
  rw [show D2M8K2.u15965 = KTree.node D2M8K2.t15974 (nat_lit 34618891) (nat_lit 1619810307) (nat_lit 0) D2M8K2.t15975 from rfl, totK_node, tot15974, tot15975]
  decide +kernel

theorem arows15968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15968 = true := by
  rw [show D2M8K2.u15968 = KTree.node D2M8K2.t15976 (nat_lit 34622289) (nat_lit 1832012323) (nat_lit 0) D2M8K2.t15977 from rfl, allE_node, rows15976, irow15968, rows15977]
  all_goals rfl

theorem atot15968 : totK PD2M8K2 D2M8K2.u15968 = [0, 0, 0, 453360222429, 966018190191, 312888929254, 12350542027, 0] := by
  rw [show D2M8K2.u15968 = KTree.node D2M8K2.t15976 (nat_lit 34622289) (nat_lit 1832012323) (nat_lit 0) D2M8K2.t15977 from rfl, totK_node, tot15976, tot15977]
  decide +kernel

theorem arows15969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15969 = true := by
  rw [show D2M8K2.u15969 = KTree.node D2M8K2.t15978 (nat_lit 34626042) (nat_lit 3885800288) (nat_lit 0) D2M8K2.t15979 from rfl, allE_node, rows15978, irow15969, rows15979]
  all_goals rfl

theorem atot15969 : totK PD2M8K2 D2M8K2.u15969 = [0, 0, 0, 491781942109, 991376301364, 287903360764, 6395644273, 0] := by
  rw [show D2M8K2.u15969 = KTree.node D2M8K2.t15978 (nat_lit 34626042) (nat_lit 3885800288) (nat_lit 0) D2M8K2.t15979 from rfl, totK_node, tot15978, tot15979]
  decide +kernel

theorem arows15971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15971 = true := by
  rw [show D2M8K2.u15971 = KTree.node D2M8K2.t15980 (nat_lit 34633269) (nat_lit 1499673756) (nat_lit 2) D2M8K2.t15981 from rfl, allE_node, rows15980, irow15971, rows15981]
  all_goals rfl

theorem atot15971 : totK PD2M8K2 D2M8K2.u15971 = [0, 0, 350817798294, 827751960273, 529825699373, 129478818333, 8863302705, 0] := by
  rw [show D2M8K2.u15971 = KTree.node D2M8K2.t15980 (nat_lit 34633269) (nat_lit 1499673756) (nat_lit 2) D2M8K2.t15981 from rfl, totK_node, tot15980, tot15981]
  decide +kernel

theorem arows15972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15972 = true := by
  rw [show D2M8K2.u15972 = KTree.node D2M8K2.t15982 (nat_lit 34634779) (nat_lit 1467629153) (nat_lit 512) D2M8K2.t15983 from rfl, allE_node, rows15982, irow15972, rows15983]
  all_goals rfl

theorem atot15972 : totK PD2M8K2 D2M8K2.u15972 = [0, 0, 89061927447, 647649112507, 839809159417, 257082477085, 12054718719, 0] := by
  rw [show D2M8K2.u15972 = KTree.node D2M8K2.t15982 (nat_lit 34634779) (nat_lit 1467629153) (nat_lit 512) D2M8K2.t15983 from rfl, totK_node, tot15982, tot15983]
  decide +kernel

theorem arows15976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15976 = true := by
  rw [show D2M8K2.u15976 = KTree.node D2M8K2.t15984 (nat_lit 34636612) (nat_lit 3869846782) (nat_lit 0) D2M8K2.t15985 from rfl, allE_node, rows15984, irow15976, rows15985]
  all_goals rfl

theorem atot15976 : totK PD2M8K2 D2M8K2.u15976 = [0, 0, 330174998102, 832190682820, 578273773981, 126039390898, 4239164426, 0] := by
  rw [show D2M8K2.u15976 = KTree.node D2M8K2.t15984 (nat_lit 34636612) (nat_lit 3869846782) (nat_lit 0) D2M8K2.t15985 from rfl, totK_node, tot15984, tot15985]
  decide +kernel

theorem arows15977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15977 = true := by
  rw [show D2M8K2.u15977 = KTree.node D2M8K2.t15986 (nat_lit 34640372) (nat_lit 3173041556) (nat_lit 0) D2M8K2.t15987 from rfl, allE_node, rows15986, irow15977, rows15987]
  all_goals rfl

theorem atot15977 : totK PD2M8K2 D2M8K2.u15977 = [0, 0, 370633868853, 928866331576, 484354101646, 40747487909, 0, 0] := by
  rw [show D2M8K2.u15977 = KTree.node D2M8K2.t15986 (nat_lit 34640372) (nat_lit 3173041556) (nat_lit 0) D2M8K2.t15987 from rfl, totK_node, tot15986, tot15987]
  decide +kernel

theorem arows15979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15979 = true := by
  rw [show D2M8K2.u15979 = KTree.node D2M8K2.t15988 (nat_lit 34642161) (nat_lit 1837442505) (nat_lit 0) D2M8K2.t15989 from rfl, allE_node, rows15988, irow15979, rows15989]
  all_goals rfl

theorem atot15979 : totK PD2M8K2 D2M8K2.u15979 = [0, 0, 123736637800, 668910579575, 849688586646, 180725881406, 4254338973, 0] := by
  rw [show D2M8K2.u15979 = KTree.node D2M8K2.t15988 (nat_lit 34642161) (nat_lit 1837442505) (nat_lit 0) D2M8K2.t15989 from rfl, totK_node, tot15988, tot15989]
  decide +kernel

theorem arows15980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15980 = true := by
  rw [show D2M8K2.u15980 = KTree.node D2M8K2.t15990 (nat_lit 34643986) (nat_lit 3734070206) (nat_lit 0) D2M8K2.t15991 from rfl, allE_node, rows15990, irow15980, rows15991]
  all_goals rfl

theorem atot15980 : totK PD2M8K2 D2M8K2.u15980 = [0, 0, 408443825540, 957866034663, 438188278830, 34760910737, 0, 0] := by
  rw [show D2M8K2.u15980 = KTree.node D2M8K2.t15990 (nat_lit 34643986) (nat_lit 3734070206) (nat_lit 0) D2M8K2.t15991 from rfl, totK_node, tot15990, tot15991]
  decide +kernel

theorem arows15983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15983 = true := by
  rw [show D2M8K2.u15983 = KTree.node D2M8K2.t15992 (nat_lit 34647343) (nat_lit 2447780778) (nat_lit 0) D2M8K2.t15993 from rfl, allE_node, rows15992, irow15983, rows15993]
  all_goals rfl

theorem atot15983 : totK PD2M8K2 D2M8K2.u15983 = [0, 0, 319790726093, 910541958473, 562483038036, 49318751780, 0, 0] := by
  rw [show D2M8K2.u15983 = KTree.node D2M8K2.t15992 (nat_lit 34647343) (nat_lit 2447780778) (nat_lit 0) D2M8K2.t15993 from rfl, totK_node, tot15992, tot15993]
  decide +kernel

theorem arows15984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15984 = true := by
  rw [show D2M8K2.u15984 = KTree.node D2M8K2.t15994 (nat_lit 34649266) (nat_lit 4101123793) (nat_lit 0) D2M8K2.t15995 from rfl, allE_node, rows15994, irow15984, rows15995]
  all_goals rfl

theorem atot15984 : totK PD2M8K2 D2M8K2.u15984 = [0, 0, 111472069962, 622166300706, 826583608900, 245933872895, 12632203081, 0] := by
  rw [show D2M8K2.u15984 = KTree.node D2M8K2.t15994 (nat_lit 34649266) (nat_lit 4101123793) (nat_lit 0) D2M8K2.t15995 from rfl, totK_node, tot15994, tot15995]
  decide +kernel

theorem arows15986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15986 = true := by
  rw [show D2M8K2.u15986 = KTree.node D2M8K2.t15996 (nat_lit 34713330) (nat_lit 3423319321) (nat_lit 0) D2M8K2.t15997 from rfl, allE_node, rows15996, irow15986, rows15997]
  all_goals rfl

theorem atot15986 : totK PD2M8K2 D2M8K2.u15986 = [0, 0, 297984264638, 868754481394, 541373110584, 54763585605, 0, 0] := by
  rw [show D2M8K2.u15986 = KTree.node D2M8K2.t15996 (nat_lit 34713330) (nat_lit 3423319321) (nat_lit 0) D2M8K2.t15997 from rfl, totK_node, tot15996, tot15997]
  decide +kernel

theorem arows15987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15987 = true := by
  rw [show D2M8K2.u15987 = KTree.node D2M8K2.t15998 (nat_lit 34715315) (nat_lit 2893975146) (nat_lit 0) D2M8K2.t15999 from rfl, allE_node, rows15998, irow15987, rows15999]
  all_goals rfl

theorem atot15987 : totK PD2M8K2 D2M8K2.u15987 = [0, 0, 193349602110, 744509644216, 770882316990, 110049252713, 0, 0] := by
  rw [show D2M8K2.u15987 = KTree.node D2M8K2.t15998 (nat_lit 34715315) (nat_lit 2893975146) (nat_lit 0) D2M8K2.t15999 from rfl, totK_node, tot15998, tot15999]
  decide +kernel

theorem arows15994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15994 = true := by
  rw [show D2M8K2.u15994 = KTree.node D2M8K2.t16000 (nat_lit 34717044) (nat_lit 3015794576) (nat_lit 0) D2M8K2.t16001 from rfl, allE_node, rows16000, irow15994, rows16001]
  all_goals rfl

theorem atot15994 : totK PD2M8K2 D2M8K2.u15994 = [0, 0, 225707023561, 792869376289, 655534829569, 148008624057, 10519103133, 0] := by
  rw [show D2M8K2.u15994 = KTree.node D2M8K2.t16000 (nat_lit 34717044) (nat_lit 3015794576) (nat_lit 0) D2M8K2.t16001 from rfl, totK_node, tot16000, tot16001]
  decide +kernel

theorem arows15995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15995 = true := by
  rw [show D2M8K2.u15995 = KTree.node D2M8K2.t16002 (nat_lit 34718953) (nat_lit 1319248883) (nat_lit 0) D2M8K2.t16003 from rfl, allE_node, rows16002, irow15995, rows16003]
  all_goals rfl

theorem atot15995 : totK PD2M8K2 D2M8K2.u15995 = [0, 0, 175566839615, 686036418258, 748667611181, 208596125893, 5774780012, 0] := by
  rw [show D2M8K2.u15995 = KTree.node D2M8K2.t16002 (nat_lit 34718953) (nat_lit 1319248883) (nat_lit 0) D2M8K2.t16003 from rfl, totK_node, tot16002, tot16003]
  decide +kernel

theorem arows15997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15997 = true := by
  rw [show D2M8K2.u15997 = KTree.node D2M8K2.t16004 (nat_lit 34723884) (nat_lit 3556071319) (nat_lit 0) D2M8K2.t16005 from rfl, allE_node, rows16004, irow15997, rows16005]
  all_goals rfl

theorem atot15997 : totK PD2M8K2 D2M8K2.u15997 = [0, 0, 268646207831, 812878994137, 632495511318, 102747831284, 1198073392, 0] := by
  rw [show D2M8K2.u15997 = KTree.node D2M8K2.t16004 (nat_lit 34723884) (nat_lit 3556071319) (nat_lit 0) D2M8K2.t16005 from rfl, totK_node, tot16004, tot16005]
  decide +kernel

theorem arows15998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15998 = true := by
  rw [show D2M8K2.u15998 = KTree.node D2M8K2.t16006 (nat_lit 34725528) (nat_lit 3247267020) (nat_lit 0) D2M8K2.t16007 from rfl, allE_node, rows16006, irow15998, rows16007]
  all_goals rfl

theorem atot15998 : totK PD2M8K2 D2M8K2.u15998 = [0, 0, 158989738083, 631855324606, 747206868306, 226386493912, 12052611869, 0] := by
  rw [show D2M8K2.u15998 = KTree.node D2M8K2.t16006 (nat_lit 34725528) (nat_lit 3247267020) (nat_lit 0) D2M8K2.t16007 from rfl, totK_node, tot16006, tot16007]
  decide +kernel

theorem arows16001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16001 = true := by
  rw [show D2M8K2.u16001 = KTree.node D2M8K2.t16008 (nat_lit 34727091) (nat_lit 3191223310) (nat_lit 2048) D2M8K2.t16009 from rfl, allE_node, rows16008, irow16001, rows16009]
  all_goals rfl

theorem atot16001 : totK PD2M8K2 D2M8K2.u16001 = [0, 0, 232400187462, 792822607605, 666687659497, 90224812603, 1096505104, 0] := by
  rw [show D2M8K2.u16001 = KTree.node D2M8K2.t16008 (nat_lit 34727091) (nat_lit 3191223310) (nat_lit 2048) D2M8K2.t16009 from rfl, totK_node, tot16008, tot16009]
  decide +kernel

theorem arows16002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16002 = true := by
  rw [show D2M8K2.u16002 = KTree.node D2M8K2.t16010 (nat_lit 34729465) (nat_lit 1524685871) (nat_lit 0) D2M8K2.t16011 from rfl, allE_node, rows16010, irow16002, rows16011]
  all_goals rfl

theorem atot16002 : totK PD2M8K2 D2M8K2.u16002 = [0, 0, 239247000468, 771093277487, 644671858235, 118536320140, 3884009855, 0] := by
  rw [show D2M8K2.u16002 = KTree.node D2M8K2.t16010 (nat_lit 34729465) (nat_lit 1524685871) (nat_lit 0) D2M8K2.t16011 from rfl, totK_node, tot16010, tot16011]
  decide +kernel

theorem arows16004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16004 = true := by
  rw [show D2M8K2.u16004 = KTree.node D2M8K2.t16012 (nat_lit 34730987) (nat_lit 2898299648) (nat_lit 0) D2M8K2.t16013 from rfl, allE_node, rows16012, irow16004, rows16013]
  all_goals rfl

theorem atot16004 : totK PD2M8K2 D2M8K2.u16004 = [0, 0, 182137505762, 756370396879, 747774381441, 121545867505, 1268739303, 0] := by
  rw [show D2M8K2.u16004 = KTree.node D2M8K2.t16012 (nat_lit 34730987) (nat_lit 2898299648) (nat_lit 0) D2M8K2.t16013 from rfl, totK_node, tot16012, tot16013]
  decide +kernel

theorem arows16005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16005 = true := by
  rw [show D2M8K2.u16005 = KTree.node D2M8K2.t16014 (nat_lit 34732718) (nat_lit 1898503808) (nat_lit 0) D2M8K2.t16015 from rfl, allE_node, rows16014, irow16005, rows16015]
  all_goals rfl

theorem atot16005 : totK PD2M8K2 D2M8K2.u16005 = [0, 0, 0, 377158700098, 962198670022, 375653028635, 18349103821, 0] := by
  rw [show D2M8K2.u16005 = KTree.node D2M8K2.t16014 (nat_lit 34732718) (nat_lit 1898503808) (nat_lit 0) D2M8K2.t16015 from rfl, totK_node, tot16014, tot16015]
  decide +kernel

theorem arows16009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16009 = true := by
  rw [show D2M8K2.u16009 = KTree.node D2M8K2.t16016 (nat_lit 34734384) (nat_lit 3701496321) (nat_lit 0) D2M8K2.t16017 from rfl, allE_node, rows16016, irow16009, rows16017]
  all_goals rfl

theorem atot16009 : totK PD2M8K2 D2M8K2.u16009 = [0, 0, 0, 207669029158, 809975145813, 613103395106, 76329950949, 1217496766] := by
  rw [show D2M8K2.u16009 = KTree.node D2M8K2.t16016 (nat_lit 34734384) (nat_lit 3701496321) (nat_lit 0) D2M8K2.t16017 from rfl, totK_node, tot16016, tot16017]
  decide +kernel

theorem arows16010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16010 = true := by
  rw [show D2M8K2.u16010 = KTree.node D2M8K2.t16018 (nat_lit 34736974) (nat_lit 3916804907) (nat_lit 0) D2M8K2.t16019 from rfl, allE_node, rows16018, irow16010, rows16019]
  all_goals rfl

theorem atot16010 : totK PD2M8K2 D2M8K2.u16010 = [0, 0, 0, 413394671844, 948149022785, 437139585055, 25190847844, 0] := by
  rw [show D2M8K2.u16010 = KTree.node D2M8K2.t16018 (nat_lit 34736974) (nat_lit 3916804907) (nat_lit 0) D2M8K2.t16019 from rfl, totK_node, tot16018, tot16019]
  decide +kernel

theorem arows16012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16012 = true := by
  rw [show D2M8K2.u16012 = KTree.node D2M8K2.t16020 (nat_lit 34744041) (nat_lit 1821171256) (nat_lit 0) D2M8K2.t16021 from rfl, allE_node, rows16020, irow16012, rows16021]
  all_goals rfl

theorem atot16012 : totK PD2M8K2 D2M8K2.u16012 = [0, 0, 0, 383677912588, 942393500720, 441058879769, 29533539369, 0] := by
  rw [show D2M8K2.u16012 = KTree.node D2M8K2.t16020 (nat_lit 34744041) (nat_lit 1821171256) (nat_lit 0) D2M8K2.t16021 from rfl, totK_node, tot16020, tot16021]
  decide +kernel

theorem arows16013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16013 = true := by
  rw [show D2M8K2.u16013 = KTree.node D2M8K2.t16022 (nat_lit 34745765) (nat_lit 1112886366) (nat_lit 512) D2M8K2.t16023 from rfl, allE_node, rows16022, irow16013, rows16023]
  all_goals rfl

theorem atot16013 : totK PD2M8K2 D2M8K2.u16013 = [0, 0, 0, 94027904595, 653745319188, 813856607326, 179382282064, 5425831197] := by
  rw [show D2M8K2.u16013 = KTree.node D2M8K2.t16022 (nat_lit 34745765) (nat_lit 1112886366) (nat_lit 512) D2M8K2.t16023 from rfl, totK_node, tot16022, tot16023]
  decide +kernel

theorem arows16016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16016 = true := by
  rw [show D2M8K2.u16016 = KTree.node D2M8K2.t16024 (nat_lit 34747733) (nat_lit 1489464751) (nat_lit 0) D2M8K2.t16025 from rfl, allE_node, rows16024, irow16016, rows16025]
  all_goals rfl

theorem atot16016 : totK PD2M8K2 D2M8K2.u16016 = [0, 0, 0, 456131590845, 969599337173, 311726412386, 10225021512, 0] := by
  rw [show D2M8K2.u16016 = KTree.node D2M8K2.t16024 (nat_lit 34747733) (nat_lit 1489464751) (nat_lit 0) D2M8K2.t16025 from rfl, totK_node, tot16024, tot16025]
  decide +kernel

theorem arows16017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16017 = true := by
  rw [show D2M8K2.u16017 = KTree.node D2M8K2.t16026 (nat_lit 34751193) (nat_lit 1802881438) (nat_lit 0) D2M8K2.t16027 from rfl, allE_node, rows16026, irow16017, rows16027]
  all_goals rfl

theorem atot16017 : totK PD2M8K2 D2M8K2.u16017 = [0, 0, 99421869408, 533942853355, 802524825868, 337247492068, 24829883820, 0] := by
  rw [show D2M8K2.u16017 = KTree.node D2M8K2.t16026 (nat_lit 34751193) (nat_lit 1802881438) (nat_lit 0) D2M8K2.t16027 from rfl, totK_node, tot16026, tot16027]
  decide +kernel

theorem arows16019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16019 = true := by
  rw [show D2M8K2.u16019 = KTree.node D2M8K2.t16028 (nat_lit 34754781) (nat_lit 1569723249) (nat_lit 0) D2M8K2.t16029 from rfl, allE_node, rows16028, irow16019, rows16029]
  all_goals rfl

theorem atot16019 : totK PD2M8K2 D2M8K2.u16019 = [0, 0, 291630003927, 857748976146, 535504647137, 64147259360, 1310517177, 0] := by
  rw [show D2M8K2.u16019 = KTree.node D2M8K2.t16028 (nat_lit 34754781) (nat_lit 1569723249) (nat_lit 0) D2M8K2.t16029 from rfl, totK_node, tot16028, tot16029]
  decide +kernel

theorem arows16020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16020 = true := by
  rw [show D2M8K2.u16020 = KTree.node D2M8K2.t16030 (nat_lit 34757390) (nat_lit 3885436770) (nat_lit 0) D2M8K2.t16031 from rfl, allE_node, rows16030, irow16020, rows16031]
  all_goals rfl

theorem atot16020 : totK PD2M8K2 D2M8K2.u16020 = [0, 0, 254995099234, 850648491359, 667945649059, 58838453532, 0, 0] := by
  rw [show D2M8K2.u16020 = KTree.node D2M8K2.t16030 (nat_lit 34757390) (nat_lit 3885436770) (nat_lit 0) D2M8K2.t16031 from rfl, totK_node, tot16030, tot16031]
  decide +kernel

theorem arows16025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16025 = true := by
  rw [show D2M8K2.u16025 = KTree.node D2M8K2.t16032 (nat_lit 34764173) (nat_lit 1096194916) (nat_lit 0) D2M8K2.t16033 from rfl, allE_node, rows16032, irow16025, rows16033]
  all_goals rfl

theorem atot16025 : totK PD2M8K2 D2M8K2.u16025 = [0, 0, 409186126312, 969720939620, 433378927422, 25334498284, 0, 0] := by
  rw [show D2M8K2.u16025 = KTree.node D2M8K2.t16032 (nat_lit 34764173) (nat_lit 1096194916) (nat_lit 0) D2M8K2.t16033 from rfl, totK_node, tot16032, tot16033]
  decide +kernel

theorem arows16026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16026 = true := by
  rw [show D2M8K2.u16026 = KTree.node D2M8K2.t16034 (nat_lit 34767439) (nat_lit 2421296594) (nat_lit 0) D2M8K2.t16035 from rfl, allE_node, rows16034, irow16026, rows16035]
  all_goals rfl

theorem atot16026 : totK PD2M8K2 D2M8K2.u16026 = [0, 0, 400415469994, 949455135321, 429837582434, 23369365458, 0, 0] := by
  rw [show D2M8K2.u16026 = KTree.node D2M8K2.t16034 (nat_lit 34767439) (nat_lit 2421296594) (nat_lit 0) D2M8K2.t16035 from rfl, totK_node, tot16034, tot16035]
  decide +kernel

theorem arows16028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16028 = true := by
  rw [show D2M8K2.u16028 = KTree.node D2M8K2.t16036 (nat_lit 34768682) (nat_lit 4182302026) (nat_lit 0) D2M8K2.t16037 from rfl, allE_node, rows16036, irow16028, rows16037]
  all_goals rfl

theorem atot16028 : totK PD2M8K2 D2M8K2.u16028 = [0, 0, 180530429488, 796158691735, 703965675127, 88735367259, 1096505104, 0] := by
  rw [show D2M8K2.u16028 = KTree.node D2M8K2.t16036 (nat_lit 34768682) (nat_lit 4182302026) (nat_lit 0) D2M8K2.t16037 from rfl, totK_node, tot16036, tot16037]
  decide +kernel

theorem arows16029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16029 = true := by
  rw [show D2M8K2.u16029 = KTree.node D2M8K2.t16038 (nat_lit 34795234) (nat_lit 3847006074) (nat_lit 0) D2M8K2.t16039 from rfl, allE_node, rows16038, irow16029, rows16039]
  all_goals rfl

theorem atot16029 : totK PD2M8K2 D2M8K2.u16029 = [0, 0, 271860929665, 806508246435, 593732278896, 106682004330, 3884009855, 0] := by
  rw [show D2M8K2.u16029 = KTree.node D2M8K2.t16038 (nat_lit 34795234) (nat_lit 3847006074) (nat_lit 0) D2M8K2.t16039 from rfl, totK_node, tot16038, tot16039]
  decide +kernel

theorem arows16032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16032 = true := by
  rw [show D2M8K2.u16032 = KTree.node D2M8K2.t16040 (nat_lit 34796852) (nat_lit 3372263354) (nat_lit 0) D2M8K2.t16041 from rfl, allE_node, rows16040, irow16032, rows16041]
  all_goals rfl

theorem atot16032 : totK PD2M8K2 D2M8K2.u16032 = [0, 0, 134690097165, 717793604957, 800196818035, 120894607212, 1369150432, 0] := by
  rw [show D2M8K2.u16032 = KTree.node D2M8K2.t16040 (nat_lit 34796852) (nat_lit 3372263354) (nat_lit 0) D2M8K2.t16041 from rfl, totK_node, tot16040, tot16041]
  decide +kernel

theorem arows16033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16033 = true := by
  rw [show D2M8K2.u16033 = KTree.node D2M8K2.t16042 (nat_lit 34799211) (nat_lit 3731856320) (nat_lit 0) D2M8K2.t16043 from rfl, allE_node, rows16042, irow16033, rows16043]
  all_goals rfl

theorem atot16033 : totK PD2M8K2 D2M8K2.u16033 = [0, 0, 378118201470, 921148876676, 514519671543, 44428819321, 0, 0] := by
  rw [show D2M8K2.u16033 = KTree.node D2M8K2.t16042 (nat_lit 34799211) (nat_lit 3731856320) (nat_lit 0) D2M8K2.t16043 from rfl, totK_node, tot16042, tot16043]
  decide +kernel

theorem arows16035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16035 = true := by
  rw [show D2M8K2.u16035 = KTree.node D2M8K2.t16044 (nat_lit 34800838) (nat_lit 3768203334) (nat_lit 0) D2M8K2.t16045 from rfl, allE_node, rows16044, irow16035, rows16045]
  all_goals rfl

theorem atot16035 : totK PD2M8K2 D2M8K2.u16035 = [0, 0, 37815634106, 577363480371, 940962267836, 280965654524, 12054718719, 0] := by
  rw [show D2M8K2.u16035 = KTree.node D2M8K2.t16044 (nat_lit 34800838) (nat_lit 3768203334) (nat_lit 0) D2M8K2.t16045 from rfl, totK_node, tot16044, tot16045]
  decide +kernel

theorem arows16036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16036 = true := by
  rw [show D2M8K2.u16036 = KTree.node D2M8K2.t16046 (nat_lit 34802496) (nat_lit 3705351137) (nat_lit 0) D2M8K2.t16047 from rfl, allE_node, rows16046, irow16036, rows16047]
  all_goals rfl

theorem atot16036 : totK PD2M8K2 D2M8K2.u16036 = [0, 0, 343255783374, 893522524795, 506239915466, 87481577963, 4239164426, 0] := by
  rw [show D2M8K2.u16036 = KTree.node D2M8K2.t16046 (nat_lit 34802496) (nat_lit 3705351137) (nat_lit 0) D2M8K2.t16047 from rfl, totK_node, tot16046, tot16047]
  decide +kernel

theorem arows16040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16040 = true := by
  rw [show D2M8K2.u16040 = KTree.node D2M8K2.t16048 (nat_lit 34804499) (nat_lit 2330070553) (nat_lit 0) D2M8K2.t16049 from rfl, allE_node, rows16048, irow16040, rows16049]
  all_goals rfl

theorem atot16040 : totK PD2M8K2 D2M8K2.u16040 = [0, 0, 171310374970, 689992564421, 764146688548, 167686682705, 5172807878, 0] := by
  rw [show D2M8K2.u16040 = KTree.node D2M8K2.t16048 (nat_lit 34804499) (nat_lit 2330070553) (nat_lit 0) D2M8K2.t16049 from rfl, totK_node, tot16048, tot16049]
  decide +kernel

theorem arows16041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16041 = true := by
  rw [show D2M8K2.u16041 = KTree.node D2M8K2.t16050 (nat_lit 34806694) (nat_lit 1206156577) (nat_lit 0) D2M8K2.t16051 from rfl, allE_node, rows16050, irow16041, rows16051]
  all_goals rfl

theorem atot16041 : totK PD2M8K2 D2M8K2.u16041 = [0, 0, 251378321267, 791637945478, 647353013045, 97129608572, 1198073392, 0] := by
  rw [show D2M8K2.u16041 = KTree.node D2M8K2.t16050 (nat_lit 34806694) (nat_lit 1206156577) (nat_lit 0) D2M8K2.t16051 from rfl, totK_node, tot16050, tot16051]
  decide +kernel

theorem arows16043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16043 = true := by
  rw [show D2M8K2.u16043 = KTree.node D2M8K2.t16052 (nat_lit 34808404) (nat_lit 2142783422) (nat_lit 0) D2M8K2.t16053 from rfl, allE_node, rows16052, irow16043, rows16053]
  all_goals rfl

theorem atot16043 : totK PD2M8K2 D2M8K2.u16043 = [0, 0, 142241969926, 644025741621, 794448599228, 210334999188, 7698146732, 0] := by
  rw [show D2M8K2.u16043 = KTree.node D2M8K2.t16052 (nat_lit 34808404) (nat_lit 2142783422) (nat_lit 0) D2M8K2.t16053 from rfl, totK_node, tot16052, tot16053]
  decide +kernel

theorem arows16044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16044 = true := by
  rw [show D2M8K2.u16044 = KTree.node D2M8K2.t16054 (nat_lit 34813251) (nat_lit 3551884385) (nat_lit 0) D2M8K2.t16055 from rfl, allE_node, rows16054, irow16044, rows16055]
  all_goals rfl

theorem atot16044 : totK PD2M8K2 D2M8K2.u16044 = [0, 0, 295558996404, 885624368105, 598836065039, 56340360686, 0, 0] := by
  rw [show D2M8K2.u16044 = KTree.node D2M8K2.t16054 (nat_lit 34813251) (nat_lit 3551884385) (nat_lit 0) D2M8K2.t16055 from rfl, totK_node, tot16054, tot16055]
  decide +kernel

theorem arows16047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16047 = true := by
  rw [show D2M8K2.u16047 = KTree.node D2M8K2.t16056 (nat_lit 34814902) (nat_lit 3495012443) (nat_lit 0) D2M8K2.t16057 from rfl, allE_node, rows16056, irow16047, rows16057]
  all_goals rfl

theorem atot16047 : totK PD2M8K2 D2M8K2.u16047 = [0, 33390828244, 34931502242, 379528742648, 925041963164, 387366760675, 21982715828, 0] := by
  rw [show D2M8K2.u16047 = KTree.node D2M8K2.t16056 (nat_lit 34814902) (nat_lit 3495012443) (nat_lit 0) D2M8K2.t16057 from rfl, totK_node, tot16056, tot16057]
  decide +kernel

theorem arows16048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16048 = true := by
  rw [show D2M8K2.u16048 = KTree.node D2M8K2.t16058 (nat_lit 35335098) (nat_lit 3935039902) (nat_lit 0) D2M8K2.t16059 from rfl, allE_node, rows16058, irow16048, rows16059]
  all_goals rfl

theorem atot16048 : totK PD2M8K2 D2M8K2.u16048 = [0, 390343913227, 955698892106, 425108342652, 22386190152, 0, 0, 0] := by
  rw [show D2M8K2.u16048 = KTree.node D2M8K2.t16058 (nat_lit 35335098) (nat_lit 3935039902) (nat_lit 0) D2M8K2.t16059 from rfl, totK_node, tot16058, tot16059]
  decide +kernel

theorem arows16050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16050 = true := by
  rw [show D2M8K2.u16050 = KTree.node D2M8K2.t16060 (nat_lit 35336743) (nat_lit 2391034705) (nat_lit 0) D2M8K2.t16061 from rfl, allE_node, rows16060, irow16050, rows16061]
  all_goals rfl

theorem atot16050 : totK PD2M8K2 D2M8K2.u16050 = [0, 99167858691, 671320703654, 888079215855, 154706468079, 1369150432, 0, 0] := by
  rw [show D2M8K2.u16050 = KTree.node D2M8K2.t16060 (nat_lit 35336743) (nat_lit 2391034705) (nat_lit 0) D2M8K2.t16061 from rfl, totK_node, tot16060, tot16061]
  decide +kernel

theorem arows16051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16051 = true := by
  rw [show D2M8K2.u16051 = KTree.node D2M8K2.t16062 (nat_lit 35341836) (nat_lit 3036536356) (nat_lit 0) D2M8K2.t16063 from rfl, allE_node, rows16062, irow16051, rows16063]
  all_goals rfl

theorem atot16051 : totK PD2M8K2 D2M8K2.u16051 = [0, 324193727878, 917004285531, 519218747196, 37785792282, 0, 0, 0] := by
  rw [show D2M8K2.u16051 = KTree.node D2M8K2.t16062 (nat_lit 35341836) (nat_lit 3036536356) (nat_lit 0) D2M8K2.t16063 from rfl, totK_node, tot16062, tot16063]
  decide +kernel

theorem arows16057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16057 = true := by
  rw [show D2M8K2.u16057 = KTree.node D2M8K2.t16064 (nat_lit 35343537) (nat_lit 1084941359) (nat_lit 512) D2M8K2.t16065 from rfl, allE_node, rows16064, irow16057, rows16065]
  all_goals rfl

theorem atot16057 : totK PD2M8K2 D2M8K2.u16057 = [0, 75698288311, 521010786644, 904780192691, 268034809821, 8815471973, 0, 0] := by
  rw [show D2M8K2.u16057 = KTree.node D2M8K2.t16064 (nat_lit 35343537) (nat_lit 1084941359) (nat_lit 512) D2M8K2.t16065 from rfl, totK_node, tot16064, tot16065]
  decide +kernel

theorem arows16058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16058 = true := by
  rw [show D2M8K2.u16058 = KTree.node D2M8K2.t16066 (nat_lit 35345555) (nat_lit 2692871986) (nat_lit 0) D2M8K2.t16067 from rfl, allE_node, rows16066, irow16058, rows16067]
  all_goals rfl

theorem atot16058 : totK PD2M8K2 D2M8K2.u16058 = [0, 332378351431, 925227400411, 508908310813, 36315628748, 0, 0, 0] := by
  rw [show D2M8K2.u16058 = KTree.node D2M8K2.t16066 (nat_lit 35345555) (nat_lit 2692871986) (nat_lit 0) D2M8K2.t16067 from rfl, totK_node, tot16066, tot16067]
  decide +kernel

theorem arows16060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16060 = true := by
  rw [show D2M8K2.u16060 = KTree.node D2M8K2.t16068 (nat_lit 35347257) (nat_lit 1673183251) (nat_lit 0) D2M8K2.t16069 from rfl, allE_node, rows16068, irow16060, rows16069]
  all_goals rfl

theorem atot16060 : totK PD2M8K2 D2M8K2.u16060 = [0, 57940408170, 510955209369, 920836086894, 281088356624, 8916669049, 0, 0] := by
  rw [show D2M8K2.u16060 = KTree.node D2M8K2.t16068 (nat_lit 35347257) (nat_lit 1673183251) (nat_lit 0) D2M8K2.t16069 from rfl, totK_node, tot16068, tot16069]
  decide +kernel

theorem arows16061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16061 = true := by
  rw [show D2M8K2.u16061 = KTree.node D2M8K2.t16070 (nat_lit 35348992) (nat_lit 1763908411) (nat_lit 0) D2M8K2.t16071 from rfl, allE_node, rows16070, irow16061, rows16071]
  all_goals rfl

theorem atot16061 : totK PD2M8K2 D2M8K2.u16061 = [0, 262694263894, 849655335950, 582818816503, 70456617609, 1096505104, 0, 0] := by
  rw [show D2M8K2.u16061 = KTree.node D2M8K2.t16070 (nat_lit 35348992) (nat_lit 1763908411) (nat_lit 0) D2M8K2.t16071 from rfl, totK_node, tot16070, tot16071]
  decide +kernel

theorem arows16064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16064 = true := by
  rw [show D2M8K2.u16064 = KTree.node D2M8K2.t16072 (nat_lit 35351671) (nat_lit 2189715180) (nat_lit 0) D2M8K2.t16073 from rfl, allE_node, rows16072, irow16064, rows16073]
  all_goals rfl

theorem atot16064 : totK PD2M8K2 D2M8K2.u16064 = [0, 258805175473, 840223347229, 645848071686, 69874281537, 0, 0, 0] := by
  rw [show D2M8K2.u16064 = KTree.node D2M8K2.t16072 (nat_lit 35351671) (nat_lit 2189715180) (nat_lit 0) D2M8K2.t16073 from rfl, totK_node, tot16072, tot16073]
  decide +kernel

theorem arows16065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16065 = true := by
  rw [show D2M8K2.u16065 = KTree.node D2M8K2.t16074 (nat_lit 35353156) (nat_lit 3772546580) (nat_lit 0) D2M8K2.t16075 from rfl, allE_node, rows16074, irow16065, rows16075]
  all_goals rfl

theorem atot16065 : totK PD2M8K2 D2M8K2.u16065 = [0, 166260413610, 702740281630, 769947769559, 167433463819, 2304167554, 0, 0] := by
  rw [show D2M8K2.u16065 = KTree.node D2M8K2.t16074 (nat_lit 35353156) (nat_lit 3772546580) (nat_lit 0) D2M8K2.t16075 from rfl, totK_node, tot16074, tot16075]
  decide +kernel

theorem arows16067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16067 = true := by
  rw [show D2M8K2.u16067 = KTree.node D2M8K2.t16076 (nat_lit 35354822) (nat_lit 2402240433) (nat_lit 0) D2M8K2.t16077 from rfl, allE_node, rows16076, irow16067, rows16077]
  all_goals rfl

theorem atot16067 : totK PD2M8K2 D2M8K2.u16067 = [0, 0, 357198148365, 943727517096, 443152433622, 27657117930, 0, 0] := by
  rw [show D2M8K2.u16067 = KTree.node D2M8K2.t16076 (nat_lit 35354822) (nat_lit 2402240433) (nat_lit 0) D2M8K2.t16077 from rfl, totK_node, tot16076, tot16077]
  decide +kernel

theorem arows16068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16068 = true := by
  rw [show D2M8K2.u16068 = KTree.node D2M8K2.t16078 (nat_lit 35356369) (nat_lit 1492319315) (nat_lit 0) D2M8K2.t16079 from rfl, allE_node, rows16078, irow16068, rows16079]
  all_goals rfl

theorem atot16068 : totK PD2M8K2 D2M8K2.u16068 = [0, 0, 255616929805, 801104391080, 585631364582, 97287164687, 1369150432, 0] := by
  rw [show D2M8K2.u16068 = KTree.node D2M8K2.t16078 (nat_lit 35356369) (nat_lit 1492319315) (nat_lit 0) D2M8K2.t16079 from rfl, totK_node, tot16078, tot16079]
  decide +kernel

theorem arows16072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16072 = true := by
  rw [show D2M8K2.u16072 = KTree.node D2M8K2.t16080 (nat_lit 35361918) (nat_lit 3481212165) (nat_lit 0) D2M8K2.t16081 from rfl, allE_node, rows16080, irow16072, rows16081]
  all_goals rfl

theorem atot16072 : totK PD2M8K2 D2M8K2.u16072 = [0, 0, 247397327759, 865470996683, 608921695929, 49722461231, 0, 0] := by
  rw [show D2M8K2.u16072 = KTree.node D2M8K2.t16080 (nat_lit 35361918) (nat_lit 3481212165) (nat_lit 0) D2M8K2.t16081 from rfl, totK_node, tot16080, tot16081]
  decide +kernel

theorem arows16073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16073 = true := by
  rw [show D2M8K2.u16073 = KTree.node D2M8K2.t16082 (nat_lit 35365264) (nat_lit 3243269564) (nat_lit 0) D2M8K2.t16083 from rfl, allE_node, rows16082, irow16073, rows16083]
  all_goals rfl

theorem atot16073 : totK PD2M8K2 D2M8K2.u16073 = [0, 0, 399758825656, 966073880598, 407792605566, 14853662709, 0, 0] := by
  rw [show D2M8K2.u16073 = KTree.node D2M8K2.t16082 (nat_lit 35365264) (nat_lit 3243269564) (nat_lit 0) D2M8K2.t16083 from rfl, totK_node, tot16082, tot16083]
  decide +kernel

theorem arows16075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16075 = true := by
  rw [show D2M8K2.u16075 = KTree.node D2M8K2.t16084 (nat_lit 35366864) (nat_lit 2303420029) (nat_lit 0) D2M8K2.t16085 from rfl, allE_node, rows16084, irow16075, rows16085]
  all_goals rfl

theorem atot16075 : totK PD2M8K2 D2M8K2.u16075 = [0, 0, 338699210211, 942905073782, 454501903169, 22127727535, 0, 0] := by
  rw [show D2M8K2.u16075 = KTree.node D2M8K2.t16084 (nat_lit 35366864) (nat_lit 2303420029) (nat_lit 0) D2M8K2.t16085 from rfl, totK_node, tot16084, tot16085]
  decide +kernel

theorem arows16076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16076 = true := by
  rw [show D2M8K2.u16076 = KTree.node D2M8K2.t16086 (nat_lit 35372265) (nat_lit 1376156535) (nat_lit 512) D2M8K2.t16087 from rfl, allE_node, rows16086, irow16076, rows16087]
  all_goals rfl

theorem atot16076 : totK PD2M8K2 D2M8K2.u16076 = [0, 0, 400242636753, 963274879727, 403862866305, 14757551993, 0, 0] := by
  rw [show D2M8K2.u16076 = KTree.node D2M8K2.t16086 (nat_lit 35372265) (nat_lit 1376156535) (nat_lit 512) D2M8K2.t16087 from rfl, totK_node, tot16086, tot16087]
  decide +kernel

theorem arows16079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16079 = true := by
  rw [show D2M8K2.u16079 = KTree.node D2M8K2.t16088 (nat_lit 35373812) (nat_lit 1315756933) (nat_lit 0) D2M8K2.t16089 from rfl, allE_node, rows16088, irow16079, rows16089]
  all_goals rfl

theorem atot16079 : totK PD2M8K2 D2M8K2.u16079 = [0, 182603865993, 584127599272, 740017211276, 313027594066, 20237790448, 0, 0] := by
  rw [show D2M8K2.u16079 = KTree.node D2M8K2.t16088 (nat_lit 35373812) (nat_lit 1315756933) (nat_lit 0) D2M8K2.t16089 from rfl, totK_node, tot16088, tot16089]
  decide +kernel

theorem arows16080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16080 = true := by
  rw [show D2M8K2.u16080 = KTree.node D2M8K2.t16090 (nat_lit 35380443) (nat_lit 2575679770) (nat_lit 0) D2M8K2.t16091 from rfl, allE_node, rows16090, irow16080, rows16091]
  all_goals rfl

theorem atot16080 : totK PD2M8K2 D2M8K2.u16080 = [0, 261726886125, 831063174044, 608931061028, 121469598792, 13136570770, 0, 0] := by
  rw [show D2M8K2.u16080 = KTree.node D2M8K2.t16090 (nat_lit 35380443) (nat_lit 2575679770) (nat_lit 0) D2M8K2.t16091 from rfl, totK_node, tot16090, tot16091]
  decide +kernel

theorem arows16082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16082 = true := by
  rw [show D2M8K2.u16082 = KTree.node D2M8K2.t16092 (nat_lit 35381912) (nat_lit 3844024738) (nat_lit 0) D2M8K2.t16093 from rfl, allE_node, rows16092, irow16082, rows16093]
  all_goals rfl

theorem atot16082 : totK PD2M8K2 D2M8K2.u16082 = [0, 17512063623, 375244333020, 922312840998, 465956743309, 24472827335, 0, 0] := by
  rw [show D2M8K2.u16082 = KTree.node D2M8K2.t16092 (nat_lit 35381912) (nat_lit 3844024738) (nat_lit 0) D2M8K2.t16093 from rfl, totK_node, tot16092, tot16093]
  decide +kernel

theorem arows16083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16083 = true := by
  rw [show D2M8K2.u16083 = KTree.node D2M8K2.t16094 (nat_lit 35383200) (nat_lit 3228499149) (nat_lit 0) D2M8K2.t16095 from rfl, allE_node, rows16094, irow16083, rows16095]
  all_goals rfl

theorem atot16083 : totK PD2M8K2 D2M8K2.u16083 = [0, 393557353158, 940744752568, 461203458487, 34631574767, 0, 0, 0] := by
  rw [show D2M8K2.u16083 = KTree.node D2M8K2.t16094 (nat_lit 35383200) (nat_lit 3228499149) (nat_lit 0) D2M8K2.t16095 from rfl, totK_node, tot16094, tot16095]
  decide +kernel

theorem arows16088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16088 = true := by
  rw [show D2M8K2.u16088 = KTree.node D2M8K2.t16096 (nat_lit 35384894) (nat_lit 3821288067) (nat_lit 0) D2M8K2.t16097 from rfl, allE_node, rows16096, irow16088, rows16097]
  all_goals rfl

theorem atot16088 : totK PD2M8K2 D2M8K2.u16088 = [0, 0, 505654503237, 983082523558, 285418504453, 11623571359, 0, 0] := by
  rw [show D2M8K2.u16088 = KTree.node D2M8K2.t16096 (nat_lit 35384894) (nat_lit 3821288067) (nat_lit 0) D2M8K2.t16097 from rfl, totK_node, tot16096, tot16097]
  decide +kernel

theorem arows16089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16089 = true := by
  rw [show D2M8K2.u16089 = KTree.node D2M8K2.t16098 (nat_lit 35386921) (nat_lit 1491996615) (nat_lit 0) D2M8K2.t16099 from rfl, allE_node, rows16098, irow16089, rows16099]
  all_goals rfl

theorem atot16089 : totK PD2M8K2 D2M8K2.u16089 = [0, 395540202782, 942727933123, 459705977059, 34751833545, 0, 0, 0] := by
  rw [show D2M8K2.u16089 = KTree.node D2M8K2.t16098 (nat_lit 35386921) (nat_lit 1491996615) (nat_lit 0) D2M8K2.t16099 from rfl, totK_node, tot16098, tot16099]
  decide +kernel

theorem arows16091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16091 = true := by
  rw [show D2M8K2.u16091 = KTree.node D2M8K2.t16100 (nat_lit 35388617) (nat_lit 1055518918) (nat_lit 0) D2M8K2.t16101 from rfl, allE_node, rows16100, irow16091, rows16101]
  all_goals rfl

theorem atot16091 : totK PD2M8K2 D2M8K2.u16091 = [0, 19374756099, 517603780780, 951593372113, 287141186229, 11777714805, 0, 0] := by
  rw [show D2M8K2.u16091 = KTree.node D2M8K2.t16100 (nat_lit 35388617) (nat_lit 1055518918) (nat_lit 0) D2M8K2.t16101 from rfl, totK_node, tot16100, tot16101]
  decide +kernel

theorem arows16092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16092 = true := by
  rw [show D2M8K2.u16092 = KTree.node D2M8K2.t16102 (nat_lit 35390258) (nat_lit 3949341186) (nat_lit 0) D2M8K2.t16103 from rfl, allE_node, rows16102, irow16092, rows16103]
  all_goals rfl

theorem atot16092 : totK PD2M8K2 D2M8K2.u16092 = [0, 327550899068, 902447933969, 563002790840, 60798510533, 0, 0, 0] := by
  rw [show D2M8K2.u16092 = KTree.node D2M8K2.t16102 (nat_lit 35390258) (nat_lit 3949341186) (nat_lit 0) D2M8K2.t16103 from rfl, totK_node, tot16102, tot16103]
  decide +kernel

theorem arows16095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16095 = true := by
  rw [show D2M8K2.u16095 = KTree.node D2M8K2.t16104 (nat_lit 35392901) (nat_lit 2297959885) (nat_lit 0) D2M8K2.t16105 from rfl, allE_node, rows16104, irow16095, rows16105]
  all_goals rfl

theorem atot16095 : totK PD2M8K2 D2M8K2.u16095 = [0, 197663993741, 758421213276, 767998863561, 130228183535, 1493059870, 0, 0] := by
  rw [show D2M8K2.u16095 = KTree.node D2M8K2.t16104 (nat_lit 35392901) (nat_lit 2297959885) (nat_lit 0) D2M8K2.t16105 from rfl, totK_node, tot16104, tot16105]
  decide +kernel

theorem arows16096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16096 = true := by
  rw [show D2M8K2.u16096 = KTree.node D2M8K2.t16106 (nat_lit 35394395) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t16107 from rfl, allE_node, rows16106, irow16096, rows16107]
  all_goals rfl

theorem atot16096 : totK PD2M8K2 D2M8K2.u16096 = [0, 232063653139, 792613713597, 677837086762, 113526102281, 1267860612, 0, 0] := by
  rw [show D2M8K2.u16096 = KTree.node D2M8K2.t16106 (nat_lit 35394395) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t16107 from rfl, totK_node, tot16106, tot16107]
  decide +kernel

theorem arows16098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16098 = true := by
  rw [show D2M8K2.u16098 = KTree.node D2M8K2.t16108 (nat_lit 35396102) (nat_lit 4125681607) (nat_lit 0) D2M8K2.t16109 from rfl, allE_node, rows16108, irow16098, rows16109]
  all_goals rfl

theorem atot16098 : totK PD2M8K2 D2M8K2.u16098 = [0, 0, 359821910024, 918930259366, 481340379999, 40726128845, 0, 0] := by
  rw [show D2M8K2.u16098 = KTree.node D2M8K2.t16108 (nat_lit 35396102) (nat_lit 4125681607) (nat_lit 0) D2M8K2.t16109 from rfl, totK_node, tot16108, tot16109]
  decide +kernel

theorem arows16099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16099 = true := by
  rw [show D2M8K2.u16099 = KTree.node D2M8K2.t16110 (nat_lit 35400990) (nat_lit 3869046296) (nat_lit 0) D2M8K2.t16111 from rfl, allE_node, rows16110, irow16099, rows16111]
  all_goals rfl

theorem atot16099 : totK PD2M8K2 D2M8K2.u16099 = [0, 0, 349112804240, 931746018861, 517516652205, 40766704711, 0, 0] := by
  rw [show D2M8K2.u16099 = KTree.node D2M8K2.t16110 (nat_lit 35400990) (nat_lit 3869046296) (nat_lit 0) D2M8K2.t16111 from rfl, totK_node, tot16110, tot16111]
  decide +kernel

theorem arows16103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16103 = true := by
  rw [show D2M8K2.u16103 = KTree.node D2M8K2.t16112 (nat_lit 35402479) (nat_lit 2447849823) (nat_lit 0) D2M8K2.t16113 from rfl, allE_node, rows16112, irow16103, rows16113]
  all_goals rfl

theorem atot16103 : totK PD2M8K2 D2M8K2.u16103 = [0, 0, 0, 398611477430, 962332145229, 409385398312, 24368350617, 0] := by
  rw [show D2M8K2.u16103 = KTree.node D2M8K2.t16112 (nat_lit 35402479) (nat_lit 2447849823) (nat_lit 0) D2M8K2.t16113 from rfl, totK_node, tot16112, tot16113]
  decide +kernel

theorem arows16104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16104 = true := by
  rw [show D2M8K2.u16104 = KTree.node D2M8K2.t16114 (nat_lit 35403816) (nat_lit 2637903004) (nat_lit 0) D2M8K2.t16115 from rfl, allE_node, rows16114, irow16104, rows16115]
  all_goals rfl

theorem atot16104 : totK PD2M8K2 D2M8K2.u16104 = [0, 0, 342160275933, 843375109211, 493842078766, 109344089388, 6524090962, 0] := by
  rw [show D2M8K2.u16104 = KTree.node D2M8K2.t16114 (nat_lit 35403816) (nat_lit 2637903004) (nat_lit 0) D2M8K2.t16115 from rfl, totK_node, tot16114, tot16115]
  decide +kernel

theorem arows16106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16106 = true := by
  rw [show D2M8K2.u16106 = KTree.node D2M8K2.t16116 (nat_lit 35405610) (nat_lit 3099568646) (nat_lit 0) D2M8K2.t16117 from rfl, allE_node, rows16116, irow16106, rows16117]
  all_goals rfl

theorem atot16106 : totK PD2M8K2 D2M8K2.u16106 = [0, 0, 88948762272, 639405136519, 891600389280, 180005742148, 2665309491, 0] := by
  rw [show D2M8K2.u16106 = KTree.node D2M8K2.t16116 (nat_lit 35405610) (nat_lit 3099568646) (nat_lit 0) D2M8K2.t16117 from rfl, totK_node, tot16116, tot16117]
  decide +kernel

theorem arows16107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16107 = true := by
  rw [show D2M8K2.u16107 = KTree.node D2M8K2.t16118 (nat_lit 35407680) (nat_lit 3234836369) (nat_lit 0) D2M8K2.t16119 from rfl, allE_node, rows16118, irow16107, rows16119]
  all_goals rfl

theorem atot16107 : totK PD2M8K2 D2M8K2.u16107 = [0, 0, 396329743838, 941215454302, 453942482997, 33754344987, 0, 0] := by
  rw [show D2M8K2.u16107 = KTree.node D2M8K2.t16118 (nat_lit 35407680) (nat_lit 3234836369) (nat_lit 0) D2M8K2.t16119 from rfl, totK_node, tot16118, tot16119]
  decide +kernel

theorem arows16110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16110 = true := by
  rw [show D2M8K2.u16110 = KTree.node D2M8K2.t16120 (nat_lit 35409528) (nat_lit 3320083143) (nat_lit 0) D2M8K2.t16121 from rfl, allE_node, rows16120, irow16110, rows16121]
  all_goals rfl

theorem atot16110 : totK PD2M8K2 D2M8K2.u16110 = [0, 0, 89427196855, 644962839813, 884139653610, 185320718805, 2681443193, 0] := by
  rw [show D2M8K2.u16110 = KTree.node D2M8K2.t16120 (nat_lit 35409528) (nat_lit 3320083143) (nat_lit 0) D2M8K2.t16121 from rfl, totK_node, tot16120, tot16121]
  decide +kernel

theorem arows16111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16111 = true := by
  rw [show D2M8K2.u16111 = KTree.node D2M8K2.t16122 (nat_lit 35411197) (nat_lit 1130797583) (nat_lit 0) D2M8K2.t16123 from rfl, allE_node, rows16122, irow16111, rows16123]
  all_goals rfl

theorem atot16111 : totK PD2M8K2 D2M8K2.u16111 = [0, 0, 236905348790, 846450961357, 672727971470, 73765952291, 0, 0] := by
  rw [show D2M8K2.u16111 = KTree.node D2M8K2.t16122 (nat_lit 35411197) (nat_lit 1130797583) (nat_lit 0) D2M8K2.t16123 from rfl, totK_node, tot16122, tot16123]
  decide +kernel

theorem arows16113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16113 = true := by
  rw [show D2M8K2.u16113 = KTree.node D2M8K2.t16124 (nat_lit 35414019) (nat_lit 3717632037) (nat_lit 0) D2M8K2.t16125 from rfl, allE_node, rows16124, irow16113, rows16125]
  all_goals rfl

theorem atot16113 : totK PD2M8K2 D2M8K2.u16113 = [0, 0, 302328005208, 884044112346, 600075229815, 50355319385, 0, 0] := by
  rw [show D2M8K2.u16113 = KTree.node D2M8K2.t16124 (nat_lit 35414019) (nat_lit 3717632037) (nat_lit 0) D2M8K2.t16125 from rfl, totK_node, tot16124, tot16125]
  decide +kernel

theorem arows16114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16114 = true := by
  rw [show D2M8K2.u16114 = KTree.node D2M8K2.t16126 (nat_lit 35415680) (nat_lit 3594874641) (nat_lit 0) D2M8K2.t16127 from rfl, allE_node, rows16126, irow16114, rows16127]
  all_goals rfl

theorem atot16114 : totK PD2M8K2 D2M8K2.u16114 = [0, 0, 125579789091, 703721072011, 816987507815, 155214005682, 1238673482, 0] := by
  rw [show D2M8K2.u16114 = KTree.node D2M8K2.t16126 (nat_lit 35415680) (nat_lit 3594874641) (nat_lit 0) D2M8K2.t16127 from rfl, totK_node, tot16126, tot16127]
  decide +kernel

theorem arows16122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16122 = true := by
  rw [show D2M8K2.u16122 = KTree.node D2M8K2.t16128 (nat_lit 35417362) (nat_lit 4073638830) (nat_lit 0) D2M8K2.t16129 from rfl, allE_node, rows16128, irow16122, rows16129]
  all_goals rfl

theorem atot16122 : totK PD2M8K2 D2M8K2.u16122 = [0, 291089037037, 684261854017, 392827075316, 271632567333, 133026716877, 8063697217, 0] := by
  rw [show D2M8K2.u16122 = KTree.node D2M8K2.t16128 (nat_lit 35417362) (nat_lit 4073638830) (nat_lit 0) D2M8K2.t16129 from rfl, totK_node, tot16128, tot16129]
  decide +kernel

theorem arows16123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16123 = true := by
  rw [show D2M8K2.u16123 = KTree.node D2M8K2.t16130 (nat_lit 35418926) (nat_lit 2201867162) (nat_lit 0) D2M8K2.t16131 from rfl, allE_node, rows16130, irow16123, rows16131]
  all_goals rfl

theorem atot16123 : totK PD2M8K2 D2M8K2.u16123 = [0, 116092385875, 698773316517, 819951729606, 133974481187, 1369150432, 0, 0] := by
  rw [show D2M8K2.u16123 = KTree.node D2M8K2.t16130 (nat_lit 35418926) (nat_lit 2201867162) (nat_lit 0) D2M8K2.t16131 from rfl, totK_node, tot16130, tot16131]
  decide +kernel

theorem arows16125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16125 = true := by
  rw [show D2M8K2.u16125 = KTree.node D2M8K2.t16132 (nat_lit 35421256) (nat_lit 3844769005) (nat_lit 0) D2M8K2.t16133 from rfl, allE_node, rows16132, irow16125, rows16133]
  all_goals rfl

theorem atot16125 : totK PD2M8K2 D2M8K2.u16125 = [0, 330150843283, 904335824107, 553789887831, 54543236148, 0, 0, 0] := by
  rw [show D2M8K2.u16125 = KTree.node D2M8K2.t16132 (nat_lit 35421256) (nat_lit 3844769005) (nat_lit 0) D2M8K2.t16133 from rfl, totK_node, tot16132, tot16133]
  decide +kernel

theorem arows16126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16126 = true := by
  rw [show D2M8K2.u16126 = KTree.node D2M8K2.t16134 (nat_lit 35422805) (nat_lit 2145833384) (nat_lit 0) D2M8K2.t16135 from rfl, allE_node, rows16134, irow16126, rows16135]
  all_goals rfl

theorem atot16126 : totK PD2M8K2 D2M8K2.u16126 = [0, 88453318852, 508037517561, 827826471210, 374726540624, 27744257752, 0, 0] := by
  rw [show D2M8K2.u16126 = KTree.node D2M8K2.t16134 (nat_lit 35422805) (nat_lit 2145833384) (nat_lit 0) D2M8K2.t16135 from rfl, totK_node, tot16134, tot16135]
  decide +kernel

theorem arows16129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16129 = true := by
  rw [show D2M8K2.u16129 = KTree.node D2M8K2.t16136 (nat_lit 35424121) (nat_lit 1519018273) (nat_lit 0) D2M8K2.t16137 from rfl, allE_node, rows16136, irow16129, rows16137]
  all_goals rfl

theorem atot16129 : totK PD2M8K2 D2M8K2.u16129 = [0, 261217064945, 708151116889, 646367745442, 205846681905, 8209931632, 0, 0] := by
  rw [show D2M8K2.u16129 = KTree.node D2M8K2.t16136 (nat_lit 35424121) (nat_lit 1519018273) (nat_lit 0) D2M8K2.t16137 from rfl, totK_node, tot16136, tot16137]
  decide +kernel

theorem arows16130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16130 = true := by
  rw [show D2M8K2.u16130 = KTree.node D2M8K2.t16138 (nat_lit 35425594) (nat_lit 3928031331) (nat_lit 0) D2M8K2.t16139 from rfl, allE_node, rows16138, irow16130, rows16139]
  all_goals rfl

theorem atot16130 : totK PD2M8K2 D2M8K2.u16130 = [0, 178627885223, 762572137566, 741416635328, 121087278133, 1164319620, 0, 0] := by
  rw [show D2M8K2.u16130 = KTree.node D2M8K2.t16138 (nat_lit 35425594) (nat_lit 3928031331) (nat_lit 0) D2M8K2.t16139 from rfl, totK_node, tot16138, tot16139]
  decide +kernel

theorem arows16132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16132 = true := by
  rw [show D2M8K2.u16132 = KTree.node D2M8K2.t16140 (nat_lit 35427288) (nat_lit 3543776591) (nat_lit 0) D2M8K2.t16141 from rfl, allE_node, rows16140, irow16132, rows16141]
  all_goals rfl

theorem atot16132 : totK PD2M8K2 D2M8K2.u16132 = [0, 173960204262, 646125643161, 743608009304, 214325152388, 11885407614, 0, 0] := by
  rw [show D2M8K2.u16132 = KTree.node D2M8K2.t16140 (nat_lit 35427288) (nat_lit 3543776591) (nat_lit 0) D2M8K2.t16141 from rfl, totK_node, tot16140, tot16141]
  decide +kernel

theorem arows16133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16133 = true := by
  rw [show D2M8K2.u16133 = KTree.node D2M8K2.t16142 (nat_lit 35432737) (nat_lit 1509172513) (nat_lit 0) D2M8K2.t16143 from rfl, allE_node, rows16142, irow16133, rows16143]
  all_goals rfl

theorem atot16133 : totK PD2M8K2 D2M8K2.u16133 = [0, 168474244683, 750490323078, 766554571677, 114341641200, 1096505104, 0, 0] := by
  rw [show D2M8K2.u16133 = KTree.node D2M8K2.t16142 (nat_lit 35432737) (nat_lit 1509172513) (nat_lit 0) D2M8K2.t16143 from rfl, totK_node, tot16142, tot16143]
  decide +kernel

theorem arows16137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16137 = true := by
  rw [show D2M8K2.u16137 = KTree.node D2M8K2.t16144 (nat_lit 35434982) (nat_lit 4125165185) (nat_lit 0) D2M8K2.t16145 from rfl, allE_node, rows16144, irow16137, rows16145]
  all_goals rfl

theorem atot16137 : totK PD2M8K2 D2M8K2.u16137 = [0, 386884453024, 937010870397, 474688970927, 37376396327, 0, 0, 0] := by
  rw [show D2M8K2.u16137 = KTree.node D2M8K2.t16144 (nat_lit 35434982) (nat_lit 4125165185) (nat_lit 0) D2M8K2.t16145 from rfl, totK_node, tot16144, tot16145]
  decide +kernel

theorem arows16138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16138 = true := by
  rw [show D2M8K2.u16138 = KTree.node D2M8K2.t16146 (nat_lit 35436517) (nat_lit 1182843462) (nat_lit 0) D2M8K2.t16147 from rfl, allE_node, rows16146, irow16138, rows16147]
  all_goals rfl

theorem atot16138 : totK PD2M8K2 D2M8K2.u16138 = [0, 19689835847, 521572807304, 947819886688, 292446494718, 8708200738, 0, 0] := by
  rw [show D2M8K2.u16138 = KTree.node D2M8K2.t16146 (nat_lit 35436517) (nat_lit 1182843462) (nat_lit 0) D2M8K2.t16147 from rfl, totK_node, tot16146, tot16147]
  decide +kernel

theorem arows16140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16140 = true := by
  rw [show D2M8K2.u16140 = KTree.node D2M8K2.t16148 (nat_lit 35438499) (nat_lit 3158995255) (nat_lit 0) D2M8K2.t16149 from rfl, allE_node, rows16148, irow16140, rows16149]
  all_goals rfl

theorem atot16140 : totK PD2M8K2 D2M8K2.u16140 = [0, 0, 356675720778, 948022012894, 428766230035, 23668856606, 0, 0] := by
  rw [show D2M8K2.u16140 = KTree.node D2M8K2.t16148 (nat_lit 35438499) (nat_lit 3158995255) (nat_lit 0) D2M8K2.t16149 from rfl, totK_node, tot16148, tot16149]
  decide +kernel

theorem arows16141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16141 = true := by
  rw [show D2M8K2.u16141 = KTree.node D2M8K2.t16150 (nat_lit 35440155) (nat_lit 3123553604) (nat_lit 0) D2M8K2.t16151 from rfl, allE_node, rows16150, irow16141, rows16151]
  all_goals rfl

theorem atot16141 : totK PD2M8K2 D2M8K2.u16141 = [0, 0, 161063227213, 744964326872, 747128396421, 95392489440, 1206465782, 0] := by
  rw [show D2M8K2.u16141 = KTree.node D2M8K2.t16150 (nat_lit 35440155) (nat_lit 3123553604) (nat_lit 0) D2M8K2.t16151 from rfl, totK_node, tot16150, tot16151]
  decide +kernel

theorem arows16144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16144 = true := by
  rw [show D2M8K2.u16144 = KTree.node D2M8K2.t16152 (nat_lit 35442277) (nat_lit 1149596992) (nat_lit 0) D2M8K2.t16153 from rfl, allE_node, rows16152, irow16144, rows16153]
  all_goals rfl

theorem atot16144 : totK PD2M8K2 D2M8K2.u16144 = [0, 0, 343817856987, 943781413333, 511347918818, 36616345070, 0, 0] := by
  rw [show D2M8K2.u16144 = KTree.node D2M8K2.t16152 (nat_lit 35442277) (nat_lit 1149596992) (nat_lit 0) D2M8K2.t16153 from rfl, totK_node, tot16152, tot16153]
  decide +kernel

theorem arows16145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16145 = true := by
  rw [show D2M8K2.u16145 = KTree.node D2M8K2.t16154 (nat_lit 35445299) (nat_lit 2934367985) (nat_lit 0) D2M8K2.t16155 from rfl, allE_node, rows16154, irow16145, rows16155]
  all_goals rfl

theorem atot16145 : totK PD2M8K2 D2M8K2.u16145 = [0, 0, 366953344181, 922287727731, 471141257576, 36060699458, 0, 0] := by
  rw [show D2M8K2.u16145 = KTree.node D2M8K2.t16154 (nat_lit 35445299) (nat_lit 2934367985) (nat_lit 0) D2M8K2.t16155 from rfl, totK_node, tot16154, tot16155]
  decide +kernel

theorem arows16147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16147 = true := by
  rw [show D2M8K2.u16147 = KTree.node D2M8K2.t16156 (nat_lit 35446852) (nat_lit 3798767105) (nat_lit 0) D2M8K2.t16157 from rfl, allE_node, rows16156, irow16147, rows16157]
  all_goals rfl

theorem atot16147 : totK PD2M8K2 D2M8K2.u16147 = [0, 0, 71435426167, 567512216701, 854242596308, 233678795725, 8802081085, 0] := by
  rw [show D2M8K2.u16147 = KTree.node D2M8K2.t16156 (nat_lit 35446852) (nat_lit 3798767105) (nat_lit 0) D2M8K2.t16157 from rfl, totK_node, tot16156, tot16157]
  decide +kernel

theorem arows16148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16148 = true := by
  rw [show D2M8K2.u16148 = KTree.node D2M8K2.t16158 (nat_lit 35452178) (nat_lit 4099311819) (nat_lit 0) D2M8K2.t16159 from rfl, allE_node, rows16158, irow16148, rows16159]
  all_goals rfl

theorem atot16148 : totK PD2M8K2 D2M8K2.u16148 = [0, 0, 322607689623, 918772892187, 515548296275, 38435047726, 0, 0] := by
  rw [show D2M8K2.u16148 = KTree.node D2M8K2.t16158 (nat_lit 35452178) (nat_lit 4099311819) (nat_lit 0) D2M8K2.t16159 from rfl, totK_node, tot16158, tot16159]
  decide +kernel

theorem arows16153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16153 = true := by
  rw [show D2M8K2.u16153 = KTree.node D2M8K2.t16160 (nat_lit 35455173) (nat_lit 1472983938) (nat_lit 0) D2M8K2.t16161 from rfl, allE_node, rows16160, irow16153, rows16161]
  all_goals rfl

theorem atot16153 : totK PD2M8K2 D2M8K2.u16153 = [0, 0, 224635261226, 784633772963, 673696659918, 83700459539, 1021600638, 0] := by
  rw [show D2M8K2.u16153 = KTree.node D2M8K2.t16160 (nat_lit 35455173) (nat_lit 1472983938) (nat_lit 0) D2M8K2.t16161 from rfl, totK_node, tot16160, tot16161]
  decide +kernel

theorem arows16154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16154 = true := by
  rw [show D2M8K2.u16154 = KTree.node D2M8K2.t16162 (nat_lit 35456686) (nat_lit 4057428474) (nat_lit 0) D2M8K2.t16163 from rfl, allE_node, rows16162, irow16154, rows16163]
  all_goals rfl

theorem atot16154 : totK PD2M8K2 D2M8K2.u16154 = [0, 156589052074, 568094219736, 724544510374, 330521926226, 23468525424, 0, 0] := by
  rw [show D2M8K2.u16154 = KTree.node D2M8K2.t16162 (nat_lit 35456686) (nat_lit 4057428474) (nat_lit 0) D2M8K2.t16163 from rfl, totK_node, tot16162, tot16163]
  decide +kernel

theorem arows16156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16156 = true := by
  rw [show D2M8K2.u16156 = KTree.node D2M8K2.t16164 (nat_lit 35460008) (nat_lit 2726790561) (nat_lit 0) D2M8K2.t16165 from rfl, allE_node, rows16164, irow16156, rows16165]
  all_goals rfl

theorem atot16156 : totK PD2M8K2 D2M8K2.u16156 = [0, 250659299679, 792916612811, 630247782429, 103501302621, 1369150432, 0, 0] := by
  rw [show D2M8K2.u16156 = KTree.node D2M8K2.t16164 (nat_lit 35460008) (nat_lit 2726790561) (nat_lit 0) D2M8K2.t16165 from rfl, totK_node, tot16164, tot16165]
  decide +kernel

theorem arows16157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16157 = true := by
  rw [show D2M8K2.u16157 = KTree.node D2M8K2.t16166 (nat_lit 35462376) (nat_lit 2796634238) (nat_lit 0) D2M8K2.t16167 from rfl, allE_node, rows16166, irow16157, rows16167]
  all_goals rfl

theorem atot16157 : totK PD2M8K2 D2M8K2.u16157 = [0, 229467810292, 794393212854, 730708543847, 86285191349, 0, 0, 0] := by
  rw [show D2M8K2.u16157 = KTree.node D2M8K2.t16166 (nat_lit 35462376) (nat_lit 2796634238) (nat_lit 0) D2M8K2.t16167 from rfl, totK_node, tot16166, tot16167]
  decide +kernel

theorem arows16160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16160 = true := by
  rw [show D2M8K2.u16160 = KTree.node D2M8K2.t16168 (nat_lit 35463607) (nat_lit 1845732226) (nat_lit 0) D2M8K2.t16169 from rfl, allE_node, rows16168, irow16160, rows16169]
  all_goals rfl

theorem atot16160 : totK PD2M8K2 D2M8K2.u16160 = [0, 189219154771, 727090436835, 677656889304, 210969824920, 21155077365, 0, 0] := by
  rw [show D2M8K2.u16160 = KTree.node D2M8K2.t16168 (nat_lit 35463607) (nat_lit 1845732226) (nat_lit 0) D2M8K2.t16169 from rfl, totK_node, tot16168, tot16169]
  decide +kernel

theorem arows16161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16161 = true := by
  rw [show D2M8K2.u16161 = KTree.node D2M8K2.t16170 (nat_lit 35465156) (nat_lit 3605738724) (nat_lit 0) D2M8K2.t16171 from rfl, allE_node, rows16170, irow16161, rows16171]
  all_goals rfl

theorem atot16161 : totK PD2M8K2 D2M8K2.u16161 = [0, 120438301973, 513009070430, 800835591381, 355920470201, 14837381712, 0, 0] := by
  rw [show D2M8K2.u16161 = KTree.node D2M8K2.t16170 (nat_lit 35465156) (nat_lit 3605738724) (nat_lit 0) D2M8K2.t16171 from rfl, totK_node, tot16170, tot16171]
  decide +kernel

theorem arows16163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16163 = true := by
  rw [show D2M8K2.u16163 = KTree.node D2M8K2.t16172 (nat_lit 35470102) (nat_lit 2655931384) (nat_lit 0) D2M8K2.t16173 from rfl, allE_node, rows16172, irow16163, rows16173]
  all_goals rfl

theorem atot16163 : totK PD2M8K2 D2M8K2.u16163 = [0, 319579490186, 905416848638, 559007586817, 50186237287, 0, 0, 0] := by
  rw [show D2M8K2.u16163 = KTree.node D2M8K2.t16172 (nat_lit 35470102) (nat_lit 2655931384) (nat_lit 0) D2M8K2.t16173 from rfl, totK_node, tot16172, tot16173]
  decide +kernel

theorem arows16164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16164 = true := by
  rw [show D2M8K2.u16164 = KTree.node D2M8K2.t16174 (nat_lit 35471760) (nat_lit 3229271102) (nat_lit 0) D2M8K2.t16175 from rfl, allE_node, rows16174, irow16164, rows16175]
  all_goals rfl

theorem atot16164 : totK PD2M8K2 D2M8K2.u16164 = [0, 79515775218, 506817433772, 884381462400, 297658649832, 13250685261, 0, 0] := by
  rw [show D2M8K2.u16164 = KTree.node D2M8K2.t16174 (nat_lit 35471760) (nat_lit 3229271102) (nat_lit 0) D2M8K2.t16175 from rfl, totK_node, tot16174, tot16175]
  decide +kernel

theorem arows16168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16168 = true := by
  rw [show D2M8K2.u16168 = KTree.node D2M8K2.t16176 (nat_lit 35473408) (nat_lit 1657839911) (nat_lit 0) D2M8K2.t16177 from rfl, allE_node, rows16176, irow16168, rows16177]
  all_goals rfl

theorem atot16168 : totK PD2M8K2 D2M8K2.u16168 = [0, 244602771778, 819819550696, 641734070452, 93156002209, 1096505104, 0, 0] := by
  rw [show D2M8K2.u16168 = KTree.node D2M8K2.t16176 (nat_lit 35473408) (nat_lit 1657839911) (nat_lit 0) D2M8K2.t16177 from rfl, totK_node, tot16176, tot16177]
  decide +kernel

theorem arows16169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16169 = true := by
  rw [show D2M8K2.u16169 = KTree.node D2M8K2.t16178 (nat_lit 35476042) (nat_lit 3828955305) (nat_lit 0) D2M8K2.t16179 from rfl, allE_node, rows16178, irow16169, rows16179]
  all_goals rfl

theorem atot16169 : totK PD2M8K2 D2M8K2.u16169 = [0, 246417533557, 837304167305, 672875965112, 72598790603, 0, 0, 0] := by
  rw [show D2M8K2.u16169 = KTree.node D2M8K2.t16178 (nat_lit 35476042) (nat_lit 3828955305) (nat_lit 0) D2M8K2.t16179 from rfl, totK_node, tot16178, tot16179]
  decide +kernel

theorem arows16171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16171 = true := by
  rw [show D2M8K2.u16171 = KTree.node D2M8K2.t16180 (nat_lit 35477551) (nat_lit 2183669256) (nat_lit 0) D2M8K2.t16181 from rfl, allE_node, rows16180, irow16171, rows16181]
  all_goals rfl

theorem atot16171 : totK PD2M8K2 D2M8K2.u16171 = [0, 182261201038, 728408203835, 757860399730, 151384981390, 2303467656, 0, 0] := by
  rw [show D2M8K2.u16171 = KTree.node D2M8K2.t16180 (nat_lit 35477551) (nat_lit 2183669256) (nat_lit 0) D2M8K2.t16181 from rfl, totK_node, tot16180, tot16181]
  decide +kernel

theorem arows16172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16172 = true := by
  rw [show D2M8K2.u16172 = KTree.node D2M8K2.t16182 (nat_lit 35479231) (nat_lit 2223044629) (nat_lit 0) D2M8K2.t16183 from rfl, allE_node, rows16182, irow16172, rows16183]
  all_goals rfl

theorem atot16172 : totK PD2M8K2 D2M8K2.u16172 = [0, 0, 381895868114, 954964302668, 415622815134, 22257684677, 0, 0] := by
  rw [show D2M8K2.u16172 = KTree.node D2M8K2.t16182 (nat_lit 35479231) (nat_lit 2223044629) (nat_lit 0) D2M8K2.t16183 from rfl, totK_node, tot16182, tot16183]
  decide +kernel

theorem arows16175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16175 = true := by
  rw [show D2M8K2.u16175 = KTree.node D2M8K2.t16184 (nat_lit 35480869) (nat_lit 1367397861) (nat_lit 0) D2M8K2.t16185 from rfl, allE_node, rows16184, irow16175, rows16185]
  all_goals rfl

theorem atot16175 : totK PD2M8K2 D2M8K2.u16175 = [0, 0, 205400836138, 793233377186, 660228020712, 84434888220, 1239866073, 0] := by
  rw [show D2M8K2.u16175 = KTree.node D2M8K2.t16184 (nat_lit 35480869) (nat_lit 1367397861) (nat_lit 0) D2M8K2.t16185 from rfl, totK_node, tot16184, tot16185]
  decide +kernel

theorem arows16176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16176 = true := by
  rw [show D2M8K2.u16176 = KTree.node D2M8K2.t16186 (nat_lit 35483292) (nat_lit 1785477685) (nat_lit 0) D2M8K2.t16187 from rfl, allE_node, rows16186, irow16176, rows16187]
  all_goals rfl

theorem atot16176 : totK PD2M8K2 D2M8K2.u16176 = [0, 0, 280467982497, 861614749842, 630619817556, 54418362306, 0, 0] := by
  rw [show D2M8K2.u16176 = KTree.node D2M8K2.t16186 (nat_lit 35483292) (nat_lit 1785477685) (nat_lit 0) D2M8K2.t16187 from rfl, totK_node, tot16186, tot16187]
  decide +kernel

theorem arows16178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16178 = true := by
  rw [show D2M8K2.u16178 = KTree.node D2M8K2.t16188 (nat_lit 35489769) (nat_lit 1890793090) (nat_lit 0) D2M8K2.t16189 from rfl, allE_node, rows16188, irow16178, rows16189]
  all_goals rfl

theorem atot16178 : totK PD2M8K2 D2M8K2.u16178 = [0, 0, 386327403118, 943189860874, 459317887607, 32741722692, 0, 0] := by
  rw [show D2M8K2.u16178 = KTree.node D2M8K2.t16188 (nat_lit 35489769) (nat_lit 1890793090) (nat_lit 0) D2M8K2.t16189 from rfl, totK_node, tot16188, tot16189]
  decide +kernel

theorem arows16179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16179 = true := by
  rw [show D2M8K2.u16179 = KTree.node D2M8K2.t16190 (nat_lit 35491249) (nat_lit 1513916742) (nat_lit 0) D2M8K2.t16191 from rfl, allE_node, rows16190, irow16179, rows16191]
  all_goals rfl

theorem atot16179 : totK PD2M8K2 D2M8K2.u16179 = [0, 0, 189439928599, 777412962071, 703331751573, 103666277855, 1171084559, 0] := by
  rw [show D2M8K2.u16179 = KTree.node D2M8K2.t16190 (nat_lit 35491249) (nat_lit 1513916742) (nat_lit 0) D2M8K2.t16191 from rfl, totK_node, tot16190, tot16191]
  decide +kernel

theorem arows16185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16185 = true := by
  rw [show D2M8K2.u16185 = KTree.node D2M8K2.t16192 (nat_lit 35493130) (nat_lit 3543685093) (nat_lit 0) D2M8K2.t16193 from rfl, allE_node, rows16192, irow16185, rows16193]
  all_goals rfl

theorem atot16185 : totK PD2M8K2 D2M8K2.u16185 = [0, 0, 218294002173, 694387594916, 669887317311, 172000283628, 7682568795, 0] := by
  rw [show D2M8K2.u16185 = KTree.node D2M8K2.t16192 (nat_lit 35493130) (nat_lit 3543685093) (nat_lit 0) D2M8K2.t16193 from rfl, totK_node, tot16192, tot16193]
  decide +kernel

theorem arows16186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16186 = true := by
  rw [show D2M8K2.u16186 = KTree.node D2M8K2.t16194 (nat_lit 35495041) (nat_lit 1347469414) (nat_lit 0) D2M8K2.t16195 from rfl, allE_node, rows16194, irow16186, rows16195]
  all_goals rfl

theorem atot16186 : totK PD2M8K2 D2M8K2.u16186 = [0, 0, 189392376948, 793734180083, 692400947574, 78427815654, 1053411165, 0] := by
  rw [show D2M8K2.u16186 = KTree.node D2M8K2.t16194 (nat_lit 35495041) (nat_lit 1347469414) (nat_lit 0) D2M8K2.t16195 from rfl, totK_node, tot16194, tot16195]
  decide +kernel

theorem arows16188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16188 = true := by
  rw [show D2M8K2.u16188 = KTree.node D2M8K2.t16196 (nat_lit 35497364) (nat_lit 1900175215) (nat_lit 0) D2M8K2.t16197 from rfl, allE_node, rows16196, irow16188, rows16197]
  all_goals rfl

theorem atot16188 : totK PD2M8K2 D2M8K2.u16188 = [0, 0, 342227503063, 928222978442, 516450183910, 37756133749, 0, 0] := by
  rw [show D2M8K2.u16188 = KTree.node D2M8K2.t16196 (nat_lit 35497364) (nat_lit 1900175215) (nat_lit 0) D2M8K2.t16197 from rfl, totK_node, tot16196, tot16197]
  decide +kernel

theorem arows16189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16189 = true := by
  rw [show D2M8K2.u16189 = KTree.node D2M8K2.t16198 (nat_lit 35542376) (nat_lit 3486269447) (nat_lit 0) D2M8K2.t16199 from rfl, allE_node, rows16198, irow16189, rows16199]
  all_goals rfl

theorem atot16189 : totK PD2M8K2 D2M8K2.u16189 = [0, 393878508058, 925846206723, 415746442490, 44205174513, 7093611788, 0, 0] := by
  rw [show D2M8K2.u16189 = KTree.node D2M8K2.t16198 (nat_lit 35542376) (nat_lit 3486269447) (nat_lit 0) D2M8K2.t16199 from rfl, totK_node, tot16198, tot16199]
  decide +kernel

theorem arows16192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16192 = true := by
  rw [show D2M8K2.u16192 = KTree.node D2M8K2.t16200 (nat_lit 35543941) (nat_lit 1273806737) (nat_lit 0) D2M8K2.t16201 from rfl, allE_node, rows16200, irow16192, rows16201]
  all_goals rfl

theorem atot16192 : totK PD2M8K2 D2M8K2.u16192 = [0, 112846150294, 680511514929, 873289474553, 150868266005, 1369150432, 0, 0] := by
  rw [show D2M8K2.u16192 = KTree.node D2M8K2.t16200 (nat_lit 35543941) (nat_lit 1273806737) (nat_lit 0) D2M8K2.t16201 from rfl, totK_node, tot16200, tot16201]
  decide +kernel

theorem arows16193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16193 = true := by
  rw [show D2M8K2.u16193 = KTree.node D2M8K2.t16202 (nat_lit 35545944) (nat_lit 3285150778) (nat_lit 0) D2M8K2.t16203 from rfl, allE_node, rows16202, irow16193, rows16203]
  all_goals rfl

theorem atot16193 : totK PD2M8K2 D2M8K2.u16193 = [0, 333744399986, 932635603599, 529186910939, 41000621769, 0, 0, 0] := by
  rw [show D2M8K2.u16193 = KTree.node D2M8K2.t16202 (nat_lit 35545944) (nat_lit 3285150778) (nat_lit 0) D2M8K2.t16203 from rfl, totK_node, tot16202, tot16203]
  decide +kernel

theorem arows16195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16195 = true := by
  rw [show D2M8K2.u16195 = KTree.node D2M8K2.t16204 (nat_lit 35547440) (nat_lit 3550305444) (nat_lit 0) D2M8K2.t16205 from rfl, allE_node, rows16204, irow16195, rows16205]
  all_goals rfl

theorem atot16195 : totK PD2M8K2 D2M8K2.u16195 = [0, 0, 395794151376, 946091714081, 442098060008, 28523269697, 0, 0] := by
  rw [show D2M8K2.u16195 = KTree.node D2M8K2.t16204 (nat_lit 35547440) (nat_lit 3550305444) (nat_lit 0) D2M8K2.t16205 from rfl, totK_node, tot16204, tot16205]
  decide +kernel

theorem arows16196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16196 = true := by
  rw [show D2M8K2.u16196 = KTree.node D2M8K2.t16206 (nat_lit 35548790) (nat_lit 3976190923) (nat_lit 0) D2M8K2.t16207 from rfl, allE_node, rows16206, irow16196, rows16207]
  all_goals rfl

theorem atot16196 : totK PD2M8K2 D2M8K2.u16196 = [0, 299429600405, 793887642354, 573323545150, 145535239616, 6804944647, 0, 0] := by
  rw [show D2M8K2.u16196 = KTree.node D2M8K2.t16206 (nat_lit 35548790) (nat_lit 3976190923) (nat_lit 0) D2M8K2.t16207 from rfl, totK_node, tot16206, tot16207]
  decide +kernel

theorem arows16200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16200 = true := by
  rw [show D2M8K2.u16200 = KTree.node D2M8K2.t16208 (nat_lit 35550278) (nat_lit 3184491031) (nat_lit 0) D2M8K2.t16209 from rfl, allE_node, rows16208, irow16200, rows16209]
  all_goals rfl

theorem atot16200 : totK PD2M8K2 D2M8K2.u16200 = [0, 122594025680, 641995700475, 815974909859, 208610491808, 9252302862, 0, 0] := by
  rw [show D2M8K2.u16200 = KTree.node D2M8K2.t16208 (nat_lit 35550278) (nat_lit 3184491031) (nat_lit 0) D2M8K2.t16209 from rfl, totK_node, tot16208, tot16209]
  decide +kernel

theorem arows16201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16201 = true := by
  rw [show D2M8K2.u16201 = KTree.node D2M8K2.t16210 (nat_lit 35552192) (nat_lit 3702167081) (nat_lit 0) D2M8K2.t16211 from rfl, allE_node, rows16210, irow16201, rows16211]
  all_goals rfl

theorem atot16201 : totK PD2M8K2 D2M8K2.u16201 = [0, 265142207641, 793893049892, 633188529592, 116895260404, 1950893645, 0, 0] := by
  rw [show D2M8K2.u16201 = KTree.node D2M8K2.t16210 (nat_lit 35552192) (nat_lit 3702167081) (nat_lit 0) D2M8K2.t16211 from rfl, totK_node, tot16210, tot16211]
  decide +kernel

theorem arows16203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16203 = true := by
  rw [show D2M8K2.u16203 = KTree.node D2M8K2.t16212 (nat_lit 35553681) (nat_lit 1786495197) (nat_lit 0) D2M8K2.t16213 from rfl, allE_node, rows16212, irow16203, rows16213]
  all_goals rfl

theorem atot16203 : totK PD2M8K2 D2M8K2.u16203 = [0, 157088974604, 678677186849, 776520319019, 189063975352, 7232373827, 0, 0] := by
  rw [show D2M8K2.u16203 = KTree.node D2M8K2.t16212 (nat_lit 35553681) (nat_lit 1786495197) (nat_lit 0) D2M8K2.t16213 from rfl, totK_node, tot16212, tot16213]
  decide +kernel

theorem arows16204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16204 = true := by
  rw [show D2M8K2.u16204 = KTree.node D2M8K2.t16214 (nat_lit 35558950) (nat_lit 2869901699) (nat_lit 0) D2M8K2.t16215 from rfl, allE_node, rows16214, irow16204, rows16215]
  all_goals rfl

theorem atot16204 : totK PD2M8K2 D2M8K2.u16204 = [0, 265711451053, 778511590362, 637192179151, 138729124014, 4112248878, 0, 0] := by
  rw [show D2M8K2.u16204 = KTree.node D2M8K2.t16214 (nat_lit 35558950) (nat_lit 2869901699) (nat_lit 0) D2M8K2.t16215 from rfl, totK_node, tot16214, tot16215]
  decide +kernel

theorem arows16207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16207 = true := by
  rw [show D2M8K2.u16207 = KTree.node D2M8K2.t16216 (nat_lit 35560420) (nat_lit 4008919388) (nat_lit 0) D2M8K2.t16217 from rfl, allE_node, rows16216, irow16207, rows16217]
  all_goals rfl

theorem atot16207 : totK PD2M8K2 D2M8K2.u16207 = [0, 182497872290, 755348967273, 756897735602, 137748026729, 1268739303, 0, 0] := by
  rw [show D2M8K2.u16207 = KTree.node D2M8K2.t16216 (nat_lit 35560420) (nat_lit 4008919388) (nat_lit 0) D2M8K2.t16217 from rfl, totK_node, tot16216, tot16217]
  decide +kernel

theorem arows16208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16208 = true := by
  rw [show D2M8K2.u16208 = KTree.node D2M8K2.t16218 (nat_lit 35562082) (nat_lit 4200607152) (nat_lit 0) D2M8K2.t16219 from rfl, allE_node, rows16218, irow16208, rows16219]
  all_goals rfl

theorem atot16208 : totK PD2M8K2 D2M8K2.u16208 = [0, 0, 389665992202, 962492278519, 406156267171, 22149860293, 0, 0] := by
  rw [show D2M8K2.u16208 = KTree.node D2M8K2.t16218 (nat_lit 35562082) (nat_lit 4200607152) (nat_lit 0) D2M8K2.t16219 from rfl, totK_node, tot16218, tot16219]
  decide +kernel

theorem arows16210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16210 = true := by
  rw [show D2M8K2.u16210 = KTree.node D2M8K2.t16220 (nat_lit 35563689) (nat_lit 1565462793) (nat_lit 0) D2M8K2.t16221 from rfl, allE_node, rows16220, irow16210, rows16221]
  all_goals rfl

theorem atot16210 : totK PD2M8K2 D2M8K2.u16210 = [0, 0, 239375504501, 805148699621, 622905536405, 87446013430, 1310285577, 0] := by
  rw [show D2M8K2.u16210 = KTree.node D2M8K2.t16220 (nat_lit 35563689) (nat_lit 1565462793) (nat_lit 0) D2M8K2.t16221 from rfl, totK_node, tot16220, tot16221]
  decide +kernel

theorem arows16211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16211 = true := by
  rw [show D2M8K2.u16211 = KTree.node D2M8K2.t16222 (nat_lit 35566063) (nat_lit 2422272469) (nat_lit 0) D2M8K2.t16223 from rfl, allE_node, rows16222, irow16211, rows16223]
  all_goals rfl

theorem atot16211 : totK PD2M8K2 D2M8K2.u16211 = [0, 0, 212962829849, 797168939131, 729097874809, 71710027655, 0, 0] := by
  rw [show D2M8K2.u16211 = KTree.node D2M8K2.t16222 (nat_lit 35566063) (nat_lit 2422272469) (nat_lit 0) D2M8K2.t16223 from rfl, totK_node, tot16222, tot16223]
  decide +kernel

theorem arows16216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16216 = true := by
  rw [show D2M8K2.u16216 = KTree.node D2M8K2.t16224 (nat_lit 35567286) (nat_lit 3581471656) (nat_lit 0) D2M8K2.t16225 from rfl, allE_node, rows16224, irow16216, rows16225]
  all_goals rfl

theorem atot16216 : totK PD2M8K2 D2M8K2.u16216 = [0, 0, 384575096193, 960113339335, 454092402654, 31034739579, 0, 0] := by
  rw [show D2M8K2.u16216 = KTree.node D2M8K2.t16224 (nat_lit 35567286) (nat_lit 3581471656) (nat_lit 0) D2M8K2.t16225 from rfl, totK_node, tot16224, tot16225]
  decide +kernel

theorem arows16217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16217 = true := by
  rw [show D2M8K2.u16217 = KTree.node D2M8K2.t16226 (nat_lit 35570507) (nat_lit 1623472868) (nat_lit 0) D2M8K2.t16227 from rfl, allE_node, rows16226, irow16217, rows16227]
  all_goals rfl

theorem atot16217 : totK PD2M8K2 D2M8K2.u16217 = [0, 0, 247749102502, 790430541555, 651171226739, 85619255529, 1075657031, 0] := by
  rw [show D2M8K2.u16217 = KTree.node D2M8K2.t16226 (nat_lit 35570507) (nat_lit 1623472868) (nat_lit 0) D2M8K2.t16227 from rfl, totK_node, tot16226, tot16227]
  decide +kernel

theorem arows16219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16219 = true := by
  rw [show D2M8K2.u16219 = KTree.node D2M8K2.t16228 (nat_lit 35572451) (nat_lit 2985155367) (nat_lit 0) D2M8K2.t16229 from rfl, allE_node, rows16228, irow16219, rows16229]
  all_goals rfl

theorem atot16219 : totK PD2M8K2 D2M8K2.u16219 = [0, 0, 176018543892, 745946682328, 727776551278, 130272759058, 3804183361, 0] := by
  rw [show D2M8K2.u16219 = KTree.node D2M8K2.t16228 (nat_lit 35572451) (nat_lit 2985155367) (nat_lit 0) D2M8K2.t16229 from rfl, totK_node, tot16228, tot16229]
  decide +kernel

theorem arows16220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16220 = true := by
  rw [show D2M8K2.u16220 = KTree.node D2M8K2.t16230 (nat_lit 35574113) (nat_lit 2046168337) (nat_lit 0) D2M8K2.t16231 from rfl, allE_node, rows16230, irow16220, rows16231]
  all_goals rfl

theorem atot16220 : totK PD2M8K2 D2M8K2.u16220 = [0, 0, 241593668755, 816555529387, 641933393403, 86655401275, 1107157161, 0] := by
  rw [show D2M8K2.u16220 = KTree.node D2M8K2.t16230 (nat_lit 35574113) (nat_lit 2046168337) (nat_lit 0) D2M8K2.t16231 from rfl, totK_node, tot16230, tot16231]
  decide +kernel

theorem arows16223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16223 = true := by
  rw [show D2M8K2.u16223 = KTree.node D2M8K2.t16232 (nat_lit 35579623) (nat_lit 1846239819) (nat_lit 0) D2M8K2.t16233 from rfl, allE_node, rows16232, irow16223, rows16233]
  all_goals rfl

theorem atot16223 : totK PD2M8K2 D2M8K2.u16223 = [0, 0, 248911634793, 779541654452, 646382152101, 123282945470, 3824247485, 0] := by
  rw [show D2M8K2.u16223 = KTree.node D2M8K2.t16232 (nat_lit 35579623) (nat_lit 1846239819) (nat_lit 0) D2M8K2.t16233 from rfl, totK_node, tot16232, tot16233]
  decide +kernel

theorem arows16224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16224 = true := by
  rw [show D2M8K2.u16224 = KTree.node D2M8K2.t16234 (nat_lit 35581093) (nat_lit 1366036621) (nat_lit 0) D2M8K2.t16235 from rfl, allE_node, rows16234, irow16224, rows16235]
  all_goals rfl

theorem atot16224 : totK PD2M8K2 D2M8K2.u16224 = [0, 0, 197149340494, 785231718963, 712669033336, 110602413022, 1242138600, 0] := by
  rw [show D2M8K2.u16224 = KTree.node D2M8K2.t16234 (nat_lit 35581093) (nat_lit 1366036621) (nat_lit 0) D2M8K2.t16235 from rfl, totK_node, tot16234, tot16235]
  decide +kernel

theorem arows16226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16226 = true := by
  rw [show D2M8K2.u16226 = KTree.node D2M8K2.t16236 (nat_lit 35582778) (nat_lit 3854122169) (nat_lit 0) D2M8K2.t16237 from rfl, allE_node, rows16236, irow16226, rows16237]
  all_goals rfl

theorem atot16226 : totK PD2M8K2 D2M8K2.u16226 = [0, 0, 174989750872, 581160782046, 705552220173, 285848965507, 20509029466, 0] := by
  rw [show D2M8K2.u16226 = KTree.node D2M8K2.t16236 (nat_lit 35582778) (nat_lit 3854122169) (nat_lit 0) D2M8K2.t16237 from rfl, totK_node, tot16236, tot16237]
  decide +kernel

theorem arows16227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16227 = true := by
  rw [show D2M8K2.u16227 = KTree.node D2M8K2.t16238 (nat_lit 35584281) (nat_lit 1834976399) (nat_lit 0) D2M8K2.t16239 from rfl, allE_node, rows16238, irow16227, rows16239]
  all_goals rfl

theorem atot16227 : totK PD2M8K2 D2M8K2.u16227 = [0, 0, 256616772488, 849973803816, 593187618790, 75262159231, 1369150432, 0] := by
  rw [show D2M8K2.u16227 = KTree.node D2M8K2.t16238 (nat_lit 35584281) (nat_lit 1834976399) (nat_lit 0) D2M8K2.t16239 from rfl, totK_node, tot16238, tot16239]
  decide +kernel

theorem arows16231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16231 = true := by
  rw [show D2M8K2.u16231 = KTree.node D2M8K2.t16240 (nat_lit 35586219) (nat_lit 3273487950) (nat_lit 0) D2M8K2.t16241 from rfl, allE_node, rows16240, irow16231, rows16241]
  all_goals rfl

theorem atot16231 : totK PD2M8K2 D2M8K2.u16231 = [0, 0, 177987622975, 764286510296, 784739592102, 94969405260, 0, 0] := by
  rw [show D2M8K2.u16231 = KTree.node D2M8K2.t16240 (nat_lit 35586219) (nat_lit 3273487950) (nat_lit 0) D2M8K2.t16241 from rfl, totK_node, tot16240, tot16241]
  decide +kernel

theorem arows16232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16232 = true := by
  rw [show D2M8K2.u16232 = KTree.node D2M8K2.t16242 (nat_lit 35591403) (nat_lit 3035035876) (nat_lit 0) D2M8K2.t16243 from rfl, allE_node, rows16242, irow16232, rows16243]
  all_goals rfl

theorem atot16232 : totK PD2M8K2 D2M8K2.u16232 = [0, 0, 228819410403, 794950138012, 663252669174, 94638261366, 1164319620, 0] := by
  rw [show D2M8K2.u16232 = KTree.node D2M8K2.t16242 (nat_lit 35591403) (nat_lit 3035035876) (nat_lit 0) D2M8K2.t16243 from rfl, totK_node, tot16242, tot16243]
  decide +kernel

theorem arows16234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16234 = true := by
  rw [show D2M8K2.u16234 = KTree.node D2M8K2.t16244 (nat_lit 35593429) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t16245 from rfl, allE_node, rows16244, irow16234, rows16245]
  all_goals rfl

theorem atot16234 : totK PD2M8K2 D2M8K2.u16234 = [0, 0, 247660822589, 768358534617, 662494078073, 124183534187, 4008488258, 0] := by
  rw [show D2M8K2.u16234 = KTree.node D2M8K2.t16244 (nat_lit 35593429) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t16245 from rfl, totK_node, tot16244, tot16245]
  decide +kernel

theorem arows16235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16235 = true := by
  rw [show D2M8K2.u16235 = KTree.node D2M8K2.t16246 (nat_lit 35595007) (nat_lit 2414965113) (nat_lit 0) D2M8K2.t16247 from rfl, allE_node, rows16246, irow16235, rows16247]
  all_goals rfl

theorem atot16235 : totK PD2M8K2 D2M8K2.u16235 = [0, 0, 163345080708, 741849012760, 754450641312, 120490599071, 1198073392, 0] := by
  rw [show D2M8K2.u16235 = KTree.node D2M8K2.t16246 (nat_lit 35595007) (nat_lit 2414965113) (nat_lit 0) D2M8K2.t16247 from rfl, totK_node, tot16246, tot16247]
  decide +kernel

theorem arows16238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16238 = true := by
  rw [show D2M8K2.u16238 = KTree.node D2M8K2.t16248 (nat_lit 35597017) (nat_lit 1497717970) (nat_lit 0) D2M8K2.t16249 from rfl, allE_node, rows16248, irow16238, rows16249]
  all_goals rfl

theorem atot16238 : totK PD2M8K2 D2M8K2.u16238 = [0, 0, 270056082310, 817488467379, 576995699873, 100984641605, 4030866388, 0] := by
  rw [show D2M8K2.u16238 = KTree.node D2M8K2.t16248 (nat_lit 35597017) (nat_lit 1497717970) (nat_lit 0) D2M8K2.t16249 from rfl, totK_node, tot16248, tot16249]
  decide +kernel

theorem arows16239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16239 = true := by
  rw [show D2M8K2.u16239 = KTree.node D2M8K2.t16250 (nat_lit 35599434) (nat_lit 3844995630) (nat_lit 0) D2M8K2.t16251 from rfl, allE_node, rows16250, irow16239, rows16251]
  all_goals rfl

theorem atot16239 : totK PD2M8K2 D2M8K2.u16239 = [0, 0, 207595323915, 783104856257, 699967078823, 70979354075, 1096505104, 0] := by
  rw [show D2M8K2.u16239 = KTree.node D2M8K2.t16250 (nat_lit 35599434) (nat_lit 3844995630) (nat_lit 0) D2M8K2.t16251 from rfl, totK_node, tot16250, tot16251]
  decide +kernel

theorem arows16241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16241 = true := by
  rw [show D2M8K2.u16241 = KTree.node D2M8K2.t16252 (nat_lit 35601268) (nat_lit 2654287863) (nat_lit 0) D2M8K2.t16253 from rfl, allE_node, rows16252, irow16241, rows16253]
  all_goals rfl

theorem atot16241 : totK PD2M8K2 D2M8K2.u16241 = [0, 0, 266716252076, 853744335784, 627945371146, 62964878092, 0, 0] := by
  rw [show D2M8K2.u16241 = KTree.node D2M8K2.t16252 (nat_lit 35601268) (nat_lit 2654287863) (nat_lit 0) D2M8K2.t16253 from rfl, totK_node, tot16252, tot16253]
  decide +kernel

theorem arows16242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16242 = true := by
  rw [show D2M8K2.u16242 = KTree.node D2M8K2.t16254 (nat_lit 35602944) (nat_lit 3307447155) (nat_lit 0) D2M8K2.t16255 from rfl, allE_node, rows16254, irow16242, rows16255]
  all_goals rfl

theorem atot16242 : totK PD2M8K2 D2M8K2.u16242 = [0, 0, 0, 410858936397, 946518726863, 381580502860, 21916389073, 0] := by
  rw [show D2M8K2.u16242 = KTree.node D2M8K2.t16254 (nat_lit 35602944) (nat_lit 3307447155) (nat_lit 0) D2M8K2.t16255 from rfl, totK_node, tot16254, tot16255]
  decide +kernel

theorem arows16249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16249 = true := by
  rw [show D2M8K2.u16249 = KTree.node D2M8K2.t16256 (nat_lit 35604731) (nat_lit 2345323730) (nat_lit 0) D2M8K2.t16257 from rfl, allE_node, rows16256, irow16249, rows16257]
  all_goals rfl

theorem atot16249 : totK PD2M8K2 D2M8K2.u16249 = [0, 0, 0, 360785365489, 971444098433, 396903162122, 15294893282, 0] := by
  rw [show D2M8K2.u16249 = KTree.node D2M8K2.t16256 (nat_lit 35604731) (nat_lit 2345323730) (nat_lit 0) D2M8K2.t16257 from rfl, totK_node, tot16256, tot16257]
  decide +kernel

theorem arows16250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16250 = true := by
  rw [show D2M8K2.u16250 = KTree.node D2M8K2.t16258 (nat_lit 35606605) (nat_lit 1384954955) (nat_lit 0) D2M8K2.t16259 from rfl, allE_node, rows16258, irow16250, rows16259]
  all_goals rfl

theorem atot16250 : totK PD2M8K2 D2M8K2.u16250 = [0, 0, 0, 148290364214, 737005518946, 721046159494, 109618842657, 1369150432] := by
  rw [show D2M8K2.u16250 = KTree.node D2M8K2.t16258 (nat_lit 35606605) (nat_lit 1384954955) (nat_lit 0) D2M8K2.t16259 from rfl, totK_node, tot16258, tot16259]
  decide +kernel

theorem arows16252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16252 = true := by
  rw [show D2M8K2.u16252 = KTree.node D2M8K2.t16260 (nat_lit 35612022) (nat_lit 2147519598) (nat_lit 2048) D2M8K2.t16261 from rfl, allE_node, rows16260, irow16252, rows16261]
  all_goals rfl

theorem atot16252 : totK PD2M8K2 D2M8K2.u16252 = [0, 0, 0, 375090440435, 975963878151, 392882483192, 16638680742, 0] := by
  rw [show D2M8K2.u16252 = KTree.node D2M8K2.t16260 (nat_lit 35612022) (nat_lit 2147519598) (nat_lit 2048) D2M8K2.t16261 from rfl, totK_node, tot16260, tot16261]
  decide +kernel

theorem arows16253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16253 = true := by
  rw [show D2M8K2.u16253 = KTree.node D2M8K2.t16262 (nat_lit 35615389) (nat_lit 1077684915) (nat_lit 0) D2M8K2.t16263 from rfl, allE_node, rows16262, irow16253, rows16263]
  all_goals rfl

theorem atot16253 : totK PD2M8K2 D2M8K2.u16253 = [0, 0, 0, 379365428552, 971717993110, 377912065171, 16674907812, 0] := by
  rw [show D2M8K2.u16253 = KTree.node D2M8K2.t16262 (nat_lit 35615389) (nat_lit 1077684915) (nat_lit 0) D2M8K2.t16263 from rfl, totK_node, tot16262, tot16263]
  decide +kernel

theorem arows16256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16256 = true := by
  rw [show D2M8K2.u16256 = KTree.node D2M8K2.t16264 (nat_lit 35618793) (nat_lit 1920798711) (nat_lit 0) D2M8K2.t16265 from rfl, allE_node, rows16264, irow16256, rows16265]
  all_goals rfl

theorem atot16256 : totK PD2M8K2 D2M8K2.u16256 = [0, 0, 0, 439541512284, 974681261569, 322662042283, 10668007150, 0] := by
  rw [show D2M8K2.u16256 = KTree.node D2M8K2.t16264 (nat_lit 35618793) (nat_lit 1920798711) (nat_lit 0) D2M8K2.t16265 from rfl, totK_node, tot16264, tot16265]
  decide +kernel

theorem arows16257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16257 = true := by
  rw [show D2M8K2.u16257 = KTree.node D2M8K2.t16266 (nat_lit 35622518) (nat_lit 3831439198) (nat_lit 0) D2M8K2.t16267 from rfl, allE_node, rows16266, irow16257, rows16267]
  all_goals rfl

theorem atot16257 : totK PD2M8K2 D2M8K2.u16257 = [0, 0, 134721454216, 520076429403, 795573088062, 342530623775, 21225018219, 0] := by
  rw [show D2M8K2.u16257 = KTree.node D2M8K2.t16266 (nat_lit 35622518) (nat_lit 3831439198) (nat_lit 0) D2M8K2.t16267 from rfl, totK_node, tot16266, tot16267]
  decide +kernel

theorem arows16259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16259 = true := by
  rw [show D2M8K2.u16259 = KTree.node D2M8K2.t16268 (nat_lit 35629135) (nat_lit 2422567357) (nat_lit 0) D2M8K2.t16269 from rfl, allE_node, rows16268, irow16259, rows16269]
  all_goals rfl

theorem atot16259 : totK PD2M8K2 D2M8K2.u16259 = [0, 0, 305288432640, 917837144111, 561361699152, 48972783944, 0, 0] := by
  rw [show D2M8K2.u16259 = KTree.node D2M8K2.t16268 (nat_lit 35629135) (nat_lit 2422567357) (nat_lit 0) D2M8K2.t16269 from rfl, totK_node, tot16268, tot16269]
  decide +kernel

theorem arows16260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16260 = true := by
  rw [show D2M8K2.u16260 = KTree.node D2M8K2.t16270 (nat_lit 35630667) (nat_lit 3730294825) (nat_lit 0) D2M8K2.t16271 from rfl, allE_node, rows16270, irow16260, rows16271]
  all_goals rfl

theorem atot16260 : totK PD2M8K2 D2M8K2.u16260 = [0, 0, 67008747100, 444442683750, 874014874529, 404727420308, 25516869169, 0] := by
  rw [show D2M8K2.u16260 = KTree.node D2M8K2.t16270 (nat_lit 35630667) (nat_lit 3730294825) (nat_lit 0) D2M8K2.t16271 from rfl, totK_node, tot16270, tot16271]
  decide +kernel

theorem arows16264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16264 = true := by
  rw [show D2M8K2.u16264 = KTree.node D2M8K2.t16272 (nat_lit 35632091) (nat_lit 2343241808) (nat_lit 0) D2M8K2.t16273 from rfl, allE_node, rows16272, irow16264, rows16273]
  all_goals rfl

theorem atot16264 : totK PD2M8K2 D2M8K2.u16264 = [0, 0, 346818793145, 947027818248, 502646064041, 35161232300, 0, 0] := by
  rw [show D2M8K2.u16264 = KTree.node D2M8K2.t16272 (nat_lit 35632091) (nat_lit 2343241808) (nat_lit 0) D2M8K2.t16273 from rfl, totK_node, tot16272, tot16273]
  decide +kernel

theorem arows16265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16265 = true := by
  rw [show D2M8K2.u16265 = KTree.node D2M8K2.t16274 (nat_lit 35634262) (nat_lit 2008400916) (nat_lit 0) D2M8K2.t16275 from rfl, allE_node, rows16274, irow16265, rows16275]
  all_goals rfl

theorem atot16265 : totK PD2M8K2 D2M8K2.u16265 = [0, 0, 157261717045, 713021408425, 789051303662, 158484086933, 4166040359, 0] := by
  rw [show D2M8K2.u16265 = KTree.node D2M8K2.t16274 (nat_lit 35634262) (nat_lit 2008400916) (nat_lit 0) D2M8K2.t16275 from rfl, totK_node, tot16274, tot16275]
  decide +kernel

theorem arows16267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16267 = true := by
  rw [show D2M8K2.u16267 = KTree.node D2M8K2.t16276 (nat_lit 35636076) (nat_lit 2139975035) (nat_lit 2048) D2M8K2.t16277 from rfl, allE_node, rows16276, irow16267, rows16277]
  all_goals rfl

theorem atot16267 : totK PD2M8K2 D2M8K2.u16267 = [0, 0, 256815577739, 877701205432, 635863267047, 68754333447, 0, 0] := by
  rw [show D2M8K2.u16267 = KTree.node D2M8K2.t16276 (nat_lit 35636076) (nat_lit 2139975035) (nat_lit 2048) D2M8K2.t16277 from rfl, totK_node, tot16276, tot16277]
  decide +kernel

theorem arows16268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16268 = true := by
  rw [show D2M8K2.u16268 = KTree.node D2M8K2.t16278 (nat_lit 35638118) (nat_lit 3977316729) (nat_lit 0) D2M8K2.t16279 from rfl, allE_node, rows16278, irow16268, rows16279]
  all_goals rfl

theorem atot16268 : totK PD2M8K2 D2M8K2.u16268 = [0, 0, 192437972909, 749428098161, 744592133871, 152670452524, 4189012250, 0] := by
  rw [show D2M8K2.u16268 = KTree.node D2M8K2.t16278 (nat_lit 35638118) (nat_lit 3977316729) (nat_lit 0) D2M8K2.t16279 from rfl, totK_node, tot16278, tot16279]
  decide +kernel

theorem arows16271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16271 = true := by
  rw [show D2M8K2.u16271 = KTree.node D2M8K2.t16280 (nat_lit 35642067) (nat_lit 3699729656) (nat_lit 0) D2M8K2.t16281 from rfl, allE_node, rows16280, irow16271, rows16281]
  all_goals rfl

theorem atot16271 : totK PD2M8K2 D2M8K2.u16271 = [0, 0, 403084451094, 964921090367, 444661893758, 31737430496, 0, 0] := by
  rw [show D2M8K2.u16271 = KTree.node D2M8K2.t16280 (nat_lit 35642067) (nat_lit 3699729656) (nat_lit 0) D2M8K2.t16281 from rfl, totK_node, tot16280, tot16281]
  decide +kernel

theorem arows16272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16272 = true := by
  rw [show D2M8K2.u16272 = KTree.node D2M8K2.t16282 (nat_lit 35643504) (nat_lit 3557789816) (nat_lit 0) D2M8K2.t16283 from rfl, allE_node, rows16282, irow16272, rows16283]
  all_goals rfl

theorem atot16272 : totK PD2M8K2 D2M8K2.u16272 = [0, 0, 156467388858, 728625678907, 786212623903, 150068142588, 3654551267, 0] := by
  rw [show D2M8K2.u16272 = KTree.node D2M8K2.t16282 (nat_lit 35643504) (nat_lit 3557789816) (nat_lit 0) D2M8K2.t16283 from rfl, totK_node, tot16282, tot16283]
  decide +kernel

theorem arows16274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16274 = true := by
  rw [show D2M8K2.u16274 = KTree.node D2M8K2.t16284 (nat_lit 35666022) (nat_lit 3391277864) (nat_lit 0) D2M8K2.t16285 from rfl, allE_node, rows16284, irow16274, rows16285]
  all_goals rfl

theorem atot16274 : totK PD2M8K2 D2M8K2.u16274 = [0, 0, 244691444586, 701313038631, 617748997614, 208903378490, 17027268164, 0] := by
  rw [show D2M8K2.u16274 = KTree.node D2M8K2.t16284 (nat_lit 35666022) (nat_lit 3391277864) (nat_lit 0) D2M8K2.t16285 from rfl, totK_node, tot16284, tot16285]
  decide +kernel

theorem arows16275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16275 = true := by
  rw [show D2M8K2.u16275 = KTree.node D2M8K2.t16286 (nat_lit 35667652) (nat_lit 3767302611) (nat_lit 0) D2M8K2.t16287 from rfl, allE_node, rows16286, irow16275, rows16287]
  all_goals rfl

theorem atot16275 : totK PD2M8K2 D2M8K2.u16275 = [0, 0, 161818754478, 740800285596, 751730900415, 114317170498, 1369150432, 0] := by
  rw [show D2M8K2.u16275 = KTree.node D2M8K2.t16286 (nat_lit 35667652) (nat_lit 3767302611) (nat_lit 0) D2M8K2.t16287 from rfl, totK_node, tot16286, tot16287]
  decide +kernel

theorem arows16280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16280 = true := by
  rw [show D2M8K2.u16280 = KTree.node D2M8K2.t16288 (nat_lit 35669994) (nat_lit 3343690310) (nat_lit 0) D2M8K2.t16289 from rfl, allE_node, rows16288, irow16280, rows16289]
  all_goals rfl

theorem atot16280 : totK PD2M8K2 D2M8K2.u16280 = [0, 0, 329255694237, 898105450761, 570469469065, 51267620910, 0, 0] := by
  rw [show D2M8K2.u16280 = KTree.node D2M8K2.t16288 (nat_lit 35669994) (nat_lit 3343690310) (nat_lit 0) D2M8K2.t16289 from rfl, totK_node, tot16288, tot16289]
  decide +kernel

theorem arows16281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16281 = true := by
  rw [show D2M8K2.u16281 = KTree.node D2M8K2.t16290 (nat_lit 35671638) (nat_lit 2525128752) (nat_lit 2560) D2M8K2.t16291 from rfl, allE_node, rows16290, irow16281, rows16291]
  all_goals rfl

theorem atot16281 : totK PD2M8K2 D2M8K2.u16281 = [0, 0, 88156931025, 644442827281, 851171065992, 246314505792, 12064694307, 0] := by
  rw [show D2M8K2.u16281 = KTree.node D2M8K2.t16290 (nat_lit 35671638) (nat_lit 2525128752) (nat_lit 2560) D2M8K2.t16291 from rfl, totK_node, tot16290, tot16291]
  decide +kernel

theorem arows16283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16283 = true := by
  rw [show D2M8K2.u16283 = KTree.node D2M8K2.t16292 (nat_lit 35673290) (nat_lit 4267445157) (nat_lit 0) D2M8K2.t16293 from rfl, allE_node, rows16292, irow16283, rows16293]
  all_goals rfl

theorem atot16283 : totK PD2M8K2 D2M8K2.u16283 = [0, 0, 349965255528, 832543344476, 528602650773, 112892426923, 4246544562, 0] := by
  rw [show D2M8K2.u16283 = KTree.node D2M8K2.t16292 (nat_lit 35673290) (nat_lit 4267445157) (nat_lit 0) D2M8K2.t16293 from rfl, totK_node, tot16292, tot16293]
  decide +kernel

theorem arows16284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16284 = true := by
  rw [show D2M8K2.u16284 = KTree.node D2M8K2.t16294 (nat_lit 35674726) (nat_lit 2231609149) (nat_lit 0) D2M8K2.t16295 from rfl, allE_node, rows16294, irow16284, rows16295]
  all_goals rfl

theorem atot16284 : totK PD2M8K2 D2M8K2.u16284 = [0, 0, 89076128973, 637519732348, 852554283985, 204740126991, 7834618311, 0] := by
  rw [show D2M8K2.u16284 = KTree.node D2M8K2.t16294 (nat_lit 35674726) (nat_lit 2231609149) (nat_lit 0) D2M8K2.t16295 from rfl, totK_node, tot16294, tot16295]
  decide +kernel

theorem arows16287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16287 = true := by
  rw [show D2M8K2.u16287 = KTree.node D2M8K2.t16296 (nat_lit 35680094) (nat_lit 3923990087) (nat_lit 0) D2M8K2.t16297 from rfl, allE_node, rows16296, irow16287, rows16297]
  all_goals rfl

theorem atot16287 : totK PD2M8K2 D2M8K2.u16287 = [0, 0, 315233120359, 836491768389, 562522829480, 84523856211, 980853662, 0] := by
  rw [show D2M8K2.u16287 = KTree.node D2M8K2.t16296 (nat_lit 35680094) (nat_lit 3923990087) (nat_lit 0) D2M8K2.t16297 from rfl, totK_node, tot16296, tot16297]
  decide +kernel

theorem arows16288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16288 = true := by
  rw [show D2M8K2.u16288 = KTree.node D2M8K2.t16298 (nat_lit 35682727) (nat_lit 2142563442) (nat_lit 0) D2M8K2.t16299 from rfl, allE_node, rows16298, irow16288, rows16299]
  all_goals rfl

theorem atot16288 : totK PD2M8K2 D2M8K2.u16288 = [0, 0, 179998216731, 779309792219, 737086666655, 90209753352, 1062926506, 0] := by
  rw [show D2M8K2.u16288 = KTree.node D2M8K2.t16298 (nat_lit 35682727) (nat_lit 2142563442) (nat_lit 0) D2M8K2.t16299 from rfl, totK_node, tot16298, tot16299]
  decide +kernel

theorem arows16290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16290 = true := by
  rw [show D2M8K2.u16290 = KTree.node D2M8K2.t16300 (nat_lit 35684692) (nat_lit 4028089053) (nat_lit 0) D2M8K2.t16301 from rfl, allE_node, rows16300, irow16290, rows16301]
  all_goals rfl

theorem atot16290 : totK PD2M8K2 D2M8K2.u16290 = [0, 0, 254251863405, 791437802226, 651224594800, 112486618768, 1268739303, 0] := by
  rw [show D2M8K2.u16290 = KTree.node D2M8K2.t16300 (nat_lit 35684692) (nat_lit 4028089053) (nat_lit 0) D2M8K2.t16301 from rfl, totK_node, tot16300, tot16301]
  decide +kernel

theorem arows16291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16291 = true := by
  rw [show D2M8K2.u16291 = KTree.node D2M8K2.t16302 (nat_lit 35686400) (nat_lit 3034575475) (nat_lit 0) D2M8K2.t16303 from rfl, allE_node, rows16302, irow16291, rows16303]
  all_goals rfl

theorem atot16291 : totK PD2M8K2 D2M8K2.u16291 = [0, 0, 0, 403836448564, 954843170616, 391113152882, 22077693215, 0] := by
  rw [show D2M8K2.u16291 = KTree.node D2M8K2.t16302 (nat_lit 35686400) (nat_lit 3034575475) (nat_lit 0) D2M8K2.t16303 from rfl, totK_node, tot16302, tot16303]
  decide +kernel

theorem arows16295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16295 = true := by
  rw [show D2M8K2.u16295 = KTree.node D2M8K2.t16304 (nat_lit 35688011) (nat_lit 1556513783) (nat_lit 0) D2M8K2.t16305 from rfl, allE_node, rows16304, irow16295, rows16305]
  all_goals rfl

theorem atot16295 : totK PD2M8K2 D2M8K2.u16295 = [0, 0, 0, 278853387680, 840249021663, 518401814023, 62406407212, 1166720416] := by
  rw [show D2M8K2.u16295 = KTree.node D2M8K2.t16304 (nat_lit 35688011) (nat_lit 1556513783) (nat_lit 0) D2M8K2.t16305 from rfl, totK_node, tot16304, tot16305]
  decide +kernel

theorem arows16296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16296 = true := by
  rw [show D2M8K2.u16296 = KTree.node D2M8K2.t16306 (nat_lit 35690588) (nat_lit 2466823740) (nat_lit 512) D2M8K2.t16307 from rfl, allE_node, rows16306, irow16296, rows16307]
  all_goals rfl

theorem atot16296 : totK PD2M8K2 D2M8K2.u16296 = [0, 0, 0, 356899990042, 908159285012, 501554846449, 35303300261, 0] := by
  rw [show D2M8K2.u16296 = KTree.node D2M8K2.t16306 (nat_lit 35690588) (nat_lit 2466823740) (nat_lit 512) D2M8K2.t16307 from rfl, totK_node, tot16306, tot16307]
  decide +kernel

theorem arows16298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16298 = true := by
  rw [show D2M8K2.u16298 = KTree.node D2M8K2.t16308 (nat_lit 35693970) (nat_lit 1594031281) (nat_lit 512) D2M8K2.t16309 from rfl, allE_node, rows16308, irow16298, rows16309]
  all_goals rfl

theorem atot16298 : totK PD2M8K2 D2M8K2.u16298 = [0, 0, 0, 393787762244, 955135288713, 411350043938, 23354466652, 0] := by
  rw [show D2M8K2.u16298 = KTree.node D2M8K2.t16308 (nat_lit 35693970) (nat_lit 1594031281) (nat_lit 512) D2M8K2.t16309 from rfl, totK_node, tot16308, tot16309]
  decide +kernel

theorem arows16299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16299 = true := by
  rw [show D2M8K2.u16299 = KTree.node D2M8K2.t16310 (nat_lit 35695544) (nat_lit 2601699280) (nat_lit 136) D2M8K2.t16311 from rfl, allE_node, rows16310, irow16299, rows16311]
  all_goals rfl

theorem atot16299 : totK PD2M8K2 D2M8K2.u16299 = [0, 0, 0, 87965506125, 672177311640, 772361124085, 157983243063, 5134755853] := by
  rw [show D2M8K2.u16299 = KTree.node D2M8K2.t16310 (nat_lit 35695544) (nat_lit 2601699280) (nat_lit 136) D2M8K2.t16311 from rfl, totK_node, tot16310, tot16311]
  decide +kernel

theorem arows16302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16302 = true := by
  rw [show D2M8K2.u16302 = KTree.node D2M8K2.t16312 (nat_lit 35701302) (nat_lit 1503980146) (nat_lit 8) D2M8K2.t16313 from rfl, allE_node, rows16312, irow16302, rows16313]
  all_goals rfl

theorem atot16302 : totK PD2M8K2 D2M8K2.u16302 = [0, 0, 0, 484991402891, 958735538717, 298050160619, 15784695319, 0] := by
  rw [show D2M8K2.u16302 = KTree.node D2M8K2.t16312 (nat_lit 35701302) (nat_lit 1503980146) (nat_lit 8) D2M8K2.t16313 from rfl, totK_node, tot16312, tot16313]
  decide +kernel

theorem arows16303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16303 = true := by
  rw [show D2M8K2.u16303 = KTree.node D2M8K2.t16314 (nat_lit 35705398) (nat_lit 3581730915) (nat_lit 0) D2M8K2.t16315 from rfl, allE_node, rows16314, irow16303, rows16315]
  all_goals rfl

theorem atot16303 : totK PD2M8K2 D2M8K2.u16303 = [0, 0, 118459880326, 512870550998, 770990028477, 366163426325, 25900795513, 0] := by
  rw [show D2M8K2.u16303 = KTree.node D2M8K2.t16314 (nat_lit 35705398) (nat_lit 3581730915) (nat_lit 0) D2M8K2.t16315 from rfl, totK_node, tot16314, tot16315]
  decide +kernel

theorem arows16305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16305 = true := by
  rw [show D2M8K2.u16305 = KTree.node D2M8K2.t16316 (nat_lit 35708661) (nat_lit 1741627740) (nat_lit 0) D2M8K2.t16317 from rfl, allE_node, rows16316, irow16305, rows16317]
  all_goals rfl

theorem atot16305 : totK PD2M8K2 D2M8K2.u16305 = [0, 0, 284708070139, 857349233707, 557356114241, 70434232465, 1369150432, 0] := by
  rw [show D2M8K2.u16305 = KTree.node D2M8K2.t16316 (nat_lit 35708661) (nat_lit 1741627740) (nat_lit 0) D2M8K2.t16317 from rfl, totK_node, tot16316, tot16317]
  decide +kernel

theorem arows16306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16306 = true := by
  rw [show D2M8K2.u16306 = KTree.node D2M8K2.t16318 (nat_lit 35710694) (nat_lit 3735014334) (nat_lit 0) D2M8K2.t16319 from rfl, allE_node, rows16318, irow16306, rows16319]
  all_goals rfl

theorem atot16306 : totK PD2M8K2 D2M8K2.u16306 = [0, 0, 196286291092, 769236662536, 775296027080, 94410523001, 0, 0] := by
  rw [show D2M8K2.u16306 = KTree.node D2M8K2.t16318 (nat_lit 35710694) (nat_lit 3735014334) (nat_lit 0) D2M8K2.t16319 from rfl, totK_node, tot16318, tot16319]
  decide +kernel

theorem arows16312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16312 = true := by
  rw [show D2M8K2.u16312 = KTree.node D2M8K2.t16320 (nat_lit 35712431) (nat_lit 2777346994) (nat_lit 0) D2M8K2.t16321 from rfl, allE_node, rows16320, irow16312, rows16321]
  all_goals rfl

theorem atot16312 : totK PD2M8K2 D2M8K2.u16312 = [0, 0, 221208825897, 789625413674, 667125037634, 158668781066, 10519103133, 0] := by
  rw [show D2M8K2.u16312 = KTree.node D2M8K2.t16320 (nat_lit 35712431) (nat_lit 2777346994) (nat_lit 0) D2M8K2.t16321 from rfl, totK_node, tot16320, tot16321]
  decide +kernel

theorem arows16313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16313 = true := by
  rw [show D2M8K2.u16313 = KTree.node D2M8K2.t16322 (nat_lit 35717780) (nat_lit 3239882713) (nat_lit 0) D2M8K2.t16323 from rfl, allE_node, rows16322, irow16313, rows16323]
  all_goals rfl

theorem atot16313 : totK PD2M8K2 D2M8K2.u16313 = [0, 0, 207751196119, 700845105027, 713405317571, 199387125794, 5774780012, 0] := by
  rw [show D2M8K2.u16313 = KTree.node D2M8K2.t16322 (nat_lit 35717780) (nat_lit 3239882713) (nat_lit 0) D2M8K2.t16323 from rfl, totK_node, tot16322, tot16323]
  decide +kernel

theorem arows16315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16315 = true := by
  rw [show D2M8K2.u16315 = KTree.node D2M8K2.t16324 (nat_lit 35719264) (nat_lit 3065486351) (nat_lit 0) D2M8K2.t16325 from rfl, allE_node, rows16324, irow16315, rows16325]
  all_goals rfl

theorem atot16315 : totK PD2M8K2 D2M8K2.u16315 = [0, 0, 231463893187, 806399580188, 672939000397, 99402736667, 1198073392, 0] := by
  rw [show D2M8K2.u16315 = KTree.node D2M8K2.t16324 (nat_lit 35719264) (nat_lit 3065486351) (nat_lit 0) D2M8K2.t16325 from rfl, totK_node, tot16324, tot16325]
  decide +kernel

theorem arows16316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16316 = true := by
  rw [show D2M8K2.u16316 = KTree.node D2M8K2.t16326 (nat_lit 35720971) (nat_lit 1782679708) (nat_lit 0) D2M8K2.t16327 from rfl, allE_node, rows16326, irow16316, rows16327]
  all_goals rfl

theorem atot16316 : totK PD2M8K2 D2M8K2.u16316 = [0, 0, 162911924887, 662141152967, 753864284711, 201519450479, 7701383478, 0] := by
  rw [show D2M8K2.u16316 = KTree.node D2M8K2.t16326 (nat_lit 35720971) (nat_lit 1782679708) (nat_lit 0) D2M8K2.t16327 from rfl, totK_node, tot16326, tot16327]
  decide +kernel

theorem arows16319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16319 = true := by
  rw [show D2M8K2.u16319 = KTree.node D2M8K2.t16328 (nat_lit 35723140) (nat_lit 3637604610) (nat_lit 0) D2M8K2.t16329 from rfl, allE_node, rows16328, irow16319, rows16329]
  all_goals rfl

theorem atot16319 : totK PD2M8K2 D2M8K2.u16319 = [0, 0, 244403944332, 809372594590, 662537440512, 79094947682, 1096505104, 0] := by
  rw [show D2M8K2.u16319 = KTree.node D2M8K2.t16328 (nat_lit 35723140) (nat_lit 3637604610) (nat_lit 0) D2M8K2.t16329 from rfl, totK_node, tot16328, tot16329]
  decide +kernel

theorem arows16320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16320 = true := by
  rw [show D2M8K2.u16320 = KTree.node D2M8K2.t16330 (nat_lit 35725456) (nat_lit 3675549960) (nat_lit 0) D2M8K2.t16331 from rfl, allE_node, rows16330, irow16320, rows16331]
  all_goals rfl

theorem atot16320 : totK PD2M8K2 D2M8K2.u16320 = [0, 0, 342353222358, 923128502738, 518740681394, 41258428341, 0, 0] := by
  rw [show D2M8K2.u16320 = KTree.node D2M8K2.t16330 (nat_lit 35725456) (nat_lit 3675549960) (nat_lit 0) D2M8K2.t16331 from rfl, totK_node, tot16330, tot16331]
  decide +kernel

theorem arows16322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16322 = true := by
  rw [show D2M8K2.u16322 = KTree.node D2M8K2.t16332 (nat_lit 35727131) (nat_lit 2325998799) (nat_lit 0) D2M8K2.t16333 from rfl, allE_node, rows16332, irow16322, rows16333]
  all_goals rfl

theorem atot16322 : totK PD2M8K2 D2M8K2.u16322 = [0, 0, 0, 440716026567, 977496460004, 347416468642, 12368296313, 0] := by
  rw [show D2M8K2.u16322 = KTree.node D2M8K2.t16332 (nat_lit 35727131) (nat_lit 2325998799) (nat_lit 0) D2M8K2.t16333 from rfl, totK_node, tot16332, tot16333]
  decide +kernel

theorem arows16323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16323 = true := by
  rw [show D2M8K2.u16323 = KTree.node D2M8K2.t16334 (nat_lit 35729070) (nat_lit 4071740195) (nat_lit 0) D2M8K2.t16335 from rfl, allE_node, rows16334, irow16323, rows16335]
  all_goals rfl

theorem atot16323 : totK PD2M8K2 D2M8K2.u16323 = [0, 0, 0, 399123819363, 959294382814, 354914861837, 18573755577, 0] := by
  rw [show D2M8K2.u16323 = KTree.node D2M8K2.t16334 (nat_lit 35729070) (nat_lit 4071740195) (nat_lit 0) D2M8K2.t16335 from rfl, totK_node, tot16334, tot16335]
  decide +kernel

theorem arows16327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16327 = true := by
  rw [show D2M8K2.u16327 = KTree.node D2M8K2.t16336 (nat_lit 35731019) (nat_lit 2086461011) (nat_lit 0) D2M8K2.t16337 from rfl, allE_node, rows16336, irow16327, rows16337]
  all_goals rfl

theorem atot16327 : totK PD2M8K2 D2M8K2.u16327 = [0, 0, 0, 162905041139, 767783696343, 723151734829, 91101885912, 1200365979] := by
  rw [show D2M8K2.u16327 = KTree.node D2M8K2.t16336 (nat_lit 35731019) (nat_lit 2086461011) (nat_lit 0) D2M8K2.t16337 from rfl, totK_node, tot16336, tot16337]
  decide +kernel

theorem arows16328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16328 = true := by
  rw [show D2M8K2.u16328 = KTree.node D2M8K2.t16338 (nat_lit 35733292) (nat_lit 3704363204) (nat_lit 0) D2M8K2.t16339 from rfl, allE_node, rows16338, irow16328, rows16339]
  all_goals rfl

theorem atot16328 : totK PD2M8K2 D2M8K2.u16328 = [0, 0, 0, 444646530931, 967412841319, 375636537550, 18610044074, 0] := by
  rw [show D2M8K2.u16328 = KTree.node D2M8K2.t16338 (nat_lit 35733292) (nat_lit 3704363204) (nat_lit 0) D2M8K2.t16339 from rfl, totK_node, tot16338, tot16339]
  decide +kernel

theorem arows16330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16330 = true := by
  rw [show D2M8K2.u16330 = KTree.node D2M8K2.t16340 (nat_lit 35740056) (nat_lit 3571689769) (nat_lit 0) D2M8K2.t16341 from rfl, allE_node, rows16340, irow16330, rows16341]
  all_goals rfl

theorem atot16330 : totK PD2M8K2 D2M8K2.u16330 = [0, 0, 0, 219811530409, 804546772413, 625565764689, 83679905184, 1135526696] := by
  rw [show D2M8K2.u16330 = KTree.node D2M8K2.t16340 (nat_lit 35740056) (nat_lit 3571689769) (nat_lit 0) D2M8K2.t16341 from rfl, totK_node, tot16340, tot16341]
  decide +kernel

theorem arows16331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16331 = true := by
  rw [show D2M8K2.u16331 = KTree.node D2M8K2.t16342 (nat_lit 35742114) (nat_lit 2286925661) (nat_lit 0) D2M8K2.t16343 from rfl, allE_node, rows16342, irow16331, rows16343]
  all_goals rfl

theorem atot16331 : totK PD2M8K2 D2M8K2.u16331 = [0, 0, 0, 398116559142, 804353953384, 435127034775, 90733229211, 4028038878] := by
  rw [show D2M8K2.u16331 = KTree.node D2M8K2.t16342 (nat_lit 35742114) (nat_lit 2286925661) (nat_lit 0) D2M8K2.t16343 from rfl, totK_node, tot16342, tot16343]
  decide +kernel

theorem arows16334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16334 = true := by
  rw [show D2M8K2.u16334 = KTree.node D2M8K2.t16344 (nat_lit 35746290) (nat_lit 3433520064) (nat_lit 0) D2M8K2.t16345 from rfl, allE_node, rows16344, irow16334, rows16345]
  all_goals rfl

theorem atot16334 : totK PD2M8K2 D2M8K2.u16334 = [0, 0, 18874737507, 348285870517, 914181206522, 484122952827, 33968447482, 0] := by
  rw [show D2M8K2.u16334 = KTree.node D2M8K2.t16344 (nat_lit 35746290) (nat_lit 3433520064) (nat_lit 0) D2M8K2.t16345 from rfl, totK_node, tot16344, tot16345]
  decide +kernel

theorem arows16335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16335 = true := by
  rw [show D2M8K2.u16335 = KTree.node D2M8K2.t16346 (nat_lit 35791273) (nat_lit 1508216469) (nat_lit 0) D2M8K2.t16347 from rfl, allE_node, rows16346, irow16335, rows16347]
  all_goals rfl

theorem atot16335 : totK PD2M8K2 D2M8K2.u16335 = [0, 0, 397977571320, 971791251618, 393942881612, 15497389286, 0, 0] := by
  rw [show D2M8K2.u16335 = KTree.node D2M8K2.t16346 (nat_lit 35791273) (nat_lit 1508216469) (nat_lit 0) D2M8K2.t16347 from rfl, totK_node, tot16346, tot16347]
  decide +kernel

theorem arows16337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16337 = true := by
  rw [show D2M8K2.u16337 = KTree.node D2M8K2.t16348 (nat_lit 35793001) (nat_lit 1507380513) (nat_lit 0) D2M8K2.t16349 from rfl, allE_node, rows16348, irow16337, rows16349]
  all_goals rfl

theorem atot16337 : totK PD2M8K2 D2M8K2.u16337 = [0, 0, 93054923246, 672665696980, 898980108620, 148812119377, 1369150432, 0] := by
  rw [show D2M8K2.u16337 = KTree.node D2M8K2.t16348 (nat_lit 35793001) (nat_lit 1507380513) (nat_lit 0) D2M8K2.t16349 from rfl, totK_node, tot16348, tot16349]
  decide +kernel

theorem arows16338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16338 = true := by
  rw [show D2M8K2.u16338 = KTree.node D2M8K2.t16350 (nat_lit 35794873) (nat_lit 1382178263) (nat_lit 0) D2M8K2.t16351 from rfl, allE_node, rows16350, irow16338, rows16351]
  all_goals rfl

theorem atot16338 : totK PD2M8K2 D2M8K2.u16338 = [0, 0, 333149783287, 910439858066, 541423666819, 46953038515, 0, 0] := by
  rw [show D2M8K2.u16338 = KTree.node D2M8K2.t16350 (nat_lit 35794873) (nat_lit 1382178263) (nat_lit 0) D2M8K2.t16351 from rfl, totK_node, tot16350, tot16351]
  decide +kernel

theorem arows16343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16343 = true := by
  rw [show D2M8K2.u16343 = KTree.node D2M8K2.t16352 (nat_lit 35796462) (nat_lit 4079301544) (nat_lit 0) D2M8K2.t16353 from rfl, allE_node, rows16352, irow16343, rows16353]
  all_goals rfl

theorem atot16343 : totK PD2M8K2 D2M8K2.u16343 = [0, 0, 18444143370, 416656235354, 948483835298, 411606588269, 25217618697, 0] := by
  rw [show D2M8K2.u16343 = KTree.node D2M8K2.t16352 (nat_lit 35796462) (nat_lit 4079301544) (nat_lit 0) D2M8K2.t16353 from rfl, totK_node, tot16352, tot16353]
  decide +kernel

theorem arows16344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16344 = true := by
  rw [show D2M8K2.u16344 = KTree.node D2M8K2.t16354 (nat_lit 35797854) (nat_lit 3193315729) (nat_lit 0) D2M8K2.t16355 from rfl, allE_node, rows16354, irow16344, rows16355]
  all_goals rfl

theorem atot16344 : totK PD2M8K2 D2M8K2.u16344 = [0, 0, 394165254039, 941622037735, 435662264154, 31620169522, 0, 0] := by
  rw [show D2M8K2.u16344 = KTree.node D2M8K2.t16354 (nat_lit 35797854) (nat_lit 3193315729) (nat_lit 0) D2M8K2.t16355 from rfl, totK_node, tot16354, tot16355]
  decide +kernel

theorem arows16346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16346 = true := by
  rw [show D2M8K2.u16346 = KTree.node D2M8K2.t16356 (nat_lit 35799579) (nat_lit 3755763538) (nat_lit 0) D2M8K2.t16357 from rfl, allE_node, rows16356, irow16346, rows16357]
  all_goals rfl

theorem atot16346 : totK PD2M8K2 D2M8K2.u16346 = [0, 0, 7930757961, 529113839499, 972689200227, 251175931580, 8557595888, 0] := by
  rw [show D2M8K2.u16346 = KTree.node D2M8K2.t16356 (nat_lit 35799579) (nat_lit 3755763538) (nat_lit 0) D2M8K2.t16357 from rfl, totK_node, tot16356, tot16357]
  decide +kernel

theorem arows16347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16347 = true := by
  rw [show D2M8K2.u16347 = KTree.node D2M8K2.t16358 (nat_lit 35801573) (nat_lit 1874411370) (nat_lit 0) D2M8K2.t16359 from rfl, allE_node, rows16358, irow16347, rows16359]
  all_goals rfl

theorem atot16347 : totK PD2M8K2 D2M8K2.u16347 = [0, 0, 394177455792, 929901085216, 442543092771, 37718587391, 0, 0] := by
  rw [show D2M8K2.u16347 = KTree.node D2M8K2.t16358 (nat_lit 35801573) (nat_lit 1874411370) (nat_lit 0) D2M8K2.t16359 from rfl, totK_node, tot16358, tot16359]
  decide +kernel

theorem arows16350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16350 = true := by
  rw [show D2M8K2.u16350 = KTree.node D2M8K2.t16360 (nat_lit 35802862) (nat_lit 3997899919) (nat_lit 0) D2M8K2.t16361 from rfl, allE_node, rows16360, irow16350, rows16361]
  all_goals rfl

theorem atot16350 : totK PD2M8K2 D2M8K2.u16350 = [0, 0, 23509793184, 540331328165, 940404742204, 254042041692, 8656689423, 0] := by
  rw [show D2M8K2.u16350 = KTree.node D2M8K2.t16360 (nat_lit 35802862) (nat_lit 3997899919) (nat_lit 0) D2M8K2.t16361 from rfl, totK_node, tot16360, tot16361]
  decide +kernel

theorem arows16351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16351 = true := by
  rw [show D2M8K2.u16351 = KTree.node D2M8K2.t16362 (nat_lit 35808165) (nat_lit 863115973) (nat_lit 0) D2M8K2.t16363 from rfl, allE_node, rows16362, irow16351, rows16363]
  all_goals rfl

theorem atot16351 : totK PD2M8K2 D2M8K2.u16351 = [0, 0, 353755708962, 910791412587, 519022816532, 50426275285, 0, 0] := by
  rw [show D2M8K2.u16351 = KTree.node D2M8K2.t16362 (nat_lit 35808165) (nat_lit 863115973) (nat_lit 0) D2M8K2.t16363 from rfl, totK_node, tot16362, tot16363]
  decide +kernel

theorem arows16353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16353 = true := by
  rw [show D2M8K2.u16353 = KTree.node D2M8K2.t16364 (nat_lit 35809666) (nat_lit 4068400611) (nat_lit 0) D2M8K2.t16365 from rfl, allE_node, rows16364, irow16353, rows16365]
  all_goals rfl

theorem atot16353 : totK PD2M8K2 D2M8K2.u16353 = [0, 0, 93924006320, 603830390619, 883138171836, 228665798957, 4967996017, 0] := by
  rw [show D2M8K2.u16353 = KTree.node D2M8K2.t16364 (nat_lit 35809666) (nat_lit 4068400611) (nat_lit 0) D2M8K2.t16365 from rfl, totK_node, tot16364, tot16365]
  decide +kernel

theorem arows16354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16354 = true := by
  rw [show D2M8K2.u16354 = KTree.node D2M8K2.t16366 (nat_lit 35811265) (nat_lit 1503277576) (nat_lit 0) D2M8K2.t16367 from rfl, allE_node, rows16366, irow16354, rows16367]
  all_goals rfl

theorem atot16354 : totK PD2M8K2 D2M8K2.u16354 = [0, 0, 0, 351698294081, 932496106280, 438391468081, 26321964049, 0] := by
  rw [show D2M8K2.u16354 = KTree.node D2M8K2.t16366 (nat_lit 35811265) (nat_lit 1503277576) (nat_lit 0) D2M8K2.t16367 from rfl, totK_node, tot16366, tot16367]
  decide +kernel

theorem arows16358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16358 = true := by
  rw [show D2M8K2.u16358 = KTree.node D2M8K2.t16368 (nat_lit 35812883) (nat_lit 2834307850) (nat_lit 0) D2M8K2.t16369 from rfl, allE_node, rows16368, irow16358, rows16369]
  all_goals rfl

theorem atot16358 : totK PD2M8K2 D2M8K2.u16358 = [0, 0, 0, 152631023430, 731512431153, 724196492478, 103035811964, 1288491354] := by
  rw [show D2M8K2.u16358 = KTree.node D2M8K2.t16368 (nat_lit 35812883) (nat_lit 2834307850) (nat_lit 0) D2M8K2.t16369 from rfl, totK_node, tot16368, tot16369]
  decide +kernel

theorem arows16359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16359 = true := by
  rw [show D2M8K2.u16359 = KTree.node D2M8K2.t16370 (nat_lit 35815243) (nat_lit 1230465581) (nat_lit 0) D2M8K2.t16371 from rfl, allE_node, rows16370, irow16359, rows16371]
  all_goals rfl

theorem atot16359 : totK PD2M8K2 D2M8K2.u16359 = [0, 0, 0, 409151561263, 932402717978, 451567950767, 35911542691, 0] := by
  rw [show D2M8K2.u16359 = KTree.node D2M8K2.t16370 (nat_lit 35815243) (nat_lit 1230465581) (nat_lit 0) D2M8K2.t16371 from rfl, totK_node, tot16370, tot16371]
  decide +kernel

theorem arows16361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16361 = true := by
  rw [show D2M8K2.u16361 = KTree.node D2M8K2.t16372 (nat_lit 35818463) (nat_lit 1731797443) (nat_lit 0) D2M8K2.t16373 from rfl, allE_node, rows16372, irow16361, rows16373]
  all_goals rfl

theorem atot16361 : totK PD2M8K2 D2M8K2.u16361 = [0, 0, 0, 355234590674, 932100191995, 448509406556, 27770260813, 0] := by
  rw [show D2M8K2.u16361 = KTree.node D2M8K2.t16372 (nat_lit 35818463) (nat_lit 1731797443) (nat_lit 0) D2M8K2.t16373 from rfl, totK_node, tot16372, tot16373]
  decide +kernel

theorem arows16362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16362 = true := by
  rw [show D2M8K2.u16362 = KTree.node D2M8K2.t16374 (nat_lit 35820102) (nat_lit 1841829457) (nat_lit 0) D2M8K2.t16375 from rfl, allE_node, rows16374, irow16362, rows16375]
  all_goals rfl

theorem atot16362 : totK PD2M8K2 D2M8K2.u16362 = [0, 0, 0, 103600679851, 646816484136, 803931970941, 166855394044, 4787054165] := by
  rw [show D2M8K2.u16362 = KTree.node D2M8K2.t16374 (nat_lit 35820102) (nat_lit 1841829457) (nat_lit 0) D2M8K2.t16375 from rfl, totK_node, tot16374, tot16375]
  decide +kernel

theorem arows16365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16365 = true := by
  rw [show D2M8K2.u16365 = KTree.node D2M8K2.t16376 (nat_lit 35822413) (nat_lit 1056056118) (nat_lit 0) D2M8K2.t16377 from rfl, allE_node, rows16376, irow16365, rows16377]
  all_goals rfl

theorem atot16365 : totK PD2M8K2 D2M8K2.u16365 = [0, 0, 0, 379867206419, 944782969239, 425298468468, 22768865987, 0] := by
  rw [show D2M8K2.u16365 = KTree.node D2M8K2.t16376 (nat_lit 35822413) (nat_lit 1056056118) (nat_lit 0) D2M8K2.t16377 from rfl, totK_node, tot16376, tot16377]
  decide +kernel

theorem arows16366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16366 = true := by
  rw [show D2M8K2.u16366 = KTree.node D2M8K2.t16378 (nat_lit 35824187) (nat_lit 2159979684) (nat_lit 0) D2M8K2.t16379 from rfl, allE_node, rows16378, irow16366, rows16379]
  all_goals rfl

theorem atot16366 : totK PD2M8K2 D2M8K2.u16366 = [0, 0, 0, 105964568707, 655025864224, 782118032057, 167567890910, 4838243418] := by
  rw [show D2M8K2.u16366 = KTree.node D2M8K2.t16378 (nat_lit 35824187) (nat_lit 2159979684) (nat_lit 0) D2M8K2.t16379 from rfl, totK_node, tot16378, tot16379]
  decide +kernel

theorem arows16368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16368 = true := by
  rw [show D2M8K2.u16368 = KTree.node D2M8K2.t16380 (nat_lit 35829244) (nat_lit 3167566137) (nat_lit 0) D2M8K2.t16381 from rfl, allE_node, rows16380, irow16368, rows16381]
  all_goals rfl

theorem atot16368 : totK PD2M8K2 D2M8K2.u16368 = [0, 0, 0, 336734528459, 907823318070, 528549862998, 42599321789, 0] := by
  rw [show D2M8K2.u16368 = KTree.node D2M8K2.t16380 (nat_lit 35829244) (nat_lit 3167566137) (nat_lit 0) D2M8K2.t16381 from rfl, totK_node, tot16380, tot16381]
  decide +kernel

theorem arows16369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16369 = true := by
  rw [show D2M8K2.u16369 = KTree.node D2M8K2.t16382 (nat_lit 35830898) (nat_lit 1879004725) (nat_lit 0) D2M8K2.t16383 from rfl, allE_node, rows16382, irow16369, rows16383]
  all_goals rfl

theorem atot16369 : totK PD2M8K2 D2M8K2.u16369 = [0, 0, 0, 0, 410822987884, 927517717283, 365620745324, 21751168066] := by
  rw [show D2M8K2.u16369 = KTree.node D2M8K2.t16382 (nat_lit 35830898) (nat_lit 1879004725) (nat_lit 0) D2M8K2.t16383 from rfl, totK_node, tot16382, tot16383]
  decide +kernel

theorem arows2 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2 = true := by
  rw [show D2M8K2.u2 = KTree.node D2M8K2.u0 (nat_lit 1500) (nat_lit 3199214335) (nat_lit 0) D2M8K2.u1 from rfl, allE_node, arows0, irow2, arows1]
  all_goals rfl

theorem atot2 : totK PD2M8K2 D2M8K2.u2 = [495214582824, 1644339834810, 1332301675513, 179082143894, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u2 = KTree.node D2M8K2.u0 (nat_lit 1500) (nat_lit 3199214335) (nat_lit 0) D2M8K2.u1 from rfl, totK_node, atot0, atot1]
  decide +kernel

theorem arows5 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5 = true := by
  rw [show D2M8K2.u5 = KTree.node D2M8K2.u3 (nat_lit 8526) (nat_lit 2990931680) (nat_lit 0) D2M8K2.u4 from rfl, allE_node, arows3, irow5, arows4]
  all_goals rfl

theorem atot5 : totK PD2M8K2 D2M8K2.u5 = [375913218488, 1413634812973, 1447350703610, 331634961131, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u5 = KTree.node D2M8K2.u3 (nat_lit 8526) (nat_lit 2990931680) (nat_lit 0) D2M8K2.u4 from rfl, totK_node, atot3, atot4]
  decide +kernel

theorem arows9 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9 = true := by
  rw [show D2M8K2.u9 = KTree.node D2M8K2.u7 (nat_lit 11894) (nat_lit 3846405560) (nat_lit 0) D2M8K2.u8 from rfl, allE_node, arows7, irow9, arows8]
  all_goals rfl

theorem atot9 : totK PD2M8K2 D2M8K2.u9 = [413437776439, 1444597979367, 1384248481370, 328700064139, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u9 = KTree.node D2M8K2.u7 (nat_lit 11894) (nat_lit 3846405560) (nat_lit 0) D2M8K2.u8 from rfl, totK_node, atot7, atot8]
  decide +kernel

theorem arows12 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12 = true := by
  rw [show D2M8K2.u12 = KTree.node D2M8K2.u10 (nat_lit 14989) (nat_lit 1383681404) (nat_lit 0) D2M8K2.u11 from rfl, allE_node, arows10, irow12, arows11]
  all_goals rfl

theorem atot12 : totK PD2M8K2 D2M8K2.u12 = [418238016188, 1525105107357, 1421113373867, 232742934271, 2165917952, 0, 0, 0] := by
  rw [show D2M8K2.u12 = KTree.node D2M8K2.u10 (nat_lit 14989) (nat_lit 1383681404) (nat_lit 0) D2M8K2.u11 from rfl, totK_node, atot10, atot11]
  decide +kernel

theorem arows17 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u17 = true := by
  rw [show D2M8K2.u17 = KTree.node D2M8K2.u15 (nat_lit 18781) (nat_lit 1205998540) (nat_lit 0) D2M8K2.u16 from rfl, allE_node, arows15, irow17, arows16]
  all_goals rfl

theorem atot17 : totK PD2M8K2 D2M8K2.u17 = [422999544115, 1445600752734, 1385941928094, 337535012181, 11525337037, 0, 0, 0] := by
  rw [show D2M8K2.u17 = KTree.node D2M8K2.u15 (nat_lit 18781) (nat_lit 1205998540) (nat_lit 0) D2M8K2.u16 from rfl, totK_node, atot15, atot16]
  decide +kernel

theorem arows20 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u20 = true := by
  rw [show D2M8K2.u20 = KTree.node D2M8K2.u18 (nat_lit 21949) (nat_lit 1215652827) (nat_lit 0) D2M8K2.u19 from rfl, allE_node, arows18, irow20, arows19]
  all_goals rfl

theorem atot20 : totK PD2M8K2 D2M8K2.u20 = [0, 501731432781, 1662750959756, 1193127902131, 164011987075, 1369150432, 0, 0] := by
  rw [show D2M8K2.u20 = KTree.node D2M8K2.u18 (nat_lit 21949) (nat_lit 1215652827) (nat_lit 0) D2M8K2.u19 from rfl, totK_node, atot18, atot19]
  decide +kernel

theorem arows24 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u24 = true := by
  rw [show D2M8K2.u24 = KTree.node D2M8K2.u22 (nat_lit 29092) (nat_lit 3791399467) (nat_lit 0) D2M8K2.u23 from rfl, allE_node, arows22, irow24, arows23]
  all_goals rfl

theorem atot24 : totK PD2M8K2 D2M8K2.u24 = [0, 733263250294, 1873335266257, 921494588965, 54376570468, 0, 0, 0] := by
  rw [show D2M8K2.u24 = KTree.node D2M8K2.u22 (nat_lit 29092) (nat_lit 3791399467) (nat_lit 0) D2M8K2.u23 from rfl, totK_node, atot22, atot23]
  decide +kernel

theorem arows27 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u27 = true := by
  rw [show D2M8K2.u27 = KTree.node D2M8K2.u25 (nat_lit 35424) (nat_lit 3690063848) (nat_lit 0) D2M8K2.u26 from rfl, allE_node, arows25, irow27, arows26]
  all_goals rfl

theorem atot27 : totK PD2M8K2 D2M8K2.u27 = [0, 746893653554, 1902394487980, 873050375448, 44520356016, 0, 0, 0] := by
  rw [show D2M8K2.u27 = KTree.node D2M8K2.u25 (nat_lit 35424) (nat_lit 3690063848) (nat_lit 0) D2M8K2.u26 from rfl, totK_node, atot25, atot26]
  decide +kernel

theorem arows33 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u33 = true := by
  rw [show D2M8K2.u33 = KTree.node D2M8K2.u31 (nat_lit 83684) (nat_lit 2822708418) (nat_lit 0) D2M8K2.u32 from rfl, allE_node, arows31, irow33, arows32]
  all_goals rfl

theorem atot33 : totK PD2M8K2 D2M8K2.u33 = [422399947994, 1375013405688, 1337562891509, 435223240141, 22707539948, 0, 0, 0] := by
  rw [show D2M8K2.u33 = KTree.node D2M8K2.u31 (nat_lit 83684) (nat_lit 2822708418) (nat_lit 0) D2M8K2.u32 from rfl, totK_node, atot31, atot32]
  decide +kernel

theorem arows36 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u36 = true := by
  rw [show D2M8K2.u36 = KTree.node D2M8K2.u34 (nat_lit 87598) (nat_lit 2736627291) (nat_lit 0) D2M8K2.u35 from rfl, allE_node, arows34, irow36, arows35]
  all_goals rfl

theorem atot36 : totK PD2M8K2 D2M8K2.u36 = [327706987819, 1400271710600, 1524089490002, 362612239457, 22492124391, 0, 0, 0] := by
  rw [show D2M8K2.u36 = KTree.node D2M8K2.u34 (nat_lit 87598) (nat_lit 2736627291) (nat_lit 0) D2M8K2.u35 from rfl, totK_node, atot34, atot35]
  decide +kernel

theorem arows40 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u40 = true := by
  rw [show D2M8K2.u40 = KTree.node D2M8K2.u38 (nat_lit 90679) (nat_lit 1473896775) (nat_lit 0) D2M8K2.u39 from rfl, allE_node, arows38, irow40, arows39]
  all_goals rfl

theorem atot40 : totK PD2M8K2 D2M8K2.u40 = [439517154204, 1469705412055, 1386840056011, 328151057788, 9364503416, 0, 0, 0] := by
  rw [show D2M8K2.u40 = KTree.node D2M8K2.u38 (nat_lit 90679) (nat_lit 1473896775) (nat_lit 0) D2M8K2.u39 from rfl, totK_node, atot38, atot39]
  decide +kernel

theorem arows43 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u43 = true := by
  rw [show D2M8K2.u43 = KTree.node D2M8K2.u41 (nat_lit 97446) (nat_lit 3059707515) (nat_lit 0) D2M8K2.u42 from rfl, allE_node, arows41, irow43, arows42]
  all_goals rfl

theorem atot43 : totK PD2M8K2 D2M8K2.u43 = [409200881746, 1452154209602, 1389168252371, 305509136553, 12981912718, 0, 0, 0] := by
  rw [show D2M8K2.u43 = KTree.node D2M8K2.u41 (nat_lit 97446) (nat_lit 3059707515) (nat_lit 0) D2M8K2.u42 from rfl, totK_node, atot41, atot42]
  decide +kernel

theorem arows48 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u48 = true := by
  rw [show D2M8K2.u48 = KTree.node D2M8K2.u46 (nat_lit 100977) (nat_lit 1447709425) (nat_lit 0) D2M8K2.u47 from rfl, allE_node, arows46, irow48, arows47]
  all_goals rfl

theorem atot48 : totK PD2M8K2 D2M8K2.u48 = [414661219762, 1489901937066, 1427487477524, 280804465917, 5152749158, 0, 0, 0] := by
  rw [show D2M8K2.u48 = KTree.node D2M8K2.u46 (nat_lit 100977) (nat_lit 1447709425) (nat_lit 0) D2M8K2.u47 from rfl, totK_node, atot46, atot47]
  decide +kernel

theorem arows51 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u51 = true := by
  rw [show D2M8K2.u51 = KTree.node D2M8K2.u49 (nat_lit 104544) (nat_lit 3719854113) (nat_lit 0) D2M8K2.u50 from rfl, allE_node, arows49, irow51, arows50]
  all_goals rfl

theorem atot51 : totK PD2M8K2 D2M8K2.u51 = [0, 580145341711, 1734357596969, 1084853198311, 118159378900, 1206465782, 0, 0] := by
  rw [show D2M8K2.u51 = KTree.node D2M8K2.u49 (nat_lit 104544) (nat_lit 3719854113) (nat_lit 0) D2M8K2.u50 from rfl, totK_node, atot49, atot50]
  decide +kernel

theorem arows55 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u55 = true := by
  rw [show D2M8K2.u55 = KTree.node D2M8K2.u53 (nat_lit 108614) (nat_lit 4151327674) (nat_lit 0) D2M8K2.u54 from rfl, allE_node, arows53, irow55, arows54]
  all_goals rfl

theorem atot55 : totK PD2M8K2 D2M8K2.u55 = [0, 643771898634, 1802915191540, 1079567493194, 87967538656, 0, 0, 0] := by
  rw [show D2M8K2.u55 = KTree.node D2M8K2.u53 (nat_lit 108614) (nat_lit 4151327674) (nat_lit 0) D2M8K2.u54 from rfl, totK_node, atot53, atot54]
  decide +kernel

theorem arows58 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u58 = true := by
  rw [show D2M8K2.u58 = KTree.node D2M8K2.u56 (nat_lit 113512) (nat_lit 3723414069) (nat_lit 0) D2M8K2.u57 from rfl, allE_node, arows56, irow58, arows57]
  all_goals rfl

theorem atot58 : totK PD2M8K2 D2M8K2.u58 = [0, 386474121706, 1451031006211, 1361004985829, 303307683999, 13016197374, 0, 0] := by
  rw [show D2M8K2.u58 = KTree.node D2M8K2.u56 (nat_lit 113512) (nat_lit 3723414069) (nat_lit 0) D2M8K2.u57 from rfl, totK_node, atot56, atot57]
  decide +kernel

theorem arows65 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u65 = true := by
  rw [show D2M8K2.u65 = KTree.node D2M8K2.u63 (nat_lit 120477) (nat_lit 1539482468) (nat_lit 0) D2M8K2.u64 from rfl, allE_node, arows63, irow65, arows64]
  all_goals rfl

theorem atot65 : totK PD2M8K2 D2M8K2.u65 = [0, 458471474275, 1587913089136, 1267722135608, 186534652599, 4574395652, 0, 0] := by
  rw [show D2M8K2.u65 = KTree.node D2M8K2.u63 (nat_lit 120477) (nat_lit 1539482468) (nat_lit 0) D2M8K2.u64 from rfl, totK_node, atot63, atot64]
  decide +kernel

theorem arows68 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u68 = true := by
  rw [show D2M8K2.u68 = KTree.node D2M8K2.u66 (nat_lit 125629) (nat_lit 1210781706) (nat_lit 0) D2M8K2.u67 from rfl, allE_node, arows66, irow68, arows67]
  all_goals rfl

theorem atot68 : totK PD2M8K2 D2M8K2.u68 = [422427504925, 1501555358742, 1369491110501, 299230439355, 14936070864, 0, 0, 0] := by
  rw [show D2M8K2.u68 = KTree.node D2M8K2.u66 (nat_lit 125629) (nat_lit 1210781706) (nat_lit 0) D2M8K2.u67 from rfl, totK_node, atot66, atot67]
  decide +kernel

theorem arows72 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u72 = true := by
  rw [show D2M8K2.u72 = KTree.node D2M8K2.u70 (nat_lit 129521) (nat_lit 1558125490) (nat_lit 0) D2M8K2.u71 from rfl, allE_node, arows70, irow72, arows71]
  all_goals rfl

theorem atot72 : totK PD2M8K2 D2M8K2.u72 = [363668620247, 1302064118838, 1454260065085, 483078429838, 30732467914, 0, 0, 0] := by
  rw [show D2M8K2.u72 = KTree.node D2M8K2.u70 (nat_lit 129521) (nat_lit 1558125490) (nat_lit 0) D2M8K2.u71 from rfl, totK_node, atot70, atot71]
  decide +kernel

theorem arows75 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u75 = true := by
  rw [show D2M8K2.u75 = KTree.node D2M8K2.u73 (nat_lit 136314) (nat_lit 3918445402) (nat_lit 0) D2M8K2.u74 from rfl, allE_node, arows73, irow75, arows74]
  all_goals rfl

theorem atot75 : totK PD2M8K2 D2M8K2.u75 = [403870460419, 1460041939713, 1418840631212, 324793630267, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u75 = KTree.node D2M8K2.u73 (nat_lit 136314) (nat_lit 3918445402) (nat_lit 0) D2M8K2.u74 from rfl, totK_node, atot73, atot74]
  decide +kernel

theorem arows80 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u80 = true := by
  rw [show D2M8K2.u80 = KTree.node D2M8K2.u78 (nat_lit 139397) (nat_lit 2264115136) (nat_lit 0) D2M8K2.u79 from rfl, allE_node, arows78, irow80, arows79]
  all_goals rfl

theorem atot80 : totK PD2M8K2 D2M8K2.u80 = [409262576309, 1502162006753, 1426400238483, 247425552864, 2165917952, 0, 0, 0] := by
  rw [show D2M8K2.u80 = KTree.node D2M8K2.u78 (nat_lit 139397) (nat_lit 2264115136) (nat_lit 0) D2M8K2.u79 from rfl, totK_node, atot78, atot79]
  decide +kernel

theorem arows83 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u83 = true := by
  rw [show D2M8K2.u83 = KTree.node D2M8K2.u81 (nat_lit 143214) (nat_lit 4037877846) (nat_lit 0) D2M8K2.u82 from rfl, allE_node, arows81, irow83, arows82]
  all_goals rfl

theorem atot83 : totK PD2M8K2 D2M8K2.u83 = [414739526806, 1441392222538, 1399231755280, 343556468229, 11522610644, 0, 0, 0] := by
  rw [show D2M8K2.u83 = KTree.node D2M8K2.u81 (nat_lit 143214) (nat_lit 4037877846) (nat_lit 0) D2M8K2.u82 from rfl, totK_node, atot81, atot82]
  decide +kernel

theorem arows87 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u87 = true := by
  rw [show D2M8K2.u87 = KTree.node D2M8K2.u85 (nat_lit 146497) (nat_lit 1398338693) (nat_lit 0) D2M8K2.u86 from rfl, allE_node, arows85, irow87, arows86]
  all_goals rfl

theorem atot87 : totK PD2M8K2 D2M8K2.u87 = [0, 492864789591, 1669407664180, 1240584323308, 136674988190, 1239866073, 0, 0] := by
  rw [show D2M8K2.u87 = KTree.node D2M8K2.u85 (nat_lit 146497) (nat_lit 1398338693) (nat_lit 0) D2M8K2.u86 from rfl, totK_node, atot85, atot86]
  decide +kernel

theorem arows90 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u90 = true := by
  rw [show D2M8K2.u90 = KTree.node D2M8K2.u88 (nat_lit 155658) (nat_lit 3794669782) (nat_lit 0) D2M8K2.u89 from rfl, allE_node, arows88, irow90, arows89]
  all_goals rfl

theorem atot90 : totK PD2M8K2 D2M8K2.u90 = [0, 726034831535, 1863617486602, 962522715976, 75268737643, 0, 0, 0] := by
  rw [show D2M8K2.u90 = KTree.node D2M8K2.u88 (nat_lit 155658) (nat_lit 3794669782) (nat_lit 0) D2M8K2.u89 from rfl, totK_node, atot88, atot89]
  decide +kernel

theorem arows96 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u96 = true := by
  rw [show D2M8K2.u96 = KTree.node D2M8K2.u94 (nat_lit 158994) (nat_lit 3391139419) (nat_lit 0) D2M8K2.u95 from rfl, allE_node, arows94, irow96, arows95]
  all_goals rfl

theorem atot96 : totK PD2M8K2 D2M8K2.u96 = [0, 407369255109, 1442827674041, 1354054633091, 306925063373, 13105450397, 0, 0] := by
  rw [show D2M8K2.u96 = KTree.node D2M8K2.u94 (nat_lit 158994) (nat_lit 3391139419) (nat_lit 0) D2M8K2.u95 from rfl, totK_node, atot94, atot95]
  decide +kernel

theorem arows99 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u99 = true := by
  rw [show D2M8K2.u99 = KTree.node D2M8K2.u97 (nat_lit 162656) (nat_lit 3264485359) (nat_lit 0) D2M8K2.u98 from rfl, allE_node, arows97, irow99, arows98]
  all_goals rfl

theorem atot99 : totK PD2M8K2 D2M8K2.u99 = [22498951891, 441324127026, 1526763126468, 1337698323838, 205131424650, 4720618446, 0, 0] := by
  rw [show D2M8K2.u99 = KTree.node D2M8K2.u97 (nat_lit 162656) (nat_lit 3264485359) (nat_lit 0) D2M8K2.u98 from rfl, totK_node, atot97, atot98]
  decide +kernel

theorem arows103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u103 = true := by
  rw [show D2M8K2.u103 = KTree.node D2M8K2.u101 (nat_lit 167458) (nat_lit 4161352998) (nat_lit 0) D2M8K2.u102 from rfl, allE_node, arows101, irow103, arows102]
  all_goals rfl

theorem atot103 : totK PD2M8K2 D2M8K2.u103 = [472997481203, 1616644937619, 1334423413777, 184927363460, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u103 = KTree.node D2M8K2.u101 (nat_lit 167458) (nat_lit 4161352998) (nat_lit 0) D2M8K2.u102 from rfl, totK_node, atot101, atot102]
  decide +kernel

theorem arows106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u106 = true := by
  rw [show D2M8K2.u106 = KTree.node D2M8K2.u104 (nat_lit 171679) (nat_lit 1567585406) (nat_lit 0) D2M8K2.u105 from rfl, allE_node, arows104, irow106, arows105]
  all_goals rfl

theorem atot106 : totK PD2M8K2 D2M8K2.u106 = [416212785818, 1367715859063, 1346395928203, 439321341107, 26535726543, 0, 0, 0] := by
  rw [show D2M8K2.u106 = KTree.node D2M8K2.u104 (nat_lit 171679) (nat_lit 1567585406) (nat_lit 0) D2M8K2.u105 from rfl, totK_node, atot104, atot105]
  decide +kernel

theorem arows111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u111 = true := by
  rw [show D2M8K2.u111 = KTree.node D2M8K2.u109 (nat_lit 174859) (nat_lit 1441639963) (nat_lit 0) D2M8K2.u110 from rfl, allE_node, arows109, irow111, arows110]
  all_goals rfl

theorem atot111 : totK PD2M8K2 D2M8K2.u111 = [411230524519, 1427972332119, 1400005984356, 321606729642, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u111 = KTree.node D2M8K2.u109 (nat_lit 174859) (nat_lit 1441639963) (nat_lit 0) D2M8K2.u110 from rfl, totK_node, atot109, atot110]
  decide +kernel

theorem arows114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u114 = true := by
  rw [show D2M8K2.u114 = KTree.node D2M8K2.u112 (nat_lit 178230) (nat_lit 3633367727) (nat_lit 0) D2M8K2.u113 from rfl, allE_node, arows112, irow114, arows113]
  all_goals rfl

theorem atot114 : totK PD2M8K2 D2M8K2.u114 = [378002745411, 1412975257268, 1434973055836, 343128614396, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u114 = KTree.node D2M8K2.u112 (nat_lit 178230) (nat_lit 3633367727) (nat_lit 0) D2M8K2.u113 from rfl, totK_node, atot112, atot113]
  decide +kernel

theorem arows118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u118 = true := by
  rw [show D2M8K2.u118 = KTree.node D2M8K2.u116 (nat_lit 181542) (nat_lit 3710900557) (nat_lit 0) D2M8K2.u117 from rfl, allE_node, arows116, irow118, arows117]
  all_goals rfl

theorem atot118 : totK PD2M8K2 D2M8K2.u118 = [303387510043, 1388762992748, 1586532158814, 333476834782, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u118 = KTree.node D2M8K2.u116 (nat_lit 181542) (nat_lit 3710900557) (nat_lit 0) D2M8K2.u117 from rfl, totK_node, atot116, atot117]
  decide +kernel

theorem arows121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u121 = true := by
  rw [show D2M8K2.u121 = KTree.node D2M8K2.u119 (nat_lit 188549) (nat_lit 2049731252) (nat_lit 0) D2M8K2.u120 from rfl, allE_node, arows119, irow121, arows120]
  all_goals rfl

theorem atot121 : totK PD2M8K2 D2M8K2.u121 = [0, 518051570336, 1689505321431, 1178810431679, 134558076245, 1138244013, 0, 0] := by
  rw [show D2M8K2.u121 = KTree.node D2M8K2.u119 (nat_lit 188549) (nat_lit 2049731252) (nat_lit 0) D2M8K2.u120 from rfl, totK_node, atot119, atot120]
  decide +kernel

theorem arows129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u129 = true := by
  rw [show D2M8K2.u129 = KTree.node D2M8K2.u127 (nat_lit 194358) (nat_lit 2707062646) (nat_lit 0) D2M8K2.u128 from rfl, allE_node, arows127, irow129, arows128]
  all_goals rfl

theorem atot129 : totK PD2M8K2 D2M8K2.u129 = [0, 747475404103, 1899557366219, 888503094154, 48423964192, 0, 0, 0] := by
  rw [show D2M8K2.u129 = KTree.node D2M8K2.u127 (nat_lit 194358) (nat_lit 2707062646) (nat_lit 0) D2M8K2.u128 from rfl, totK_node, atot127, atot128]
  decide +kernel

theorem arows132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u132 = true := by
  rw [show D2M8K2.u132 = KTree.node D2M8K2.u130 (nat_lit 200988) (nat_lit 2136181959) (nat_lit 0) D2M8K2.u131 from rfl, allE_node, arows130, irow132, arows131]
  all_goals rfl

theorem atot132 : totK PD2M8K2 D2M8K2.u132 = [0, 608158150805, 1743377995707, 1066453900287, 117884313869, 1095107716, 0, 0] := by
  rw [show D2M8K2.u132 = KTree.node D2M8K2.u130 (nat_lit 200988) (nat_lit 2136181959) (nat_lit 0) D2M8K2.u131 from rfl, totK_node, atot130, atot131]
  decide +kernel

theorem arows136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u136 = true := by
  rw [show D2M8K2.u136 = KTree.node D2M8K2.u134 (nat_lit 208232) (nat_lit 3486269447) (nat_lit 0) D2M8K2.u135 from rfl, allE_node, arows134, irow136, arows135]
  all_goals rfl

theorem atot136 : totK PD2M8K2 D2M8K2.u136 = [422663761561, 1239740453087, 1164591473816, 618784255866, 124484936370, 3882006667, 0, 0] := by
  rw [show D2M8K2.u136 = KTree.node D2M8K2.u134 (nat_lit 208232) (nat_lit 3486269447) (nat_lit 0) D2M8K2.u135 from rfl, totK_node, atot134, atot135]
  decide +kernel

theorem arows139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u139 = true := by
  rw [show D2M8K2.u139 = KTree.node D2M8K2.u137 (nat_lit 211844) (nat_lit 2319514546) (nat_lit 0) D2M8K2.u138 from rfl, allE_node, arows137, irow139, arows138]
  all_goals rfl

theorem atot139 : totK PD2M8K2 D2M8K2.u139 = [329518342188, 1343956250669, 1513344102095, 422113621053, 27737127524, 0, 0, 0] := by
  rw [show D2M8K2.u139 = KTree.node D2M8K2.u137 (nat_lit 211844) (nat_lit 2319514546) (nat_lit 0) D2M8K2.u138 from rfl, totK_node, atot137, atot138]
  decide +kernel

theorem arows144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u144 = true := by
  rw [show D2M8K2.u144 = KTree.node D2M8K2.u142 (nat_lit 215465) (nat_lit 1805851422) (nat_lit 0) D2M8K2.u143 from rfl, allE_node, arows142, irow144, arows143]
  all_goals rfl

theorem atot144 : totK PD2M8K2 D2M8K2.u144 = [412579010579, 1425587641190, 1393167661907, 358581735885, 16388616678, 0, 0, 0] := by
  rw [show D2M8K2.u144 = KTree.node D2M8K2.u142 (nat_lit 215465) (nat_lit 1805851422) (nat_lit 0) D2M8K2.u143 from rfl, totK_node, atot142, atot143]
  decide +kernel

theorem arows147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u147 = true := by
  rw [show D2M8K2.u147 = KTree.node D2M8K2.u145 (nat_lit 218884) (nat_lit 2741307319) (nat_lit 0) D2M8K2.u146 from rfl, allE_node, arows145, irow147, arows146]
  all_goals rfl

theorem atot147 : totK PD2M8K2 D2M8K2.u147 = [412823072983, 1442875374296, 1399511961628, 329714335129, 13124827713, 0, 0, 0] := by
  rw [show D2M8K2.u147 = KTree.node D2M8K2.u145 (nat_lit 218884) (nat_lit 2741307319) (nat_lit 0) D2M8K2.u146 from rfl, totK_node, atot145, atot146]
  decide +kernel

theorem arows151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u151 = true := by
  rw [show D2M8K2.u151 = KTree.node D2M8K2.u149 (nat_lit 225425) (nat_lit 2210428727) (nat_lit 0) D2M8K2.u150 from rfl, allE_node, arows149, irow151, arows150]
  all_goals rfl

theorem atot151 : totK PD2M8K2 D2M8K2.u151 = [441685160947, 1532105942345, 1398779065317, 268347499989, 4847807762, 0, 0, 0] := by
  rw [show D2M8K2.u151 = KTree.node D2M8K2.u149 (nat_lit 225425) (nat_lit 2210428727) (nat_lit 0) D2M8K2.u150 from rfl, totK_node, atot149, atot150]
  decide +kernel

theorem arows154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u154 = true := by
  rw [show D2M8K2.u154 = KTree.node D2M8K2.u152 (nat_lit 228864) (nat_lit 3422611686) (nat_lit 0) D2M8K2.u153 from rfl, allE_node, arows152, irow154, arows153]
  all_goals rfl

theorem atot154 : totK PD2M8K2 D2M8K2.u154 = [0, 616561764954, 1770946101554, 1055599062282, 110809311858, 1310285577, 0, 0] := by
  rw [show D2M8K2.u154 = KTree.node D2M8K2.u152 (nat_lit 228864) (nat_lit 3422611686) (nat_lit 0) D2M8K2.u153 from rfl, totK_node, atot152, atot153]
  decide +kernel

theorem arows160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u160 = true := by
  rw [show D2M8K2.u160 = KTree.node D2M8K2.u158 (nat_lit 232560) (nat_lit 3452117834) (nat_lit 0) D2M8K2.u159 from rfl, allE_node, arows158, irow160, arows159]
  all_goals rfl

theorem atot160 : totK PD2M8K2 D2M8K2.u160 = [0, 583422927111, 1721781676831, 1207137571576, 111246895539, 0, 0, 0] := by
  rw [show D2M8K2.u160 = KTree.node D2M8K2.u158 (nat_lit 232560) (nat_lit 3452117834) (nat_lit 0) D2M8K2.u159 from rfl, totK_node, atot158, atot159]
  decide +kernel

theorem arows163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u163 = true := by
  rw [show D2M8K2.u163 = KTree.node D2M8K2.u161 (nat_lit 237553) (nat_lit 1239445218) (nat_lit 0) D2M8K2.u162 from rfl, allE_node, arows161, irow163, arows162]
  all_goals rfl

theorem atot163 : totK PD2M8K2 D2M8K2.u163 = [0, 441679104654, 1539415929315, 1347153191389, 220172853157, 4879840392, 0, 0] := by
  rw [show D2M8K2.u163 = KTree.node D2M8K2.u161 (nat_lit 237553) (nat_lit 1239445218) (nat_lit 0) D2M8K2.u162 from rfl, totK_node, atot161, atot162]
  decide +kernel

theorem arows167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u167 = true := by
  rw [show D2M8K2.u167 = KTree.node D2M8K2.u165 (nat_lit 241638) (nat_lit 3787266842) (nat_lit 0) D2M8K2.u166 from rfl, allE_node, arows165, irow167, arows166]
  all_goals rfl

theorem atot167 : totK PD2M8K2 D2M8K2.u167 = [0, 471547220277, 1577386679165, 1308747317225, 212876984777, 4931404646, 0, 0] := by
  rw [show D2M8K2.u167 = KTree.node D2M8K2.u165 (nat_lit 241638) (nat_lit 3787266842) (nat_lit 0) D2M8K2.u166 from rfl, totK_node, atot165, atot166]
  decide +kernel

theorem arows170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u170 = true := by
  rw [show D2M8K2.u170 = KTree.node D2M8K2.u168 (nat_lit 248101) (nat_lit 1348133567) (nat_lit 0) D2M8K2.u169 from rfl, allE_node, arows168, irow170, arows169]
  all_goals rfl

theorem atot170 : totK PD2M8K2 D2M8K2.u170 = [0, 360707296079, 1362517039273, 1425865729208, 398725348091, 21751168066, 0, 0] := by
  rw [show D2M8K2.u170 = KTree.node D2M8K2.u168 (nat_lit 248101) (nat_lit 1348133567) (nat_lit 0) D2M8K2.u169 from rfl, totK_node, atot168, atot169]
  decide +kernel

theorem arows175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u175 = true := by
  rw [show D2M8K2.u175 = KTree.node D2M8K2.u173 (nat_lit 251545) (nat_lit 1494107706) (nat_lit 0) D2M8K2.u174 from rfl, allE_node, arows173, irow175, arows174]
  all_goals rfl

theorem atot175 : totK PD2M8K2 D2M8K2.u175 = [0, 455345023332, 1605624536182, 1373434288043, 187534484100, 1369150432, 0, 0] := by
  rw [show D2M8K2.u175 = KTree.node D2M8K2.u173 (nat_lit 251545) (nat_lit 1494107706) (nat_lit 0) D2M8K2.u174 from rfl, totK_node, atot173, atot174]
  decide +kernel

theorem arows178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u178 = true := by
  rw [show D2M8K2.u178 = KTree.node D2M8K2.u176 (nat_lit 258636) (nat_lit 3429179398) (nat_lit 0) D2M8K2.u177 from rfl, allE_node, arows176, irow178, arows177]
  all_goals rfl

theorem atot178 : totK PD2M8K2 D2M8K2.u178 = [0, 384423348713, 1436305991495, 1427072147227, 292450939785, 12891658009, 0, 0] := by
  rw [show D2M8K2.u178 = KTree.node D2M8K2.u176 (nat_lit 258636) (nat_lit 3429179398) (nat_lit 0) D2M8K2.u177 from rfl, totK_node, atot176, atot177]
  decide +kernel

theorem arows182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u182 = true := by
  rw [show D2M8K2.u182 = KTree.node D2M8K2.u180 (nat_lit 262038) (nat_lit 3787306984) (nat_lit 0) D2M8K2.u181 from rfl, allE_node, arows180, irow182, arows181]
  all_goals rfl

theorem atot182 : totK PD2M8K2 D2M8K2.u182 = [0, 406467686647, 1431145105878, 1391862606551, 297152817327, 13092379805, 0, 0] := by
  rw [show D2M8K2.u182 = KTree.node D2M8K2.u180 (nat_lit 262038) (nat_lit 3787306984) (nat_lit 0) D2M8K2.u181 from rfl, totK_node, atot180, atot181]
  decide +kernel

theorem arows185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u185 = true := by
  rw [show D2M8K2.u185 = KTree.node D2M8K2.u183 (nat_lit 265327) (nat_lit 2447609201) (nat_lit 0) D2M8K2.u184 from rfl, allE_node, arows183, irow185, arows184]
  all_goals rfl

theorem atot185 : totK PD2M8K2 D2M8K2.u185 = [0, 452232013141, 1543048357757, 1357416493794, 212229111067, 4934531535, 0, 0] := by
  rw [show D2M8K2.u185 = KTree.node D2M8K2.u183 (nat_lit 265327) (nat_lit 2447609201) (nat_lit 0) D2M8K2.u184 from rfl, totK_node, atot183, atot184]
  decide +kernel

theorem arows192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u192 = true := by
  rw [show D2M8K2.u192 = KTree.node D2M8K2.u190 (nat_lit 268705) (nat_lit 1547309105) (nat_lit 0) D2M8K2.u191 from rfl, allE_node, arows190, irow192, arows191]
  all_goals rfl

theorem atot192 : totK PD2M8K2 D2M8K2.u192 = [0, 144051062126, 1062891446367, 1736440812879, 572112521143, 31382877437, 0, 0] := by
  rw [show D2M8K2.u192 = KTree.node D2M8K2.u190 (nat_lit 268705) (nat_lit 1547309105) (nat_lit 0) D2M8K2.u191 from rfl, totK_node, atot190, atot191]
  decide +kernel

theorem arows195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u195 = true := by
  rw [show D2M8K2.u195 = KTree.node D2M8K2.u193 (nat_lit 272176) (nat_lit 2646416075) (nat_lit 0) D2M8K2.u194 from rfl, allE_node, arows193, irow195, arows194]
  all_goals rfl

theorem atot195 : totK PD2M8K2 D2M8K2.u195 = [0, 0, 515150991433, 1651400622342, 1151999690973, 164581591861, 1369150432, 0] := by
  rw [show D2M8K2.u195 = KTree.node D2M8K2.u193 (nat_lit 272176) (nat_lit 2646416075) (nat_lit 0) D2M8K2.u194 from rfl, totK_node, atot193, atot194]
  decide +kernel

theorem arows199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u199 = true := by
  rw [show D2M8K2.u199 = KTree.node D2M8K2.u197 (nat_lit 281166) (nat_lit 4023064257) (nat_lit 0) D2M8K2.u198 from rfl, allE_node, arows197, irow199, arows198]
  all_goals rfl

theorem atot199 : totK PD2M8K2 D2M8K2.u199 = [0, 0, 805614312392, 1912003269885, 743736317991, 44263042034, 0, 0] := by
  rw [show D2M8K2.u199 = KTree.node D2M8K2.u197 (nat_lit 281166) (nat_lit 4023064257) (nat_lit 0) D2M8K2.u198 from rfl, totK_node, atot197, atot198]
  decide +kernel

theorem arows202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u202 = true := by
  rw [show D2M8K2.u202 = KTree.node D2M8K2.u200 (nat_lit 287806) (nat_lit 3892752328) (nat_lit 0) D2M8K2.u201 from rfl, allE_node, arows200, irow202, arows201]
  all_goals rfl

theorem atot202 : totK PD2M8K2 D2M8K2.u202 = [0, 249819336703, 1115690366070, 1577909542649, 572327904273, 34667481554, 0, 0] := by
  rw [show D2M8K2.u202 = KTree.node D2M8K2.u200 (nat_lit 287806) (nat_lit 3892752328) (nat_lit 0) D2M8K2.u201 from rfl, totK_node, atot200, atot201]
  decide +kernel

theorem arows207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u207 = true := by
  rw [show D2M8K2.u207 = KTree.node D2M8K2.u205 (nat_lit 334504) (nat_lit 2669887819) (nat_lit 0) D2M8K2.u206 from rfl, allE_node, arows205, irow207, arows206]
  all_goals rfl

theorem atot207 : totK PD2M8K2 D2M8K2.u207 = [0, 445824969378, 1577666353203, 1372430133940, 194122322029, 1369150432, 0, 0] := by
  rw [show D2M8K2.u207 = KTree.node D2M8K2.u205 (nat_lit 334504) (nat_lit 2669887819) (nat_lit 0) D2M8K2.u206 from rfl, totK_node, atot205, atot206]
  decide +kernel

theorem arows210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u210 = true := by
  rw [show D2M8K2.u210 = KTree.node D2M8K2.u208 (nat_lit 338843) (nat_lit 2729477752) (nat_lit 0) D2M8K2.u209 from rfl, allE_node, arows208, irow210, arows209]
  all_goals rfl

theorem atot210 : totK PD2M8K2 D2M8K2.u210 = [0, 490329264541, 1579394788522, 1322647366756, 242870946509, 5284349065, 0, 0] := by
  rw [show D2M8K2.u210 = KTree.node D2M8K2.u208 (nat_lit 338843) (nat_lit 2729477752) (nat_lit 0) D2M8K2.u209 from rfl, totK_node, atot208, atot209]
  decide +kernel

theorem arows214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u214 = true := by
  rw [show D2M8K2.u214 = KTree.node D2M8K2.u212 (nat_lit 345616) (nat_lit 3371086046) (nat_lit 0) D2M8K2.u213 from rfl, allE_node, arows212, irow214, arows213]
  all_goals rfl

theorem atot214 : totK PD2M8K2 D2M8K2.u214 = [0, 404152066390, 1395613080719, 1432642094345, 329289184393, 13049727234, 0, 0] := by
  rw [show D2M8K2.u214 = KTree.node D2M8K2.u212 (nat_lit 345616) (nat_lit 3371086046) (nat_lit 0) D2M8K2.u213 from rfl, totK_node, atot212, atot213]
  decide +kernel

theorem arows217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u217 = true := by
  rw [show D2M8K2.u217 = KTree.node D2M8K2.u215 (nat_lit 349187) (nat_lit 2975440576) (nat_lit 0) D2M8K2.u216 from rfl, allE_node, arows215, irow217, arows216]
  all_goals rfl

theorem atot217 : totK PD2M8K2 D2M8K2.u217 = [0, 417610729682, 1555711393248, 1395353381380, 220646400961, 4917269347, 0, 0] := by
  rw [show D2M8K2.u217 = KTree.node D2M8K2.u215 (nat_lit 349187) (nat_lit 2975440576) (nat_lit 0) D2M8K2.u216 from rfl, totK_node, atot215, atot216]
  decide +kernel

theorem arows223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u223 = true := by
  rw [show D2M8K2.u223 = KTree.node D2M8K2.u221 (nat_lit 373327) (nat_lit 2427379393) (nat_lit 0) D2M8K2.u222 from rfl, allE_node, arows221, irow223, arows222]
  all_goals rfl

theorem atot223 : totK PD2M8K2 D2M8K2.u223 = [0, 420395822285, 1436871868772, 1377802159329, 326933644745, 13684302317, 0, 0] := by
  rw [show D2M8K2.u223 = KTree.node D2M8K2.u221 (nat_lit 373327) (nat_lit 2427379393) (nat_lit 0) D2M8K2.u222 from rfl, totK_node, atot221, atot222]
  decide +kernel

theorem arows226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u226 = true := by
  rw [show D2M8K2.u226 = KTree.node D2M8K2.u224 (nat_lit 377256) (nat_lit 2567531928) (nat_lit 0) D2M8K2.u225 from rfl, allE_node, arows224, irow226, arows225]
  all_goals rfl

theorem atot226 : totK PD2M8K2 D2M8K2.u226 = [0, 326976031352, 1477669419188, 1571619475336, 250482855399, 1369150432, 0, 0] := by
  rw [show D2M8K2.u226 = KTree.node D2M8K2.u224 (nat_lit 377256) (nat_lit 2567531928) (nat_lit 0) D2M8K2.u225 from rfl, totK_node, atot224, atot225]
  decide +kernel

theorem arows230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u230 = true := by
  rw [show D2M8K2.u230 = KTree.node D2M8K2.u228 (nat_lit 384614) (nat_lit 3968874106) (nat_lit 0) D2M8K2.u229 from rfl, allE_node, arows228, irow230, arows229]
  all_goals rfl

theorem atot230 : totK PD2M8K2 D2M8K2.u230 = [0, 438954919465, 1502030011535, 1387690058029, 286492952470, 6527558394, 0, 0] := by
  rw [show D2M8K2.u230 = KTree.node D2M8K2.u228 (nat_lit 384614) (nat_lit 3968874106) (nat_lit 0) D2M8K2.u229 from rfl, totK_node, atot228, atot229]
  decide +kernel

theorem arows233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u233 = true := by
  rw [show D2M8K2.u233 = KTree.node D2M8K2.u231 (nat_lit 387649) (nat_lit 1544010190) (nat_lit 0) D2M8K2.u232 from rfl, allE_node, arows231, irow233, arows232]
  all_goals rfl

theorem atot233 : totK PD2M8K2 D2M8K2.u233 = [0, 408162620350, 1435414364377, 1388702097605, 309156836946, 13088430220, 0, 0] := by
  rw [show D2M8K2.u233 = KTree.node D2M8K2.u231 (nat_lit 387649) (nat_lit 1544010190) (nat_lit 0) D2M8K2.u232 from rfl, totK_node, atot231, atot232]
  decide +kernel

theorem arows238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u238 = true := by
  rw [show D2M8K2.u238 = KTree.node D2M8K2.u236 (nat_lit 391242) (nat_lit 3267423339) (nat_lit 0) D2M8K2.u237 from rfl, allE_node, arows236, irow238, arows237]
  all_goals rfl

theorem atot238 : totK PD2M8K2 D2M8K2.u238 = [0, 413743757880, 1502779273859, 1433794910029, 254187250447, 5053789144, 0, 0] := by
  rw [show D2M8K2.u238 = KTree.node D2M8K2.u236 (nat_lit 391242) (nat_lit 3267423339) (nat_lit 0) D2M8K2.u237 from rfl, totK_node, atot236, atot237]
  decide +kernel

theorem arows241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u241 = true := by
  rw [show D2M8K2.u241 = KTree.node D2M8K2.u239 (nat_lit 415623) (nat_lit 3298866344) (nat_lit 0) D2M8K2.u240 from rfl, allE_node, arows239, irow241, arows240]
  all_goals rfl

theorem atot241 : totK PD2M8K2 D2M8K2.u241 = [0, 419942918821, 1442354008951, 1357907414858, 325780284714, 13851206879, 0, 0] := by
  rw [show D2M8K2.u241 = KTree.node D2M8K2.u239 (nat_lit 415623) (nat_lit 3298866344) (nat_lit 0) D2M8K2.u240 from rfl, totK_node, atot239, atot240]
  decide +kernel

theorem arows245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u245 = true := by
  rw [show D2M8K2.u245 = KTree.node D2M8K2.u243 (nat_lit 419275) (nat_lit 2223646949) (nat_lit 0) D2M8K2.u244 from rfl, allE_node, arows243, irow245, arows244]
  all_goals rfl

theorem atot245 : totK PD2M8K2 D2M8K2.u245 = [0, 409933395645, 1538872972078, 1457879375115, 216517262479, 1409560813, 0, 0] := by
  rw [show D2M8K2.u245 = KTree.node D2M8K2.u243 (nat_lit 419275) (nat_lit 2223646949) (nat_lit 0) D2M8K2.u244 from rfl, totK_node, atot243, atot244]
  decide +kernel

theorem arows248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u248 = true := by
  rw [show D2M8K2.u248 = KTree.node D2M8K2.u246 (nat_lit 423376) (nat_lit 3384911032) (nat_lit 0) D2M8K2.u247 from rfl, allE_node, arows246, irow248, arows247]
  all_goals rfl

theorem atot248 : totK PD2M8K2 D2M8K2.u248 = [0, 410167379721, 1437604392746, 1388266960348, 301579023530, 12983449796, 0, 0] := by
  rw [show D2M8K2.u248 = KTree.node D2M8K2.u246 (nat_lit 423376) (nat_lit 3384911032) (nat_lit 0) D2M8K2.u247 from rfl, totK_node, atot246, atot247]
  decide +kernel

theorem arows257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u257 = true := by
  rw [show D2M8K2.u257 = KTree.node D2M8K2.u255 (nat_lit 426816) (nat_lit 3757128763) (nat_lit 0) D2M8K2.u256 from rfl, allE_node, arows255, irow257, arows256]
  all_goals rfl

theorem atot257 : totK PD2M8K2 D2M8K2.u257 = [0, 409125155986, 1431954055850, 1408239876475, 309377937213, 13184317400, 0, 0] := by
  rw [show D2M8K2.u257 = KTree.node D2M8K2.u255 (nat_lit 426816) (nat_lit 3757128763) (nat_lit 0) D2M8K2.u256 from rfl, totK_node, atot255, atot256]
  decide +kernel

theorem arows260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u260 = true := by
  rw [show D2M8K2.u260 = KTree.node D2M8K2.u258 (nat_lit 429860) (nat_lit 3116490976) (nat_lit 0) D2M8K2.u259 from rfl, allE_node, arows258, irow260, arows259]
  all_goals rfl

theorem atot260 : totK PD2M8K2 D2M8K2.u260 = [0, 432402288569, 1539938824149, 1397347366285, 238747420243, 4980514959, 0, 0] := by
  rw [show D2M8K2.u260 = KTree.node D2M8K2.u258 (nat_lit 429860) (nat_lit 3116490976) (nat_lit 0) D2M8K2.u259 from rfl, totK_node, atot258, atot259]
  decide +kernel

theorem arows264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u264 = true := by
  rw [show D2M8K2.u264 = KTree.node D2M8K2.u262 (nat_lit 457861) (nat_lit 1083933490) (nat_lit 0) D2M8K2.u263 from rfl, allE_node, arows262, irow264, arows263]
  all_goals rfl

theorem atot264 : totK PD2M8K2 D2M8K2.u264 = [0, 429147690622, 1586701525828, 1390244750417, 194139813059, 1369150432, 0, 0] := by
  rw [show D2M8K2.u264 = KTree.node D2M8K2.u262 (nat_lit 457861) (nat_lit 1083933490) (nat_lit 0) D2M8K2.u263 from rfl, totK_node, atot262, atot263]
  decide +kernel

theorem arows267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u267 = true := by
  rw [show D2M8K2.u267 = KTree.node D2M8K2.u265 (nat_lit 462218) (nat_lit 3816671520) (nat_lit 0) D2M8K2.u266 from rfl, allE_node, arows265, irow267, arows266]
  all_goals rfl

theorem atot267 : totK PD2M8K2 D2M8K2.u267 = [0, 459996678000, 1471880511695, 1360212009080, 322408693279, 9575627623, 0, 0] := by
  rw [show D2M8K2.u267 = KTree.node D2M8K2.u265 (nat_lit 462218) (nat_lit 3816671520) (nat_lit 0) D2M8K2.u266 from rfl, totK_node, atot265, atot266]
  decide +kernel

theorem arows272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u272 = true := by
  rw [show D2M8K2.u272 = KTree.node D2M8K2.u270 (nat_lit 465477) (nat_lit 1502937840) (nat_lit 0) D2M8K2.u271 from rfl, allE_node, arows270, irow272, arows271]
  all_goals rfl

theorem atot272 : totK PD2M8K2 D2M8K2.u272 = [0, 439942490466, 1536360873905, 1382015076369, 246290811457, 5138457373, 0, 0] := by
  rw [show D2M8K2.u272 = KTree.node D2M8K2.u270 (nat_lit 465477) (nat_lit 1502937840) (nat_lit 0) D2M8K2.u271 from rfl, totK_node, atot270, atot271]
  decide +kernel

theorem arows275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u275 = true := by
  rw [show D2M8K2.u275 = KTree.node D2M8K2.u273 (nat_lit 469300) (nat_lit 2235010790) (nat_lit 0) D2M8K2.u274 from rfl, allE_node, arows273, irow275, arows274]
  all_goals rfl

theorem atot275 : totK PD2M8K2 D2M8K2.u275 = [0, 415784507467, 1516810207549, 1426554642674, 259242516395, 5193381917, 0, 0] := by
  rw [show D2M8K2.u275 = KTree.node D2M8K2.u273 (nat_lit 469300) (nat_lit 2235010790) (nat_lit 0) D2M8K2.u274 from rfl, totK_node, atot273, atot274]
  decide +kernel

theorem arows279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u279 = true := by
  rw [show D2M8K2.u279 = KTree.node D2M8K2.u277 (nat_lit 475907) (nat_lit 2964435455) (nat_lit 0) D2M8K2.u278 from rfl, allE_node, arows277, irow279, arows278]
  all_goals rfl

theorem atot279 : totK PD2M8K2 D2M8K2.u279 = [179984371288, 603460330885, 1087863052053, 1308565194907, 409633693358, 21897291087, 0, 0] := by
  rw [show D2M8K2.u279 = KTree.node D2M8K2.u277 (nat_lit 475907) (nat_lit 2964435455) (nat_lit 0) D2M8K2.u278 from rfl, totK_node, atot277, atot278]
  decide +kernel

theorem arows282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u282 = true := by
  rw [show D2M8K2.u282 = KTree.node D2M8K2.u280 (nat_lit 997643) (nat_lit 2870286349) (nat_lit 0) D2M8K2.u281 from rfl, allE_node, arows280, irow282, arows281]
  all_goals rfl

theorem atot282 : totK PD2M8K2 D2M8K2.u282 = [457219329262, 1592571261797, 1377286106541, 196201549483, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u282 = KTree.node D2M8K2.u280 (nat_lit 997643) (nat_lit 2870286349) (nat_lit 0) D2M8K2.u281 from rfl, totK_node, atot280, atot281]
  decide +kernel

theorem arows288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u288 = true := by
  rw [show D2M8K2.u288 = KTree.node D2M8K2.u286 (nat_lit 1004552) (nat_lit 3551904898) (nat_lit 0) D2M8K2.u287 from rfl, allE_node, arows286, irow288, arows287]
  all_goals rfl

theorem atot288 : totK PD2M8K2 D2M8K2.u288 = [397391174291, 1452727267913, 1411456376966, 321477792453, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u288 = KTree.node D2M8K2.u286 (nat_lit 1004552) (nat_lit 3551904898) (nat_lit 0) D2M8K2.u287 from rfl, totK_node, atot286, atot287]
  decide +kernel

theorem arows291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u291 = true := by
  rw [show D2M8K2.u291 = KTree.node D2M8K2.u289 (nat_lit 1008620) (nat_lit 3739581627) (nat_lit 0) D2M8K2.u290 from rfl, allE_node, arows289, irow291, arows290]
  all_goals rfl

theorem atot291 : totK PD2M8K2 D2M8K2.u291 = [429914665966, 1445392734430, 1357606465072, 321325489879, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u291 = KTree.node D2M8K2.u289 (nat_lit 1008620) (nat_lit 3739581627) (nat_lit 0) D2M8K2.u290 from rfl, totK_node, atot289, atot290]
  decide +kernel

theorem arows295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u295 = true := by
  rw [show D2M8K2.u295 = KTree.node D2M8K2.u293 (nat_lit 1012045) (nat_lit 1284558185) (nat_lit 0) D2M8K2.u294 from rfl, allE_node, arows293, irow295, arows294]
  all_goals rfl

theorem atot295 : totK PD2M8K2 D2M8K2.u295 = [465002669893, 1537962501394, 1344574967379, 240357176274, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u295 = KTree.node D2M8K2.u293 (nat_lit 1012045) (nat_lit 1284558185) (nat_lit 0) D2M8K2.u294 from rfl, totK_node, atot293, atot294]
  decide +kernel

theorem arows298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u298 = true := by
  rw [show D2M8K2.u298 = KTree.node D2M8K2.u296 (nat_lit 1015296) (nat_lit 3307447155) (nat_lit 0) D2M8K2.u297 from rfl, allE_node, arows296, irow298, arows297]
  all_goals rfl

theorem atot298 : totK PD2M8K2 D2M8K2.u298 = [92230071108, 1004720487119, 1804383431579, 642217963981, 31659692706, 0, 0, 0] := by
  rw [show D2M8K2.u298 = KTree.node D2M8K2.u296 (nat_lit 1015296) (nat_lit 3307447155) (nat_lit 0) D2M8K2.u297 from rfl, totK_node, atot296, atot297]
  decide +kernel

theorem arows303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u303 = true := by
  rw [show D2M8K2.u303 = KTree.node D2M8K2.u301 (nat_lit 1018773) (nat_lit 1531767987) (nat_lit 0) D2M8K2.u302 from rfl, allE_node, arows301, irow303, arows302]
  all_goals rfl

theorem atot303 : totK PD2M8K2 D2M8K2.u303 = [0, 471208966913, 1632535065642, 1245802677694, 168796314558, 1369150432, 0, 0] := by
  rw [show D2M8K2.u303 = KTree.node D2M8K2.u301 (nat_lit 1018773) (nat_lit 1531767987) (nat_lit 0) D2M8K2.u302 from rfl, totK_node, atot301, atot302]
  decide +kernel

theorem arows306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u306 = true := by
  rw [show D2M8K2.u306 = KTree.node D2M8K2.u304 (nat_lit 1027736) (nat_lit 3608901718) (nat_lit 0) D2M8K2.u305 from rfl, allE_node, arows304, irow306, arows305]
  all_goals rfl

theorem atot306 : totK PD2M8K2 D2M8K2.u306 = [0, 734554568322, 1901473002911, 880555489246, 46219101064, 0, 0, 0] := by
  rw [show D2M8K2.u306 = KTree.node D2M8K2.u304 (nat_lit 1027736) (nat_lit 3608901718) (nat_lit 0) D2M8K2.u305 from rfl, totK_node, atot304, atot305]
  decide +kernel

theorem arows310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u310 = true := by
  rw [show D2M8K2.u310 = KTree.node D2M8K2.u308 (nat_lit 1034098) (nat_lit 3934996841) (nat_lit 0) D2M8K2.u309 from rfl, allE_node, arows308, irow310, arows309]
  all_goals rfl

theorem atot310 : totK PD2M8K2 D2M8K2.u310 = [182913464330, 983567295099, 1677180678339, 744925907399, 42120036528, 0, 0, 0] := by
  rw [show D2M8K2.u310 = KTree.node D2M8K2.u308 (nat_lit 1034098) (nat_lit 3934996841) (nat_lit 0) D2M8K2.u309 from rfl, totK_node, atot308, atot309]
  decide +kernel

theorem arows313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u313 = true := by
  rw [show D2M8K2.u313 = KTree.node D2M8K2.u311 (nat_lit 1042541) (nat_lit 2043094069) (nat_lit 0) D2M8K2.u312 from rfl, allE_node, arows311, irow313, arows312]
  all_goals rfl

theorem atot313 : totK PD2M8K2 D2M8K2.u313 = [318672079888, 1198457158664, 1483317924416, 586734059145, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u313 = KTree.node D2M8K2.u311 (nat_lit 1042541) (nat_lit 2043094069) (nat_lit 0) D2M8K2.u312 from rfl, totK_node, atot311, atot312]
  decide +kernel

theorem arows320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u320 = true := by
  rw [show D2M8K2.u320 = KTree.node D2M8K2.u318 (nat_lit 1045327) (nat_lit 2049205014) (nat_lit 0) D2M8K2.u319 from rfl, allE_node, arows318, irow320, arows319]
  all_goals rfl

theorem atot320 : totK PD2M8K2 D2M8K2.u320 = [365703668964, 1423224000573, 1474871982467, 336346849058, 13036865798, 0, 0, 0] := by
  rw [show D2M8K2.u320 = KTree.node D2M8K2.u318 (nat_lit 1045327) (nat_lit 2049205014) (nat_lit 0) D2M8K2.u319 from rfl, totK_node, atot318, atot319]
  decide +kernel

theorem arows323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u323 = true := by
  rw [show D2M8K2.u323 = KTree.node D2M8K2.u321 (nat_lit 1051886) (nat_lit 3845875013) (nat_lit 0) D2M8K2.u322 from rfl, allE_node, arows321, irow323, arows322]
  all_goals rfl

theorem atot323 : totK PD2M8K2 D2M8K2.u323 = [457386464827, 1542993560605, 1355690436805, 244180428985, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u323 = KTree.node D2M8K2.u321 (nat_lit 1051886) (nat_lit 3845875013) (nat_lit 0) D2M8K2.u322 from rfl, totK_node, atot321, atot322]
  decide +kernel

theorem arows327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u327 = true := by
  rw [show D2M8K2.u327 = KTree.node D2M8K2.u325 (nat_lit 1055806) (nat_lit 3907958896) (nat_lit 0) D2M8K2.u326 from rfl, allE_node, arows325, irow327, arows326]
  all_goals rfl

theorem atot327 : totK PD2M8K2 D2M8K2.u327 = [337878552242, 1338358033434, 1491066999306, 436402424130, 21993971087, 0, 0, 0] := by
  rw [show D2M8K2.u327 = KTree.node D2M8K2.u325 (nat_lit 1055806) (nat_lit 3907958896) (nat_lit 0) D2M8K2.u326 from rfl, totK_node, atot325, atot326]
  decide +kernel

theorem arows330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u330 = true := by
  rw [show D2M8K2.u330 = KTree.node D2M8K2.u328 (nat_lit 1062500) (nat_lit 2646363882) (nat_lit 0) D2M8K2.u329 from rfl, allE_node, arows328, irow330, arows329]
  all_goals rfl

theorem atot330 : totK PD2M8K2 D2M8K2.u330 = [0, 409349625867, 1423997563680, 1365990705788, 411909184189, 29044448997, 0, 0] := by
  rw [show D2M8K2.u330 = KTree.node D2M8K2.u328 (nat_lit 1062500) (nat_lit 2646363882) (nat_lit 0) D2M8K2.u329 from rfl, totK_node, atot328, atot329]
  decide +kernel

theorem arows335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u335 = true := by
  rw [show D2M8K2.u335 = KTree.node D2M8K2.u333 (nat_lit 1065276) (nat_lit 2718116028) (nat_lit 0) D2M8K2.u334 from rfl, allE_node, arows333, irow335, arows334]
  all_goals rfl

theorem atot335 : totK PD2M8K2 D2M8K2.u335 = [0, 424393521370, 1451934054814, 1375996616450, 329725901355, 11887334146, 0, 0] := by
  rw [show D2M8K2.u335 = KTree.node D2M8K2.u333 (nat_lit 1065276) (nat_lit 2718116028) (nat_lit 0) D2M8K2.u334 from rfl, totK_node, atot333, atot334]
  decide +kernel

theorem arows338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u338 = true := by
  rw [show D2M8K2.u338 = KTree.node D2M8K2.u336 (nat_lit 1072257) (nat_lit 1826828805) (nat_lit 0) D2M8K2.u337 from rfl, allE_node, arows336, irow338, arows337]
  all_goals rfl

theorem atot338 : totK PD2M8K2 D2M8K2.u338 = [0, 399223950031, 1544207570135, 1445158538034, 203454852226, 1149959346, 0, 0] := by
  rw [show D2M8K2.u338 = KTree.node D2M8K2.u336 (nat_lit 1072257) (nat_lit 1826828805) (nat_lit 0) D2M8K2.u337 from rfl, totK_node, atot336, atot337]
  decide +kernel

theorem arows342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u342 = true := by
  rw [show D2M8K2.u342 = KTree.node D2M8K2.u340 (nat_lit 1076304) (nat_lit 3442830870) (nat_lit 0) D2M8K2.u341 from rfl, allE_node, arows340, irow342, arows341]
  all_goals rfl

theorem atot342 : totK PD2M8K2 D2M8K2.u342 = [0, 404879493941, 1436096179917, 1425318580782, 336408654165, 5037835857, 0, 0] := by
  rw [show D2M8K2.u342 = KTree.node D2M8K2.u340 (nat_lit 1076304) (nat_lit 3442830870) (nat_lit 0) D2M8K2.u341 from rfl, totK_node, atot340, atot341]
  decide +kernel

theorem arows345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u345 = true := by
  rw [show D2M8K2.u345 = KTree.node D2M8K2.u343 (nat_lit 1079785) (nat_lit 1484247146) (nat_lit 0) D2M8K2.u344 from rfl, allE_node, arows343, irow345, arows344]
  all_goals rfl

theorem atot345 : totK PD2M8K2 D2M8K2.u345 = [493992587577, 1595245184139, 1276731287055, 194611069313, 33014910450, 5679676912, 0, 0] := by
  rw [show D2M8K2.u345 = KTree.node D2M8K2.u343 (nat_lit 1079785) (nat_lit 1484247146) (nat_lit 0) D2M8K2.u344 from rfl, totK_node, atot343, atot344]
  decide +kernel

theorem arows351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u351 = true := by
  rw [show D2M8K2.u351 = KTree.node D2M8K2.u349 (nat_lit 1083404) (nat_lit 794713347) (nat_lit 0) D2M8K2.u350 from rfl, allE_node, arows349, irow351, arows350]
  all_goals rfl

theorem atot351 : totK PD2M8K2 D2M8K2.u351 = [330236637064, 1314261400181, 1465614877647, 471862588684, 27794014180, 0, 0, 0] := by
  rw [show D2M8K2.u351 = KTree.node D2M8K2.u349 (nat_lit 1083404) (nat_lit 794713347) (nat_lit 0) D2M8K2.u350 from rfl, totK_node, atot349, atot350]
  decide +kernel

theorem arows354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u354 = true := by
  rw [show D2M8K2.u354 = KTree.node D2M8K2.u352 (nat_lit 1086444) (nat_lit 3167458472) (nat_lit 0) D2M8K2.u353 from rfl, allE_node, arows352, irow354, arows353]
  all_goals rfl

theorem atot354 : totK PD2M8K2 D2M8K2.u354 = [445903821987, 1465974547284, 1370271808874, 343286359566, 16266890063, 0, 0, 0] := by
  rw [show D2M8K2.u354 = KTree.node D2M8K2.u352 (nat_lit 1086444) (nat_lit 3167458472) (nat_lit 0) D2M8K2.u353 from rfl, totK_node, atot352, atot353]
  decide +kernel

theorem arows358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u358 = true := by
  rw [show D2M8K2.u358 = KTree.node D2M8K2.u356 (nat_lit 1092925) (nat_lit 990243075) (nat_lit 0) D2M8K2.u357 from rfl, allE_node, arows356, irow358, arows357]
  all_goals rfl

theorem atot358 : totK PD2M8K2 D2M8K2.u358 = [416136598563, 1505661964876, 1405605027918, 243726888884, 4558519234, 0, 0, 0] := by
  rw [show D2M8K2.u358 = KTree.node D2M8K2.u356 (nat_lit 1092925) (nat_lit 990243075) (nat_lit 0) D2M8K2.u357 from rfl, totK_node, atot356, atot357]
  decide +kernel

theorem arows361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u361 = true := by
  rw [show D2M8K2.u361 = KTree.node D2M8K2.u359 (nat_lit 1096438) (nat_lit 3511211972) (nat_lit 0) D2M8K2.u360 from rfl, allE_node, arows359, irow361, arows360]
  all_goals rfl

theorem atot361 : totK PD2M8K2 D2M8K2.u361 = [420826860807, 1438886426691, 1405651714410, 323356494411, 8852005872, 0, 0, 0] := by
  rw [show D2M8K2.u361 = KTree.node D2M8K2.u359 (nat_lit 1096438) (nat_lit 3511211972) (nat_lit 0) D2M8K2.u360 from rfl, totK_node, atot359, atot360]
  decide +kernel

theorem arows366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u366 = true := by
  rw [show D2M8K2.u366 = KTree.node D2M8K2.u364 (nat_lit 1100003) (nat_lit 2944114254) (nat_lit 0) D2M8K2.u365 from rfl, allE_node, arows364, irow366, arows365]
  all_goals rfl

theorem atot366 : totK PD2M8K2 D2M8K2.u366 = [0, 574063088075, 1716501478680, 1103119206683, 118194072138, 1206465782, 0, 0] := by
  rw [show D2M8K2.u366 = KTree.node D2M8K2.u364 (nat_lit 1100003) (nat_lit 2944114254) (nat_lit 0) D2M8K2.u365 from rfl, totK_node, atot364, atot365]
  decide +kernel

theorem arows369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u369 = true := by
  rw [show D2M8K2.u369 = KTree.node D2M8K2.u367 (nat_lit 1103789) (nat_lit 2018643398) (nat_lit 0) D2M8K2.u368 from rfl, allE_node, arows367, irow369, arows368]
  all_goals rfl

theorem atot369 : totK PD2M8K2 D2M8K2.u369 = [0, 673091531341, 1821770599373, 1043244559736, 84207719712, 0, 0, 0] := by
  rw [show D2M8K2.u369 = KTree.node D2M8K2.u367 (nat_lit 1103789) (nat_lit 2018643398) (nat_lit 0) D2M8K2.u368 from rfl, totK_node, atot367, atot368]
  decide +kernel

theorem arows373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u373 = true := by
  rw [show D2M8K2.u373 = KTree.node D2M8K2.u371 (nat_lit 1108394) (nat_lit 3963281488) (nat_lit 0) D2M8K2.u372 from rfl, allE_node, arows371, irow373, arows372]
  all_goals rfl

theorem atot373 : totK PD2M8K2 D2M8K2.u373 = [0, 433337352045, 1470688020203, 1324359062659, 297291353786, 13016197374, 0, 0] := by
  rw [show D2M8K2.u373 = KTree.node D2M8K2.u371 (nat_lit 1108394) (nat_lit 3963281488) (nat_lit 0) D2M8K2.u372 from rfl, totK_node, atot371, atot372]
  decide +kernel

theorem arows376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u376 = true := by
  rw [show D2M8K2.u376 = KTree.node D2M8K2.u374 (nat_lit 1115457) (nat_lit 1520505334) (nat_lit 0) D2M8K2.u375 from rfl, allE_node, arows374, irow376, arows375]
  all_goals rfl

theorem atot376 : totK PD2M8K2 D2M8K2.u376 = [0, 432134523028, 1568172496527, 1287807110056, 191321726306, 4574395652, 0, 0] := by
  rw [show D2M8K2.u376 = KTree.node D2M8K2.u374 (nat_lit 1115457) (nat_lit 1520505334) (nat_lit 0) D2M8K2.u375 from rfl, totK_node, atot374, atot375]
  decide +kernel

theorem arows384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u384 = true := by
  rw [show D2M8K2.u384 = KTree.node D2M8K2.u382 (nat_lit 1162207) (nat_lit 2321058057) (nat_lit 0) D2M8K2.u383 from rfl, allE_node, arows382, irow384, arows383]
  all_goals rfl

theorem atot384 : totK PD2M8K2 D2M8K2.u384 = [409603254599, 1426334106199, 1362589916516, 364832314869, 18818157577, 0, 0, 0] := by
  rw [show D2M8K2.u384 = KTree.node D2M8K2.u382 (nat_lit 1162207) (nat_lit 2321058057) (nat_lit 0) D2M8K2.u383 from rfl, totK_node, atot382, atot383]
  decide +kernel

theorem arows387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u387 = true := by
  rw [show D2M8K2.u387 = KTree.node D2M8K2.u385 (nat_lit 1165865) (nat_lit 1803274704) (nat_lit 0) D2M8K2.u386 from rfl, allE_node, arows385, irow387, arows386]
  all_goals rfl

theorem atot387 : totK PD2M8K2 D2M8K2.u387 = [386187293179, 1398547385791, 1420946637314, 395323485050, 25278154240, 0, 0, 0] := by
  rw [show D2M8K2.u387 = KTree.node D2M8K2.u385 (nat_lit 1165865) (nat_lit 1803274704) (nat_lit 0) D2M8K2.u386 from rfl, totK_node, atot385, atot386]
  decide +kernel

theorem arows391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u391 = true := by
  rw [show D2M8K2.u391 = KTree.node D2M8K2.u389 (nat_lit 1168820) (nat_lit 3664909440) (nat_lit 0) D2M8K2.u390 from rfl, allE_node, arows389, irow391, arows390]
  all_goals rfl

theorem atot391 : totK PD2M8K2 D2M8K2.u391 = [423686589494, 1451046528943, 1374975122580, 338930938190, 12158044496, 0, 0, 0] := by
  rw [show D2M8K2.u391 = KTree.node D2M8K2.u389 (nat_lit 1168820) (nat_lit 3664909440) (nat_lit 0) D2M8K2.u390 from rfl, totK_node, atot389, atot390]
  decide +kernel

theorem arows394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u394 = true := by
  rw [show D2M8K2.u394 = KTree.node D2M8K2.u392 (nat_lit 1172544) (nat_lit 3507538042) (nat_lit 0) D2M8K2.u393 from rfl, allE_node, arows392, irow394, arows393]
  all_goals rfl

theorem atot394 : totK PD2M8K2 D2M8K2.u394 = [326404507212, 1313108007426, 1489761725526, 422197123099, 21554143046, 0, 0, 0] := by
  rw [show D2M8K2.u394 = KTree.node D2M8K2.u392 (nat_lit 1172544) (nat_lit 3507538042) (nat_lit 0) D2M8K2.u393 from rfl, totK_node, atot392, atot393]
  decide +kernel

theorem arows399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u399 = true := by
  rw [show D2M8K2.u399 = KTree.node D2M8K2.u397 (nat_lit 1176037) (nat_lit 1252885204) (nat_lit 0) D2M8K2.u398 from rfl, allE_node, arows397, irow399, arows398]
  all_goals rfl

theorem atot399 : totK PD2M8K2 D2M8K2.u399 = [435809923056, 1540752694101, 1390934359146, 236295732923, 4678454933, 0, 0, 0] := by
  rw [show D2M8K2.u399 = KTree.node D2M8K2.u397 (nat_lit 1176037) (nat_lit 1252885204) (nat_lit 0) D2M8K2.u398 from rfl, totK_node, atot397, atot398]
  decide +kernel

theorem arows402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u402 = true := by
  rw [show D2M8K2.u402 = KTree.node D2M8K2.u400 (nat_lit 1183261) (nat_lit 1081283312) (nat_lit 0) D2M8K2.u401 from rfl, allE_node, arows400, irow402, arows401]
  all_goals rfl

theorem atot402 : totK PD2M8K2 D2M8K2.u402 = [0, 538735095109, 1732476482204, 1119391765009, 114991860159, 1138244013, 0, 0] := by
  rw [show D2M8K2.u402 = KTree.node D2M8K2.u400 (nat_lit 1183261) (nat_lit 1081283312) (nat_lit 0) D2M8K2.u401 from rfl, totK_node, atot400, atot401]
  decide +kernel

theorem arows406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u406 = true := by
  rw [show D2M8K2.u406 = KTree.node D2M8K2.u404 (nat_lit 1188960) (nat_lit 3592768262) (nat_lit 0) D2M8K2.u405 from rfl, allE_node, arows404, irow406, arows405]
  all_goals rfl

theorem atot406 : totK PD2M8K2 D2M8K2.u406 = [0, 716560332602, 1854546193600, 954510510982, 69453191850, 0, 0, 0] := by
  rw [show D2M8K2.u406 = KTree.node D2M8K2.u404 (nat_lit 1188960) (nat_lit 3592768262) (nat_lit 0) D2M8K2.u405 from rfl, totK_node, atot404, atot405]
  decide +kernel

theorem arows409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u409 = true := by
  rw [show D2M8K2.u409 = KTree.node D2M8K2.u407 (nat_lit 1195858) (nat_lit 3065158769) (nat_lit 0) D2M8K2.u408 from rfl, allE_node, arows407, irow409, arows408]
  all_goals rfl

theorem atot409 : totK PD2M8K2 D2M8K2.u409 = [0, 750748424566, 1866661273144, 904947884139, 58689007543, 0, 0, 0] := by
  rw [show D2M8K2.u409 = KTree.node D2M8K2.u407 (nat_lit 1195858) (nat_lit 3065158769) (nat_lit 0) D2M8K2.u408 from rfl, totK_node, atot407, atot408]
  decide +kernel

theorem arows415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u415 = true := by
  rw [show D2M8K2.u415 = KTree.node D2M8K2.u413 (nat_lit 1202797) (nat_lit 1134544092) (nat_lit 0) D2M8K2.u414 from rfl, allE_node, arows413, irow415, arows414]
  all_goals rfl

theorem atot415 : totK PD2M8K2 D2M8K2.u415 = [410905367637, 1041006034210, 1034729505849, 850025222845, 192215148162, 4977114383, 0, 0] := by
  rw [show D2M8K2.u415 = KTree.node D2M8K2.u413 (nat_lit 1202797) (nat_lit 1134544092) (nat_lit 0) D2M8K2.u414 from rfl, totK_node, atot413, atot414]
  decide +kernel

theorem arows418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u418 = true := by
  rw [show D2M8K2.u418 = KTree.node D2M8K2.u416 (nat_lit 1206714) (nat_lit 3553682206) (nat_lit 0) D2M8K2.u417 from rfl, allE_node, arows416, irow418, arows417]
  all_goals rfl

theorem atot418 : totK PD2M8K2 D2M8K2.u418 = [388275877044, 1514932257551, 1480520014110, 258130437464, 11812634922, 0, 0, 0] := by
  rw [show D2M8K2.u418 = KTree.node D2M8K2.u416 (nat_lit 1206714) (nat_lit 3553682206) (nat_lit 0) D2M8K2.u417 from rfl, totK_node, atot416, atot417]
  decide +kernel

theorem arows422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u422 = true := by
  rw [show D2M8K2.u422 = KTree.node D2M8K2.u420 (nat_lit 1209732) (nat_lit 3296745973) (nat_lit 0) D2M8K2.u421 from rfl, allE_node, arows420, irow422, arows421]
  all_goals rfl

theorem atot422 : totK PD2M8K2 D2M8K2.u422 = [424503916002, 1345912087631, 1336002446368, 484796816164, 25831995884, 0, 0, 0] := by
  rw [show D2M8K2.u422 = KTree.node D2M8K2.u420 (nat_lit 1209732) (nat_lit 3296745973) (nat_lit 0) D2M8K2.u421 from rfl, totK_node, atot420, atot421]
  decide +kernel

theorem arows425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u425 = true := by
  rw [show D2M8K2.u425 = KTree.node D2M8K2.u423 (nat_lit 1213112) (nat_lit 2549676762) (nat_lit 0) D2M8K2.u424 from rfl, allE_node, arows423, irow425, arows424]
  all_goals rfl

theorem atot425 : totK PD2M8K2 D2M8K2.u425 = [329310474659, 1383974013841, 1534026834638, 352233660934, 13043783340, 0, 0, 0] := by
  rw [show D2M8K2.u425 = KTree.node D2M8K2.u423 (nat_lit 1213112) (nat_lit 2549676762) (nat_lit 0) D2M8K2.u424 from rfl, totK_node, atot423, atot424]
  decide +kernel

theorem arows430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u430 = true := by
  rw [show D2M8K2.u430 = KTree.node D2M8K2.u428 (nat_lit 1220484) (nat_lit 1352334799) (nat_lit 0) D2M8K2.u429 from rfl, allE_node, arows428, irow430, arows429]
  all_goals rfl

theorem atot430 : totK PD2M8K2 D2M8K2.u430 = [440265286504, 1461213943061, 1390286329301, 323828904335, 10918999833, 0, 0, 0] := by
  rw [show D2M8K2.u430 = KTree.node D2M8K2.u428 (nat_lit 1220484) (nat_lit 1352334799) (nat_lit 0) D2M8K2.u429 from rfl, totK_node, atot428, atot429]
  decide +kernel

theorem arows433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u433 = true := by
  rw [show D2M8K2.u433 = KTree.node D2M8K2.u431 (nat_lit 1223581) (nat_lit 1369820453) (nat_lit 0) D2M8K2.u432 from rfl, allE_node, arows431, irow433, arows432]
  all_goals rfl

theorem atot433 : totK PD2M8K2 D2M8K2.u433 = [0, 761092648685, 1893393285985, 874888361936, 48905478834, 0, 0, 0] := by
  rw [show D2M8K2.u433 = KTree.node D2M8K2.u431 (nat_lit 1223581) (nat_lit 1369820453) (nat_lit 0) D2M8K2.u432 from rfl, totK_node, atot431, atot432]
  decide +kernel

theorem arows437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u437 = true := by
  rw [show D2M8K2.u437 = KTree.node D2M8K2.u435 (nat_lit 1227576) (nat_lit 3212538818) (nat_lit 0) D2M8K2.u436 from rfl, allE_node, arows435, irow437, arows436]
  all_goals rfl

theorem atot437 : totK PD2M8K2 D2M8K2.u437 = [0, 523307843145, 1642134912897, 1288717866003, 154503873489, 1310285577, 0, 0] := by
  rw [show D2M8K2.u437 = KTree.node D2M8K2.u435 (nat_lit 1227576) (nat_lit 3212538818) (nat_lit 0) D2M8K2.u436 from rfl, totK_node, atot435, atot436]
  decide +kernel

theorem arows440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u440 = true := by
  rw [show D2M8K2.u440 = KTree.node D2M8K2.u438 (nat_lit 1232200) (nat_lit 3554022579) (nat_lit 0) D2M8K2.u439 from rfl, allE_node, arows438, irow440, arows439]
  all_goals rfl

theorem atot440 : totK PD2M8K2 D2M8K2.u440 = [0, 438397061032, 1546254440694, 1353627657509, 223905236632, 4879840392, 0, 0] := by
  rw [show D2M8K2.u440 = KTree.node D2M8K2.u438 (nat_lit 1232200) (nat_lit 3554022579) (nat_lit 0) D2M8K2.u439 from rfl, totK_node, atot438, atot439]
  decide +kernel

theorem arows447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u447 = true := by
  rw [show D2M8K2.u447 = KTree.node D2M8K2.u445 (nat_lit 1236563) (nat_lit 1820634234) (nat_lit 0) D2M8K2.u446 from rfl, allE_node, arows445, irow447, arows446]
  all_goals rfl

theorem atot447 : totK PD2M8K2 D2M8K2.u447 = [0, 502405621143, 1568416527786, 1306963669523, 219936942989, 4931404646, 0, 0] := by
  rw [show D2M8K2.u447 = KTree.node D2M8K2.u445 (nat_lit 1236563) (nat_lit 1820634234) (nat_lit 0) D2M8K2.u446 from rfl, totK_node, atot445, atot446]
  decide +kernel

theorem arows450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u450 = true := by
  rw [show D2M8K2.u450 = KTree.node D2M8K2.u448 (nat_lit 1243369) (nat_lit 1470595831) (nat_lit 0) D2M8K2.u449 from rfl, allE_node, arows448, irow450, arows449]
  all_goals rfl

theorem atot450 : totK PD2M8K2 D2M8K2.u450 = [0, 375775229289, 1360967828668, 1409541791477, 398488637485, 21751168066, 0, 0] := by
  rw [show D2M8K2.u450 = KTree.node D2M8K2.u448 (nat_lit 1243369) (nat_lit 1470595831) (nat_lit 0) D2M8K2.u449 from rfl, totK_node, atot448, atot449]
  decide +kernel

theorem arows454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u454 = true := by
  rw [show D2M8K2.u454 = KTree.node D2M8K2.u452 (nat_lit 1246836) (nat_lit 3244651262) (nat_lit 0) D2M8K2.u453 from rfl, allE_node, arows452, irow454, arows453]
  all_goals rfl

theorem atot454 : totK PD2M8K2 D2M8K2.u454 = [0, 425610091249, 1602196856256, 1393740494559, 188937997247, 1369150432, 0, 0] := by
  rw [show D2M8K2.u454 = KTree.node D2M8K2.u452 (nat_lit 1246836) (nat_lit 3244651262) (nat_lit 0) D2M8K2.u453 from rfl, totK_node, atot452, atot453]
  decide +kernel

theorem arows457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u457 = true := by
  rw [show D2M8K2.u457 = KTree.node D2M8K2.u455 (nat_lit 1253582) (nat_lit 2990198638) (nat_lit 0) D2M8K2.u456 from rfl, allE_node, arows455, irow457, arows456]
  all_goals rfl

theorem atot457 : totK PD2M8K2 D2M8K2.u457 = [0, 429448059518, 1459693422507, 1361435864609, 306626366918, 13049727234, 0, 0] := by
  rw [show D2M8K2.u457 = KTree.node D2M8K2.u455 (nat_lit 1253582) (nat_lit 2990198638) (nat_lit 0) D2M8K2.u456 from rfl, totK_node, atot455, atot456]
  decide +kernel

theorem arows462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u462 = true := by
  rw [show D2M8K2.u462 = KTree.node D2M8K2.u460 (nat_lit 1258108) (nat_lit 3660524743) (nat_lit 0) D2M8K2.u461 from rfl, allE_node, arows460, irow462, arows461]
  all_goals rfl

theorem atot462 : totK PD2M8K2 D2M8K2.u462 = [0, 492525803220, 1653875588867, 1273294805111, 152061137515, 1198073392, 0, 0] := by
  rw [show D2M8K2.u462 = KTree.node D2M8K2.u460 (nat_lit 1258108) (nat_lit 3660524743) (nat_lit 0) D2M8K2.u461 from rfl, totK_node, atot460, atot461]
  decide +kernel

theorem arows465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u465 = true := by
  rw [show D2M8K2.u465 = KTree.node D2M8K2.u463 (nat_lit 1261755) (nat_lit 3776555214) (nat_lit 0) D2M8K2.u464 from rfl, allE_node, arows463, irow465, arows464]
  all_goals rfl

theorem atot465 : totK PD2M8K2 D2M8K2.u465 = [0, 414406933978, 1518738557968, 1426690098913, 230153953149, 4917269347, 0, 0] := by
  rw [show D2M8K2.u465 = KTree.node D2M8K2.u463 (nat_lit 1261755) (nat_lit 3776555214) (nat_lit 0) D2M8K2.u464 from rfl, totK_node, atot463, atot464]
  decide +kernel

theorem arows469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u469 = true := by
  rw [show D2M8K2.u469 = KTree.node D2M8K2.u467 (nat_lit 1265090) (nat_lit 3032877523) (nat_lit 0) D2M8K2.u468 from rfl, allE_node, arows467, irow469, arows468]
  all_goals rfl

theorem atot469 : totK PD2M8K2 D2M8K2.u469 = [0, 0, 786934303224, 1929648402219, 769885925972, 39628514104, 0, 0] := by
  rw [show D2M8K2.u469 = KTree.node D2M8K2.u467 (nat_lit 1265090) (nat_lit 3032877523) (nat_lit 0) D2M8K2.u468 from rfl, totK_node, atot467, atot468]
  decide +kernel

theorem arows472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u472 = true := by
  rw [show D2M8K2.u472 = KTree.node D2M8K2.u470 (nat_lit 1272388) (nat_lit 3869846782) (nat_lit 0) D2M8K2.u471 from rfl, allE_node, arows470, irow472, arows471]
  all_goals rfl

theorem atot472 : totK PD2M8K2 D2M8K2.u472 = [0, 0, 558589438818, 1727519246577, 1069735222482, 117992194302, 1275377855, 0] := by
  rw [show D2M8K2.u472 = KTree.node D2M8K2.u470 (nat_lit 1272388) (nat_lit 3869846782) (nat_lit 0) D2M8K2.u471 from rfl, totK_node, atot470, atot471]
  decide +kernel

theorem arows478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u478 = true := by
  rw [show D2M8K2.u478 = KTree.node D2M8K2.u476 (nat_lit 1279584) (nat_lit 3690063848) (nat_lit 0) D2M8K2.u477 from rfl, allE_node, arows476, irow478, arows477]
  all_goals rfl

theorem atot478 : totK PD2M8K2 D2M8K2.u478 = [0, 0, 866960882754, 1954894648553, 671784180817, 22303192375, 0, 0] := by
  rw [show D2M8K2.u478 = KTree.node D2M8K2.u476 (nat_lit 1279584) (nat_lit 3690063848) (nat_lit 0) D2M8K2.u477 from rfl, totK_node, atot476, atot477]
  decide +kernel

theorem arows481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u481 = true := by
  rw [show D2M8K2.u481 = KTree.node D2M8K2.u479 (nat_lit 1290180) (nat_lit 2592731250) (nat_lit 0) D2M8K2.u480 from rfl, allE_node, arows479, irow481, arows480]
  all_goals rfl

theorem atot481 : totK PD2M8K2 D2M8K2.u481 = [0, 430077321765, 1438706312085, 1361890377195, 408908362904, 32026229172, 0, 0] := by
  rw [show D2M8K2.u481 = KTree.node D2M8K2.u479 (nat_lit 1290180) (nat_lit 2592731250) (nat_lit 0) D2M8K2.u480 from rfl, totK_node, atot479, atot480]
  decide +kernel

theorem arows485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u485 = true := by
  rw [show D2M8K2.u485 = KTree.node D2M8K2.u483 (nat_lit 1292966) (nat_lit 4041768059) (nat_lit 0) D2M8K2.u484 from rfl, allE_node, arows483, irow485, arows484]
  all_goals rfl

theorem atot485 : totK PD2M8K2 D2M8K2.u485 = [0, 425114237593, 1424907083141, 1362293881469, 383057859200, 13238194675, 0, 0] := by
  rw [show D2M8K2.u485 = KTree.node D2M8K2.u483 (nat_lit 1292966) (nat_lit 4041768059) (nat_lit 0) D2M8K2.u484 from rfl, totK_node, atot483, atot484]
  decide +kernel

theorem arows488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u488 = true := by
  rw [show D2M8K2.u488 = KTree.node D2M8K2.u486 (nat_lit 1299875) (nat_lit 2884199461) (nat_lit 0) D2M8K2.u487 from rfl, allE_node, arows486, irow488, arows487]
  all_goals rfl

theorem atot488 : totK PD2M8K2 D2M8K2.u488 = [0, 399283816670, 1474558825460, 1414278047278, 297806428998, 11873025674, 0, 0] := by
  rw [show D2M8K2.u488 = KTree.node D2M8K2.u486 (nat_lit 1299875) (nat_lit 2884199461) (nat_lit 0) D2M8K2.u487 from rfl, totK_node, atot486, atot487]
  decide +kernel

theorem arows493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u493 = true := by
  rw [show D2M8K2.u493 = KTree.node D2M8K2.u491 (nat_lit 1303536) (nat_lit 3466624776) (nat_lit 0) D2M8K2.u492 from rfl, allE_node, arows491, irow493, arows492]
  all_goals rfl

theorem atot493 : totK PD2M8K2 D2M8K2.u493 = [0, 405438044637, 1504448217598, 1454770951562, 269986213739, 5112235778, 0, 0] := by
  rw [show D2M8K2.u493 = KTree.node D2M8K2.u491 (nat_lit 1303536) (nat_lit 3466624776) (nat_lit 0) D2M8K2.u492 from rfl, totK_node, atot491, atot492]
  decide +kernel

theorem arows496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u496 = true := by
  rw [show D2M8K2.u496 = KTree.node D2M8K2.u494 (nat_lit 1327874) (nat_lit 3845682763) (nat_lit 0) D2M8K2.u495 from rfl, allE_node, arows494, irow496, arows495]
  all_goals rfl

theorem atot496 : totK PD2M8K2 D2M8K2.u496 = [0, 416183864361, 1407077617956, 1344768223742, 369300781416, 17894111944, 0, 0] := by
  rw [show D2M8K2.u496 = KTree.node D2M8K2.u494 (nat_lit 1327874) (nat_lit 3845682763) (nat_lit 0) D2M8K2.u495 from rfl, totK_node, atot494, atot495]
  decide +kernel

theorem arows500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u500 = true := by
  rw [show D2M8K2.u500 = KTree.node D2M8K2.u498 (nat_lit 1331544) (nat_lit 2709683275) (nat_lit 0) D2M8K2.u499 from rfl, allE_node, arows498, irow500, arows499]
  all_goals rfl

theorem atot500 : totK PD2M8K2 D2M8K2.u500 = [0, 405971615009, 1499046474772, 1429218111593, 283978332448, 14593677817, 0, 0] := by
  rw [show D2M8K2.u500 = KTree.node D2M8K2.u498 (nat_lit 1331544) (nat_lit 2709683275) (nat_lit 0) D2M8K2.u499 from rfl, totK_node, atot498, atot499]
  decide +kernel

theorem arows503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u503 = true := by
  rw [show D2M8K2.u503 = KTree.node D2M8K2.u501 (nat_lit 1334527) (nat_lit 1092260603) (nat_lit 0) D2M8K2.u502 from rfl, allE_node, arows501, irow503, arows502]
  all_goals rfl

theorem atot503 : totK PD2M8K2 D2M8K2.u503 = [0, 445333500882, 1447798856961, 1352150148127, 347268830352, 10659566080, 0, 0] := by
  rw [show D2M8K2.u503 = KTree.node D2M8K2.u501 (nat_lit 1334527) (nat_lit 1092260603) (nat_lit 0) D2M8K2.u502 from rfl, totK_node, atot501, atot502]
  decide +kernel

theorem arows513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u513 = true := by
  rw [show D2M8K2.u513 = KTree.node D2M8K2.u511 (nat_lit 1341277) (nat_lit 1086159196) (nat_lit 0) D2M8K2.u512 from rfl, allE_node, arows511, irow513, arows512]
  all_goals rfl

theorem atot513 : totK PD2M8K2 D2M8K2.u513 = [0, 414552745396, 1493753976641, 1375647321496, 282995273265, 11885407614, 0, 0] := by
  rw [show D2M8K2.u513 = KTree.node D2M8K2.u511 (nat_lit 1341277) (nat_lit 1086159196) (nat_lit 0) D2M8K2.u512 from rfl, totK_node, atot511, atot512]
  decide +kernel

theorem arows516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u516 = true := by
  rw [show D2M8K2.u516 = KTree.node D2M8K2.u514 (nat_lit 1344803) (nat_lit 2970155676) (nat_lit 0) D2M8K2.u515 from rfl, allE_node, arows514, irow516, arows515]
  all_goals rfl

theorem atot516 : totK PD2M8K2 D2M8K2.u516 = [0, 420032133219, 1488848935351, 1418876132045, 252958716048, 6086930351, 0, 0] := by
  rw [show D2M8K2.u516 = KTree.node D2M8K2.u514 (nat_lit 1344803) (nat_lit 2970155676) (nat_lit 0) D2M8K2.u515 from rfl, totK_node, atot514, atot515]
  decide +kernel

theorem arows520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u520 = true := by
  rw [show D2M8K2.u520 = KTree.node D2M8K2.u518 (nat_lit 1348426) (nat_lit 3897365607) (nat_lit 0) D2M8K2.u519 from rfl, allE_node, arows518, irow520, arows519]
  all_goals rfl

theorem atot520 : totK PD2M8K2 D2M8K2.u520 = [0, 0, 743874719164, 1857145467582, 828807519798, 65492310997, 1206465782, 0] := by
  rw [show D2M8K2.u520 = KTree.node D2M8K2.u518 (nat_lit 1348426) (nat_lit 3897365607) (nat_lit 0) D2M8K2.u519 from rfl, totK_node, atot518, atot519]
  decide +kernel

theorem arows523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u523 = true := by
  rw [show D2M8K2.u523 = KTree.node D2M8K2.u521 (nat_lit 1352199) (nat_lit 3629924412) (nat_lit 0) D2M8K2.u522 from rfl, allE_node, arows521, irow523, arows522]
  all_goals rfl

theorem atot523 : totK PD2M8K2 D2M8K2.u523 = [0, 0, 600326223739, 1749245586035, 1090853806254, 110534108940, 0, 0] := by
  rw [show D2M8K2.u523 = KTree.node D2M8K2.u521 (nat_lit 1352199) (nat_lit 3629924412) (nat_lit 0) D2M8K2.u522 from rfl, totK_node, atot521, atot522]
  decide +kernel

theorem arows528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u528 = true := by
  rw [show D2M8K2.u528 = KTree.node D2M8K2.u526 (nat_lit 1356904) (nat_lit 3705233496) (nat_lit 0) D2M8K2.u527 from rfl, allE_node, arows526, irow528, arows527]
  all_goals rfl

theorem atot528 : totK PD2M8K2 D2M8K2.u528 = [0, 0, 404758313021, 1458800924848, 1317202790916, 300725806751, 13016197374, 0] := by
  rw [show D2M8K2.u528 = KTree.node D2M8K2.u526 (nat_lit 1356904) (nat_lit 3705233496) (nat_lit 0) D2M8K2.u527 from rfl, totK_node, atot526, atot527]
  decide +kernel

theorem arows531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u531 = true := by
  rw [show D2M8K2.u531 = KTree.node D2M8K2.u529 (nat_lit 1363981) (nat_lit 1248264691) (nat_lit 0) D2M8K2.u530 from rfl, allE_node, arows529, irow531, arows530]
  all_goals rfl

theorem atot531 : totK PD2M8K2 D2M8K2.u531 = [0, 0, 499990209038, 1603811747078, 1154117077234, 175950657496, 4574395652, 0] := by
  rw [show D2M8K2.u531 = KTree.node D2M8K2.u529 (nat_lit 1363981) (nat_lit 1248264691) (nat_lit 0) D2M8K2.u530 from rfl, totK_node, atot529, atot530]
  decide +kernel

theorem arows535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u535 = true := by
  rw [show D2M8K2.u535 = KTree.node D2M8K2.u533 (nat_lit 1411039) (nat_lit 2321058057) (nat_lit 0) D2M8K2.u534 from rfl, allE_node, arows533, irow535, arows534]
  all_goals rfl

theorem atot535 : totK PD2M8K2 D2M8K2.u535 = [0, 408370364658, 1449674754095, 1351067361586, 332041870521, 14690319815, 0, 0] := by
  rw [show D2M8K2.u535 = KTree.node D2M8K2.u533 (nat_lit 1411039) (nat_lit 2321058057) (nat_lit 0) D2M8K2.u534 from rfl, totK_node, atot533, atot534]
  decide +kernel

theorem arows538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u538 = true := by
  rw [show D2M8K2.u538 = KTree.node D2M8K2.u536 (nat_lit 1414725) (nat_lit 1511955985) (nat_lit 0) D2M8K2.u537 from rfl, allE_node, arows536, irow538, arows537]
  all_goals rfl

theorem atot538 : totK PD2M8K2 D2M8K2.u538 = [0, 385752772852, 1458842989340, 1446664852787, 333892266762, 13604428459, 0, 0] := by
  rw [show D2M8K2.u538 = KTree.node D2M8K2.u536 (nat_lit 1414725) (nat_lit 1511955985) (nat_lit 0) D2M8K2.u537 from rfl, totK_node, atot536, atot537]
  decide +kernel

theorem arows544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u544 = true := by
  rw [show D2M8K2.u544 = KTree.node D2M8K2.u542 (nat_lit 1418180) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u543 from rfl, allE_node, arows542, irow544, arows543]
  all_goals rfl

theorem atot544 : totK PD2M8K2 D2M8K2.u544 = [0, 422504983006, 1447937629237, 1391098376531, 321384110814, 10997273917, 0, 0] := by
  rw [show D2M8K2.u544 = KTree.node D2M8K2.u542 (nat_lit 1418180) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u543 from rfl, totK_node, atot542, atot543]
  decide +kernel

theorem arows547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u547 = true := by
  rw [show D2M8K2.u547 = KTree.node D2M8K2.u545 (nat_lit 1421649) (nat_lit 1862972224) (nat_lit 0) D2M8K2.u546 from rfl, allE_node, arows545, irow547, arows546]
  all_goals rfl

theorem atot547 : totK PD2M8K2 D2M8K2.u547 = [0, 415349069906, 1473566736318, 1392252282022, 271254534935, 8148162562, 0, 0] := by
  rw [show D2M8K2.u547 = KTree.node D2M8K2.u545 (nat_lit 1421649) (nat_lit 1862972224) (nat_lit 0) D2M8K2.u546 from rfl, totK_node, atot545, atot546]
  decide +kernel

theorem arows551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u551 = true := by
  rw [show D2M8K2.u551 = KTree.node D2M8K2.u549 (nat_lit 1425622) (nat_lit 2986205858) (nat_lit 0) D2M8K2.u550 from rfl, allE_node, arows549, irow551, arows550]
  all_goals rfl

theorem atot551 : totK PD2M8K2 D2M8K2.u551 = [0, 345466061500, 1408231216948, 1523523784548, 312108801142, 6350335412, 0, 0] := by
  rw [show D2M8K2.u551 = KTree.node D2M8K2.u549 (nat_lit 1425622) (nat_lit 2986205858) (nat_lit 0) D2M8K2.u550 from rfl, totK_node, atot549, atot550]
  decide +kernel

theorem arows554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u554 = true := by
  rw [show D2M8K2.u554 = KTree.node D2M8K2.u552 (nat_lit 1432752) (nat_lit 3479690153) (nat_lit 0) D2M8K2.u553 from rfl, allE_node, arows552, irow554, arows553]
  all_goals rfl

theorem atot554 : totK PD2M8K2 D2M8K2.u554 = [0, 0, 586085064915, 1744713591636, 1036612034809, 97864834908, 1103454931, 0] := by
  rw [show D2M8K2.u554 = KTree.node D2M8K2.u552 (nat_lit 1432752) (nat_lit 3479690153) (nat_lit 0) D2M8K2.u553 from rfl, totK_node, atot552, atot553]
  decide +kernel

theorem arows559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u559 = true := by
  rw [show D2M8K2.u559 = KTree.node D2M8K2.u557 (nat_lit 1438880) (nat_lit 3817391977) (nat_lit 0) D2M8K2.u558 from rfl, allE_node, arows557, irow559, arows558]
  all_goals rfl

theorem atot559 : totK PD2M8K2 D2M8K2.u559 = [0, 0, 851029745140, 1938861743280, 722761759186, 31002816328, 0, 0] := by
  rw [show D2M8K2.u559 = KTree.node D2M8K2.u557 (nat_lit 1438880) (nat_lit 3817391977) (nat_lit 0) D2M8K2.u558 from rfl, totK_node, atot557, atot558]
  decide +kernel

theorem arows562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u562 = true := by
  rw [show D2M8K2.u562 = KTree.node D2M8K2.u560 (nat_lit 1445824) (nat_lit 3712318215) (nat_lit 0) D2M8K2.u561 from rfl, allE_node, arows560, irow562, arows561]
  all_goals rfl

theorem atot562 : totK PD2M8K2 D2M8K2.u562 = [0, 78129874012, 539707185661, 1505626501919, 1135700933088, 176281148832, 4779662215, 0] := by
  rw [show D2M8K2.u562 = KTree.node D2M8K2.u560 (nat_lit 1445824) (nat_lit 3712318215) (nat_lit 0) D2M8K2.u561 from rfl, totK_node, atot560, atot561]
  decide +kernel

theorem arows566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u566 = true := by
  rw [show D2M8K2.u566 = KTree.node D2M8K2.u564 (nat_lit 1453252) (nat_lit 3767302611) (nat_lit 0) D2M8K2.u565 from rfl, allE_node, arows564, irow566, arows565]
  all_goals rfl

theorem atot566 : totK PD2M8K2 D2M8K2.u566 = [0, 448361292866, 1601442676228, 1371418051676, 179963907189, 1369150432, 0, 0] := by
  rw [show D2M8K2.u566 = KTree.node D2M8K2.u564 (nat_lit 1453252) (nat_lit 3767302611) (nat_lit 0) D2M8K2.u565 from rfl, totK_node, atot564, atot565]
  decide +kernel

theorem arows569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u569 = true := by
  rw [show D2M8K2.u569 = KTree.node D2M8K2.u567 (nat_lit 1457227) (nat_lit 1269132946) (nat_lit 0) D2M8K2.u568 from rfl, allE_node, arows567, irow569, arows568]
  all_goals rfl

theorem atot569 : totK PD2M8K2 D2M8K2.u569 = [0, 347978932329, 1283619627107, 1434584044100, 525976517546, 32762398897, 0, 0] := by
  rw [show D2M8K2.u569 = KTree.node D2M8K2.u567 (nat_lit 1457227) (nat_lit 1269132946) (nat_lit 0) D2M8K2.u568 from rfl, totK_node, atot567, atot568]
  decide +kernel

theorem arows576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u576 = true := by
  rw [show D2M8K2.u576 = KTree.node D2M8K2.u574 (nat_lit 1460150) (nat_lit 3179939393) (nat_lit 0) D2M8K2.u575 from rfl, allE_node, arows574, irow576, arows575]
  all_goals rfl

theorem atot576 : totK PD2M8K2 D2M8K2.u576 = [0, 420766999390, 1500140445024, 1401230789922, 274792593415, 9583672031, 0, 0] := by
  rw [show D2M8K2.u576 = KTree.node D2M8K2.u574 (nat_lit 1460150) (nat_lit 3179939393) (nat_lit 0) D2M8K2.u575 from rfl, totK_node, atot574, atot575]
  decide +kernel

theorem arows579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u579 = true := by
  rw [show D2M8K2.u579 = KTree.node D2M8K2.u577 (nat_lit 1463978) (nat_lit 4126665669) (nat_lit 0) D2M8K2.u578 from rfl, allE_node, arows577, irow579, arows578]
  all_goals rfl

theorem atot579 : totK PD2M8K2 D2M8K2.u579 = [0, 490098803607, 1550098513581, 1339526998561, 251449516707, 5228939780, 0, 0] := by
  rw [show D2M8K2.u579 = KTree.node D2M8K2.u577 (nat_lit 1463978) (nat_lit 4126665669) (nat_lit 0) D2M8K2.u578 from rfl, totK_node, atot577, atot578]
  decide +kernel

theorem arows583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u583 = true := by
  rw [show D2M8K2.u583 = KTree.node D2M8K2.u581 (nat_lit 1471122) (nat_lit 2449283621) (nat_lit 0) D2M8K2.u582 from rfl, allE_node, arows581, irow583, arows582]
  all_goals rfl

theorem atot583 : totK PD2M8K2 D2M8K2.u583 = [157204742844, 523721132681, 1109968871579, 1362483540336, 425536825101, 21982452388, 0, 0] := by
  rw [show D2M8K2.u583 = KTree.node D2M8K2.u581 (nat_lit 1471122) (nat_lit 2449283621) (nat_lit 0) D2M8K2.u582 from rfl, totK_node, atot581, atot582]
  decide +kernel

theorem arows586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u586 = true := by
  rw [show D2M8K2.u586 = KTree.node D2M8K2.u584 (nat_lit 1494865) (nat_lit 1558578335) (nat_lit 0) D2M8K2.u585 from rfl, allE_node, arows584, irow586, arows585]
  all_goals rfl

theorem atot586 : totK PD2M8K2 D2M8K2.u586 = [455883325080, 1627750031903, 1362464031512, 181369963615, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u586 = KTree.node D2M8K2.u584 (nat_lit 1494865) (nat_lit 1558578335) (nat_lit 0) D2M8K2.u585 from rfl, totK_node, atot584, atot585]
  decide +kernel

theorem arows591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u591 = true := by
  rw [show D2M8K2.u591 = KTree.node D2M8K2.u589 (nat_lit 1502826) (nat_lit 2855376760) (nat_lit 0) D2M8K2.u590 from rfl, allE_node, arows589, irow591, arows590]
  all_goals rfl

theorem atot591 : totK PD2M8K2 D2M8K2.u591 = [433386647384, 1451954119887, 1373579423397, 317234388240, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u591 = KTree.node D2M8K2.u589 (nat_lit 1502826) (nat_lit 2855376760) (nat_lit 0) D2M8K2.u590 from rfl, totK_node, atot589, atot590]
  decide +kernel

theorem arows594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u594 = true := by
  rw [show D2M8K2.u594 = KTree.node D2M8K2.u592 (nat_lit 1506193) (nat_lit 1360543781) (nat_lit 0) D2M8K2.u593 from rfl, allE_node, arows592, irow594, arows593]
  all_goals rfl

theorem atot594 : totK PD2M8K2 D2M8K2.u594 = [390739561046, 1420342082381, 1411328190712, 338173841328, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u594 = KTree.node D2M8K2.u592 (nat_lit 1506193) (nat_lit 1360543781) (nat_lit 0) D2M8K2.u593 from rfl, totK_node, atot592, atot593]
  decide +kernel

theorem arows598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u598 = true := by
  rw [show D2M8K2.u598 = KTree.node D2M8K2.u596 (nat_lit 1509453) (nat_lit 1445001560) (nat_lit 0) D2M8K2.u597 from rfl, allE_node, arows596, irow598, arows597]
  all_goals rfl

theorem atot598 : totK PD2M8K2 D2M8K2.u598 = [441221177580, 1523415964007, 1372132081405, 247680211924, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u598 = KTree.node D2M8K2.u596 (nat_lit 1509453) (nat_lit 1445001560) (nat_lit 0) D2M8K2.u597 from rfl, totK_node, atot596, atot597]
  decide +kernel

theorem arows601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u601 = true := by
  rw [show D2M8K2.u601 = KTree.node D2M8K2.u599 (nat_lit 1512847) (nat_lit 1553067729) (nat_lit 0) D2M8K2.u600 from rfl, allE_node, arows599, irow601, arows600]
  all_goals rfl

theorem atot601 : totK PD2M8K2 D2M8K2.u601 = [148396324619, 1050197632279, 1725885507436, 620035688889, 31659692706, 0, 0, 0] := by
  rw [show D2M8K2.u601 = KTree.node D2M8K2.u599 (nat_lit 1512847) (nat_lit 1553067729) (nat_lit 0) D2M8K2.u600 from rfl, totK_node, atot599, atot600]
  decide +kernel

theorem arows607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u607 = true := by
  rw [show D2M8K2.u607 = KTree.node D2M8K2.u605 (nat_lit 1516169) (nat_lit 1536612103) (nat_lit 0) D2M8K2.u606 from rfl, allE_node, arows605, irow607, arows606]
  all_goals rfl

theorem atot607 : totK PD2M8K2 D2M8K2.u607 = [0, 481888891575, 1647569780234, 1217718179774, 165779550946, 1369150432, 0, 0] := by
  rw [show D2M8K2.u607 = KTree.node D2M8K2.u605 (nat_lit 1516169) (nat_lit 1536612103) (nat_lit 0) D2M8K2.u606 from rfl, totK_node, atot605, atot606]
  decide +kernel

theorem arows610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u610 = true := by
  rw [show D2M8K2.u610 = KTree.node D2M8K2.u608 (nat_lit 1525298) (nat_lit 3046960876) (nat_lit 0) D2M8K2.u609 from rfl, allE_node, arows608, irow610, arows609]
  all_goals rfl

theorem atot610 : totK PD2M8K2 D2M8K2.u610 = [0, 740319995959, 1900102334601, 892459187643, 46832676326, 0, 0, 0] := by
  rw [show D2M8K2.u610 = KTree.node D2M8K2.u608 (nat_lit 1525298) (nat_lit 3046960876) (nat_lit 0) D2M8K2.u609 from rfl, totK_node, atot608, atot609]
  decide +kernel

theorem arows614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u614 = true := by
  rw [show D2M8K2.u614 = KTree.node D2M8K2.u612 (nat_lit 1531654) (nat_lit 3816079831) (nat_lit 0) D2M8K2.u613 from rfl, allE_node, arows612, irow614, arows613]
  all_goals rfl

theorem atot614 : totK PD2M8K2 D2M8K2.u614 = [152031495639, 922619066763, 1720644965905, 782935057450, 44572490000, 0, 0, 0] := by
  rw [show D2M8K2.u614 = KTree.node D2M8K2.u612 (nat_lit 1531654) (nat_lit 3816079831) (nat_lit 0) D2M8K2.u613 from rfl, totK_node, atot612, atot613]
  decide +kernel

theorem arows617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u617 = true := by
  rw [show D2M8K2.u617 = KTree.node D2M8K2.u615 (nat_lit 1540121) (nat_lit 1693077601) (nat_lit 0) D2M8K2.u616 from rfl, allE_node, arows615, irow617, arows616]
  all_goals rfl

theorem atot617 : totK PD2M8K2 D2M8K2.u617 = [282148326200, 1204716819044, 1521564999830, 586228734794, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u617 = KTree.node D2M8K2.u615 (nat_lit 1540121) (nat_lit 1693077601) (nat_lit 0) D2M8K2.u616 from rfl, totK_node, atot615, atot616]
  decide +kernel

theorem arows622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u622 = true := by
  rw [show D2M8K2.u622 = KTree.node D2M8K2.u620 (nat_lit 1546336) (nat_lit 3003695623) (nat_lit 0) D2M8K2.u621 from rfl, allE_node, arows620, irow622, arows621]
  all_goals rfl

theorem atot622 : totK PD2M8K2 D2M8K2.u622 = [422469058626, 1465266448712, 1390264624678, 322313627221, 13237669976, 0, 0, 0] := by
  rw [show D2M8K2.u622 = KTree.node D2M8K2.u620 (nat_lit 1546336) (nat_lit 3003695623) (nat_lit 0) D2M8K2.u621 from rfl, totK_node, atot620, atot621]
  decide +kernel

theorem arows625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u625 = true := by
  rw [show D2M8K2.u625 = KTree.node D2M8K2.u623 (nat_lit 1549468) (nat_lit 3845805815) (nat_lit 0) D2M8K2.u624 from rfl, allE_node, arows623, irow625, arows624]
  all_goals rfl

theorem atot625 : totK PD2M8K2 D2M8K2.u625 = [424079571056, 1501183508515, 1412378738168, 267065864855, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u625 = KTree.node D2M8K2.u623 (nat_lit 1549468) (nat_lit 3845805815) (nat_lit 0) D2M8K2.u624 from rfl, totK_node, atot623, atot624]
  decide +kernel

theorem arows629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u629 = true := by
  rw [show D2M8K2.u629 = KTree.node D2M8K2.u627 (nat_lit 1553341) (nat_lit 1254182436) (nat_lit 0) D2M8K2.u628 from rfl, allE_node, arows627, irow629, arows628]
  all_goals rfl

theorem atot629 : totK PD2M8K2 D2M8K2.u629 = [382152125481, 1419377978519, 1462503094529, 359842050492, 9902299053, 0, 0, 0] := by
  rw [show D2M8K2.u629 = KTree.node D2M8K2.u627 (nat_lit 1553341) (nat_lit 1254182436) (nat_lit 0) D2M8K2.u628 from rfl, totK_node, atot627, atot628]
  decide +kernel

theorem arows632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u632 = true := by
  rw [show D2M8K2.u632 = KTree.node D2M8K2.u630 (nat_lit 1560034) (nat_lit 3118663928) (nat_lit 0) D2M8K2.u631 from rfl, allE_node, arows630, irow632, arows631]
  all_goals rfl

theorem atot632 : totK PD2M8K2 D2M8K2.u632 = [0, 429410198805, 1421954476644, 1346958200329, 403485684360, 29044448997, 0, 0] := by
  rw [show D2M8K2.u632 = KTree.node D2M8K2.u630 (nat_lit 1560034) (nat_lit 3118663928) (nat_lit 0) D2M8K2.u631 from rfl, totK_node, atot630, atot631]
  decide +kernel

theorem arows640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u640 = true := by
  rw [show D2M8K2.u640 = KTree.node D2M8K2.u638 (nat_lit 1566562) (nat_lit 4123203255) (nat_lit 0) D2M8K2.u639 from rfl, allE_node, arows638, irow640, arows639]
  all_goals rfl

theorem atot640 : totK PD2M8K2 D2M8K2.u640 = [0, 424575910031, 1489412668198, 1388662102407, 302922077854, 7877424857, 0, 0] := by
  rw [show D2M8K2.u640 = KTree.node D2M8K2.u638 (nat_lit 1566562) (nat_lit 4123203255) (nat_lit 0) D2M8K2.u639 from rfl, totK_node, atot638, atot639]
  decide +kernel

theorem arows643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u643 = true := by
  rw [show D2M8K2.u643 = KTree.node D2M8K2.u641 (nat_lit 1569843) (nat_lit 2568185769) (nat_lit 0) D2M8K2.u642 from rfl, allE_node, arows641, irow643, arows642]
  all_goals rfl

theorem atot643 : totK PD2M8K2 D2M8K2.u643 = [0, 399275795302, 1523419415119, 1421150307874, 232025739663, 5218872685, 0, 0] := by
  rw [show D2M8K2.u643 = KTree.node D2M8K2.u641 (nat_lit 1569843) (nat_lit 2568185769) (nat_lit 0) D2M8K2.u642 from rfl, totK_node, atot641, atot642]
  decide +kernel

theorem arows647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u647 = true := by
  rw [show D2M8K2.u647 = KTree.node D2M8K2.u645 (nat_lit 1573579) (nat_lit 2142924453) (nat_lit 0) D2M8K2.u646 from rfl, allE_node, arows645, irow647, arows646]
  all_goals rfl

theorem atot647 : totK PD2M8K2 D2M8K2.u647 = [0, 404939122715, 1478149897527, 1431558731160, 297614995505, 3899220927, 0, 0] := by
  rw [show D2M8K2.u647 = KTree.node D2M8K2.u645 (nat_lit 1573579) (nat_lit 2142924453) (nat_lit 0) D2M8K2.u646 from rfl, totK_node, atot645, atot646]
  decide +kernel

theorem arows650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u650 = true := by
  rw [show D2M8K2.u650 = KTree.node D2M8K2.u648 (nat_lit 1618806) (nat_lit 3723555697) (nat_lit 0) D2M8K2.u649 from rfl, allE_node, arows648, irow650, arows649]
  all_goals rfl

theorem atot650 : totK PD2M8K2 D2M8K2.u650 = [437729727136, 1496218955749, 1272032750283, 286932879796, 92456604904, 6818291842, 0, 0] := by
  rw [show D2M8K2.u650 = KTree.node D2M8K2.u648 (nat_lit 1618806) (nat_lit 3723555697) (nat_lit 0) D2M8K2.u649 from rfl, totK_node, atot648, atot649]
  decide +kernel

theorem arows655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u655 = true := by
  rw [show D2M8K2.u655 = KTree.node D2M8K2.u653 (nat_lit 1622438) (nat_lit 4033088525) (nat_lit 0) D2M8K2.u654 from rfl, allE_node, arows653, irow655, arows654]
  all_goals rfl

theorem atot655 : totK PD2M8K2 D2M8K2.u655 = [386643749773, 1348534913783, 1392405112631, 455185576441, 27802551719, 0, 0, 0] := by
  rw [show D2M8K2.u655 = KTree.node D2M8K2.u653 (nat_lit 1622438) (nat_lit 4033088525) (nat_lit 0) D2M8K2.u654 from rfl, totK_node, atot653, atot654]
  decide +kernel

theorem arows658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u658 = true := by
  rw [show D2M8K2.u658 = KTree.node D2M8K2.u656 (nat_lit 1628956) (nat_lit 3527692812) (nat_lit 0) D2M8K2.u657 from rfl, allE_node, arows656, irow658, arows657]
  all_goals rfl

theorem atot658 : totK PD2M8K2 D2M8K2.u658 = [446034111305, 1492675789929, 1375593420168, 324480478543, 12441494953, 0, 0, 0] := by
  rw [show D2M8K2.u658 = KTree.node D2M8K2.u656 (nat_lit 1628956) (nat_lit 3527692812) (nat_lit 0) D2M8K2.u657 from rfl, totK_node, atot656, atot657]
  decide +kernel

theorem arows662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u662 = true := by
  rw [show D2M8K2.u662 = KTree.node D2M8K2.u660 (nat_lit 1631960) (nat_lit 3500368473) (nat_lit 0) D2M8K2.u661 from rfl, allE_node, arows660, irow662, arows661]
  all_goals rfl

theorem atot662 : totK PD2M8K2 D2M8K2.u662 = [416199041148, 1478244817967, 1386561642339, 273136203517, 8578316156, 0, 0, 0] := by
  rw [show D2M8K2.u662 = KTree.node D2M8K2.u660 (nat_lit 1631960) (nat_lit 3500368473) (nat_lit 0) D2M8K2.u661 from rfl, totK_node, atot660, atot661]
  decide +kernel

theorem arows665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u665 = true := by
  rw [show D2M8K2.u665 = KTree.node D2M8K2.u663 (nat_lit 1635468) (nat_lit 2911596792) (nat_lit 0) D2M8K2.u664 from rfl, allE_node, arows663, irow665, arows664]
  all_goals rfl

theorem atot665 : totK PD2M8K2 D2M8K2.u665 = [420909814441, 1491676277430, 1415449859700, 277661543585, 5152749158, 0, 0, 0] := by
  rw [show D2M8K2.u665 = KTree.node D2M8K2.u663 (nat_lit 1635468) (nat_lit 2911596792) (nat_lit 0) D2M8K2.u664 from rfl, totK_node, atot663, atot664]
  decide +kernel

theorem arows671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u671 = true := by
  rw [show D2M8K2.u671 = KTree.node D2M8K2.u669 (nat_lit 1639086) (nat_lit 4071740195) (nat_lit 0) D2M8K2.u670 from rfl, allE_node, arows669, irow671, arows670]
  all_goals rfl

theorem atot671 : totK PD2M8K2 D2M8K2.u671 = [0, 596702365447, 1745362690507, 1073872193015, 110994515540, 1239866073, 0, 0] := by
  rw [show D2M8K2.u671 = KTree.node D2M8K2.u669 (nat_lit 1639086) (nat_lit 4071740195) (nat_lit 0) D2M8K2.u670 from rfl, totK_node, atot669, atot670]
  decide +kernel

theorem arows674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u674 = true := by
  rw [show D2M8K2.u674 = KTree.node D2M8K2.u672 (nat_lit 1642784) (nat_lit 3830058444) (nat_lit 0) D2M8K2.u673 from rfl, allE_node, arows672, irow674, arows673]
  all_goals rfl

theorem atot674 : totK PD2M8K2 D2M8K2.u674 = [0, 636586792016, 1773962107409, 1112887906398, 98723090964, 0, 0, 0] := by
  rw [show D2M8K2.u674 = KTree.node D2M8K2.u672 (nat_lit 1642784) (nat_lit 3830058444) (nat_lit 0) D2M8K2.u673 from rfl, totK_node, atot672, atot673]
  decide +kernel

theorem arows678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u678 = true := by
  rw [show D2M8K2.u678 = KTree.node D2M8K2.u676 (nat_lit 1651124) (nat_lit 3057825941) (nat_lit 0) D2M8K2.u677 from rfl, allE_node, arows676, irow678, arows677]
  all_goals rfl

theorem atot678 : totK PD2M8K2 D2M8K2.u678 = [0, 381825004090, 1458276563639, 1382485521249, 307100934591, 13105450397, 0, 0] := by
  rw [show D2M8K2.u678 = KTree.node D2M8K2.u676 (nat_lit 1651124) (nat_lit 3057825941) (nat_lit 0) D2M8K2.u677 from rfl, totK_node, atot676, atot677]
  decide +kernel

theorem arows681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u681 = true := by
  rw [show D2M8K2.u681 = KTree.node D2M8K2.u679 (nat_lit 1654294) (nat_lit 1730200991) (nat_lit 0) D2M8K2.u680 from rfl, allE_node, arows679, irow681, arows680]
  all_goals rfl

theorem atot681 : totK PD2M8K2 D2M8K2.u681 = [0, 482581108349, 1569594341199, 1255650729692, 193938409909, 4720618446, 0, 0] := by
  rw [show D2M8K2.u681 = KTree.node D2M8K2.u679 (nat_lit 1654294) (nat_lit 1730200991) (nat_lit 0) D2M8K2.u680 from rfl, totK_node, atot679, atot680]
  decide +kernel

theorem arows686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u686 = true := by
  rw [show D2M8K2.u686 = KTree.node D2M8K2.u684 (nat_lit 1659697) (nat_lit 1408261823) (nat_lit 0) D2M8K2.u685 from rfl, allE_node, arows684, irow686, arows685]
  all_goals rfl

theorem atot686 : totK PD2M8K2 D2M8K2.u686 = [409630840049, 1358846285414, 1344323041643, 446956115755, 27300781952, 0, 0, 0] := by
  rw [show D2M8K2.u686 = KTree.node D2M8K2.u684 (nat_lit 1659697) (nat_lit 1408261823) (nat_lit 0) D2M8K2.u685 from rfl, totK_node, atot684, atot685]
  decide +kernel

theorem arows689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u689 = true := by
  rw [show D2M8K2.u689 = KTree.node D2M8K2.u687 (nat_lit 1663332) (nat_lit 2486264185) (nat_lit 0) D2M8K2.u688 from rfl, allE_node, arows687, irow689, arows688]
  all_goals rfl

theorem atot689 : totK PD2M8K2 D2M8K2.u689 = [386263522558, 1451861059805, 1413960103944, 349709056547, 25276541998, 0, 0, 0] := by
  rw [show D2M8K2.u689 = KTree.node D2M8K2.u687 (nat_lit 1663332) (nat_lit 2486264185) (nat_lit 0) D2M8K2.u688 from rfl, totK_node, atot687, atot688]
  decide +kernel

theorem arows693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u693 = true := by
  rw [show D2M8K2.u693 = KTree.node D2M8K2.u691 (nat_lit 1666378) (nat_lit 3607917660) (nat_lit 0) D2M8K2.u692 from rfl, allE_node, arows691, irow693, arows692]
  all_goals rfl

theorem atot693 : totK PD2M8K2 D2M8K2.u693 = [326288597226, 1263944712019, 1498503163730, 482425175366, 20567184416, 0, 0, 0] := by
  rw [show D2M8K2.u693 = KTree.node D2M8K2.u691 (nat_lit 1666378) (nat_lit 3607917660) (nat_lit 0) D2M8K2.u692 from rfl, totK_node, atot691, atot692]
  decide +kernel

theorem arows696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u696 = true := by
  rw [show D2M8K2.u696 = KTree.node D2M8K2.u694 (nat_lit 1670441) (nat_lit 1738884925) (nat_lit 0) D2M8K2.u695 from rfl, allE_node, arows694, irow696, arows695]
  all_goals rfl

theorem atot696 : totK PD2M8K2 D2M8K2.u696 = [423872698287, 1446665587242, 1370964195291, 321142940151, 13130749562, 0, 0, 0] := by
  rw [show D2M8K2.u696 = KTree.node D2M8K2.u694 (nat_lit 1670441) (nat_lit 1738884925) (nat_lit 0) D2M8K2.u695 from rfl, totK_node, atot694, atot695]
  decide +kernel

theorem arows703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u703 = true := by
  rw [show D2M8K2.u703 = KTree.node D2M8K2.u701 (nat_lit 1673521) (nat_lit 1403630470) (nat_lit 0) D2M8K2.u702 from rfl, allE_node, arows701, irow703, arows702]
  all_goals rfl

theorem atot703 : totK PD2M8K2 D2M8K2.u703 = [435828682369, 1531120291890, 1387375830869, 241676050043, 4678454933, 0, 0, 0] := by
  rw [show D2M8K2.u703 = KTree.node D2M8K2.u701 (nat_lit 1673521) (nat_lit 1403630470) (nat_lit 0) D2M8K2.u702 from rfl, totK_node, atot701, atot702]
  decide +kernel

theorem arows706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u706 = true := by
  rw [show D2M8K2.u706 = KTree.node D2M8K2.u704 (nat_lit 1680744) (nat_lit 3409712938) (nat_lit 0) D2M8K2.u705 from rfl, allE_node, arows704, irow706, arows705]
  all_goals rfl

theorem atot706 : totK PD2M8K2 D2M8K2.u706 = [0, 562387632951, 1732190866832, 1099705997524, 114991860159, 1138244013, 0, 0] := by
  rw [show D2M8K2.u706 = KTree.node D2M8K2.u704 (nat_lit 1680744) (nat_lit 3409712938) (nat_lit 0) D2M8K2.u705 from rfl, totK_node, atot704, atot705]
  decide +kernel

theorem arows710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u710 = true := by
  rw [show D2M8K2.u710 = KTree.node D2M8K2.u708 (nat_lit 1684638) (nat_lit 3851639397) (nat_lit 0) D2M8K2.u709 from rfl, allE_node, arows708, irow710, arows709]
  all_goals rfl

theorem atot710 : totK PD2M8K2 D2M8K2.u710 = [0, 739166353065, 1863792959941, 938826235853, 68302050067, 0, 0, 0] := by
  rw [show D2M8K2.u710 = KTree.node D2M8K2.u708 (nat_lit 1684638) (nat_lit 3851639397) (nat_lit 0) D2M8K2.u709 from rfl, totK_node, atot708, atot709]
  decide +kernel

theorem arows713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u713 = true := by
  rw [show D2M8K2.u713 = KTree.node D2M8K2.u711 (nat_lit 1691554) (nat_lit 4159550692) (nat_lit 0) D2M8K2.u712 from rfl, allE_node, arows711, irow713, arows712]
  all_goals rfl

theorem atot713 : totK PD2M8K2 D2M8K2.u713 = [0, 731795834540, 1879291245701, 912027824743, 53690768933, 0, 0, 0] := by
  rw [show D2M8K2.u713 = KTree.node D2M8K2.u711 (nat_lit 1691554) (nat_lit 4159550692) (nat_lit 0) D2M8K2.u712 from rfl, totK_node, atot711, atot712]
  decide +kernel

theorem arows718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u718 = true := by
  rw [show D2M8K2.u718 = KTree.node D2M8K2.u716 (nat_lit 1696491) (nat_lit 2896267591) (nat_lit 0) D2M8K2.u717 from rfl, allE_node, arows716, irow718, arows717]
  all_goals rfl

theorem atot718 : totK PD2M8K2 D2M8K2.u718 = [369281099351, 974129404539, 1085794999716, 901723835894, 196234708224, 4977114383, 0, 0] := by
  rw [show D2M8K2.u718 = KTree.node D2M8K2.u716 (nat_lit 1696491) (nat_lit 2896267591) (nat_lit 0) D2M8K2.u717 from rfl, totK_node, atot716, atot717]
  decide +kernel

theorem arows721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u721 = true := by
  rw [show D2M8K2.u721 = KTree.node D2M8K2.u719 (nat_lit 1704210) (nat_lit 3372653511) (nat_lit 0) D2M8K2.u720 from rfl, allE_node, arows719, irow721, arows720]
  all_goals rfl

theorem atot721 : totK PD2M8K2 D2M8K2.u721 = [426021234305, 1588514665299, 1429523254143, 206016471497, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u721 = KTree.node D2M8K2.u719 (nat_lit 1704210) (nat_lit 3372653511) (nat_lit 0) D2M8K2.u720 from rfl, totK_node, atot719, atot720]
  decide +kernel

theorem arows725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u725 = true := by
  rw [show D2M8K2.u725 = KTree.node D2M8K2.u723 (nat_lit 1707198) (nat_lit 3952233191) (nat_lit 0) D2M8K2.u724 from rfl, allE_node, arows723, irow725, arows724]
  all_goals rfl

theorem atot725 : totK PD2M8K2 D2M8K2.u725 = [329183105084, 1242212164923, 1477066076722, 552577610838, 36307520372, 0, 0, 0] := by
  rw [show D2M8K2.u725 = KTree.node D2M8K2.u723 (nat_lit 1707198) (nat_lit 3952233191) (nat_lit 0) D2M8K2.u724 from rfl, totK_node, atot723, atot724]
  decide +kernel

theorem arows728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u728 = true := by
  rw [show D2M8K2.u728 = KTree.node D2M8K2.u726 (nat_lit 1711180) (nat_lit 3704090693) (nat_lit 0) D2M8K2.u727 from rfl, allE_node, arows726, irow728, arows727]
  all_goals rfl

theorem atot728 : totK PD2M8K2 D2M8K2.u728 = [424706585713, 1472131667070, 1399088633927, 303417642807, 10767460221, 0, 0, 0] := by
  rw [show D2M8K2.u728 = KTree.node D2M8K2.u726 (nat_lit 1711180) (nat_lit 3704090693) (nat_lit 0) D2M8K2.u727 from rfl, totK_node, atot726, atot727]
  decide +kernel

theorem arows734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u734 = true := by
  rw [show D2M8K2.u734 = KTree.node D2M8K2.u732 (nat_lit 1717979) (nat_lit 2859965586) (nat_lit 0) D2M8K2.u733 from rfl, allE_node, arows732, irow734, arows733]
  all_goals rfl

theorem atot734 : totK PD2M8K2 D2M8K2.u734 = [440289439084, 1503175487690, 1375279517156, 302946942372, 12045711471, 0, 0, 0] := by
  rw [show D2M8K2.u734 = KTree.node D2M8K2.u732 (nat_lit 1717979) (nat_lit 2859965586) (nat_lit 0) D2M8K2.u733 from rfl, totK_node, atot732, atot733]
  decide +kernel

theorem arows737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u737 = true := by
  rw [show D2M8K2.u737 = KTree.node D2M8K2.u735 (nat_lit 1721078) (nat_lit 3082673425) (nat_lit 0) D2M8K2.u736 from rfl, allE_node, arows735, irow737, arows736]
  all_goals rfl

theorem atot737 : totK PD2M8K2 D2M8K2.u737 = [0, 810873632105, 1943546644388, 778180400687, 32483106296, 0, 0, 0] := by
  rw [show D2M8K2.u737 = KTree.node D2M8K2.u735 (nat_lit 1721078) (nat_lit 3082673425) (nat_lit 0) D2M8K2.u736 from rfl, totK_node, atot735, atot736]
  decide +kernel

theorem arows741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u741 = true := by
  rw [show D2M8K2.u741 = KTree.node D2M8K2.u739 (nat_lit 1725066) (nat_lit 3816600073) (nat_lit 0) D2M8K2.u740 from rfl, allE_node, arows739, irow741, arows740]
  all_goals rfl

theorem atot741 : totK PD2M8K2 D2M8K2.u741 = [0, 469103781714, 1598381852344, 1374607442210, 169623374487, 1310285577, 0, 0] := by
  rw [show D2M8K2.u741 = KTree.node D2M8K2.u739 (nat_lit 1725066) (nat_lit 3816600073) (nat_lit 0) D2M8K2.u740 from rfl, totK_node, atot739, atot740]
  decide +kernel

theorem arows744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u744 = true := by
  rw [show D2M8K2.u744 = KTree.node D2M8K2.u742 (nat_lit 1730056) (nat_lit 3762547936) (nat_lit 0) D2M8K2.u743 from rfl, allE_node, arows742, irow744, arows743]
  all_goals rfl

theorem atot744 : totK PD2M8K2 D2M8K2.u744 = [0, 486466233206, 1566598124437, 1323212396399, 222466641505, 4879840392, 0, 0] := by
  rw [show D2M8K2.u744 = KTree.node D2M8K2.u742 (nat_lit 1730056) (nat_lit 3762547936) (nat_lit 0) D2M8K2.u743 from rfl, totK_node, atot742, atot743]
  decide +kernel

theorem arows749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u749 = true := by
  rw [show D2M8K2.u749 = KTree.node D2M8K2.u747 (nat_lit 1734162) (nat_lit 3447247446) (nat_lit 0) D2M8K2.u748 from rfl, allE_node, arows747, irow749, arows748]
  all_goals rfl

theorem atot749 : totK PD2M8K2 D2M8K2.u749 = [0, 435759446362, 1577386706501, 1329420958156, 215193178340, 4931404646, 0, 0] := by
  rw [show D2M8K2.u749 = KTree.node D2M8K2.u747 (nat_lit 1734162) (nat_lit 3447247446) (nat_lit 0) D2M8K2.u748 from rfl, totK_node, atot747, atot748]
  decide +kernel

theorem arows752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u752 = true := by
  rw [show D2M8K2.u752 = KTree.node D2M8K2.u750 (nat_lit 1740811) (nat_lit 1464102976) (nat_lit 0) D2M8K2.u751 from rfl, allE_node, arows750, irow752, arows751]
  all_goals rfl

theorem atot752 : totK PD2M8K2 D2M8K2.u752 = [0, 357068159128, 1354146452007, 1425294760680, 401012328916, 21751168066, 0, 0] := by
  rw [show D2M8K2.u752 = KTree.node D2M8K2.u750 (nat_lit 1740811) (nat_lit 1464102976) (nat_lit 0) D2M8K2.u751 from rfl, totK_node, atot750, atot751]
  decide +kernel

theorem arows756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u756 = true := by
  rw [show D2M8K2.u756 = KTree.node D2M8K2.u754 (nat_lit 1744163) (nat_lit 2353068237) (nat_lit 0) D2M8K2.u755 from rfl, allE_node, arows754, irow756, arows755]
  all_goals rfl

theorem atot756 : totK PD2M8K2 D2M8K2.u756 = [0, 486426562250, 1625530552532, 1323485820099, 176425992725, 1369150432, 0, 0] := by
  rw [show D2M8K2.u756 = KTree.node D2M8K2.u754 (nat_lit 1744163) (nat_lit 2353068237) (nat_lit 0) D2M8K2.u755 from rfl, totK_node, atot754, atot755]
  decide +kernel

theorem arows759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u759 = true := by
  rw [show D2M8K2.u759 = KTree.node D2M8K2.u757 (nat_lit 1752250) (nat_lit 3743493237) (nat_lit 0) D2M8K2.u758 from rfl, allE_node, arows757, irow759, arows758]
  all_goals rfl

theorem atot759 : totK PD2M8K2 D2M8K2.u759 = [0, 529576527127, 1670499945377, 1245575774647, 150812655746, 1164319620, 0, 0] := by
  rw [show D2M8K2.u759 = KTree.node D2M8K2.u757 (nat_lit 1752250) (nat_lit 3743493237) (nat_lit 0) D2M8K2.u758 from rfl, totK_node, atot757, atot758]
  decide +kernel

theorem arows768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u768 = true := by
  rw [show D2M8K2.u768 = KTree.node D2M8K2.u766 (nat_lit 1755430) (nat_lit 3770568387) (nat_lit 0) D2M8K2.u767 from rfl, allE_node, arows766, irow768, arows767]
  all_goals rfl

theorem atot768 : totK PD2M8K2 D2M8K2.u768 = [0, 361766968445, 1397428507216, 1445566225110, 334805947225, 13189998508, 0, 0] := by
  rw [show D2M8K2.u768 = KTree.node D2M8K2.u766 (nat_lit 1755430) (nat_lit 3770568387) (nat_lit 0) D2M8K2.u767 from rfl, totK_node, atot766, atot767]
  decide +kernel

theorem arows771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u771 = true := by
  rw [show D2M8K2.u771 = KTree.node D2M8K2.u769 (nat_lit 1759172) (nat_lit 2859607723) (nat_lit 0) D2M8K2.u770 from rfl, allE_node, arows769, irow771, arows770]
  all_goals rfl

theorem atot771 : totK PD2M8K2 D2M8K2.u771 = [0, 470165424993, 1567650536841, 1332147925128, 215853520909, 4917684815, 0, 0] := by
  rw [show D2M8K2.u771 = KTree.node D2M8K2.u769 (nat_lit 1759172) (nat_lit 2859607723) (nat_lit 0) D2M8K2.u770 from rfl, totK_node, atot769, atot770]
  decide +kernel

theorem arows775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u775 = true := by
  rw [show D2M8K2.u775 = KTree.node D2M8K2.u773 (nat_lit 1762549) (nat_lit 1253144617) (nat_lit 0) D2M8K2.u774 from rfl, allE_node, arows773, irow775, arows774]
  all_goals rfl

theorem atot775 : totK PD2M8K2 D2M8K2.u775 = [0, 0, 895955005864, 1946512512380, 662372516275, 28383153554, 0, 0] := by
  rw [show D2M8K2.u775 = KTree.node D2M8K2.u773 (nat_lit 1762549) (nat_lit 1253144617) (nat_lit 0) D2M8K2.u774 from rfl, totK_node, atot773, atot774]
  decide +kernel

theorem arows778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u778 = true := by
  rw [show D2M8K2.u778 = KTree.node D2M8K2.u776 (nat_lit 1770049) (nat_lit 1556661526) (nat_lit 0) D2M8K2.u777 from rfl, allE_node, arows776, irow778, arows777]
  all_goals rfl

theorem atot778 : totK PD2M8K2 D2M8K2.u778 = [0, 0, 552091898996, 1742139322482, 1066719246373, 113833092168, 1310517177, 0] := by
  rw [show D2M8K2.u778 = KTree.node D2M8K2.u776 (nat_lit 1770049) (nat_lit 1556661526) (nat_lit 0) D2M8K2.u777 from rfl, totK_node, atot776, atot777]
  decide +kernel

theorem arows783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u783 = true := by
  rw [show D2M8K2.u783 = KTree.node D2M8K2.u781 (nat_lit 1776873) (nat_lit 1712466799) (nat_lit 0) D2M8K2.u782 from rfl, allE_node, arows781, irow783, arows782]
  all_goals rfl

theorem atot783 : totK PD2M8K2 D2M8K2.u783 = [0, 0, 769053472822, 1909007999719, 789249742027, 38408224876, 0, 0] := by
  rw [show D2M8K2.u783 = KTree.node D2M8K2.u781 (nat_lit 1776873) (nat_lit 1712466799) (nat_lit 0) D2M8K2.u782 from rfl, totK_node, atot781, atot782]
  decide +kernel

theorem arows786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u786 = true := by
  rw [show D2M8K2.u786 = KTree.node D2M8K2.u784 (nat_lit 1787451) (nat_lit 3642318905) (nat_lit 0) D2M8K2.u785 from rfl, allE_node, arows784, irow786, arows785]
  all_goals rfl

theorem atot786 : totK PD2M8K2 D2M8K2.u786 = [0, 430243710856, 1477820310410, 1393920557467, 346299362607, 18129352193, 0, 0] := by
  rw [show D2M8K2.u786 = KTree.node D2M8K2.u784 (nat_lit 1787451) (nat_lit 3642318905) (nat_lit 0) D2M8K2.u785 from rfl, totK_node, atot784, atot785]
  decide +kernel

theorem arows790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u790 = true := by
  rw [show D2M8K2.u790 = KTree.node D2M8K2.u788 (nat_lit 1793671) (nat_lit 2377939237) (nat_lit 0) D2M8K2.u789 from rfl, allE_node, arows788, irow790, arows789]
  all_goals rfl

theorem atot790 : totK PD2M8K2 D2M8K2.u790 = [0, 387512026134, 1279404577060, 1385708710031, 531043041523, 30482727813, 0, 0] := by
  rw [show D2M8K2.u790 = KTree.node D2M8K2.u788 (nat_lit 1793671) (nat_lit 2377939237) (nat_lit 0) D2M8K2.u789 from rfl, totK_node, atot788, atot789]
  decide +kernel

theorem arows793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u793 = true := by
  rw [show D2M8K2.u793 = KTree.node D2M8K2.u791 (nat_lit 1796875) (nat_lit 1782679708) (nat_lit 0) D2M8K2.u792 from rfl, allE_node, arows791, irow793, arows792]
  all_goals rfl

theorem atot793 : totK PD2M8K2 D2M8K2.u793 = [0, 379268820415, 1402200618897, 1447587061241, 347557684583, 13183084702, 0, 0] := by
  rw [show D2M8K2.u793 = KTree.node D2M8K2.u791 (nat_lit 1796875) (nat_lit 1782679708) (nat_lit 0) D2M8K2.u792 from rfl, totK_node, atot791, atot792]
  decide +kernel

theorem arows799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u799 = true := by
  rw [show D2M8K2.u799 = KTree.node D2M8K2.u797 (nat_lit 1800728) (nat_lit 2483115942) (nat_lit 0) D2M8K2.u798 from rfl, allE_node, arows797, irow799, arows798]
  all_goals rfl

theorem atot799 : totK PD2M8K2 D2M8K2.u799 = [0, 460487043058, 1612702238914, 1350793128482, 203734025984, 3880716147, 0, 0] := by
  rw [show D2M8K2.u799 = KTree.node D2M8K2.u797 (nat_lit 1800728) (nat_lit 2483115942) (nat_lit 0) D2M8K2.u798 from rfl, totK_node, atot797, atot798]
  decide +kernel

theorem arows802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u802 = true := by
  rw [show D2M8K2.u802 = KTree.node D2M8K2.u800 (nat_lit 1866249) (nat_lit 1834472244) (nat_lit 0) D2M8K2.u801 from rfl, allE_node, arows800, irow802, arows801]
  all_goals rfl

theorem atot802 : totK PD2M8K2 D2M8K2.u802 = [0, 416235866548, 1389183266996, 1353554304246, 392334964362, 17826494640, 0, 0] := by
  rw [show D2M8K2.u802 = KTree.node D2M8K2.u800 (nat_lit 1866249) (nat_lit 1834472244) (nat_lit 0) D2M8K2.u801 from rfl, totK_node, atot800, atot801]
  decide +kernel

theorem arows806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u806 = true := by
  rw [show D2M8K2.u806 = KTree.node D2M8K2.u804 (nat_lit 1870186) (nat_lit 3883896084) (nat_lit 0) D2M8K2.u805 from rfl, allE_node, arows804, irow806, arows805]
  all_goals rfl

theorem atot806 : totK PD2M8K2 D2M8K2.u806 = [0, 406075943202, 1562833450012, 1443632079601, 193939393520, 1369150432, 0, 0] := by
  rw [show D2M8K2.u806 = KTree.node D2M8K2.u804 (nat_lit 1870186) (nat_lit 3883896084) (nat_lit 0) D2M8K2.u805 from rfl, totK_node, atot804, atot805]
  decide +kernel

theorem arows809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u809 = true := by
  rw [show D2M8K2.u809 = KTree.node D2M8K2.u807 (nat_lit 1873070) (nat_lit 2035109233) (nat_lit 0) D2M8K2.u808 from rfl, allE_node, arows807, irow809, arows808]
  all_goals rfl

theorem atot809 : totK PD2M8K2 D2M8K2.u809 = [0, 356521777567, 1268172593498, 1425018186105, 520520812061, 30151172974, 0, 0] := by
  rw [show D2M8K2.u809 = KTree.node D2M8K2.u807 (nat_lit 1873070) (nat_lit 2035109233) (nat_lit 0) D2M8K2.u808 from rfl, totK_node, atot807, atot808]
  decide +kernel

theorem arows814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u814 = true := by
  rw [show D2M8K2.u814 = KTree.node D2M8K2.u812 (nat_lit 1879636) (nat_lit 2645304427) (nat_lit 0) D2M8K2.u813 from rfl, allE_node, arows812, irow814, arows813]
  all_goals rfl

theorem atot814 : totK PD2M8K2 D2M8K2.u814 = [0, 397189552436, 1399880034360, 1426135913980, 344930174654, 13250685261, 0, 0] := by
  rw [show D2M8K2.u814 = KTree.node D2M8K2.u812 (nat_lit 1879636) (nat_lit 2645304427) (nat_lit 0) D2M8K2.u813 from rfl, totK_node, atot812, atot813]
  decide +kernel

theorem arows817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u817 = true := by
  rw [show D2M8K2.u817 = KTree.node D2M8K2.u815 (nat_lit 1883008) (nat_lit 3308236299) (nat_lit 0) D2M8K2.u816 from rfl, allE_node, arows815, irow817, arows816]
  all_goals rfl

theorem atot817 : totK PD2M8K2 D2M8K2.u817 = [0, 430457278685, 1541192587352, 1376356547867, 224084705530, 4980514959, 0, 0] := by
  rw [show D2M8K2.u817 = KTree.node D2M8K2.u815 (nat_lit 1883008) (nat_lit 3308236299) (nat_lit 0) D2M8K2.u816 from rfl, totK_node, atot815, atot816]
  decide +kernel

theorem arows821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u821 = true := by
  rw [show D2M8K2.u821 = KTree.node D2M8K2.u819 (nat_lit 1886272) (nat_lit 1377703264) (nat_lit 0) D2M8K2.u820 from rfl, allE_node, arows819, irow821, arows820]
  all_goals rfl

theorem atot821 : totK PD2M8K2 D2M8K2.u821 = [0, 92620862180, 981944760898, 1812465862303, 620723684001, 28182338736, 0, 0] := by
  rw [show D2M8K2.u821 = KTree.node D2M8K2.u819 (nat_lit 1886272) (nat_lit 1377703264) (nat_lit 0) D2M8K2.u820 from rfl, totK_node, atot819, atot820]
  decide +kernel

theorem arows824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u824 = true := by
  rw [show D2M8K2.u824 = KTree.node D2M8K2.u822 (nat_lit 1890200) (nat_lit 1307921293) (nat_lit 0) D2M8K2.u823 from rfl, allE_node, arows822, irow824, arows823]
  all_goals rfl

theorem atot824 : totK PD2M8K2 D2M8K2.u824 = [0, 0, 538399505549, 1690274390330, 1151103679566, 132125794093, 1217496766, 0] := by
  rw [show D2M8K2.u824 = KTree.node D2M8K2.u822 (nat_lit 1890200) (nat_lit 1307921293) (nat_lit 0) D2M8K2.u823 from rfl, totK_node, atot822, atot823]
  decide +kernel

end QECKChecks.D2M8K2
